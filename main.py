from __future__ import annotations

import csv
import base64
import hashlib
import json
import math
import re
import sys
from collections import OrderedDict
from io import BytesIO
from dataclasses import asdict, dataclass, field
from pathlib import Path
from typing import Any

from PySide6.QtCore import Qt, QSize, QSizeF, QRect, QRectF, QPointF, Signal, QMarginsF, QSettings, QByteArray, QBuffer, QIODevice, QTimer
from PySide6.QtGui import QColor, QFont, QFontMetricsF, QImage, QPainter, QPen, QPixmap, QPageSize, QPageLayout, QAction, QKeySequence, QShortcut, QIcon, QTextLayout, QTextOption
from PySide6.QtSvg import QSvgRenderer
from PySide6.QtPdf import QPdfDocument
from PySide6.QtPrintSupport import QPrinter, QPrintDialog, QPrintPreviewWidget, QPrinterInfo
from PySide6.QtWidgets import (
    QApplication, QAbstractItemView, QCheckBox, QComboBox, QColorDialog, QDoubleSpinBox, QGridLayout, QDialog, QDialogButtonBox,
    QFileDialog, QFormLayout, QFrame, QHBoxLayout, QLabel, QLineEdit, QMainWindow, QFontComboBox, QInputDialog,
    QMessageBox, QPushButton, QSpinBox, QTableWidget, QTableWidgetItem, QTabWidget, QToolButton, QMenu, QProgressDialog,
    QToolBar, QVBoxLayout, QWidget, QHeaderView, QListWidget, QListWidgetItem, QScrollArea, QDockWidget,
)

try:
    import zxingcpp as _zxingcpp
except ImportError:
    _zxingcpp = None

APP = "Label Studio"
INK = "#20242b"
MUTED = "#7e8793"
ACCENT = "#4169e1"
PANEL = "#ffffff"
BG = "#f0f2f5"


@dataclass
class Element:
    kind: str = "text"
    x: float = 3.0
    y: float = 3.0
    width: float = 30.0
    height: float = 8.0
    value: str = "Текст"
    font_size: float = 10.0
    letter_spacing_pt: float = 0.0
    line_spacing_pt: float = 0.0
    bold: bool = False
    color: str = "#000000"
    font_family: str = "Arial"
    italic: bool = False
    underline: bool = False
    horizontal_alignment: str = "left"
    vertical_alignment: str = "center"
    barcode_type: str = "Code 128"
    hri_position: str = "bottom"
    hri_alignment: str = "center"
    hri_font_size: float = 8.0
    rotation: float = 0.0
    gs1: bool = True
    shape_type: str = "rectangle"
    fill_enabled: bool = False
    fill_color: str = "#ffffff"
    line_width: float = 0.35
    line_style: str = "solid"
    asset_data: str = ""
    layer_locked: bool = False
    lock_proportions: bool = False


def draw_text_layout(painter: QPainter, element: Element, rect: QRectF, text: str):
    """Lay out text consistently and apply optional tracking/leading."""
    font=QFont(element.font_family)
    font_size_mm=max(.1,element.font_size*25.4/72)
    # QTextLayout rounds glyph advances at tiny font sizes (often 3–4 px here),
    # which makes neighboring letters collide in the editor. Shape at 100 units
    # per millimeter, then scale the finished layout back into label coordinates.
    layout_units_per_mm=100
    font_px=max(1,round(font_size_mm*layout_units_per_mm));font_scale=1/layout_units_per_mm
    font.setPixelSize(font_px)
    font.setBold(element.bold);font.setItalic(element.italic);font.setUnderline(element.underline)
    font.setStyleStrategy(QFont.StyleStrategy.ForceOutline)
    font.setKerning(True)
    font.setLetterSpacing(QFont.SpacingType.AbsoluteSpacing,element.letter_spacing_pt*25.4/72/font_scale)
    layout=QTextLayout(str(text or ""),font)
    option=QTextOption()
    option.setWrapMode(QTextOption.WrapMode.WrapAtWordBoundaryOrAnywhere)
    option.setUseDesignMetrics(True)
    horizontal="center" if element.kind=="symbol" else element.horizontal_alignment
    option.setAlignment({"left":Qt.AlignmentFlag.AlignLeft,"center":Qt.AlignmentFlag.AlignHCenter,
                         "right":Qt.AlignmentFlag.AlignRight}.get(horizontal,Qt.AlignmentFlag.AlignLeft))
    layout.setTextOption(option);layout.beginLayout();lines=[];y=0.0
    line_gap=element.line_spacing_pt*25.4/72/font_scale
    layout_width=max(1.0,rect.width()/font_scale)
    while True:
        line=layout.createLine()
        if not line.isValid():break
        line.setLineWidth(layout_width);line.setPosition(QPointF(0,y));lines.append(line)
        y+=line.height()+line_gap
    layout.endLayout()
    if not lines:return
    total_height=max(0.0,(y-line_gap)*font_scale)
    vertical="center" if element.kind=="symbol" else element.vertical_alignment
    vertical_offset={"top":0.0,"center":(rect.height()-total_height)/2,
                     "bottom":rect.height()-total_height}.get(vertical,(rect.height()-total_height)/2)
    painter.save()
    # Keep descenders visible even when a text box was sized to the font cap height.
    clip_slack=font_size_mm*.4
    painter.setClipRect(QRectF(rect.left(),rect.top()-clip_slack*.2,rect.width(),rect.height()+clip_slack))
    painter.setPen(QColor(element.color));painter.translate(rect.left(),rect.top()+vertical_offset);painter.scale(font_scale,font_scale)
    layout.draw(painter,QPointF(0,0))
    painter.restore()


def element_bounds_in_label(element: Element, template: "LabelTemplate", tolerance: float = 0.01) -> tuple[bool, bool]:
    angle=math.radians(element.rotation)
    bound_w=abs(element.width*math.cos(angle))+abs(element.height*math.sin(angle))
    bound_h=abs(element.width*math.sin(angle))+abs(element.height*math.cos(angle))
    center_x=element.x+element.width/2;center_y=element.y+element.height/2
    left=center_x-bound_w/2;top=center_y-bound_h/2;right=center_x+bound_w/2;bottom=center_y+bound_h/2
    fully_inside=(left>=-tolerance and top>=-tolerance and right<=template.width+tolerance and bottom<=template.height+tolerance)
    intersects=(right>tolerance and bottom>tolerance and left<template.width-tolerance and top<template.height-tolerance)
    return fully_inside,intersects


def extract_gs1_fields(raw: str) -> dict[str, str]:
    """Extract common GTIN (AI 01) and serial (AI 21) fields from GS1/ЧЗ text."""
    value = normalize_gs1_payload(raw).strip()
    result = {"GTIN": "", "Серийный номер": ""}
    gtin_match = re.search(r"(?:^|[^0-9])01(\d{14})", value)
    if gtin_match:
        result["GTIN"] = gtin_match.group(1)
        start = gtin_match.end()
        serial_start = re.match(r"21", value[start:])
        if serial_start:
            serial_start_at = start + 2
            serial_end = len(value)
            gs = value.find("<GS>", serial_start_at)
            if gs >= 0:
                serial_end = min(serial_end, gs)
            crypto_start = re.search(r"91.{4}92", value[serial_start_at:], flags=re.DOTALL)
            if crypto_start:
                serial_end = min(serial_end, serial_start_at + crypto_start.start())
            # Also accept explicitly parenthesized/non-GS1 field boundaries.
            next_ai = re.search(r"(?:^|<GS>)(?:91|92)", value[serial_start_at:])
            if next_ai:
                serial_end = min(serial_end, serial_start_at + next_ai.start())
            result["Серийный номер"] = value[serial_start_at:serial_end].strip("<GS>")
    return result


def resolve_template_value(value: str, row: dict[str, Any]) -> str:
    def replace(match):
        key = match.group(1)
        if key == "SEQ":
            return str(row.get("_SEQ", ""))
        if key.startswith("GTIN:"):
            return extract_gs1_fields(row.get(key[5:], ""))["GTIN"]
        if key.startswith("SERIAL:"):
            return extract_gs1_fields(row.get(key[7:], ""))["Серийный номер"]
        return str(row.get(key, ""))
    return re.sub(r"\{([^{}]+)\}", replace, value)


def normalize_gs1_payload(raw: str) -> str:
    """Convert parenthesized GS1 AI notation to the encoded data stream."""
    value=str(raw or "").replace("\\x1d","<GS>").replace("\x1d","<GS>")
    value=re.sub(r"^\]d[12]","",value,flags=re.IGNORECASE)
    matches=list(re.finditer(r"\((\d{2,4})\)",value))
    if matches:
        pieces=[]
        variable_ais={"10","21","22","30","37",*(f"{number:02d}" for number in range(90,100))}
        for index,match in enumerate(matches):
            end=matches[index+1].start() if index+1<len(matches) else len(value)
            ai=match.group(1);data=value[match.end():end]
            pieces.append(ai+data)
            if index+1<len(matches) and ai in variable_ais:pieces.append("<GS>")
        value="".join(pieces)
    return value


@dataclass
class LabelTemplate:
    name: str = "Новый шаблон"
    width: float = 58.0
    height: float = 40.0
    background: str = "#ffffff"
    background_image: str = ""
    background_image_opacity: float = 0.35
    background_image_visible: bool = True
    background_image_fit: str = "stretch"
    grid: float = 1.0
    guides: list[dict[str, Any]] = field(default_factory=list)
    elements: list[Element] = field(default_factory=list)
    print_settings: dict[str, Any] = field(default_factory=dict)


@dataclass
class CompositionBlock:
    path: str | None
    template: LabelTemplate
    copies: int = 1


class PrintPreviewDialog(QDialog):
    def __init__(self,parent,printer,available,start,end,copies,orientation,continue_sequence,build_order,render_callback,print_callback):
        super().__init__(parent)
        self.owner=parent;self.printer=printer;self.available=available;self.build_order=build_order
        self.render_callback=render_callback;self.print_callback=print_callback
        self.columns=parent.label_columns;self.gap=parent.column_gap
        self.setWindowTitle("Печать этикеток");self.resize(1280,840);self.setMinimumSize(1000,680)
        self.setStyleSheet("""
            QDialog { background:#eef2f7; color:#1d2939; }
            QFrame#topBar { background:#2563eb; border-radius:9px; }
            QFrame#settingsCard,QFrame#previewCard { background:#ffffff; border:1px solid #d8e0eb; border-radius:10px; }
            QLabel { color:#263447; }
            QLabel#title { color:white; font-size:20px; font-weight:700; }
            QLabel#section { color:#344054; font-size:13px; font-weight:700; }
            QLabel#hint { color:#667085; font-size:11px; }
            QComboBox,QSpinBox,QDoubleSpinBox { color:#202a39; background:white; border:1px solid #cbd5e1; border-radius:6px; padding:7px; min-height:24px; }
            QCheckBox { color:#344054; spacing:8px; }
            QPushButton { color:#263447; background:#ffffff; border:1px solid #cbd5e1; border-radius:6px; padding:8px 11px; }
            QPushButton:hover { background:#f0f5ff; border-color:#8aafff; }
            QPushButton#primaryPrint { background:#2563eb; color:white; border:0; font-size:15px; font-weight:700; padding:13px; }
            QPushButton#primaryPrint:hover { background:#1d4ed8; }
        """)
        root=QVBoxLayout(self);root.setContentsMargins(14,14,14,14);root.setSpacing(12)
        top=QFrame();top.setObjectName("topBar");top_layout=QHBoxLayout(top);top_layout.setContentsMargins(18,12,18,12)
        title=QLabel("Печать этикеток");title.setObjectName("title");top_layout.addWidget(title);top_layout.addStretch()
        self.variation_label=QLabel(f"Доступно вариантов: {available}");self.variation_label.setStyleSheet("color:#eaf1ff;font-size:12px");top_layout.addWidget(self.variation_label);root.addWidget(top)
        body=QHBoxLayout();body.setSpacing(12);root.addLayout(body,1)

        left=QFrame();left.setObjectName("settingsCard");left.setFixedWidth(370);left_layout=QVBoxLayout(left);left_layout.setContentsMargins(18,16,18,16);left_layout.setSpacing(11)
        printer_title=QLabel("ПРИНТЕР");printer_title.setObjectName("section");left_layout.addWidget(printer_title)
        printer_row=QHBoxLayout();self.printer_combo=QComboBox();self.printer_combo.setMinimumWidth(205);printer_row.addWidget(self.printer_combo,1)
        self.refresh_button=QPushButton("⟳");self.refresh_button.setToolTip("Обновить список принтеров");printer_row.addWidget(self.refresh_button);left_layout.addLayout(printer_row)
        self.printer_settings_button=QPushButton("Настройки принтера…");left_layout.addWidget(self.printer_settings_button)
        profile_row=QHBoxLayout();self.profile_combo=QComboBox();self.profile_combo.setMinimumWidth(140);self.profile_combo.setToolTip("Сохранённые профили печати")
        self.profile_save_button=QPushButton("＋");self.profile_save_button.setToolTip("Сохранить текущие настройки как профиль")
        self.profile_delete_button=QPushButton("−");self.profile_delete_button.setToolTip("Удалить выбранный профиль")
        profile_row.addWidget(self.profile_combo,1);profile_row.addWidget(self.profile_save_button);profile_row.addWidget(self.profile_delete_button);left_layout.addLayout(profile_row)
        left_layout.addSpacing(4);range_title=QLabel("ДИАПАЗОН ВАРИАНТОВ");range_title.setObjectName("section");left_layout.addWidget(range_title)
        range_row=QHBoxLayout();self.start_spin=QSpinBox();self.end_spin=QSpinBox()
        for spin in (self.start_spin,self.end_spin):spin.setRange(1,max(1,available))
        self.start_spin.setValue(min(max(1,start),max(1,available)));self.end_spin.setValue(min(max(self.start_spin.value(),end),max(1,available)))
        range_row.addWidget(self.start_spin);range_row.addWidget(QLabel("по"));range_row.addWidget(self.end_spin);left_layout.addLayout(range_row)
        range_hint=QLabel("Выберите номера строк данных, которые нужно напечатать.");range_hint.setObjectName("hint");range_hint.setWordWrap(True);left_layout.addWidget(range_hint)
        copies_title=QLabel("КОЛИЧЕСТВО КОПИЙ ДИАПАЗОНА");copies_title.setObjectName("section");left_layout.addWidget(copies_title)
        self.copies_spin=QSpinBox();self.copies_spin.setRange(1,9999);self.copies_spin.setValue(max(1,copies));left_layout.addWidget(self.copies_spin)
        orientation_title=QLabel("ОРИЕНТАЦИЯ ЭТИКЕТКИ");orientation_title.setObjectName("section");left_layout.addWidget(orientation_title)
        self.orientation_combo=QComboBox()
        for title,degrees in (("Книжная · 0°",0),("Книжная · 180°",180),("Альбомная · 90°",90),("Альбомная · 270°",270)):
            self.orientation_combo.addItem(title,degrees)
        legacy_orientation=orientation.value if isinstance(orientation,QPageLayout.Orientation) else int(orientation)
        if legacy_orientation==QPageLayout.Orientation.Landscape.value:legacy_orientation=90
        self.orientation_combo.setCurrentIndex(max(0,self.orientation_combo.findData(legacy_orientation)));left_layout.addWidget(self.orientation_combo)
        self.preflight_check=QCheckBox("Проверять макет перед печатью")
        self.preflight_check.setChecked(bool(parent.settings.value("print/preflight",True)))
        left_layout.addWidget(self.preflight_check)
        self.advanced_toggle=QToolButton();self.advanced_toggle.setText("Дополнительные параметры  ▸");self.advanced_toggle.setCheckable(True);self.advanced_toggle.setToolButtonStyle(Qt.ToolButtonStyle.ToolButtonTextOnly);left_layout.addWidget(self.advanced_toggle)
        self.advanced_panel=QFrame();advanced_layout=QVBoxLayout(self.advanced_panel);advanced_layout.setContentsMargins(4,0,4,0)
        self.continue_check=QCheckBox("Продолжать {SEQ} между копиями диапазона");self.continue_check.setChecked(continue_sequence);advanced_layout.addWidget(self.continue_check)
        self.reverse_check=QCheckBox("Печатать диапазон в обратном порядке");advanced_layout.addWidget(self.reverse_check)
        correction_row=QHBoxLayout();correction_row.addWidget(QLabel("Поправка ширины носителя"))
        self.width_correction_spin=QDoubleSpinBox();self.width_correction_spin.setRange(-10,10);self.width_correction_spin.setDecimals(1);self.width_correction_spin.setSingleStep(.1);self.width_correction_spin.setSuffix(" мм")
        self.width_correction_spin.setToolTip("Прибавляется к ширине носителя, передаваемой драйверу. Значение сохраняется отдельно для каждого принтера.")
        correction_row.addWidget(self.width_correction_spin);advanced_layout.addLayout(correction_row)
        self.columns_label=QLabel();self.columns_label.setObjectName("hint");advanced_layout.addWidget(self.columns_label)
        self.columns_button=QPushButton("Настроить колонки ленты…");advanced_layout.addWidget(self.columns_button);self.advanced_panel.hide();left_layout.addWidget(self.advanced_panel)
        left_layout.addStretch()
        self.summary=QLabel();self.summary.setStyleSheet("font-size:12px;font-weight:600;color:#344054;padding:7px 0");self.summary.setWordWrap(True);left_layout.addWidget(self.summary)
        self.print_button=QPushButton("Печать");self.print_button.setObjectName("primaryPrint");left_layout.addWidget(self.print_button)
        self.cancel_button=QPushButton("Отмена");left_layout.addWidget(self.cancel_button)
        body.addWidget(left)

        preview_card=QFrame();preview_card.setObjectName("previewCard");preview_layout=QVBoxLayout(preview_card);preview_layout.setContentsMargins(14,12,14,12);preview_layout.setSpacing(9)
        preview_head=QHBoxLayout();preview_title=QLabel("ПРЕДВАРИТЕЛЬНЫЙ ПРОСМОТР");preview_title.setObjectName("section");preview_head.addWidget(preview_title);preview_head.addStretch()
        self.page_spin=QSpinBox();self.page_spin.setRange(1,1);preview_head.addWidget(QLabel("Страница"));preview_head.addWidget(self.page_spin);self.page_total=QLabel("из 1");preview_head.addWidget(self.page_total)
        zoom_out=QPushButton("−");zoom_in=QPushButton("+");fit_width=QPushButton("По ширине");fit_page=QPushButton("Целиком")
        for button in (zoom_out,zoom_in,fit_width,fit_page):preview_head.addWidget(button)
        preview_layout.addLayout(preview_head)
        self.preview=QPrintPreviewWidget(printer,self);self.preview.setZoomMode(QPrintPreviewWidget.ZoomMode.FitInView);preview_layout.addWidget(self.preview,1)
        # Printer previews can be expensive for large variable-data runs. Coalesce
        # rapid spin-box changes and render only the final requested page set.
        self._preview_timer=QTimer(self);self._preview_timer.setSingleShot(True)
        self._preview_timer.setInterval(120);self._preview_timer.timeout.connect(self.preview.updatePreview)
        body.addWidget(preview_card,1)

        self._refresh_profile_list()
        self._fill_printers()
        self.printer_combo.currentIndexChanged.connect(self._printer_changed)
        self.profile_combo.currentIndexChanged.connect(self._apply_selected_profile)
        self.profile_save_button.clicked.connect(self._save_profile)
        self.profile_delete_button.clicked.connect(self._delete_profile)
        self.refresh_button.clicked.connect(self._fill_printers)
        self.printer_settings_button.clicked.connect(self._open_printer_settings)
        self.advanced_toggle.toggled.connect(self._toggle_advanced)
        self.start_spin.valueChanged.connect(self._range_changed);self.end_spin.valueChanged.connect(self._range_changed)
        self.copies_spin.valueChanged.connect(self._refresh_job)
        self.orientation_combo.currentIndexChanged.connect(self._refresh_job)
        self.continue_check.toggled.connect(self._refresh_job);self.reverse_check.toggled.connect(self._refresh_job)
        self.width_correction_spin.valueChanged.connect(self._width_correction_changed)
        self.columns_button.clicked.connect(self._configure_columns)
        self.preview.paintRequested.connect(self._paint_preview);self.preview.previewChanged.connect(self._sync_pages)
        self.page_spin.valueChanged.connect(self.preview.setCurrentPage)
        zoom_out.clicked.connect(self.preview.zoomOut);zoom_in.clicked.connect(self.preview.zoomIn)
        fit_width.clicked.connect(lambda:self.preview.setZoomMode(QPrintPreviewWidget.ZoomMode.FitToWidth))
        fit_page.clicked.connect(lambda:self.preview.setZoomMode(QPrintPreviewWidget.ZoomMode.FitInView))
        self.print_button.clicked.connect(self._print);self.cancel_button.clicked.connect(self.reject)
        self._refresh_job()

    def _fill_printers(self):
        old=str(self.printer.printerName() or self.owner.settings.value("printer/name",""))
        infos=QPrinterInfo.availablePrinters();self.printer_combo.blockSignals(True);self.printer_combo.clear()
        for info in infos:self.printer_combo.addItem(info.printerName(),info.printerName())
        if old and self.printer_combo.findData(old)<0:self.printer_combo.addItem(old,old)
        if not infos and not old:self.printer_combo.addItem("Системный принтер"," ")
        index=self.printer_combo.findData(old)
        if index<0 and infos:index=self.printer_combo.findData(QPrinterInfo.defaultPrinter().printerName())
        self.printer_combo.setCurrentIndex(max(0,index));self.printer_combo.blockSignals(False)
        self._printer_changed()

    def _printer_changed(self,*_):
        name=str(self.printer_combo.currentData() or "").strip()
        if name and self.printer.printerName()!=name:self.printer.setPrinterName(name)
        self._load_width_correction(name)
        if name:
            self.owner.settings.setValue("printer/name",name)
            self.owner.settings.sync()
            self.owner.template.print_settings.setdefault("printer",{})["name"]=name
        self._refresh_job()
        if name:self._save_printer_settings()

    def _width_correction_key(self,printer_name):
        identity=hashlib.sha1((str(printer_name).casefold() or "default").encode("utf-8")).hexdigest()
        return f"printer/width_correction/{identity}"

    def _load_width_correction(self,printer_name):
        key=self._width_correction_key(printer_name)
        # Start from the template's exact media dimensions. Any per-printer
        # correction must be an explicit saved user choice, never a model guess.
        value=float(self.owner.settings.value(key,0.0))
        self.width_correction_spin.blockSignals(True);self.width_correction_spin.setValue(value);self.width_correction_spin.blockSignals(False)

    def _width_correction_changed(self,value):
        name=str(self.printer_combo.currentData() or "")
        self.owner.settings.setValue(self._width_correction_key(name),float(value));self.owner.settings.sync()
        self._refresh_job()

    def _profiles(self):
        try:return json.loads(str(self.owner.settings.value("printer/profiles","{}")))
        except (TypeError,ValueError):return {}

    def _refresh_profile_list(self,selected=""):
        profiles=self._profiles();self.profile_combo.blockSignals(True);self.profile_combo.clear()
        self.profile_combo.addItem("Профиль печати…","")
        for name in sorted(profiles,key=str.casefold):self.profile_combo.addItem(name,name)
        index=self.profile_combo.findData(selected) if selected else 0
        self.profile_combo.setCurrentIndex(max(0,index));self.profile_combo.blockSignals(False)
        self.profile_delete_button.setEnabled(bool(selected))

    def _save_profile(self):
        name,accepted=QInputDialog.getText(self,"Сохранить профиль печати","Название профиля:")
        name=name.strip()
        if not accepted or not name:return
        profile={"printer_name":self.printer.printerName(),"resolution":self.printer.resolution(),
                 "color_mode":self.printer.colorMode().value,"duplex":self.printer.duplex().value,
                 "paper_source":self.printer.paperSource().value,"page_order":self.printer.pageOrder().value,
                 "collate":self.printer.collateCopies(),"orientation":self.orientation_combo.currentData(),
                 "columns":self.owner.label_columns,"column_gap":self.owner.column_gap,
                 "page_layout":self._page_layout_config(self.printer)}
        profiles=self._profiles();profiles[name]=profile
        self.owner.settings.setValue("printer/profiles",json.dumps(profiles,ensure_ascii=False));self.owner.settings.sync()
        self._refresh_profile_list(name)

    def _apply_selected_profile(self,index):
        name=self.profile_combo.itemData(index)
        if not name:return
        profile=self._profiles().get(str(name),{})
        printer_name=str(profile.get("printer_name", ""))
        if printer_name:
            combo_index=self.printer_combo.findData(printer_name)
            if combo_index<0:self.printer_combo.addItem(printer_name,printer_name);combo_index=self.printer_combo.findData(printer_name)
            self.printer_combo.blockSignals(True);self.printer_combo.setCurrentIndex(combo_index);self.printer_combo.blockSignals(False)
            self.printer.setPrinterName(printer_name)
            self._load_width_correction(printer_name)
        try:
            if "resolution" in profile:self.printer.setResolution(int(profile["resolution"]))
            if "color_mode" in profile:self.printer.setColorMode(QPrinter.ColorMode(int(profile["color_mode"])))
            if "duplex" in profile:self.printer.setDuplex(QPrinter.DuplexMode(int(profile["duplex"])))
            if "paper_source" in profile:self.printer.setPaperSource(QPrinter.PaperSource(int(profile["paper_source"])))
            if "page_order" in profile:self.printer.setPageOrder(QPrinter.PageOrder(int(profile["page_order"])))
            if "collate" in profile:self.printer.setCollateCopies(bool(profile["collate"]))
        except (TypeError,ValueError):pass
        self._restore_page_layout(self.printer,profile.get("page_layout"))
        if profile.get("orientation") is not None:
            profile_orientation=int(profile["orientation"])
            if profile_orientation==QPageLayout.Orientation.Landscape.value:profile_orientation=90
            orientation_index=self.orientation_combo.findData(profile_orientation)
            if orientation_index>=0:self.orientation_combo.setCurrentIndex(orientation_index)
        if profile.get("columns"):
            self.owner.label_columns=max(1,int(profile["columns"]))
            self.owner.column_gap=max(0.0,float(profile.get("column_gap",0)))
            self.owner.settings.setValue("label_columns",self.owner.label_columns);self.owner.settings.setValue("column_gap",self.owner.column_gap)
        self.owner.settings.setValue("printer/name",printer_name);self._save_printer_settings();self._refresh_job()

    def _delete_profile(self):
        name=str(self.profile_combo.currentData() or "")
        if not name:return
        answer=QMessageBox.question(self,"Удалить профиль",f"Удалить профиль «{name}»?")
        if answer!=QMessageBox.StandardButton.Yes:return
        profiles=self._profiles();profiles.pop(name,None)
        self.owner.settings.setValue("printer/profiles",json.dumps(profiles,ensure_ascii=False));self.owner.settings.sync()
        self._refresh_profile_list()

    def _configure_page(self):
        self.columns=self.owner.label_columns;self.gap=self.owner.column_gap
        self.rotation=int(self.orientation_combo.currentData() or 0)
        label_w=self.owner.template.height if self.rotation in (90,270) else self.owner.template.width
        label_h=self.owner.template.width if self.rotation in (90,270) else self.owner.template.height
        self.page_width=label_w*self.columns+self.gap*(self.columns-1)
        self.page_height=label_h
        width_correction=self.width_correction_spin.value()
        self.driver_page_width=self.page_width+width_correction
        # The driver's orientation follows the user's choice, not the label's
        # aspect ratio. QPageSize is stored in portrait coordinates, so only a
        # requested 90°/270° rotation swaps the base dimensions for Qt.
        landscape=self.rotation in (90,270)
        base_width,base_height=(label_h,self.driver_page_width) if landscape else (self.driver_page_width,label_h)
        page_size=QPageSize(QSizeF(base_width,base_height),QPageSize.Unit.Millimeter,
                             "Label template",QPageSize.SizeMatchPolicy.ExactMatch)
        page_orientation=QPageLayout.Orientation.Landscape if landscape else QPageLayout.Orientation.Portrait
        # Apply size and orientation as separate Qt print-engine properties.
        # Some Windows thermal drivers reject a complete QPageLayout when its
        # zero-margin request conflicts with their non-printable margins, even
        # though they accept the same custom paper size for the print job.
        self.printer.setFullPage(True)
        size_accepted=self.printer.setPageSize(page_size)
        orientation_accepted=self.printer.setPageOrientation(page_orientation)
        effective=self.printer.pageLayout().fullRect(QPageLayout.Unit.Millimeter)
        self.effective_page_width=effective.width();self.effective_page_height=effective.height()
        # fullRect() is already reported in the selected orientation. The media
        # width must stay the label/column width in either orientation.
        expected_effective=(self.driver_page_width,label_h)
        self.media_layout_applied=(size_accepted and orientation_accepted and
                                   abs(effective.width()-expected_effective[0])<.05 and
                                   abs(effective.height()-expected_effective[1])<.05)
        self.printer.setCopyCount(1)  # Copies are expanded into the page sequence by the app.
        if self.media_layout_applied:
            correction_note=f" · коррекция ширины {width_correction:+.1f} мм" if abs(width_correction)>.001 else ""
            self.columns_label.setText(f"Формат задания: {self.driver_page_width:.2f} × {self.page_height:.2f} мм · {self.columns} колонок · зазор {self.gap:.2f} мм{correction_note}")
        else:
            self.columns_label.setText(f"Шаблон {self.page_width:.2f} × {label_h:.2f} мм; драйверу передано {self.driver_page_width:.2f} мм по ширине · драйвер сообщает {effective.width():.2f} × {effective.height():.2f} мм")

    @staticmethod
    def _page_layout_config(printer):
        layout=printer.pageLayout();size=layout.pageSize().size(QPageSize.Unit.Millimeter)
        margins=layout.margins(QPageLayout.Unit.Millimeter)
        return {"width_mm":size.width(),"height_mm":size.height(),
                "name":layout.pageSize().name(),"orientation":layout.orientation().value,
                "margins_mm":[margins.left(),margins.top(),margins.right(),margins.bottom()]}

    @staticmethod
    def _restore_page_layout(printer,config):
        if not isinstance(config,dict):return
        try:
            width=float(config["width_mm"]);height=float(config["height_mm"])
            if width<=0 or height<=0:return
            page_size=QPageSize(QSizeF(width,height),QPageSize.Unit.Millimeter,
                                str(config.get("name") or "Saved printer media"),
                                QPageSize.SizeMatchPolicy.ExactMatch)
            orientation=QPageLayout.Orientation(int(config.get("orientation",0)))
            values=config.get("margins_mm",[0,0,0,0])
            margins=QMarginsF(*(float(value) for value in values))
            printer.setPageLayout(QPageLayout(page_size,orientation,margins,QPageLayout.Unit.Millimeter))
        except (KeyError,TypeError,ValueError):pass

    def _refresh_job(self,*_):
        if not hasattr(self,"orientation_combo"):return
        if self.end_spin.value()<self.start_spin.value():
            self.end_spin.blockSignals(True);self.end_spin.setValue(self.start_spin.value());self.end_spin.blockSignals(False)
        self.ordered=self.build_order(self.start_spin.value(),self.end_spin.value(),self.copies_spin.value(),self.continue_check.isChecked(),self.reverse_check.isChecked())
        self._configure_page()
        pages=max(1,(len(self.ordered)+self.columns-1)//self.columns)
        correction_note=f" · поправка {self.width_correction_spin.value():+.1f} мм" if abs(self.width_correction_spin.value())>.001 else ""
        page_status=(f"Шаблон {self.page_width:.2f} × {self.page_height:.2f} мм · драйверу: {self.driver_page_width:.2f} мм по ширине{correction_note}" if self.media_layout_applied else
                     f"Шаблон {self.page_width:.2f} × {self.page_height:.2f} мм · драйверу: {self.driver_page_width:.2f} мм по ширине{correction_note} · сообщает: {self.effective_page_width:.2f} × {self.effective_page_height:.2f} мм")
        self.summary.setText(f"Этикеток: {len(self.ordered)}    Страниц: {pages}\nВарианты: {self.start_spin.value()}–{self.end_spin.value()} · копий диапазона: {self.copies_spin.value()}\n{page_status}")
        self.variation_label.setText(f"{self.available} вариантов доступно")
        self._preview_timer.start();self._sync_pages()

    def _range_changed(self,*_):self._refresh_job()

    def _toggle_advanced(self,checked):
        self.advanced_panel.setVisible(checked);self.advanced_toggle.setText("Дополнительные параметры  ▾" if checked else "Дополнительные параметры  ▸")

    def _configure_columns(self):
        self.owner.configure_column_layout()
        saved=int(self.owner.template.print_settings.get("orientation",0))
        if saved==QPageLayout.Orientation.Landscape.value:saved=90
        index=self.orientation_combo.findData(saved)
        saved_orientation=profile.get("orientation")
        if saved_orientation is not None:
            try:
                saved_orientation=int(saved_orientation)
                if saved_orientation==QPageLayout.Orientation.Landscape.value:saved_orientation=90
                orientation_index=self.orientation_combo.findData(saved_orientation)
                if orientation_index>=0:self.orientation_combo.setCurrentIndex(orientation_index)
            except (TypeError,ValueError):pass
        self._refresh_job()

    def _open_printer_settings(self):
        name=str(self.printer_combo.currentData() or "").strip()
        if name:self.printer.setPrinterName(name)
        self._configure_page()
        dialog=QPrintDialog(self.printer,self);dialog.setWindowTitle("Настройки выбранного принтера")
        if dialog.exec()==QDialog.DialogCode.Accepted:
            actual=self.printer.printerName()
            index=self.printer_combo.findData(actual)
            if index<0:self.printer_combo.addItem(actual,actual);index=self.printer_combo.findData(actual)
            self.printer_combo.blockSignals(True);self.printer_combo.setCurrentIndex(index);self.printer_combo.blockSignals(False)
            self._load_width_correction(actual);self._refresh_job();self._save_printer_settings()

    def _save_printer_settings(self):
        settings=self.owner.settings
        printer_config={"name":self.printer.printerName(),"resolution":self.printer.resolution(),
                        "color_mode":self.printer.colorMode().value,"duplex":self.printer.duplex().value,
                        "paper_source":self.printer.paperSource().value,"page_order":self.printer.pageOrder().value,
                        "collate":self.printer.collateCopies(),
                        "requested_media":{"width_mm":getattr(self,"page_width",self.owner.template.width),
                                           "height_mm":getattr(self,"page_height",self.owner.template.height),
                                           "driver_width_mm":getattr(self,"driver_page_width",self.owner.template.width),
                                           "width_correction_mm":self.width_correction_spin.value(),
                                           "orientation_degrees":getattr(self,"rotation",0)}}
        previous=self.owner.template.print_settings.get("printer",{})
        if getattr(self,"media_layout_applied",False):
            printer_config["page_layout"]=self._page_layout_config(self.printer)
        elif previous.get("page_layout"):
            # A rejected layout is the driver's old paper stock; do not replace
            # the saved template media with that stale size.
            printer_config["page_layout"]=previous["page_layout"]
        settings.setValue("printer/name",printer_config["name"]);settings.setValue("printer/resolution",printer_config["resolution"])
        settings.setValue("printer/color_mode",printer_config["color_mode"]);settings.setValue("printer/duplex",printer_config["duplex"])
        settings.setValue("printer/paper_source",printer_config["paper_source"]);settings.setValue("printer/page_order",printer_config["page_order"])
        settings.setValue("printer/collate",printer_config["collate"])
        self.owner.template.print_settings["printer"]=printer_config
        self.owner.template.print_settings["orientation"]=self.orientation_combo.currentData()
        self.owner.template.print_settings["columns"]=self.owner.label_columns
        self.owner.template.print_settings["column_gap"]=self.owner.column_gap
        path=self.owner.template_path
        if path:
            key=hashlib.sha1(str(Path(path).resolve()).encode("utf-8")).hexdigest()
            settings.setValue(f"printer/templates/{key}",json.dumps(printer_config))
        settings.sync()
        self.owner.schedule_history_change()

    def _paint_preview(self,printer):
        self._configure_page();self.render_callback(printer,self.ordered,self.columns,self.page_width,self.rotation)

    def _sync_pages(self,*_):
        if not hasattr(self,"page_spin"):return
        count=max(1,self.preview.pageCount());current=max(1,self.preview.currentPage())
        self.page_spin.blockSignals(True);self.page_spin.setRange(1,count);self.page_spin.setValue(min(current,count));self.page_spin.blockSignals(False)
        self.page_total.setText(f"из {count}")

    def _print(self):
        self.owner.settings.setValue("print/range_start",self.start_spin.value());self.owner.settings.setValue("print/range_end",self.end_spin.value())
        self.owner.settings.setValue("print/copies",self.copies_spin.value());self.owner.settings.setValue("print/orientation",self.orientation_combo.currentData())
        self.owner.settings.setValue("print/continue_sequence",self.continue_check.isChecked());self.owner.settings.sync()
        self.owner.settings.setValue("print/preflight",self.preflight_check.isChecked());self.owner.settings.sync()
        if self.preflight_check.isChecked():
            issues=self.owner.validate_print_job(self.ordered)
            if issues:
                message="Перед печатью найдены замечания:\n\n"+"\n".join(f"• {item}" for item in issues[:20])
                if len(issues)>20:message+=f"\n…и ещё {len(issues)-20}"
                message+="\n\nПродолжить печать?"
                if QMessageBox.question(self,"Проверка перед печатью",message,QMessageBox.StandardButton.Yes|QMessageBox.StandardButton.No,QMessageBox.StandardButton.No)!=QMessageBox.StandardButton.Yes:return
        self._save_printer_settings();self._configure_page()
        try:
            if not self.print_callback(self.printer,self.ordered,self.columns,self.page_width,self.rotation,
                                       self.start_spin.value(),self.end_spin.value(),self.copies_spin.value()):return
        except Exception as exc:QMessageBox.critical(self,"Ошибка печати",str(exc));return
        self.accept()

class LabelCanvas(QWidget):
    selected = Signal(int)
    selectionChanged = Signal(object)
    elementDoubleClicked = Signal(int)
    contextRequested = Signal(int, object)
    moved = Signal()
    zoomChanged = Signal(float)

    def __init__(self, template: LabelTemplate):
        super().__init__()
        self.template = template
        self.selected_index = -1
        self.selected_indices:set[int]=set()
        self.selection_anchor=-1
        self.show_grid = True
        self.show_guides = True
        self.preview_row: dict[str, Any] = {}
        # Repainting is frequent while editing. Keep decoded assets and generated
        # symbols around so paintEvent never repeats expensive image/barcode work.
        self._asset_image_cache: OrderedDict[str, QImage] = OrderedDict()
        self._svg_renderer_cache: OrderedDict[str, QSvgRenderer] = OrderedDict()
        self._code_image_cache: OrderedDict[tuple, QImage | None] = OrderedDict()
        self.scale = 8.0
        self.zoom_factor=1.0
        self.pan_offset=QPointF(0,0)
        self.pan_start=None
        self.pan_mode=False
        self.drag_offset: tuple[float, float] | None = None
        self.drag_start: tuple[float, float, float, float, float] | None = None
        self.group_drag_start=None
        self.marquee_start:QPointF|None=None
        self.marquee_current:QPointF|None=None
        self.drag_guide: int | None = None
        self.resize_data: tuple[str,float,float,float,float,float,float,float] | None = None
        self.alignment_x: float | None = None
        self.alignment_y: float | None = None
        self.setMinimumSize(560, 430)
        self.setMouseTracking(True)
        self.setFocusPolicy(Qt.FocusPolicy.StrongFocus)

    def paintEvent(self, _event):
        p = QPainter(self)
        p.setRenderHint(QPainter.RenderHint.Antialiasing)
        p.fillRect(self.rect(), QColor(BG))
        fit_scale = min((self.width() - 100) / max(self.template.width, 1),
                        (self.height() - 90) / max(self.template.height, 1), 12)
        fit_scale = max(2.5, fit_scale)
        scale=fit_scale*self.zoom_factor
        self.scale = scale
        w, h = self.template.width * scale, self.template.height * scale
        x0, y0 = (self.width() - w) / 2+self.pan_offset.x(), (self.height() - h) / 2+self.pan_offset.y()
        self.origin = (x0, y0)
        label = QRectF(x0, y0, w, h)
        p.setPen(QPen(QColor("#c8cdd5"), 1))
        p.setBrush(QColor(self.template.background))
        p.drawRoundedRect(label, 4, 4)
        if self.template.background_image and self.template.background_image_visible:
            try:
                bg_img=QImage.fromData(base64.b64decode(self.template.background_image))
                if not bg_img.isNull():
                    target=QRectF(label)
                    if self.template.background_image_fit=="contain":
                        ratio=min(label.width()/bg_img.width(),label.height()/bg_img.height())
                        iw,ih=bg_img.width()*ratio,bg_img.height()*ratio
                        target=QRectF(label.center().x()-iw/2,label.center().y()-ih/2,iw,ih)
                    p.save();p.setOpacity(min(1,max(0,self.template.background_image_opacity)));p.drawImage(target,bg_img);p.restore()
            except Exception: pass
        p.save()
        if self.show_grid and self.template.grid > 0:
            step = max(self.template.grid * scale, 3)
            p.setPen(QPen(QColor("#dce1e8"), .6))
            xx = x0
            while xx < x0 + w:
                p.drawLine(int(xx), int(y0), int(xx), int(y0 + h)); xx += step
            yy = y0
            while yy < y0 + h:
                p.drawLine(int(x0), int(yy), int(x0 + w), int(yy)); yy += step
        for i, el in enumerate(self.template.elements):
            r = QRectF(x0 + el.x * scale, y0 + el.y * scale, el.width * scale, el.height * scale)
            p.save(); p.translate(r.center()); p.rotate(el.rotation); p.translate(-r.center())
            self._draw_element(p, el, r, scale)
            if i in self.selected_indices or i==self.selected_index:
                p.setPen(QPen(QColor(ACCENT), 1.5, Qt.PenStyle.DashLine))
                p.setBrush(Qt.BrushStyle.NoBrush)
                p.drawRect(r)
                if i==self.selected_index and len(self.selected_indices)<=1 and not el.layer_locked:
                    p.setPen(QPen(QColor(ACCENT),1)); p.setBrush(QColor("#ffffff"))
                    for point in self._handle_points(r): p.drawRect(QRectF(point.x()-3.5,point.y()-3.5,7,7))
                elif i==self.selected_index and el.layer_locked:
                    p.setPen(QColor("#b42318"));p.drawText(QPointF(r.left(),r.top()-5),"LOCKED")
                if self.show_guides:
                    p.setPen(QPen(QColor(ACCENT + "88"), 1, Qt.PenStyle.DotLine))
                    p.drawLine(int(r.center().x()), int(y0), int(r.center().x()), int(y0 + h))
                    p.drawLine(int(x0), int(r.center().y()), int(x0 + w), int(r.center().y()))
            p.restore()
        if self.marquee_start is not None and self.marquee_current is not None:
            marquee=QRectF(self.marquee_start,self.marquee_current).normalized()
            p.setPen(QPen(QColor(ACCENT),1,Qt.PenStyle.DashLine));p.setBrush(QColor(65,105,225,35));p.drawRect(marquee)
        if self.show_guides:
            p.setPen(QPen(QColor("#d8345f"), 2.0, Qt.PenStyle.SolidLine))
            for guide in self.template.guides:
                if guide["orientation"] == "vertical":
                    gx = x0 + float(guide["position"]) * scale
                    p.drawLine(int(gx), int(y0), int(gx), int(y0 + h))
                else:
                    gy = y0 + float(guide["position"]) * scale
                    p.drawLine(int(x0), int(gy), int(x0 + w), int(gy))
            if self.alignment_x is not None:
                gx=x0+self.alignment_x*scale
                self._draw_alignment_line(p,QPointF(gx,y0),QPointF(gx,y0+h),f"X {self.alignment_x:.3f} мм",QPointF(gx+5,y0+5))
            if self.alignment_y is not None:
                gy=y0+self.alignment_y*scale
                self._draw_alignment_line(p,QPointF(x0,gy),QPointF(x0+w,gy),f"Y {self.alignment_y:.3f} мм",QPointF(x0+5,gy+5))
        p.restore()
        p.setPen(QColor(MUTED)); p.setFont(QFont("Segoe UI", 9))
        p.drawText(QRectF(x0, y0 + h + 9, w, 20), Qt.AlignmentFlag.AlignLeft,
                   f"{self.template.width:.3f} × {self.template.height:.3f} мм")
        p.end()

    def contextMenuEvent(self,event):
        ox,oy=getattr(self,"origin",(0,0));point=QPointF(event.pos())
        target=-1
        for index in range(len(self.template.elements)-1,-1,-1):
            element=self.template.elements[index]
            rect=QRectF(ox+element.x*self.scale,oy+element.y*self.scale,element.width*self.scale,element.height*self.scale)
            if rect.contains(self._unrotate(point,rect,element.rotation)):
                target=index;break
        if target>=0:
            if target not in self.selected_indices:
                self.selected_index=target;self.selected_indices={target}
                self.selected.emit(target);self.selectionChanged.emit(set(self.selected_indices));self.update()
            self.contextRequested.emit(target,event.globalPos());event.accept();return
        super().contextMenuEvent(event)

    def _fit_scale(self):
        return max(2.5,min((self.width()-100)/max(self.template.width,1),(self.height()-90)/max(self.template.height,1),12))

    def zoom_by(self,factor,anchor=None):
        anchor=anchor or QPointF(self.width()/2,self.height()/2)
        old_scale=self.scale or self._fit_scale()*self.zoom_factor
        old_origin=getattr(self,"origin",((self.width()-self.template.width*old_scale)/2,(self.height()-self.template.height*old_scale)/2))
        world_x=(anchor.x()-old_origin[0])/old_scale;world_y=(anchor.y()-old_origin[1])/old_scale
        self.zoom_factor=min(8.0,max(.25,self.zoom_factor*factor))
        new_scale=self._fit_scale()*self.zoom_factor
        centered_x=(self.width()-self.template.width*new_scale)/2;centered_y=(self.height()-self.template.height*new_scale)/2
        self.pan_offset=QPointF(anchor.x()-world_x*new_scale-centered_x,anchor.y()-world_y*new_scale-centered_y)
        self.zoomChanged.emit(self.zoom_factor);self.update()

    def reset_view(self):
        self.zoom_factor=1.0;self.pan_offset=QPointF(0,0);self.zoomChanged.emit(self.zoom_factor);self.update()

    def wheelEvent(self,event):
        steps=event.angleDelta().y()/120
        if steps:self.zoom_by(1.18**steps,event.position())
        event.accept()

    def keyPressEvent(self,event):
        if event.key()==Qt.Key.Key_Space:
            self.pan_mode=True;self.setCursor(Qt.CursorShape.OpenHandCursor);event.accept();return
        super().keyPressEvent(event)

    def keyReleaseEvent(self,event):
        if event.key()==Qt.Key.Key_Space:
            self.pan_mode=False
            if self.pan_start is None:self.unsetCursor()
            event.accept();return
        super().keyReleaseEvent(event)

    @staticmethod
    def _draw_alignment_line(painter,start,end,label,label_pos):
        painter.save()
        painter.setPen(QPen(QColor("#102a43"),5,Qt.PenStyle.SolidLine,Qt.PenCapStyle.SquareCap))
        painter.drawLine(start,end)
        painter.setPen(QPen(QColor("#00b8d9"),2.5,Qt.PenStyle.SolidLine,Qt.PenCapStyle.SquareCap))
        painter.drawLine(start,end)
        painter.setFont(QFont("Segoe UI",8,QFont.Weight.DemiBold))
        bounds=QRectF(painter.fontMetrics().boundingRect(label)).adjusted(-5,-2,5,2)
        bounds.moveTopLeft(label_pos)
        painter.setPen(Qt.PenStyle.NoPen); painter.setBrush(QColor("#102a43")); painter.drawRoundedRect(bounds,3,3)
        painter.setPen(QColor("#ffffff")); painter.drawText(bounds,Qt.AlignmentFlag.AlignCenter,label)
        painter.restore()

    def _draw_element(self, p: QPainter, el: Element, r: QRectF, scale: float):
        if el.kind=="image":
            encoded=self.resolve(el.value) if el.value.startswith("{") else el.asset_data
            if not encoded:encoded=el.asset_data
            image=self.decoded_asset(encoded)
            if not image.isNull():p.drawImage(r,image)
            else:p.drawRect(r)
            return
        if el.kind=="pdf":
            try:
                resolved=self.resolve(el.value)
                encoded=resolved if el.value.startswith("{") and resolved else el.asset_data
                image=self.decoded_asset(encoded)
                if not image.isNull():p.drawImage(r,image)
                else:p.drawRect(r)
            except Exception:p.drawRect(r)
            return
        if el.kind=="svg":
            try:
                renderer=self.svg_renderer(el.asset_data)
                if renderer.isValid():renderer.render(p,r)
                else:p.drawRect(r)
            except Exception:p.drawRect(r)
            return
        if el.kind in ("text","symbol"):
            p.save()
            p.translate(r.left(),r.top());p.scale(scale,scale)
            draw_text_layout(p,el,QRectF(0,0,el.width,el.height),self.resolve(el.value))
            p.restore()
            return
        if el.kind in ("line","shape"):
            self._draw_vector_element(p,el,r,scale); return
        image = self.code_image(el)
        if image:
            if el.kind == "barcode": self._draw_barcode(p, el, r, image, scale, preview=True)
            else: p.drawImage(r, image)
        else:
            p.setPen(QPen(QColor("#31363d"), 1))
            if el.kind in ("qr", "datamatrix"):
                p.fillRect(r, QColor("#ffffff")); p.drawRect(r)
                p.setPen(QColor("#7e8793")); p.setFont(QFont("Segoe UI", max(7, int(min(r.width(),r.height())/6))))
                p.drawText(r, Qt.AlignmentFlag.AlignCenter, "QR" if el.kind == "qr" else "DM")
            elif el.kind == "barcode":
                for i in range(70):
                    if (i * 17 + i // 3) % 5 in (0, 2):
                        xx = r.left() + r.width() * i / 70
                        p.drawLine(int(xx), int(r.top()), int(xx), int(r.bottom()))
            else:
                p.drawRect(r); p.drawLine(r.topLeft(), r.bottomRight()); p.drawLine(r.topRight(), r.bottomLeft())

    @staticmethod
    def _draw_vector_element(painter,el,rect,scale=1):
        styles={"solid":Qt.PenStyle.SolidLine,"dash":Qt.PenStyle.DashLine,"dot":Qt.PenStyle.DotLine}
        pen=QPen(QColor(el.color)); pen.setWidthF(max(.1,el.line_width*scale)); pen.setStyle(styles.get(el.line_style,Qt.PenStyle.SolidLine))
        painter.save(); painter.setPen(pen)
        painter.setBrush(QColor(el.fill_color) if el.fill_enabled and el.kind=="shape" else Qt.BrushStyle.NoBrush)
        if el.kind=="line":
            painter.drawLine(QPointF(rect.left(),rect.center().y()),QPointF(rect.right(),rect.center().y()))
        elif el.shape_type=="ellipse": painter.drawEllipse(rect)
        elif el.shape_type=="triangle":
            from PySide6.QtGui import QPolygonF
            painter.drawPolygon(QPolygonF([rect.topLeft()+QPointF(rect.width()/2,0),rect.bottomRight(),QPointF(rect.left(),rect.bottom())]))
        elif el.shape_type=="diamond":
            from PySide6.QtGui import QPolygonF
            painter.drawPolygon(QPolygonF([QPointF(rect.center().x(),rect.top()),QPointF(rect.right(),rect.center().y()),QPointF(rect.center().x(),rect.bottom()),QPointF(rect.left(),rect.center().y())]))
        elif el.shape_type=="rounded": painter.drawRoundedRect(rect,min(rect.width(),rect.height())*.12,min(rect.width(),rect.height())*.12)
        else: painter.drawRect(rect)
        painter.restore()

    def resolve(self, value: str) -> str:
        return resolve_template_value(value, self.preview_row)

    @staticmethod
    def _text_flags(el):
        horizontal={"left":Qt.AlignmentFlag.AlignLeft,"center":Qt.AlignmentFlag.AlignHCenter,"right":Qt.AlignmentFlag.AlignRight}.get(el.horizontal_alignment,Qt.AlignmentFlag.AlignLeft)
        vertical={"top":Qt.AlignmentFlag.AlignTop,"center":Qt.AlignmentFlag.AlignVCenter,"bottom":Qt.AlignmentFlag.AlignBottom}.get(el.vertical_alignment,Qt.AlignmentFlag.AlignVCenter)
        return horizontal | vertical

    def _draw_barcode(self,painter,el,rect,image,scale,preview=False):
        position=el.hri_position
        if position == "hidden":
            painter.drawImage(rect,image); return
        inside=position in ("inside_top","inside_bottom","inside_center")
        caption_mm=max(1.5,(el.hri_font_size * 25.4 / 72) * (1.45 if preview else 1.35))
        caption_height=min(rect.height()*.32,caption_mm*(scale if preview else 1))
        gap=min(.45*(scale if preview else 1),rect.height()*.035)
        if inside:barcode_rect=rect
        elif position == "top": barcode_rect=QRectF(rect.left(),rect.top()+caption_height+gap,rect.width(),max(1,rect.height()-caption_height-gap))
        elif position == "bottom": barcode_rect=QRectF(rect.left(),rect.top(),rect.width(),max(1,rect.height()-caption_height-gap))
        elif position == "both": barcode_rect=QRectF(rect.left(),rect.top()+caption_height+gap,rect.width(),max(1,rect.height()-caption_height*2-gap*2))
        else: barcode_rect=rect
        painter.save(); painter.setClipRect(rect); painter.drawImage(barcode_rect,image)
        text=self.resolve(el.value)
        font=QFont("Arial")
        wanted=round(el.hri_font_size*96/72*scale/3.78) if preview else round(el.hri_font_size*25.4/72)
        available=caption_height
        font.setPixelSize(max(1,min(wanted,round(available*.72))))
        if inside:
            max_text_width=max(1,rect.width()-4);metrics=QFontMetricsF(font)
            while metrics.horizontalAdvance(text)>max_text_width and font.pixelSize()>1:
                font.setPixelSize(font.pixelSize()-1);metrics=QFontMetricsF(font)
            text_width=min(max_text_width,metrics.horizontalAdvance(text)+4);text_height=min(caption_height,metrics.height()+2)
            x={"left":rect.left()+2,"center":rect.center().x()-text_width/2,"right":rect.right()-text_width-2}.get(el.hri_alignment,rect.center().x()-text_width/2)
            y={"inside_top":rect.top()+1,"inside_bottom":rect.bottom()-text_height-1,"inside_center":rect.center().y()-text_height/2}[position]
            label_rect=QRectF(x,y,text_width,text_height)
            painter.setPen(Qt.PenStyle.NoPen);painter.setBrush(QColor(255,255,255,235));painter.drawRoundedRect(label_rect,1.2,1.2)
            painter.setFont(font);painter.setPen(QColor(el.color));painter.drawText(label_rect,Qt.AlignmentFlag.AlignCenter,text)
            painter.restore();return
        painter.setFont(font); painter.setPen(QColor(el.color))
        flags={"left":Qt.AlignmentFlag.AlignLeft,"center":Qt.AlignmentFlag.AlignHCenter,"right":Qt.AlignmentFlag.AlignRight}.get(el.hri_alignment,Qt.AlignmentFlag.AlignHCenter)|Qt.AlignmentFlag.AlignVCenter
        if position in ("top","both"):
            painter.drawText(QRectF(rect.left(),rect.top(),rect.width(),caption_height),flags,text)
        if position in ("bottom","both"):
            y=rect.bottom()-caption_height
            painter.drawText(QRectF(rect.left(),y,rect.width(),caption_height),flags,text)
        painter.restore()

    @staticmethod
    def _cache_put(cache, key, value, limit):
        cache[key] = value
        cache.move_to_end(key)
        while len(cache) > limit:
            cache.popitem(last=False)
        return value

    def decoded_asset(self, encoded: str) -> QImage:
        if not encoded:
            return QImage()
        cached = self._asset_image_cache.get(encoded)
        if cached is not None:
            self._asset_image_cache.move_to_end(encoded)
            return cached
        try:
            image = QImage.fromData(base64.b64decode(encoded))
        except Exception:
            image = QImage()
        return self._cache_put(self._asset_image_cache, encoded, image, 16)

    def svg_renderer(self, encoded: str) -> QSvgRenderer:
        renderer = self._svg_renderer_cache.get(encoded)
        if renderer is not None:
            self._svg_renderer_cache.move_to_end(encoded)
            return renderer
        try:
            renderer = QSvgRenderer(QByteArray(base64.b64decode(encoded)))
        except Exception:
            renderer = QSvgRenderer()
        return self._cache_put(self._svg_renderer_cache, encoded, renderer, 16)

    def code_image(self, el: Element) -> QImage | None:
        text = self.resolve(el.value) or "SAMPLE"
        if el.kind == "datamatrix" and el.gs1:
            text = normalize_gs1_payload(text)
        cache_key = (el.kind, el.barcode_type, text, bool(el.gs1))
        if cache_key in self._code_image_cache:
            self._code_image_cache.move_to_end(cache_key)
            return self._code_image_cache[cache_key]
        try:
            if el.kind == "qr":
                import qrcode
                qr=qrcode.QRCode(border=0,box_size=5)
                qr.add_data(text);qr.make(fit=True)
                pil=qr.make_image(fill_color="black",back_color="white").convert("RGB")
            elif el.kind == "datamatrix":
                from pystrich.datamatrix import DataMatrixData, DataMatrixEncoder, FNC1
                text=text.replace("<GS>","\x1d")
                payload = DataMatrixData(FNC1, text, encoding="ascii") if el.gs1 else DataMatrixData(text, auto_encoding=True)
                image = QImage.fromData(DataMatrixEncoder(payload,quiet_zone=0).get_imagedata(cellsize=5))
                result = image if not image.isNull() else None
                return self._cache_put(self._code_image_cache, cache_key, result, 96)
            else:
                import barcode
                from barcode.writer import ImageWriter
                from io import BytesIO
                from PIL import Image
                image_bytes = BytesIO()
                symbology = {"Code 128": "code128", "Code 39": "code39", "EAN-13": "ean13", "UPC-A": "upca", "ITF": "itf"}.get(el.barcode_type, "code128")
                barcode.get(symbology, text, writer=ImageWriter()).write(image_bytes,
                    options={"module_height": 12, "quiet_zone": 0, "margin_top": 0, "margin_bottom": 0,
                             "font_size": 0, "text_distance": 0, "write_text": False})
                pil = Image.open(image_bytes).convert("RGB")
            from io import BytesIO
            buf = BytesIO(); pil.save(buf, format="PNG")
            image = QImage.fromData(buf.getvalue())
            result = image if not image.isNull() else None
            return self._cache_put(self._code_image_cache, cache_key, result, 96)
        except Exception:
            return self._cache_put(self._code_image_cache, cache_key, None, 96)

    def mousePressEvent(self, event):
        if event.button()==Qt.MouseButton.MiddleButton or (event.button()==Qt.MouseButton.LeftButton and self.pan_mode):
            self.pan_start=(event.position(),QPointF(self.pan_offset));self.setCursor(Qt.CursorShape.ClosedHandCursor);event.accept();return
        if event.button() == Qt.MouseButton.RightButton and self.show_guides:
            ox,oy=getattr(self,"origin",(0,0))
            for i in range(len(self.template.guides)-1,-1,-1):
                guide=self.template.guides[i]
                delta=abs(event.position().x()-(ox+float(guide["position"])*self.scale)) if guide["orientation"]=="vertical" else abs(event.position().y()-(oy+float(guide["position"])*self.scale))
                if delta<=7:
                    self.template.guides.pop(i); self.update(); return
            return
        if event.button() != Qt.MouseButton.LeftButton:
            return
        ox, oy = getattr(self, "origin", (0, 0)); scale = self.scale
        if len(self.selected_indices)<=1 and 0 <= self.selected_index < len(self.template.elements):
            el=self.template.elements[self.selected_index]
            if not el.layer_locked:
                selected_rect=QRectF(ox+el.x*scale,oy+el.y*scale,el.width*scale,el.height*scale)
                local=self._unrotate(event.position(),selected_rect,el.rotation)
                handle=self._hit_resize_handle(local,selected_rect)
                if handle:
                    self.resize_data=(handle,event.position().x(),event.position().y(),el.x,el.y,el.width,el.height,el.rotation)
                    self.drag_start=None; self.drag_offset=None; return
        for i in range(len(self.template.elements) - 1, -1, -1):
            el = self.template.elements[i]
            r = QRectF(ox + el.x * scale, oy + el.y * scale, el.width * scale, el.height * scale)
            local = self._unrotate(event.position(), r, el.rotation)
            if r.contains(local):
                modifiers=event.modifiers();control=bool(modifiers & Qt.KeyboardModifier.ControlModifier);shift=bool(modifiers & Qt.KeyboardModifier.ShiftModifier)
                if shift:
                    anchor=self.selection_anchor if self.selection_anchor>=0 else i
                    self.selected_indices.update(range(min(anchor,i),max(anchor,i)+1))
                elif control:
                    if i in self.selected_indices:self.selected_indices.remove(i)
                    else:self.selected_indices.add(i)
                    self.selection_anchor=i
                else:
                    if i not in self.selected_indices:self.selected_indices={i}
                    self.selection_anchor=i
                if i in self.selected_indices:self.selected_index=i
                elif self.selected_indices:self.selected_index=max(self.selected_indices)
                else:self.selected_index=-1
                self.selected.emit(self.selected_index);self.selectionChanged.emit(set(self.selected_indices))
                self.group_drag_start=(event.position(),{j:(self.template.elements[j].x,self.template.elements[j].y)
                                       for j in self.selected_indices if not self.template.elements[j].layer_locked}) if i in self.selected_indices else None
                self.drag_start=None;self.drag_offset=(0,0);self.update();self.setFocus();return
        if self.show_guides:
            for i in range(len(self.template.guides) - 1, -1, -1):
                guide = self.template.guides[i]
                delta = abs(event.position().x() - (ox + float(guide["position"]) * scale)) if guide["orientation"] == "vertical" else abs(event.position().y() - (oy + float(guide["position"]) * scale))
                if delta <= 7:
                    self.drag_guide = i; return
        self.marquee_start=event.position();self.marquee_current=event.position()
        self.selected_index = -1; self.selected.emit(-1);self.update()
        self.setFocus()

    def mouseMoveEvent(self, event):
        if self.pan_start is not None:
            start,offset=self.pan_start;delta=event.position()-start
            self.pan_offset=QPointF(offset.x()+delta.x(),offset.y()+delta.y());self.update();return
        if self.marquee_start is not None and event.buttons() & Qt.MouseButton.LeftButton:
            self.marquee_current=event.position();self.update();return
        if self.drag_guide is not None:
            ox, oy = self.origin; guide = self.template.guides[self.drag_guide]
            raw = (event.position().x() - ox) / self.scale if guide["orientation"] == "vertical" else (event.position().y() - oy) / self.scale
            limit = self.template.width if guide["orientation"] == "vertical" else self.template.height
            guide["position"] = round(min(max(raw, 0), limit), 3); self.update(); return
        if self.resize_data is not None and 0 <= self.selected_index < len(self.template.elements) and not self.template.elements[self.selected_index].layer_locked:
            self._resize_selected(event.position()); self.moved.emit(); self.update(); return
        if self.group_drag_start is not None and event.buttons() & Qt.MouseButton.LeftButton:
            start,positions=self.group_drag_start;dx=(event.position().x()-start.x())/self.scale;dy=(event.position().y()-start.y())/self.scale
            for index,(start_x,start_y) in positions.items():
                element=self.template.elements[index]
                element.x=round(start_x+dx,3);element.y=round(start_y+dy,3)
            self.moved.emit();self.update();return
        if self.drag_start is None or self.selected_index < 0:
            return
        el = self.template.elements[self.selected_index]
        if el.layer_locked:return
        sx,sy,start_x,start_y,angle=self.drag_start
        dx=event.position().x()-sx; dy=event.position().y()-sy
        proposed_x=round(start_x+dx/self.scale,3)
        proposed_y=round(start_y+dy/self.scale,3)
        self.alignment_x=self.alignment_y=None
        if self.show_guides and not (event.modifiers() & Qt.KeyboardModifier.ControlModifier):
            proposed_x,self.alignment_x=self._snap_axis(proposed_x,el.width,el.height,el.rotation,"x")
            proposed_y,self.alignment_y=self._snap_axis(proposed_y,el.width,el.height,el.rotation,"y")
        el.x,el.y=proposed_x,proposed_y
        self.moved.emit(); self.update()

    def mouseReleaseEvent(self, event):
        if self.pan_start is not None:
            self.pan_start=None
            if self.pan_mode:self.setCursor(Qt.CursorShape.OpenHandCursor)
            else:self.unsetCursor()
            event.accept();return
        if self.marquee_start is not None:
            rect=QRectF(self.marquee_start,self.marquee_current or self.marquee_start).normalized()
            selected=set()
            for index,element in enumerate(self.template.elements):
                angle=math.radians(element.rotation);bw=abs(element.width*math.cos(angle))+abs(element.height*math.sin(angle));bh=abs(element.width*math.sin(angle))+abs(element.height*math.cos(angle))
                bounds=QRectF(element.x+element.width/2-bw/2,element.y+element.height/2-bh/2,bw,bh)
                view=QRectF(self.origin[0]+bounds.x()*self.scale,self.origin[1]+bounds.y()*self.scale,bounds.width()*self.scale,bounds.height()*self.scale)
                if rect.intersects(view):selected.add(index)
            self.selected_indices=selected;self.selected_index=max(selected) if selected else -1
            self.marquee_start=self.marquee_current=None;self.selected.emit(self.selected_index);self.selectionChanged.emit(set(selected));self.update()
        self.drag_offset = None
        self.drag_start = None
        self.group_drag_start=None
        self.drag_guide = None
        self.resize_data = None
        self.alignment_x = self.alignment_y = None
        self.update()

    def mouseDoubleClickEvent(self,event):
        if event.button()==Qt.MouseButton.LeftButton and not self.pan_mode:
            ox,oy=getattr(self,"origin",(0,0))
            for index in range(len(self.template.elements)-1,-1,-1):
                element=self.template.elements[index]
                rect=QRectF(ox+element.x*self.scale,oy+element.y*self.scale,element.width*self.scale,element.height*self.scale)
                if rect.contains(self._unrotate(event.position(),rect,element.rotation)):
                    self.selected_index=index;self.selected_indices={index};self.selected.emit(index);self.selectionChanged.emit({index});self.update()
                    if element.kind in ("text","symbol","qr","barcode","datamatrix"):self.elementDoubleClicked.emit(index)
                    event.accept();return
            self.reset_view();event.accept();return
        super().mouseDoubleClickEvent(event)

    @staticmethod
    def _handle_points(rect):
        cx,cy=rect.center().x(),rect.center().y()
        return [QPointF(rect.left(),rect.top()),QPointF(cx,rect.top()),QPointF(rect.right(),rect.top()),
                QPointF(rect.right(),cy),QPointF(rect.right(),rect.bottom()),QPointF(cx,rect.bottom()),
                QPointF(rect.left(),rect.bottom()),QPointF(rect.left(),cy)]

    def _hit_resize_handle(self,point,rect):
        for name,handle in zip(("nw","n","ne","e","se","s","sw","w"),self._handle_points(rect)):
            if math.hypot(point.x()-handle.x(),point.y()-handle.y())<=8:return name
        return ""

    def _resize_selected(self,point):
        handle,sx,sy,bx,by,bw,bh,angle=self.resize_data
        dx=point.x()-sx; dy=point.y()-sy; radians=math.radians(angle)
        dx,dy=math.cos(radians)*dx+math.sin(radians)*dy,-math.sin(radians)*dx+math.cos(radians)*dy
        dx/=self.scale; dy/=self.scale
        left=handle in ("nw","w","sw"); right=handle in ("ne","e","se")
        top=handle in ("nw","n","ne"); bottom=handle in ("sw","s","se")
        el=self.template.elements[self.selected_index]
        if left:
            nw=max(1.0,bw-dx); el.x=round(bx+bw-nw,3); el.width=round(nw,3)
        elif right: el.width=round(max(1.0,bw+dx),3)
        if top:
            nh=max(1.0,bh-dy); el.y=round(by+bh-nh,3); el.height=round(nh,3)
        elif bottom: el.height=round(max(1.0,bh+dy),3)
        if el.lock_proportions:
            ratio=bw/max(bh,.001)
            if left or right:
                el.height=round(el.width/ratio,3)
                if top:el.y=round(by+bh-el.height,3)
            else:
                el.width=round(el.height*ratio,3)
                if left:el.x=round(bx+bw-el.width,3)

    def _snap_axis(self,position,width,height,rotation,axis):
        extent=abs(width*math.cos(math.radians(rotation)))+abs(height*math.sin(math.radians(rotation))) if axis=="x" else abs(width*math.sin(math.radians(rotation)))+abs(height*math.cos(math.radians(rotation)))
        center=position+(width/2 if axis=="x" else height/2); half=extent/2
        own=(center-half,center,center+half); targets=[]
        for guide in self.template.guides:
            if (axis=="x" and guide["orientation"]=="vertical") or (axis=="y" and guide["orientation"]=="horizontal"):
                targets.append(float(guide["position"]))
        for index,other in enumerate(self.template.elements):
            if index==self.selected_index:continue
            oc=other.x+other.width/2 if axis=="x" else other.y+other.height/2
            oe=abs(other.width*math.cos(math.radians(other.rotation)))+abs(other.height*math.sin(math.radians(other.rotation))) if axis=="x" else abs(other.width*math.sin(math.radians(other.rotation)))+abs(other.height*math.cos(math.radians(other.rotation)))
            targets.extend((oc-oe/2,oc,oc+oe/2))
        best=(.8,position,None)
        for own_anchor in own:
            for target in targets:
                delta=target-own_anchor
                if abs(delta)<best[0]:best=(abs(delta),position+delta,target)
        return (round(best[1],3),best[2]) if best[2] is not None else (position,None)

    @staticmethod
    def _unrotate(point, rect, degrees):
        radians = math.radians(degrees); dx = point.x() - rect.center().x(); dy = point.y() - rect.center().y()
        return QPointF(rect.center().x() + math.cos(radians) * dx + math.sin(radians) * dy,
                       rect.center().y() - math.sin(radians) * dx + math.cos(radians) * dy)

    def keyPressEvent(self, event):
        el = self.template.elements[self.selected_index] if 0 <= self.selected_index < len(self.template.elements) else None
        if el and not el.layer_locked and event.key() in (Qt.Key.Key_Left, Qt.Key.Key_Right, Qt.Key.Key_Up, Qt.Key.Key_Down):
            step = 1.0 if event.modifiers() & Qt.KeyboardModifier.ShiftModifier else .1
            dx = step if event.key() == Qt.Key.Key_Right else -step if event.key() == Qt.Key.Key_Left else 0
            dy = step if event.key() == Qt.Key.Key_Down else -step if event.key() == Qt.Key.Key_Up else 0
            el.x = round(el.x + dx, 3); el.y = round(el.y + dy, 3)
            self.moved.emit(); self.update(); event.accept(); return
        super().keyPressEvent(event)


class LabelThumbnail(QWidget):
    def __init__(self, renderer, parent=None):
        super().__init__(parent)
        self.renderer=renderer
        self.setMinimumSize(210,145)

    def paintEvent(self,_event):
        painter=QPainter(self); painter.setRenderHint(QPainter.RenderHint.Antialiasing)
        painter.fillRect(self.rect(),QColor("#f1f4f8"))
        self.renderer(painter,QRectF(self.rect()).adjusted(10,10,-10,-10))
        painter.end()


class ImportOptionsDialog(QDialog):
    """Choose worksheet, header/data rows, CSV decoding and imported columns."""
    def __init__(self, path: str, parent=None):
        super().__init__(parent)
        self.path=Path(path); self.is_excel=self.path.suffix.lower() in (".xlsx",".xlsm")
        self.setWindowTitle("Настройки импорта данных")
        self.resize(760,600)
        self.setStyleSheet("""
            QDialog { background:#f3f5f8; color:#20242b; }
            QLabel { color:#20242b; background:transparent; }
            QCheckBox { color:#20242b; spacing:7px; }
            QSpinBox,QComboBox { color:#20242b; background:#ffffff; border:1px solid #c8d0dc; border-radius:4px; padding:5px; }
            QComboBox QAbstractItemView { background:#ffffff; color:#20242b; selection-background-color:#4169e1; selection-color:#ffffff; border:1px solid #b9c3d0; }
            QListWidget,QTableWidget { background:#ffffff; color:#20242b; alternate-background-color:#f5f7fa; selection-background-color:#dce7ff; selection-color:#172d62; border:1px solid #c8d0dc; }
            QHeaderView::section { background:#e8edf4; color:#20242b; border:0; padding:5px; }
            QPushButton { color:#20242b; background:#ffffff; border:1px solid #c8d0dc; border-radius:4px; padding:7px 12px; }
            QPushButton:hover { background:#eaf0ff; }
        """)
        root=QVBoxLayout(self)
        self.sheet_combo=QComboBox()
        self.delimiter_combo=QComboBox(); self.delimiter_combo.setEditable(True)
        self.delimiter_combo.addItem("Автоопределение", "auto")
        self.delimiter_combo.addItem("Запятая ,", ","); self.delimiter_combo.addItem("Точка с запятой ;", ";")
        self.delimiter_combo.addItem("Табуляция", "\t"); self.delimiter_combo.addItem("Вертикальная черта |", "|")
        self.delimiter_combo.addItem("Одна колонка (строка целиком)", "none")
        self.encoding_combo=QComboBox()
        for label,name in (("Автоопределение","auto"),("UTF-8","utf-8"),("UTF-8 с BOM","utf-8-sig"),("UTF-16","utf-16"),("Windows-1251 / Кириллица","cp1251"),("Windows-1252","cp1252"),("DOS-866","cp866"),("KOI8-R","koi8-r"),("ISO-8859-1","iso-8859-1")):
            self.encoding_combo.addItem(label,name)
        settings=QGridLayout(); self.sheet_label=QLabel("Лист Excel"); self.delimiter_label=QLabel("Разделитель CSV"); self.encoding_label=QLabel("Кодировка CSV")
        settings.addWidget(self.sheet_label,0,0); settings.addWidget(self.sheet_combo,0,1)
        settings.addWidget(self.delimiter_label,1,0); settings.addWidget(self.delimiter_combo,1,1)
        settings.addWidget(self.encoding_label,2,0); settings.addWidget(self.encoding_combo,2,1)
        self.header_check=QCheckBox("Первая строка содержит названия колонок"); self.header_check.setChecked(True)
        self.header_row=QSpinBox(); self.header_row.setRange(1,100000); self.header_row.setValue(1)
        self.data_row=QSpinBox(); self.data_row.setRange(1,100000); self.data_row.setValue(2)
        settings.addWidget(self.header_check,0,2); settings.addWidget(QLabel("Строка заголовка (с 1)"),1,2); settings.addWidget(self.header_row,1,3)
        settings.addWidget(QLabel("Первая строка данных (с 1)"),2,2); settings.addWidget(self.data_row,2,3)
        root.addLayout(settings)
        if self.is_excel:
            self.delimiter_combo.setEnabled(False); self.encoding_combo.setEnabled(False)
            try:
                from openpyxl import load_workbook
                book=load_workbook(path,read_only=True,data_only=True)
                active=book.active.title; self.sheet_combo.addItems(book.sheetnames); self.sheet_combo.setCurrentText(active); book.close()
            except Exception as exc:
                self.sheet_combo.addItem("Не удалось прочитать листы")
                self.error_label=QLabel(str(exc)); root.addWidget(self.error_label)
        else:
            self.sheet_combo.hide(); self.sheet_label.hide()
        if self.is_excel:
            self.delimiter_combo.hide(); self.delimiter_label.hide(); self.encoding_combo.hide(); self.encoding_label.hide()
        panels=QHBoxLayout()
        cols_panel=QVBoxLayout(); cols_panel.addWidget(QLabel("Колонки для импорта (отметьте нужные)"))
        self.columns=QListWidget(); self.columns.setMinimumWidth(230); self.columns.setWordWrap(True); self.columns.setHorizontalScrollBarPolicy(Qt.ScrollBarPolicy.ScrollBarAlwaysOff); cols_panel.addWidget(self.columns)
        panels.addLayout(cols_panel,1)
        preview_panel=QVBoxLayout(); preview_panel.addWidget(QLabel("Предпросмотр прочитанных данных"))
        self.sample=QTableWidget(0,0); self.sample.setEditTriggers(QAbstractItemView.EditTrigger.NoEditTriggers)
        self.sample.horizontalHeader().setSectionResizeMode(QHeaderView.ResizeMode.ResizeToContents); self.sample.horizontalHeader().setStretchLastSection(True)
        self.sample.verticalHeader().setDefaultSectionSize(20)
        preview_panel.addWidget(self.sample,1); panels.addLayout(preview_panel,2)
        root.addLayout(panels,1)
        self.info=QLabel(); self.info.setWordWrap(True); root.addWidget(self.info)
        self.columns.itemChanged.connect(self.refresh_data)
        buttons=QDialogButtonBox(QDialogButtonBox.StandardButton.Cancel|QDialogButtonBox.StandardButton.Ok)
        buttons.button(QDialogButtonBox.StandardButton.Ok).setText("Импортировать")
        buttons.button(QDialogButtonBox.StandardButton.Cancel).setText("Отмена")
        buttons.accepted.connect(self.accept); buttons.rejected.connect(self.reject); root.addWidget(buttons)
        for control in (self.sheet_combo,self.delimiter_combo,self.encoding_combo,self.header_row,self.data_row):
            if control.isEnabled():
                if isinstance(control,QSpinBox): control.valueChanged.connect(self.refresh_data)
                else:
                    control.currentIndexChanged.connect(self.refresh_data)
                    if control.isEditable(): control.lineEdit().editingFinished.connect(self.refresh_data)
        self.header_check.toggled.connect(self._header_toggled)
        self._raw=[]; self.headers=[]; self.rows=[]; self._initialized=False
        self.refresh_data()

    def _header_toggled(self,checked):
        self.header_row.setEnabled(checked)
        if checked and self.data_row.value()<=self.header_row.value(): self.data_row.setValue(self.header_row.value()+1)
        elif not checked and self.data_row.value()==self.header_row.value()+1: self.data_row.setValue(1)
        self.refresh_data()

    def _read_source(self):
        if self.is_excel:
            from openpyxl import load_workbook
            book=load_workbook(self.path,read_only=True,data_only=True)
            try:
                sheet=book[self.sheet_combo.currentText()]
                return [[ "" if value is None else str(value) for value in row] for row in sheet.iter_rows(values_only=True)]
            finally: book.close()
        raw=self.path.read_bytes()
        encoding=self.encoding_combo.currentData()
        if encoding=="auto":
            for candidate in ("utf-8-sig","cp1251"):
                try: content=raw.decode(candidate); encoding=candidate; break
                except UnicodeDecodeError: continue
            else: raise UnicodeError("Не удалось определить кодировку. Выберите её вручную.")
        else: content=raw.decode(encoding)
        self.detected_encoding=encoding
        delimiter_text=self.delimiter_combo.currentText()
        delimiter_map={"Автоопределение":"auto","Запятая ,":",","Точка с запятой ;":";","Табуляция":"\t","Вертикальная черта |":"|","Одна колонка (строка целиком)":"none"}
        combo_index=self.delimiter_combo.currentIndex()
        if combo_index>=0 and delimiter_text==self.delimiter_combo.itemText(combo_index):
            delimiter=self.delimiter_combo.currentData()
        else:
            delimiter=delimiter_map.get(delimiter_text,delimiter_text)
        if delimiter=="none":
            self.detected_delimiter="нет (одна колонка)"
            import io
            return [row for row in csv.reader(io.StringIO(content,newline=""),delimiter="\x00")]
        if delimiter=="auto":
            first_line=next((line.strip() for line in content.splitlines() if line.strip()),"")
            # Marking payloads are often unquoted and may contain commas or semicolons.
            # In that common one-code-per-line format, splitting corrupts the code.
            if re.match(r"^(?:\]d2)?01\d{14}",first_line,re.IGNORECASE):
                delimiter="\t" if "\t" in first_line else "none"
                self.detected_delimiter="табуляция" if delimiter=="\t" else "нет (одна колонка, код маркировки)"
                if delimiter=="\t":
                    import io
                    return [row for row in csv.reader(io.StringIO(content,newline=""),delimiter=delimiter)]
                import io
                return [row for row in csv.reader(io.StringIO(content,newline=""),delimiter="\x00")]
            sample=content[:16384]
            import io
            best=None
            for candidate in (",",";","\t","|"):
                try:
                    parsed=list(csv.reader(io.StringIO(sample,newline=""),delimiter=candidate))
                    widths=[len(row) for row in parsed if any(cell.strip() for cell in row)]
                    if not widths: continue
                    counts={width:widths.count(width) for width in set(widths)}
                    common_width,common_count=max(counts.items(),key=lambda item:(item[1],item[0]))
                    score=(common_count/len(widths),common_width)
                    if common_width>1 and score[0]>=0.8 and (best is None or score>best[0]): best=(score,candidate)
                except csv.Error: continue
            delimiter=best[1] if best else "none"
            if delimiter=="none":
                self.detected_delimiter="нет (одна колонка)"
                return [row for row in csv.reader(io.StringIO(content,newline=""),delimiter="\x00")]
        self.detected_delimiter={"\t":"табуляция",",":"запятая", ";":"точка с запятой", "|":"вертикальная черта"}.get(delimiter,delimiter)
        if delimiter=="\\t": delimiter="\t"
        import io
        return [row for row in csv.reader(io.StringIO(content,newline=""),delimiter=delimiter)]

    def refresh_data(self,*_):
        try:
            if self.header_check.isChecked() and self.data_row.value()<=self.header_row.value():
                self.data_row.blockSignals(True); self.data_row.setValue(self.header_row.value()+1); self.data_row.blockSignals(False)
            raw=self._read_source()
            if not raw: raise ValueError("Файл пуст.")
            if not self._initialized:
                self._initialized=True
                first=str(raw[0][0]).strip() if raw and raw[0] else ""
                looks_like_code=bool(re.match(r"^(?:\]d2)?01\d{14}",first,re.IGNORECASE) or (len(first)>=24 and first[:1].isdigit()))
                if not self.is_excel and self.header_check.isChecked() and looks_like_code:
                    self.header_check.blockSignals(True); self.header_check.setChecked(False); self.header_check.blockSignals(False)
                    self.header_row.setEnabled(False); self.data_row.setValue(1)
            self._raw=raw
            max_columns=max((len(row) for row in raw),default=0)
            if self.header_check.isChecked():
                header_index=min(self.header_row.value()-1,len(raw)-1)
                row=raw[header_index]
                headers=[str(row[i]).strip() if i<len(row) and str(row[i]).strip() else f"Столбец {i+1}" for i in range(max_columns)]
            else: headers=[f"Столбец {i+1}" for i in range(max_columns)]
            old_headers={self.columns.item(i).text() for i in range(self.columns.count())}
            previous={self.columns.item(i).text() for i in range(self.columns.count()) if self.columns.item(i).checkState()==Qt.CheckState.Checked}
            self.headers=headers
            self.columns.clear()
            for header in headers:
                item=QListWidgetItem(header); item.setFlags(item.flags()|Qt.ItemFlag.ItemIsUserCheckable)
                item.setCheckState(Qt.CheckState.Checked if not old_headers or header not in old_headers or header in previous else Qt.CheckState.Unchecked); self.columns.addItem(item)
            first=max(0,self.data_row.value()-1)
            if self.header_check.isChecked(): first=max(first,self.header_row.value())
            selected=[i for i in range(self.columns.count()) if self.columns.item(i).checkState()==Qt.CheckState.Checked]
            selected_headers=[headers[i] for i in selected]
            self.rows=[]
            for row in raw[first:]:
                values={headers[i]:row[i] if i<len(row) else "" for i in selected}
                if any(str(v).strip() for v in values.values()): self.rows.append(values)
            self.sample.clear(); self.sample.setColumnCount(len(selected_headers)); self.sample.setHorizontalHeaderLabels(selected_headers); self.sample.setRowCount(len(self.rows))
            for r,row in enumerate(self.rows):
                for c,header in enumerate(selected_headers): self.sample.setItem(r,c,QTableWidgetItem(str(row.get(header,""))))
            source_info=f"кодировка: {self.detected_encoding}; разделитель: {self.detected_delimiter}" if not self.is_excel else f"лист: {self.sheet_combo.currentText()}"
            self.info.setText(f"Найдено строк данных: {len(self.rows)} · выбрано колонок: {len(selected_headers)} · строк в файле: {len(raw)} · {source_info}")
        except Exception as exc:
            self._raw=[]; self.rows=[]; self.info.setText(f"Ошибка чтения: {exc}")

    def accept(self):
        selected=[self.columns.item(i).text() for i in range(self.columns.count()) if self.columns.item(i).checkState()==Qt.CheckState.Checked]
        if not selected or not self.rows:
            QMessageBox.warning(self,"Нечего импортировать","Выберите хотя бы одну колонку и проверьте номер строки начала данных.")
            return
        self.headers=selected
        super().accept()


def image_to_base64(image: QImage) -> str:
    buffer=QBuffer();buffer.open(QIODevice.OpenModeFlag.WriteOnly)
    if not image.save(buffer,"PNG"):
        buffer.close();raise ValueError("Не удалось сохранить изображение.")
    encoded=base64.b64encode(bytes(buffer.data())).decode("ascii");buffer.close()
    return encoded


class PdfPageCropCanvas(QWidget):
    def __init__(self,document: QPdfDocument,page=0,parent=None):
        super().__init__(parent);self.document=document;self.page=page;self.image=QImage();self.selection=None;self.drag_origin=None;self.draw_rect=QRectF()
        self.zoom_factor=1.0;self.pan_offset=QPointF();self.pan_start=None
        self.setMinimumSize(500,500);self.setMouseTracking(True);self.load_page(page)

    def load_page(self,page):
        self.page=page;size=self.document.pagePointSize(page);width=1200;height=max(1,round(width*size.height()/max(size.width(),1)))
        self.image=self.document.render(page,QSize(width,height));self.selection=None;self.zoom_factor=1.0;self.pan_offset=QPointF();self.update()

    def paintEvent(self,_event):
        painter=QPainter(self);painter.fillRect(self.rect(),QColor("#e8edf3"))
        if self.image.isNull():return
        scale=self._fit_scale()*self.zoom_factor
        w=self.image.width()*scale;h=self.image.height()*scale
        self.draw_rect=QRectF((self.width()-w)/2+self.pan_offset.x(),(self.height()-h)/2+self.pan_offset.y(),w,h)
        painter.drawImage(self.draw_rect,self.image);painter.setPen(QPen(QColor("#64748b"),1));painter.drawRect(self.draw_rect)
        if self.selection is not None:
            selected=QRectF(self.draw_rect.left()+self.selection.left()*scale,self.draw_rect.top()+self.selection.top()*scale,self.selection.width()*scale,self.selection.height()*scale)
            painter.setPen(QPen(QColor("#2563eb"),2));painter.setBrush(QColor(37,99,235,50));painter.drawRect(selected)

    def _image_point(self,point):
        scale=self.draw_rect.width()/max(1,self.image.width())
        x=min(max((point.x()-self.draw_rect.left())/scale,0),self.image.width())
        y=min(max((point.y()-self.draw_rect.top())/scale,0),self.image.height())
        return QPointF(x,y)

    def _fit_scale(self):
        if self.image.isNull():return 1.0
        return max(.01,min((self.width()-24)/self.image.width(),(self.height()-24)/self.image.height()))

    def zoom_by(self,factor,anchor=None):
        if self.image.isNull():return
        anchor=anchor or QPointF(self.width()/2,self.height()/2)
        old_scale=self._fit_scale()*self.zoom_factor
        world_x=(anchor.x()-self.draw_rect.left())/old_scale;world_y=(anchor.y()-self.draw_rect.top())/old_scale
        self.zoom_factor=min(8.0,max(.25,self.zoom_factor*factor));new_scale=self._fit_scale()*self.zoom_factor
        base_x=(self.width()-self.image.width()*new_scale)/2;base_y=(self.height()-self.image.height()*new_scale)/2
        self.pan_offset=QPointF(anchor.x()-world_x*new_scale-base_x,anchor.y()-world_y*new_scale-base_y)
        self.update()

    def fit_page(self):
        self.zoom_factor=1.0;self.pan_offset=QPointF();self.update()

    def wheelEvent(self,event):
        delta=event.angleDelta().y()
        if delta:self.zoom_by(1.2 if delta>0 else 1/1.2,event.position())
        event.accept()

    def mousePressEvent(self,event):
        if event.button()==Qt.MouseButton.MiddleButton:
            self.pan_start=(event.position(),QPointF(self.pan_offset));self.setCursor(Qt.CursorShape.ClosedHandCursor);event.accept();return
        if event.button()==Qt.MouseButton.LeftButton and self.draw_rect.contains(event.position()):
            self.drag_origin=self._image_point(event.position());self.selection=QRectF(self.drag_origin,self.drag_origin);self.update()

    def mouseMoveEvent(self,event):
        if self.pan_start is not None:
            start,offset=self.pan_start;delta=event.position()-start;self.pan_offset=offset+delta;self.update();return
        if self.drag_origin is not None:
            self.selection=QRectF(self.drag_origin,self._image_point(event.position())).normalized();self.update()

    def mouseReleaseEvent(self,event):
        if event.button()==Qt.MouseButton.MiddleButton and self.pan_start is not None:
            self.pan_start=None;self.unsetCursor();event.accept();return
        if self.drag_origin is not None:
            self.selection=QRectF(self.drag_origin,self._image_point(event.position())).normalized();self.drag_origin=None;self.update()

    def crop_points(self):
        if self.selection is None:return QRectF()
        size=self.document.pagePointSize(self.page)
        return QRectF(self.selection.left()*size.width()/self.image.width(),self.selection.top()*size.height()/self.image.height(),
                      self.selection.width()*size.width()/self.image.width(),self.selection.height()*size.height()/self.image.height())


class PdfRegionDialog(QDialog):
    def __init__(self,path,parent=None):
        super().__init__(parent);self.path=Path(path);self.document=QPdfDocument(self);error=self.document.load(str(self.path))
        if error!=QPdfDocument.Error.None_:raise ValueError(f"Не удалось открыть PDF: {error}")
        self.setWindowTitle("Выбрать область PDF");self.resize(1000,780)
        layout=QVBoxLayout(self);bar=QHBoxLayout();bar.addWidget(QLabel("Страница"));self.page_spin=QSpinBox();self.page_spin.setRange(1,max(1,self.document.pageCount()));bar.addWidget(self.page_spin)
        zoom_out=QPushButton("−");zoom_in=QPushButton("+");fit=QPushButton("Вписать")
        zoom_out.setToolTip("Уменьшить PDF");zoom_in.setToolTip("Увеличить PDF");fit.setToolTip("Показать страницу целиком")
        bar.addWidget(zoom_out);bar.addWidget(zoom_in);bar.addWidget(fit);bar.addStretch()
        self.hint=QLabel("Обведите элемент или этикетку: границы подстроятся по содержимому, текст и GS1/DataMatrix добавятся редактируемыми объектами.");self.hint.setWordWrap(True);bar.addWidget(self.hint);layout.addLayout(bar)
        self.canvas=PdfPageCropCanvas(self.document);layout.addWidget(self.canvas,1);self.page_spin.valueChanged.connect(lambda value:self.canvas.load_page(value-1))
        zoom_out.clicked.connect(lambda:self.canvas.zoom_by(1/1.2));zoom_in.clicked.connect(lambda:self.canvas.zoom_by(1.2));fit.clicked.connect(self.canvas.fit_page)
        buttons=QDialogButtonBox(QDialogButtonBox.StandardButton.Ok|QDialogButtonBox.StandardButton.Cancel);buttons.accepted.connect(self._accept_crop);buttons.rejected.connect(self.reject);layout.addWidget(buttons)

    def _accept_crop(self):
        rect=self.canvas.crop_points()
        if rect.width()<2 or rect.height()<2:
            QMessageBox.information(self,"Выберите элемент","Обведите элемент мышью на странице PDF.");return
        self.accept()

class PdfImportOptionsDialog(QDialog):
    def __init__(self,path,page_count,labels_per_page,width_mm,height_mm,parent=None):
        super().__init__(parent);self.setWindowTitle("Распознавание PDF-этикеток");self.setMinimumWidth(460)
        layout=QVBoxLayout(self);intro=QLabel(f"Обнаружена повторяющаяся сетка этикеток: примерно {labels_per_page} на страницу, страниц в PDF: {page_count}. Текстовый слой будет преобразован в поля шаблона, GS1-строки — в объект DataMatrix.")
        intro.setWordWrap(True);layout.addWidget(intro)
        form=QFormLayout();self.width_spin=QDoubleSpinBox();self.width_spin.setRange(5,300);self.width_spin.setDecimals(2);self.width_spin.setSuffix(" мм");self.width_spin.setValue(width_mm)
        self.height_spin=QDoubleSpinBox();self.height_spin.setRange(5,300);self.height_spin.setDecimals(2);self.height_spin.setSuffix(" мм");self.height_spin.setValue(height_mm)
        self.left_offset=QDoubleSpinBox();self.left_offset.setRange(0,50);self.left_offset.setDecimals(2);self.left_offset.setSuffix(" мм");self.left_offset.setValue(4.60)
        self.top_offset=QDoubleSpinBox();self.top_offset.setRange(0,50);self.top_offset.setDecimals(2);self.top_offset.setSuffix(" мм");self.top_offset.setValue(3.53)
        form.addRow("Ширина этикетки",self.width_spin);form.addRow("Высота этикетки",self.height_spin)
        form.addRow("Отступ от заголовка слева",self.left_offset);form.addRow("Отступ от заголовка сверху",self.top_offset);layout.addLayout(form)
        note=QLabel("Размеры и отступы можно подстроить под исходный макет. Программа извлекает текст из текстового слоя PDF; сканированные PDF без текстового слоя потребуют OCR.")
        note.setWordWrap(True);note.setStyleSheet("color:#687385");layout.addWidget(note)
        buttons=QDialogButtonBox(QDialogButtonBox.StandardButton.Ok|QDialogButtonBox.StandardButton.Cancel);buttons.accepted.connect(self.accept);buttons.rejected.connect(self.reject);layout.addWidget(buttons)


class RasterCropCanvas(QWidget):
    def __init__(self,image,parent=None):
        super().__init__(parent);self.image=image;self.selection=QRectF(0,0,image.width(),image.height());self.drag_start=None;self.drag_mode=None;self.drag_rect=QRectF();self.image_rect=QRectF()
        self.setMinimumSize(500,400);self.setMouseTracking(True)

    def paintEvent(self,_event):
        painter=QPainter(self);painter.fillRect(self.rect(),QColor("#e8edf3"))
        if self.image.isNull():return
        scale=min((self.width()-24)/self.image.width(),(self.height()-24)/self.image.height())
        w=self.image.width()*scale;h=self.image.height()*scale;self.image_rect=QRectF((self.width()-w)/2,(self.height()-h)/2,w,h)
        painter.drawImage(self.image_rect,self.image);painter.setPen(QPen(QColor("#64748b"),1));painter.drawRect(self.image_rect)
        selected=QRectF(self.image_rect.left()+self.selection.left()*scale,self.image_rect.top()+self.selection.top()*scale,self.selection.width()*scale,self.selection.height()*scale)
        painter.fillRect(QRectF(self.image_rect.left(),self.image_rect.top(),self.image_rect.width(),max(0,selected.top()-self.image_rect.top())),QColor(15,23,42,90))
        painter.fillRect(QRectF(self.image_rect.left(),selected.bottom(),self.image_rect.width(),max(0,self.image_rect.bottom()-selected.bottom())),QColor(15,23,42,90))
        painter.fillRect(QRectF(self.image_rect.left(),selected.top(),max(0,selected.left()-self.image_rect.left()),selected.height()),QColor(15,23,42,90))
        painter.fillRect(QRectF(selected.right(),selected.top(),max(0,self.image_rect.right()-selected.right()),selected.height()),QColor(15,23,42,90))
        painter.setPen(QPen(QColor("#2563eb"),2));painter.setBrush(Qt.BrushStyle.NoBrush);painter.drawRect(selected)
        cx=selected.center().x();cy=selected.center().y()
        for point in (selected.topLeft(),QPointF(cx,selected.top()),selected.topRight(),QPointF(selected.right(),cy),selected.bottomRight(),QPointF(cx,selected.bottom()),selected.bottomLeft(),QPointF(selected.left(),cy)):
            painter.setPen(QPen(QColor("#1d4ed8"),1));painter.setBrush(QColor("#ffffff"));painter.drawRect(QRectF(point.x()-5,point.y()-5,10,10))

    def _image_point(self,point):
        scale=self.image_rect.width()/max(1,self.image.width())
        return QPointF(min(max((point.x()-self.image_rect.left())/scale,0),self.image.width()),min(max((point.y()-self.image_rect.top())/scale,0),self.image.height()))

    def _screen_selection(self):
        scale=self.image_rect.width()/max(1,self.image.width())
        return QRectF(self.image_rect.left()+self.selection.left()*scale,self.image_rect.top()+self.selection.top()*scale,self.selection.width()*scale,self.selection.height()*scale)

    def _hit_handle(self,point):
        rect=self._screen_selection();cx=rect.center().x();cy=rect.center().y()
        handles={"nw":rect.topLeft(),"n":QPointF(cx,rect.top()),"ne":rect.topRight(),"e":QPointF(rect.right(),cy),"se":rect.bottomRight(),"s":QPointF(cx,rect.bottom()),"sw":rect.bottomLeft(),"w":QPointF(rect.left(),cy)}
        return next((name for name,pos in handles.items() if abs(point.x()-pos.x())<=9 and abs(point.y()-pos.y())<=9),None)

    def mousePressEvent(self,event):
        if event.button()!=Qt.MouseButton.LeftButton or not self.image_rect.contains(event.position()):return
        self.drag_start=self._image_point(event.position());self.drag_rect=QRectF(self.selection)
        self.drag_mode=self._hit_handle(event.position()) or ("move" if self._screen_selection().contains(event.position()) else "new")

    def mouseMoveEvent(self,event):
        if self.drag_start is None:
            handle=self._hit_handle(event.position()) if self.image_rect.contains(event.position()) else None
            cursors={"nw":Qt.CursorShape.SizeFDiagCursor,"se":Qt.CursorShape.SizeFDiagCursor,"ne":Qt.CursorShape.SizeBDiagCursor,"sw":Qt.CursorShape.SizeBDiagCursor,"n":Qt.CursorShape.SizeVerCursor,"s":Qt.CursorShape.SizeVerCursor,"e":Qt.CursorShape.SizeHorCursor,"w":Qt.CursorShape.SizeHorCursor}
            if handle:self.setCursor(cursors[handle])
            elif self._screen_selection().contains(event.position()):self.setCursor(Qt.CursorShape.SizeAllCursor)
            elif self.image_rect.contains(event.position()):self.setCursor(Qt.CursorShape.CrossCursor)
            else:self.unsetCursor()
            return
        point=self._image_point(event.position());rect=QRectF(self.drag_rect);minimum=2.0
        if self.drag_mode=="move":
            dx=point.x()-self.drag_start.x();dy=point.y()-self.drag_start.y()
            dx=min(max(dx,-rect.left()),self.image.width()-rect.right());dy=min(max(dy,-rect.top()),self.image.height()-rect.bottom());rect.translate(dx,dy)
        elif self.drag_mode=="new":rect=QRectF(self.drag_start,point).normalized().intersected(QRectF(0,0,self.image.width(),self.image.height()))
        else:
            x0=rect.left();x1=rect.right();y0=rect.top();y1=rect.bottom()
            if "w" in self.drag_mode:x0=min(max(point.x(),0),x1-minimum)
            if "e" in self.drag_mode:x1=max(min(point.x(),self.image.width()),x0+minimum)
            if "n" in self.drag_mode:y0=min(max(point.y(),0),y1-minimum)
            if "s" in self.drag_mode:y1=max(min(point.y(),self.image.height()),y0+minimum)
            rect=QRectF(QPointF(x0,y0),QPointF(x1,y1))
        self.selection=rect;self.update()

    def mouseReleaseEvent(self,event):
        if self.drag_start is not None:
            if self.drag_mode=="new" and (self.selection.width()<2 or self.selection.height()<2):self.selection=QRectF(self.drag_rect)
            self.drag_start=None;self.drag_mode=None;self.update()

    def cropped_image(self):return self.image.copy(self.selection.toAlignedRect().intersected(self.image.rect()))


class RasterCropDialog(QDialog):
    def __init__(self,image,parent=None):
        super().__init__(parent);self.setWindowTitle("Обрезать растровое изображение");self.resize(900,700)
        layout=QVBoxLayout(self);hint=QLabel("Перетаскивайте края и углы рамки, чтобы изменить обрезку. Перетащите область внутри рамки, чтобы переместить её.");hint.setWordWrap(True);layout.addWidget(hint)
        self.canvas=RasterCropCanvas(image);layout.addWidget(self.canvas,1)
        buttons=QDialogButtonBox(QDialogButtonBox.StandardButton.Ok|QDialogButtonBox.StandardButton.Cancel);buttons.accepted.connect(self._accept_crop);buttons.rejected.connect(self.reject);layout.addWidget(buttons)

    def _accept_crop(self):
        if self.canvas.selection.width()<2 or self.canvas.selection.height()<2:
            QMessageBox.information(self,"Выберите область","Размер области обрезки должен быть больше двух пикселей.");return
        self.accept()


class MainWindow(QMainWindow):
    def __init__(self, initial_template: LabelTemplate | None = None, initial_path: Path | None = None, editor_only: bool = False):
        super().__init__()
        self.setWindowTitle(APP)
        self.resize(1440, 900)
        self.settings=QSettings("DataMatrixPrinter","LabelStudioTemplateEditor" if editor_only else "LabelStudio")
        self.print_printer=None
        self.template = initial_template or LabelTemplate(elements=[Element()])
        self.rows: list[dict[str, Any]] = []
        self.headers: list[str] = []
        self.table_keys: list[str] = []
        self.selected_file = ""
        self.template_path: Path | None = initial_path
        self.editor_only=editor_only
        self.object_clipboard: Element | None=None
        self.object_clipboard_paste_count=0
        self.composition_blocks: list[CompositionBlock] = [CompositionBlock(None,self.template,1)]
        self.label_columns = int(self.settings.value("label_columns",1))
        self.column_gap = float(self.settings.value("column_gap",0.0))
        self.template_editors=[];self.composition_tab=None
        self.documents=[];self.document=None
        self._template_file_cache={}
        self.history_timer=QTimer(self);self.history_timer.setSingleShot(True);self.history_timer.setInterval(250);self.history_timer.timeout.connect(self._commit_history_change)
        icon_root=Path(getattr(sys,"_MEIPASS",Path(__file__).resolve().parent))
        icon_path=icon_root/"assets"/"labelstudio.ico"
        if icon_path.exists():self.setWindowIcon(QIcon(str(icon_path)))
        self._build_ui()
        self._add_shortcuts()
        self._style()
        dock_state=self.settings.value("dock_state")
        geometry=self.settings.value("window_geometry")
        if not self.editor_only and dock_state:self.restoreState(dock_state)
        if not self.editor_only and geometry:self.restoreGeometry(geometry)
        if self.editor_only:self.data_dock.hide()
        else:
            self.data_dock.setVisible(True)
            self.preview_dock.setVisible(True)
        self._sync_data_dock_floating(self.data_dock.isFloating())

    def _build_ui(self):
        toolbar = QToolBar(); toolbar.setObjectName("mainToolbar"); toolbar.setMovable(False); toolbar.setIconSize(QSizeF(18, 18).toSize()); self.addToolBar(toolbar)
        self.logo_label=QLabel(); self.logo_label.setFixedSize(20,20)
        asset_root=Path(getattr(sys,"_MEIPASS",Path(__file__).resolve().parent))
        logo_path=asset_root/"logodeveloper.svg"
        if logo_path.exists():
            logo_pixmap=QPixmap(20,20); logo_pixmap.fill(Qt.GlobalColor.transparent)
            logo_painter=QPainter(logo_pixmap); QSvgRenderer(str(logo_path)).render(logo_painter,QRectF(0,0,20,20)); logo_painter.end()
            self.logo_label.setPixmap(logo_pixmap)
        self.logo_label.setToolTip("Developer")
        toolbar.addWidget(self.logo_label)
        self.title_label = QLabel("LABEL STUDIO")
        self.title_label.setStyleSheet("font-weight:700; letter-spacing:1px; color:#263243; padding-right:25px")
        toolbar.addWidget(self.title_label)
        toolbar_buttons = [
            ("Новый", self.new_template, "＋", "Ctrl+N"),
            ("Открыть", self.open_template, "▱", "Ctrl+O"),
            ("Сохранить", self.save_template, "▣", "Ctrl+S"),
            ("Сохранить как", self.save_template_as, "▣+", "Ctrl+Shift+S"),
            ("Фон", self.set_background, "◐", "Цвет фона"),
            ("Фон этикетки…", self.set_background_image, "▧", "Добавить изображение-подложку для редактора; на печать оно не выводится"),
            ("⟲", self.rotate_label_ccw, "↶", "Повернуть этикетку против часовой стрелки"),
            ("⟳", self.rotate_label_cw, "↷", "Повернуть этикетку по часовой стрелке"),
            ("Шаблоны тиража", self.configure_composition, "▦", "Порядок и редактирование шаблонов в тираже"),
            ("Колонки ленты", self.configure_column_layout, "▤", "Разделить печатную область на физические колонки"),
            ("Печать", self.print_labels, "⎙", "Ctrl+P"),
        ]
        for text, callback, glyph, tip in toolbar_buttons:
            if self.editor_only and text in ("Печать","Шаблоны тиража","Колонки ленты"):continue
            b = QPushButton(text); b.setIcon(self.glyph_icon(glyph)); b.setToolTip(tip); b.clicked.connect(callback); toolbar.addWidget(b)
        self._build_menus()

        left = QFrame(); left.setObjectName("panel"); ll = QVBoxLayout(left)
        self.object_list = QListWidget(); self.object_list.setObjectName("objectList")
        self.object_list.setSelectionMode(QAbstractItemView.SelectionMode.ExtendedSelection)
        self.object_list.itemSelectionChanged.connect(self._list_selection_changed)
        self.object_list.setContextMenuPolicy(Qt.ContextMenuPolicy.CustomContextMenu)
        self.object_list.customContextMenuRequested.connect(self._object_list_context_menu)
        ll.addWidget(self.object_list, 1)
        layer_controls=QHBoxLayout()
        self.layer_up_btn=QPushButton("↑");self.layer_up_btn.setToolTip("Поднять слой выше");self.layer_up_btn.clicked.connect(lambda:self.move_layer(1))
        self.layer_down_btn=QPushButton("↓");self.layer_down_btn.setToolTip("Опустить слой ниже");self.layer_down_btn.clicked.connect(lambda:self.move_layer(-1))
        self.layer_lock_btn=QPushButton("🔒");self.layer_lock_btn.setToolTip("Заблокировать или разблокировать выбранный объект");self.layer_lock_btn.clicked.connect(self.toggle_layer_lock)
        for button in (self.layer_up_btn,self.layer_down_btn,self.layer_lock_btn):layer_controls.addWidget(button)
        ll.addLayout(layer_controls)
        duplicate_button=QPushButton("Дублировать объект");duplicate_button.setToolTip("Создать копию выбранного объекта со всеми его данными (Ctrl+D)");duplicate_button.clicked.connect(self.duplicate_selected_object);ll.addWidget(duplicate_button)
        add_title=QLabel("Добавить элемент");add_title.setStyleSheet("font-weight:600;color:#465266;padding-top:4px");ll.addWidget(add_title)
        self.add_buttons = QGridLayout(); self.add_buttons.setContentsMargins(0,0,0,0); self.add_buttons.setHorizontalSpacing(6); self.add_buttons.setVerticalSpacing(5)
        insert_items = [
            ("Текст","text","Текст","T",0,0,1), ("Штрихкод","barcode","123456789","▥",0,1,1),
            ("QR","qr","https://","⌗",1,0,1), ("DataMatrix","datamatrix","010460123456789021ABC","▦",1,1,1),
            ("Линия","line","","／",2,0,1), ("Фигура","shape","","□",2,1,1),
            ("Изображение","image","","▧",3,0,1), ("SVG","svg","","◇",3,1,1),
            ("Символ","symbol","★","★",4,0,2), ("Элемент PDF","pdf","","▤",5,0,2),
        ]
        for name,kind,val,glyph,row,col,span in insert_items:
            btn=QPushButton(name); btn.setIcon(self.glyph_icon(glyph)); btn.setToolTip(f"Добавить объект: {name}");btn.setMinimumHeight(36)
            if kind=="image":btn.clicked.connect(self.insert_image)
            elif kind=="svg":btn.clicked.connect(self.insert_svg)
            elif kind=="pdf":btn.clicked.connect(self.insert_pdf_element)
            else:btn.clicked.connect(lambda _=False,k=kind,v=val:self.add_element(k,v))
            self.add_buttons.addWidget(btn,row,col,1,span)
        ll.addLayout(self.add_buttons)
        self.canvas = LabelCanvas(self.template);self._connect_canvas(self.canvas)
        self.editor_tabs=QTabWidget();self.editor_tabs.setDocumentMode(True);self.editor_tabs.setTabsClosable(True);self.editor_tabs.setMovable(False)
        self.editor_tabs.tabCloseRequested.connect(self.close_document_tab)
        self.editor_tabs.currentChanged.connect(self.activate_document)
        self.editor_tabs.addTab(self.canvas,Path(self.template_path).stem if self.template_path else self.template.name)
        self.document={"template":self.template,"canvas":self.canvas,"path":self.template_path,
                       "composition":self.composition_blocks,"columns":self.label_columns,"gap":self.column_gap,
                       "undo":[],"redo":[],"last":None,"saved":None,"dirty":False}
        self.documents.append(self.document)
        self.document["last"]=self._snapshot_document()
        if self.template_path:self.document["saved"]=self.document["last"]
        new_tab_button=QToolButton();new_tab_button.setText("＋");new_tab_button.setToolTip("Новая вкладка шаблона");new_tab_button.clicked.connect(self.new_template)
        self.editor_tabs.setCornerWidget(new_tab_button,Qt.Corner.TopRightCorner)
        center = QFrame(); center.setObjectName("panel"); cl = QVBoxLayout(center)
        top = QHBoxLayout(); top.addWidget(self.section("ХОЛСТ ЭТИКЕТКИ")); top.addStretch()
        self.grid_btn = QPushButton("Сетка"); self.grid_btn.setIcon(self.glyph_icon("▦")); self.grid_btn.setCheckable(True); self.grid_btn.setChecked(True); self.grid_btn.clicked.connect(self.toggle_grid)
        self.guides_btn = QPushButton("Направляющие"); self.guides_btn.setIcon(self.glyph_icon("┆")); self.guides_btn.setToolTip("Перетаскивайте линии мышью; удаление — правая кнопка мыши"); self.guides_btn.setCheckable(True); self.guides_btn.setChecked(True); self.guides_btn.clicked.connect(self.toggle_guides)
        add_v = QPushButton("＋ V"); add_v.setIcon(self.glyph_icon("↕")); add_v.setToolTip("Добавить вертикальную направляющую"); add_v.clicked.connect(lambda: self.add_guide("vertical"))
        add_h = QPushButton("＋ H"); add_h.setIcon(self.glyph_icon("↔")); add_h.setToolTip("Добавить горизонтальную направляющую"); add_h.clicked.connect(lambda: self.add_guide("horizontal"))
        bg_settings=QPushButton("Подложка");bg_settings.setToolTip("Показать, скрыть, настроить прозрачность или удалить фоновый образец");bg_settings.clicked.connect(self.configure_background_image)
        zoom_out=QPushButton("−");zoom_out.setToolTip("Уменьшить масштаб колесом или кнопкой");zoom_out.clicked.connect(lambda:self.canvas.zoom_by(1/1.2))
        zoom_in=QPushButton("+");zoom_in.setToolTip("Увеличить масштаб колесом или кнопкой");zoom_in.clicked.connect(lambda:self.canvas.zoom_by(1.2))
        fit_view=QPushButton("Вписать");fit_view.setToolTip("Вернуть этикетку в центр и вписать в область просмотра");fit_view.clicked.connect(self.canvas.reset_view)
        self.zoom_label=QLabel("100%");self.canvas.zoomChanged.connect(lambda factor:self.zoom_label.setText(f"{factor*100:.0f}%"))
        self.canvas.setToolTip("Колесо мыши — масштаб · средняя кнопка или Space+перетаскивание — перемещение области просмотра · двойной щелчок по объекту — изменить значение, по фону — вписать этикетку")
        top.addWidget(self.grid_btn); top.addWidget(self.guides_btn); top.addWidget(add_v); top.addWidget(add_h);top.addWidget(bg_settings); top.addSpacing(14);top.addWidget(zoom_out);top.addWidget(self.zoom_label);top.addWidget(zoom_in);top.addWidget(fit_view); cl.addLayout(top); cl.addWidget(self.editor_tabs, 1)
        right = QFrame(); right.setObjectName("panel"); rl = QVBoxLayout(right)
        self.label_w = self.num(58, 1, 300); self.label_h = self.num(40, 1, 300); self.grid_size = self.num(1, .1, 20)
        form = QFormLayout(); form.setVerticalSpacing(4); form.addRow("Ширина, мм", self.label_w); form.addRow("Высота, мм", self.label_h); form.addRow("Шаг сетки, мм", self.grid_size); rl.addLayout(form)
        self.label_w.valueChanged.connect(lambda v: self.set_dimension("width", v)); self.label_h.valueChanged.connect(lambda v: self.set_dimension("height", v)); self.grid_size.valueChanged.connect(lambda v: self.set_dimension("grid", v))
        self.align_panel=QWidget(); align_grid=QGridLayout(self.align_panel); align_grid.setContentsMargins(0,0,0,0); align_grid.setHorizontalSpacing(4); align_grid.setVerticalSpacing(4)
        for text,icon,alignment,row,col in (("Влево","⇤","left",0,0),("Центр","↔","center_h",0,1),("Вправо","⇥","right",0,2),
                                           ("Вверх","⇡","top",1,0),("Центр","↕","center_v",1,1),("Вниз","⇣","bottom",1,2)):
            button=QPushButton(text); button.setIcon(self.glyph_icon(icon)); button.setToolTip(f"Выровнять объект: {text.lower()}"); button.clicked.connect(lambda _=False,a=alignment:self.align_selected(a)); align_grid.addWidget(button,row,col)
        rl.addWidget(self.align_panel)
        self.value_edit = QLineEdit(); self.value_edit.setPlaceholderText("Текст или переменная, например {GTIN:Код}")
        self.variable_button=QToolButton(); self.variable_button.setText("Переменная ▾"); self.variable_button.setPopupMode(QToolButton.ToolButtonPopupMode.InstantPopup); self.variable_menu=QMenu(self.variable_button); self.variable_button.setMenu(self.variable_menu)
        self.field_combo = QComboBox(); self.field_combo.addItem("Вручную", ""); self.field_combo.addItem("Нумерация тиража", "SEQ")
        self.x_spin = self.num(3, 0, 300); self.y_spin = self.num(3, 0, 300); self.w_spin = self.num(30, .1, 300); self.h_spin = self.num(8, .1, 300); self.font_spin = self.num(10, 1, 96)
        self.font_spin.setDecimals(0); self.font_spin.setSingleStep(1)
        self.letter_spacing_spin=self.num(0,-5,30);self.letter_spacing_spin.setDecimals(2);self.letter_spacing_spin.setSingleStep(.25);self.letter_spacing_spin.setSuffix(" pt")
        self.letter_spacing_spin.setToolTip("Положительное значение раздвигает буквы, отрицательное сближает.")
        self.line_spacing_spin=self.num(0,-5,30);self.line_spacing_spin.setDecimals(2);self.line_spacing_spin.setSingleStep(.25);self.line_spacing_spin.setSuffix(" pt")
        self.line_spacing_spin.setToolTip("Дополнительный интервал между строками; отрицательное значение уменьшает его.")
        self.proportion_check=QCheckBox("Сохранять пропорции")
        self.barcode_combo = QComboBox(); self.barcode_combo.addItems(["Code 128", "Code 39", "EAN-13", "UPC-A", "ITF"])
        self.font_family_combo=QFontComboBox(); self.font_family_combo.setCurrentFont(QFont("Arial")); self.font_family_combo.setMaximumWidth(220)
        self.bold_check=QCheckBox("Ж"); self.italic_check=QCheckBox("К"); self.underline_check=QCheckBox("Ч")
        self.bold_check.setToolTip("Полужирный"); self.italic_check.setToolTip("Курсив"); self.underline_check.setToolTip("Подчёркивание")
        self.style_box=QWidget(); style_layout=QHBoxLayout(self.style_box); style_layout.setContentsMargins(0,0,0,0); style_layout.addWidget(self.bold_check); style_layout.addWidget(self.italic_check); style_layout.addWidget(self.underline_check); style_layout.addStretch()
        self.text_color_btn=QPushButton("Цвет текста"); self.text_color_btn.setIcon(self.glyph_icon("●","#111111")); self.text_color_btn.clicked.connect(self.choose_text_color)
        self.fill_color_btn=QPushButton("Цвет заливки"); self.fill_color_btn.setIcon(self.glyph_icon("■","#ffffff")); self.fill_color_btn.clicked.connect(self.choose_fill_color)
        self.stroke_color_btn=QPushButton("Цвет контура"); self.stroke_color_btn.setIcon(self.glyph_icon("●","#20242b")); self.stroke_color_btn.clicked.connect(self.choose_stroke_color)
        self.symbol_combo=QComboBox(); self.symbol_combo.setEditable(True); self.symbol_combo.addItems(["★","☆","✓","✔","♡","♥","●","■","▲","→","←","⚠","©","®","₽","€"])
        self.shape_type_combo=QComboBox()
        for label,value in (("Прямоугольник","rectangle"),("Эллипс","ellipse"),("Треугольник","triangle"),("Ромб","diamond"),("Скруглённый прямоугольник","rounded")): self.shape_type_combo.addItem(label,value)
        self.line_width_spin=self.num(.35,.1,10)
        self.line_style_combo=QComboBox(); self.line_style_combo.addItem("Сплошная","solid"); self.line_style_combo.addItem("Пунктир","dash"); self.line_style_combo.addItem("Точки","dot")
        self.fill_check=QCheckBox("Заливка фигуры")
        self.align_h_combo=QComboBox(); self.align_h_combo.addItem("Слева","left"); self.align_h_combo.addItem("По центру","center"); self.align_h_combo.addItem("Справа","right")
        self.align_v_combo=QComboBox(); self.align_v_combo.addItem("Сверху","top"); self.align_v_combo.addItem("По центру","center"); self.align_v_combo.addItem("Снизу","bottom")
        self.hri_position_combo=QComboBox(); self.hri_position_combo.addItem("Скрыть","hidden"); self.hri_position_combo.addItem("Сверху","top"); self.hri_position_combo.addItem("Снизу","bottom"); self.hri_position_combo.addItem("Сверху и снизу","both"); self.hri_position_combo.addItem("Внутри сверху","inside_top"); self.hri_position_combo.addItem("Внутри снизу","inside_bottom"); self.hri_position_combo.addItem("Внутри по центру","inside_center")
        self.hri_align_combo=QComboBox(); self.hri_align_combo.addItem("Слева","left"); self.hri_align_combo.addItem("По центру","center"); self.hri_align_combo.addItem("Справа","right")
        self.hri_font_spin=self.num(8,4,36)
        self.dm_summary=QLabel("GTIN: —\nСерийный номер: —"); self.dm_summary.setWordWrap(True)
        self.property_tabs=QTabWidget(); self.property_tabs.setDocumentMode(True)
        def prop_tab(title):
            scroll=QScrollArea(); scroll.setWidgetResizable(True); scroll.setFrameShape(QFrame.Shape.NoFrame); scroll.setHorizontalScrollBarPolicy(Qt.ScrollBarPolicy.ScrollBarAlwaysOff)
            page=QWidget(); form=QFormLayout(page); form.setContentsMargins(7,7,9,7); form.setHorizontalSpacing(8); form.setVerticalSpacing(7); form.setRowWrapPolicy(QFormLayout.RowWrapPolicy.WrapLongRows)
            scroll.setWidget(page); self.property_tabs.addTab(scroll,title); return form
        self.content_form=prop_tab("Данные"); self.position_form=prop_tab("Размер"); self.text_form=prop_tab("Текст"); self.code_form=prop_tab("Код"); self.shape_form=prop_tab("Фигура")
        value_row=QWidget(); value_layout=QHBoxLayout(value_row); value_layout.setContentsMargins(0,0,0,0); value_layout.setSpacing(4); value_layout.addWidget(self.value_edit,1); value_layout.addWidget(self.variable_button)
        self.content_form.addRow("Значение",value_row); self.content_form.addRow("Поле таблицы",self.field_combo)
        self.position_form.addRow("X, мм", self.x_spin); self.position_form.addRow("Y, мм", self.y_spin); self.position_form.addRow("Ширина, мм", self.w_spin); self.position_form.addRow("Высота, мм", self.h_spin)
        self.position_form.addRow("",self.proportion_check)
        self.text_form.addRow("Символ",self.symbol_combo); self.text_form.addRow("Шрифт", self.font_family_combo); self.text_form.addRow("Размер, pt", self.font_spin)
        self.text_form.addRow("Интервал букв",self.letter_spacing_spin);self.text_form.addRow("Интервал строк",self.line_spacing_spin)
        self.text_form.addRow("Стиль", self.style_box); self.text_form.addRow("Цвет", self.text_color_btn)
        self.text_form.addRow("Выравнивание", self.align_h_combo); self.text_form.addRow("По вертикали", self.align_v_combo)
        self.rotation_spin = self.num(0, 0, 359.9); self.rotation_spin.setSuffix(" °")
        self.gs1_check = QCheckBox("GS1 / Честный знак")
        self.position_form.addRow("Поворот", self.rotation_spin)
        self.code_form.addRow("Формат", self.gs1_check); self.code_form.addRow("Тип штрихкода", self.barcode_combo)
        self.code_form.addRow("Номер", self.hri_position_combo); self.code_form.addRow("Выравнивание номера", self.hri_align_combo); self.code_form.addRow("Размер номера, pt", self.hri_font_spin); self.code_form.addRow("Из DataMatrix", self.dm_summary)
        self.shape_form.addRow("Форма",self.shape_type_combo); self.shape_form.addRow("Цвет контура",self.stroke_color_btn); self.shape_form.addRow("Толщина линии, мм",self.line_width_spin); self.shape_form.addRow("Стиль линии",self.line_style_combo); self.shape_form.addRow("Заливка",self.fill_check); self.shape_form.addRow("Цвет заливки",self.fill_color_btn)
        rl.addWidget(self.property_tabs,1)
        self.value_edit.textEdited.connect(lambda _text:self.change_value()); self.field_combo.currentIndexChanged.connect(self.change_field)
        self.variable_menu.aboutToShow.connect(self.rebuild_variable_menu)
        self.barcode_combo.currentTextChanged.connect(self.change_barcode_type)
        self.symbol_combo.currentTextChanged.connect(self.change_symbol)
        self.shape_type_combo.currentIndexChanged.connect(lambda _=0:self.change_prop("shape_type",self.shape_type_combo.currentData()))
        self.line_width_spin.valueChanged.connect(lambda value:self.change_prop("line_width",value))
        self.line_style_combo.currentIndexChanged.connect(lambda _=0:self.change_prop("line_style",self.line_style_combo.currentData()))
        self.fill_check.toggled.connect(lambda value:self.change_prop("fill_enabled",value))
        self.gs1_check.toggled.connect(self.change_gs1)
        self.rotation_spin.valueChanged.connect(lambda value: self.change_prop("rotation", value))
        self.proportion_check.toggled.connect(lambda value:self.change_prop("lock_proportions",value))
        self.font_family_combo.currentFontChanged.connect(lambda font: self.change_prop("font_family",font.family()))
        self.bold_check.toggled.connect(lambda value:self.change_prop("bold",value)); self.italic_check.toggled.connect(lambda value:self.change_prop("italic",value)); self.underline_check.toggled.connect(lambda value:self.change_prop("underline",value))
        self.align_h_combo.currentIndexChanged.connect(lambda _=0:self.change_prop("horizontal_alignment",self.align_h_combo.currentData()))
        self.align_v_combo.currentIndexChanged.connect(lambda _=0:self.change_prop("vertical_alignment",self.align_v_combo.currentData()))
        self.hri_position_combo.currentIndexChanged.connect(lambda _=0:self.change_prop("hri_position",self.hri_position_combo.currentData()))
        self.hri_align_combo.currentIndexChanged.connect(lambda _=0:self.change_prop("hri_alignment",self.hri_align_combo.currentData()))
        self.hri_font_spin.valueChanged.connect(lambda value:self.change_prop("hri_font_size",value))
        self.letter_spacing_spin.valueChanged.connect(lambda value:self.change_prop("letter_spacing_pt",value))
        self.line_spacing_spin.valueChanged.connect(lambda value:self.change_prop("line_spacing_pt",value))
        for s, attr in [(self.x_spin, "x"), (self.y_spin, "y"), (self.w_spin, "width"), (self.h_spin, "height"), (self.font_spin, "font_size")]:
            s.valueChanged.connect(lambda v, a=attr: self.change_prop(a, v))
        self.crop_image_btn=QPushButton("Обрезать изображение…");self.crop_image_btn.clicked.connect(self.crop_selected_image);rl.addWidget(self.crop_image_btn)
        del_btn = QPushButton("Удалить объект"); del_btn.setIcon(self.glyph_icon("×","#c83e55")); del_btn.clicked.connect(self.delete_element); rl.addWidget(del_btn)
        right.setMinimumWidth(300); left.setMinimumWidth(260); center.setMinimumSize(400,430)

        data_panel = QFrame(); data_panel.setObjectName("panel")
        data_layout=QVBoxLayout(data_panel); data_layout.setContentsMargins(10,8,10,8); data_layout.setSpacing(8)
        data_content=QWidget(); data_content.setMinimumWidth(570); dl=QVBoxLayout(data_content); dl.setContentsMargins(0,0,0,0)
        data_head = QHBoxLayout(); data_head.addWidget(self.section("ИСТОЧНИК ДАННЫХ И ТИРАЖ")); data_head.addStretch()
        self.table_float_button=QPushButton("↗ Таблица отдельно");self.table_float_button.setCheckable(True)
        self.table_float_button.setToolTip("Показать таблицу данных отдельным плавающим окном")
        data_head.addWidget(self.table_float_button)
        self.file_label = QLabel("Файл не выбран"); self.file_label.setStyleSheet(f"color:{MUTED}")
        load_btn = QPushButton("Импорт CSV / XLSX"); load_btn.setIcon(self.glyph_icon("↥")); load_btn.clicked.connect(self.load_data)
        pdf_load_btn=QPushButton("Этикетки из PDF…");pdf_load_btn.setToolTip("Распознать этикетки на страницах PDF, создать поля шаблона и загрузить вариации тиража");pdf_load_btn.clicked.connect(self.import_pdf_labels)
        self.detach_btn=QPushButton("Отвязать файл"); self.detach_btn.setIcon(self.glyph_icon("×","#c83e55")); self.detach_btn.setEnabled(False); self.detach_btn.setToolTip("Отключить источник данных и печатать макет с нумерацией."); self.detach_btn.clicked.connect(self.detach_data)
        data_head.addWidget(self.file_label); data_head.addWidget(self.detach_btn); data_head.addWidget(load_btn);data_head.addWidget(pdf_load_btn); dl.addLayout(data_head)
        self.table = QTableWidget(0, 0); self.table.setMaximumHeight(180); self.table.setToolTip("Дважды щёлкните ячейку, чтобы изменить значение. Нажмите на строку, чтобы увидеть именно эту запись на этикетке."); self.table.setEditTriggers(QAbstractItemView.EditTrigger.DoubleClicked|QAbstractItemView.EditTrigger.EditKeyPressed|QAbstractItemView.EditTrigger.AnyKeyPressed); self.table.horizontalHeader().setSectionResizeMode(QHeaderView.ResizeMode.Stretch);self.table.cellChanged.connect(self._table_cell_changed); dl.addWidget(self.table)
        self.table.cellClicked.connect(self.select_preview_row)
        bottom = QHBoxLayout(); bottom.addWidget(QLabel("Печатать строк:")); self.from_spin = QSpinBox(); self.from_spin.setMinimum(1); self.from_spin.setMaximum(999999); self.from_spin.setValue(1); self.from_spin.setEnabled(False); self.count_spin = QSpinBox(); self.count_spin.setMinimum(1); self.count_spin.setMaximum(999999); self.count_spin.setValue(1); bottom.addWidget(self.from_spin); bottom.addWidget(QLabel("Количество:")); bottom.addWidget(self.count_spin)
        bottom.addSpacing(10); bottom.addWidget(QLabel("Нумерация с:")); self.seq_start=QSpinBox(); self.seq_start.setRange(0,999999999); self.seq_start.setValue(1); bottom.addWidget(self.seq_start)
        self.seq_direction=QComboBox(); self.seq_direction.addItem("↑ Вверх",1); self.seq_direction.addItem("↓ Вниз",-1); bottom.addWidget(self.seq_direction)
        bottom.addWidget(QLabel("Разрядность:")); self.seq_width=QSpinBox(); self.seq_width.setRange(0,18); self.seq_width.setValue(0); bottom.addWidget(self.seq_width); bottom.addStretch()
        for spin in (self.from_spin,self.seq_start,self.seq_direction,self.seq_width):
            if isinstance(spin,QComboBox): spin.currentIndexChanged.connect(self.update_preview)
            else: spin.valueChanged.connect(self.update_preview)
        self.status = QLabel("Готово"); self.status.setStyleSheet(f"color:{MUTED}"); bottom.addWidget(self.status); print_btn = QPushButton("Печать тиража"); print_btn.setIcon(self.glyph_icon("⎙", "#ffffff")); print_btn.setObjectName("primary"); print_btn.clicked.connect(self.print_labels); bottom.addWidget(print_btn); dl.addLayout(bottom)
        data_layout.addWidget(data_content,1)
        preview_panel=QFrame(); preview_panel.setObjectName("previewCard"); preview_panel.setMinimumWidth(230); preview_layout=QVBoxLayout(preview_panel); preview_layout.setContentsMargins(12,8,12,10); preview_layout.setSpacing(5)
        preview_layout.addWidget(self.section("ТЕКУЩАЯ ЭТИКЕТКА"))
        self.preview_counter=QLabel("0 / 0"); self.preview_counter.setAlignment(Qt.AlignmentFlag.AlignCenter); self.preview_counter.setStyleSheet("font-size:22px;font-weight:700;color:#244cb5;")
        preview_layout.addWidget(self.preview_counter)
        self.preview_counter_caption=QLabel("текущая этикетка / всего в выбранном тираже")
        self.preview_counter_caption.setAlignment(Qt.AlignmentFlag.AlignCenter)
        self.preview_counter_caption.setStyleSheet(f"font-size:10px;color:{MUTED}")
        preview_layout.addWidget(self.preview_counter_caption)
        self.preview_thumb=LabelThumbnail(self.paint_print_preview); preview_layout.addWidget(self.preview_thumb,1)
        self.preview_label=QLabel("Загрузите таблицу или используйте нумерацию"); self.preview_label.setWordWrap(True); self.preview_label.setAlignment(Qt.AlignmentFlag.AlignCenter); self.preview_label.setStyleSheet(f"color:{MUTED}")
        preview_layout.addWidget(self.preview_label)
        preview_select=QHBoxLayout(); preview_select.addWidget(QLabel("Этикетка №"))
        self.preview_variant_spin=QSpinBox(); self.preview_variant_spin.setRange(1,1); self.preview_variant_spin.setMaximumWidth(80); self.preview_variant_spin.setToolTip("Выберите этикетку в запланированном тираже.")
        preview_select.addWidget(self.preview_variant_spin); preview_select.addStretch(); preview_layout.addLayout(preview_select)
        self.count_spin.valueChanged.connect(self.update_preview); self.preview_variant_spin.valueChanged.connect(self.update_preview)
        self.from_spin.valueChanged.connect(self._store_print_range);self.count_spin.valueChanged.connect(self._store_print_range)
        self.setCentralWidget(center)
        self.objects_dock=self._create_dock("Элементы макета",left,"objectsDock")
        self.properties_dock=self._create_dock("Свойства",right,"propertiesDock")
        self.data_dock=self._create_dock("Данные тиража",data_panel,"dataDock")
        self.preview_dock=self._create_dock("Предпросмотр тиража",preview_panel,"previewDock")
        panels_menu=self.menuBar().addMenu("Панели")
        panels_menu.addAction(self.data_dock.toggleViewAction())
        self.table_float_action=QAction("Таблица данных отдельным окном",self);self.table_float_action.setCheckable(True)
        panels_menu.addAction(self.table_float_action)
        panels_menu.addAction(self.preview_dock.toggleViewAction())
        if self.editor_only:self.data_dock.hide()
        self.addDockWidget(Qt.DockWidgetArea.LeftDockWidgetArea,self.objects_dock)
        self.addDockWidget(Qt.DockWidgetArea.RightDockWidgetArea,self.properties_dock)
        self.addDockWidget(Qt.DockWidgetArea.BottomDockWidgetArea,self.data_dock)
        self.addDockWidget(Qt.DockWidgetArea.BottomDockWidgetArea,self.preview_dock)
        self.splitDockWidget(self.data_dock,self.preview_dock,Qt.Orientation.Horizontal)
        self.table_float_button.toggled.connect(self.set_data_dock_floating)
        self.table_float_action.toggled.connect(self.set_data_dock_floating)
        self.data_dock.topLevelChanged.connect(self._sync_data_dock_floating)
        self.resizeDocks([self.objects_dock,self.properties_dock],[300,350],Qt.Orientation.Horizontal)
        self.resizeDocks([self.data_dock,self.preview_dock],[240,240],Qt.Orientation.Vertical)
        self.resizeDocks([self.data_dock,self.preview_dock],[900,300],Qt.Orientation.Horizontal)
        self.refresh_object_list(); self.select_element(0)
        self.update_preview()

    def _create_dock(self,title,widget,name):
        dock=QDockWidget(title,self); dock.setObjectName(name); dock.setWidget(widget)
        dock.setFeatures(QDockWidget.DockWidgetFeature.DockWidgetMovable|QDockWidget.DockWidgetFeature.DockWidgetFloatable)
        dock.setAllowedAreas(Qt.DockWidgetArea.AllDockWidgetAreas)
        dock.setContextMenuPolicy(Qt.ContextMenuPolicy.PreventContextMenu)
        return dock

    def set_data_dock_floating(self,floating):
        floating=bool(floating)
        if self.data_dock.isFloating()!=floating:self.data_dock.setFloating(floating)
        if floating:
            self.table.setMaximumHeight(16777215)
            self.data_dock.resize(1200,650)
            self.data_dock.show();self.data_dock.raise_();self.data_dock.activateWindow()
        else:
            self.table.setMaximumHeight(180)
            self.addDockWidget(Qt.DockWidgetArea.BottomDockWidgetArea,self.data_dock)
            self.data_dock.show()
        self._sync_data_dock_floating(floating)

    def _sync_data_dock_floating(self,floating):
        floating=bool(floating)
        if not hasattr(self,"table_float_button"):return
        self.table.setMaximumHeight(16777215 if floating else 180)
        self.table_float_button.blockSignals(True);self.table_float_button.setChecked(floating);self.table_float_button.blockSignals(False)
        self.table_float_action.blockSignals(True);self.table_float_action.setChecked(floating);self.table_float_action.blockSignals(False)

    def _connect_canvas(self,canvas):
        canvas.selectionChanged.connect(self.select_elements)
        canvas.contextRequested.connect(self._show_element_context_menu)
        canvas.moved.connect(self.refresh_properties)
        canvas.moved.connect(self.refresh_print_preview)
        canvas.elementDoubleClicked.connect(self.edit_element_value)

    def _snapshot_document(self):
        composition=[{"path":block.path,"copies":block.copies,"template":asdict(block.template)} for block in self.composition_blocks]
        return json.dumps({"template":asdict(self.template),"composition":composition,
                           "columns":self.label_columns,"gap":self.column_gap},ensure_ascii=False,sort_keys=True)

    def schedule_history_change(self):
        if self.document:self.history_timer.start()

    def _commit_history_change(self):
        doc=self.document
        if not doc:return
        current=self._snapshot_document()
        previous=doc.get("last")
        if current==previous:return
        if previous is not None:
            doc["undo"].append(previous)
            del doc["undo"][:-100]
        doc["redo"].clear();doc["last"]=current
        doc["template"]=self.template;doc["composition"]=self.composition_blocks
        doc["columns"]=self.label_columns;doc["gap"]=self.column_gap
        doc["dirty"]=current!=doc.get("saved")
        self._update_tab_title(doc)

    def _restore_document_snapshot(self,snapshot):
        data=json.loads(snapshot)
        self.template=self._template_from_data(data["template"])
        self.document["template"]=self.template
        self.canvas=self.document["canvas"];self.canvas.template=self.template
        self.composition_blocks=[CompositionBlock(item.get("path"),self._template_from_data(item["template"]),int(item.get("copies",1))) for item in data.get("composition",[])] or [CompositionBlock(None,self.template,1)]
        self.document["composition"]=self.composition_blocks
        self.label_columns=int(data.get("columns",1));self.column_gap=float(data.get("gap",0))
        self.document["columns"]=self.label_columns;self.document["gap"]=self.column_gap
        self.canvas.selected_index=min(max(0,self.canvas.selected_index),len(self.template.elements)-1)
        for spin,value in ((self.label_w,self.template.width),(self.label_h,self.template.height),(self.grid_size,self.template.grid)):
            spin.blockSignals(True);spin.setValue(value);spin.blockSignals(False)
        self.refresh_object_list();self.select_element(self.canvas.selected_index);self.canvas.update();self.update_preview()
        self.document["last"]=snapshot;self.document["dirty"]=snapshot!=self.document.get("saved");self._update_tab_title(self.document)

    def undo_document(self):
        self.history_timer.stop();self._commit_history_change()
        if not self.document or not self.document["undo"]:return
        current=self._snapshot_document();target=self.document["undo"].pop();self.document["redo"].append(current);self._restore_document_snapshot(target)

    def redo_document(self):
        self.history_timer.stop();self._commit_history_change()
        if not self.document or not self.document["redo"]:return
        current=self._snapshot_document();target=self.document["redo"].pop();self.document["undo"].append(current);self._restore_document_snapshot(target)

    def _update_tab_title(self,doc):
        if doc not in self.documents:return
        index=self.documents.index(doc);path=doc.get("path")
        title=Path(path).stem if path else doc["template"].name
        self.editor_tabs.setTabText(index,title+(" •" if doc.get("dirty") else ""))

    def add_document_tab(self,template,path=None):
        path=Path(path) if path else None
        canvas=LabelCanvas(template);self._connect_canvas(canvas)
        canvas.selected_index=0 if template.elements else -1
        canvas.selected_indices={canvas.selected_index} if canvas.selected_index>=0 else set()
        doc={"template":template,"canvas":canvas,"path":path,
             "composition":[CompositionBlock(None,template,1)],
             "columns":int(template.print_settings.get("columns",self.settings.value("label_columns",1))),
             "gap":float(template.print_settings.get("column_gap",self.settings.value("column_gap",0.0))),
             "undo":[],"redo":[],"last":None,"saved":None,"dirty":False}
        self.documents.append(doc)
        tab_index=len(self.documents)-1
        self.editor_tabs.insertTab(tab_index,canvas,Path(path).stem if path else template.name)
        doc["last"]=self._snapshot_for_doc(template,doc["composition"],doc["columns"],doc["gap"])
        if path:doc["saved"]=doc["last"]
        self.editor_tabs.setCurrentIndex(len(self.documents)-1)

    @staticmethod
    def _snapshot_for_doc(template,composition,columns,gap):
        blocks=[{"path":block.path,"copies":block.copies,"template":asdict(block.template)} for block in composition]
        return json.dumps({"template":asdict(template),"composition":blocks,"columns":columns,"gap":gap},ensure_ascii=False,sort_keys=True)

    def activate_document(self,index):
        if not (0<=index<len(self.documents)):return
        if self.document:
            self.history_timer.stop();self._commit_history_change()
            self.document.update(template=self.template,composition=self.composition_blocks,columns=self.label_columns,gap=self.column_gap)
        doc=self.documents[index]
        if doc is self.document:return
        self.document=doc;self.template=doc["template"];self.canvas=doc["canvas"];self.template_path=doc.get("path")
        self.composition_blocks=doc["composition"];self.label_columns=doc["columns"];self.column_gap=doc["gap"]
        self.canvas.template=self.template;self.canvas.reset_view()
        for spin,value in ((self.label_w,self.template.width),(self.label_h,self.template.height),(self.grid_size,self.template.grid)):
            spin.blockSignals(True);spin.setValue(value);spin.blockSignals(False)
        self.setWindowTitle(f"{APP} — {Path(self.template_path).stem}" if self.template_path else APP)
        self.refresh_object_list();self.select_element(self.canvas.selected_index);self.update_preview()

    def close_document_tab(self,index):
        if not (0<=index<self.editor_tabs.count()):return
        if index>=len(self.documents):
            if self.composition_tab is not None:
                widget=self.composition_tab;self.composition_tab=None
                self.editor_tabs.blockSignals(True);self.editor_tabs.removeTab(index);self.editor_tabs.blockSignals(False);widget.deleteLater()
                if self.documents:self.editor_tabs.setCurrentIndex(max(0,min(self.editor_tabs.currentIndex(),len(self.documents)-1)))
            return
        doc=self.documents[index]
        if doc is self.document:
            self.history_timer.stop();self._commit_history_change()
        if doc.get("dirty"):
            answer=QMessageBox.question(self,"Несохранённый шаблон",f"Сохранить изменения в «{Path(doc['path']).stem if doc.get('path') else doc['template'].name}» перед закрытием?",QMessageBox.StandardButton.Yes|QMessageBox.StandardButton.No|QMessageBox.StandardButton.Cancel,QMessageBox.StandardButton.Yes)
            if answer==QMessageBox.StandardButton.Cancel:return
            if answer==QMessageBox.StandardButton.Yes:
                self.editor_tabs.setCurrentIndex(index);self.save_template()
                if doc.get("dirty"):return
        self.editor_tabs.blockSignals(True);self.editor_tabs.removeTab(index);self.editor_tabs.blockSignals(False)
        self.documents.pop(index)
        if not self.documents:
            self.document=None;self.new_template();return
        if doc is self.document:
            self.document=None;target=self.editor_tabs.currentIndex()
            if target>=len(self.documents):target=max(0,min(index,len(self.documents)-1));self.editor_tabs.setCurrentIndex(target)
            self.activate_document(target)

    def restore_default_docks(self):
        self.set_data_dock_floating(False)
        if self.editor_only:self.data_dock.hide()
        self.addDockWidget(Qt.DockWidgetArea.LeftDockWidgetArea,self.objects_dock)
        self.addDockWidget(Qt.DockWidgetArea.RightDockWidgetArea,self.properties_dock)
        self.addDockWidget(Qt.DockWidgetArea.BottomDockWidgetArea,self.data_dock)
        self.addDockWidget(Qt.DockWidgetArea.BottomDockWidgetArea,self.preview_dock)
        self.splitDockWidget(self.data_dock,self.preview_dock,Qt.Orientation.Horizontal)
        self.resizeDocks([self.objects_dock,self.properties_dock],[300,350],Qt.Orientation.Horizontal)
        self.resizeDocks([self.data_dock,self.preview_dock],[240,240],Qt.Orientation.Vertical)
        self.resizeDocks([self.data_dock,self.preview_dock],[900,300],Qt.Orientation.Horizontal)

    def closeEvent(self,event):
        if self.document:
            self.history_timer.stop();self._commit_history_change()
        for doc in list(self.documents):
            if not doc.get("dirty"):
                continue
            name=Path(doc["path"]).stem if doc.get("path") else doc["template"].name
            answer=QMessageBox.question(self,"Несохранённый шаблон",f"Сохранить изменения в «{name}» перед закрытием?",QMessageBox.StandardButton.Yes|QMessageBox.StandardButton.No|QMessageBox.StandardButton.Cancel,QMessageBox.StandardButton.Yes)
            if answer==QMessageBox.StandardButton.Cancel:
                event.ignore();return
            if answer==QMessageBox.StandardButton.Yes:
                index=self.documents.index(doc);self.editor_tabs.setCurrentIndex(index);self.save_template()
                if doc.get("dirty"):
                    event.ignore();return
        if not self.editor_only:
            self.settings.setValue("dock_state",self.saveState())
            self.settings.setValue("window_geometry",self.saveGeometry())
            self.settings.sync()
        super().closeEvent(event)

    def _style(self):
        self.setStyleSheet(f"""
            QMainWindow {{ background:{BG}; }} QFrame#panel {{ background:{PANEL}; border:1px solid #e1e5ea; border-radius:8px; }}
            QPushButton {{ background:#f7f8fa; border:1px solid #d9dee6; border-radius:5px; padding:7px 10px; color:{INK}; }}
            QPushButton:hover {{ background:#eaf0ff; border-color:#a9bcfa; }} QPushButton#primary {{ background:{ACCENT}; color:white; font-weight:600; border:0; padding:9px 18px; }}
            QLabel {{ color:{INK}; }} QLineEdit,QDoubleSpinBox,QSpinBox,QComboBox {{ border:1px solid #d9dee6; border-radius:4px; padding:5px; background:white; }}
            QComboBox QAbstractItemView {{ background:#ffffff; color:#20242b; selection-background-color:#4169e1; selection-color:#ffffff; border:1px solid #b9c3d0; outline:0; padding:2px; }}
            QComboBox QAbstractItemView::item {{ min-height:24px; padding:4px 8px; }} QComboBox QAbstractItemView::item:hover {{ background:#eaf0ff; color:#172d62; }}
            QAbstractItemView {{ background:#ffffff; color:#20242b; selection-background-color:#4169e1; selection-color:#ffffff; }}
            QTabWidget::pane {{ border:1px solid #e3e7ec; border-radius:5px; top:-1px; }} QTabBar::tab {{ background:#f4f6f9; color:#566273; padding:6px 9px; border:1px solid #e3e7ec; }} QTabBar::tab:selected {{ background:#eaf0ff; color:#244cb5; border-bottom-color:#eaf0ff; }}
            QListWidget,QTableWidget {{ background:#ffffff; color:#20242b; alternate-background-color:#f6f8fb; border:1px solid #e3e7ec; border-radius:5px; selection-background-color:#dce7ff; selection-color:#172d62; }}
            QListWidget::item {{ padding:8px 7px; border-bottom:1px solid #f0f2f5; }} QListWidget::item:selected {{ background:#eaf0ff; color:#172d62; border-left:3px solid {ACCENT}; }}
            QTableWidget::item {{ padding:4px; }}
            QLineEdit,QDoubleSpinBox,QSpinBox,QComboBox {{ color:#20242b; selection-color:#ffffff; selection-background-color:#4169e1; }}
            QLineEdit:disabled,QDoubleSpinBox:disabled,QSpinBox:disabled,QComboBox:disabled {{ color:#6e7784; background:#f2f4f7; }}
            QCheckBox {{ color:#20242b; spacing:6px; }}
            QScrollArea {{ background:#ffffff; border:0; }} QScrollArea QWidget {{ background:#ffffff; color:#20242b; }} QScrollArea::viewport {{ background:#ffffff; }}
            QToolBar {{ background:white; border:0; border-bottom:1px solid #dfe3e8; spacing:6px; padding:6px; }}
            QDockWidget {{ color:{INK}; font-weight:600; }} QDockWidget::title {{ background:#f7f8fa; border:1px solid #e1e5ea; padding:5px 8px; text-align:left; }}
            QMainWindow::separator {{ background:#dce2ea; width:5px; height:5px; }} QMainWindow::separator:hover {{ background:#8ea8e8; }}
            QHeaderView::section {{ background:#f5f7f9; border:0; padding:5px; }}
            QHeaderView::section {{ color:#20242b; }} QMenuBar {{ background:#ffffff; color:#20242b; }} QMenuBar::item:selected {{ background:#eaf0ff; }} QMenu {{ background:#ffffff; color:#20242b; }}
        """)

    def _build_menus(self):
        bar = self.menuBar()
        file_menu = bar.addMenu("Файл")
        file_actions=(("Новый шаблон", "Ctrl+N", self.new_template), ("Открыть шаблон…", "Ctrl+O", self.open_template), ("Сохранить шаблон", "Ctrl+S", self.save_template), ("Сохранить шаблон как…", "Ctrl+Shift+S", self.save_template_as))
        if not self.editor_only:file_actions+=(("Печать тиража…", "Ctrl+P", self.print_labels),)
        for title, key, callback in file_actions:
            action = QAction(title, self); action.setShortcut(QKeySequence(key)); action.triggered.connect(callback); file_menu.addAction(action)
        insert_menu = bar.addMenu("Вставка")
        for title, key, kind, value in (("Текст", "Ctrl+Shift+T", "text", "Текст"), ("Штрихкод", "Ctrl+Shift+B", "barcode", "123456789"), ("QR-код", "Ctrl+Shift+Q", "qr", "https://"), ("DataMatrix", "Ctrl+Shift+D", "datamatrix", "010460123456789021ABC")):
            action = QAction(title, self); action.setShortcut(QKeySequence(key)); action.triggered.connect(lambda _=False, k=kind, v=value: self.add_element(k, v)); insert_menu.addAction(action)
        insert_menu.addSeparator()
        for title,kind,value in (("Линия","line",""),("Фигура","shape",""),("Символ","symbol","★")):
            action=QAction(title,self); action.triggered.connect(lambda _=False,k=kind,v=value:self.add_element(k,v)); insert_menu.addAction(action)
        insert_menu.addSeparator()
        for title, key, orientation in (("Вертикальная направляющая", "Ctrl+Alt+V", "vertical"), ("Горизонтальная направляющая", "Ctrl+Alt+H", "horizontal")):
            action = QAction(title, self); action.setShortcut(QKeySequence(key)); action.triggered.connect(lambda _=False, o=orientation: self.add_guide(o)); insert_menu.addAction(action)
        edit_menu = bar.addMenu("Правка")
        delete_action = QAction("Удалить выбранный объект (Delete)", self); delete_action.triggered.connect(self.delete_element); edit_menu.addAction(delete_action)
        edit_menu.addAction("Поднять слой",self.raise_layer,QKeySequence("Ctrl+Up"))
        edit_menu.addAction("Опустить слой",self.lower_layer,QKeySequence("Ctrl+Down"))
        edit_menu.addAction("Заблокировать / разблокировать",self.toggle_layer_lock,QKeySequence("Ctrl+L"))
        edit_menu.addSeparator()
        edit_menu.addAction("Отменить",self.undo_document,QKeySequence("Ctrl+Z"))
        edit_menu.addAction("Повторить",self.redo_document,QKeySequence("Ctrl+Y"))
        for title,key,callback in (("Копировать объект","Ctrl+C",self.copy_selected_object),("Вставить объект","Ctrl+V",self.paste_copied_object),("Дублировать объект","Ctrl+D",self.duplicate_selected_object)):
            action=QAction(title,self);action.setShortcut(QKeySequence(key));action.triggered.connect(callback);edit_menu.addAction(action)
        edit_menu.addSeparator()
        edit_value_action=QAction("Изменить значение объекта…",self);edit_value_action.triggered.connect(lambda:self.edit_element_value(self.canvas.selected_index));edit_menu.addAction(edit_value_action)
        for title, key, callback in (("Повернуть объект на 90° против часовой", "Ctrl+Alt+Left", self.rotate_element_ccw), ("Повернуть объект на 90° по часовой", "Ctrl+Alt+Right", self.rotate_element_cw)):
            action=QAction(title,self); action.setShortcut(QKeySequence(key)); action.triggered.connect(callback); edit_menu.addAction(action)
        label_menu = bar.addMenu("Этикетка")
        for title, key, callback in (("Повернуть этикетку на 90° против часовой", "Ctrl+Shift+Alt+Left", self.rotate_label_ccw), ("Повернуть этикетку на 90° по часовой", "Ctrl+Shift+Alt+Right", self.rotate_label_cw)):
            action=QAction(title,self); action.setShortcut(QKeySequence(key)); action.triggered.connect(callback); label_menu.addAction(action)
        view_menu=bar.addMenu("Вид")
        reset_action=QAction("Восстановить расположение панелей",self); reset_action.triggered.connect(self.restore_default_docks); view_menu.addAction(reset_action)

    def _add_shortcuts(self):
        delete_shortcut = QShortcut(QKeySequence(Qt.Key.Key_Delete), self)
        delete_shortcut.setContext(Qt.ShortcutContext.WindowShortcut); delete_shortcut.activated.connect(self.delete_if_canvas_selected)

    def delete_if_canvas_selected(self):
        focus=QApplication.focusWidget()
        if isinstance(focus,(QLineEdit,QDoubleSpinBox,QSpinBox,QComboBox,QTableWidget)):
            return
        self.delete_element()

    def _object_command_has_text_focus(self):
        return isinstance(QApplication.focusWidget(),(QLineEdit,QDoubleSpinBox,QSpinBox,QComboBox,QTableWidget))

    def copy_selected_object(self):
        if self._object_command_has_text_focus():return
        index=self.canvas.selected_index
        if 0<=index<len(self.template.elements):
            self.object_clipboard=Element(**asdict(self.template.elements[index]));self.object_clipboard_paste_count=0

    def paste_copied_object(self):
        if self._object_command_has_text_focus() or self.object_clipboard is None:return
        self.object_clipboard_paste_count+=1
        self._add_object_copy(self.object_clipboard,2.0*self.object_clipboard_paste_count)

    def duplicate_selected_object(self):
        if self._object_command_has_text_focus():return
        index=self.canvas.selected_index
        if 0<=index<len(self.template.elements):self._add_object_copy(self.template.elements[index],2.0)

    def _add_object_copy(self,source,offset):
        copy=Element(**asdict(source))
        copy.layer_locked=False
        copy.x=round(min(max(0,source.x+offset),max(0,self.template.width-source.width)),3)
        copy.y=round(min(max(0,source.y+offset),max(0,self.template.height-source.height)),3)
        self.template.elements.append(copy);self.canvas.selected_index=len(self.template.elements)-1
        self.refresh_object_list();self.select_element(self.canvas.selected_index);self.canvas.update();self.canvas.setFocus();self.refresh_print_preview()

    def edit_element_value(self,index):
        if not 0<=index<len(self.template.elements):return
        element=self.template.elements[index]
        if element.kind not in ("text","symbol","qr","barcode","datamatrix"):return
        value,accepted=QInputDialog.getMultiLineText(self,"Изменить значение объекта","Текст, код или переменная:",element.value)
        if accepted:
            element.value=value;self.canvas.selected_index=index;self.select_element(index);self.canvas.update();self.refresh_print_preview()

    def _object_list_context_menu(self,position):
        item=self.object_list.itemAt(position)
        if item is None:return
        index=int(item.data(Qt.ItemDataRole.UserRole))
        if index not in self.canvas.selected_indices:self.select_elements({index})
        self._show_element_context_menu(index,self.object_list.viewport().mapToGlobal(position))

    def _show_element_context_menu(self,index,global_position):
        if not 0<=index<len(self.template.elements):return
        if index not in self.canvas.selected_indices:self.select_elements({index})
        selected=self.selected_elements();editable=[element for element in selected if element.kind in ("text","symbol","qr","barcode","datamatrix")]
        menu=QMenu(self)
        if editable:
            edit=menu.addAction("Изменить данные…")
            edit.triggered.connect(lambda:self._edit_selected_element_values(editable))
            properties=menu.addAction("Открыть свойства")
            properties.triggered.connect(lambda:self.property_tabs.setCurrentIndex(0))
            menu.addSeparator()
        menu.addAction("Копировать",self.copy_selected_object)
        menu.addAction("Дублировать",self.duplicate_selected_object)
        menu.addAction("Вставить скопированный объект",self.paste_copied_object)
        menu.addSeparator()
        menu.addAction("Заблокировать / разблокировать",self.toggle_layer_lock)
        menu.addAction("Удалить",self.delete_element)
        menu.exec(global_position)

    def _edit_selected_element_values(self,elements):
        editable=[element for element in elements if element in self.template.elements and element.kind in ("text","symbol","qr","barcode","datamatrix")]
        if not editable:return
        value,accepted=QInputDialog.getMultiLineText(self,"Изменить данные объекта","Текст, код или переменная:",editable[0].value)
        if not accepted:return
        for element in editable:element.value=value
        self.value_edit.setText(value);self.canvas.update();self.refresh_dm_summary();self.refresh_print_preview()

    def section(self, text):
        label = QLabel(text); label.setStyleSheet(f"font-size:10px; font-weight:700; letter-spacing:1px; color:{MUTED}; padding:7px 0")
        return label

    def glyph_icon(self, glyph, color=ACCENT):
        pixmap=QPixmap(24,24); pixmap.fill(Qt.GlobalColor.transparent)
        painter=QPainter(pixmap); painter.setRenderHint(QPainter.RenderHint.Antialiasing)
        font=QFont("Segoe UI Symbol", 15); font.setBold(True); painter.setFont(font); painter.setPen(QColor(color))
        painter.drawText(pixmap.rect(),Qt.AlignmentFlag.AlignCenter,glyph); painter.end()
        return QIcon(pixmap)

    def num(self, value, low, high):
        s = QDoubleSpinBox(); s.setRange(low, high); s.setDecimals(3); s.setSingleStep(.1); s.setValue(value); s.setSuffix("  "); s.setKeyboardTracking(False); return s

    def add_element(self, kind, value):
        square_code = kind in ("qr", "datamatrix")
        width=14 if square_code else 36 if kind=="barcode" else 8 if kind=="symbol" else 28 if kind=="line" else 18 if kind=="shape" else 30
        height=14 if square_code or kind=="symbol" else 2 if kind=="line" else 14 if kind=="shape" else 18 if kind=="barcode" else 6
        x,y=self._view_center_position(width,height)
        el = Element(kind=kind, x=x, y=y, gs1=(kind == "datamatrix"), width=width, height=height, value=value)
        self.template.elements.append(el); self.refresh_object_list(); self.canvas.selected_index = len(self.template.elements)-1; self.canvas.update(); self.select_element(self.canvas.selected_index); self.canvas.setFocus(); self.refresh_print_preview()

    def insert_image(self):
        path,_=QFileDialog.getOpenFileName(self,"Вставить изображение","","Изображения (*.png *.jpg *.jpeg *.bmp *.webp)")
        if path:self._insert_asset(path,"image")

    def crop_selected_image(self):
        element=self.selected_element()
        if not element or element.kind!="image":return
        try:
            image=QImage.fromData(base64.b64decode(element.asset_data))
            if image.isNull():raise ValueError("Встроенное изображение повреждено.")
            dialog=RasterCropDialog(image,self)
            if dialog.exec()!=QDialog.DialogCode.Accepted:return
            source_rect=dialog.canvas.selection.toAlignedRect().intersected(image.rect())
            cropped=image.copy(source_rect)
            if cropped.isNull():return
            old_x,old_y,old_width,old_height=element.x,element.y,element.width,element.height
            element.x=round(old_x+old_width*source_rect.left()/image.width(),3)
            element.y=round(old_y+old_height*source_rect.top()/image.height(),3)
            element.width=round(old_width*source_rect.width()/image.width(),3)
            element.height=round(old_height*source_rect.height()/image.height(),3)
            element.asset_data=image_to_base64(cropped)
            self.select_element(self.canvas.selected_index);self.canvas.update();self.refresh_print_preview()
            self.status.setText(f"Изображение пропорционально обрезано: {element.width:.2f} × {element.height:.2f} мм")
        except Exception as exc:QMessageBox.warning(self,"Не удалось обрезать изображение",str(exc))

    def insert_svg(self):
        path,_=QFileDialog.getOpenFileName(self,"Вставить SVG","","Векторные изображения (*.svg)")
        if path:self._insert_asset(path,"svg")

    def insert_pdf_element(self):
        path,_=QFileDialog.getOpenFileName(self,"Выбрать PDF","","PDF-файлы (*.pdf)")
        if not path:return
        progress=None
        try:
            dialog=PdfRegionDialog(path,self)
            if dialog.exec()!=QDialog.DialogCode.Accepted:return
            document=dialog.document;page=dialog.canvas.page;selection=dialog.canvas.crop_points()
            progress=QProgressDialog("Распознавание выделенной области PDF…","",0,0,self);progress.setCancelButton(None);progress.setWindowModality(Qt.WindowModality.ApplicationModal);progress.setMinimumDuration(0);progress.setAutoClose(False);progress.show();QApplication.processEvents()
            lines=self._pdf_region_text_lines(document,page,selection)
            codes=self._pdf_decode_codes(document,page,selection,progress_callback=lambda message:(progress.setLabelText(message),QApplication.processEvents()))
            fallback_code=self._pdf_join_code_lines(lines)
            decoded_matrix=next((code for code in codes if code["kind"]=="datamatrix"),None)
            if fallback_code and decoded_matrix and len(fallback_code.replace("<GS>",""))>len(decoded_matrix["text"].replace("<GS>","")):
                decoded_matrix["text"]=fallback_code
            elif fallback_code and not decoded_matrix:
                source=next(line for line in lines if re.search(r"01\d{14}21",re.sub(r"\s+","",normalize_gs1_payload(line["text"]))))
                size=min(selection.width()*.42,selection.height()*.6)
                codes.append({"kind":"datamatrix","text":fallback_code,"rect":QRectF(source["x"],max(selection.top(),source["y"]-size-3),size,size)})
            code_text_rects=[code["rect"] for code in codes]
            code_text_lines=self._pdf_gs1_line_indexes(lines)
            bounds=QRectF()
            for line in lines:
                rect=QRectF(line["x"],line["y"],line["width"],line["height"])
                bounds=rect if bounds.isNull() else bounds.united(rect)
            for rect in code_text_rects:bounds=rect if bounds.isNull() else bounds.united(rect)
            if bounds.isNull():bounds=QRectF(selection)
            bounds=bounds.adjusted(-1.5,-1.5,1.5,1.5).intersected(selection)
            if bounds.width()<2 or bounds.height()<2:raise ValueError("Не удалось автоматически определить границы содержимого.")
            mm_per_point=25.4/72;region_w=bounds.width()*mm_per_point;region_h=bounds.height()*mm_per_point
            base_x,base_y=self._view_center_position(region_w,region_h)
            raster=self._pdf_region_raster(document,page,bounds,lines,[code["rect"] for code in codes])
            additions=[Element(kind="image",x=base_x,y=base_y,width=round(region_w,3),height=round(region_h,3),value="Фрагмент PDF — графика",asset_data=image_to_base64(raster))]
            for index,line in enumerate(lines):
                if index in code_text_lines:continue
                x=base_x+(line["x"]-bounds.left())*mm_per_point;y=base_y+(line["y"]-bounds.top())*mm_per_point
                width=max(2,line["width"]*mm_per_point+1);height=max(2,line["height"]*mm_per_point+1)
                font_size=max(3,round(line["height"]*.9))
                height=max(height,font_size*25.4/72*1.4)
                additions.append(Element(kind="text",x=round(x,3),y=round(y,3),width=round(width,3),height=round(height,3),value=line["text"],font_size=font_size,bold=index==0))
            for code in codes:
                rect=code["rect"]
                x=round(base_x+(rect.x()-bounds.left())*mm_per_point,3);y=round(base_y+(rect.y()-bounds.top())*mm_per_point,3)
                w=round(rect.width()*mm_per_point,3);h=round(rect.height()*mm_per_point,3)
                additions.append(Element(kind=code["kind"],x=x,y=y,width=w,height=h,value=code["text"],gs1=code["kind"]=="datamatrix",barcode_type=code.get("barcode_type","Code 128")))
            self.template.elements.extend(additions);self.canvas.selected_index=len(self.template.elements)-1
            self.canvas.selected_indices={self.canvas.selected_index};self.refresh_object_list();self.select_element(self.canvas.selected_index);self.canvas.update();self.refresh_print_preview()
            self.status.setText(f"Из PDF добавлено объектов: {len(additions)}; графика сохранена изображением")
        except Exception as exc:
            if progress:progress.close()
            QMessageBox.critical(self,"Не удалось вставить область PDF",str(exc))
        finally:
            if progress:progress.close()

    @staticmethod
    def _pdf_region_text_lines(document,page,area):
        text=document.getAllText(page).text();words=[]
        for match in re.finditer(r"\S+",text):
            token=match.group()
            rect=document.getSelectionAtIndex(page,match.start(),len(token)).boundingRectangle()
            if rect.width()>0 and rect.height()>0 and area.contains(rect.center()):
                words.append((rect.y(),rect.x(),rect.width(),rect.height(),token))
        groups=[]
        for y,x,w,h,token in sorted(words):
            line=next((entry for entry in groups if abs(entry["y"]-y)<=1.0),None)
            if line is None:line={"y":y,"x":x,"right":x+w,"height":h,"parts":[]};groups.append(line)
            line["parts"].append((x,token));line["x"]=min(line["x"],x);line["right"]=max(line["right"],x+w);line["height"]=max(line["height"],h)
        return [{"x":line["x"],"y":line["y"],"width":line["right"]-line["x"],"height":line["height"],"text":" ".join(word for _x,word in sorted(line["parts"]))} for line in sorted(groups,key=lambda line:line["y"])]

    @staticmethod
    def _pdf_render_region(document,page,area,scale=4.0,page_image=None):
        page_size=document.pagePointSize(page)
        full=QRectF(0,0,page_size.width(),page_size.height())
        area=QRectF(area).intersected(full)
        if area.isEmpty():return QImage()
        rendered=page_image
        if rendered is None:
            width=max(1,min(6000,round(page_size.width()*scale)));height=max(1,min(6000,round(page_size.height()*scale)))
            rendered=document.render(page,QSize(width,height))
        if rendered.isNull():return QImage()
        x=round(area.x()*rendered.width()/page_size.width());y=round(area.y()*rendered.height()/page_size.height())
        w=max(1,round(area.width()*rendered.width()/page_size.width()));h=max(1,round(area.height()*rendered.height()/page_size.height()))
        return rendered.copy(x,y,w,h)

    @classmethod
    def _pdf_decode_codes(cls,document,page,area,page_cache=None,progress_callback=None):
        zxingcpp=_zxingcpp
        if zxingcpp is None:
            hint="В каталоге проекта выполните `uv sync`, затем запустите приложение командой `uv run main.py`." if sys.platform.startswith("linux") else "Переустановите приложение из актуальной сборки."
            raise RuntimeError(f"Не найден модуль распознавания zxing-cpp. {hint}")
        try:
            if page_cache is not None and page in page_cache:
                all_codes=page_cache[page]
            else:
                page_size=document.pagePointSize(page);page_area=QRectF(0,0,page_size.width(),page_size.height());found=[]
                scan_errors=[]
                for scale in (4.0,6.0,8.0):
                    image=cls._pdf_render_region(document,page,page_area,scale)
                    if image.isNull():continue
                    from PIL import Image
                    png=QByteArray();buffer=QBuffer(png);buffer.open(QIODevice.OpenModeFlag.WriteOnly)
                    if not image.save(buffer,"PNG"):
                        buffer.close();continue
                    decoder_image=Image.open(BytesIO(bytes(png))).convert("RGB");buffer.close()
                    for mode in (zxingcpp.TextMode.Escaped,zxingcpp.TextMode.HRI):
                        if progress_callback:progress_callback(f"Распознавание кодов: страница {page+1}, масштаб {scale:.0f}×")
                        try:decoded=zxingcpp.read_barcodes(decoder_image,text_mode=mode)
                        except Exception as exc:scan_errors.append(str(exc));continue
                        for item in decoded:
                            value=str(item.text or "").strip()
                            if not value:continue
                            corners=item.position
                            xs=[float(p.x) for p in (corners.top_left,corners.top_right,corners.bottom_right,corners.bottom_left)]
                            ys=[float(p.y) for p in (corners.top_left,corners.top_right,corners.bottom_right,corners.bottom_left)]
                            rect=QRectF(min(xs)*page_size.width()/image.width(),min(ys)*page_size.height()/image.height(),(max(xs)-min(xs))*page_size.width()/image.width(),(max(ys)-min(ys))*page_size.height()/image.height()).adjusted(-1,-1,1,1)
                            fmt=str(item.format).lower()
                            kind="qr" if "qr" in fmt else "datamatrix" if "data" in fmt and "matrix" in fmt else "barcode"
                            if kind=="datamatrix":value=normalize_gs1_payload(value)
                            if kind=="barcode" and not any(name in fmt for name in ("code128","code39","ean13","upca","itf")):continue
                            if kind=="barcode" and "ean13" in fmt:barcode_type="EAN-13"
                            elif kind=="barcode" and "upca" in fmt:barcode_type="UPC-A"
                            elif kind=="barcode" and "itf" in fmt:barcode_type="ITF"
                            elif kind=="barcode" and "code39" in fmt:barcode_type="Code 39"
                            else:barcode_type="Code 128"
                            duplicate=next((entry for entry in found if entry["kind"]==kind and (entry["rect"].center()-rect.center()).manhattanLength()<max(4,min(rect.width(),rect.height())*.35)),None)
                            if duplicate is None:found.append({"kind":kind,"text":value,"rect":rect,"barcode_type":barcode_type})
                            elif len(value.replace("<GS>",""))>len(duplicate["text"].replace("<GS>","")):
                                duplicate.update(text=value,rect=rect,barcode_type=barcode_type)
                if scan_errors and not found:
                    raise RuntimeError(f"Не удалось запустить распознавание DataMatrix в PDF: {scan_errors[-1]}")
                all_codes=sorted(found,key=lambda code:(code["rect"].top(),code["rect"].left()))
                if page_cache is not None:page_cache[page]=all_codes
            return [code for code in all_codes if area.contains(code["rect"].center())]
        except RuntimeError:raise
        except Exception as exc:
            raise RuntimeError(f"Ошибка анализа кодов PDF: {exc}") from exc

    @classmethod
    def _pdf_region_raster(cls,document,page,area,lines,codes,page_image=None):
        image=cls._pdf_render_region(document,page,area,4.0,page_image)
        if image.isNull():return image
        page_size=document.pagePointSize(page);sx=image.width()/max(area.width(),1);sy=image.height()/max(area.height(),1)
        painter=QPainter(image);painter.setPen(Qt.PenStyle.NoPen);painter.setBrush(QColor("white"))
        for line in lines:
            rect=QRectF((line["x"]-area.x())*sx,(line["y"]-area.y())*sy,line["width"]*sx,line["height"]*sy).adjusted(-2,-2,2,2)
            painter.drawRect(rect)
        for code in codes:
            rect=QRectF((code.x()-area.x())*sx,(code.y()-area.y())*sy,code.width()*sx,code.height()*sy).adjusted(-3,-3,3,3)
            painter.drawRect(rect)
        painter.end();return image

    @staticmethod
    def _pdf_gs1_line_indexes(lines):
        ordered=sorted(enumerate(lines),key=lambda pair:(pair[1]["y"],pair[1]["x"]))
        start=next((index for index,(_original_index,line) in enumerate(ordered) if re.search(r"01\d{14}21",re.sub(r"\s+","",normalize_gs1_payload(line["text"])))),None)
        if start is None:return set()
        original_index,base=ordered[start];selected={original_index}
        for original_index,line in ordered[start+1:]:
            if line["y"]-base["y"]>max(18,base["height"]*3.5):break
            text=line["text"].strip()
            if not text or re.search(r"[А-Яа-яЁё:]",text):break
            if line["x"]>base["x"]+max(24,base["width"]*.6):break
            selected.add(original_index);base=line
            if len(selected)>=5:break
        return selected

    @classmethod
    def _pdf_join_code_lines(cls,lines):
        """Reassemble a GS1 payload split by PDF text extraction into several lines."""
        selected_indexes=cls._pdf_gs1_line_indexes(lines)
        if not selected_indexes:return ""
        selected=sorted((lines[index] for index in selected_indexes),key=lambda line:(line["y"],line["x"]))
        tokens=[]
        for line in selected:
            for token in re.findall(r"\S+",line["text"]):
                token=re.sub(r"^\((91|92)\)",r"\1",token)
                if tokens and re.fullmatch(r"(?:91|92)\S*",token) and re.search(r"01\d{14}21", "".join(tokens).replace("<GS>","")):
                    tokens.append("<GS>")
                tokens.append(token)
        value="".join(tokens)
        return normalize_gs1_payload(value)

    @staticmethod
    def _cluster_pdf_coordinates(values,tolerance=3.0):
        groups=[]
        for value in sorted(values):
            if not groups or abs(value-sum(groups[-1])/len(groups[-1]))>tolerance:groups.append([value])
            else:groups[-1].append(value)
        return [sum(group)/len(group) for group in groups]

    def _pdf_text_anchors(self,document,progress=None):
        pattern=re.compile(r"\b[A-Z0-9]{2,}_[A-Z0-9_-]{2,}\b");pages=[]
        for page in range(document.pageCount()):
            if progress:
                progress.setLabelText(f"Поиск этикеток в PDF · страница {page+1} из {document.pageCount()}")
                progress.setValue(page);QApplication.processEvents()
            text=document.getAllText(page).text();anchors=[]
            for match in pattern.finditer(text):
                rect=document.getSelectionAtIndex(page,match.start(),len(match.group())).boundingRectangle()
                if rect.width()>0 and rect.height()>0:anchors.append({"name":match.group(),"x":rect.x(),"y":rect.y(),"rect":rect})
            pages.append(anchors)
        if progress:
            progress.setValue(document.pageCount());QApplication.processEvents()
        first=next((page for page in pages if len(page)>=2),[])
        if len(first)<2:return pages,[],[]
        xs=self._cluster_pdf_coordinates([item["x"] for item in first]);ys=self._cluster_pdf_coordinates([item["y"] for item in first])
        if len(xs)<2 or len(ys)<1 or len(first)<max(2,int(len(xs)*len(ys)*.65)):return pages,[],[]
        return pages,xs,ys

    def _insert_asset(self,path,kind):
        try:
            raw=Path(path).read_bytes()
            if kind=="svg":
                renderer=QSvgRenderer(QByteArray(raw))
                if not renderer.isValid():raise ValueError("Файл SVG повреждён или не поддерживается.")
                size=renderer.defaultSize();aspect=size.width()/size.height() if size.width()>0 and size.height()>0 else 1.0
            else:
                image=QImage.fromData(raw)
                if image.isNull():raise ValueError("Формат или содержимое изображения не поддерживается.")
                aspect=image.width()/image.height()
            width=min(30.0,22.0*aspect);height=width/aspect
            if height>22.0:height=22.0;width=height*aspect
            x,y=self._view_center_position(width,height)
            el=Element(kind=kind,x=x,y=y,width=width,height=height,value=Path(path).name,asset_data=base64.b64encode(raw).decode("ascii"))
            self.template.elements.append(el);self.canvas.selected_index=len(self.template.elements)-1;self.refresh_object_list();self.select_element(self.canvas.selected_index);self.canvas.update();self.refresh_print_preview()
        except Exception as exc:QMessageBox.warning(self,"Не удалось вставить изображение",str(exc))

    def _view_center_position(self,width,height):
        ox,oy=getattr(self.canvas,"origin",((self.canvas.width()-self.template.width*self.canvas.scale)/2,(self.canvas.height()-self.template.height*self.canvas.scale)/2))
        center_x=(self.canvas.width()/2-ox)/self.canvas.scale;center_y=(self.canvas.height()/2-oy)/self.canvas.scale
        x=center_x-width/2;y=center_y-height/2
        return round(min(max(x,0),max(0,self.template.width-width)),3),round(min(max(y,0),max(0,self.template.height-height)),3)

    def _next_free_position(self,width,height):
        margin=2.0; max_x=max(0,self.template.width-width); max_y=max(0,self.template.height-height)
        step_x=max(4.0,width+margin); step_y=max(4.0,height+margin)
        ys=[]; y=3.0
        while y<=max_y: ys.append(y); y+=step_y
        if not ys: ys=[0.0]
        xs=[]; x=3.0
        while x<=max_x: xs.append(x); x+=step_x
        xs.append(max_x)
        for y in ys:
            for x in xs:
                overlaps=any(not (x+width+margin<=e.x or e.x+e.width+margin<=x or y+height+margin<=e.y or e.y+e.height+margin<=y) for e in self.template.elements)
                if not overlaps:return round(x,3),round(y,3)
        return 3.0,3.0

    def refresh_object_list(self):
        labels = {"text":"Текст", "barcode":"Штрихкод", "qr":"QR-код", "datamatrix":"DataMatrix","line":"Линия","shape":"Фигура","symbol":"Символ","image":"Изображение","svg":"SVG","pdf":"Элемент PDF"}
        current = self.canvas.selected_index
        self.object_list.blockSignals(True); self.object_list.clear()
        for index, element in enumerate(self.template.elements):
            lock_mark="🔒 " if element.layer_locked else ""
            item = QListWidgetItem(f"{index + 1:02d}   {lock_mark}{labels.get(element.kind, element.kind)}")
            item.setData(Qt.ItemDataRole.UserRole,index)
            item.setToolTip(element.value)
            self.object_list.addItem(item)
            item.setSelected(index in self.canvas.selected_indices or index==current)
        if 0 <= current < self.object_list.count(): self.object_list.setCurrentRow(current)
        self.object_list.blockSignals(False)

    def _list_selection_changed(self):
        indices={int(item.data(Qt.ItemDataRole.UserRole)) for item in self.object_list.selectedItems()}
        self.canvas.selected_indices=indices
        current=self.object_list.currentRow()
        self.canvas.selected_index=current if current in indices else (max(indices) if indices else -1)
        self.select_element(self.canvas.selected_index,preserve_multi=True);self.canvas.update()

    def select_elements(self,indices):
        self.canvas.selected_indices={i for i in indices if 0<=i<len(self.template.elements)}
        self.canvas.selected_index=max(self.canvas.selected_indices) if self.canvas.selected_indices else -1
        self.object_list.blockSignals(True)
        for i in range(self.object_list.count()):self.object_list.item(i).setSelected(i in self.canvas.selected_indices)
        if self.canvas.selected_index>=0:self.object_list.setCurrentRow(self.canvas.selected_index)
        self.object_list.blockSignals(False)
        self.select_element(self.canvas.selected_index,preserve_multi=True);self.canvas.update()

    def move_layer(self,delta):
        index=self.canvas.selected_index;target=index+delta
        if not (0<=index<len(self.template.elements) and 0<=target<len(self.template.elements)):return
        self.template.elements[index],self.template.elements[target]=self.template.elements[target],self.template.elements[index]
        self.canvas.selected_index=target;self.refresh_object_list();self.select_element(target);self.canvas.update();self.refresh_print_preview()

    def raise_layer(self):self.move_layer(1)
    def lower_layer(self):self.move_layer(-1)

    def toggle_layer_lock(self):
        selected=self.selected_elements()
        if selected:
            lock=not all(element.layer_locked for element in selected)
            for element in selected:element.layer_locked=lock
            self.refresh_object_list();self.select_element(self.canvas.selected_index,preserve_multi=True);self.canvas.update();self.refresh_print_preview()

    def select_element(self, index,preserve_multi=False):
        self.canvas.selected_index = index
        if not preserve_multi:self.canvas.selected_indices={index} if 0<=index<len(self.template.elements) else set()
        if hasattr(self,"object_list"):
            self.object_list.blockSignals(True)
            if self.object_list.currentRow()!=index:self.object_list.setCurrentRow(index)
            for row in range(self.object_list.count()):self.object_list.item(row).setSelected(row in self.canvas.selected_indices)
            self.object_list.blockSignals(False)
        enabled = 0 <= index < len(self.template.elements)
        el = self.template.elements[index] if enabled else None
        selected=[self.template.elements[i] for i in self.canvas.selected_indices if 0<=i<len(self.template.elements)]
        movable=any(not item.layer_locked for item in selected) if selected else enabled and not el.layer_locked
        self.align_panel.setEnabled(movable)
        for w in (self.x_spin,self.y_spin,self.w_spin,self.h_spin,self.rotation_spin):w.setEnabled(movable)
        self.proportion_check.setEnabled(movable)
        single=len(selected)<=1
        self.layer_up_btn.setEnabled(enabled and single and index<len(self.template.elements)-1)
        self.layer_down_btn.setEnabled(enabled and single and index>0)
        self.layer_lock_btn.setEnabled(enabled)
        all_locked=bool(selected) and all(item.layer_locked for item in selected)
        self.layer_lock_btn.setText("🔓" if all_locked else "🔒")
        self.layer_lock_btn.setToolTip("Разблокировать выбранные объекты" if all_locked else "Заблокировать выбранные объекты")
        kinds={item.kind for item in selected}
        same_kind=len(kinds)==1
        asset_selected=enabled and same_kind and el.kind in ("image","svg")
        crop_enabled=enabled and single and el.kind=="image" and bool(el.asset_data)
        self.crop_image_btn.setVisible(crop_enabled)
        self.crop_image_btn.setEnabled(crop_enabled)
        text_selected=enabled and same_kind and el.kind in ("text","symbol"); symbol_selected=enabled and same_kind and el.kind=="symbol"
        barcode_selected=enabled and same_kind and el.kind=="barcode"; gs1_selected=enabled and same_kind and el.kind=="datamatrix"
        vector_selected=enabled and same_kind and el.kind in ("line","shape"); shape_selected=enabled and same_kind and el.kind=="shape"
        for w in (self.x_spin,self.y_spin,self.w_spin,self.h_spin,self.rotation_spin): w.setEnabled(movable)
        for w in (self.value_edit,self.variable_button,self.field_combo):w.setEnabled(enabled and not asset_selected)
        if asset_selected:self.value_edit.setToolTip("Имя встроенного файла. Для замены удалите элемент и вставьте изображение заново.")
        else:self.value_edit.setToolTip("Текст или переменная, например {GTIN:Код}")
        for w in (self.font_family_combo,self.font_spin,self.letter_spacing_spin,self.line_spacing_spin,self.style_box,self.text_color_btn,self.align_h_combo,self.align_v_combo): w.setEnabled(text_selected)
        self.symbol_combo.setEnabled(symbol_selected)
        for w in (self.barcode_combo,self.hri_position_combo,self.hri_align_combo,self.hri_font_spin): w.setEnabled(barcode_selected)
        self.gs1_check.setEnabled(gs1_selected); self.dm_summary.setEnabled(gs1_selected)
        for w in (self.shape_type_combo,self.fill_check,self.fill_color_btn): w.setEnabled(shape_selected)
        self.stroke_color_btn.setEnabled(vector_selected)
        for w in (self.line_width_spin,self.line_style_combo): w.setEnabled(vector_selected)
        self.property_tabs.setTabEnabled(2,text_selected)
        self.property_tabs.setTabEnabled(3,barcode_selected or gs1_selected or (enabled and same_kind and el.kind=="qr"))
        self.property_tabs.setTabEnabled(4,vector_selected)
        if vector_selected: self.property_tabs.setCurrentIndex(4)
        elif barcode_selected or gs1_selected or (enabled and same_kind and el.kind=="qr"): self.property_tabs.setCurrentIndex(3)
        elif symbol_selected: self.property_tabs.setCurrentIndex(2)
        if enabled:
            for s,v in [(self.x_spin,el.x),(self.y_spin,el.y),(self.w_spin,el.width),(self.h_spin,el.height),(self.font_spin,el.font_size),
                        (self.letter_spacing_spin,el.letter_spacing_pt),(self.line_spacing_spin,el.line_spacing_pt)]:
                s.blockSignals(True); s.setValue(v); s.blockSignals(False)
            self.value_edit.blockSignals(True); self.value_edit.setText(el.value); self.value_edit.blockSignals(False)
            self.field_combo.blockSignals(True)
            saved = el.value
            self.field_combo.setCurrentIndex(max(0, self.field_combo.findData(saved[1:-1] if saved.startswith("{") and saved.endswith("}") else "")))
            self.field_combo.blockSignals(False)
            self.barcode_combo.blockSignals(True); self.barcode_combo.setCurrentText(el.barcode_type); self.barcode_combo.blockSignals(False)
            self.rotation_spin.blockSignals(True); self.rotation_spin.setValue(el.rotation); self.rotation_spin.blockSignals(False)
            self.proportion_check.blockSignals(True);self.proportion_check.setChecked(el.lock_proportions);self.proportion_check.blockSignals(False)
            self.gs1_check.blockSignals(True); self.gs1_check.setChecked(el.gs1); self.gs1_check.blockSignals(False)
            self.font_family_combo.blockSignals(True); self.font_family_combo.setCurrentFont(QFont(el.font_family)); self.font_family_combo.blockSignals(False)
            self.symbol_combo.blockSignals(True); self.symbol_combo.setCurrentText(el.value if symbol_selected else "★"); self.symbol_combo.blockSignals(False)
            self.shape_type_combo.blockSignals(True); self.shape_type_combo.setCurrentIndex(max(0,self.shape_type_combo.findData(el.shape_type))); self.shape_type_combo.blockSignals(False)
            self.line_width_spin.blockSignals(True); self.line_width_spin.setValue(el.line_width); self.line_width_spin.blockSignals(False)
            self.line_style_combo.blockSignals(True); self.line_style_combo.setCurrentIndex(max(0,self.line_style_combo.findData(el.line_style))); self.line_style_combo.blockSignals(False)
            self.fill_check.blockSignals(True); self.fill_check.setChecked(el.fill_enabled); self.fill_check.blockSignals(False)
            self.fill_color_btn.setIcon(self.glyph_icon("■",el.fill_color))
            self.stroke_color_btn.setIcon(self.glyph_icon("●",el.color))
            for control,value in ((self.bold_check,el.bold),(self.italic_check,el.italic),(self.underline_check,el.underline)):
                control.blockSignals(True); control.setChecked(value); control.blockSignals(False)
            for combo,value in ((self.align_h_combo,el.horizontal_alignment),(self.align_v_combo,el.vertical_alignment),(self.hri_position_combo,el.hri_position),(self.hri_align_combo,el.hri_alignment)):
                combo.blockSignals(True); combo.setCurrentIndex(max(0,combo.findData(value))); combo.blockSignals(False)
            self.hri_font_spin.blockSignals(True); self.hri_font_spin.setValue(el.hri_font_size); self.hri_font_spin.blockSignals(False)
            self.text_color_btn.setIcon(self.glyph_icon("●",el.color)); self.text_color_btn.setToolTip(f"Цвет текста: {el.color}")
            self.refresh_dm_summary()
        self.canvas.update()

    def selected_element(self):
        i=self.canvas.selected_index
        return self.template.elements[i] if 0 <= i < len(self.template.elements) else None

    def selected_elements(self):
        return [self.template.elements[i] for i in sorted(self.canvas.selected_indices) if 0<=i<len(self.template.elements)]

    def refresh_properties(self):
        el=self.selected_element()
        if el:
            for spin,value in ((self.x_spin,el.x),(self.y_spin,el.y),(self.w_spin,el.width),(self.h_spin,el.height),(self.rotation_spin,el.rotation)):
                spin.blockSignals(True); spin.setValue(value); spin.blockSignals(False)

    def change_value(self):
        value=self.value_edit.text();changed=False
        for el in self.selected_elements():
            if el.kind in ("text","symbol","qr","barcode","datamatrix"):
                el.value=value;changed=True
        if changed:
            el=self.selected_element()
            if el and el.kind=="symbol": self.symbol_combo.blockSignals(True); self.symbol_combo.setCurrentText(el.value); self.symbol_combo.blockSignals(False)
            self.canvas.update(); self.refresh_dm_summary(); self.refresh_print_preview()

    def change_symbol(self,value):
        changed=False
        for el in self.selected_elements():
            if el.kind=="symbol":el.value=value;changed=True
        if changed:self.value_edit.setText(value);self.canvas.update();self.refresh_print_preview()

    def choose_fill_color(self):
        el=self.selected_element()
        if not el:return
        color=QColorDialog.getColor(QColor(el.fill_color),self,"Цвет заливки")
        if color.isValid():
            for item in self.selected_elements():item.fill_color=color.name()
            self.fill_color_btn.setIcon(self.glyph_icon("■",color.name())); self.canvas.update(); self.refresh_print_preview()

    def choose_stroke_color(self):
        el=self.selected_element()
        if not el:return
        color=QColorDialog.getColor(QColor(el.color),self,"Цвет контура")
        if color.isValid():
            for item in self.selected_elements():item.color=color.name()
            self.stroke_color_btn.setIcon(self.glyph_icon("●",color.name())); self.canvas.update(); self.refresh_print_preview()

    def rebuild_variable_menu(self):
        self.variable_menu.clear()
        def add(label,token):
            self.variable_menu.addAction(label).triggered.connect(lambda _=False,t=token:self.insert_variable(t))
        add("Нумерация тиража", "SEQ")
        for header in self.headers:
            add(f"Поле: {header}",header)
            add(f"GTIN из «{header}»",f"GTIN:{header}")
            add(f"Серийный номер из «{header}»",f"SERIAL:{header}")

    def insert_variable(self, token):
        self.value_edit.insert("{"+token+"}")
        self.change_value()

    def change_barcode_type(self, value):
        changed=False
        for el in self.selected_elements():
            if el.kind=="barcode":el.barcode_type=value;changed=True
        if changed:self.canvas.update();self.refresh_print_preview()

    def change_gs1(self, value):
        changed=False
        for el in self.selected_elements():
            if el.kind=="datamatrix":el.gs1=value;changed=True
        if changed:self.canvas.update(); self.refresh_dm_summary(); self.refresh_print_preview()

    def change_field(self, idx):
        el=self.selected_element()
        if el and idx > 0:
            token=str(self.field_combo.currentData())
            for selected in self.selected_elements():
                if selected.kind in ("text","symbol","qr","barcode","datamatrix"):selected.value="{"+token+"}"
            self.value_edit.setText(el.value); self.canvas.update(); self.refresh_dm_summary(); self.refresh_print_preview()

    def change_prop(self, attr, value):
        selected=self.selected_elements()
        if selected:
            for el in selected:
                if attr in ("x","y","width","height","rotation") and el.layer_locked:continue
                if attr=="width" and el.lock_proportions:
                    ratio=el.height/max(el.width,.001);el.width=value;el.height=round(value*ratio,3)
                elif attr=="height" and el.lock_proportions:
                    ratio=el.width/max(el.height,.001);el.height=value;el.width=round(value*ratio,3)
                else:setattr(el,attr,value)
            self.select_element(self.canvas.selected_index,preserve_multi=True)
            self.canvas.update(); self.refresh_print_preview()

    def choose_text_color(self):
        el=self.selected_element()
        if not el:return
        color=QColorDialog.getColor(QColor(el.color),self,"Цвет текста")
        if color.isValid():
            for item in self.selected_elements():item.color=color.name()
            self.text_color_btn.setIcon(self.glyph_icon("●",color.name())); self.text_color_btn.setToolTip(f"Цвет текста: {color.name()}"); self.canvas.update(); self.refresh_print_preview()

    def _resolved(self,value,row):
        return resolve_template_value(value,row)

    def select_preview_row(self,row,_column):
        self.preview_variant_spin.setValue(1)
        self.from_spin.setValue(row+1)

    def refresh_dm_summary(self):
        el=self.selected_element()
        if not el or el.kind!="datamatrix":return
        value=self._resolved(el.value,self.canvas.preview_row)
        fields=extract_gs1_fields(value)
        self.dm_summary.setText(f"GTIN: {fields['GTIN'] or 'не найден'}\nСерийный номер: {fields['Серийный номер'] or 'не найден'}")

    def update_preview(self,*_args):
        if not hasattr(self,"canvas"):return
        if self.rows and hasattr(self,"count_spin"):
            available=max(1,len(self.rows)-self.from_spin.value()+1)
            self.count_spin.blockSignals(True); self.count_spin.setMaximum(available)
            if self.count_spin.value()>available:self.count_spin.setValue(available)
            self.count_spin.blockSignals(False)
        variant=max(0,self.preview_variant_spin.value()-1) if hasattr(self,"preview_variant_spin") else 0
        if hasattr(self,"count_spin") and hasattr(self,"preview_variant_spin"):
            max_variant=self.count_spin.value()
            if self.rows:
                max_variant=min(max_variant,max(1,len(self.rows)-self.from_spin.value()+1))
            self.preview_variant_spin.setMaximum(max(1,max_variant))
            variant=min(max(0,self.preview_variant_spin.value()-1),max_variant-1)
        row_index=max(0,self.from_spin.value()-1+variant) if hasattr(self,"from_spin") else 0
        row=dict(self.rows[row_index]) if row_index<len(self.rows) else {}
        step=self.seq_direction.currentData() if hasattr(self,"seq_direction") else 1
        start=self.seq_start.value() if hasattr(self,"seq_start") else 1
        width=self.seq_width.value() if hasattr(self,"seq_width") else 0
        identity=self.template_identity_for_print_index(variant)
        sequence=start+self.template_occurrence_before(variant,identity)*int(step or 1)
        row["_SEQ"]=str(sequence).zfill(width) if width else str(sequence)
        self.canvas.preview_row=row; self.canvas.update()
        if hasattr(self,"preview_label"):
            total=len(self.rows[max(0,self.from_spin.value()-1):max(0,self.from_spin.value()-1)+self.count_spin.value()]) if self.rows else self.count_spin.value()
            source=f"CSV/XLSX · строка {row_index+1}" if self.rows and row_index<len(self.rows) else "Нумерация без файла данных"
            self.preview_counter.setText(f"{variant+1} / {total}")
            template=self.template_for_print_index(variant)
            self.preview_label.setText(f"{source}\nШаблон: {template.name}\nНомер {{SEQ}}: {row['_SEQ']}")
            self.refresh_print_preview()
        if hasattr(self,"dm_summary"): self.refresh_dm_summary()

    def refresh_print_preview(self):
        self.schedule_history_change()
        if hasattr(self,"preview_thumb"): self.preview_thumb.update()

    def paint_print_preview(self,painter,area):
        index=max(0,self.preview_variant_spin.value()-1) if hasattr(self,"preview_variant_spin") else 0
        template=self.template_for_print_index(index)
        row=dict(self.canvas.preview_row)
        identity=self.template_identity_for_print_index(index)
        row["_SEQ"]=str(self.seq_start.value()+self.template_occurrence_before(index,identity)*int(self.seq_direction.currentData())).zfill(self.seq_width.value()) if self.seq_width.value() else str(self.seq_start.value()+self.template_occurrence_before(index,identity)*int(self.seq_direction.currentData()))
        self._paint_label(painter,row,fit_rect=area,template=template)

    def set_dimension(self, attr, value):
        setattr(self.template,attr,value); self.canvas.update(); self.refresh_print_preview()

    def toggle_grid(self, checked): self.canvas.show_grid=checked; self.canvas.update()
    def toggle_guides(self, checked): self.canvas.show_guides=checked; self.canvas.update()

    def add_guide(self, orientation):
        limit=self.template.width if orientation == "vertical" else self.template.height
        self.template.guides.append({"orientation":orientation,"position":round(limit / 2, 3)})
        self.canvas.show_guides=True; self.guides_btn.setChecked(True); self.canvas.update();self.schedule_history_change()

    def align_selected(self, alignment):
        for el in self.selected_elements():
            if el.layer_locked:continue
            angle=math.radians(el.rotation)
            bbox_w=abs(el.width*math.cos(angle))+abs(el.height*math.sin(angle))
            bbox_h=abs(el.width*math.sin(angle))+abs(el.height*math.cos(angle))
            if alignment=="left": el.x=round(bbox_w/2-el.width/2,3)
            elif alignment=="center_h": el.x=round((self.template.width-el.width)/2,3)
            elif alignment=="right": el.x=round(self.template.width-bbox_w/2-el.width/2,3)
            elif alignment=="top": el.y=round(bbox_h/2-el.height/2,3)
            elif alignment=="center_v": el.y=round((self.template.height-el.height)/2,3)
            elif alignment=="bottom": el.y=round(self.template.height-bbox_h/2-el.height/2,3)
        self.refresh_properties(); self.canvas.update(); self.refresh_print_preview()

    def rotate_element(self, degrees):
        for el in self.selected_elements():
            if el.layer_locked:continue
            el.rotation=round((el.rotation + degrees) % 360, 3)
        self.select_element(self.canvas.selected_index,preserve_multi=True);self.canvas.update(); self.refresh_print_preview()

    def rotate_element_cw(self): self.rotate_element(90)
    def rotate_element_ccw(self): self.rotate_element(-90)

    def rotate_label(self, clockwise=True):
        old_w,old_h=self.template.width,self.template.height
        for el in self.template.elements:
            center_x=el.x+el.width/2;center_y=el.y+el.height/2
            if clockwise:
                center_x,center_y=old_h-center_y,center_x
            else:
                center_x,center_y=center_y,old_w-center_x
            el.x=round(center_x-el.width/2,3);el.y=round(center_y-el.height/2,3)
            el.rotation=(el.rotation + (90 if clockwise else -90)) % 360
        for guide in self.template.guides:
            old_position=float(guide["position"])
            if clockwise:
                guide["orientation"]="horizontal" if guide["orientation"] == "vertical" else "vertical"
                guide["position"]=round(old_position if guide["orientation"] == "horizontal" else old_h-old_position,3)
            else:
                guide["orientation"]="horizontal" if guide["orientation"] == "vertical" else "vertical"
                guide["position"]=round(old_w-old_position if guide["orientation"] == "horizontal" else old_position,3)
        self.template.width,self.template.height=old_h,old_w
        self.label_w.blockSignals(True); self.label_h.blockSignals(True)
        self.label_w.setValue(self.template.width); self.label_h.setValue(self.template.height)
        self.label_w.blockSignals(False); self.label_h.blockSignals(False)
        self.refresh_properties(); self.canvas.update(); self.refresh_print_preview()

    def _rotated_template_copy(self,template,degrees=90):
        degrees=int(degrees)%360
        rotated=self._template_from_data(asdict(template));old_w,old_h=template.width,template.height
        for element in rotated.elements:
            cx=element.x+element.width/2;cy=element.y+element.height/2
            if degrees==90:cx,cy=old_h-cy,cx
            elif degrees==180:cx,cy=old_w-cx,old_h-cy
            elif degrees==270:cx,cy=cy,old_w-cx
            element.x=round(cx-element.width/2,3);element.y=round(cy-element.height/2,3)
            element.rotation=(element.rotation+degrees)%360
        for guide in rotated.guides:
            pos=float(guide["position"]);old_orientation=guide["orientation"]
            if degrees==90:
                guide["orientation"]="horizontal" if old_orientation=="vertical" else "vertical"
                guide["position"]=round(pos if old_orientation=="vertical" else old_h-pos,3)
            elif degrees==180:
                guide["position"]=round((old_w if old_orientation=="vertical" else old_h)-pos,3)
            elif degrees==270:
                guide["orientation"]="horizontal" if old_orientation=="vertical" else "vertical"
                guide["position"]=round(old_w-pos if old_orientation=="vertical" else pos,3)
        if degrees in (90,270):rotated.width,rotated.height=old_h,old_w
        return rotated

    def rotate_label_cw(self): self.rotate_label(True)
    def rotate_label_ccw(self): self.rotate_label(False)

    def delete_element(self):
        selected=self.selected_elements()
        if not selected:return
        locked=sum(element.layer_locked for element in selected)
        selected_ids={id(element) for element in selected}
        self.template.elements=[element for element in self.template.elements if id(element) not in selected_ids or element.layer_locked]
        if locked:self.status.setText("Заблокированные объекты оставлены. Разблокируйте их, чтобы удалить.")
        self.canvas.selected_indices=set();self.canvas.selected_index=-1
        self.refresh_object_list();self.select_element(-1);self.canvas.update();self.refresh_print_preview()

    def set_background(self):
        color=QColorDialog.getColor(QColor(self.template.background),self,"Фон этикетки")
        if color.isValid(): self.template.background=color.name(); self.canvas.update(); self.refresh_print_preview()

    def set_background_image(self):
        path,_=QFileDialog.getOpenFileName(self,"Выбрать подложку этикетки","","Изображения (*.png *.jpg *.jpeg *.bmp *.webp)")
        if not path:return
        try:
            raw=Path(path).read_bytes()
            if QImage.fromData(raw).isNull():raise ValueError("Не удалось прочитать файл как растровое изображение.")
            self.template.background_image=base64.b64encode(raw).decode("ascii")
            self.canvas.update()
            self.configure_background_image()
        except Exception as e: QMessageBox.critical(self,"Не удалось загрузить фон",str(e))

    def configure_background_image(self):
        if not self.template.background_image:
            self.set_background_image();return
        dialog=QDialog(self);dialog.setWindowTitle("Подложка редактора");dialog.setMinimumWidth(390)
        dialog.setStyleSheet("QDialog{background:#f3f5f8;color:#20242b} QLabel,QCheckBox{color:#20242b} QComboBox,QDoubleSpinBox{background:white;color:#20242b;padding:5px} QPushButton{background:white;color:#20242b;padding:6px}")
        layout=QVBoxLayout(dialog);note=QLabel("Подложка помогает сверять макет с образцом и отображается только на холсте редактора. В печатное задание она не включается.");note.setWordWrap(True);layout.addWidget(note)
        visible=QCheckBox("Показывать подложку на холсте");visible.setChecked(self.template.background_image_visible)
        opacity=QDoubleSpinBox();opacity.setRange(0,1);opacity.setSingleStep(.05);opacity.setDecimals(2);opacity.setValue(self.template.background_image_opacity)
        fit=QComboBox();fit.addItem("Растянуть на этикетку","stretch");fit.addItem("Вписать целиком","contain");fit.setCurrentIndex(max(0,fit.findData(self.template.background_image_fit)))
        form=QFormLayout();form.addRow(visible);form.addRow("Непрозрачность",opacity);form.addRow("Масштабирование",fit);layout.addLayout(form)
        clear=QPushButton("Удалить подложку");layout.addWidget(clear);buttons=QDialogButtonBox(QDialogButtonBox.StandardButton.Ok|QDialogButtonBox.StandardButton.Cancel);layout.addWidget(buttons)
        clear.clicked.connect(lambda:(setattr(self.template,"background_image",""),dialog.accept()))
        buttons.accepted.connect(dialog.accept);buttons.rejected.connect(dialog.reject)
        if dialog.exec()==QDialog.DialogCode.Accepted:
            self.template.background_image_visible=visible.isChecked();self.template.background_image_opacity=opacity.value();self.template.background_image_fit=fit.currentData() or "stretch"
            self.canvas.update();self.refresh_print_preview();self.status.setText("Настройки подложки обновлены; она не участвует в печати.")

    def import_pdf_labels(self):
        path,_=QFileDialog.getOpenFileName(self,"Импортировать этикетки из PDF","","PDF-файлы (*.pdf)")
        if not path:return
        document=QPdfDocument(self)
        progress=None
        try:
            error=document.load(path)
            if error!=QPdfDocument.Error.None_:raise ValueError(f"Не удалось открыть PDF: {error}")
            page_count=max(1,document.pageCount())
            progress=QProgressDialog("Подготовка PDF…","",0,page_count,self);progress.setCancelButton(None);progress.setWindowModality(Qt.WindowModality.ApplicationModal);progress.setMinimumDuration(0);progress.setAutoClose(False);progress.setAutoReset(False);progress.show();QApplication.processEvents()
            pages,xs,ys=self._pdf_text_anchors(document,progress)
            if not xs or not ys:
                QMessageBox.warning(self,"Не найдена сетка этикеток","Не удалось найти повторяющиеся заголовки этикеток в текстовом слое PDF. Отдельную область можно добавить через инструмент «Элемент PDF».");return
            first_page=next(i for i,page in enumerate(pages) if page);page_size=document.pagePointSize(first_page)
            xp=sorted(b-a for a,b in zip(xs,xs[1:]));yp=sorted(b-a for a,b in zip(ys,ys[1:]))
            guessed_w=(sum(xp)/len(xp) if xp else page_size.width()/len(xs))*25.4/72
            guessed_h=(sum(yp)/len(yp) if yp else page_size.height()/len(ys))*25.4/72
            size_match=re.search(r"(\d{2,3})\s*[xх×]\s*(\d{2,3})",Path(path).stem,re.IGNORECASE)
            if size_match:guessed_w=float(size_match.group(1));guessed_h=float(size_match.group(2))
            detected=sum(len(page) for page in pages)
            options=PdfImportOptionsDialog(Path(path).name,document.pageCount(),f"{len(xs)} × {len(ys)}; всего меток текста: {detected}",guessed_w,guessed_h,self)
            progress.hide()
            if options.exec()!=QDialog.DialogCode.Accepted:return
            width_mm=options.width_spin.value();height_mm=options.height_spin.value()
            crop_w=width_mm*72/25.4;crop_h=height_mm*72/25.4
            offset_x=options.left_offset.value()*72/25.4;offset_y=options.top_offset.value()*72/25.4
            progress.setLabelText("Извлечение текста и графики из PDF…");progress.setRange(0,page_count);progress.setValue(0);progress.show();QApplication.processEvents()
            labels=[]
            for page_index,anchors in enumerate(pages):
                progress.setLabelText(f"Извлечение текста · страница {page_index+1} из {page_count}");progress.setValue(page_index);QApplication.processEvents()
                if not anchors:
                    progress.setValue(page_index+1);QApplication.processEvents();continue
                page_wh=document.pagePointSize(page_index);cells=[]
                for anchor in anchors:
                    crop=QRectF(anchor["x"]-offset_x,anchor["y"]-offset_y,crop_w,crop_h).intersected(QRectF(0,0,page_wh.width(),page_wh.height()))
                    if crop.width()<10 or crop.height()<10:continue
                    cells.append({"page":page_index,"anchor":anchor,"crop":crop,"lines":[]})
                text=document.getAllText(page_index).text()
                for match in re.finditer(r"\S+",text):
                    token=match.group()
                    rect=document.getSelectionAtIndex(page_index,match.start(),len(token)).boundingRectangle()
                    if rect.width()<=0 or rect.height()<=0:continue
                    center=rect.center();candidates=[cell for cell in cells if cell["crop"].contains(center)]
                    if not candidates:continue
                    cell=min(candidates,key=lambda item:(center.x()-item["crop"].center().x())**2+(center.y()-item["crop"].center().y())**2)
                    cell["lines"].append((rect.y(),rect.x(),rect.width(),rect.height(),token))
                for cell in cells:
                    groups=[]
                    for y,x,w,h,token in sorted(cell["lines"]):
                        line=next((item for item in groups if abs(item["y"]-y)<=1.0),None)
                        if line is None:line={"y":y,"x":x,"right":x+w,"height":h,"parts":[]};groups.append(line)
                        line["parts"].append((x,token));line["x"]=min(line["x"],x);line["right"]=max(line["right"],x+w);line["height"]=max(line["height"],h)
                    cell["lines"]=[{"x":line["x"],"y":line["y"],"width":line["right"]-line["x"],"height":line["height"],"text":" ".join(word for _x,word in sorted(line["parts"])),"parts":line["parts"]} for line in sorted(groups,key=lambda item:item["y"])]
                    if cell["lines"]:labels.append(cell)
                progress.setValue(page_index+1);QApplication.processEvents()
            if not labels:raise ValueError("На страницах не удалось выделить текстовые строки этикеток.")
            progress.setRange(0,page_count+len(labels));progress.setValue(page_count);QApplication.processEvents()
            barcode_page_cache={}
            raster_page_cache={}
            for label_index,label in enumerate(labels):
                page_index=label["page"]
                progress.setLabelText(f"Распознавание объектов и изображений · этикетка {label_index+1} из {len(labels)} (страница {page_index+1})")
                progress.setValue(page_count+label_index);QApplication.processEvents()
                def update_code_progress(message):
                    progress.setLabelText(message);QApplication.processEvents()
                label["codes"]=self._pdf_decode_codes(document,page_index,label["crop"],barcode_page_cache,update_code_progress)
                label["code_values"]={kind:[code["text"] for code in label["codes"] if code["kind"]==kind] for kind in ("qr","datamatrix","barcode")}
                fallback=self._pdf_join_code_lines(label["lines"])
                current=label["code_values"]["datamatrix"]
                if fallback and (not current or len(fallback.replace("<GS>",""))>len(current[0].replace("<GS>",""))):
                    if current:
                        matrix=next((code for code in label["codes"] if code["kind"]=="datamatrix"),None)
                        if matrix:matrix["text"]=fallback
                        label["code_values"]["datamatrix"][0]=fallback
                    else:label["code_values"]["datamatrix"].append(fallback)
                code_text_lines=self._pdf_gs1_line_indexes(label["lines"])
                if page_index not in raster_page_cache:
                    raster_page_cache.clear()
                    progress.setLabelText(f"Сохранение графики · страница {page_index+1}");QApplication.processEvents()
                    page_size=document.pagePointSize(page_index)
                    raster_page_cache[page_index]=self._pdf_render_region(document,page_index,QRectF(0,0,page_size.width(),page_size.height()),4.0)
                raster_image=self._pdf_region_raster(document,page_index,label["crop"],label["lines"],[code["rect"] for code in label["codes"]],raster_page_cache[page_index])
                label["raster_data"]=image_to_base64(raster_image);del raster_image
                label["lines"]=[line for index,line in enumerate(label["lines"]) if index not in code_text_lines]
                progress.setValue(page_count+label_index+1);QApplication.processEvents()
            first=labels[0];reference=first["lines"];descriptors=[]
            for index,line in enumerate(reference,1):descriptors.append({"key":f"PDF_TEXT_{index:02d}","x":line["x"]-first["crop"].left(),"y":line["y"]-first["crop"].top(),"height":line["height"],"width":line["width"],"text":line["text"]})
            code_kinds=[kind for kind in ("qr","datamatrix","barcode") if any(label["code_values"].get(kind) for label in labels)]
            code_slots=[]
            for kind in code_kinds:
                count=max(len(label["code_values"].get(kind,[])) for label in labels)
                for slot in range(count):
                    key={"qr":"QR_CODE","datamatrix":"DATA_MATRIX","barcode":"BARCODE"}[kind]
                    if slot:key+=f"_{slot+1:02d}"
                    code_slots.append({"kind":kind,"slot":slot,"key":key})
            template=LabelTemplate(name=f"{Path(path).stem} · PDF",width=width_mm,height=height_mm,elements=[])
            sx=width_mm/max(crop_w,1);sy=height_mm/max(crop_h,1)
            template.elements.append(Element(kind="image",x=0,y=0,width=width_mm,height=height_mm,value="{PDF_RASTER}") )
            for index,line in enumerate(descriptors):
                x=max(0,line["x"]*sx);y=max(0,line["y"]*sy)
                element_width=max(4,width_mm-x-.7);element_height=max(2,line["height"]*sy+1.1)
                font_size=max(3,round(line["height"]*.92))
                element_height=max(element_height,font_size*25.4/72*1.4)
                template.elements.append(Element(kind="text",x=round(x,3),y=round(y,3),width=round(element_width,3),height=round(element_height,3),value="{"+line["key"]+"}",font_size=font_size,bold=index==0))
            for code_slot in code_slots:
                kind=code_slot["kind"];slot=code_slot["slot"]
                example=next((code for label in labels for code in [c for c in label["codes"] if c["kind"]==kind][slot:slot+1]),None)
                if example:
                    rect=example["rect"];code_x=max(0,round((rect.x()-first["crop"].left())*sx,3));code_y=max(0,round((rect.y()-first["crop"].top())*sy,3))
                    code_w=max(3,round(rect.width()*sx,3));code_h=max(3,round(rect.height()*sy,3))
                else:
                    code_w=code_h=round(min(width_mm*.41,height_mm*.62),3);code_x=code_y=0
                    if kind=="datamatrix":
                        line=next((line for line in reference if re.search(r"01\d{14}21",line["text"].replace(" ",""))),None)
                        if line:
                            code_x=max(0,round((line["x"]-first["crop"].left())*sx,3))
                            code_y=max(0,round((line["y"]-first["crop"].top())*sy-code_h-2,3))
                template.elements.append(Element(kind=kind,x=code_x,y=code_y,width=code_w,height=code_h,value="{"+code_slot["key"]+"}",gs1=kind=="datamatrix",barcode_type=(example or {}).get("barcode_type","Code 128")))
            rows=[]
            for label in labels:
                row={};available=list(label["lines"])
                for descriptor in descriptors:
                    best=min(available,key=lambda line:abs((line["x"]-label["crop"].left())-descriptor["x"])+2*abs((line["y"]+line["height"]-label["crop"].top())-(descriptor["y"]+descriptor["height"]))) if available else None
                    if best and abs((best["y"]+best["height"]-label["crop"].top())-(descriptor["y"]+descriptor["height"]))<max(3,descriptor["height"]*.35):row[descriptor["key"]]=best["text"];available.remove(best)
                    else:row[descriptor["key"]]=""
                for code_slot in code_slots:
                    values=label["code_values"].get(code_slot["kind"],[])
                    value=values[code_slot["slot"]] if len(values)>code_slot["slot"] else ""
                    row[code_slot["key"]]=normalize_gs1_payload(value) if code_slot["kind"]=="datamatrix" else value
                row["PDF_RASTER"]=label["raster_data"]
                rows.append(row)
            if not rows:raise ValueError("Не удалось подготовить строки тиража из PDF.")
            code_headers={"qr":"QR","datamatrix":"DataMatrix","barcode":"Штрихкод"}
            self.add_document_tab(template);self.headers=[f"Текст {i+1}" for i in range(len(descriptors))]+[code_headers[slot["kind"]]+(f" {slot['slot']+1}" if sum(item["kind"]==slot["kind"] for item in code_slots)>1 else "") for slot in code_slots]+["Растровая графика"]
            keys=[line["key"] for line in descriptors]+[slot["key"] for slot in code_slots]+["PDF_RASTER"]
            self.table_keys=keys;self.rows=rows;self.selected_file=path
            self.file_label.setText(Path(path).name);self.detach_btn.setEnabled(True);self.from_spin.setEnabled(True)
            self.field_combo.blockSignals(True);self.field_combo.clear();self.field_combo.addItem("Вручную","");self.field_combo.addItem("Нумерация тиража","SEQ")
            for header,key in zip(self.headers,keys):
                if key!="PDF_RASTER":self.field_combo.addItem(header,key)
            self.field_combo.blockSignals(False);self.table.blockSignals(True);self.table.setAlternatingRowColors(True);self.table.setColumnCount(len(self.headers));self.table.setHorizontalHeaderLabels(self.headers);self.table.setRowCount(len(rows))
            for row_index,row in enumerate(rows):
                for column,key in enumerate(keys):
                    item=QTableWidgetItem("[растровое изображение]" if key=="PDF_RASTER" and row.get(key) else row.get(key,""))
                    if key=="PDF_RASTER":item.setFlags(item.flags() & ~Qt.ItemFlag.ItemIsEditable)
                    self.table.setItem(row_index,column,item)
            self.table.blockSignals(False)
            self.from_spin.setMaximum(len(rows));self.count_spin.setMaximum(len(rows));self.count_spin.setValue(len(rows));self.from_spin.setValue(1);self.preview_variant_spin.setValue(1)
            self.select_element(0);self.update_preview();self.refresh_print_preview();self.status.setText(f"Из PDF извлечено этикеток: {len(rows)}")
        except Exception as exc:
            if progress:progress.close()
            QMessageBox.critical(self,"Не удалось импортировать PDF",str(exc))
        finally:
            if progress:progress.close()
            document.close()

    def _table_cell_changed(self,row_index,column):
        if not (0<=row_index<len(self.rows) and 0<=column<len(self.table_keys)):return
        item=self.table.item(row_index,column)
        if item is None:return
        key=self.table_keys[column]
        if key=="PDF_RASTER":return
        self.rows[row_index][key]=item.text()
        self.update_preview();self.refresh_print_preview()

    def load_data(self):
        path,_=QFileDialog.getOpenFileName(self,"Загрузить данные","","Таблицы (*.csv *.xlsx *.xlsm)")
        if not path: return
        try:
            dialog=ImportOptionsDialog(path,self)
            if dialog.exec()!=QDialog.DialogCode.Accepted:return
            self.headers=list(dialog.headers);self.table_keys=list(dialog.headers); self.rows=[dict(row) for row in dialog.rows]
            self.selected_file=path; self.file_label.setText(Path(path).name)
            self.detach_btn.setEnabled(True); self.from_spin.setEnabled(True)
            self.field_combo.blockSignals(True); self.field_combo.clear(); self.field_combo.addItem("Вручную", "")
            self.field_combo.addItem("Нумерация тиража", "SEQ")
            for header in self.headers:
                self.field_combo.addItem(header,header)
                self.field_combo.addItem(f"GTIN из «{header}»",f"GTIN:{header}")
                self.field_combo.addItem(f"Серийный номер из «{header}»",f"SERIAL:{header}")
            self.field_combo.blockSignals(False)
            self.select_element(self.canvas.selected_index)
            self.table.blockSignals(True);self.table.setAlternatingRowColors(True); self.table.setColumnCount(len(self.headers)); self.table.setHorizontalHeaderLabels(self.headers); self.table.setRowCount(len(self.rows))
            for r,row in enumerate(self.rows):
                for c,h in enumerate(self.headers): self.table.setItem(r,c,QTableWidgetItem(row.get(h,"")))
            self.table.blockSignals(False)
            self.from_spin.setMaximum(max(1,len(self.rows))); self.count_spin.setMaximum(max(1,len(self.rows))); self.count_spin.setValue(min(max(1,len(self.rows)),max(1,self.count_spin.value())))
            self.from_spin.setValue(1); self.preview_variant_spin.setValue(1); self.update_preview()
            self.status.setText(f"Загружено строк: {len(self.rows)}")
            self.refresh_print_preview()
        except Exception as e: QMessageBox.critical(self,"Не удалось прочитать файл",str(e))

    def detach_data(self):
        self.rows=[]; self.headers=[];self.table_keys=[]; self.selected_file=""
        self.file_label.setText("Файл не выбран"); self.detach_btn.setEnabled(False)
        self.field_combo.blockSignals(True); self.field_combo.clear(); self.field_combo.addItem("Вручную",""); self.field_combo.addItem("Нумерация тиража","SEQ"); self.field_combo.blockSignals(False)
        self.table.clear(); self.table.setRowCount(0); self.table.setColumnCount(0)
        self.from_spin.setValue(1); self.from_spin.setMaximum(1); self.from_spin.setEnabled(False)
        self.count_spin.setMaximum(999999)
        self.preview_variant_spin.setValue(1)
        self.update_preview()
        self.status.setText("Источник данных отключён; доступна печать макета без таблицы.")

    def _paint_label(self,painter, row, fit_rect=None, template=None, show_editor_background=False):
        template=template or self.template
        if fit_rect is None:
            fit_rect=QRectF(0,0,painter.viewport().width(),painter.viewport().height())
        scale=min(fit_rect.width()/template.width,fit_rect.height()/template.height)
        label_w=template.width*scale; label_h=template.height*scale
        painter.save(); painter.translate(fit_rect.left()+(fit_rect.width()-label_w)/2,fit_rect.top()+(fit_rect.height()-label_h)/2); painter.scale(scale,scale)
        painter.fillRect(QRectF(0,0,template.width,template.height),QColor(template.background))
        if show_editor_background and template.background_image and template.background_image_visible:
            try:
                background=self.canvas.decoded_asset(template.background_image)
                if not background.isNull():
                    target=QRectF(0,0,template.width,template.height)
                    if template.background_image_fit=="contain":
                        ratio=min(template.width/background.width(),template.height/background.height())
                        w=background.width()*ratio;h=background.height()*ratio
                        target=QRectF((template.width-w)/2,(template.height-h)/2,w,h)
                    painter.save();painter.setOpacity(min(1,max(0,template.background_image_opacity)));painter.drawImage(target,background);painter.restore()
            except Exception:pass
        painter.save();painter.setClipRect(QRectF(0,0,template.width,template.height))
        for el in template.elements:
            _,intersects=element_bounds_in_label(el,template)
            if not intersects:continue
            r=QRectF(el.x,el.y,el.width,el.height)
            painter.save(); painter.translate(r.center()); painter.rotate(el.rotation); painter.translate(-r.center())
            if el.kind in ("text","symbol"):
                draw_text_layout(painter,el,r,self._resolved(el.value,row))
            elif el.kind in ("line","shape"):
                LabelCanvas._draw_vector_element(painter,el,r,1)
            elif el.kind=="image":
                encoded=self._resolved(el.value,row) if el.value.startswith("{") else el.asset_data
                if not encoded:encoded=el.asset_data
                image=self.canvas.decoded_asset(encoded)
                if not image.isNull():painter.drawImage(r,image)
            elif el.kind=="pdf":
                encoded=self._resolved(el.value,row) if el.value.startswith("{") else el.asset_data
                if not encoded:encoded=el.asset_data
                image=self.canvas.decoded_asset(encoded)
                if not image.isNull():painter.drawImage(r,image)
            elif el.kind=="svg":
                renderer=self.canvas.svg_renderer(el.asset_data)
                if renderer.isValid():renderer.render(painter,r)
            else:
                copy=Element(**asdict(el)); copy.value=self._resolved(el.value,row); image=self.canvas.code_image(copy)
                if image:
                    if el.kind=="barcode": self.canvas._draw_barcode(painter,copy,r,image,1,preview=False)
                    else: painter.drawImage(r,image)
            painter.restore()
        painter.restore()
        painter.restore()

    def _template_from_file(self,path):
        data=json.loads(Path(path).read_text(encoding="utf-8"))
        return self._template_from_data(data)

    @staticmethod
    def _template_from_data(data):
        elements=[]
        for raw in data.get("elements",[]):
            item=dict(raw)
            if item.get("kind","text") in ("text","symbol"):
                try:item["font_size"]=max(1,int(round(float(item.get("font_size",10)))))
                except (TypeError,ValueError):item["font_size"]=10
            elements.append(Element(**item))
        return LabelTemplate(name=data.get("name","Шаблон"),width=float(data.get("width",58)),height=float(data.get("height",40)),background=data.get("background","#ffffff"),background_image=data.get("background_image",""),background_image_opacity=float(data.get("background_image_opacity",.35)),background_image_visible=bool(data.get("background_image_visible",True)),background_image_fit=data.get("background_image_fit","stretch"),grid=float(data.get("grid",1)),guides=data.get("guides",[]),elements=elements,print_settings=data.get("print_settings",{}))

    def template_identity_for_print_index(self,index):
        blocks=[(b.path or "__current__",max(1,int(b.copies))) for b in self.composition_blocks] or [("__current__",1)]
        offset=index%sum(copies for _identity,copies in blocks)
        for identity,copies in blocks:
            if offset<copies:return identity
            offset-=copies
        return "__current__"

    def template_for_print_index(self,index):
        identity=self.template_identity_for_print_index(index)
        if identity=="__current__":return self.template
        for block in self.composition_blocks:
            if block.path==identity:
                return self._load_template_cached(block.path,block.template)
        return self.template

    def _load_template_cached(self,path,fallback=None):
        try:
            resolved=str(Path(path).resolve());stat=Path(resolved).stat();signature=(stat.st_mtime_ns,stat.st_size)
            cached=self._template_file_cache.get(resolved)
            if cached and cached[0]==signature:return cached[1]
            loaded=self._template_from_file(resolved);self._template_file_cache[resolved]=(signature,loaded);return loaded
        except Exception:
            return fallback or self.template

    def template_occurrence_before(self,index,identity):
        blocks=[(b.path or "__current__",max(1,int(b.copies))) for b in self.composition_blocks] or [("__current__",1)]
        cycle_size=sum(copies for _item,copies in blocks);cycles,remainder=divmod(index,cycle_size)
        total=sum(copies for item,copies in blocks if item==identity)*cycles
        for item,copies in blocks:
            if remainder<=0:break
            used=min(copies,remainder)
            if item==identity:total+=used
            remainder-=used
        return total

    def validate_print_job(self,ordered):
        """Return a compact list of print risks for the optional preflight prompt."""
        issues=set()
        checked_values=set()
        for template,row in ordered:
            for element_index,element in enumerate(template.elements,1):
                fully_inside,intersects=element_bounds_in_label(element,template)
                if not intersects:continue
                if not fully_inside:
                    issues.add(f"{template.name}: объект {element_index} частично выходит за границы этикетки.")
                resolved=self._resolved(element.value,row) if element.kind not in ("image","svg","line","shape") else ""
                if element.kind in ("text","symbol","qr","barcode","datamatrix"):
                    for token in re.findall(r"\{([^{}]+)\}",element.value):
                        if not self._resolved("{"+token+"}",row).strip():
                            issues.add(f"{template.name}: переменная {{{token}}} пуста в выбранном диапазоне.")
                    unresolved=re.findall(r"\{([^{}]+)\}",resolved)
                    for token in unresolved:
                        issues.add(f"{template.name}: для переменной {{{token}}} нет значения в выбранном диапазоне.")
                    if element.kind in ("qr","barcode","datamatrix") and not resolved.strip():
                        issues.add(f"{template.name}: кодовый объект {element_index} содержит пустые данные.")
                    elif element.kind in ("qr","barcode","datamatrix") and "{" not in resolved:
                        key=(element.kind,element.barcode_type,resolved,element.gs1)
                        if key not in checked_values:
                            checked_values.add(key)
                            probe=Element(**asdict(element));probe.value=resolved
                            if self.canvas.code_image(probe) is None:
                                issues.add(f"{template.name}: данные объекта {element_index} не подходят для выбранного типа кода.")
                elif element.kind in ("image","svg") and not element.asset_data:
                    issues.add(f"{template.name}: в объекте {element_index} отсутствует встроенное изображение.")
        return sorted(issues)

    def print_labels(self):
        available=len(self.rows) if self.rows else max(1,self.count_spin.value())
        initial_start=int(self.settings.value("print/range_start",self.from_spin.value()))
        initial_end=int(self.settings.value("print/range_end",min(available,self.from_spin.value()+self.count_spin.value()-1)))
        initial_copies=int(self.settings.value("print/copies",1))
        template_settings=self.template.print_settings
        saved_orientation=int(template_settings.get("orientation",self.settings.value("print/orientation",0)))
        if saved_orientation==QPageLayout.Orientation.Landscape.value:saved_orientation=90
        continue_sequence=bool(self.settings.value("print/continue_sequence",False))
        printer_config=template_settings.get("printer",{})
        if self.template_path:
            key=hashlib.sha1(str(Path(self.template_path).resolve()).encode("utf-8")).hexdigest()
            try:printer_config=json.loads(str(self.settings.value(f"printer/templates/{key}",json.dumps(printer_config))))
            except (TypeError,ValueError):pass
        printer=self.print_printer or QPrinter(QPrinter.PrinterMode.HighResolution)
        saved_name=str(printer_config.get("name",self.settings.value("printer/name","")))
        if saved_name and printer.printerName()!=saved_name:printer.setPrinterName(saved_name)
        try:
            printer.setResolution(int(printer_config.get("resolution",self.settings.value("printer/resolution",printer.resolution()))))
            printer.setColorMode(QPrinter.ColorMode(int(printer_config.get("color_mode",self.settings.value("printer/color_mode",printer.colorMode().value)))))
            printer.setDuplex(QPrinter.DuplexMode(int(printer_config.get("duplex",self.settings.value("printer/duplex",printer.duplex().value)))))
            printer.setPaperSource(QPrinter.PaperSource(int(printer_config.get("paper_source",self.settings.value("printer/paper_source",printer.paperSource().value)))))
            printer.setPageOrder(QPrinter.PageOrder(int(printer_config.get("page_order",self.settings.value("printer/page_order",printer.pageOrder().value)))))
            printer.setCollateCopies(bool(printer_config.get("collate",self.settings.value("printer/collate",True))))
        except (TypeError,ValueError):pass
        PrintPreviewDialog._restore_page_layout(printer,printer_config.get("page_layout"))
        self.print_printer=printer

        def build_order(first,last,copies,continue_seq,reverse):
            selected=self.rows[first-1:last] if self.rows else [{} for _ in range(first,last+1)]
            if not selected:raise ValueError("Выбранный диапазон пуст.")
            ordered=[];range_identity_counts={}
            for offset in range(len(selected)):
                identity=self.template_identity_for_print_index(first-1+offset)
                range_identity_counts[identity]=range_identity_counts.get(identity,0)+1
            for pass_index in range(copies):
                for offset,row in enumerate(selected):
                    absolute_index=first-1+offset
                    identity=self.template_identity_for_print_index(absolute_index)
                    template=self.template_for_print_index(absolute_index)
                    occurrence=self.template_occurrence_before(absolute_index,identity)
                    if continue_seq:occurrence+=pass_index*range_identity_counts[identity]
                    numbered=dict(row)
                    number=self.seq_start.value()+occurrence*int(self.seq_direction.currentData())
                    digits=self.seq_width.value();numbered["_SEQ"]=str(number).zfill(digits) if digits else str(number)
                    ordered.append((template,numbered))
            if reverse:ordered.reverse()
            if any(abs(t.width-self.template.width)>0.001 or abs(t.height-self.template.height)>0.001 for t,_ in ordered):
                raise ValueError("Все шаблоны в одном задании должны иметь одинаковую ширину и высоту.")
            return ordered

        def render_job(device,ordered,columns,width,rotation):
            final_order=[(self._rotated_template_copy(t,rotation) if rotation else t,row) for t,row in ordered]
            self._render_print_job(device,final_order,columns,width,preview=True)

        def send_print_job(device,ordered,columns,width,rotation,first,last,copies):
            device.setDocName(f"{APP} — {len(ordered)} этикеток")
            try:
                final_order=[(self._rotated_template_copy(t,rotation) if rotation else t,row) for t,row in ordered]
                self._render_print_job(device,final_order,columns,width,preview=False)
            except Exception as exc:
                QMessageBox.critical(self,"Ошибка печати",str(exc));return False
            self.print_printer=device
            self.from_spin.setValue(first);self.count_spin.setValue(last-first+1);self.update_preview()
            self.status.setText(f"В очередь отправлено этикеток: {len(ordered)} · страниц: {(len(ordered)+columns-1)//columns}")
            return True

        dialog=PrintPreviewDialog(self,printer,available,initial_start,initial_end,initial_copies,
                                  saved_orientation,continue_sequence,
                                  build_order,render_job,send_print_job)
        dialog.exec()

    def _render_print_job(self,printer,ordered,columns,width,preview=False):
        painter=QPainter()
        if not painter.begin(printer):raise RuntimeError("Не удалось открыть драйвер принтера.")
        try:
            label_width=ordered[0][0].width if ordered else self.template.width
            label_height=ordered[0][0].height if ordered else self.template.height
            page_width=label_width*columns+self.column_gap*(columns-1)
            # Map the app's mm coordinate space onto the requested full media page;
            # printer printable-area offsets must not shift or crop the artwork.
            viewport=printer.pageLayout().fullRectPixels(printer.resolution())
            painter.setViewport(viewport)
            painter.setWindow(QRect(0,0,max(1,round(page_width*1000)),max(1,round(label_height*1000))))
            painter.scale(1000,1000)
            for i,(template,row) in enumerate(ordered):
                if i and i%columns==0 and not printer.newPage():raise RuntimeError("Драйвер не смог добавить следующую строку этикеток.")
                col=i%columns; cell=QRectF(col*(label_width+self.column_gap),0,label_width,label_height)
                self._paint_label(painter,row,cell,template,show_editor_background=preview)
        finally:painter.end()

    def _store_print_range(self,*_):
        if not hasattr(self,"from_spin") or not self.from_spin.isEnabled():return
        first=max(1,self.from_spin.value());last=min(len(self.rows),first+self.count_spin.value()-1) if self.rows else first+self.count_spin.value()-1
        self.settings.setValue("print/range_start",first);self.settings.setValue("print/range_end",max(first,last))

    def configure_composition(self):
        if self.composition_tab is not None:
            index=self.editor_tabs.indexOf(self.composition_tab)
            if index>=0:self.editor_tabs.setCurrentIndex(index);return
        dialog=QDialog(self);dialog.setWindowFlags(Qt.WindowType.Widget);dialog.setWindowTitle("Шаблоны тиража");dialog.resize(760,580);dialog.setMinimumSize(630,440)
        self.composition_tab=dialog
        tab_index=self.editor_tabs.addTab(dialog,"Шаблоны тиража");self.editor_tabs.setCurrentIndex(tab_index)
        def remove_composition_tab(*_):
            if self.composition_tab is dialog:
                index=self.editor_tabs.indexOf(dialog);self.composition_tab=None
                if index>=0:
                    self.editor_tabs.blockSignals(True);self.editor_tabs.removeTab(index);self.editor_tabs.blockSignals(False)
                    if self.documents:self.editor_tabs.setCurrentIndex(min(index,len(self.documents)-1))
                dialog.deleteLater()
        dialog.finished.connect(remove_composition_tab)
        dialog.setStyleSheet("QDialog{background:#f3f5f8;color:#20242b} QLabel{color:#20242b} QListWidget{background:white;color:#20242b;border:1px solid #cbd2dc;border-radius:5px} QListWidget::item{padding:8px} QListWidget::item:selected{background:#dce7ff;color:#172d62} QSpinBox{background:white;color:#20242b;padding:4px} QPushButton{background:white;color:#20242b;border:1px solid #cbd2dc;border-radius:4px;padding:6px}")
        layout=QVBoxLayout(dialog)
        intro=QLabel("Блоки повторяются по кругу. Например: Шаблон A — 5 этикеток, затем шаблон B — 2; цикл повторится на всех строках тиража. Каждая этикетка расходует следующую строку данных."); intro.setWordWrap(True); layout.addWidget(intro)
        working=[CompositionBlock(b.path,b.template,b.copies) for b in self.composition_blocks]
        listing=QListWidget(); layout.addWidget(listing,1)
        def refresh():
            listing.clear()
            for block in working:
                name="Текущий шаблон" if block.path is None else Path(block.path).stem
                listing.addItem(f"{name} × {block.copies}")
        refresh()
        form=QFormLayout(); copies=QSpinBox(); copies.setRange(1,999999); form.addRow("Этикеток в блоке",copies); layout.addLayout(form)
        def select_row(index):
            if 0<=index<len(working):copies.setValue(working[index].copies)
        listing.currentRowChanged.connect(select_row)
        def change_copies(value):
            index=listing.currentRow()
            if 0<=index<len(working):working[index].copies=value; refresh(); listing.setCurrentRow(index)
        copies.valueChanged.connect(change_copies)
        controls=QHBoxLayout(); create=QPushButton("Создать шаблон…"); add=QPushButton("Добавить из файла…"); edit=QPushButton("Редактировать выбранный…"); remove=QPushButton("Удалить"); up=QPushButton("↑"); down=QPushButton("↓")
        for button in (create,add,edit,remove,up,down):controls.addWidget(button)
        controls.addStretch(); layout.addLayout(controls)
        profile_row=QHBoxLayout();save_profile=QPushButton("Сохранить последовательность…");load_profile=QPushButton("Открыть последовательность…");profile_row.addWidget(save_profile);profile_row.addWidget(load_profile);profile_row.addStretch();layout.addLayout(profile_row)
        def save_sequence():
            path,_=QFileDialog.getSaveFileName(dialog,"Сохранить последовательность","Последовательность.layout.json","Компоновка шаблонов (*.layout.json)")
            if not path:return
            if not path.lower().endswith(".layout.json"):path=Path(path).with_suffix(".layout.json").as_posix()
            try:
                Path(path).write_text(json.dumps({"blocks":[{"path":block.path,"copies":block.copies} for block in working]},ensure_ascii=False,indent=2),encoding="utf-8")
            except Exception as exc:QMessageBox.warning(dialog,"Не удалось сохранить последовательность",str(exc))
        def load_sequence():
            path,_=QFileDialog.getOpenFileName(dialog,"Открыть последовательность","","Компоновка шаблонов (*.layout.json)")
            if not path:return
            try:
                data=json.loads(Path(path).read_text(encoding="utf-8"));loaded=[]
                for record in data.get("blocks",[]):
                    source=record.get("path")
                    template=self.template if source is None else self._template_from_file(source)
                    if abs(template.width-self.template.width)>0.001 or abs(template.height-self.template.height)>0.001:raise ValueError("Размеры шаблонов должны совпадать с текущей этикеткой.")
                    loaded.append(CompositionBlock(source,template,max(1,int(record.get("copies",1)))))
                if not loaded:raise ValueError("В файле нет блоков шаблонов.")
                working[:]=loaded;refresh();listing.setCurrentRow(0)
            except Exception as exc:QMessageBox.warning(dialog,"Не удалось открыть последовательность",str(exc))
        save_profile.clicked.connect(save_sequence);load_profile.clicked.connect(load_sequence)
        def add_template():
            path,_=QFileDialog.getOpenFileName(dialog,"Добавить шаблон","","Шаблоны Label Studio (*.json)")
            if not path:return
            try:
                template=self._template_from_file(path)
                if abs(template.width-self.template.width)>0.001 or abs(template.height-self.template.height)>0.001:raise ValueError("Размеры должны совпадать с текущей этикеткой.")
                working.append(CompositionBlock(path,template,1)); refresh(); listing.setCurrentRow(len(working)-1)
            except Exception as exc:QMessageBox.warning(dialog,"Не удалось добавить шаблон",str(exc))
        def create_template():
            path,_=QFileDialog.getSaveFileName(dialog,"Создать шаблон","Новый шаблон.json","Шаблон Label Studio (*.json)")
            if not path:return
            if not path.lower().endswith(".json"):path+=".json"
            template=LabelTemplate(name=Path(path).stem,width=self.template.width,height=self.template.height,elements=[Element()])
            try:
                Path(path).write_text(json.dumps(asdict(template),ensure_ascii=False,indent=2),encoding="utf-8")
                working.append(CompositionBlock(path,template,1));refresh();listing.setCurrentRow(len(working)-1)
                editor=MainWindow(template,Path(path),True);editor.setWindowTitle(f"Редактор шаблона — {Path(path).stem}");editor.show();self.template_editors.append(editor)
            except Exception as exc:QMessageBox.warning(dialog,"Не удалось создать шаблон",str(exc))
        def edit_template():
            index=listing.currentRow()
            if not 0<=index<len(working):return
            block=working[index]
            path=block.path
            if path is None:
                path,_=QFileDialog.getSaveFileName(dialog,"Сохранить текущий шаблон для редактирования","template.json","Шаблон Label Studio (*.json)")
                if not path:return
                if not path.lower().endswith(".json"):path+=".json"
                try:Path(path).write_text(json.dumps(asdict(self.template),ensure_ascii=False,indent=2),encoding="utf-8")
                except Exception as exc:QMessageBox.warning(dialog,"Не удалось сохранить шаблон",str(exc));return
                block.path=path
                refresh();listing.setCurrentRow(index)
            editor=MainWindow(block.template,Path(path),True); editor.setWindowTitle(f"Редактор шаблона — {Path(path).stem}"); editor.show(); self.template_editors.append(editor)
            editor.destroyed.connect(lambda *_: refresh())
        def remove_block():
            index=listing.currentRow()
            if 0<=index<len(working):working.pop(index);refresh()
        def move_block(delta):
            index=listing.currentRow(); target=index+delta
            if 0<=index<len(working) and 0<=target<len(working):working[index],working[target]=working[target],working[index];refresh();listing.setCurrentRow(target)
        create.clicked.connect(create_template);add.clicked.connect(add_template);edit.clicked.connect(edit_template);remove.clicked.connect(remove_block);up.clicked.connect(lambda:move_block(-1));down.clicked.connect(lambda:move_block(1))
        buttons=QDialogButtonBox(QDialogButtonBox.StandardButton.Ok|QDialogButtonBox.StandardButton.Cancel);layout.addWidget(buttons)
        def apply_sequence():
            for block in working:
                template=self.template if block.path is None else block.template
                if abs(template.width-self.template.width)>0.001 or abs(template.height-self.template.height)>0.001:
                    QMessageBox.warning(dialog,"Размеры шаблонов не совпадают","Все шаблоны в цикле должны иметь одинаковые размеры.");return
            self.composition_blocks=working or [CompositionBlock(None,self.template,1)];self.refresh_print_preview();self.status.setText(f"Последовательность настроена: {len(working)} блоков");dialog.accept()
        buttons.accepted.connect(apply_sequence);buttons.rejected.connect(dialog.reject)
        dialog.show()

    def configure_column_layout(self):
        dialog=QDialog(self);dialog.setWindowTitle("Колонки ленты");dialog.resize(760,520)
        dialog.setStyleSheet("QDialog{background:#f3f5f8;color:#20242b} QLabel{color:#20242b} QSpinBox,QDoubleSpinBox{background:white;color:#20242b;padding:5px} QPushButton{background:white;color:#20242b;border:1px solid #cbd2dc;border-radius:4px;padding:6px}")
        root=QVBoxLayout(dialog);intro=QLabel("Предпросмотр показывает, как этикетки расположатся по ширине носителя. Проверьте допустимую ширину в настройках принтера.");intro.setWordWrap(True);root.addWidget(intro)
        columns=QSpinBox();columns.setRange(1,20);columns.setValue(self.label_columns);gap=QDoubleSpinBox();gap.setRange(0,100);gap.setDecimals(2);gap.setSuffix(" мм");gap.setValue(self.column_gap)
        orientation=QComboBox()
        for title,degrees in (("Книжная · 0°",0),("Книжная · 180°",180),("Альбомная · 90°",90),("Альбомная · 270°",270)):
            orientation.addItem(title,degrees)
        saved_orientation=self.template.print_settings.get("orientation",QPageLayout.Orientation.Portrait.value)
        if int(saved_orientation)==QPageLayout.Orientation.Landscape.value:saved_orientation=90
        orientation.setCurrentIndex(max(0,orientation.findData(saved_orientation)))
        form=QFormLayout();form.addRow("Колонок на ленте",columns);form.addRow("Зазор между этикетками",gap);form.addRow("Ориентация",orientation);root.addLayout(form)
        owner=self
        class RibbonPreview(QWidget):
            def __init__(self):super().__init__();self.setMinimumHeight(300)
            def paintEvent(self,event):
                p=QPainter(self);p.fillRect(self.rect(),QColor("#e7ebf1"));p.setRenderHint(QPainter.RenderHint.Antialiasing)
                count=columns.value(); gap_mm=gap.value(); degrees=int(orientation.currentData() or 0);rotated=degrees in (90,270)
                label_w=owner.template.height if rotated else owner.template.width;label_h=owner.template.width if rotated else owner.template.height
                page_width=label_w*count+gap_mm*(count-1)
                scale=min((self.width()-48)/page_width,(self.height()-48)/(label_h*2+8))
                w=page_width*scale; h=label_h*scale; x=(self.width()-w)/2; y=(self.height()-2*h-8*scale)/2
                for row_index in range(count*2):
                    row=row_index//count; col=row_index%count; xx=x+(col*(label_w+gap_mm))*scale; yy=y+row*(label_h+8)*scale
                    cell=QRectF(xx,yy,label_w*scale,h)
                    p.fillRect(cell,Qt.GlobalColor.white);p.setPen(QPen(QColor("#7790ae"),1));p.drawRect(cell)
                    template=owner.template_for_print_index(row_index)
                    if degrees:template=owner._rotated_template_copy(template,degrees)
                    owner._paint_label(p,owner.canvas.preview_row,cell,template,show_editor_background=True)
                p.setPen(QColor("#4b596b"));p.drawText(QRectF(8,8,self.width()-16,22),Qt.AlignmentFlag.AlignLeft,f"Предпросмотр · {count} колонок · ширина ленты {page_width:.2f} мм")
        preview=RibbonPreview();root.addWidget(preview,1);columns.valueChanged.connect(preview.update);gap.valueChanged.connect(preview.update);orientation.currentIndexChanged.connect(preview.update)
        buttons=QDialogButtonBox(QDialogButtonBox.StandardButton.Ok|QDialogButtonBox.StandardButton.Cancel);buttons.accepted.connect(dialog.accept);buttons.rejected.connect(dialog.reject);root.addWidget(buttons)
        if dialog.exec()==QDialog.DialogCode.Accepted:
            self.label_columns=columns.value();self.column_gap=gap.value();self.settings.setValue("label_columns",self.label_columns);self.settings.setValue("column_gap",self.column_gap)
            self.template.print_settings.update(columns=self.label_columns,column_gap=self.column_gap,orientation=orientation.currentData())
            if self.document:self.document.update(columns=self.label_columns,gap=self.column_gap)
            self.refresh_print_preview();self.status.setText(f"Печатная область: {self.label_columns} колонок, зазор {self.column_gap:.2f} мм")

    def _write_template(self,path):
        self.history_timer.stop();self._commit_history_change()
        data=asdict(self.template)
        target=Path(path)
        if target.suffix.lower()!=".json": target=target.with_suffix(".json")
        try:
            target.write_text(json.dumps(data,ensure_ascii=False,indent=2),encoding="utf-8")
            self.template_path=target
            if self.document:
                self.document["path"]=target;self.document["saved"]=self._snapshot_document();self.document["last"]=self.document["saved"];self.document["dirty"]=False
                self._update_tab_title(self.document)
            self.setWindowTitle(f"{APP} — {target.stem}"); self.status.setText(f"Шаблон сохранён: {target.name}")
            QMessageBox.information(self,"Шаблон сохранён",f"Файл сохранён:\n{target}")
        except Exception as e: QMessageBox.critical(self,"Ошибка сохранения",str(e))

    def save_template(self):
        if self.template_path:
            self._write_template(self.template_path)
        else:
            self.save_template_as()

    def save_template_as(self):
        default=str(self.template_path or Path.cwd()/f"{self.template.name}.json")
        path,_=QFileDialog.getSaveFileName(self,"Сохранить шаблон как",default,"Шаблон Label Studio (*.json)")
        if path:self._write_template(path)

    def open_template(self):
        path,_=QFileDialog.getOpenFileName(self,"Открыть шаблон","","Шаблон Label Studio (*.json)")
        if not path:return
        try:
            target=Path(path).resolve()
            for index,doc in enumerate(self.documents):
                if doc.get("path") and Path(doc["path"]).resolve()==target:
                    self.editor_tabs.setCurrentIndex(index);return
            template=self._template_from_file(target);self.add_document_tab(template,target)
            self.status.setText(f"Открыт шаблон: {target.name}")
        except Exception as e: QMessageBox.critical(self,"Ошибка открытия шаблона",str(e))

    def new_template(self):
        self.add_document_tab(LabelTemplate(elements=[Element()]))


if __name__ == "__main__":
    app=QApplication(sys.argv); app.setApplicationName(APP)
    icon_root=Path(getattr(sys,"_MEIPASS",Path(__file__).resolve().parent)); app_icon=icon_root/"assets"/"labelstudio.ico"
    if app_icon.exists():app.setWindowIcon(QIcon(str(app_icon)))
    win=MainWindow(); win.show(); sys.exit(app.exec())
