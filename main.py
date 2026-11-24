from __future__ import annotations

import csv
import base64
import json
import math
import re
import sys
from dataclasses import asdict, dataclass, field
from pathlib import Path
from typing import Any

from PySide6.QtCore import Qt, QSizeF, QRectF, QPointF, Signal, QMarginsF, QSettings, QByteArray
from PySide6.QtGui import QColor, QFont, QImage, QPainter, QPen, QPixmap, QPageSize, QPageLayout, QAction, QKeySequence, QShortcut, QIcon
from PySide6.QtSvg import QSvgRenderer
from PySide6.QtPrintSupport import QPrinter, QPrintDialog
from PySide6.QtWidgets import (
    QApplication, QAbstractItemView, QCheckBox, QComboBox, QColorDialog, QDoubleSpinBox, QGridLayout, QDialog, QDialogButtonBox,
    QFileDialog, QFormLayout, QFrame, QHBoxLayout, QLabel, QLineEdit, QMainWindow, QFontComboBox,
    QMessageBox, QPushButton, QSpinBox, QTableWidget, QTableWidgetItem, QTabWidget, QToolButton, QMenu,
    QToolBar, QVBoxLayout, QWidget, QHeaderView, QListWidget, QListWidgetItem, QScrollArea, QDockWidget,
)

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


def extract_gs1_fields(raw: str) -> dict[str, str]:
    """Extract common GTIN (AI 01) and serial (AI 21) fields from GS1/ЧЗ text."""
    value = str(raw or "").replace("\x1d", "<GS>").replace("\\x1d", "<GS>")
    value = re.sub(r"^\]d2", "", value, flags=re.IGNORECASE).strip()
    value = value.replace("(01)", "01").replace("(21)", "21").replace("(91)", "91").replace("(92)", "92")
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


@dataclass
class CompositionBlock:
    path: str | None
    template: LabelTemplate
    copies: int = 1


class LabelCanvas(QWidget):
    selected = Signal(int)
    moved = Signal()
    zoomChanged = Signal(float)

    def __init__(self, template: LabelTemplate):
        super().__init__()
        self.template = template
        self.selected_index = -1
        self.show_grid = True
        self.show_guides = True
        self.preview_row: dict[str, Any] = {}
        self.scale = 8.0
        self.zoom_factor=1.0
        self.pan_offset=QPointF(0,0)
        self.pan_start=None
        self.pan_mode=False
        self.drag_offset: tuple[float, float] | None = None
        self.drag_start: tuple[float, float, float, float, float] | None = None
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
        p.setClipRect(label)
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
            if i == self.selected_index:
                p.setPen(QPen(QColor(ACCENT), 1.5, Qt.PenStyle.DashLine))
                p.setBrush(Qt.BrushStyle.NoBrush)
                p.drawRect(r)
                p.setPen(QPen(QColor(ACCENT),1)); p.setBrush(QColor("#ffffff"))
                for point in self._handle_points(r): p.drawRect(QRectF(point.x()-3.5,point.y()-3.5,7,7))
                if self.show_guides:
                    p.setPen(QPen(QColor(ACCENT + "88"), 1, Qt.PenStyle.DotLine))
                    p.drawLine(int(r.center().x()), int(y0), int(r.center().x()), int(y0 + h))
                    p.drawLine(int(x0), int(r.center().y()), int(x0 + w), int(r.center().y()))
            p.restore()
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
            image=QImage.fromData(base64.b64decode(el.asset_data)) if el.asset_data else QImage()
            if not image.isNull():p.drawImage(r,image)
            else:p.drawRect(r)
            return
        if el.kind=="svg":
            try:
                renderer=QSvgRenderer(QByteArray(base64.b64decode(el.asset_data)))
                if renderer.isValid():renderer.render(p,r)
                else:p.drawRect(r)
            except Exception:p.drawRect(r)
            return
        if el.kind in ("text","symbol"):
            p.save()
            px = max(6, int(el.font_size * 96 / 72 * scale / 3.78))
            f = QFont(el.font_family); f.setPixelSize(px); f.setBold(el.bold); f.setItalic(el.italic); f.setUnderline(el.underline); p.setFont(f); p.setPen(QColor(el.color))
            text = self.resolve(el.value)
            flags=Qt.AlignmentFlag.AlignCenter if el.kind=="symbol" else self._text_flags(el)
            p.drawText(r, flags, text)
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
        caption_mm=max(1.5,(el.hri_font_size * 25.4 / 72) * (1.45 if preview else 1.35))
        caption_height=min(rect.height()*.32,caption_mm*(scale if preview else 1))
        gap=min(.45*(scale if preview else 1),rect.height()*.035)
        if position == "top": barcode_rect=QRectF(rect.left(),rect.top()+caption_height+gap,rect.width(),max(1,rect.height()-caption_height-gap))
        elif position == "bottom": barcode_rect=QRectF(rect.left(),rect.top(),rect.width(),max(1,rect.height()-caption_height-gap))
        elif position == "both": barcode_rect=QRectF(rect.left(),rect.top()+caption_height+gap,rect.width(),max(1,rect.height()-caption_height*2-gap*2))
        else: barcode_rect=rect
        painter.save(); painter.setClipRect(rect); painter.drawImage(barcode_rect,image)
        text=self.resolve(el.value)
        font=QFont("Arial")
        wanted=round(el.hri_font_size*96/72*scale/3.78) if preview else round(el.hri_font_size*25.4/72)
        available=caption_height
        font.setPixelSize(max(1,min(wanted,round(available*.72)))); painter.setFont(font); painter.setPen(QColor(el.color))
        flags={"left":Qt.AlignmentFlag.AlignLeft,"center":Qt.AlignmentFlag.AlignHCenter,"right":Qt.AlignmentFlag.AlignRight}.get(el.hri_alignment,Qt.AlignmentFlag.AlignHCenter)|Qt.AlignmentFlag.AlignVCenter
        if position in ("top","both"):
            painter.drawText(QRectF(rect.left(),rect.top(),rect.width(),caption_height),flags,text)
        if position in ("bottom","both"):
            y=rect.bottom()-caption_height
            painter.drawText(QRectF(rect.left(),y,rect.width(),caption_height),flags,text)
        painter.restore()

    def code_image(self, el: Element) -> QImage | None:
        text = self.resolve(el.value) or "SAMPLE"
        try:
            if el.kind == "qr":
                import qrcode
                pil = qrcode.make(text).convert("RGB")
            elif el.kind == "datamatrix":
                from pystrich.datamatrix import DataMatrixData, DataMatrixEncoder, FNC1
                payload = DataMatrixData(FNC1, text, encoding="ascii") if el.gs1 else DataMatrixData(text, auto_encoding=True)
                image = QImage.fromData(DataMatrixEncoder(payload).get_imagedata(cellsize=5))
                return image if not image.isNull() else None
            else:
                import barcode
                from barcode.writer import ImageWriter
                from io import BytesIO
                from PIL import Image
                image_bytes = BytesIO()
                symbology = {"Code 128": "code128", "Code 39": "code39", "EAN-13": "ean13", "UPC-A": "upca", "ITF": "itf"}.get(el.barcode_type, "code128")
                barcode.get(symbology, text, writer=ImageWriter()).write(image_bytes,
                    options={"module_height": 12, "quiet_zone": 1, "font_size": 0, "text_distance": 0, "write_text": False})
                pil = Image.open(image_bytes).convert("RGB")
            from io import BytesIO
            buf = BytesIO(); pil.save(buf, format="PNG")
            image = QImage.fromData(buf.getvalue())
            return image if not image.isNull() else None
        except Exception:
            return None

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
        if 0 <= self.selected_index < len(self.template.elements):
            el=self.template.elements[self.selected_index]
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
                self.selected_index = i
                self.drag_start = (event.position().x(),event.position().y(),el.x,el.y,el.rotation)
                self.drag_offset = (0,0)
                self.selected.emit(i); self.update(); self.setFocus(); return
        if self.show_guides:
            for i in range(len(self.template.guides) - 1, -1, -1):
                guide = self.template.guides[i]
                delta = abs(event.position().x() - (ox + float(guide["position"]) * scale)) if guide["orientation"] == "vertical" else abs(event.position().y() - (oy + float(guide["position"]) * scale))
                if delta <= 7:
                    self.drag_guide = i; return
        self.selected_index = -1; self.selected.emit(-1); self.update()
        self.setFocus()

    def mouseMoveEvent(self, event):
        if self.pan_start is not None:
            start,offset=self.pan_start;delta=event.position()-start
            self.pan_offset=QPointF(offset.x()+delta.x(),offset.y()+delta.y());self.update();return
        if self.drag_guide is not None:
            ox, oy = self.origin; guide = self.template.guides[self.drag_guide]
            raw = (event.position().x() - ox) / self.scale if guide["orientation"] == "vertical" else (event.position().y() - oy) / self.scale
            limit = self.template.width if guide["orientation"] == "vertical" else self.template.height
            guide["position"] = round(min(max(raw, 0), limit), 3); self.update(); return
        if self.resize_data is not None and 0 <= self.selected_index < len(self.template.elements):
            self._resize_selected(event.position()); self.moved.emit(); self.update(); return
        if self.drag_start is None or self.selected_index < 0:
            return
        el = self.template.elements[self.selected_index]
        sx,sy,start_x,start_y,angle=self.drag_start
        dx=event.position().x()-sx; dy=event.position().y()-sy
        proposed_x=round(max(0,start_x+dx/self.scale),3); proposed_y=round(max(0,start_y+dy/self.scale),3)
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
        self.drag_offset = None
        self.drag_start = None
        self.drag_guide = None
        self.resize_data = None
        self.alignment_x = self.alignment_y = None
        self.update()

    def mouseDoubleClickEvent(self,event):
        if event.button()==Qt.MouseButton.LeftButton and not self.pan_mode:
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
        if el and event.key() in (Qt.Key.Key_Left, Qt.Key.Key_Right, Qt.Key.Key_Up, Qt.Key.Key_Down):
            step = 1.0 if event.modifiers() & Qt.KeyboardModifier.ShiftModifier else .1
            dx = step if event.key() == Qt.Key.Key_Right else -step if event.key() == Qt.Key.Key_Left else 0
            dy = step if event.key() == Qt.Key.Key_Down else -step if event.key() == Qt.Key.Key_Up else 0
            el.x = max(0, round(el.x + dx, 3)); el.y = max(0, round(el.y + dy, 3))
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


class MainWindow(QMainWindow):
    def __init__(self, initial_template: LabelTemplate | None = None, initial_path: Path | None = None, editor_only: bool = False):
        super().__init__()
        self.setWindowTitle(APP)
        self.resize(1440, 900)
        self.settings=QSettings("DataMatrixPrinter","LabelStudio")
        self.template = initial_template or LabelTemplate(elements=[Element()])
        self.rows: list[dict[str, Any]] = []
        self.headers: list[str] = []
        self.selected_file = ""
        self.template_path: Path | None = initial_path
        self.editor_only=editor_only
        self.composition_blocks: list[CompositionBlock] = [CompositionBlock(None,self.template,1)]
        self.label_columns = int(self.settings.value("label_columns",1))
        self.column_gap = float(self.settings.value("column_gap",0.0))
        self.template_editors=[]
        icon_root=Path(getattr(sys,"_MEIPASS",Path(__file__).resolve().parent))
        icon_path=icon_root/"assets"/"labelstudio.ico"
        if icon_path.exists():self.setWindowIcon(QIcon(str(icon_path)))
        self._build_ui()
        self._add_shortcuts()
        self._style()
        dock_state=self.settings.value("dock_state")
        geometry=self.settings.value("window_geometry")
        if dock_state: self.restoreState(dock_state)
        if geometry: self.restoreGeometry(geometry)
        if self.editor_only:self.data_dock.hide()

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
        self.object_list.currentRowChanged.connect(self.select_element)
        ll.addWidget(self.object_list, 1)
        self.add_buttons = QGridLayout(); self.add_buttons.setContentsMargins(0,0,0,0); self.add_buttons.setHorizontalSpacing(4); self.add_buttons.setVerticalSpacing(4)
        insert_items = [
            ("Текст","text","Текст","T",0,0),("Штрихкод","barcode","123456789","▥",0,1),("QR","qr","https://","⌗",0,2),
            ("DataMatrix","datamatrix","010460123456789021ABC","▦",1,0),("Линия","line","","／",1,1),("Фигура","shape","","□",1,2),
            ("Изображение","image","","▧",2,0),("SVG","svg","","◇",2,1),("Символ","symbol","★","★",3,0),
        ]
        for name,kind,val,glyph,row,col in insert_items:
            btn=QPushButton(name); btn.setIcon(self.glyph_icon(glyph)); btn.setToolTip(f"Добавить объект: {name}")
            if kind=="image":btn.clicked.connect(self.insert_image)
            elif kind=="svg":btn.clicked.connect(self.insert_svg)
            else:btn.clicked.connect(lambda _=False,k=kind,v=val:self.add_element(k,v))
            self.add_buttons.addWidget(btn,row,col,1,3 if kind=="symbol" else 1)
        ll.addLayout(self.add_buttons)
        self.canvas = LabelCanvas(self.template); self.canvas.selected.connect(self.select_element); self.canvas.moved.connect(self.refresh_properties)
        self.canvas.moved.connect(self.refresh_print_preview)
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
        self.canvas.setToolTip("Колесо мыши — масштаб · средняя кнопка или Space+перетаскивание — перемещение области просмотра · двойной щелчок — вписать")
        top.addWidget(self.grid_btn); top.addWidget(self.guides_btn); top.addWidget(add_v); top.addWidget(add_h);top.addWidget(bg_settings); top.addSpacing(14);top.addWidget(zoom_out);top.addWidget(self.zoom_label);top.addWidget(zoom_in);top.addWidget(fit_view); cl.addLayout(top); cl.addWidget(self.canvas, 1)
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
        self.hri_position_combo=QComboBox(); self.hri_position_combo.addItem("Скрыть","hidden"); self.hri_position_combo.addItem("Сверху","top"); self.hri_position_combo.addItem("Снизу","bottom"); self.hri_position_combo.addItem("Сверху и снизу","both")
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
        self.text_form.addRow("Символ",self.symbol_combo); self.text_form.addRow("Шрифт", self.font_family_combo); self.text_form.addRow("Размер, pt", self.font_spin); self.text_form.addRow("Стиль", self.style_box); self.text_form.addRow("Цвет", self.text_color_btn)
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
        self.font_family_combo.currentFontChanged.connect(lambda font: self.change_prop("font_family",font.family()))
        self.bold_check.toggled.connect(lambda value:self.change_prop("bold",value)); self.italic_check.toggled.connect(lambda value:self.change_prop("italic",value)); self.underline_check.toggled.connect(lambda value:self.change_prop("underline",value))
        self.align_h_combo.currentIndexChanged.connect(lambda _=0:self.change_prop("horizontal_alignment",self.align_h_combo.currentData()))
        self.align_v_combo.currentIndexChanged.connect(lambda _=0:self.change_prop("vertical_alignment",self.align_v_combo.currentData()))
        self.hri_position_combo.currentIndexChanged.connect(lambda _=0:self.change_prop("hri_position",self.hri_position_combo.currentData()))
        self.hri_align_combo.currentIndexChanged.connect(lambda _=0:self.change_prop("hri_alignment",self.hri_align_combo.currentData()))
        self.hri_font_spin.valueChanged.connect(lambda value:self.change_prop("hri_font_size",value))
        for s, attr in [(self.x_spin, "x"), (self.y_spin, "y"), (self.w_spin, "width"), (self.h_spin, "height"), (self.font_spin, "font_size")]:
            s.valueChanged.connect(lambda v, a=attr: self.change_prop(a, v))
        del_btn = QPushButton("Удалить объект"); del_btn.setIcon(self.glyph_icon("×","#c83e55")); del_btn.clicked.connect(self.delete_element); rl.addWidget(del_btn)
        right.setMinimumWidth(300); left.setMinimumWidth(260); center.setMinimumSize(400,430)

        data_panel = QFrame(); data_panel.setObjectName("panel")
        data_layout=QVBoxLayout(data_panel); data_layout.setContentsMargins(10,8,10,8); data_layout.setSpacing(8)
        data_content=QWidget(); data_content.setMinimumWidth(570); dl=QVBoxLayout(data_content); dl.setContentsMargins(0,0,0,0)
        data_head = QHBoxLayout(); data_head.addWidget(self.section("ИСТОЧНИК ДАННЫХ И ТИРАЖ")); data_head.addStretch()
        self.file_label = QLabel("Файл не выбран"); self.file_label.setStyleSheet(f"color:{MUTED}")
        load_btn = QPushButton("Импорт CSV / XLSX"); load_btn.setIcon(self.glyph_icon("↥")); load_btn.clicked.connect(self.load_data)
        self.detach_btn=QPushButton("Отвязать файл"); self.detach_btn.setIcon(self.glyph_icon("×","#c83e55")); self.detach_btn.setEnabled(False); self.detach_btn.setToolTip("Отключить источник данных и печатать макет с нумерацией."); self.detach_btn.clicked.connect(self.detach_data)
        data_head.addWidget(self.file_label); data_head.addWidget(self.detach_btn); data_head.addWidget(load_btn); dl.addLayout(data_head)
        self.table = QTableWidget(0, 0); self.table.setMaximumHeight(180); self.table.setToolTip("Нажмите на строку, чтобы увидеть именно эту запись на этикетке."); self.table.setEditTriggers(QAbstractItemView.EditTrigger.NoEditTriggers); self.table.horizontalHeader().setSectionResizeMode(QHeaderView.ResizeMode.Stretch); dl.addWidget(self.table)
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
        self.setCentralWidget(center)
        self.objects_dock=self._create_dock("Элементы макета",left,"objectsDock")
        self.properties_dock=self._create_dock("Свойства",right,"propertiesDock")
        self.data_dock=self._create_dock("Данные тиража",data_panel,"dataDock")
        self.preview_dock=self._create_dock("Предпросмотр тиража",preview_panel,"previewDock")
        if self.editor_only:self.data_dock.hide()
        self.addDockWidget(Qt.DockWidgetArea.LeftDockWidgetArea,self.objects_dock)
        self.addDockWidget(Qt.DockWidgetArea.RightDockWidgetArea,self.properties_dock)
        self.addDockWidget(Qt.DockWidgetArea.BottomDockWidgetArea,self.data_dock)
        self.addDockWidget(Qt.DockWidgetArea.BottomDockWidgetArea,self.preview_dock)
        self.splitDockWidget(self.data_dock,self.preview_dock,Qt.Orientation.Horizontal)
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

    def restore_default_docks(self):
        self.addDockWidget(Qt.DockWidgetArea.LeftDockWidgetArea,self.objects_dock)
        self.addDockWidget(Qt.DockWidgetArea.RightDockWidgetArea,self.properties_dock)
        self.addDockWidget(Qt.DockWidgetArea.BottomDockWidgetArea,self.data_dock)
        self.addDockWidget(Qt.DockWidgetArea.BottomDockWidgetArea,self.preview_dock)
        self.splitDockWidget(self.data_dock,self.preview_dock,Qt.Orientation.Horizontal)
        self.resizeDocks([self.objects_dock,self.properties_dock],[300,350],Qt.Orientation.Horizontal)
        self.resizeDocks([self.data_dock,self.preview_dock],[240,240],Qt.Orientation.Vertical)
        self.resizeDocks([self.data_dock,self.preview_dock],[900,300],Qt.Orientation.Horizontal)

    def closeEvent(self,event):
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
        x,y=self._next_free_position(width,height)
        el = Element(kind=kind, x=x, y=y, gs1=(kind == "datamatrix"), width=width, height=height, value=value)
        self.template.elements.append(el); self.refresh_object_list(); self.canvas.selected_index = len(self.template.elements)-1; self.canvas.update(); self.select_element(self.canvas.selected_index); self.canvas.setFocus(); self.refresh_print_preview()

    def insert_image(self):
        path,_=QFileDialog.getOpenFileName(self,"Вставить изображение","","Изображения (*.png *.jpg *.jpeg *.bmp *.webp)")
        if path:self._insert_asset(path,"image")

    def insert_svg(self):
        path,_=QFileDialog.getOpenFileName(self,"Вставить SVG","","Векторные изображения (*.svg)")
        if path:self._insert_asset(path,"svg")

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
            x,y=self._next_free_position(width,height)
            el=Element(kind=kind,x=x,y=y,width=width,height=height,value=Path(path).name,asset_data=base64.b64encode(raw).decode("ascii"))
            self.template.elements.append(el);self.canvas.selected_index=len(self.template.elements)-1;self.refresh_object_list();self.select_element(self.canvas.selected_index);self.canvas.update();self.refresh_print_preview()
        except Exception as exc:QMessageBox.warning(self,"Не удалось вставить изображение",str(exc))

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
        labels = {"text":"Текст", "barcode":"Штрихкод", "qr":"QR-код", "datamatrix":"DataMatrix","line":"Линия","shape":"Фигура","symbol":"Символ","image":"Изображение","svg":"SVG"}
        current = self.canvas.selected_index
        self.object_list.blockSignals(True); self.object_list.clear()
        for index, element in enumerate(self.template.elements):
            item = QListWidgetItem(f"{index + 1:02d}   {labels.get(element.kind, element.kind)}")
            item.setToolTip(element.value)
            self.object_list.addItem(item)
        if 0 <= current < self.object_list.count(): self.object_list.setCurrentRow(current)
        self.object_list.blockSignals(False)

    def select_element(self, index):
        self.canvas.selected_index = index
        if hasattr(self, "object_list") and self.object_list.currentRow() != index:
            self.object_list.blockSignals(True); self.object_list.setCurrentRow(index); self.object_list.blockSignals(False)
        enabled = 0 <= index < len(self.template.elements)
        el = self.template.elements[index] if enabled else None
        self.align_panel.setEnabled(enabled)
        asset_selected=enabled and el.kind in ("image","svg")
        text_selected=enabled and el.kind in ("text","symbol"); symbol_selected=enabled and el.kind=="symbol"
        barcode_selected=enabled and el.kind=="barcode"; gs1_selected=enabled and el.kind=="datamatrix"
        vector_selected=enabled and el.kind in ("line","shape"); shape_selected=enabled and el.kind=="shape"
        for w in (self.x_spin,self.y_spin,self.w_spin,self.h_spin,self.rotation_spin): w.setEnabled(enabled)
        for w in (self.value_edit,self.variable_button,self.field_combo):w.setEnabled(enabled and not asset_selected)
        if asset_selected:self.value_edit.setToolTip("Имя встроенного файла. Для замены удалите элемент и вставьте изображение заново.")
        else:self.value_edit.setToolTip("Текст или переменная, например {GTIN:Код}")
        for w in (self.font_family_combo,self.font_spin,self.style_box,self.text_color_btn,self.align_h_combo,self.align_v_combo): w.setEnabled(text_selected)
        self.symbol_combo.setEnabled(symbol_selected)
        for w in (self.barcode_combo,self.hri_position_combo,self.hri_align_combo,self.hri_font_spin): w.setEnabled(barcode_selected)
        self.gs1_check.setEnabled(gs1_selected); self.dm_summary.setEnabled(gs1_selected)
        for w in (self.shape_type_combo,self.fill_check,self.fill_color_btn): w.setEnabled(shape_selected)
        self.stroke_color_btn.setEnabled(vector_selected)
        for w in (self.line_width_spin,self.line_style_combo): w.setEnabled(vector_selected)
        self.property_tabs.setTabEnabled(2,text_selected)
        self.property_tabs.setTabEnabled(3,barcode_selected or gs1_selected or (enabled and el.kind=="qr"))
        self.property_tabs.setTabEnabled(4,vector_selected)
        if vector_selected: self.property_tabs.setCurrentIndex(4)
        elif barcode_selected or gs1_selected or (enabled and el.kind=="qr"): self.property_tabs.setCurrentIndex(3)
        elif symbol_selected: self.property_tabs.setCurrentIndex(2)
        if enabled:
            for s,v in [(self.x_spin,el.x),(self.y_spin,el.y),(self.w_spin,el.width),(self.h_spin,el.height),(self.font_spin,el.font_size)]:
                s.blockSignals(True); s.setValue(v); s.blockSignals(False)
            self.value_edit.blockSignals(True); self.value_edit.setText(el.value); self.value_edit.blockSignals(False)
            self.field_combo.blockSignals(True)
            saved = el.value
            self.field_combo.setCurrentIndex(max(0, self.field_combo.findData(saved[1:-1] if saved.startswith("{") and saved.endswith("}") else "")))
            self.field_combo.blockSignals(False)
            self.barcode_combo.blockSignals(True); self.barcode_combo.setCurrentText(el.barcode_type); self.barcode_combo.blockSignals(False)
            self.rotation_spin.blockSignals(True); self.rotation_spin.setValue(el.rotation); self.rotation_spin.blockSignals(False)
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

    def refresh_properties(self):
        el=self.selected_element()
        if el:
            for spin,value in ((self.x_spin,el.x),(self.y_spin,el.y),(self.w_spin,el.width),(self.h_spin,el.height),(self.rotation_spin,el.rotation)):
                spin.blockSignals(True); spin.setValue(value); spin.blockSignals(False)

    def change_value(self):
        el=self.selected_element()
        if el:
            el.value=self.value_edit.text()
            if el.kind=="symbol": self.symbol_combo.blockSignals(True); self.symbol_combo.setCurrentText(el.value); self.symbol_combo.blockSignals(False)
            self.canvas.update(); self.refresh_dm_summary(); self.refresh_print_preview()

    def change_symbol(self,value):
        el=self.selected_element()
        if el and el.kind=="symbol":
            el.value=value; self.value_edit.setText(value); self.canvas.update(); self.refresh_print_preview()

    def choose_fill_color(self):
        el=self.selected_element()
        if not el:return
        color=QColorDialog.getColor(QColor(el.fill_color),self,"Цвет заливки")
        if color.isValid():
            el.fill_color=color.name(); self.fill_color_btn.setIcon(self.glyph_icon("■",el.fill_color)); self.canvas.update(); self.refresh_print_preview()

    def choose_stroke_color(self):
        el=self.selected_element()
        if not el:return
        color=QColorDialog.getColor(QColor(el.color),self,"Цвет контура")
        if color.isValid():
            el.color=color.name(); self.stroke_color_btn.setIcon(self.glyph_icon("●",el.color)); self.canvas.update(); self.refresh_print_preview()

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
        el=self.selected_element()
        if el and el.kind == "barcode": el.barcode_type=value; self.canvas.update(); self.refresh_print_preview()

    def change_gs1(self, value):
        el=self.selected_element()
        if el and el.kind == "datamatrix": el.gs1=value; self.canvas.update(); self.refresh_dm_summary(); self.refresh_print_preview()

    def change_field(self, idx):
        el=self.selected_element()
        if el and idx > 0:
            token=str(self.field_combo.currentData())
            if token.startswith("GTIN:") or token.startswith("SERIAL:"): el.value="{"+token+"}"
            elif token=="SEQ": el.value="{SEQ}"
            else: el.value="{"+token+"}"
            self.value_edit.setText(el.value); self.canvas.update(); self.refresh_dm_summary(); self.refresh_print_preview()

    def change_prop(self, attr, value):
        el=self.selected_element()
        if el: setattr(el,attr,value); self.canvas.update(); self.refresh_print_preview()

    def choose_text_color(self):
        el=self.selected_element()
        if not el:return
        color=QColorDialog.getColor(QColor(el.color),self,"Цвет текста")
        if color.isValid(): el.color=color.name(); self.text_color_btn.setIcon(self.glyph_icon("●",el.color)); self.text_color_btn.setToolTip(f"Цвет текста: {el.color}"); self.canvas.update(); self.refresh_print_preview()

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
        self.canvas.show_guides=True; self.guides_btn.setChecked(True); self.canvas.update()

    def align_selected(self, alignment):
        el=self.selected_element()
        if not el:return
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
        el=self.selected_element()
        if el:
            el.rotation=round((el.rotation + degrees) % 360, 3)
            self.rotation_spin.blockSignals(True); self.rotation_spin.setValue(el.rotation); self.rotation_spin.blockSignals(False)
            self.canvas.update(); self.refresh_print_preview()

    def rotate_element_cw(self): self.rotate_element(90)
    def rotate_element_ccw(self): self.rotate_element(-90)

    def rotate_label(self, clockwise=True):
        old_w,old_h=self.template.width,self.template.height
        for el in self.template.elements:
            if clockwise:
                el.x,el.y=round(old_h-el.y-el.height,3),round(el.x,3)
            else:
                el.x,el.y=round(el.y,3),round(old_w-el.x-el.width,3)
            el.width,el.height=el.height,el.width
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

    def rotate_label_cw(self): self.rotate_label(True)
    def rotate_label_ccw(self): self.rotate_label(False)

    def delete_element(self):
        i=self.canvas.selected_index
        if 0 <= i < len(self.template.elements):
            self.template.elements.pop(i); self.canvas.selected_index=min(i,len(self.template.elements)-1); self.refresh_object_list(); self.select_element(self.canvas.selected_index); self.refresh_print_preview()

    def set_background(self):
        color=QColorDialog.getColor(QColor(self.template.background),self,"Фон этикетки")
        if color.isValid(): self.template.background=color.name(); self.canvas.update(); self.refresh_print_preview()

    def set_background_image(self):
        path,_=QFileDialog.getOpenFileName(self,"Выбрать подложку этикетки","","Изображения (*.png *.jpg *.jpeg *.bmp *.webp)")
        if not path:
            if self.template.background_image:self.configure_background_image()
            return
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

    def load_data(self):
        path,_=QFileDialog.getOpenFileName(self,"Загрузить данные","","Таблицы (*.csv *.xlsx *.xlsm)")
        if not path: return
        try:
            dialog=ImportOptionsDialog(path,self)
            if dialog.exec()!=QDialog.DialogCode.Accepted:return
            self.headers=list(dialog.headers); self.rows=[dict(row) for row in dialog.rows]
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
            self.table.setAlternatingRowColors(True); self.table.setColumnCount(len(self.headers)); self.table.setHorizontalHeaderLabels(self.headers); self.table.setRowCount(len(self.rows))
            for r,row in enumerate(self.rows):
                for c,h in enumerate(self.headers): self.table.setItem(r,c,QTableWidgetItem(row.get(h,"")))
            self.from_spin.setMaximum(max(1,len(self.rows))); self.count_spin.setMaximum(max(1,len(self.rows))); self.count_spin.setValue(min(max(1,len(self.rows)),max(1,self.count_spin.value())))
            self.from_spin.setValue(1); self.preview_variant_spin.setValue(1); self.update_preview()
            self.status.setText(f"Загружено строк: {len(self.rows)}")
            self.refresh_print_preview()
        except Exception as e: QMessageBox.critical(self,"Не удалось прочитать файл",str(e))

    def detach_data(self):
        self.rows=[]; self.headers=[]; self.selected_file=""
        self.file_label.setText("Файл не выбран"); self.detach_btn.setEnabled(False)
        self.field_combo.blockSignals(True); self.field_combo.clear(); self.field_combo.addItem("Вручную",""); self.field_combo.addItem("Нумерация тиража","SEQ"); self.field_combo.blockSignals(False)
        self.table.clear(); self.table.setRowCount(0); self.table.setColumnCount(0)
        self.from_spin.setValue(1); self.from_spin.setMaximum(1); self.from_spin.setEnabled(False)
        self.count_spin.setMaximum(999999)
        self.preview_variant_spin.setValue(1)
        self.update_preview()
        self.status.setText("Источник данных отключён; доступна печать макета без таблицы.")

    def _paint_label(self,painter, row, fit_rect=None, template=None):
        template=template or self.template
        if fit_rect is None:
            fit_rect=QRectF(0,0,painter.viewport().width(),painter.viewport().height())
        scale=min(fit_rect.width()/template.width,fit_rect.height()/template.height)
        label_w=template.width*scale; label_h=template.height*scale
        painter.save(); painter.translate(fit_rect.left()+(fit_rect.width()-label_w)/2,fit_rect.top()+(fit_rect.height()-label_h)/2); painter.scale(scale,scale)
        painter.fillRect(QRectF(0,0,template.width,template.height),QColor(template.background))
        for el in template.elements:
            r=QRectF(el.x,el.y,el.width,el.height)
            painter.save(); painter.translate(r.center()); painter.rotate(el.rotation); painter.translate(-r.center())
            if el.kind in ("text","symbol"):
                f=QFont(el.font_family); f.setPixelSize(max(1,round(el.font_size*25.4/72))); f.setBold(el.bold); f.setItalic(el.italic); f.setUnderline(el.underline); painter.setFont(f); painter.setPen(QColor(el.color)); flags=Qt.AlignmentFlag.AlignCenter if el.kind=="symbol" else self.canvas._text_flags(el); painter.drawText(r,flags,self._resolved(el.value,row))
            elif el.kind in ("line","shape"):
                LabelCanvas._draw_vector_element(painter,el,r,1)
            elif el.kind=="image":
                image=QImage.fromData(base64.b64decode(el.asset_data)) if el.asset_data else QImage()
                if not image.isNull():painter.drawImage(r,image)
            elif el.kind=="svg":
                renderer=QSvgRenderer(QByteArray(base64.b64decode(el.asset_data)))
                if renderer.isValid():renderer.render(painter,r)
            else:
                copy=Element(**asdict(el)); copy.value=self._resolved(el.value,row); image=self.canvas.code_image(copy)
                if image:
                    if el.kind=="barcode": self.canvas._draw_barcode(painter,copy,r,image,1,preview=False)
                    else: painter.drawImage(r,image)
            painter.restore()
        painter.restore()

    def _template_from_file(self,path):
        data=json.loads(Path(path).read_text(encoding="utf-8"))
        return LabelTemplate(name=data.get("name","Шаблон"),width=float(data.get("width",58)),height=float(data.get("height",40)),background=data.get("background","#ffffff"),background_image=data.get("background_image",""),background_image_opacity=float(data.get("background_image_opacity",.35)),background_image_visible=bool(data.get("background_image_visible",True)),background_image_fit=data.get("background_image_fit","stretch"),grid=float(data.get("grid",1)),guides=data.get("guides",[]),elements=[Element(**e) for e in data.get("elements",[])])

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
                try:
                    return self._template_from_file(block.path)
                except Exception:
                    return block.template
        return self.template

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

    def print_labels(self):
        start=max(0,self.from_spin.value()-1)
        selected=self.rows[start:start+self.count_spin.value()] if self.rows else [{} for _ in range(self.count_spin.value())]
        if not selected:
            QMessageBox.information(self,"Нет строк","Выбранный диапазон пуст."); return
        ordered=[]
        counters={}
        for index,row in enumerate(selected):
            identity=self.template_identity_for_print_index(index)
            template=self.template_for_print_index(index)
            occurrence=counters.get(identity,0); counters[identity]=occurrence+1
            numbered=dict(row); number=self.seq_start.value()+occurrence*int(self.seq_direction.currentData()); digits=self.seq_width.value()
            numbered["_SEQ"]=str(number).zfill(digits) if digits else str(number)
            ordered.append((template,numbered))
        if any(abs(t.width-self.template.width)>0.001 or abs(t.height-self.template.height)>0.001 for t,_ in ordered):
            QMessageBox.warning(self,"Размеры этикеток не совпадают","Все шаблоны в одном задании должны иметь одинаковые ширину и высоту."); return
        columns=self.label_columns; gap=self.column_gap
        width=self.template.width*columns+gap*(columns-1)
        printer=QPrinter(QPrinter.PrinterMode.HighResolution)
        printer.setDocName(f"{APP} — {len(ordered)} этикеток")
        printer.setPageSize(QPageSize(QSizeF(width,self.template.height),QPageSize.Unit.Millimeter,"Label layout"))
        printer.setPageMargins(QMarginsF(0,0,0,0),QPageLayout.Unit.Millimeter); printer.setFullPage(True)
        dialog=QPrintDialog(printer,self); dialog.setWindowTitle("Выбрать принтер и параметры")
        if dialog.exec()!=QPrintDialog.DialogCode.Accepted:return
        painter=QPainter()
        if not painter.begin(printer):
            QMessageBox.critical(self,"Ошибка печати","Не удалось открыть драйвер принтера."); return
        try:
            for i,(template,row) in enumerate(ordered):
                if i and i%columns==0 and not printer.newPage():raise RuntimeError("Драйвер не смог добавить следующую строку этикеток.")
                page=QRectF(painter.viewport()); cell_w=page.width()*self.template.width/width; gap_px=page.width()*gap/width
                col=i%columns; cell=QRectF(col*(cell_w+gap_px),page.top(),cell_w,page.height())
                self._paint_label(painter,row,cell,template)
        except Exception as exc:QMessageBox.critical(self,"Ошибка задания печати",str(exc))
        else:self.status.setText(f"В очередь отправлено этикеток: {len(ordered)}")
        finally:painter.end()

    def configure_composition(self):
        dialog=QDialog(self); dialog.setWindowTitle("Шаблоны тиража"); dialog.resize(700,500); dialog.setMinimumSize(630,440)
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
        dialog.setModal(False);dialog.show()

    def configure_column_layout(self):
        dialog=QDialog(self);dialog.setWindowTitle("Колонки ленты");dialog.resize(760,520)
        dialog.setStyleSheet("QDialog{background:#f3f5f8;color:#20242b} QLabel{color:#20242b} QSpinBox,QDoubleSpinBox{background:white;color:#20242b;padding:5px} QPushButton{background:white;color:#20242b;border:1px solid #cbd2dc;border-radius:4px;padding:6px}")
        root=QVBoxLayout(dialog);intro=QLabel("Предпросмотр показывает, как этикетки расположатся по ширине носителя. Проверьте допустимую ширину в настройках принтера.");intro.setWordWrap(True);root.addWidget(intro)
        columns=QSpinBox();columns.setRange(1,20);columns.setValue(self.label_columns);gap=QDoubleSpinBox();gap.setRange(0,100);gap.setDecimals(2);gap.setSuffix(" мм");gap.setValue(self.column_gap)
        form=QFormLayout();form.addRow("Колонок на ленте",columns);form.addRow("Зазор между этикетками",gap);root.addLayout(form)
        owner=self
        class RibbonPreview(QWidget):
            def __init__(self):super().__init__();self.setMinimumHeight(300)
            def paintEvent(self,event):
                p=QPainter(self);p.fillRect(self.rect(),QColor("#e7ebf1"));p.setRenderHint(QPainter.RenderHint.Antialiasing)
                count=columns.value(); gap_mm=gap.value(); page_width=owner.template.width*count+gap_mm*(count-1)
                scale=min((self.width()-48)/page_width,(self.height()-48)/(owner.template.height*2+8))
                w=page_width*scale; h=owner.template.height*scale; x=(self.width()-w)/2; y=(self.height()-2*h-8*scale)/2
                for row_index in range(count*2):
                    row=row_index//count; col=row_index%count; xx=x+(col*(owner.template.width+gap_mm))*scale; yy=y+row*(owner.template.height+8)*scale
                    p.fillRect(QRectF(xx,yy,owner.template.width*scale,h),Qt.GlobalColor.white);p.setPen(QPen(QColor("#7790ae"),1));p.drawRect(QRectF(xx,yy,owner.template.width*scale,h))
                    template=owner.template_for_print_index(row_index);owner._paint_label(p,owner.canvas.preview_row,QRectF(xx,yy,owner.template.width*scale,h),template)
                p.setPen(QColor("#4b596b"));p.drawText(QRectF(8,8,self.width()-16,22),Qt.AlignmentFlag.AlignLeft,f"Предпросмотр · {count} колонок · ширина ленты {page_width:.2f} мм")
        preview=RibbonPreview();root.addWidget(preview,1);columns.valueChanged.connect(preview.update);gap.valueChanged.connect(preview.update)
        buttons=QDialogButtonBox(QDialogButtonBox.StandardButton.Ok|QDialogButtonBox.StandardButton.Cancel);buttons.accepted.connect(dialog.accept);buttons.rejected.connect(dialog.reject);root.addWidget(buttons)
        if dialog.exec()==QDialog.DialogCode.Accepted:
            self.label_columns=columns.value();self.column_gap=gap.value();self.settings.setValue("label_columns",self.label_columns);self.settings.setValue("column_gap",self.column_gap)
            self.refresh_print_preview();self.status.setText(f"Печатная область: {self.label_columns} колонок, зазор {self.column_gap:.2f} мм")

    def _write_template(self,path):
        data=asdict(self.template)
        target=Path(path)
        if target.suffix.lower()!=".json": target=target.with_suffix(".json")
        try:
            target.write_text(json.dumps(data,ensure_ascii=False,indent=2),encoding="utf-8")
            self.template_path=target; self.setWindowTitle(f"{APP} — {target.stem}"); self.status.setText(f"Шаблон сохранён: {target.name}")
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
            data=json.loads(Path(path).read_text(encoding="utf-8")); self.template_path=Path(path); self.setWindowTitle(f"{APP} — {self.template_path.stem}"); self.template=LabelTemplate(name=data.get("name","Шаблон"),width=float(data.get("width",58)),height=float(data.get("height",40)),background=data.get("background","#ffffff"),background_image=data.get("background_image",""),background_image_opacity=float(data.get("background_image_opacity",.35)),background_image_visible=bool(data.get("background_image_visible",True)),background_image_fit=data.get("background_image_fit","stretch"),grid=float(data.get("grid",1)),guides=data.get("guides",[]),elements=[Element(**e) for e in data.get("elements",[])])
            self.canvas.template=self.template; self.canvas.reset_view(); self.label_w.setValue(self.template.width); self.label_h.setValue(self.template.height); self.grid_size.setValue(self.template.grid); self.canvas.selected_index=0; self.refresh_object_list(); self.select_element(0); self.update_preview(); self.status.setText(f"Открыт шаблон: {Path(path).name}")
        except Exception as e: QMessageBox.critical(self,"Ошибка открытия шаблона",str(e))

    def new_template(self):
        self.template_path=None; self.setWindowTitle(APP); self.template=LabelTemplate(elements=[Element()]); self.canvas.template=self.template; self.canvas.reset_view(); self.canvas.selected_index=0; self.canvas.preview_row={}; self.label_w.setValue(58); self.label_h.setValue(40); self.grid_size.setValue(1); self.refresh_object_list(); self.select_element(0); self.update_preview()


if __name__ == "__main__":
    app=QApplication(sys.argv); app.setApplicationName(APP)
    icon_root=Path(getattr(sys,"_MEIPASS",Path(__file__).resolve().parent)); app_icon=icon_root/"assets"/"labelstudio.ico"
    if app_icon.exists():app.setWindowIcon(QIcon(str(app_icon)))
    win=MainWindow(); win.show(); sys.exit(app.exec())
