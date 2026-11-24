#define AppName "Label Studio"
#define AppVersion "0.1.0"
[Setup]
AppId={{8521FA9F-6011-493A-9EA3-C762ABFD419B}
AppName={#AppName}
AppVersion={#AppVersion}
DefaultDirName={autopf}\Label Studio
DefaultGroupName={#AppName}
OutputDir=dist
OutputBaseFilename=LabelStudio-Setup
Compression=lzma2
SolidCompression=yes
ArchitecturesInstallIn64BitMode=x64
[Files]
Source: "dist\LabelStudio\*"; DestDir: "{app}"; Flags: recursesubdirs ignoreversion
[Icons]
Name: "{group}\Label Studio"; Filename: "{app}\LabelStudio.exe"
Name: "{autodesktop}\Label Studio"; Filename: "{app}\LabelStudio.exe"
[Run]
Filename: "{app}\LabelStudio.exe"; Description: "Запустить Label Studio"; Flags: postinstall nowait skipifsilent
