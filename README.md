# MetaStudio

An ExifTool-style metadata manager with a desktop GUI, written in **pure Python** (Tkinter + SQLite). It needs no ExifTool, no browser, and no pip packages. Pillow is optional and only gives nicer image thumbnails.

> Inspired by Phil Harvey's ExifTool. This is an independent project and is not affiliated with it.

## Features

- **Read** metadata from JPEG, PNG, GIF, BMP, WEBP, TIFF (EXIF / GPS / XMP / JFIF), MP3 (ID3v1/v2 and audio info), WAV, MP4 / M4A / MOV, PDF (Info dictionary), and DOCX / XLSX / PPTX (core and app properties)
- **Write** metadata:
  - JPEG: EXIF and GPS tags, JPEG comment
  - PNG: text chunks and EXIF (eXIf chunk)
  - MP3: ID3 tags (Title, Artist, Album, Year, Genre, Comment, ...)
  - DOCX / XLSX / PPTX: core properties (Title, Creator, Keywords, ...)
- **Strip** metadata from the four writable formats (useful for privacy)
- **Batch Edit** tab to change many files at once
- **Audit Log** of every edit, with one-click revert
- **Snapshots** of a file's metadata, with a diff between scans
- SQLite storage for recent files, snapshots, audit log, and settings (optional backup of files before editing)

## Requirements

- Python 3.8 or newer
- Tkinter (included with the standard Python installers on Windows and macOS; on some Linux systems install it with `sudo apt install python3-tk`)
- Optional: `pip install pillow` for image thumbnails

## How to Run

```bash
git clone https://github.com/tabassumbanugitthub/MetaStudio.git
cd MetaStudio
python metastudio.py
```

The app database is stored in your home folder as `.metastudio.db`, so nothing is created inside the project folder.

## Screenshots

*Add screenshots of the Metadata tab, Batch Edit, and Audit Log here.*

## Project Structure

```
MetaStudio/
├── metastudio.py   # Parsers, writers, SQLite layer, and GUI
├── README.md
├── LICENSE
└── .gitignore
```

## Disclaimer

Writing and stripping modify files. Turn on the backup option in Settings, or work on copies, before editing files you care about.

## Future Improvements

- Split parsers, writers, and GUI into separate modules
- Write support for more formats (PDF, MP4, WEBP)
- Unit tests with sample files

## License

This project is licensed under the MIT License. See the [LICENSE](LICENSE) file for details.
