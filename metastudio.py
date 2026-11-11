#!/usr/bin/env python3
"""
MetaStudio  -  an ExifTool-style metadata manager.  100% pure Python.

    * NO ExifTool, NO pip packages, NO browser.  Only Python 3.8+ (Tkinter + SQLite are built in).
    * Optional:  pip install pillow   ->  nicer image thumbnails.

READ  : JPEG, PNG, GIF, BMP, WEBP, TIFF (EXIF/GPS/XMP/JFIF), MP3 (ID3v1/v2 + audio info),
        WAV, MP4/M4A/MOV, PDF (Info dictionary), DOCX/XLSX/PPTX (core + app properties)
WRITE : JPEG   -> EXIF / GPS tags, JPEG comment
        PNG    -> text chunks (PNG:Author ...) and EXIF (eXIf chunk)
        MP3    -> ID3 tags (Title, Artist, Album, Year, Genre, Comment ...)
        DOCX / XLSX / PPTX -> Core properties (Title, Creator, Keywords ...)
STRIP : the four writable formats above
SQLite: recent files, scan snapshots (+diff), full audit log with one-click revert, settings

Run:  python metastudio.py
"""

import csv
import datetime as dt
import io
import json
import mimetypes
import os
import queue
import re
import shutil
import sqlite3
import struct
import sys
import threading
import tkinter as tk
import zipfile
import zlib
from fractions import Fraction
from tkinter import filedialog, messagebox, ttk
from xml.sax.saxutils import escape as xml_escape

try:
    from PIL import Image, ImageTk  # optional
    HAS_PIL = True
except Exception:  # pragma: no cover
    HAS_PIL = False

APP_NAME = "MetaStudio"
DB_FILE = os.path.join(os.path.expanduser("~"), ".metastudio.db")

# =====================================================================
#                     PURE-PYTHON METADATA ENGINE
# =====================================================================
TSIZE = {1: 1, 2: 1, 3: 2, 4: 4, 5: 8, 6: 1, 7: 1, 8: 2, 9: 4, 10: 8, 11: 4, 12: 8}

# kind: a=ascii s=short l=long r=rational R=signed rational b=byte
#       c=UserComment x=Windows XP (utf-16) u=undefined (read-only)
IFD0_TAGS = {
    0x0100: ("ImageWidth", "l"), 0x0101: ("ImageHeight", "l"), 0x0102: ("BitsPerSample", "s"),
    0x0103: ("Compression", "s"), 0x0106: ("PhotometricInterpretation", "s"),
    0x010E: ("ImageDescription", "a"), 0x010F: ("Make", "a"), 0x0110: ("Model", "a"),
    0x0112: ("Orientation", "s"), 0x0115: ("SamplesPerPixel", "s"),
    0x011A: ("XResolution", "r"), 0x011B: ("YResolution", "r"), 0x0128: ("ResolutionUnit", "s"),
    0x0131: ("Software", "a"), 0x0132: ("ModifyDate", "a"), 0x013B: ("Artist", "a"),
    0x013E: ("WhitePoint", "r"), 0x0213: ("YCbCrPositioning", "s"), 0x8298: ("Copyright", "a"),
    0x9C9B: ("XPTitle", "x"), 0x9C9C: ("XPComment", "x"), 0x9C9D: ("XPAuthor", "x"),
    0x9C9E: ("XPKeywords", "x"), 0x9C9F: ("XPSubject", "x"),
}
EXIF_TAGS = {
    0x829A: ("ExposureTime", "r"), 0x829D: ("FNumber", "r"), 0x8822: ("ExposureProgram", "s"),
    0x8827: ("ISO", "s"), 0x9000: ("ExifVersion", "u"), 0x9003: ("DateTimeOriginal", "a"),
    0x9004: ("CreateDate", "a"), 0x9010: ("OffsetTime", "a"), 0x9011: ("OffsetTimeOriginal", "a"),
    0x9101: ("ComponentsConfiguration", "u"), 0x9201: ("ShutterSpeedValue", "R"),
    0x9202: ("ApertureValue", "r"), 0x9204: ("ExposureCompensation", "R"),
    0x9207: ("MeteringMode", "s"), 0x9209: ("Flash", "s"), 0x920A: ("FocalLength", "r"),
    0x927C: ("MakerNote", "u"), 0x9286: ("UserComment", "c"), 0x9290: ("SubSecTime", "a"),
    0x9291: ("SubSecTimeOriginal", "a"), 0xA000: ("FlashpixVersion", "u"),
    0xA001: ("ColorSpace", "s"), 0xA002: ("ExifImageWidth", "l"), 0xA003: ("ExifImageHeight", "l"),
    0xA401: ("CustomRendered", "s"), 0xA402: ("ExposureMode", "s"), 0xA403: ("WhiteBalance", "s"),
    0xA404: ("DigitalZoomRatio", "r"), 0xA405: ("FocalLengthIn35mmFormat", "s"),
    0xA406: ("SceneCaptureType", "s"), 0xA420: ("ImageUniqueID", "a"), 0xA430: ("OwnerName", "a"),
    0xA431: ("SerialNumber", "a"), 0xA432: ("LensInfo", "r"), 0xA433: ("LensMake", "a"),
    0xA434: ("LensModel", "a"),
}
GPS_TAGS = {
    0x0000: ("GPSVersionID", "u"), 0x0001: ("GPSLatitudeRef", "a"), 0x0002: ("GPSLatitude", "r"),
    0x0003: ("GPSLongitudeRef", "a"), 0x0004: ("GPSLongitude", "r"),
    0x0005: ("GPSAltitudeRef", "b"), 0x0006: ("GPSAltitude", "r"), 0x0007: ("GPSTimeStamp", "r"),
    0x000C: ("GPSSpeedRef", "a"), 0x000D: ("GPSSpeed", "r"), 0x0010: ("GPSImgDirectionRef", "a"),
    0x0011: ("GPSImgDirection", "r"), 0x0012: ("GPSMapDatum", "a"), 0x001D: ("GPSDateStamp", "a"),
}
TABLES = {"IFD0": IFD0_TAGS, "Exif": EXIF_TAGS, "GPS": GPS_TAGS}
ALLTAGS = {}
for _ifd, _tab in TABLES.items():
    for _id, (_n, _k) in _tab.items():
        ALLTAGS[_n] = (_ifd, _id, _k)
WRITABLE_KINDS = set("aslrRbcx")
POINTERS = {0x8769, 0x8825, 0xA005}
EXIF_GROUPS = {"EXIF", "IFD0", "EXIFIFD", "GPS"}

ENUMS = {
    "Orientation": {1: "Horizontal (normal)", 2: "Mirror horizontal", 3: "Rotate 180",
                    4: "Mirror vertical", 5: "Mirror horizontal and rotate 270 CW",
                    6: "Rotate 90 CW", 7: "Mirror horizontal and rotate 90 CW",
                    8: "Rotate 270 CW"},
    "ResolutionUnit": {1: "None", 2: "inches", 3: "cm"},
    "ColorSpace": {1: "sRGB", 65535: "Uncalibrated"},
    "ExposureProgram": {0: "Not Defined", 1: "Manual", 2: "Program AE", 3: "Aperture-priority AE",
                        4: "Shutter speed priority AE", 5: "Creative (Slow speed)",
                        6: "Action (High speed)", 7: "Portrait", 8: "Landscape"},
    "MeteringMode": {0: "Unknown", 1: "Average", 2: "Center-weighted average", 3: "Spot",
                     4: "Multi-spot", 5: "Multi-segment", 6: "Partial", 255: "Other"},
    "WhiteBalance": {0: "Auto", 1: "Manual"},
    "Flash": {0: "No Flash", 1: "Fired", 5: "Fired, Return not detected", 7: "Fired, Return detected",
              16: "Off, Did not fire", 24: "Auto, Did not fire", 25: "Auto, Fired"},
    "ExposureMode": {0: "Auto", 1: "Manual", 2: "Auto bracket"},
    "SceneCaptureType": {0: "Standard", 1: "Landscape", 2: "Portrait", 3: "Night"},
    "GPSAltitudeRef": {0: "Above Sea Level", 1: "Below Sea Level"},
    "YCbCrPositioning": {1: "Centered", 2: "Co-sited"},
    "CustomRendered": {0: "Normal", 1: "Custom"},
}
ENUM_REV = {n: {v.lower(): k for k, v in m.items()} for n, m in ENUMS.items()}
COMP = {0: "-", 1: "Y", 2: "Cb", 3: "Cr", 4: "R", 5: "G", 6: "B"}


def fmt_num(v):
    if isinstance(v, float):
        if v == int(v) and abs(v) < 1e12:
            return str(int(v))
        return f"{v:.6g}"
    return str(v)


def fmt_dur(sec):
    if sec < 60:
        return f"{sec:.2f} s"
    h, r = divmod(int(sec), 3600)
    m, s = divmod(r, 60)
    return f"{h}:{m:02d}:{s:02d}" if h else f"{m}:{s:02d}"


def human_size(n):
    n = float(n)
    for u in ("B", "KB", "MB", "GB", "TB"):
        if n < 1024:
            return f"{n:.0f} {u}" if u == "B" else f"{n:.1f} {u}"
        n /= 1024
    return f"{n:.1f} PB"


def now():
    return dt.datetime.now().strftime("%Y-%m-%d %H:%M:%S")


def ts_str(t):
    return dt.datetime.fromtimestamp(t).strftime("%Y:%m:%d %H:%M:%S")


# ----------------------------------------------------------- TIFF / EXIF --
def parse_tiff(buf, base=0):
    """Parse TIFF structure starting at buf[base:]. Returns dict or None."""
    try:
        sig = buf[base:base + 2]
        e = "<" if sig == b"II" else ">" if sig == b"MM" else None
        if not e or struct.unpack(e + "H", buf[base + 2:base + 4])[0] != 42:
            return None

        def read_ifd(off):
            ents = {}
            n = struct.unpack(e + "H", buf[base + off:base + off + 2])[0]
            if n > 2000:
                return ents, 0
            for i in range(n):
                p = base + off + 2 + 12 * i
                tag, typ, cnt = struct.unpack(e + "HHI", buf[p:p + 8])
                sz = TSIZE.get(typ, 1) * cnt
                if sz <= 4:
                    data = buf[p + 8:p + 8 + sz]
                else:
                    vo = struct.unpack(e + "I", buf[p + 8:p + 12])[0]
                    if sz > len(buf) or base + vo + sz > len(buf):
                        continue
                    data = buf[base + vo:base + vo + sz]
                ents[tag] = (typ, cnt, bytes(data))
            nxt = struct.unpack(e + "I", buf[base + off + 2 + 12 * n:base + off + 6 + 12 * n])[0]
            return ents, nxt

        t = {"endian": e}
        first = struct.unpack(e + "I", buf[base + 4:base + 8])[0]
        t["IFD0"], nxt = read_ifd(first)

        def ptr(ents, tag):
            if tag in ents:
                return struct.unpack(e + "I", ents[tag][2][:4])[0]
            return None
        p = ptr(t["IFD0"], 0x8769)
        if p:
            t["Exif"], _ = read_ifd(p)
        p = ptr(t["IFD0"], 0x8825)
        if p:
            t["GPS"], _ = read_ifd(p)
        return t
    except Exception:
        return None


def _ser_ifd(entries, offset, e):
    n = len(entries)
    data_off = offset + 2 + 12 * n + 4
    out = struct.pack(e + "H", n)
    extra = b""
    for tag in sorted(entries):
        typ, cnt, d = entries[tag]
        if len(d) <= 4:
            val = d.ljust(4, b"\0")
        else:
            if len(extra) % 2:
                extra += b"\0"
            val = struct.pack(e + "I", data_off + len(extra))
            extra += d
        out += struct.pack(e + "HHI", tag, typ, cnt) + val
    out += struct.pack(e + "I", 0)
    out += extra
    if len(out) % 2:
        out += b"\0"
    return out


def build_tiff(t):
    e = t["endian"]
    ifd0 = {k: v for k, v in t.get("IFD0", {}).items() if k not in POINTERS}
    exif = {k: v for k, v in t.get("Exif", {}).items() if k not in POINTERS}
    gps = dict(t.get("GPS", {}))
    zero = (4, 1, struct.pack(e + "I", 0))
    if exif:
        ifd0[0x8769] = zero
    if gps:
        ifd0[0x8825] = zero
    len0 = len(_ser_ifd(ifd0, 8, e))
    exif_off = 8 + len0
    lenx = len(_ser_ifd(exif, exif_off, e)) if exif else 0
    gps_off = exif_off + lenx
    if exif:
        ifd0[0x8769] = (4, 1, struct.pack(e + "I", exif_off))
    if gps:
        ifd0[0x8825] = (4, 1, struct.pack(e + "I", gps_off))
    head = (b"II" if e == "<" else b"MM") + struct.pack(e + "HI", 42, 8)
    out = head + _ser_ifd(ifd0, 8, e)
    if exif:
        out += _ser_ifd(exif, exif_off, e)
    if gps:
        out += _ser_ifd(gps, gps_off, e)
    return out


def _rats(e, typ, d):
    n = len(d) // 8
    fmt = "I" if typ == 5 else "i"
    p = struct.unpack(e + f"{n * 2}{fmt}", d[:n * 8])
    return [(p[i] / p[i + 1]) if p[i + 1] else 0.0 for i in range(0, n * 2, 2)]


def decode_usercomment(d):
    if len(d) < 8:
        return ""
    code, body = d[:8], d[8:]
    try:
        if code.startswith(b"UNICODE"):
            try:
                return body.decode("utf-16").rstrip("\x00")
            except Exception:
                return body.decode("utf-16-le", "replace").rstrip("\x00")
        return body.decode("utf-8", "replace").rstrip("\x00 ")
    except Exception:
        return ""


def decode_value(e, typ, cnt, d, name, raw):
    try:
        if name == "MakerNote":
            return f"(Binary data {len(d)} bytes)"
        if name == "UserComment":
            return decode_usercomment(d)
        if name in ("ExifVersion", "FlashpixVersion"):
            return d.decode("ascii", "replace")
        if name.startswith("XP") and typ == 1:
            return d.decode("utf-16-le", "replace").rstrip("\x00")
        if typ == 2:
            return d.split(b"\0")[0].decode("utf-8", "replace").strip()
        if typ in (3, 8):
            vals = list(struct.unpack(e + f"{len(d) // 2}{'H' if typ == 3 else 'h'}", d[:len(d) // 2 * 2]))
        elif typ in (4, 9):
            vals = list(struct.unpack(e + f"{len(d) // 4}{'I' if typ == 4 else 'i'}", d[:len(d) // 4 * 4]))
        elif typ in (5, 10):
            vals = _rats(e, typ, d)
        elif typ in (11, 12):
            f = "f" if typ == 11 else "d"
            sz = 4 if typ == 11 else 8
            vals = list(struct.unpack(e + f"{len(d) // sz}{f}", d[:len(d) // sz * sz]))
        elif typ in (1, 6, 7):
            if name == "GPSVersionID":
                return ".".join(map(str, d))
            if name == "ComponentsConfiguration":
                return ", ".join(COMP.get(b, str(b)) for b in d)
            if typ == 7:
                if d and all(32 <= b < 127 for b in d):
                    return d.decode("ascii")
                return f"(Binary data {len(d)} bytes)"
            vals = list(d)
        else:
            return f"(type {typ}, {len(d)} bytes)"
        if len(vals) > 32:
            return f"({len(vals)} values)"
        if not raw and len(vals) == 1:
            v = vals[0]
            if name in ENUMS and int(v) in ENUMS[name]:
                return ENUMS[name][int(v)]
            if name == "ExposureTime" and v:
                return f"1/{round(1 / v)}" if v < 1 else fmt_num(v)
            if name in ("FNumber", "ApertureValue"):
                return f"{v:.1f}"
            if name in ("FocalLength",):
                return f"{v:.1f} mm"
        return " ".join(fmt_num(v) for v in vals)
    except Exception:
        return f"(unreadable, {len(d)} bytes)"


def tiff_rows(t, raw):
    rows = []
    e = t["endian"]
    for key, grp in (("IFD0", "EXIF"), ("Exif", "EXIF"), ("GPS", "GPS")):
        for tid, (typ, cnt, data) in sorted(t.get(key, {}).items()):
            if tid in POINTERS:
                continue
            name = TABLES[key].get(tid, (f"Tag0x{tid:04X}", None))[0]
            rows.append((grp, name, decode_value(e, typ, cnt, data, name, raw)))
    g = t.get("GPS", {})
    try:
        def dms(tag, ref):
            if tag in g and ref in g:
                v = _rats(e, g[tag][0], g[tag][2])
                deg = v[0] + v[1] / 60 + v[2] / 3600
                r = g[ref][2].split(b"\0")[0].decode("ascii", "replace").upper()
                return -deg if r in ("S", "W") else deg
        lat, lon = dms(0x0002, 0x0001), dms(0x0004, 0x0003)
        if lat is not None:
            rows.append(("Composite", "GPSLatitude", f"{lat:.6f}"))
        if lon is not None:
            rows.append(("Composite", "GPSLongitude", f"{lon:.6f}"))
        if lat is not None and lon is not None:
            rows.append(("Composite", "GPSPosition", f"{lat:.6f}, {lon:.6f}"))
    except Exception:
        pass
    return rows


def enc_value(kind, name, text, e):
    """Encode text -> (type, count, bytes)"""
    if kind == "a":
        d = text.encode("utf-8") + b"\0"
        return 2, len(d), d
    if kind == "x":
        d = text.encode("utf-16-le") + b"\0\0"
        return 1, len(d), d
    if kind == "c":
        try:
            d = b"ASCII\0\0\0" + text.encode("ascii")
        except UnicodeEncodeError:
            d = b"UNICODE\0" + text.encode("utf-16-le" if e == "<" else "utf-16-be")
        return 7, len(d), d
    if kind in ("s", "l", "b"):
        t = text.strip()
        if name in ENUM_REV and t.lower() in ENUM_REV[name]:
            nums = [ENUM_REV[name][t.lower()]]
        else:
            toks = re.findall(r"-?\d+(?:\.\d+)?", t)
            if not toks:
                raise ValueError(f"{name}: a number is required (got '{text}')")
            nums = [int(float(x)) for x in toks]
        if kind == "b":
            return 1, len(nums), bytes(nums)
        f = "H" if kind == "s" else "I"
        return (3 if kind == "s" else 4), len(nums), struct.pack(e + f"{len(nums)}{f}", *nums)
    if kind in ("r", "R"):
        toks = re.findall(r"-?\d+(?:/\d+)?(?:\.\d+)?", text)
        if not toks:
            raise ValueError(f"{name}: a number is required (got '{text}')")
        d = b""
        for tk_ in toks:
            fr = Fraction(tk_).limit_denominator(1000000)
            d += struct.pack(e + ("II" if kind == "r" else "ii"), fr.numerator, fr.denominator)
        return (5 if kind == "r" else 10), len(toks), d
    raise ValueError(f"{name} is read-only")


def split_tag(full):
    if ":" in full:
        g, n = full.split(":", 1)
        return g, n
    return None, full


def apply_exif(t, items):
    """items: [(group, name, value|None)] -> modifies tiff dict t in place."""
    e = t["endian"]
    errors = []
    for g, name, val in items:
        if g and g.upper() not in EXIF_GROUPS:
            errors.append(f"{g}:{name} is not an EXIF tag")
            continue
        info = ALLTAGS.get(name)
        if info is None:
            if val is None and name.startswith("Tag0x"):
                try:
                    tid = int(name[5:], 16)
                    for k in ("IFD0", "Exif", "GPS"):
                        t.get(k, {}).pop(tid, None)
                except ValueError:
                    errors.append(f"Unknown tag {name}")
            else:
                errors.append(f"Unknown or unsupported EXIF tag '{name}'")
            continue
        ifd, tid, kind = info
        if g and ((g.upper() == "GPS") != (ifd == "GPS")):
            errors.append(f"'{name}' does not belong to group {g}")
            continue
        ents = t.setdefault(ifd, {})
        if val is None:
            ents.pop(tid, None)
            if name == "GPSLatitude":
                ents.pop(0x0001, None)
            if name == "GPSLongitude":
                ents.pop(0x0003, None)
            continue
        if kind not in WRITABLE_KINDS:
            errors.append(f"'{name}' is read-only")
            continue
        try:
            if name in ("GPSLatitude", "GPSLongitude"):
                toks = re.findall(r"-?\d+(?:\.\d+)?", val)
                if len(toks) == 1:  # decimal degrees -> DMS + ref
                    dec = float(toks[0])
                    a = abs(dec)
                    d_ = int(a)
                    m_ = int((a - d_) * 60)
                    s_ = round((a - d_ - m_ / 60) * 3600, 4)
                    ref = ("N" if dec >= 0 else "S") if name == "GPSLatitude" else ("E" if dec >= 0 else "W")
                    fr = Fraction(s_).limit_denominator(10000)
                    ents[tid] = (5, 3, struct.pack(e + "IIIIII", d_, 1, m_, 1, fr.numerator, fr.denominator))
                    rid = 0x0001 if name == "GPSLatitude" else 0x0003
                    ents[rid] = enc_value("a", "ref", ref, e)
                    continue
            ents[tid] = enc_value(kind, name, val, e)
        except ValueError as ex:
            errors.append(str(ex))
    if errors:
        raise ValueError("\n".join(errors))


# ----------------------------------------------------------------- JPEG --
def jpeg_segments(data):
    i, segs = 2, []
    while i + 4 <= len(data):
        if data[i] != 0xFF:
            break
        m = data[i + 1]
        if m == 0xFF:
            i += 1
            continue
        if m == 0x01 or 0xD0 <= m <= 0xD8:
            i += 2
            continue
        if m == 0xDA:
            return segs, i
        L = struct.unpack(">H", data[i + 2:i + 4])[0]
        segs.append((m, i, i + 2 + L))
        i += 2 + L
    return segs, len(data)


XMP_FIELDS = ["dc:title", "dc:creator", "dc:description", "dc:subject", "dc:rights",
              "xmp:CreatorTool", "xmp:CreateDate", "xmp:ModifyDate", "xmp:Rating", "xmp:Label",
              "photoshop:City", "photoshop:Country", "photoshop:Credit", "photoshop:Headline"]


def xmp_rows(xml):
    rows = [("XMP", "Packet", f"({len(xml)} bytes)")]
    for f in XMP_FIELDS:
        m = re.search(r"<%s[^>]*>(.*?)</%s>" % (f, f), xml, re.S)
        val = None
        if m:
            lis = re.findall(r"<rdf:li[^>]*>(.*?)</rdf:li>", m.group(1), re.S)
            val = ", ".join(x.strip() for x in lis) if lis else re.sub(r"<[^>]+>", "", m.group(1)).strip()
        else:
            m = re.search(r'%s="([^"]*)"' % f, xml)
            if m:
                val = m.group(1)
        if val:
            rows.append(("XMP", f.split(":")[1][0].upper() + f.split(":")[1][1:], val.replace("&amp;", "&")
                         .replace("&lt;", "<").replace("&gt;", ">")))
    return rows


# ------------------------------------------------------------------ PNG --
PNG_SIG = b"\x89PNG\r\n\x1a\n"
PNG_RO = {"ImageWidth", "ImageHeight", "BitDepth", "ColorType", "Compression", "Filter",
          "Interlace", "PixelsPerUnitX", "PixelsPerUnitY", "PixelUnits", "ModifyDate", "Gamma"}


def png_chunks(data):
    i = 8
    while i + 12 <= len(data):
        L, typ = struct.unpack(">I4s", data[i:i + 8])
        yield typ, data[i + 8:i + 8 + L], data[i:i + 12 + L]
        i += 12 + L


def png_chunk(typ, payload):
    return struct.pack(">I", len(payload)) + typ + payload + struct.pack(">I", zlib.crc32(typ + payload) & 0xFFFFFFFF)


def png_text(typ, p):
    try:
        if typ == b"tEXt":
            k, v = p.split(b"\0", 1)
            return k.decode("latin-1"), v.decode("latin-1")
        if typ == b"zTXt":
            k, rest = p.split(b"\0", 1)
            return k.decode("latin-1"), zlib.decompress(rest[1:]).decode("latin-1")
        if typ == b"iTXt":
            k, rest = p.split(b"\0", 1)
            comp, meth = rest[0], rest[1]
            rest = rest[2:]
            _, rest = rest.split(b"\0", 1)
            _, text = rest.split(b"\0", 1)
            if comp:
                text = zlib.decompress(text)
            return k.decode("latin-1"), text.decode("utf-8", "replace")
    except Exception:
        pass
    return None


# ------------------------------------------------------------------ ID3 --
ID3NAMES = {"TIT2": "Title", "TPE1": "Artist", "TALB": "Album", "TYER": "Year", "TDRC": "Year",
            "TRCK": "Track", "TCON": "Genre", "TPE2": "AlbumArtist", "TCOM": "Composer",
            "TPOS": "DiscNumber", "TCOP": "Copyright", "TENC": "EncodedBy", "TBPM": "BeatsPerMinute",
            "TPUB": "Publisher", "TSSE": "Encoder", "COMM": "Comment", "USLT": "Lyrics",
            "TLEN": "Length", "TKEY": "InitialKey", "TLAN": "Language", "TIT3": "Subtitle",
            "TOPE": "OriginalArtist"}
ID3_WRITE = {"Title": "TIT2", "Artist": "TPE1", "Album": "TALB", "Year": "TYER", "Track": "TRCK",
             "Genre": "TCON", "AlbumArtist": "TPE2", "Composer": "TCOM", "DiscNumber": "TPOS",
             "Copyright": "TCOP", "EncodedBy": "TENC", "BeatsPerMinute": "TBPM", "Publisher": "TPUB",
             "Encoder": "TSSE", "Comment": "COMM", "Lyrics": "USLT", "InitialKey": "TKEY",
             "Language": "TLAN", "Subtitle": "TIT3", "OriginalArtist": "TOPE"}
V22MAP = {"TT2": "TIT2", "TP1": "TPE1", "TAL": "TALB", "TYE": "TYER", "TRK": "TRCK", "TCO": "TCON",
          "COM": "COMM", "TP2": "TPE2", "TCM": "TCOM", "TEN": "TENC", "TPA": "TPOS", "TBP": "TBPM",
          "TPB": "TPUB", "TCR": "TCOP", "PIC": "APIC", "TXX": "TXXX", "TSS": "TSSE", "ULT": "USLT"}
ID3V1_GENRES = ["Blues", "Classic Rock", "Country", "Dance", "Disco", "Funk", "Grunge", "Hip-Hop", "Jazz",
                "Metal", "New Age", "Oldies", "Other", "Pop", "R&B", "Rap", "Reggae", "Rock", "Techno",
                "Industrial", "Alternative", "Ska", "Death Metal", "Pranks", "Soundtrack", "Euro-Techno",
                "Ambient", "Trip-Hop", "Vocal", "Jazz+Funk", "Fusion", "Trance", "Classical", "Instrumental",
                "Acid", "House", "Game", "Sound Clip", "Gospel", "Noise", "AlternRock", "Bass", "Soul",
                "Punk", "Space", "Meditative", "Instrumental Pop", "Instrumental Rock", "Ethnic", "Gothic",
                "Darkwave", "Techno-Industrial", "Electronic", "Pop-Folk", "Eurodance", "Dream",
                "Southern Rock", "Comedy", "Cult", "Gangsta", "Top 40", "Christian Rap", "Pop/Funk"]


def _syncsafe(b):
    return (b[0] << 21) | (b[1] << 14) | (b[2] << 7) | b[3]


def _to_syncsafe(n):
    return bytes([(n >> 21) & 127, (n >> 14) & 127, (n >> 7) & 127, n & 127])


def id3_parse(head_and_tag):
    """Return dict(ver, frames[(id,data)], total) or None."""
    b = head_and_tag
    if b[:3] != b"ID3" or len(b) < 10:
        return None
    major, flags = b[3], b[5]
    size = _syncsafe(b[6:10])
    total = 10 + size + (10 if (major == 4 and flags & 0x10) else 0)
    body = b[10:10 + size]
    if flags & 0x80 and major == 3:
        body = body.replace(b"\xff\x00", b"\xff")
    pos = 0
    if flags & 0x40 and len(body) >= 4:  # extended header
        es = _syncsafe(body[:4]) if major == 4 else struct.unpack(">I", body[:4])[0] + 4
        pos = es
    frames = []
    while True:
        if major == 2:
            if pos + 6 > len(body) or body[pos] == 0:
                break
            fid = body[pos:pos + 3].decode("latin-1")
            fs = int.from_bytes(body[pos + 3:pos + 6], "big")
            data = body[pos + 6:pos + 6 + fs]
            pos += 6 + fs
            fid = V22MAP.get(fid, fid)
        else:
            if pos + 10 > len(body) or body[pos] == 0:
                break
            fid = body[pos:pos + 4].decode("latin-1")
            fs = _syncsafe(body[pos + 4:pos + 8]) if major == 4 else struct.unpack(">I", body[pos + 4:pos + 8])[0]
            data = body[pos + 10:pos + 10 + fs]
            pos += 10 + fs
        if fid == "TDRC":  # v2.4 -> v2.3 Year
            fid = "TYER"
            enc = data[:1]
            txt = id3_text(data)[:4]
            data = enc_text(txt)
        frames.append((fid, data))
    return {"ver": major, "frames": frames, "total": total}


def _split_term(t, enc):
    if enc in (1, 2):
        i = 0
        while i + 1 < len(t):
            if t[i] == 0 and t[i + 1] == 0 and i % 2 == 0:
                return t[:i], t[i + 2:]
            i += 1
        return t, b""
    i = t.find(b"\0")
    return (t, b"") if i < 0 else (t[:i], t[i + 1:])


def _codec(enc):
    return {0: "latin-1", 1: "utf-16", 2: "utf-16-be", 3: "utf-8"}.get(enc, "latin-1")


def id3_text(data):
    if not data:
        return ""
    enc = data[0]
    s = data[1:].decode(_codec(enc), "replace")
    return s.replace("\x00", " / ").strip(" /\x00\ufeff")


def enc_text(text):
    try:
        return b"\x00" + text.encode("latin-1")
    except UnicodeEncodeError:
        return b"\x01" + b"\xff\xfe" + text.encode("utf-16-le")


def id3_frame_rows(frames):
    rows = []
    for fid, data in frames:
        try:
            if fid == "TXXX":
                enc = data[0]
                desc, val = _split_term(data[1:], enc)
                rows.append(("ID3", "TXXX:" + desc.decode(_codec(enc), "replace"),
                             val.decode(_codec(enc), "replace").strip("\x00\ufeff")))
            elif fid in ("COMM", "USLT"):
                enc = data[0]
                desc, val = _split_term(data[4:], enc)
                rows.append(("ID3", ID3NAMES[fid], val.decode(_codec(enc), "replace").strip("\x00\ufeff")))
            elif fid == "APIC":
                enc = data[0]
                mime, rest = _split_term(data[1:], 0)
                rows.append(("ID3", "Picture", f"({mime.decode('latin-1')}, {len(data)} bytes)"))
            elif fid[0] == "T":
                rows.append(("ID3", ID3NAMES.get(fid, fid), id3_text(data)))
            else:
                rows.append(("ID3", fid, f"(Binary data {len(data)} bytes)"))
        except Exception:
            rows.append(("ID3", fid, "(unreadable)"))
    return rows


def id3_build_frames(frames):
    out = b""
    for fid, data in frames:
        out += fid.encode("latin-1") + struct.pack(">I", len(data)) + b"\0\0" + data
    return out


MP3_BR = {(1, 1): [0, 32, 64, 96, 128, 160, 192, 224, 256, 288, 320, 352, 384, 416, 448, 0],
          (1, 2): [0, 32, 48, 56, 64, 80, 96, 112, 128, 160, 192, 224, 256, 320, 384, 0],
          (1, 3): [0, 32, 40, 48, 56, 64, 80, 96, 112, 128, 160, 192, 224, 256, 320, 0],
          (2, 1): [0, 32, 48, 56, 64, 80, 96, 112, 128, 144, 160, 176, 192, 224, 256, 0],
          (2, 2): [0, 8, 16, 24, 32, 40, 48, 56, 64, 80, 96, 112, 128, 144, 160, 0],
          (2, 3): [0, 8, 16, 24, 32, 40, 48, 56, 64, 80, 96, 112, 128, 144, 160, 0]}
MP3_SR = {1: [44100, 48000, 32000], 2: [22050, 24000, 16000], 3: [11025, 12000, 8000]}


def mp3_info(chunk, audio_bytes):
    rows = []
    for i in range(len(chunk) - 4):
        if chunk[i] == 0xFF and (chunk[i + 1] & 0xE0) == 0xE0:
            h = struct.unpack(">I", chunk[i:i + 4])[0]
            vb, lb = (h >> 19) & 3, (h >> 17) & 3
            bri, sri = (h >> 12) & 15, (h >> 10) & 3
            if vb == 1 or lb == 0 or bri in (0, 15) or sri == 3:
                continue
            ver = {3: 1, 2: 2, 0: 3}[vb]
            layer = {3: 1, 2: 2, 1: 3}[lb]
            br = MP3_BR[(1 if ver == 1 else 2, layer)][bri]
            sr = MP3_SR[ver][sri]
            mode = "Mono" if ((h >> 6) & 3) == 3 else "Stereo"
            rows += [("MPEG", "MPEGAudioVersion", {1: "1", 2: "2", 3: "2.5"}[ver]),
                     ("MPEG", "AudioLayer", str(layer)), ("MPEG", "AudioBitrate", f"{br} kbps"),
                     ("MPEG", "SampleRate", str(sr)), ("MPEG", "ChannelMode", mode)]
            if br:
                rows.append(("Composite", "Duration", fmt_dur(audio_bytes * 8 / (br * 1000)) + " (approx.)"))
            break
    return rows


# --------------------------------------------------------------- misc fmt --
def pdf_unescape(s):
    s = re.sub(rb"\\([nrtbf()\\])", lambda m: {b"n": b"\n", b"r": b"\r", b"t": b"\t", b"b": b"\b",
                                               b"f": b"\f"}.get(m.group(1), m.group(1)), s)
    s = re.sub(rb"\\([0-7]{1,3})", lambda m: bytes([int(m.group(1), 8) & 255]), s)
    return s


def pdf_decode(b):
    if b[:2] == b"\xfe\xff":
        return b[2:].decode("utf-16-be", "replace")
    try:
        return b.decode("utf-8")
    except UnicodeDecodeError:
        return b.decode("latin-1")


def pdf_date(s):
    m = re.match(r"D:(\d{4})(\d\d)?(\d\d)?(\d\d)?(\d\d)?(\d\d)?", s)
    if not m:
        return s
    p = [x or ("01" if i < 3 else "00") for i, x in enumerate(m.groups())]
    return f"{p[0]}:{p[1]}:{p[2]} {p[3]}:{p[4]}:{p[5]}"


MP4_EPOCH = dt.datetime(1904, 1, 1)
MP4_NAMES = {"\xa9nam": "Title", "\xa9ART": "Artist", "\xa9alb": "Album", "\xa9day": "Year",
             "\xa9gen": "Genre", "\xa9cmt": "Comment", "\xa9too": "Encoder", "aART": "AlbumArtist",
             "\xa9wrt": "Composer", "cprt": "Copyright", "desc": "Description", "\xa9grp": "Grouping",
             "\xa9lyr": "Lyrics"}


def mp4_atoms(data, start, end):
    i = start
    while i + 8 <= end:
        size = struct.unpack(">I", data[i:i + 4])[0]
        typ = data[i + 4:i + 8]
        hdr = 8
        if size == 1:
            size = struct.unpack(">Q", data[i + 8:i + 16])[0]
            hdr = 16
        elif size == 0:
            size = end - i
        if size < hdr:
            break
        yield typ, i + hdr, min(i + size, end)
        i += size


CORE_MAP = {"Title": "dc:title", "Subject": "dc:subject", "Creator": "dc:creator",
            "Keywords": "cp:keywords", "Description": "dc:description",
            "LastModifiedBy": "cp:lastModifiedBy", "Revision": "cp:revision",
            "Created": "dcterms:created", "Modified": "dcterms:modified", "Category": "cp:category",
            "ContentStatus": "cp:contentStatus", "Language": "dc:language"}
APP_FIELDS = ["Application", "AppVersion", "Company", "Manager", "Template", "Pages", "Words",
              "Characters", "Lines", "Paragraphs", "Slides", "Notes", "HiddenSlides", "TotalTime",
              "DocSecurity"]


def read_all(path, limit=500 * 1024 * 1024):
    if os.path.getsize(path) > limit:
        raise ValueError("File too large for this operation")
    with open(path, "rb") as f:
        return f.read()


def detect(path):
    with open(path, "rb") as f:
        h = f.read(16)
    ext = os.path.splitext(path)[1].lower().lstrip(".")
    if h[:2] == b"\xff\xd8":
        return "JPEG"
    if h[:8] == PNG_SIG:
        return "PNG"
    if h[:6] in (b"GIF87a", b"GIF89a"):
        return "GIF"
    if h[:2] == b"BM":
        return "BMP"
    if h[:4] == b"RIFF" and h[8:12] == b"WEBP":
        return "WEBP"
    if h[:4] == b"RIFF" and h[8:12] == b"WAVE":
        return "WAV"
    if h[:4] == b"%PDF":
        return "PDF"
    if h[:4] in (b"II*\0", b"MM\0*"):
        return "TIFF"
    if h[4:8] == b"ftyp":
        return "MP4"
    if h[:3] == b"ID3" or ext == "mp3":
        return "MP3"
    if h[:4] == b"PK\x03\x04" and ext in ("docx", "xlsx", "pptx"):
        return ext.upper()
    return ext.upper() or "UNKNOWN"


class MetaEngine:
    """Pure-Python reader / writer. API: read(), write(), strip_all(), version()."""
    WRITE_FORMATS = ("JPEG", "PNG", "MP3", "DOCX", "XLSX", "PPTX")

    def version(self):
        return "built-in pure-Python engine"

    # ------------------------------------------------------------- READ --
    def read(self, path, raw=False):
        ft = detect(path)
        mime = mimetypes.guess_type(path)[0] or "application/octet-stream"
        st = os.stat(path)
        rows = [("File", "FileName", os.path.basename(path)),
                ("File", "Directory", os.path.dirname(os.path.abspath(path))),
                ("File", "FileSize", human_size(st.st_size)),
                ("File", "FileModifyDate", ts_str(st.st_mtime)),
                ("File", "FileAccessDate", ts_str(st.st_atime)),
                ("File", "FileCreateDate", ts_str(st.st_ctime)),
                ("File", "FileType", ft), ("File", "MIMEType", mime),
                ("File", "FilePermissions", oct(st.st_mode & 0o777))]
        fn = {"JPEG": self._r_jpeg, "PNG": self._r_png, "GIF": self._r_gif, "BMP": self._r_bmp,
              "WEBP": self._r_webp, "WAV": self._r_wav, "PDF": self._r_pdf, "TIFF": self._r_tiff,
              "MP3": self._r_mp3, "MP4": self._r_mp4, "DOCX": self._r_ooxml, "XLSX": self._r_ooxml,
              "PPTX": self._r_ooxml}.get(ft)
        if fn:
            try:
                rows += fn(path, raw)
            except Exception as ex:
                rows.append(("Warning", "ReadError", f"{type(ex).__name__}: {ex}"))
        else:
            rows.append(("Warning", "Format", f"No metadata reader for '{ft}' - only file info shown"))
        # unique keys
        seen, out = {}, []
        for g, t, v in rows:
            full = f"{g}:{t}"
            if full in seen:
                seen[full] += 1
                t = f"{t} ({seen[full]})"
                full = f"{g}:{t}"
            else:
                seen[full] = 1
            out.append((g, t, str(v), full))
        return out

    def _r_jpeg(self, path, raw):
        data = read_all(path)
        segs, _ = jpeg_segments(data)
        rows, w, h = [], None, None
        for m, s, e in segs:
            p = data[s + 4:e]
            if m == 0xE0 and p[:5] == b"JFIF\0":
                rows += [("JFIF", "JFIFVersion", f"{p[5]}.{p[6]:02d}"),
                         ("JFIF", "ResolutionUnit", {0: "None", 1: "inches", 2: "cm"}.get(p[7], str(p[7]))),
                         ("JFIF", "XResolution", str(struct.unpack(">H", p[8:10])[0])),
                         ("JFIF", "YResolution", str(struct.unpack(">H", p[10:12])[0]))]
            elif m == 0xE1 and p[:6] == b"Exif\0\0":
                t = parse_tiff(p, 6)
                if t:
                    rows += tiff_rows(t, raw)
            elif m == 0xE1 and p.startswith(b"http://ns.adobe.com/xap/1.0/\0"):
                rows += xmp_rows(p[29:].decode("utf-8", "replace"))
            elif m == 0xE2 and p[:11] == b"ICC_PROFILE":
                rows.append(("ICC_Profile", "ProfileSize", f"{len(p) - 14} bytes"))
            elif m == 0xED and p[:6] == b"Photos":
                rows.append(("Photoshop", "IPTC/Photoshop", f"(present, {len(p)} bytes - read-only)"))
            elif m == 0xFE:
                rows.append(("File", "Comment", p.decode("utf-8", "replace")))
            elif 0xC0 <= m <= 0xCF and m not in (0xC4, 0xC8, 0xCC):
                prec, h, w, nc = struct.unpack(">BHHB", p[:6])
                rows += [("File", "ImageWidth", str(w)), ("File", "ImageHeight", str(h)),
                         ("File", "BitsPerSample", str(prec)), ("File", "ColorComponents", str(nc)),
                         ("File", "EncodingProcess", {0xC0: "Baseline DCT", 0xC1: "Extended sequential DCT",
                                                      0xC2: "Progressive DCT"}.get(m, f"SOF{m - 0xC0}"))]
        if w and h:
            rows += [("Composite", "ImageSize", f"{w}x{h}"),
                     ("Composite", "Megapixels", f"{w * h / 1e6:.3g}")]
        return rows

    def _r_tiff(self, path, raw):
        data = read_all(path)
        t = parse_tiff(data, 0)
        return tiff_rows(t, raw) if t else []

    def _r_png(self, path, raw):
        data = read_all(path)
        rows, w, h = [], None, None
        for typ, p, _ in png_chunks(data):
            if typ == b"IHDR":
                w, h, bd, ct, cm, fl, il = struct.unpack(">IIBBBBB", p[:13])
                rows += [("PNG", "ImageWidth", w), ("PNG", "ImageHeight", h), ("PNG", "BitDepth", bd),
                         ("PNG", "ColorType", {0: "Grayscale", 2: "RGB", 3: "Palette", 4: "Grayscale with Alpha",
                                               6: "RGB with Alpha"}.get(ct, ct)),
                         ("PNG", "Compression", "Deflate/Inflate" if cm == 0 else cm),
                         ("PNG", "Filter", "Adaptive" if fl == 0 else fl),
                         ("PNG", "Interlace", "Noninterlaced" if il == 0 else "Adam7 Interlace")]
            elif typ == b"pHYs":
                x, y, u = struct.unpack(">IIB", p[:9])
                rows += [("PNG", "PixelsPerUnitX", x), ("PNG", "PixelsPerUnitY", y),
                         ("PNG", "PixelUnits", "meters" if u == 1 else "Unknown")]
            elif typ == b"gAMA":
                rows.append(("PNG", "Gamma", f"{struct.unpack('>I', p[:4])[0] / 100000:.5g}"))
            elif typ == b"tIME":
                y, mo, d, hh, mi, ss = struct.unpack(">HBBBBB", p[:7])
                rows.append(("PNG", "ModifyDate", f"{y:04d}:{mo:02d}:{d:02d} {hh:02d}:{mi:02d}:{ss:02d}"))
            elif typ in (b"tEXt", b"zTXt", b"iTXt"):
                kv = png_text(typ, p)
                if kv:
                    if kv[0] == "XML:com.adobe.xmp":
                        rows += xmp_rows(kv[1])
                    else:
                        rows.append(("PNG", kv[0], kv[1]))
            elif typ == b"eXIf":
                t = parse_tiff(p, 0)
                if t:
                    rows += tiff_rows(t, raw)
        if w and h:
            rows += [("Composite", "ImageSize", f"{w}x{h}"), ("Composite", "Megapixels", f"{w * h / 1e6:.3g}")]
        return rows

    def _r_gif(self, path, raw):
        with open(path, "rb") as f:
            h = f.read(13)
        w, hh, fl = struct.unpack("<HHB", h[6:11])
        return [("GIF", "GIFVersion", h[3:6].decode()), ("GIF", "ImageWidth", w), ("GIF", "ImageHeight", hh),
                ("GIF", "HasColorMap", "Yes" if fl & 0x80 else "No"),
                ("GIF", "ColorResolutionDepth", (fl >> 4 & 7) + 1), ("Composite", "ImageSize", f"{w}x{hh}")]

    def _r_bmp(self, path, raw):
        with open(path, "rb") as f:
            h = f.read(54)
        w, hh = struct.unpack("<ii", h[18:26])
        bpp = struct.unpack("<H", h[28:30])[0]
        comp = struct.unpack("<I", h[30:34])[0]
        return [("BMP", "ImageWidth", w), ("BMP", "ImageHeight", abs(hh)), ("BMP", "BitDepth", bpp),
                ("BMP", "Compression", {0: "None", 1: "RLE8", 2: "RLE4", 3: "Bitfields"}.get(comp, comp)),
                ("Composite", "ImageSize", f"{w}x{abs(hh)}")]

    def _r_webp(self, path, raw):
        data = read_all(path)
        rows, i = [], 12
        w = h = None
        while i + 8 <= len(data):
            typ = data[i:i + 4]
            L = struct.unpack("<I", data[i + 4:i + 8])[0]
            p = data[i + 8:i + 8 + L]
            if typ == b"VP8X":
                w = 1 + int.from_bytes(p[4:7], "little")
                h = 1 + int.from_bytes(p[7:10], "little")
                rows.append(("WEBP", "Flags", hex(p[0])))
            elif typ == b"VP8 " and w is None:
                w, h = struct.unpack("<HH", p[6:10])
                w, h = w & 0x3FFF, h & 0x3FFF
            elif typ == b"VP8L" and w is None:
                b = p[1:5]
                w = 1 + (((b[1] & 0x3F) << 8) | b[0])
                h = 1 + (((b[3] & 0xF) << 10) | (b[2] << 2) | ((b[1] & 0xC0) >> 6))
            elif typ == b"EXIF":
                t = parse_tiff(p[6:] if p[:6] == b"Exif\0\0" else p, 0)
                if t:
                    rows += tiff_rows(t, raw)
            elif typ == b"XMP ":
                rows += xmp_rows(p.decode("utf-8", "replace"))
            i += 8 + L + (L & 1)
        if w:
            rows = [("WEBP", "ImageWidth", w), ("WEBP", "ImageHeight", h),
                    ("Composite", "ImageSize", f"{w}x{h}")] + rows
        return rows

    def _r_wav(self, path, raw):
        data = read_all(path, 200 * 1024 * 1024)
        rows, i, br, size = [], 12, 0, 0
        names = {b"INAM": "Title", b"IART": "Artist", b"ICMT": "Comment", b"ICRD": "DateCreated",
                 b"ISFT": "Software", b"IPRD": "Product", b"IGNR": "Genre", b"ICOP": "Copyright"}
        while i + 8 <= len(data):
            cid, L = data[i:i + 4], struct.unpack("<I", data[i + 4:i + 8])[0]
            p = data[i + 8:i + 8 + L]
            if cid == b"fmt ":
                fmt, ch, sr, br, _, bps = struct.unpack("<HHIIHH", p[:16])
                rows += [("RIFF", "Encoding", {1: "Microsoft PCM", 3: "IEEE Float"}.get(fmt, str(fmt))),
                         ("RIFF", "NumChannels", ch), ("RIFF", "SampleRate", sr),
                         ("RIFF", "AvgBytesPerSec", br), ("RIFF", "BitsPerSample", bps)]
            elif cid == b"data":
                size = L
            elif cid == b"LIST" and p[:4] == b"INFO":
                j = 4
                while j + 8 <= len(p):
                    k, kl = p[j:j + 4], struct.unpack("<I", p[j + 4:j + 8])[0]
                    rows.append(("RIFF", names.get(k, k.decode("latin-1")),
                                 p[j + 8:j + 8 + kl].split(b"\0")[0].decode("utf-8", "replace")))
                    j += 8 + kl + (kl & 1)
            i += 8 + L + (L & 1)
        if br and size:
            rows.append(("Composite", "Duration", fmt_dur(size / br)))
        return rows

    def _r_pdf(self, path, raw):
        data = read_all(path, 300 * 1024 * 1024)
        rows = [("PDF", "PDFVersion", data[5:8].decode("latin-1", "replace"))]
        pages = len(re.findall(rb"/Type\s*/Page[^s]", data))
        if pages:
            rows.append(("PDF", "PageCount", pages))
        for key in ("Title", "Author", "Subject", "Keywords", "Creator", "Producer", "CreationDate", "ModDate"):
            ms = re.findall(rb"/" + key.encode() + rb"\s*(\((?:\\.|[^\\)])*\)|<[0-9A-Fa-f\s]*>)", data)
            if ms:
                v = ms[-1]
                if v[:1] == b"(":
                    s = pdf_decode(pdf_unescape(v[1:-1]))
                else:
                    hx = re.sub(rb"\s", b"", v[1:-1])
                    s = pdf_decode(bytes.fromhex((hx + b"0" * (len(hx) % 2)).decode()))
                if key.endswith("Date"):
                    s = pdf_date(s)
                rows.append(("PDF", key, s))
        if b"/Encrypt" in data:
            rows.append(("PDF", "Encrypted", "Yes"))
        return rows

    def _r_mp3(self, path, raw):
        size = os.path.getsize(path)
        rows = []
        with open(path, "rb") as f:
            head = f.read(10)
            total = 0
            if head[:3] == b"ID3":
                n = 10 + _syncsafe(head[6:10])
                f.seek(0)
                tag = id3_parse(f.read(n + 10))
                if tag:
                    total = tag["total"]
                    rows.append(("ID3", "ID3Version", f"2.{tag['ver']}"))
                    rows += id3_frame_rows(tag["frames"])
            f.seek(total)
            chunk = f.read(8192)
            v1 = None
            if size > 128:
                f.seek(size - 128)
                last = f.read(128)
                if last[:3] == b"TAG":
                    v1 = last
        if v1:
            def s(b):
                return b.split(b"\0")[0].decode("latin-1").strip()
            g = v1[127]
            rows += [("ID3v1", "Title", s(v1[3:33])), ("ID3v1", "Artist", s(v1[33:63])),
                     ("ID3v1", "Album", s(v1[63:93])), ("ID3v1", "Year", s(v1[93:97])),
                     ("ID3v1", "Comment", s(v1[97:127])),
                     ("ID3v1", "Genre", ID3V1_GENRES[g] if g < len(ID3V1_GENRES) else str(g))]
        rows += mp3_info(chunk, size - total - (128 if v1 else 0))
        return rows

    def _r_mp4(self, path, raw):
        size = os.path.getsize(path)
        rows, moov = [], None
        with open(path, "rb") as f:
            pos = 0
            while pos + 8 <= size:
                f.seek(pos)
                h = f.read(16)
                sz = struct.unpack(">I", h[:4])[0]
                typ = h[4:8]
                hdr = 8
                if sz == 1:
                    sz = struct.unpack(">Q", h[8:16])[0]
                    hdr = 16
                elif sz == 0:
                    sz = size - pos
                if sz < hdr:
                    break
                if typ == b"ftyp":
                    f.seek(pos + hdr)
                    rows.append(("QuickTime", "MajorBrand", f.read(4).decode("latin-1")))
                if typ == b"moov":
                    f.seek(pos + hdr)
                    moov = f.read(min(sz - hdr, 64 * 1024 * 1024))
                pos += sz
        if not moov:
            return rows
        for typ, s, e in mp4_atoms(moov, 0, len(moov)):
            if typ == b"mvhd":
                v = moov[s]
                if v == 1:
                    c, m, ts, du = struct.unpack(">QQIQ", moov[s + 4:s + 32])
                else:
                    c, m, ts, du = struct.unpack(">IIII", moov[s + 4:s + 20])
                if c:
                    rows.append(("QuickTime", "CreateDate", (MP4_EPOCH + dt.timedelta(seconds=c)).strftime("%Y:%m:%d %H:%M:%S")))
                if m:
                    rows.append(("QuickTime", "ModifyDate", (MP4_EPOCH + dt.timedelta(seconds=m)).strftime("%Y:%m:%d %H:%M:%S")))
                if ts:
                    rows += [("QuickTime", "TimeScale", ts), ("Composite", "Duration", fmt_dur(du / ts))]
            elif typ == b"trak":
                for t2, s2, e2 in mp4_atoms(moov, s, e):
                    if t2 == b"tkhd":
                        w, h = struct.unpack(">II", moov[e2 - 8:e2])
                        if w >> 16 and h >> 16:
                            rows += [("QuickTime", "ImageWidth", w >> 16), ("QuickTime", "ImageHeight", h >> 16),
                                     ("Composite", "ImageSize", f"{w >> 16}x{h >> 16}")]
            elif typ == b"udta":
                for t2, s2, e2 in mp4_atoms(moov, s, e):
                    if t2 == b"meta":
                        for t3, s3, e3 in mp4_atoms(moov, s2 + 4, e2):
                            if t3 == b"ilst":
                                for t4, s4, e4 in mp4_atoms(moov, s3, e3):
                                    k = t4.decode("latin-1")
                                    for t5, s5, e5 in mp4_atoms(moov, s4, e4):
                                        if t5 == b"data":
                                            body = moov[s5 + 8:e5]
                                            flag = struct.unpack(">I", moov[s5:s5 + 4])[0] & 0xFFFFFF
                                            if k == "covr":
                                                rows.append(("iTunes", "CoverArt", f"(Binary data {len(body)} bytes)"))
                                            elif flag == 1:
                                                rows.append(("iTunes", MP4_NAMES.get(k, k), body.decode("utf-8", "replace")))
                                            elif k == "trkn" and len(body) >= 6:
                                                rows.append(("iTunes", "Track", f"{body[3]} of {body[5]}"))
        return rows

    def _r_ooxml(self, path, raw):
        rows = []
        with zipfile.ZipFile(path) as z:
            names = z.namelist()
            if "docProps/core.xml" in names:
                x = z.read("docProps/core.xml").decode("utf-8", "replace")
                for n, tag in CORE_MAP.items():
                    m = re.search(r"<%s(?:\s[^>]*)?>(.*?)</%s>" % (tag, tag), x, re.S)
                    if m:
                        rows.append(("Core", n, re.sub(r"<[^>]+>", "", m.group(1)).replace("&amp;", "&")
                                     .replace("&lt;", "<").replace("&gt;", ">")))
            if "docProps/app.xml" in names:
                x = z.read("docProps/app.xml").decode("utf-8", "replace")
                for n in APP_FIELDS:
                    m = re.search(r"<%s>(.*?)</%s>" % (n, n), x, re.S)
                    if m and m.group(1).strip():
                        rows.append(("App", n, m.group(1).strip()))
            rows.append(("Zip", "ContainedFiles", len(names)))
        return rows

    # ------------------------------------------------------------ WRITE --
    def _save(self, path, new, keep_backup):
        if keep_backup:
            bak = path + "_original"
            if not os.path.exists(bak):
                shutil.copy2(path, bak)
        tmp = path + ".metastudio.tmp"
        with open(tmp, "wb") as f:
            f.write(new)
        try:
            shutil.copymode(path, tmp)
        except Exception:
            pass
        os.replace(tmp, path)

    def write(self, path, changes, keep_backup=False):
        """changes {full_tag: value | None}. Returns (ok, message)."""
        try:
            ft = detect(path)
            items = [(*split_tag(k), v) for k, v in changes.items()]
            fn = {"JPEG": self._w_jpeg, "PNG": self._w_png, "MP3": self._w_mp3,
                  "DOCX": self._w_ooxml, "XLSX": self._w_ooxml, "PPTX": self._w_ooxml}.get(ft)
            if not fn:
                return False, (f"{ft}: this format is read-only in the built-in engine.\n"
                               f"Writable: {', '.join(self.WRITE_FORMATS)}")
            new = fn(path, items)
            self._save(path, new, keep_backup)
            return True, "1 file updated"
        except Exception as ex:
            return False, f"{type(ex).__name__}: {ex}"

    def strip_all(self, path, keep_backup=False):
        try:
            ft = detect(path)
            if ft == "JPEG":
                data = read_all(path)
                segs, sos = jpeg_segments(data)
                out = b"\xff\xd8"
                for m, s, e in segs:
                    if m == 0xE1 or m == 0xED or m == 0xFE or 0xE3 <= m <= 0xEC or m == 0xEF:
                        continue
                    out += data[s:e]
                new = out + data[sos:]
            elif ft == "PNG":
                data = read_all(path)
                new = PNG_SIG + b"".join(raw for typ, p, raw in png_chunks(data)
                                         if typ not in (b"tEXt", b"zTXt", b"iTXt", b"eXIf", b"tIME"))
            elif ft == "MP3":
                data = read_all(path)
                tag = id3_parse(data[:10 + _syncsafe(data[6:10])] if data[:3] == b"ID3" else b"")
                new = data[tag["total"]:] if tag else data
                if len(new) > 128 and new[-128:-125] == b"TAG":
                    new = new[:-128]
            elif ft in ("DOCX", "XLSX", "PPTX"):
                new = self._w_ooxml(path, [(None, n, None) for n in CORE_MAP] +
                                    [("App", "Company", None), ("App", "Manager", None)])
            else:
                return False, f"{ft}: strip is not supported for this format"
            self._save(path, new, keep_backup)
            return True, "1 file updated"
        except Exception as ex:
            return False, f"{type(ex).__name__}: {ex}"

    # ----- JPEG
    def _w_jpeg(self, path, items):
        data = read_all(path)
        if data[:2] != b"\xff\xd8":
            raise ValueError("Not a valid JPEG file")
        exif_items, comment, errors = [], "__keep__", []
        for g, n, v in items:
            if n == "Comment" and (g is None or g.upper() in ("FILE", "JPEG", "COM")):
                comment = v
            elif g and g.upper() not in EXIF_GROUPS:
                errors.append(f"{g}:{n} cannot be written in JPEG (writable: EXIF:*, GPS:*, File:Comment)")
            else:
                exif_items.append((g, n, v))
        if errors:
            raise ValueError("\n".join(errors))
        segs, sos = jpeg_segments(data)
        tiff, exif_raw = None, None
        others = []
        for m, s, e in segs:
            p = data[s + 4:e]
            if m == 0xE1 and p[:6] == b"Exif\0\0":
                if tiff is None:
                    tiff = parse_tiff(p, 6)
                    exif_raw = data[s:e]
                continue
            if m == 0xFE and comment != "__keep__":
                continue
            others.append((m, data[s:e]))
        exif_seg = exif_raw
        if exif_items:
            if tiff is None:
                tiff = {"endian": "<", "IFD0": {}}
            apply_exif(tiff, exif_items)
            payload = b"Exif\0\0" + build_tiff(tiff)
            if len(payload) + 2 > 65535:
                raise ValueError("EXIF block too large (>64 KB)")
            exif_seg = b"\xff\xe1" + struct.pack(">H", len(payload) + 2) + payload
        out = b"\xff\xd8"
        k = 0
        while k < len(others) and others[k][0] == 0xE0:
            out += others[k][1]
            k += 1
        if exif_seg:
            out += exif_seg
        if comment not in ("__keep__", None):
            c = comment.encode("utf-8")
            out += b"\xff\xfe" + struct.pack(">H", len(c) + 2) + c
        for m, b in others[k:]:
            out += b
        return out + data[sos:]

    # ----- PNG
    def _w_png(self, path, items):
        data = read_all(path)
        if data[:8] != PNG_SIG:
            raise ValueError("Not a valid PNG file")
        exif_items, texts, errors = [], {}, []
        for g, n, v in items:
            if (g and g.upper() in EXIF_GROUPS) or (g is None and n in ALLTAGS):
                exif_items.append((g, n, v))
            elif g is None or g.upper() == "PNG":
                if n in PNG_RO:
                    errors.append(f"PNG:{n} is read-only")
                else:
                    texts[n] = v
            else:
                errors.append(f"{g}:{n} cannot be written in PNG (use PNG:<Keyword> or EXIF:*)")
        if errors:
            raise ValueError("\n".join(errors))
        out, new_chunks, tiff = [], [], None
        for typ, p, rawc in png_chunks(data):
            if typ in (b"tEXt", b"zTXt", b"iTXt"):
                kv = png_text(typ, p)
                if kv and kv[0] in texts:
                    continue
            if typ == b"eXIf" and exif_items:
                tiff = parse_tiff(p, 0)
                continue
            out.append((typ, rawc))
        for k, v in texts.items():
            if v is None:
                continue
            if not (1 <= len(k) <= 79):
                raise ValueError("PNG keyword must be 1-79 characters")
            try:
                kb, vb = k.encode("latin-1"), v.encode("latin-1")
                if b"\0" in vb:
                    raise UnicodeEncodeError("x", "", 0, 1, "")
                new_chunks.append(png_chunk(b"tEXt", kb + b"\0" + vb))
            except UnicodeEncodeError:
                new_chunks.append(png_chunk(b"iTXt", k.encode("latin-1", "replace") + b"\0\0\0\0\0" + v.encode("utf-8")))
        if exif_items:
            if tiff is None:
                tiff = {"endian": "<", "IFD0": {}}
            apply_exif(tiff, exif_items)
            new_chunks.append(png_chunk(b"eXIf", build_tiff(tiff)))
        res = PNG_SIG
        inserted = False
        for typ, rawc in out:
            if typ == b"IDAT" and not inserted:
                res += b"".join(new_chunks)
                inserted = True
            res += rawc
        if not inserted:
            res += b"".join(new_chunks)
        return res

    # ----- MP3
    def _w_mp3(self, path, items):
        data = read_all(path)
        tag = id3_parse(data[:10 + _syncsafe(data[6:10])] if data[:3] == b"ID3" else b"")
        frames = list(tag["frames"]) if tag else []
        audio = data[tag["total"]:] if tag else data
        errors = []
        for g, n, v in items:
            if g and g.upper() != "ID3":
                errors.append(f"{g}:{n} cannot be written in MP3 (use ID3:<Name>)")
                continue
            if n.startswith("TXXX:"):
                desc = n[5:]
                frames = [f for f in frames if not (f[0] == "TXXX" and _txxx_desc(f[1]) == desc)]
                if v is not None:
                    frames.append(("TXXX", _mk_txxx(desc, v)))
                continue
            fid = ID3_WRITE.get(n) or (n if re.fullmatch(r"T[A-Z0-9]{3}", n) else None)
            if not fid:
                errors.append(f"Unknown ID3 tag '{n}'. Try: {', '.join(list(ID3_WRITE)[:8])} ...")
                continue
            frames = [f for f in frames if f[0] != fid and not (fid == "TYER" and f[0] == "TDRC")]
            if v is None:
                continue
            if fid in ("COMM", "USLT"):
                body = enc_text(v)
                frames.append((fid, body[:1] + b"eng" + (b"\0" if body[0] == 0 else b"\xff\xfe\0\0") + body[1:]))
            else:
                frames.append((fid, enc_text(v)))
        if errors:
            raise ValueError("\n".join(errors))
        body = id3_build_frames(frames)
        if not body:
            return audio
        return b"ID3" + bytes([3, 0, 0]) + _to_syncsafe(len(body)) + body + audio

    # ----- OOXML
    def _w_ooxml(self, path, items):
        errors = []
        core, app = {}, {}
        for g, n, v in items:
            if n in CORE_MAP and (g is None or g.upper() == "CORE"):
                core[n] = v
            elif n in ("Company", "Manager") and g and g.upper() == "APP":
                app[n] = v
            else:
                errors.append(f"{(g + ':') if g else ''}{n} is not writable (use Core:Title, Core:Creator, ...)")
        if errors:
            raise ValueError("\n".join(errors))
        buf = io.BytesIO()
        with zipfile.ZipFile(path) as zin, zipfile.ZipFile(buf, "w", zipfile.ZIP_DEFLATED) as zout:
            if core and "docProps/core.xml" not in zin.namelist():
                raise ValueError("This document has no docProps/core.xml")
            for info in zin.infolist():
                b = zin.read(info.filename)
                if info.filename == "docProps/core.xml" and core:
                    x = b.decode("utf-8")
                    for n, v in core.items():
                        x = _xml_set(x, CORE_MAP[n], v, "</cp:coreProperties>",
                                     ' xsi:type="dcterms:W3CDTF"' if n in ("Created", "Modified") else "")
                    b = x.encode("utf-8")
                elif info.filename == "docProps/app.xml" and app:
                    x = b.decode("utf-8")
                    for n, v in app.items():
                        x = _xml_set(x, n, v, "</Properties>", "")
                    b = x.encode("utf-8")
                zout.writestr(info, b)
        return buf.getvalue()


def _mk_txxx(desc, val):
    try:
        desc.encode("latin-1")
        val.encode("latin-1")
        return b"\x00" + desc.encode("latin-1") + b"\0" + val.encode("latin-1")
    except UnicodeEncodeError:
        return b"\x01\xff\xfe" + desc.encode("utf-16-le") + b"\0\0\xff\xfe" + val.encode("utf-16-le")


def _txxx_desc(data):
    enc = data[0]
    d, _ = _split_term(data[1:], enc)
    return d.decode(_codec(enc), "replace").strip("\x00\ufeff")


def _xml_set(x, tag, val, closing, attrs):
    pat = re.compile(r"<%s(\s[^>]*)?(?:/>|>.*?</%s>)" % (re.escape(tag), re.escape(tag)), re.S)
    if val is None:
        return pat.sub("", x)
    new = f"<{tag}{attrs}>{xml_escape(val)}</{tag}>"
    if pat.search(x):
        return pat.sub(lambda m: new, x, count=1)
    if closing not in x:
        raise ValueError(f"Cannot insert {tag}: unexpected XML layout")
    return x.replace(closing, new + closing)


# =====================================================================
#                            DATABASE
# =====================================================================
class DB:
    def __init__(self, path=DB_FILE):
        self.conn = sqlite3.connect(path, check_same_thread=False)
        self.lock = threading.Lock()
        self.conn.executescript("""
        CREATE TABLE IF NOT EXISTS settings(key TEXT PRIMARY KEY, value TEXT);
        CREATE TABLE IF NOT EXISTS files(
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            path TEXT UNIQUE, name TEXT, ext TEXT, size INTEGER,
            added_at TEXT, last_scanned TEXT, tag_count INTEGER DEFAULT 0);
        CREATE TABLE IF NOT EXISTS snapshots(
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            path TEXT, scanned_at TEXT, tag_count INTEGER, data TEXT);
        CREATE TABLE IF NOT EXISTS edits(
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            at TEXT, path TEXT, tag TEXT, old_value TEXT, new_value TEXT,
            action TEXT, status TEXT, reverted INTEGER DEFAULT 0);
        """)
        self.conn.commit()

    def q(self, sql, args=(), commit=False):
        with self.lock:
            cur = self.conn.execute(sql, args)
            if commit:
                self.conn.commit()
            return cur.fetchall()

    def get(self, key, default=None):
        r = self.q("SELECT value FROM settings WHERE key=?", (key,))
        return r[0][0] if r else default

    def set(self, key, value):
        self.q("INSERT INTO settings(key,value) VALUES(?,?) "
               "ON CONFLICT(key) DO UPDATE SET value=excluded.value", (key, str(value)), True)

    def add_file(self, path):
        try:
            size = os.path.getsize(path)
        except OSError:
            size = 0
        self.q("INSERT OR IGNORE INTO files(path,name,ext,size,added_at) VALUES(?,?,?,?,?)",
               (path, os.path.basename(path), os.path.splitext(path)[1].lower().lstrip("."), size, now()), True)

    def remove_file(self, path):
        self.q("DELETE FROM files WHERE path=?", (path,), True)

    def all_files(self):
        return self.q("SELECT path,ext,size FROM files ORDER BY added_at DESC, id DESC")

    def mark_scanned(self, path, count):
        self.q("UPDATE files SET last_scanned=?, tag_count=? WHERE path=?", (now(), count, path), True)

    def add_snapshot(self, path, rows):
        self.q("INSERT INTO snapshots(path,scanned_at,tag_count,data) VALUES(?,?,?,?)",
               (path, now(), len(rows), json.dumps({r[3]: r[2] for r in rows})), True)

    def snapshots(self, path):
        return self.q("SELECT id,scanned_at,tag_count FROM snapshots WHERE path=? ORDER BY id DESC", (path,))

    def snapshot_data(self, sid):
        r = self.q("SELECT data FROM snapshots WHERE id=?", (sid,))
        return json.loads(r[0][0]) if r else {}

    def log_edit(self, path, tag, old, new, action, status):
        self.q("INSERT INTO edits(at,path,tag,old_value,new_value,action,status) VALUES(?,?,?,?,?,?,?)",
               (now(), path, tag, old, new, action, status), True)

    def edits(self, limit=500):
        return self.q("SELECT id,at,path,tag,old_value,new_value,action,status,reverted "
                      "FROM edits ORDER BY id DESC LIMIT ?", (limit,))

    def edit(self, eid):
        r = self.q("SELECT id,at,path,tag,old_value,new_value,action,status,reverted FROM edits WHERE id=?", (eid,))
        return r[0] if r else None

    def mark_reverted(self, eid):
        self.q("UPDATE edits SET reverted=1 WHERE id=?", (eid,), True)

    def stats(self):
        return (self.q("SELECT COUNT(*) FROM files")[0][0], self.q("SELECT COUNT(*) FROM edits")[0][0],
                self.q("SELECT COUNT(*) FROM snapshots")[0][0])


# =====================================================================
#                               GUI
# =====================================================================
C = {"bg": "#0b1020", "panel": "#131a2e", "card": "#1a2340", "card2": "#212c50", "border": "#2b3866",
     "text": "#e6eaf7", "muted": "#8d9bc4", "accent": "#7c5cff", "accent2": "#22d3ee",
     "ok": "#34d399", "warn": "#fbbf24", "err": "#f87171", "row_a": "#161e38", "row_b": "#1a2342"}
FONT = ("Segoe UI", 10)
FONT_B = ("Segoe UI", 10, "bold")
FONT_H = ("Segoe UI", 18, "bold")
FONT_S = ("Segoe UI", 9)
MONO = ("Consolas", 10)
TYPE_ICONS = {"image": "🖼️", "audio": "🎵", "video": "🎬", "pdf": "📕", "text": "📄", "app": "📦"}

CAPS_TEXT = (
    "Format            Read   Write   Strip\n"
    "JPEG              ✔      ✔ EXIF/GPS/Comment   ✔\n"
    "PNG               ✔      ✔ PNG:*, EXIF        ✔\n"
    "MP3               ✔      ✔ ID3 tags           ✔\n"
    "DOCX/XLSX/PPTX    ✔      ✔ Core properties    ✔\n"
    "TIFF/GIF/BMP/WEBP ✔      -                    -\n"
    "WAV/MP4/M4A/MOV   ✔      -                    -\n"
    "PDF               ✔      -                    -")


class TagDialog(tk.Toplevel):
    def __init__(self, master, title, tag="", value="", tag_editable=True):
        super().__init__(master)
        self.title(title)
        self.configure(bg=C["panel"])
        self.transient(master)
        self.resizable(False, False)
        self.result = None
        frm = tk.Frame(self, bg=C["panel"], padx=22, pady=18)
        frm.pack(fill="both", expand=True)
        tk.Label(frm, text=title, font=("Segoe UI", 14, "bold"), bg=C["panel"], fg=C["text"]
                 ).grid(row=0, column=0, columnspan=2, sticky="w", pady=(0, 12))
        tk.Label(frm, text="Tag  (EXIF:Artist · GPS:GPSLatitude · PNG:Author · ID3:Title · Core:Title · File:Comment)",
                 bg=C["panel"], fg=C["muted"], font=FONT_S).grid(row=1, column=0, sticky="w")
        self.e_tag = ttk.Entry(frm, width=58)
        self.e_tag.insert(0, tag)
        if not tag_editable:
            self.e_tag.state(["readonly"])
        self.e_tag.grid(row=2, column=0, columnspan=2, sticky="ew", pady=(2, 10))
        tk.Label(frm, text="Value", bg=C["panel"], fg=C["muted"], font=FONT_S).grid(row=3, column=0, sticky="w")
        self.t_val = tk.Text(frm, width=58, height=6, bg=C["card"], fg=C["text"], insertbackground=C["text"],
                             relief="flat", font=FONT, highlightthickness=1, highlightbackground=C["border"],
                             highlightcolor=C["accent"], padx=8, pady=6)
        self.t_val.insert("1.0", value)
        self.t_val.grid(row=4, column=0, columnspan=2, sticky="ew", pady=(2, 14))
        bar = tk.Frame(frm, bg=C["panel"])
        bar.grid(row=5, column=0, columnspan=2, sticky="e")
        ttk.Button(bar, text="Cancel", style="Ghost.TButton", command=self.destroy).pack(side="right", padx=(8, 0))
        ttk.Button(bar, text="Save", style="Accent.TButton", command=self.ok).pack(side="right")
        self.bind("<Escape>", lambda e: self.destroy())
        self.update_idletasks()
        x = master.winfo_rootx() + (master.winfo_width() - self.winfo_width()) // 2
        y = master.winfo_rooty() + (master.winfo_height() - self.winfo_height()) // 3
        self.geometry(f"+{max(x, 0)}+{max(y, 0)}")
        self.grab_set()
        (self.t_val if not tag_editable else self.e_tag).focus_set()
        self.wait_window(self)

    def ok(self):
        tag = self.e_tag.get().strip().lstrip("-")
        if not tag:
            messagebox.showwarning(APP_NAME, "Tag name is required.", parent=self)
            return
        self.result = (tag, self.t_val.get("1.0", "end-1c"))
        self.destroy()


class SettingsDialog(tk.Toplevel):
    def __init__(self, app):
        super().__init__(app)
        self.app = app
        self.title("Settings")
        self.configure(bg=C["panel"])
        self.transient(app)
        self.resizable(False, False)
        f = tk.Frame(self, bg=C["panel"], padx=22, pady=18)
        f.pack()
        tk.Label(f, text="Settings", font=("Segoe UI", 14, "bold"), bg=C["panel"], fg=C["text"]
                 ).pack(anchor="w", pady=(0, 12))
        self.backup = tk.BooleanVar(value=app.db.get("keep_backup", "0") == "1")
        self.raw = tk.BooleanVar(value=app.db.get("raw_values", "0") == "1")
        ttk.Checkbutton(f, text="Keep a backup copy (file_original) before writing", variable=self.backup
                        ).pack(anchor="w", pady=2)
        ttk.Checkbutton(f, text="Show raw / numeric values (like ExifTool -n)", variable=self.raw
                        ).pack(anchor="w", pady=2)
        tk.Label(f, text="Supported formats (built-in engine, no ExifTool needed)", bg=C["panel"], fg=C["muted"],
                 font=FONT_S).pack(anchor="w", pady=(14, 4))
        tk.Label(f, text=CAPS_TEXT, justify="left", bg=C["card"], fg=C["accent2"], font=("Consolas", 9),
                 padx=12, pady=10).pack(fill="x")
        tk.Label(f, text=f"Database: {DB_FILE}", bg=C["panel"], fg=C["muted"], font=FONT_S
                 ).pack(anchor="w", pady=(10, 14))
        bar = tk.Frame(f, bg=C["panel"])
        bar.pack(fill="x")
        ttk.Button(bar, text="Cancel", style="Ghost.TButton", command=self.destroy).pack(side="right", padx=(8, 0))
        ttk.Button(bar, text="Save", style="Accent.TButton", command=self.save).pack(side="right")
        self.grab_set()

    def save(self):
        self.app.db.set("keep_backup", "1" if self.backup.get() else "0")
        self.app.db.set("raw_values", "1" if self.raw.get() else "0")
        self.destroy()
        if self.app.current:
            self.app.load_metadata(self.app.current, force=True)


class App(tk.Tk):
    def __init__(self):
        super().__init__()
        self.title(f"{APP_NAME}  -  Metadata Manager")
        self.geometry("1360x820")
        self.minsize(1080, 660)
        self.configure(bg=C["bg"])
        self.db = DB()
        self.et = MetaEngine()
        self.cache = {}
        self.current = None
        self.bgq = queue.Queue()
        self.busy = 0
        self.preview_img = None
        self.sort_state = {}
        self.setup_style()
        self.build_ui()
        self.fill_sidebar()
        self.after(100, self.poll)

    # ------------------------------------------------------------ style --
    def setup_style(self):
        s = ttk.Style(self)
        s.theme_use("clam")
        s.configure(".", background=C["panel"], foreground=C["text"], font=FONT, fieldbackground=C["card"],
                    bordercolor=C["border"], lightcolor=C["panel"], darkcolor=C["panel"], troughcolor=C["card"])
        s.configure("TFrame", background=C["panel"])
        s.configure("TLabel", background=C["panel"], foreground=C["text"])
        s.configure("TEntry", fieldbackground=C["card"], foreground=C["text"], insertcolor=C["text"], padding=6)
        s.map("TEntry", bordercolor=[("focus", C["accent"])])
        s.configure("TCombobox", fieldbackground=C["card"], foreground=C["text"], background=C["card2"],
                    arrowcolor=C["text"], padding=5)
        s.map("TCombobox", fieldbackground=[("readonly", C["card"])], foreground=[("readonly", C["text"])])
        self.option_add("*TCombobox*Listbox.background", C["card"])
        self.option_add("*TCombobox*Listbox.foreground", C["text"])
        self.option_add("*TCombobox*Listbox.selectBackground", C["accent"])
        s.configure("TCheckbutton", background=C["panel"], foreground=C["text"])
        s.map("TCheckbutton", background=[("active", C["panel"])])
        for name, bg, fg, hov in (("TButton", C["card2"], C["text"], C["border"]),
                                  ("Accent.TButton", C["accent"], "#ffffff", "#9279ff"),
                                  ("Ghost.TButton", C["card"], C["muted"], C["card2"]),
                                  ("Danger.TButton", "#4a1f2c", C["err"], "#6b2a3d")):
            s.configure(name, background=bg, foreground=fg, padding=(14, 7), borderwidth=0, focusthickness=0,
                        font=FONT_B)
            s.map(name, background=[("active", hov), ("pressed", hov)])
        s.configure("Treeview", background=C["row_a"], fieldbackground=C["row_a"], foreground=C["text"],
                    rowheight=28, borderwidth=0, font=FONT)
        s.map("Treeview", background=[("selected", C["accent"])], foreground=[("selected", "#ffffff")])
        s.configure("Treeview.Heading", background=C["card2"], foreground=C["muted"], font=FONT_B, relief="flat",
                    padding=7)
        s.map("Treeview.Heading", background=[("active", C["border"])])
        s.configure("TNotebook", background=C["bg"], borderwidth=0, tabmargins=(0, 0, 0, 0))
        s.configure("TNotebook.Tab", background=C["panel"], foreground=C["muted"], padding=(20, 10), font=FONT_B,
                    borderwidth=0)
        s.map("TNotebook.Tab", background=[("selected", C["card"])], foreground=[("selected", C["accent2"])])
        s.configure("Vertical.TScrollbar", background=C["card2"], troughcolor=C["panel"], arrowcolor=C["muted"],
                    borderwidth=0)
        s.configure("Horizontal.TProgressbar", background=C["accent2"], troughcolor=C["card"], borderwidth=0)

    # -------------------------------------------------------------- UI --
    def build_ui(self):
        hdr = tk.Frame(self, bg=C["bg"], padx=22, pady=14)
        hdr.pack(fill="x")
        logo = tk.Canvas(hdr, width=46, height=46, bg=C["bg"], highlightthickness=0)
        logo.create_oval(2, 2, 44, 44, fill=C["accent"], outline="")
        logo.create_oval(13, 13, 33, 33, fill=C["bg"], outline="")
        logo.create_oval(19, 19, 27, 27, fill=C["accent2"], outline="")
        logo.pack(side="left")
        tt = tk.Frame(hdr, bg=C["bg"])
        tt.pack(side="left", padx=12)
        tk.Label(tt, text=APP_NAME, font=FONT_H, bg=C["bg"], fg=C["text"]).pack(anchor="w")
        tk.Label(tt, text="Pure-Python metadata engine  ·  no ExifTool, no browser  ·  SQLite powered",
                 font=FONT_S, bg=C["bg"], fg=C["ok"]).pack(anchor="w")
        btns = tk.Frame(hdr, bg=C["bg"])
        btns.pack(side="right")
        ttk.Button(btns, text="＋ Add Files", style="Accent.TButton", command=self.add_files).pack(side="left", padx=4)
        ttk.Button(btns, text="📁 Add Folder", command=self.add_folder).pack(side="left", padx=4)
        ttk.Button(btns, text="⟳ Refresh",
                   command=lambda: self.current and self.load_metadata(self.current, True)).pack(side="left", padx=4)
        ttk.Button(btns, text="⇩ Export", command=self.export).pack(side="left", padx=4)
        ttk.Button(btns, text="⚙ Settings", style="Ghost.TButton",
                   command=lambda: SettingsDialog(self)).pack(side="left", padx=4)

        body = ttk.PanedWindow(self, orient="horizontal")
        body.pack(fill="both", expand=True, padx=18, pady=(0, 6))
        side = tk.Frame(body, bg=C["panel"])
        body.add(side, weight=1)
        tk.Label(side, text="FILES", font=FONT_B, bg=C["panel"], fg=C["muted"]).pack(anchor="w", padx=14, pady=(14, 4))
        self.side_search = tk.StringVar()
        self.side_search.trace_add("write", lambda *a: self.fill_sidebar())
        ttk.Entry(side, textvariable=self.side_search).pack(fill="x", padx=12, pady=(0, 8))
        wrap = tk.Frame(side, bg=C["panel"])
        wrap.pack(fill="both", expand=True, padx=8)
        self.files_tv = ttk.Treeview(wrap, columns=("type", "size"), selectmode="extended")
        self.files_tv.heading("#0", text="Name", anchor="w")
        self.files_tv.heading("type", text="Type")
        self.files_tv.heading("size", text="Size")
        self.files_tv.column("#0", width=210, anchor="w")
        self.files_tv.column("type", width=55, anchor="center")
        self.files_tv.column("size", width=70, anchor="e")
        sb = ttk.Scrollbar(wrap, orient="vertical", command=self.files_tv.yview)
        self.files_tv.configure(yscrollcommand=sb.set)
        self.files_tv.pack(side="left", fill="both", expand=True)
        sb.pack(side="right", fill="y")
        self.files_tv.bind("<<TreeviewSelect>>", self.on_select_file)
        self.files_tv.bind("<Delete>", lambda e: self.remove_selected())
        sbar = tk.Frame(side, bg=C["panel"])
        sbar.pack(fill="x", padx=12, pady=10)
        ttk.Button(sbar, text="Remove selected", style="Ghost.TButton", command=self.remove_selected).pack(side="left")
        self.lbl_count = tk.Label(sbar, text="", bg=C["panel"], fg=C["muted"], font=FONT_S)
        self.lbl_count.pack(side="right")

        main = tk.Frame(body, bg=C["bg"])
        body.add(main, weight=4)
        self.nb = ttk.Notebook(main)
        self.nb.pack(fill="both", expand=True, padx=(10, 0))
        self.tab_meta, self.tab_batch, self.tab_log, self.tab_snap = (tk.Frame(self.nb, bg=C["card"]) for _ in range(4))
        self.nb.add(self.tab_meta, text="  Metadata  ")
        self.nb.add(self.tab_batch, text="  Batch Edit  ")
        self.nb.add(self.tab_log, text="  Audit Log  ")
        self.nb.add(self.tab_snap, text="  Snapshots  ")
        self.build_meta_tab()
        self.build_batch_tab()
        self.build_log_tab()
        self.build_snap_tab()
        self.nb.bind("<<NotebookTabChanged>>", self.on_tab_change)

        st = tk.Frame(self, bg=C["panel"], padx=14, pady=6)
        st.pack(fill="x", side="bottom")
        self.status = tk.Label(st, text="Ready - add files to begin", bg=C["panel"], fg=C["muted"], font=FONT_S)
        self.status.pack(side="left")
        self.pb = ttk.Progressbar(st, mode="indeterminate", length=140)
        self.pb.pack(side="right")
        self.lbl_stats = tk.Label(st, text="", bg=C["panel"], fg=C["muted"], font=FONT_S)
        self.lbl_stats.pack(side="right", padx=14)
        self.update_stats()

    def build_meta_tab(self):
        t = self.tab_meta
        card = tk.Frame(t, bg=C["card2"], padx=16, pady=14)
        card.pack(fill="x", padx=14, pady=14)
        self.cv_prev = tk.Canvas(card, width=120, height=120, bg=C["card"], highlightthickness=1,
                                 highlightbackground=C["border"])
        self.cv_prev.pack(side="left")
        self.prev_placeholder("Select a file")
        info = tk.Frame(card, bg=C["card2"])
        info.pack(side="left", fill="x", expand=True, padx=18)
        self.lbl_name = tk.Label(info, text="No file selected", bg=C["card2"], fg=C["text"],
                                 font=("Segoe UI", 14, "bold"), anchor="w")
        self.lbl_name.pack(fill="x")
        self.lbl_path = tk.Label(info, text="", bg=C["card2"], fg=C["muted"], font=FONT_S, anchor="w")
        self.lbl_path.pack(fill="x", pady=(0, 8))
        chips = tk.Frame(info, bg=C["card2"])
        chips.pack(fill="x")
        self.chips = {}
        for key in ("Size", "Type", "Dimensions", "Modified", "Tags"):
            box = tk.Frame(chips, bg=C["card"], padx=12, pady=6)
            box.pack(side="left", padx=(0, 8))
            tk.Label(box, text=key.upper(), bg=C["card"], fg=C["muted"], font=("Segoe UI", 8, "bold")).pack(anchor="w")
            lab = tk.Label(box, text="-", bg=C["card"], fg=C["accent2"], font=FONT_B)
            lab.pack(anchor="w")
            self.chips[key] = lab

        bar = tk.Frame(t, bg=C["card"])
        bar.pack(fill="x", padx=14)
        self.meta_filter = tk.StringVar()
        self.meta_filter.trace_add("write", lambda *a: self.fill_meta())
        ttk.Entry(bar, textvariable=self.meta_filter, width=30).pack(side="left")
        tk.Label(bar, text="🔍 filter", bg=C["card"], fg=C["muted"], font=FONT_S).pack(side="left", padx=8)
        self.group_var = tk.StringVar(value="All groups")
        self.group_cb = ttk.Combobox(bar, textvariable=self.group_var, state="readonly", width=16,
                                     values=["All groups"])
        self.group_cb.pack(side="left", padx=6)
        self.group_cb.bind("<<ComboboxSelected>>", lambda e: self.fill_meta())
        ttk.Button(bar, text="Strip ALL", style="Danger.TButton", command=self.strip_current).pack(side="right")
        ttk.Button(bar, text="Delete", style="Ghost.TButton", command=self.delete_tag).pack(side="right", padx=6)
        ttk.Button(bar, text="Edit", command=self.edit_tag).pack(side="right")
        ttk.Button(bar, text="＋ Add tag", style="Accent.TButton", command=self.add_tag).pack(side="right", padx=6)

        wrap = tk.Frame(t, bg=C["card"])
        wrap.pack(fill="both", expand=True, padx=14, pady=12)
        self.meta_tv = ttk.Treeview(wrap, columns=("group", "tag", "value"), show="headings", selectmode="browse")
        for c, w, txt in (("group", 110, "Group"), ("tag", 220, "Tag"), ("value", 520, "Value")):
            self.meta_tv.heading(c, text=txt, anchor="w", command=lambda c=c: self.sort_meta(c))
            self.meta_tv.column(c, width=w, anchor="w")
        self.meta_tv.tag_configure("a", background=C["row_a"])
        self.meta_tv.tag_configure("b", background=C["row_b"])
        sy = ttk.Scrollbar(wrap, orient="vertical", command=self.meta_tv.yview)
        self.meta_tv.configure(yscrollcommand=sy.set)
        self.meta_tv.pack(side="left", fill="both", expand=True)
        sy.pack(side="right", fill="y")
        self.meta_tv.bind("<Double-1>", lambda e: self.edit_tag())
        self.meta_tv.bind("<Return>", lambda e: self.edit_tag())
        self.meta_tv.bind("<Control-c>", self.copy_value)
        self.meta_menu = tk.Menu(self, tearoff=0, bg=C["card"], fg=C["text"], activebackground=C["accent"], bd=0)
        self.meta_menu.add_command(label="Edit value", command=self.edit_tag)
        self.meta_menu.add_command(label="Copy value", command=self.copy_value)
        self.meta_menu.add_command(label="Delete tag", command=self.delete_tag)
        self.meta_tv.bind("<Button-3>", self.popup_menu)
        self.meta_tv.bind("<Button-2>", self.popup_menu)

    def popup_menu(self, e):
        iid = self.meta_tv.identify_row(e.y)
        if iid:
            self.meta_tv.selection_set(iid)
            self.meta_menu.tk_popup(e.x_root, e.y_root)

    def copy_value(self, e=None):
        sel = self.meta_tv.selection()
        if sel:
            full = sel[0]
            for g, t, v, f in self.cache.get(self.current, []):
                if f == full:
                    self.clipboard_clear()
                    self.clipboard_append(v)
                    self.set_status("Value copied to clipboard")
                    return

    def prev_placeholder(self, text, icon="🗂️"):
        self.cv_prev.delete("all")
        self.cv_prev.create_text(60, 48, text=icon, font=("Segoe UI Emoji", 34), fill=C["accent2"])
        self.cv_prev.create_text(60, 100, text=text, fill=C["muted"], font=FONT_S)

    def show_preview(self, path):
        ext = os.path.splitext(path)[1].lower()
        mime = mimetypes.guess_type(path)[0] or ""
        kind = mime.split("/")[0]
        icon = TYPE_ICONS.get(kind, "📄")
        if "pdf" in mime:
            icon = TYPE_ICONS["pdf"]
        img = None
        try:
            if HAS_PIL and kind == "image":
                im = Image.open(path)
                im.thumbnail((116, 116))
                img = ImageTk.PhotoImage(im)
            elif ext in (".png", ".gif"):
                img = tk.PhotoImage(file=path)
                f = max(img.width() // 116, img.height() // 116, 1)
                if f > 1:
                    img = img.subsample(f, f)
        except Exception:
            img = None
        if img:
            self.preview_img = img
            self.cv_prev.delete("all")
            self.cv_prev.create_image(60, 60, image=img)
        else:
            self.prev_placeholder(ext.upper().lstrip(".") or "FILE", icon)

    def build_batch_tab(self):
        t = self.tab_batch
        tk.Label(t, text="Batch edit", font=("Segoe UI", 15, "bold"), bg=C["card"], fg=C["text"]
                 ).pack(anchor="w", padx=18, pady=(16, 0))
        tk.Label(t, text="Apply one tag change to the selected files (or all files in the list). "
                         "Files whose format doesn't support the tag are reported and skipped.",
                 bg=C["card"], fg=C["muted"], font=FONT_S).pack(anchor="w", padx=18, pady=(0, 12))
        form = tk.Frame(t, bg=C["card2"], padx=18, pady=16)
        form.pack(fill="x", padx=18)
        for i, txt in enumerate(("Tag", "Value", "Action")):
            tk.Label(form, text=txt, bg=C["card2"], fg=C["muted"], font=FONT_S).grid(
                row=0, column=i, sticky="w", padx=(0 if i == 0 else 10, 0))
        self.b_tag = tk.StringVar(value="EXIF:Artist")
        self.b_val = tk.StringVar()
        self.b_act = tk.StringVar(value="Set value")
        ttk.Entry(form, textvariable=self.b_tag, width=26).grid(row=1, column=0, sticky="ew")
        ttk.Entry(form, textvariable=self.b_val, width=40).grid(row=1, column=1, padx=10)
        ttk.Combobox(form, textvariable=self.b_act, state="readonly", width=14,
                     values=["Set value", "Delete tag"]).grid(row=1, column=2, padx=10)
        self.b_scope = tk.StringVar(value="selected")
        r = tk.Frame(form, bg=C["card2"])
        r.grid(row=2, column=0, columnspan=3, sticky="w", pady=(12, 0))
        for txt, val in (("Selected files", "selected"), ("All files in list", "all")):
            tk.Radiobutton(r, text=txt, value=val, variable=self.b_scope, bg=C["card2"], fg=C["text"],
                           selectcolor=C["card"], activebackground=C["card2"], activeforeground=C["text"],
                           font=FONT).pack(side="left", padx=(0, 16))
        ttk.Button(form, text="▶ Run batch", style="Accent.TButton", command=self.run_batch).grid(row=1, column=3, padx=6)
        self.batch_log = tk.Text(t, bg=C["bg"], fg=C["text"], font=MONO, relief="flat", padx=12, pady=10, height=10,
                                 state="disabled")
        self.batch_log.pack(fill="both", expand=True, padx=18, pady=16)
        self.batch_log.tag_configure("ok", foreground=C["ok"])
        self.batch_log.tag_configure("err", foreground=C["err"])
        self.batch_log.tag_configure("info", foreground=C["accent2"])

    def blog(self, text, tag="info"):
        self.batch_log.configure(state="normal")
        self.batch_log.insert("end", text + "\n", tag)
        self.batch_log.see("end")
        self.batch_log.configure(state="disabled")

    def build_log_tab(self):
        t = self.tab_log
        bar = tk.Frame(t, bg=C["card"])
        bar.pack(fill="x", padx=14, pady=14)
        tk.Label(bar, text="Audit log - every write is recorded in SQLite", bg=C["card"], fg=C["text"],
                 font=("Segoe UI", 13, "bold")).pack(side="left")
        ttk.Button(bar, text="↶ Revert selected", style="Accent.TButton", command=self.revert_edit).pack(side="right")
        ttk.Button(bar, text="⟳", style="Ghost.TButton", command=self.fill_log).pack(side="right", padx=6)
        wrap = tk.Frame(t, bg=C["card"])
        wrap.pack(fill="both", expand=True, padx=14, pady=(0, 14))
        cols = ("id", "at", "file", "tag", "old", "new", "action", "status")
        self.log_tv = ttk.Treeview(wrap, columns=cols, show="headings")
        for c, w in zip(cols, (50, 140, 170, 150, 150, 150, 70, 80)):
            self.log_tv.heading(c, text=c.title(), anchor="w")
            self.log_tv.column(c, width=w, anchor="w")
        self.log_tv.tag_configure("ok", foreground=C["ok"])
        self.log_tv.tag_configure("fail", foreground=C["err"])
        self.log_tv.tag_configure("rev", foreground=C["muted"])
        sy = ttk.Scrollbar(wrap, orient="vertical", command=self.log_tv.yview)
        self.log_tv.configure(yscrollcommand=sy.set)
        self.log_tv.pack(side="left", fill="both", expand=True)
        sy.pack(side="right", fill="y")

    def fill_log(self):
        self.log_tv.delete(*self.log_tv.get_children())
        for (eid, at, path, tag, old, new, action, status, rev) in self.db.edits():
            tg = "rev" if rev else ("ok" if status == "ok" else "fail")
            self.log_tv.insert("", "end", iid=str(eid), tags=(tg,), values=(
                eid, at, os.path.basename(path), tag, old if old is not None else "∅",
                new if new is not None else "∅", action, "reverted" if rev else status))

    def build_snap_tab(self):
        t = self.tab_snap
        bar = tk.Frame(t, bg=C["card"])
        bar.pack(fill="x", padx=14, pady=14)
        tk.Label(bar, text="Snapshots of the selected file", bg=C["card"], fg=C["text"],
                 font=("Segoe UI", 13, "bold")).pack(side="left")
        ttk.Button(bar, text="Compare with current", style="Accent.TButton", command=self.diff_snapshot).pack(side="right")
        wrap = tk.Frame(t, bg=C["card"])
        wrap.pack(fill="x", padx=14)
        self.snap_tv = ttk.Treeview(wrap, columns=("id", "at", "n"), show="headings", height=6)
        for c, w, tx in (("id", 60, "ID"), ("at", 200, "Scanned at"), ("n", 100, "Tags")):
            self.snap_tv.heading(c, text=tx, anchor="w")
            self.snap_tv.column(c, width=w, anchor="w")
        self.snap_tv.pack(fill="x")
        self.diff_txt = tk.Text(t, bg=C["bg"], fg=C["text"], font=MONO, relief="flat", padx=12, pady=10,
                                state="disabled")
        self.diff_txt.pack(fill="both", expand=True, padx=14, pady=14)
        for n, col in (("add", C["ok"]), ("del", C["err"]), ("chg", C["warn"]), ("hdr", C["accent2"])):
            self.diff_txt.tag_configure(n, foreground=col)

    def fill_snaps(self):
        self.snap_tv.delete(*self.snap_tv.get_children())
        if self.current:
            for sid, at, n in self.db.snapshots(self.current):
                self.snap_tv.insert("", "end", iid=str(sid), values=(sid, at, n))

    def diff_snapshot(self):
        sel = self.snap_tv.selection()
        if not sel or not self.current:
            messagebox.showinfo(APP_NAME, "Select a snapshot first.")
            return
        old = self.db.snapshot_data(int(sel[0]))
        cur = {r[3]: r[2] for r in self.cache.get(self.current, [])}
        self.diff_txt.configure(state="normal")
        self.diff_txt.delete("1.0", "end")
        self.diff_txt.insert("end", f"Snapshot #{sel[0]}  →  current state\n\n", "hdr")
        n = 0
        for k in sorted(set(old) | set(cur)):
            if k.startswith("File:FileAccessDate"):
                continue
            if k not in old:
                self.diff_txt.insert("end", f"+ {k} = {cur[k]}\n", "add")
            elif k not in cur:
                self.diff_txt.insert("end", f"- {k} = {old[k]}\n", "del")
            elif old[k] != cur[k]:
                self.diff_txt.insert("end", f"~ {k}:  {old[k]}  →  {cur[k]}\n", "chg")
            else:
                continue
            n += 1
        if not n:
            self.diff_txt.insert("end", "No differences.\n", "hdr")
        self.diff_txt.configure(state="disabled")

    def on_tab_change(self, e=None):
        i = self.nb.index(self.nb.select())
        if i == 2:
            self.fill_log()
        elif i == 3:
            self.fill_snaps()

    # ------------------------------------------------------- background --
    def run_bg(self, fn, cb=None, err=None, msg="Working…"):
        self.busy += 1
        self.pb.start(12)
        self.set_status(msg)

        def worker():
            try:
                self.bgq.put((cb, fn(), None, err))
            except Exception as ex:
                self.bgq.put((cb, None, ex, err))
        threading.Thread(target=worker, daemon=True).start()

    def poll(self):
        try:
            while True:
                cb, res, ex, errcb = self.bgq.get_nowait()
                self.busy = max(0, self.busy - 1)
                if self.busy == 0:
                    self.pb.stop()
                if ex is not None:
                    self.set_status(f"Error: {ex}", C["err"])
                    (errcb or (lambda x: messagebox.showerror(APP_NAME, str(x))))(ex)
                elif cb:
                    cb(res)
        except queue.Empty:
            pass
        self.after(80, self.poll)

    def set_status(self, text, color=None):
        self.status.configure(text=text, fg=color or C["muted"])

    def update_stats(self):
        f, e, s = self.db.stats()
        self.lbl_stats.configure(text=f"{f} files · {s} snapshots · {e} edits logged")

    # ------------------------------------------------------------ files --
    def fill_sidebar(self):
        flt = self.side_search.get().lower().strip()
        self.files_tv.delete(*self.files_tv.get_children())
        n = 0
        for path, ext, size in self.db.all_files():
            if flt and flt not in os.path.basename(path).lower():
                continue
            if not os.path.exists(path):
                continue
            self.files_tv.insert("", "end", iid=path, text="  " + os.path.basename(path),
                                 values=(ext.upper() or "-", human_size(size)))
            n += 1
        self.lbl_count.configure(text=f"{n} file(s)")
        self.update_stats()

    def add_files(self):
        paths = filedialog.askopenfilenames(title="Select files")
        for p in paths:
            self.db.add_file(p)
        self.fill_sidebar()
        if paths:
            self.files_tv.selection_set(paths[0])
            self.files_tv.see(paths[0])

    def add_folder(self):
        d = filedialog.askdirectory(title="Select folder")
        if not d:
            return
        recurse = messagebox.askyesno(APP_NAME, "Include sub-folders?")

        def scan():
            found = []
            if recurse:
                for root, _, fs in os.walk(d):
                    found += [os.path.join(root, f) for f in fs if not f.endswith(("_original", ".tmp"))]
            else:
                found = [os.path.join(d, f) for f in os.listdir(d)
                         if os.path.isfile(os.path.join(d, f)) and not f.endswith(("_original", ".tmp"))]
            for p in found:
                self.db.add_file(p)
            return len(found)

        self.run_bg(scan, lambda n: (self.fill_sidebar(), self.set_status(f"Added {n} files", C["ok"])),
                    msg="Scanning folder…")

    def remove_selected(self):
        for iid in self.files_tv.selection():
            self.db.remove_file(iid)
            self.cache.pop(iid, None)
        self.fill_sidebar()

    def on_select_file(self, e=None):
        sel = self.files_tv.selection()
        if sel and sel[0] != self.current:
            self.load_metadata(sel[0])

    # --------------------------------------------------------- metadata --
    def load_metadata(self, path, force=False):
        self.current = path
        self.lbl_name.configure(text=os.path.basename(path))
        self.lbl_path.configure(text=path)
        self.show_preview(path)
        if path in self.cache and not force:
            self.after_read(path, self.cache[path], snapshot=False)
            return
        raw = self.db.get("raw_values", "0") == "1"
        self.run_bg(lambda: self.et.read(path, raw), lambda rows: self.after_read(path, rows, True),
                    msg=f"Reading {os.path.basename(path)}…")

    def after_read(self, path, rows, snapshot=True):
        self.cache[path] = rows
        if snapshot:
            self.db.add_snapshot(path, rows)
            self.db.mark_scanned(path, len(rows))
        if path != self.current:
            return
        groups = sorted({r[0] for r in rows})
        self.group_cb.configure(values=["All groups"] + groups)
        if self.group_var.get() not in groups:
            self.group_var.set("All groups")
        self.fill_meta()
        d = {r[3]: r[2] for r in rows}
        self.chips["Size"].configure(text=human_size(os.path.getsize(path)) if os.path.exists(path) else "-")
        self.chips["Type"].configure(text=d.get("File:FileType", "-"))
        self.chips["Dimensions"].configure(text=d.get("Composite:ImageSize", "-"))
        self.chips["Modified"].configure(text=d.get("File:FileModifyDate", "-")[:19])
        self.chips["Tags"].configure(text=str(len(rows)))
        self.set_status(f"Loaded {len(rows)} tags", C["ok"])
        self.update_stats()
        if self.nb.index(self.nb.select()) == 3:
            self.fill_snaps()

    def fill_meta(self):
        self.meta_tv.delete(*self.meta_tv.get_children())
        if not self.current:
            return
        flt = self.meta_filter.get().lower().strip()
        grp = self.group_var.get()
        i = 0
        for g, t, v, full in self.cache.get(self.current, []):
            if grp != "All groups" and g != grp:
                continue
            if flt and flt not in t.lower() and flt not in v.lower() and flt not in g.lower():
                continue
            disp = v if len(v) < 400 else v[:400] + " …"
            self.meta_tv.insert("", "end", iid=full, tags=("a" if i % 2 else "b",),
                                values=(g, t, disp.replace("\n", " ⏎ ")))
            i += 1

    def sort_meta(self, col):
        rev = self.sort_state.get(col, False)
        items = sorted(((self.meta_tv.set(k, col).lower(), k) for k in self.meta_tv.get_children()), reverse=rev)
        for idx, (_, k) in enumerate(items):
            self.meta_tv.move(k, "", idx)
            self.meta_tv.item(k, tags=("a" if idx % 2 else "b",))
        self.sort_state[col] = not rev

    def selected_tag(self):
        sel = self.meta_tv.selection()
        return sel[0] if sel else None

    def old_value(self, full):
        for g, t, v, f in self.cache.get(self.current, []):
            if f == full:
                return v
        return None

    def need_file(self):
        if not self.current:
            messagebox.showinfo(APP_NAME, "Select a file first.")
            return False
        return True

    # -------------------------------------------------------- write ops --
    def keep_backup(self):
        return self.db.get("keep_backup", "0") == "1"

    def do_write(self, path, changes, action):
        olds = {tag: self.lookup_old(path, tag) for tag in changes}
        kb = self.keep_backup()

        def done(res):
            ok, msg = res
            for tag, new in changes.items():
                self.db.log_edit(path, tag, olds[tag], new, action, "ok" if ok else "fail")
            if ok:
                self.set_status("Metadata written successfully", C["ok"])
                self.cache.pop(path, None)
                if path == self.current:
                    self.load_metadata(path, force=True)
            else:
                self.set_status("Write failed", C["err"])
                messagebox.showerror(APP_NAME, "Could not write this change:\n\n" + msg[:700])
            self.update_stats()

        self.run_bg(lambda: self.et.write(path, changes, kb), done, msg="Writing metadata…")

    def lookup_old(self, path, tag):
        for g, t, v, f in self.cache.get(path, []):
            if f == tag or (":" not in tag and t == tag):
                return v
        return None

    def edit_tag(self):
        if not self.need_file():
            return
        full = self.selected_tag()
        if not full:
            messagebox.showinfo(APP_NAME, "Select a tag to edit.")
            return
        d = TagDialog(self, "Edit tag", full, self.old_value(full) or "", tag_editable=False)
        if d.result and d.result[1] != self.old_value(full):
            self.do_write(self.current, {d.result[0]: d.result[1]}, "edit")

    def add_tag(self):
        if not self.need_file():
            return
        d = TagDialog(self, "Add tag", "EXIF:Artist", "")
        if d.result:
            self.do_write(self.current, {d.result[0]: d.result[1]}, "add")

    def delete_tag(self):
        if not self.need_file():
            return
        full = self.selected_tag()
        if not full:
            messagebox.showinfo(APP_NAME, "Select a tag to delete.")
            return
        if messagebox.askyesno(APP_NAME, f"Delete tag  {full} ?"):
            self.do_write(self.current, {full: None}, "delete")

    def strip_current(self):
        if not self.need_file():
            return
        if not messagebox.askyesno(APP_NAME, "Remove ALL writable metadata from this file?\n\n"
                                             "A snapshot of the current tags is kept in the database."):
            return
        path, kb = self.current, self.keep_backup()

        def done(res):
            ok, msg = res
            self.db.log_edit(path, "ALL", f"{len(self.cache.get(path, []))} tags", None, "strip",
                             "ok" if ok else "fail")
            if ok:
                self.cache.pop(path, None)
                self.load_metadata(path, force=True)
                self.set_status("All metadata stripped", C["ok"])
            else:
                messagebox.showerror(APP_NAME, msg[:700])
            self.update_stats()

        self.run_bg(lambda: self.et.strip_all(path, kb), done, msg="Stripping metadata…")

    # ------------------------------------------------------------ batch --
    def run_batch(self):
        tag = self.b_tag.get().strip().lstrip("-")
        if not tag:
            messagebox.showwarning(APP_NAME, "Enter a tag name.")
            return
        delete = self.b_act.get() == "Delete tag"
        val = None if delete else self.b_val.get()
        files = list(self.files_tv.selection()) if self.b_scope.get() == "selected" \
            else list(self.files_tv.get_children())
        if not files:
            messagebox.showinfo(APP_NAME, "No files to process.")
            return
        if not messagebox.askyesno(APP_NAME, f"{'Delete' if delete else 'Set'} {tag} on {len(files)} file(s)?"):
            return
        kb = self.keep_backup()
        self.blog(f"── Batch started: {tag} on {len(files)} file(s)", "info")

        def work():
            out = []
            for p in files:
                old = self.lookup_old(p, tag)
                ok, msg = self.et.write(p, {tag: val}, kb)
                self.db.log_edit(p, tag, old, val, "batch", "ok" if ok else "fail")
                out.append((p, ok, msg))
            return out

        def done(res):
            good = 0
            for p, ok, msg in res:
                if ok:
                    good += 1
                    self.blog(f"✔ {os.path.basename(p)}", "ok")
                else:
                    self.blog(f"✘ {os.path.basename(p)}  -  {msg.splitlines()[0] if msg else ''}", "err")
                self.cache.pop(p, None)
            self.blog(f"── Done: {good}/{len(res)} succeeded\n", "info")
            self.set_status(f"Batch finished: {good}/{len(res)} OK", C["ok"] if good == len(res) else C["warn"])
            if self.current:
                self.load_metadata(self.current, force=True)
            self.update_stats()

        self.run_bg(work, done, msg="Running batch…")

    # ----------------------------------------------------------- revert --
    def revert_edit(self):
        sel = self.log_tv.selection()
        if not sel:
            messagebox.showinfo(APP_NAME, "Select a log entry to revert.")
            return
        eid, at, path, tag, old, new, action, status, rev = self.db.edit(int(sel[0]))
        if status != "ok" or rev or action == "strip":
            messagebox.showinfo(APP_NAME, "This entry cannot be reverted (failed, already reverted, or strip).")
            return
        if not os.path.exists(path):
            messagebox.showerror(APP_NAME, "File no longer exists.")
            return
        what = "delete the tag" if old is None else f"restore the value to:\n{old[:200]}"
        if not messagebox.askyesno(APP_NAME, f"Revert edit #{eid} on {os.path.basename(path)}?\n\nThis will {what}"):
            return
        kb = self.keep_backup()

        def done(res):
            ok, msg = res
            self.db.log_edit(path, tag, new, old, "revert", "ok" if ok else "fail")
            if ok:
                self.db.mark_reverted(eid)
                self.cache.pop(path, None)
                if path == self.current:
                    self.load_metadata(path, force=True)
                self.set_status("Edit reverted", C["ok"])
            else:
                messagebox.showerror(APP_NAME, msg[:700])
            self.fill_log()

        self.run_bg(lambda: self.et.write(path, {tag: old}, kb), done, msg="Reverting…")

    # ----------------------------------------------------------- export --
    def export(self):
        if not self.need_file():
            return
        rows = self.cache.get(self.current, [])
        if not rows:
            return
        base = os.path.splitext(os.path.basename(self.current))[0] + "_metadata"
        p = filedialog.asksaveasfilename(defaultextension=".json", initialfile=base,
                                         filetypes=[("JSON", "*.json"), ("CSV", "*.csv"), ("Text", "*.txt")])
        if not p:
            return
        try:
            if p.lower().endswith(".csv"):
                with open(p, "w", newline="", encoding="utf-8-sig") as f:
                    w = csv.writer(f)
                    w.writerow(["Group", "Tag", "Value"])
                    for g, t, v, _ in rows:
                        w.writerow([g, t, v])
            elif p.lower().endswith(".txt"):
                with open(p, "w", encoding="utf-8") as f:
                    for g, t, v, _ in rows:
                        f.write(f"[{g}] {t}: {v}\n")
            else:
                with open(p, "w", encoding="utf-8") as f:
                    json.dump({"file": self.current, "exported": now(), "metadata": {r[3]: r[2] for r in rows}},
                              f, indent=2, ensure_ascii=False)
            self.set_status(f"Exported to {p}", C["ok"])
        except Exception as ex:
            messagebox.showerror(APP_NAME, str(ex))


if __name__ == "__main__":
    try:
        from ctypes import windll  # sharper text on Windows
        windll.shcore.SetProcessDpiAwareness(1)
    except Exception:
        pass
    App().mainloop()
