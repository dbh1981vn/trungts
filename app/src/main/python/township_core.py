from __future__ import annotations

"""
Township Simple Save Editor + Direct FetchCity - single-file edition

Requirements:
    pip install lz4 requests cryptography

Default target:
    ADB      : D:\\LDPlayer\\LDPlayer9\\adb.exe
    Device   : emulator-5556
    Package  : com.playrix.township.vn
    Save     : /data/data/com.playrix.township.vn/saves/mGameInfo.xml

The codec below is ported from the verified Android MGameInfoCodec source used by
Township Tool v0.2.4. It is not a guessed/reconstructed codec.
"""

import base64
import gzip
import hashlib
import html
import io
import zipfile
import json
import os
import re
import time
import random
import shlex
import shutil
import struct
import subprocess
import sys
import tempfile
import uuid
import zlib
import xml.etree.ElementTree as ET
from collections import deque
from dataclasses import dataclass
from datetime import datetime, timedelta, timezone
from pathlib import Path
from typing import Any, Iterable, Mapping
from urllib.parse import quote

try:
    import lz4.block
except ModuleNotFoundError:
    print("Thiếu thư viện lz4. Hãy chạy: python -m pip install lz4")
    raise SystemExit(2)

try:
    import requests
except ModuleNotFoundError:
    print("Thiếu thư viện requests. Hãy chạy: python -m pip install requests")
    raise SystemExit(2)

try:
    from cryptography.hazmat.primitives.ciphers.aead import AESGCM
except ModuleNotFoundError:
    print("Thiếu thư viện cryptography. Hãy chạy: python -m pip install cryptography")
    raise SystemExit(2)


# =============================================================================
# CONFIG - change only this block when your emulator/path changes
# =============================================================================
ADB_PATH = Path(r"D:\LDPlayer\LDPlayer14\adb.exe")
DEVICE_ID = "emulator-5556"
PACKAGE_NAME = "com.playrix.township.vn"
REMOTE_SAVE = "/data/data/com.playrix.township.vn/saves/mGameInfo.xml"
REMOTE_LOCALINFO = "/data/data/com.playrix.township.vn/saves/LocalInfo.xml"
WORK_DIR = Path(__file__).resolve().parent / "workspace_simple"
BACKUP_DIR = WORK_DIR / "backups"
SOURCE_FILE = WORK_DIR / "source.mGameInfo"
DECODED_FILE = WORK_DIR / "decoded.xml"
MODIFIED_FILE = WORK_DIR / "modified.xml"
OUTPUT_FILE = WORK_DIR / "output.mGameInfo"
VERIFY_FILE = WORK_DIR / "verify.xml"
DONOR_FILE = WORK_DIR / "friend_city_donor.xml"
CLONE_REPORT_FILE = WORK_DIR / "friend_city_clone_report.txt"
LOCALINFO_SOURCE_FILE = WORK_DIR / "source.LocalInfo"
LOCALINFO_DECODED_FILE = WORK_DIR / "LocalInfo_decoded.xml"
FRIENDS_DIR = WORK_DIR / "friends"
SELECTED_FRIEND_FILE = WORK_DIR / "selected_friend.json"
FRIEND_NETWORK_DIR = WORK_DIR / "friend_network"
FRIEND_NETWORK_JSON = FRIEND_NETWORK_DIR / "network.json"
FRIEND_NETWORK_EDGES = FRIEND_NETWORK_DIR / "edges.tsv"
FRIEND_NETWORK_MATCHES_JSON = FRIEND_NETWORK_DIR / "matches.json"
FRIEND_NETWORK_MATCHES_TSV = FRIEND_NETWORK_DIR / "matches.tsv"
UTC_PLUS_7 = timezone(timedelta(hours=7), name="UTC+7")


# =============================================================================
# CODEC 0x79 - copied into this file from the verified v0.2.4 implementation
# =============================================================================
FORMAT_79 = 0x79
MASK32 = 0xFFFF_FFFF
HASH_TABLE_SIZE = 727
MAX_XML_SIZE = 32 * 1024 * 1024
MAX_CONTAINER_SIZE = 64 * 1024 * 1024
LZ4_MAGIC = b"\x04\x22\x4d\x18"
XML_END = b"</root>"
HEADER_SIZE = 8
HEADER_XOR = 810_733
PAYLOAD_XOR = 235_176
MURMUR_M = 0x5BD1E995


class SaveToolError(RuntimeError):
    pass


def u32(value: int) -> int:
    return value & MASK32


def le_u32(data: bytes | bytearray | memoryview, offset: int = 0) -> int:
    return struct.unpack_from("<I", data, offset)[0]


def le_i32(data: bytes | bytearray | memoryview, offset: int = 0) -> int:
    return struct.unpack_from("<i", data, offset)[0]


def le_bytes(value: int) -> bytes:
    return struct.pack("<I", value & MASK32)


def murmur_hash2(data: bytes, length: int, seed: int) -> int:
    h = u32(seed ^ length)
    offset = 0
    remaining = length
    while remaining >= 4:
        k = le_u32(data, offset)
        k = u32(k * MURMUR_M)
        k ^= k >> 24
        k = u32(k * MURMUR_M)
        h = u32(h * MURMUR_M)
        h = u32(h ^ k)
        offset += 4
        remaining -= 4
    if remaining >= 3:
        h ^= data[offset + 2] << 16
    if remaining >= 2:
        h ^= data[offset + 1] << 8
    if remaining >= 1:
        h ^= data[offset]
        h = u32(h * MURMUR_M)
    h ^= h >> 13
    h = u32(h * MURMUR_M)
    h ^= h >> 15
    return u32(h)


def build_hash_table(header_seed: int, content_seed_plus_four: int) -> bytes:
    state = u32(content_seed_plus_four)
    table = bytearray(HASH_TABLE_SIZE)
    position = 0
    while position < HASH_TABLE_SIZE:
        state = murmur_hash2(le_bytes(state), 4, header_seed)
        block = le_bytes(state)
        writable = min(4, HASH_TABLE_SIZE - position)
        table[position:position + writable] = block[:writable]
        position += 4
    return bytes(table)


@dataclass(frozen=True)
class ContainerInfo:
    is_xml: bool
    total_size: int
    first_content_offset: int | None = None
    header_seed: int | None = None
    content_seed: int | None = None
    payload_length: int | None = None


def first_non_whitespace(data: bytes) -> int | None:
    for index, value in enumerate(data):
        if not chr(value).isspace():
            return index
    return None


def inspect_container(data: bytes) -> ContainerInfo:
    if not data:
        raise SaveToolError("File rỗng")
    if len(data) > MAX_CONTAINER_SIZE:
        raise SaveToolError("File vượt giới hạn an toàn 64 MB")
    first = first_non_whitespace(data)
    if first is not None and data[first] == ord("<"):
        if data.find(XML_END, first) < 0:
            raise SaveToolError("XML không chứa </root>")
        return ContainerInfo(True, len(data), first_content_offset=first)
    if len(data) < HEADER_SIZE:
        raise SaveToolError("Container ngắn hơn header")
    if data[0] != FORMAT_79:
        raise SaveToolError(f"Không hỗ trợ định dạng 0x{data[0]:02X}")
    header_seed = data[1] | (data[2] << 8) | (data[3] << 16)
    content_seed = le_u32(data, 4)
    recovered = u32(header_seed - (HEADER_XOR ^ len(data))) ^ PAYLOAD_XOR
    if recovered > len(data) - HEADER_SIZE:
        raise SaveToolError("Payload vượt kích thước container")
    return ContainerInfo(
        False,
        len(data),
        header_seed=header_seed,
        content_seed=content_seed,
        payload_length=recovered,
    )


def trim_xml(data: bytes, start: int = 0) -> bytes:
    end = data.find(XML_END, start)
    if end < 0:
        raise SaveToolError("Không tìm thấy </root>")
    return data[start:end + len(XML_END)]


def decode_save(container: bytes) -> bytes:
    info = inspect_container(container)
    if info.is_xml:
        assert info.first_content_offset is not None
        return trim_xml(container, info.first_content_offset)

    assert info.header_seed is not None
    assert info.content_seed is not None
    assert info.payload_length is not None
    table = build_hash_table(info.header_seed, u32(info.content_seed + 4))
    payload = bytearray(container[HEADER_SIZE:HEADER_SIZE + info.payload_length])
    table_index = 0
    for index in range(len(payload)):
        if index > 0:
            payload[index] = (payload[index] - payload[index - 1]) & 0xFF
        payload[index] ^= table[table_index]
        table_index = (table_index + 1) % HASH_TABLE_SIZE

    decoded_payload = bytes(payload)
    if decoded_payload.startswith(LZ4_MAGIC):
        if len(decoded_payload) < 8:
            raise SaveToolError("LZ4 payload bị cắt")
        output_size = le_i32(decoded_payload, 4)
        if not 1 <= output_size <= MAX_XML_SIZE:
            raise SaveToolError(f"Kích thước XML không hợp lệ: {output_size}")
        try:
            xml = lz4.block.decompress(
                decoded_payload[8:], uncompressed_size=output_size
            )
        except Exception as exc:
            raise SaveToolError(f"Giải nén LZ4 thất bại: {exc}") from exc
        if len(xml) != output_size:
            raise SaveToolError("Kích thước XML giải nén không khớp")
    else:
        xml = decoded_payload
    return trim_xml(xml)


def canonical_xml(xml_input: bytes) -> bytes:
    end = xml_input.find(XML_END)
    if end < 0:
        raise SaveToolError("XML đầu vào không chứa </root>")
    xml = xml_input[:end + len(XML_END)]
    if len(xml) > MAX_XML_SIZE:
        raise SaveToolError("XML vượt giới hạn 32 MB")
    return xml


def encode_save(xml_input: bytes, template: bytes) -> bytes:
    info = inspect_container(template)
    if info.is_xml or info.content_seed is None:
        raise SaveToolError("Template phải là container 0x79 gốc")

    raw = canonical_xml(xml_input) + b"\x00"
    compressed = lz4.block.compress(raw, mode="default", store_size=False)
    payload = LZ4_MAGIC + struct.pack("<I", len(raw)) + compressed

    target_size = info.total_size
    if target_size < len(payload) + HEADER_SIZE:
        raise SaveToolError(
            "Container gốc quá nhỏ cho dữ liệu mới. Không ghi để tránh hỏng save."
        )
    header_seed = u32((len(payload) ^ PAYLOAD_XOR) + (target_size ^ HEADER_XOR))
    if header_seed > 0xFF_FFFF:
        raise SaveToolError("Header seed vượt giới hạn 24-bit")

    table = build_hash_table(header_seed, u32(info.content_seed + 4))
    output = bytearray(target_size)
    output[0] = FORMAT_79
    output[1:4] = header_seed.to_bytes(3, "little")
    output[4:8] = struct.pack("<I", info.content_seed & MASK32)
    previous_plain = 0
    for index, byte in enumerate(payload):
        output[HEADER_SIZE + index] = (
            (byte ^ table[index % HASH_TABLE_SIZE]) + previous_plain
        ) & 0xFF
        previous_plain = byte
    return bytes(output)



# =============================================================================
# VERIFIED FETCHCITY PROTOCOL
# Source: tested standalone tsvip_fetchcity_final.py
# =============================================================================
AES_KEY = b"Wucai6oj0sheiX3p"
PROTOCOL_PREFIX = "002"
FETCH_URL = "https://township.playrix.com/api/1/FetchCity?cityId={}"

# Li43.<clinit>: 721-byte static key, represented as hex in the DEX.
_STATIC_KEY_HEX = (
    "775F7628505354364B48304F4A42303478783E524333216B52782A7C2B32355E4F53682E5827264E3E606D394B6649576F7C53326A686263206654643761535A3652426751624C2966573131623C274757274D294E236C6C5E715A7B5D3A62616A406E763959517960283827264532792A3C6E26526A4F656F694F45335B3F494C4F2B3F645340757C5D765649486769767477235F726C6F674C3F72636C4A6B4132563664485F617620753966772456676A25417442472B645245283A6E287449276234373F737A61494E6B6D387B3C376A4C23743B534A3B49275F767256436F7A216F706834702F64756D542836787B33517E266D6D6129252F7E4252636E6F6A795466542E79716E26736B396A3B61793370672B2C63634A473D544575324B2D2A642549552A59324E292E7D7B55505F4E2A783F5A5D5F6C2C5D767E276D7276422975472E7377325025512B7C4E514C603E4966794C77645D2C493F662B69673A6F3873234C524D792824305932567A584245567E51754267527E795A656F682D63434071403E362D567654322C5A53576C557E74682B25307C575F69506C7D4D30756E3F70796471756C607C5A4C607537726D314C3065777A3463392A666E525A463A38283B2625365B476E3E2C4C585739463F51513431283A357376724756237B2733295D322F366C6E5B735964733A7154644268384F79423C235121552551275B642B7225294F424F75795D213D7D6167304750365A7E602B393E724626605F385E7D4E7E583032442948237D614F2930387471783A2C4F26664E707B5224573E294D42654C697C52583A2E7A27354225675D313345662079254B3F7B524170676B7B2E31292C414F5B685579492E6F7C7140705E204D73314937205A75623A61274F3459275F303B586D5A7E764B3D6E4A2377594363636E5E437A4A75343C66356F67795D7D234B3546496C4B6E6E77545F5E6456415A67765D442057497440736C21693D2971786E5768"
)
STATIC_KEY = bytes.fromhex(_STATIC_KEY_HEX)

ASCII_KEY_S = (
    "BLD18qQhOwEylkVki91hjILTcIwbEMhUHamjkAzgyIWnl1tqOZvO+7AvOTqn036uyHAQVVbSH3/BzYMjNHTMXvogJBWI1siiMZF2zFzD0GEpuGdF+WbSIrug4fzHojQ/AAaBx2HT/tZ8hP+ITRc8z9a7ecsrGX+EBq+b3mada6zeJPxE2j47psb/J4Xnx0AEfh+lEb2GLpczI7e3o0BGP9GlmQYPSXINq87N2D8G175+cBwbMmzdfsIxr9hNGJgLGTFe/NdMP6NoAERNJOij9vzbgwiaOpdvmqBkV2HLp//Pj28HgIc392BrzFQ/slGN0/TqxugL1UY9GMpmI+GQVDSMzswGVWZ5VMjs4sSvkAmQ/p5AnrRyDoszxO+SKI5HV+OwHS0G7NcKXUMCx32xk6mVNxcpl0DwivGhJuvk/gphiG0b2f0gciQaaDJzuOJASND397ryTg4EuRYRw8D2A1lNF5lGEkzxMCGi56t4zCLduBcROWbbjBKKZer6enhbgsEytVBmzo4ONfQ+ZFv3sLhaEb72lnMkVKDD3tw7hzAoL86ObHGLOEGMUY3n9wihn1peBNBTcL3kSfH4/t9KF4qZ3GtXA++WO1h5/0edqVhDygXMUzQ87EZvcGuqLMk6iR08pFBO529aAADg8o9hHKfspYvwghDW/5HtJGL7CrGpE4Sr8FnvNvv7J3AGa9csWrhMB00P/dupnCafDuJAeCgFL0l"
).encode("utf-8")

ASCII_KEY_BRACE = (
    "AO[hUyI.o|q@p^ Ms1I7 Zub:a'O4Y'_0;XmZ~vK=nJ#wYCccn^CzJu4<f5ogy]}#K5FIlKnnwT_^dVAZgv]D WIt@sl!i=)qxnWh'QuBgR~yZeoh-cC@q@>6-VvT2,ZSWlU~th+%0|W_iPl}M0un?pydqul`|ZL`u7rm1L0ewz4c9*fnRZF:8(;&%6[Gn>,LXW9F?QQ41(:5svrGV#{'3)]2/6ln[sYds:qTdBh8OyB<#Q!U%Q'[d+r%)OBOuy]!=}ag0GP6Z~`+9>rF&`_8^}N~X02D)H#}aO)08tqx:,O&fNp{R$W>)MBeLi|RX:.z'5B%g]13Ef y%K?{RApgk{.1),Z]_l,]v~'mrvB)uG.sw2P%Q+|NQL`>IfyLwd],I?f+ig:o8s#LRMy($0Y2VzXBEV~oph4p/dumT(6x{3Q~&mma)%/~BRcnojyTfT.yqn&sk9j;ay3pg+,ccJG=TEu2K-*d%IU*Y2N).}{UP_N*x?u9fw$Vgj%AtBG+dRE(:n(tI'b47?szaINkm8{<7jL#t;SJ;I'_vrVCoz!E2y*<n&RjOeoiOE3[?ILO+?dS@u|]vVIHgivtw#_rlogL?rclJkA2V6dH_av 7aSZ6RBgQbL)fW11b<'GW'M)N#ll^qZ{]:baj@nv9YQy`(8'&w_v(PST6KH0OJB04xx>RC3!kRx*|+25^OSh.X'&N>`m9KfIWo|S2jhbc fTd"
).encode("utf-8")


class FetchCityError(RuntimeError):
    pass


def _i32(x: int) -> int:
    x &= 0xFFFFFFFF
    return x - 0x100000000 if x & 0x80000000 else x


def _u32(x: int) -> int:
    return x & 0xFFFFFFFF


def _java_copy_of_range(data: bytes, start: int, end: int) -> bytearray:
    """Java Arrays.copyOfRange(byte[], start, end), including zero padding."""
    if start < 0 or start > len(data) or start > end:
        raise FetchCityError(f"Invalid copy range [{start}:{end}] for {len(data)} bytes")
    wanted = end - start
    chunk = bytearray(data[start:min(end, len(data))])
    if len(chunk) < wanted:
        chunk.extend(b"\x00" * (wanted - len(chunk)))
    return chunk


def _decode_delta_xor(buf: bytearray, count: int, key: bytes, modulus: int) -> bytes:
    if not buf:
        return b""
    # The DEX subtracts ASCII 'T' (84) before entering the loop.
    buf[0] = (buf[0] - 84) & 0xFF
    count = min(count, len(buf))
    for i in range(count):
        if i > 0:
            buf[i] = (buf[i] - buf[i - 1]) & 0xFF
        buf[i] ^= key[i % modulus]
    return bytes(buf)


def _make_y_keystream(seed24: int, initial_state: int) -> bytes:
    """Reconstructed 727-byte iterative MurmurHash2-derived keystream."""
    out = bytearray(727)
    state = _u32(initial_state)
    m = 0x5BD1E995
    for pos in range(0, 727, 4):
        k = _u32(state * m)
        k ^= k >> 24
        k = _u32(k * m)
        h = _u32(_u32((seed24 ^ 4) * m) ^ k)
        h ^= h >> 13
        h = _u32(h * m)
        h ^= h >> 15
        h = _u32(h)
        block = h.to_bytes(4, "little")
        out[pos:min(pos + 4, 727)] = block[: max(0, min(4, 727 - pos))]
        state = h
    return bytes(out)


def decode_city_container(data: bytes, declared_length: int | None = None) -> bytes:
    """Port of Li43.a(int, byte[]) from the recovered DEX."""
    if not data:
        raise FetchCityError("Empty city data")
    n = len(data) if declared_length is None else declared_length
    sig = data[0]

    # Signature 'T' (0x54): 3-byte header.
    #
    # The two header bytes encode the number of bytes at the beginning of the
    # payload that are delta/XOR transformed:
    #
    #   transformed_count = (data[1] ^ STATIC_KEY[0]) | (data[2] << 8)
    #
    # Only that prefix is transformed. The remainder of the payload is copied
    # unchanged. The key index does NOT wrap at 0x54; it advances through the
    # full static key table.
    if sig == 0x54:
        if len(data) < 3:
            raise FetchCityError("Truncated T container")

        transformed_count = (data[1] ^ STATIC_KEY[0]) | (data[2] << 8)
        payload = data[3:n]

        if transformed_count < 0 or transformed_count > len(payload):
            raise FetchCityError(
                f"Invalid T transformed length {transformed_count}; "
                f"payload length is {len(payload)}"
            )

        prefix = _decode_delta_xor(
            bytearray(payload[:transformed_count]),
            transformed_count,
            STATIC_KEY,
            len(STATIC_KEY),
        )
        return prefix + payload[transformed_count:]

    # Signature 'S' (0x53): 3-byte header + long ASCII table.
    if sig == 0x53:
        if len(data) < 3:
            raise FetchCityError("Truncated S container")
        end = (data[1] ^ 0x53) | (data[2] << 8)
        count = min(end, n - 3)
        payload = _java_copy_of_range(data, 3, end)
        return _decode_delta_xor(payload, count, ASCII_KEY_S, len(ASCII_KEY_S))

    # Signature 'y' (0x79): 8-byte header + generated 727-byte stream.
    if sig == 0x79:
        if len(data) < 8:
            raise FetchCityError("Truncated y container")
        seed24 = data[1] | (data[2] << 8) | (data[3] << 16)
        initial_state = int.from_bytes(data[4:8], "little")
        initial_state = _u32(initial_state + 4)
        key = _make_y_keystream(seed24, initial_state)

        # Exact Java arithmetic from the DEX:
        # outLen = (int)(seed24 - ((long)n ^ 0x000C5EEDL)) ^ 0x000396A8
        out_len = _i32(_u32(seed24 - (n ^ 0x000C5EED)))
        out_len = _i32(_u32(out_len ^ 0x000396A8))

        payload = bytearray(data[8:])
        count = min(out_len, len(payload))
        if count < 0:
            raise FetchCityError(f"Invalid y output length {out_len}")
        key_pos = 0
        for i in range(count):
            if i > 0:
                payload[i] = (payload[i] - payload[i - 1]) & 0xFF
            payload[i] ^= key[key_pos]
            key_pos = (key_pos + 1) % 727
        return bytes(payload[:out_len])

    # Signature '}' (0x7D): XOR the complete byte array with a fixed table.
    if sig == 0x7D:
        out = bytearray(data[:n])
        for i in range(len(out)):
            out[i] ^= ASCII_KEY_BRACE[i % len(ASCII_KEY_BRACE)]
        return bytes(out)

    # Already decoded formats.
    if sig == 0x1F and len(data) >= 2 and data[1] == 0x8B:
        return data
    if sig == ord("<"):
        return data[:n]
    if sig == ord("{") and data[-1] == ord("}"):
        return data[:n]

    raise FetchCityError(f"Unknown city-data signature: 0x{sig:02x}")


def city_bytes_to_text(data: bytes) -> str:
    if data.startswith(b"\x1f\x8b"):
        try:
            data = gzip.decompress(data)
        except (OSError, EOFError, zlib.error) as exc:
            raise FetchCityError(
                "Decoded city payload begins with a GZIP header, but the stream is "
                "invalid or truncated. Raw artifacts were preserved for analysis."
            ) from exc
    try:
        return data.decode("utf-8")
    except UnicodeDecodeError as exc:
        raise FetchCityError("Decoded city payload is not valid UTF-8") from exc


@dataclass
class PreparedRequest:
    url: str
    headers: dict[str, str]
    body: bytes
    plaintext_json: str


def prepare_request(city_id: str, bver: str, fver: str, city_ver: int = 0,
                    iv: bytes | None = None) -> PreparedRequest:
    # The original app constructs this exact compact field order manually.
    plaintext = (
        f'{{"fetchCityId":"{city_id}","bver":"{bver}",'
        f'"fver":"{fver}","cityVer":{int(city_ver)}}}'
    )
    packed = gzip.compress(plaintext.encode("utf-8"), mtime=0)
    iv = os.urandom(12) if iv is None else iv
    if len(iv) != 12:
        raise ValueError("AES-GCM IV must be 12 bytes")
    encrypted = AESGCM(AES_KEY).encrypt(iv, packed, None)
    ciphertext, tag = encrypted[:-16], encrypted[-16:]
    ts_id = PROTOCOL_PREFIX + iv.hex() + tag.hex()
    headers = {
        "Accept-Encoding": "identity",
        "Content-Type": "application/octet-stream",
        "Connection": "close",
        "User-Agent": "okhttp/4.9.0",
        "ts-bp": "i",
        "ts-bver": bver,
        "ts-fver": fver,
        "ts-gpid": "new",
        "ts-id": ts_id,
    }
    return PreparedRequest(
        url=FETCH_URL.format(quote(city_id, safe="")),
        headers=headers,
        body=ciphertext,
        plaintext_json=plaintext,
    )


def decrypt_response_json(body: bytes, ts_id: str) -> dict[str, Any]:
    ts_id = ts_id.strip()
    if len(ts_id) != 59:
        raise FetchCityError(f"Invalid ts-id length {len(ts_id)}; expected 59")
    if ts_id[:3] != PROTOCOL_PREFIX:
        raise FetchCityError(f"Unsupported ts-id protocol prefix {ts_id[:3]!r}")
    try:
        iv = bytes.fromhex(ts_id[3:27])
        tag = bytes.fromhex(ts_id[27:59])
    except ValueError as exc:
        raise FetchCityError("ts-id contains invalid hexadecimal data") from exc
    try:
        packed = AESGCM(AES_KEY).decrypt(iv, body + tag, None)
    except Exception as exc:
        raise FetchCityError("AES-GCM authentication/decryption failed") from exc
    try:
        raw_json = gzip.decompress(packed)
        obj = json.loads(raw_json.decode("utf-8"))
    except Exception as exc:
        raise FetchCityError("Response decrypted, but GZIP/JSON decoding failed") from exc
    if not isinstance(obj, dict):
        raise FetchCityError("Response JSON root is not an object")
    return obj


def extract_city(obj: dict[str, Any]) -> tuple[int, bytes, str]:
    result = obj.get("result")
    if not isinstance(result, dict):
        raise FetchCityError("Response has no result object")
    city_ver = int(result.get("cityVer", 0) or 0)
    encoded = result.get("data")
    if not isinstance(encoded, str) or not encoded:
        raise FetchCityError("Response result.data is missing or not a Base64 string")
    try:
        container = base64.b64decode(encoded, validate=False)
    except Exception as exc:
        raise FetchCityError("result.data Base64 decoding failed") from exc
    decoded = decode_city_container(container, len(container))
    text = city_bytes_to_text(decoded)
    return city_ver, decoded, text


def fetch_city_live(
    city_id: str,
    bver: str,
    fver: str,
    city_ver: int = 0,
    out_dir: Path | None = None,
) -> tuple[bytes, dict[str, Any], int]:
    """Send FetchCity directly and return donor XML, response JSON, city version."""
    prepared = prepare_request(city_id, bver, fver, city_ver)
    try:
        response = requests.post(
            prepared.url,
            headers=prepared.headers,
            data=prepared.body,
            timeout=(15, 45),
            allow_redirects=False,
        )
    except requests.RequestException as exc:
        raise SaveToolError(f"FetchCity HTTP thất bại: {exc}") from exc

    target = out_dir or (FRIENDS_DIR / city_id)
    target.mkdir(parents=True, exist_ok=True)
    atomic_write(target / "request_body.bin", prepared.body)
    atomic_write(
        target / "request.json",
        prepared.plaintext_json.encode("utf-8"),
    )
    atomic_write(
        target / "request_meta.json",
        json.dumps(
            {"url": prepared.url, "headers": prepared.headers},
            ensure_ascii=False,
            indent=2,
        ).encode("utf-8"),
    )
    atomic_write(target / "response_body.bin", response.content)
    atomic_write(
        target / "response_headers.json",
        json.dumps(dict(response.headers), ensure_ascii=False, indent=2).encode("utf-8"),
    )

    if not 200 <= response.status_code < 300:
        preview = response.content[:500].decode("utf-8", "replace")
        raise SaveToolError(f"FetchCity HTTP {response.status_code}: {preview}")

    response_ts_id = response.headers.get("ts-id", "")
    try:
        response_obj = decrypt_response_json(response.content, response_ts_id)
        city_ver_result, decoded_city, city_text = extract_city(response_obj)
    except FetchCityError as exc:
        raise SaveToolError(f"Giải FetchCity thất bại: {exc}") from exc

    donor = city_text.encode("utf-8")
    donor = canonical_xml(donor)
    validate_xml_document(donor, "FetchCity donor")
    get_direct_child_block(donor, "TownGround")
    get_direct_child_block(donor, "Buildings")

    atomic_write(
        target / "response.json",
        json.dumps(response_obj, ensure_ascii=False, indent=2).encode("utf-8"),
    )
    atomic_write(target / "city_decoded.bin", decoded_city)
    atomic_write(target / "friend_city.xml", donor)
    return donor, response_obj, city_ver_result


# =============================================================================
# GENERIC XML TAG ATTRIBUTE EDITOR
# =============================================================================
ATTR_RE = re.compile(rb'([A-Za-z_][\w:.-]*)\s*=\s*(["\'])(.*?)\2', re.DOTALL)
TAG_NAME_RE = re.compile(rb"<\s*([A-Za-z_][\w:.-]*)\b")


def parse_attributes(tag: bytes) -> dict[str, str]:
    return {
        m.group(1).decode("utf-8"): m.group(3).decode("utf-8")
        for m in ATTR_RE.finditer(tag)
    }


def xml_escape_attribute(value: str) -> str:
    return (
        value.replace("&", "&amp;")
        .replace('"', "&quot;")
        .replace("'", "&apos;")
        .replace("<", "&lt;")
        .replace(">", "&gt;")
    )


def replace_attribute(tag: bytes, attribute: str, new_value: str) -> bytes:
    escaped_name = re.escape(attribute.encode("utf-8"))
    pattern = re.compile(
        rb"(\b" + escaped_name + rb"\s*=\s*)([\"\'])(.*?)\2", re.DOTALL
    )
    matches = list(pattern.finditer(tag))
    if len(matches) > 1:
        raise SaveToolError(
            f"Thuộc tính {attribute!r} xuất hiện nhiều lần trong cùng một tag"
        )
    encoded_value = xml_escape_attribute(new_value).encode("utf-8")
    if matches:
        match = matches[0]
        replacement = match.group(1) + match.group(2) + encoded_value + match.group(2)
        return tag[:match.start()] + replacement + tag[match.end():]

    close_pos = tag.rfind(b"/>")
    if close_pos < 0:
        close_pos = tag.rfind(b">")
    if close_pos < 0:
        raise SaveToolError("Tag XML không hợp lệ")
    insertion = b" " + attribute.encode("utf-8") + b'="' + encoded_value + b'"'
    return tag[:close_pos] + insertion + tag[close_pos:]


def find_matching_tags(
    xml: bytes,
    tag_name: str,
    match_attributes: Mapping[str, str],
) -> list[re.Match[bytes]]:
    safe_tag = re.escape(tag_name.encode("utf-8"))
    pattern = re.compile(rb"<\s*" + safe_tag + rb"\b[^>]*>", re.DOTALL)
    result: list[re.Match[bytes]] = []
    for match in pattern.finditer(xml):
        attrs = parse_attributes(match.group(0))
        if all(attrs.get(key) == value for key, value in match_attributes.items()):
            result.append(match)
    return result


def read_tag_attributes(
    xml: bytes,
    tag_name: str,
    match_attributes: Mapping[str, str],
) -> dict[str, str]:
    matches = find_matching_tags(xml, tag_name, match_attributes)
    if len(matches) != 1:
        raise SaveToolError(
            f"<{tag_name}> với điều kiện {dict(match_attributes)}: "
            f"cần đúng 1 tag, tìm thấy {len(matches)}"
        )
    return parse_attributes(matches[0].group(0))


def patch_tag_attributes(
    xml: bytes,
    tag_name: str,
    match_attributes: Mapping[str, str],
    updates: Mapping[str, str],
) -> tuple[bytes, dict[str, tuple[str | None, str]]]:
    matches = find_matching_tags(xml, tag_name, match_attributes)
    if len(matches) != 1:
        raise SaveToolError(
            f"<{tag_name}> với điều kiện {dict(match_attributes)}: "
            f"cần đúng 1 tag, tìm thấy {len(matches)}"
        )
    match = matches[0]
    old_tag = match.group(0)
    old_attrs = parse_attributes(old_tag)
    new_tag = old_tag
    changes: dict[str, tuple[str | None, str]] = {}
    for attr_name, new_value in updates.items():
        changes[attr_name] = (old_attrs.get(attr_name), new_value)
        new_tag = replace_attribute(new_tag, attr_name, new_value)
    updated_xml = xml[:match.start()] + new_tag + xml[match.end():]

    verified_attrs = read_tag_attributes(updated_xml, tag_name, match_attributes)
    for attr_name, new_value in updates.items():
        # A selector attribute should normally not be edited. If it is, verification
        # by the old selector becomes impossible; generic menu blocks that case.
        if verified_attrs.get(attr_name) != new_value:
            raise SaveToolError(
                f"Xác minh thất bại: {attr_name}={verified_attrs.get(attr_name)!r}, "
                f"mong đợi {new_value!r}"
            )
    return updated_xml, changes


def read_var(xml: bytes, var_name: str) -> dict[str, str]:
    return read_tag_attributes(xml, "Var", {"name": var_name})


def patch_var(xml: bytes, var_name: str, updates: Mapping[str, str]) -> tuple[bytes, dict]:
    if "name" in updates:
        raise SaveToolError("Không đổi thuộc tính name của <Var> bằng hàm patch_var")
    return patch_tag_attributes(xml, "Var", {"name": var_name}, updates)


def parse_int(text: str, label: str, minimum: int, maximum: int) -> int:
    try:
        value = int(text.strip())
    except ValueError as exc:
        raise SaveToolError(f"{label} phải là số nguyên") from exc
    if not minimum <= value <= maximum:
        raise SaveToolError(f"{label} phải từ {minimum:,} đến {maximum:,}")
    return value


def set_integer_var(
    xml: bytes,
    var_name: str,
    value: int,
    minimum: int = 0,
    maximum: int = 2_000_000_000,
) -> tuple[bytes, dict]:
    if not minimum <= value <= maximum:
        raise SaveToolError(f"{var_name} phải từ {minimum:,} đến {maximum:,}")
    return patch_var(xml, var_name, {"v": str(value)})


# TSVIP v121: uh3.<clinit> XP thresholds, uh3.a and gt1.invoke (lvl).
# Index 0 is the b(0) sentinel; indices 1..1089 are copied from the APK.
TSVIP_LEVEL_XP = (0,
    9, 26, 70, 200, 484, 776, 1184, 1740,
    2519, 3482, 4716, 6271, 8206, 10583, 13472, 16950,
    21099, 26011, 31782, 38518, 46331, 55342, 65680, 77482,
    90895, 106073, 123181, 142391, 163886, 187860, 214514, 244061,
    276724, 312737, 352343, 395798, 443369, 495332, 551977, 613605,
    680529, 753074, 831577, 916388, 1007869, 1106395, 1212356, 1326153,
    1448200, 1578927, 1718775, 1868202, 2027678, 2197687, 2378730, 2571320,
    2775987, 2993273, 3223740, 3467960, 3726525, 4000040, 4300040, 4612040,
    4937040, 5274040, 5623040, 5984040, 6357040, 6741040, 7137040, 7545040,
    7964040, 8395040, 8837040, 9290040, 9755040, 10231040, 10718040, 11216040,
    11725040, 12245040, 12776040, 13317040, 13869040, 14432040, 15005040, 15589040,
    16183040, 16788040, 17403040, 18028040, 18664040, 19310040, 19966040, 20632040,
    21308040, 21994040, 22690040, 23396040, 24112040, 24837040, 25572040, 26317040,
    27072040, 27836040, 28610040, 29393040, 30186040, 30988040, 31799040, 32620040,
    33450040, 34289040, 35138040, 35996040, 36863040, 37739040, 38624040, 39518040,
    40421040, 41333040, 42254040, 43184040, 44123040, 45070040, 46026040, 46991040,
    47965040, 48948040, 49939040, 50938040, 51946040, 52963040, 53988040, 55022040,
    56064040, 57114040, 58173040, 59240040, 60315040, 61399040, 62491040, 63591040,
    64699040, 65816040, 66941040, 68074040, 69215040, 70364040, 71521040, 72686040,
    73859040, 75040040, 76229040, 77426040, 78631040, 79844040, 81065040, 82293040,
    83529040, 84773040, 86025040, 87284040, 88551040, 89826040, 91108040, 92398040,
    93696040, 95001040, 96314040, 97634040, 98962040, 100297040, 101640040, 102990040,
    104348040, 105713040, 107085040, 108465040, 109852040, 111246040, 112648040, 114057040,
    115473040, 116897040, 118328040, 119766040, 121211040, 122663040, 124123040, 125590040,
    127064040, 128545040, 130033040, 131528040, 133030040, 134539040, 136055040, 137578040,
    139108040, 140645040, 142189040, 143740040, 145298040, 146863040, 148435040, 150013040,
    151598040, 153190040, 154789040, 156395040, 158007040, 159626040, 161252040, 162885040,
    164524040, 166170040, 167823040, 169482040, 171148040, 172821040, 174500040, 176186040,
    177879040, 179578040, 181284040, 182996040, 184715040, 186440040, 188172040, 189910040,
    191655040, 193406040, 195164040, 196928040, 198699040, 200476040, 202259040, 204049040,
    205845040, 207648040, 209457040, 211272040, 213094040, 214922040, 216756040, 218596040,
    220443040, 222297040, 224156040, 226021040, 227893040, 229771040, 231655040, 233545040,
    235441040, 237344040, 239253040, 241168040, 243089040, 245016040, 246949040, 248888040,
    250833040, 252784040, 254741040, 256704040, 258673040, 260648040, 262629040, 264616040,
    266609040, 268608040, 270613040, 272624040, 274641040, 276664040, 278693040, 280728040,
    282769040, 284816040, 286869040, 288928040, 290992040, 293062040, 295138040, 297220040,
    299308040, 301402040, 303501040, 305606040, 307717040, 309834040, 311957040, 314085040,
    316219040, 318359040, 320504040, 322655040, 324812040, 326975040, 329143040, 331317040,
    333497040, 335682040, 337873040, 340070040, 342272040, 344480040, 346693040, 348912040,
    351137040, 353367040, 355603040, 357844040, 360091040, 362343040, 364601040, 366864040,
    369133040, 371407040, 373687040, 375972040, 378263040, 380559040, 382861040, 385168040,
    387481040, 389799040, 392123040, 394452040, 396787040, 399127040, 401472040, 403823040,
    406179040, 408541040, 410908040, 413280040, 415658040, 418041040, 420429040, 422823040,
    425222040, 427626040, 430036040, 432451040, 434871040, 437297040, 439728040, 442164040,
    444605040, 447052040, 449504040, 451961040, 454423040, 456891040, 459364040, 461842040,
    464325040, 466813040, 469307040, 471806040, 474310040, 476819040, 479333040, 481852040,
    484377040, 486907040, 489442040, 491982040, 494527040, 497077040, 499632040, 502192040,
    504758040, 507329040, 509905040, 512486040, 515072040, 517663040, 520259040, 522860040,
    525466040, 528077040, 530693040, 533314040, 535940040, 538571040, 541207040, 543848040,
    546494040, 549145040, 551801040, 554462040, 557128040, 559799040, 562475040, 565156040,
    567842040, 570533040, 573229040, 575930040, 578636040, 581346040, 584061040, 586782040,
    589507040, 592237040, 594972040, 597712040, 600457040, 603207040, 605961040, 608720040,
    611484040, 614253040, 617027040, 619806040, 622589040, 625377040, 628170040, 630968040,
    633771040, 636578040, 639390040, 642207040, 645029040, 647856040, 650687040, 653523040,
    656364040, 659210040, 662060040, 664915040, 667775040, 670640040, 673509040, 676383040,
    679262040, 682145040, 685033040, 687926040, 690824040, 693726040, 696633040, 699545040,
    702461040, 705382040, 708308040, 711238040, 714173040, 717112040, 720056040, 723005040,
    725958040, 728916040, 731879040, 734846040, 737818040, 740795040, 743776040, 746762040,
    749752040, 752747040, 755746040, 758750040, 761759040, 764772040, 767790040, 770812040,
    773839040, 776870040, 779906040, 782946040, 785991040, 789040040, 792094040, 795152040,
    798215040, 801282040, 804354040, 807430040, 810510040, 813604040, 816703040, 819807040,
    822916040, 826030040, 829149040, 832273040, 835402040, 838536040, 841675040, 844819040,
    847968040, 851122040, 854281040, 857445040, 860700834, 863953864, 867204304, 870452325,
    873698100, 876941803, 880183606, 883423682, 886662202, 889899341, 893135271, 896370165,
    899604195, 902837534, 906070355, 909302830, 912535132, 915767435, 918999910, 922232731,
    925466070, 928700100, 931934993, 935170923, 938408062, 941646583, 944886659, 948128462,
    951372164, 954617940, 957865961, 961116401, 964369431, 967625225, 970883955, 974145795,
    977410916, 980679493, 983951696, 987227700, 990507676, 993791798, 997080238, 1000373170,
    1003670765, 1006973196, 1010280637, 1013593259, 1016911237, 1020234741, 1023563946, 1026935946,
    1030342718, 1033751149, 1037161318, 1040573303, 1043987181, 1047403031, 1050820930, 1054240956,
    1057663188, 1061087703, 1064514579, 1067943894, 1071375727, 1074810154, 1078247253, 1081687104,
    1085129783, 1088575369, 1092023939, 1095475572, 1098930345, 1102388336, 1105849623, 1109314285,
    1112782399, 1116254042, 1119729294, 1123208231, 1126690932, 1130177475, 1133667937, 1137162397,
    1140660932, 1144163621, 1147670540, 1151181770, 1154697386, 1158217467, 1161742091, 1165271336,
    1168805280, 1172344001, 1175887576, 1179436084, 1182989602, 1186548209, 1190111983, 1193681000,
    1197254856, 1200833077, 1204415641, 1208002526, 1211593711, 1215189173, 1218788890, 1222392840,
    1226001001, 1229613351, 1233229867, 1236850529, 1240475313, 1244104198, 1247737162, 1251374182,
    1255015237, 1258660304, 1262309362, 1265962388, 1269619360, 1273280257, 1276945056, 1280613735,
    1284286272, 1287962646, 1291642833, 1295326812, 1299014561, 1302706058, 1306401281, 1310100208,
    1313802816, 1317509084, 1321218989, 1324932510, 1328649624, 1332370310, 1336094545, 1339822308,
    1343553575, 1347288326, 1351026539, 1354768190, 1358513258, 1362261721, 1366013557, 1369768744,
    1373527260, 1377289083, 1381054190, 1384822560, 1388594171, 1392369000, 1396147758, 1399931151,
    1403719148, 1407511721, 1411308839, 1415110473, 1418916594, 1422727171, 1426542175, 1430361577,
    1434185347, 1438013455, 1441845872, 1445682568, 1449523514, 1453368679, 1457218035, 1461071551,
    1464929198, 1468790947, 1472656767, 1476526630, 1480400505, 1484278363, 1488160174, 1492045910,
    1495935539, 1499829033, 1503726362, 1507627496, 1511532406, 1515441062, 1519353434, 1523269493,
    1527189210, 1531112554, 1535039496, 1538970006, 1542904056, 1546841614, 1550782652, 1554727140,
    1558675049, 1562626348, 1566581008, 1570539000, 1574500607, 1578466125, 1582435542, 1586408845,
    1590386021, 1594367059, 1598351946, 1602340670, 1606333218, 1610329578, 1614329738, 1618333685,
    1622341407, 1626352892, 1630368127, 1634387100, 1638409798, 1642436210, 1646466322, 1650500123,
    1654537600, 1658578740, 1662623532, 1666671963, 1670724021, 1674779693, 1678838967, 1682901831,
    1686968272, 1691038278, 1695111836, 1699188935, 1703269562, 1707353704, 1711441349, 1715532485,
    1719627099, 1723725179, 1727826713, 1731931689, 1736040093, 1740151914, 1744267140, 1748385757,
    1752507754, 1756633118, 1760761837, 1764893899, 1769029290, 1773168000, 1777310882, 1781458743,
    1785611503, 1789769077, 1793931384, 1798098341, 1802269865, 1806445876, 1810626289, 1814811022,
    1818999994, 1823193121, 1827390322, 1831591513, 1835796613, 1840005539, 1844218208, 1848434538,
    1852654447, 1856877852, 1861104671, 1865334821, 1869568220, 1873804786, 1878044436, 1882287087,
    1886532658, 1890781065, 1895032227, 1899286061, 1903542484, 1907801415, 1912062770, 1916326467,
    1920592425, 1924860559, 1929130789, 1933403031, 1937677203, 1941953223, 1946231008, 1950510476,
    1954791544, 1959074130, 1963358152, 1967643527, 1971930172, 1976218006, 1980506946, 1984826946,
    1989181100, 1993536775, 1997894016, 2002252869, 2006613379, 2010975591, 2015339550, 2019705303,
    2024072894, 2028442369, 2032813774, 2037187153, 2041562552, 2045940017, 2050319592, 2054701324,
    2059085257, 2063471438, 2067859910, 2072250721, 2076643915, 2081039537, 2085437633, 2089838249,
    2094241429, 2098647220, 2103055666, 2107466812, 2111880706, 2116297391, 2120716913, 2125139317,
    2129564649, 2133992955, 2138424279, 2142858668, 2147296165, 2151736818, 2156180670, 2160627769,
    2165078158, 2169531884, 2173988991, 2178449526, 2182913533, 2187381058, 2191852147, 2196326844,
    2200805195, 2205287246, 2209773041, 2214262627, 2218756049, 2223253352, 2227754581, 2232259782,
    2236769000, 2241281938, 2245798275, 2250318023, 2254841195, 2259367801, 2263897855, 2268431367,
    2272968350, 2277508815, 2282052774, 2286600240, 2291151224, 2295705737, 2300263792, 2304825401,
    2309390575, 2313959326, 2318531667, 2323107608, 2327687163, 2332270342, 2336857157, 2341447621,
    2346041746, 2350639542, 2355241022, 2359846199, 2364455082, 2369067686, 2373684021, 2378304099,
    2382927932, 2387555532, 2392186911, 2396822080, 2401461053, 2406103839, 2410750452, 2415400903,
    2420055204, 2424713366, 2429375402, 2434041324, 2438711143, 2443384872, 2448062521, 2452744104,
    2457429631, 2462119115, 2466812567, 2471510000, 2476211184, 2480915869, 2485624032, 2490335650,
    2495050703, 2499769167, 2504491020, 2509216241, 2513944807, 2518676697, 2523411887, 2528150356,
    2532892081, 2537637041, 2542385214, 2547136576, 2551891107, 2556648783, 2561409584, 2566173485,
    2570940467, 2575710505, 2580483579, 2585259666, 2590038744, 2594820790, 2599605783, 2604393701,
    2609184521, 2613978221, 2618774779, 2623574172, 2628376380, 2633181379, 2637989148, 2642799663,
    2647612904, 2652428848, 2657247473, 2662068757, 2666892677, 2671719211, 2676548338, 2681380035,
    2686214280, 2691051050, 2695890325, 2700732080, 2705576296, 2710422948, 2715272016, 2720123476,
    2724977308, 2729833488, 2734691994, 2739552805, 2744415898, 2749281252, 2754148843, 2759018650,
    2763890650, 2768764822, 2773641144, 2778519592, 2783400146, 2788282783, 2793167480, 2798054216,
    2802942969, 2807833715, 2812726434, 2817621103, 2822517700, 2827416203, 2832316589, 2837218837,
    2842122924, 2847028829, 2851936528, 2856846000, 2861759888, 2866680808, 2871608701, 2876543505,
    2881485162, 2886433610, 2891388789, 2896350638, 2901319098, 2906294109, 2911275608, 2916263538,
    2921257836, 2926258443, 2931265299, 2936278343, 2941297515, 2946322754, 2951354000, 2956389546,
    2961427717, 2966468501, 2971511887, 2976557863, 2981606419, 2986657543, 2991711223, 2996767447,
    3001826206, 3006887486, 3011951277, 3017017567, 3022086345, 3027157600, 3032231320, 3037307493,
    3042386108, 3047467155, 3052550620, 3057636494, 3062724764, 3067815420, 3072908449, 3078003840,
    3083101583, 3088201665, 3093304075, 3098408802, 3103515834, 3108625160, 3113736769, 3118850648,
    3123966787, 3129085175, 3134205799, 3139328649, 3144453713, 3149580979, 3154710436, 3159842074,
    3164975880, 3170111842, 3175249950, 3180390193, 3185532558, 3190677034, 3195823611, 3200972275,
    3206123017, 3211275825, 3216430687, 3221587592, 3226746528, 3231907484, 3237070449, 3242235411,
    3247402359, 3252571281, 3257742166, 3262915003, 3268089780, 3273266486, 3278445109, 3283625638,
    3288808062, 3293992368, 3299178547, 3304366586, 3309556473, 3314748198, 3319941749, 3325137115,
    3330334284, 3335533245, 3340733986, 3345936497, 3351140765, 3356346779, 3361554528, 3366764000,
    3372017000,
)
TSVIP_LEVEL_MIN = 1
TSVIP_LEVEL_MAX = 1089
TSVIP_XP_XOR = 509438470


def township_level_values(level: int) -> dict[str, int]:
    if type(level) is not int or not TSVIP_LEVEL_MIN <= level <= TSVIP_LEVEL_MAX:
        raise SaveToolError("Level phải là số nguyên từ 1 đến 1089")
    previous = TSVIP_LEVEL_XP[level - 1]
    # Match Java long -> double -> multiply 0.9 -> truncate to long exactly.
    experience = previous + int(float(TSVIP_LEVEL_XP[level] - previous) * 0.9)
    return {"levelup": level, "experience": experience,
            "sexpx": experience ^ TSVIP_XP_XOR}


def _level_field_tags(xml: bytes, name: str) -> list[re.Match[bytes]]:
    return [m for m in re.finditer(rb"<(?:Var|DataElem)\b[^>]*>", xml, re.I)
            if parse_attributes(m.group(0)).get("name", "").casefold() == name.casefold()]


def read_township_level(xml: bytes) -> int:
    matches = _level_field_tags(xml, "levelup")
    if len(matches) != 1:
        raise SaveToolError("Cần đúng một trường levelup để xác định level hiện tại")
    attrs = parse_attributes(matches[0].group(0))
    return parse_int(attrs.get("value", attrs.get("v", "")), "Level hiện tại", 0, 2_147_483_647)


def set_township_level(xml: bytes, level: int, allow_decrease: bool = False) -> tuple[bytes, dict]:
    values = township_level_values(level)
    current = read_township_level(xml)
    if level < current and not allow_decrease:
        raise SaveToolError(f"TSVIP không cho giảm level: hiện tại {current}, yêu cầu {level}")
    updated = xml
    changes = {}
    for name, value in values.items():
        matches = _level_field_tags(updated, name)
        if len(matches) > 1:
            raise SaveToolError(f"Trường {name} bị trùng; không áp dụng thay đổi")
        if matches:
            match = matches[0]
            attrs = parse_attributes(match.group(0))
            attribute = "value" if "value" in attrs else "v"
            changes[name] = (attrs.get(attribute), str(value))
            tag = replace_attribute(match.group(0), attribute, str(value))
            updated = updated[:match.start()] + tag + updated[match.end():]
        else:
            endings = list(re.finditer(rb"</Global\s*>", updated, re.I))
            if len(endings) != 1:
                raise SaveToolError(f"Thiếu {name} và không xác định được khối Global để thêm")
            position = endings[0].start()
            tag = f'<Var name="{name}" v="{value}" t="i"/>'.encode()
            updated = updated[:position] + b"    " + tag + b"\n" + updated[position:]
            changes[name] = (None, str(value))
    validate_xml_document(updated, "Set Level")
    for name, value in values.items():
        matches = _level_field_tags(updated, name)
        attrs = parse_attributes(matches[0].group(0))
        if attrs.get("value", attrs.get("v")) != str(value):
            raise SaveToolError(f"Xác minh {name} thất bại")
    return updated, changes


def set_game_start_month(xml: bytes, year: int, month: int) -> tuple[bytes, dict]:
    if not 1970 <= year <= 2100:
        raise SaveToolError("Năm phải từ 1970 đến 2100")
    if not 1 <= month <= 12:
        raise SaveToolError("Tháng phải từ 1 đến 12")
    dt = datetime(year, month, 1, 0, 0, 0, tzinfo=UTC_PLUS_7)
    now = datetime.now(UTC_PLUS_7)
    if dt > now:
        raise SaveToolError("Không cho phép ngày tạo trong tương lai")
    return patch_var(xml, "gameStartDate", {"v": str(int(dt.timestamp()))})



# =============================================================================
# FRIEND CITY LAYOUT CLONE ENGINE
# =============================================================================
XML_TOKEN_RE = re.compile(
    rb"<!--.*?-->|<\?.*?\?>|<!\[CDATA\[.*?\]\]>|<![^>]*>|"
    rb"</\s*([A-Za-z_][\w:.-]*)\s*>|"
    rb"<\s*([A-Za-z_][\w:.-]*)\b[^>]*?/\s*>|"
    rb"<\s*([A-Za-z_][\w:.-]*)\b[^>]*>",
    re.DOTALL,
)


@dataclass(frozen=True)
class XmlElementSpan:
    tag: str
    start: int
    end: int


def validate_xml_document(xml: bytes, label: str) -> ET.Element:
    canonical = canonical_xml(xml)
    try:
        return ET.fromstring(canonical)
    except ET.ParseError as exc:
        raise SaveToolError(f"{label} không phải XML hợp lệ: {exc}") from exc


def direct_child_spans(xml: bytes, parent_tag: str = "root") -> list[XmlElementSpan]:
    """
    Trả về các phần tử con trực tiếp của parent_tag mà không serialize lại XML.
    Nhờ vậy các chuỗi JSON trong thuộc tính Object data được giữ nguyên byte.
    """
    stack: list[tuple[str, int]] = []
    parent_depth: int | None = None
    result: list[XmlElementSpan] = []

    for match in XML_TOKEN_RE.finditer(xml):
        closing = match.group(1)
        self_closing = match.group(2)
        opening = match.group(3)

        if closing:
            tag = closing.decode("utf-8")
            if not stack:
                raise SaveToolError(f"XML lỗi: gặp </{tag}> khi stack rỗng")
            open_tag, open_start = stack.pop()
            if open_tag != tag:
                raise SaveToolError(
                    f"XML lỗi: mở <{open_tag}> nhưng đóng </{tag}>"
                )
            if parent_depth is not None and len(stack) == parent_depth:
                result.append(XmlElementSpan(tag, open_start, match.end()))
            if tag == parent_tag and parent_depth == len(stack):
                parent_depth = None
            continue

        if self_closing:
            tag = self_closing.decode("utf-8")
            if parent_depth is not None and len(stack) == parent_depth:
                result.append(XmlElementSpan(tag, match.start(), match.end()))
            continue

        if opening:
            tag = opening.decode("utf-8")
            stack.append((tag, match.start()))
            if tag == parent_tag and parent_depth is None:
                parent_depth = len(stack)

    if stack:
        raise SaveToolError(f"XML lỗi: còn {len(stack)} tag chưa đóng")
    return result


def find_unique_direct_child(
    xml: bytes,
    tag: str,
    parent_tag: str = "root",
) -> XmlElementSpan:
    matches = [span for span in direct_child_spans(xml, parent_tag) if span.tag == tag]
    if len(matches) != 1:
        raise SaveToolError(
            f"<{parent_tag}> cần đúng 1 con trực tiếp <{tag}>, "
            f"tìm thấy {len(matches)}"
        )
    return matches[0]


def get_direct_child_block(
    xml: bytes,
    tag: str,
    parent_tag: str = "root",
) -> bytes:
    span = find_unique_direct_child(xml, tag, parent_tag)
    return xml[span.start:span.end]


def replace_direct_child_block(
    xml: bytes,
    tag: str,
    replacement: bytes,
    parent_tag: str = "root",
) -> bytes:
    span = find_unique_direct_child(xml, tag, parent_tag)
    return xml[:span.start] + replacement + xml[span.end:]


def get_nested_child_block(
    xml: bytes,
    container_tag: str,
    child_tag: str,
) -> bytes:
    container = get_direct_child_block(xml, container_tag, "root")
    return get_direct_child_block(container, child_tag, container_tag)


def replace_nested_child_block(
    xml: bytes,
    container_tag: str,
    child_tag: str,
    replacement: bytes,
) -> bytes:
    container_span = find_unique_direct_child(xml, container_tag, "root")
    container = xml[container_span.start:container_span.end]
    updated_container = replace_direct_child_block(
        container, child_tag, replacement, container_tag
    )
    return xml[:container_span.start] + updated_container + xml[container_span.end:]


def count_layout_objects(xml: bytes, path: str) -> dict[str, int]:
    root = validate_xml_document(xml, path)
    if path == "city":
        ground = root.find("TownGround")
        buildings = root.find("Buildings")
    elif path == "zoo":
        zoo = root.find("Zoo")
        ground = zoo.find("TownGround") if zoo is not None else None
        buildings = zoo.find("Buildings") if zoo is not None else None
    elif path == "stash":
        ground = None
        buildings = root.find("BuildingsStash")
    else:
        raise SaveToolError(f"Layout path không hợp lệ: {path}")

    if buildings is None:
        raise SaveToolError(f"Không tìm thấy Buildings cho {path}")
    rows = len(ground.findall("row")) if ground is not None else 0
    objects = len(buildings.findall("Object"))
    entries = len(list(buildings))

    invalid_json = 0
    store_ids: set[str] = set()
    bids: list[str] = []
    for obj in buildings.findall("Object"):
        raw = obj.get("data")
        if not raw:
            invalid_json += 1
            continue
        try:
            data = json.loads(raw)
        except Exception:
            invalid_json += 1
            continue
        store_id = data.get("storeId")
        if isinstance(store_id, str):
            store_ids.add(store_id)
        bid = data.get("bid")
        if isinstance(bid, str):
            bids.append(bid)

    if invalid_json:
        raise SaveToolError(
            f"{path}: có {invalid_json}/{objects} Object chứa JSON lỗi"
        )

    return {
        "rows": rows,
        "entries": entries,
        "objects": objects,
        "store_ids": len(store_ids),
        "duplicate_bids": len(bids) - len(set(bids)),
    }


def load_friend_donor(path: Path) -> bytes:
    if not path.is_file():
        raise SaveToolError(f"Không tìm thấy XML donor: {path}")
    raw = path.read_bytes().rstrip(b"\x00")
    donor = canonical_xml(raw)
    validate_xml_document(donor, "XML donor")

    # Các block tối thiểu cần tồn tại để donor được coi là city capture hợp lệ.
    get_direct_child_block(donor, "TownGround")
    get_direct_child_block(donor, "Buildings")
    return donor


def clone_friend_layout(
    target_xml: bytes,
    donor_xml: bytes,
    mode: str,
) -> tuple[bytes, list[str], dict[str, dict[str, int]]]:
    if mode not in {"city", "zoo", "stash", "all"}:
        raise SaveToolError(f"Chế độ clone không hợp lệ: {mode}")

    target = canonical_xml(target_xml)
    donor = canonical_xml(donor_xml)
    changed: list[str] = []

    before = {
        "city": count_layout_objects(target, "city"),
        "zoo": count_layout_objects(target, "zoo"),
        "stash": count_layout_objects(target, "stash"),
    }
    donor_stats = {
        "city": count_layout_objects(donor, "city"),
        "zoo": count_layout_objects(donor, "zoo"),
        "stash": count_layout_objects(donor, "stash"),
    }

    if mode in {"city", "all"}:
        target = replace_direct_child_block(
            target, "TownGround", get_direct_child_block(donor, "TownGround")
        )
        target = replace_direct_child_block(
            target, "Buildings", get_direct_child_block(donor, "Buildings")
        )
        changed.extend(["root/TownGround", "root/Buildings"])

    if mode in {"zoo", "all"}:
        target = replace_nested_child_block(
            target, "Zoo", "TownGround",
            get_nested_child_block(donor, "Zoo", "TownGround"),
        )
        target = replace_nested_child_block(
            target, "Zoo", "Buildings",
            get_nested_child_block(donor, "Zoo", "Buildings"),
        )
        changed.extend(["root/Zoo/TownGround", "root/Zoo/Buildings"])

    if mode in {"stash", "all"}:
        target = replace_direct_child_block(
            target,
            "BuildingsStash",
            get_direct_child_block(donor, "BuildingsStash"),
        )
        changed.append("root/BuildingsStash")

    validate_xml_document(target, "XML sau clone")
    after = {
        "city": count_layout_objects(target, "city"),
        "zoo": count_layout_objects(target, "zoo"),
        "stash": count_layout_objects(target, "stash"),
    }

    for key in ("city", "zoo", "stash"):
        if mode == "all" or mode == key:
            if after[key] != donor_stats[key]:
                raise SaveToolError(
                    f"Xác minh clone {key} thất bại: "
                    f"after={after[key]}, donor={donor_stats[key]}"
                )
        else:
            if after[key] != before[key]:
                raise SaveToolError(
                    f"Block không được chọn đã thay đổi ngoài ý muốn: {key}"
                )

    stats = {
        "target_before": before,
        "donor": donor_stats,
        "target_after": after,
    }
    return target, changed, stats


def choose_clone_mode() -> str:
    print("\n--- Chế độ sao chép ---")
    print("1. City layout: TownGround + Buildings")
    print("2. Zoo layout: Zoo/TownGround + Zoo/Buildings")
    print("3. BuildingsStash")
    print("4. All: City + Zoo + Stash")
    mapping = {"1": "city", "2": "zoo", "3": "stash", "4": "all"}
    choice = input("Chọn: ").strip()
    mode = mapping.get(choice)
    if mode is None:
        raise SaveToolError("Lựa chọn clone không hợp lệ")
    return mode


def clone_friend_city_prompt() -> None:
    SESSION.require_loaded()
    assert SESSION.current_xml is not None

    default = str(DONOR_FILE) if DONOR_FILE.is_file() else ""
    prompt = "Đường dẫn friend_city_*.xml"
    if default:
        prompt += f" [Enter = {default}]"
    prompt += ": "

    raw_path = input(prompt).strip().strip('"')
    donor_path = Path(raw_path) if raw_path else DONOR_FILE
    donor_xml = load_friend_donor(donor_path)
    mode = choose_clone_mode()

    new_xml, changed, stats = clone_friend_layout(
        SESSION.current_xml, donor_xml, mode
    )

    print("\n--- Báo cáo dự kiến ---")
    print("Donor :", donor_path)
    print("Mode  :", mode)
    print("Blocks:", ", ".join(changed))
    print("Target trước:", stats["target_before"])
    print("Donor       :", stats["donor"])
    print("Target sau  :", stats["target_after"])
    print("\nLưu ý: chế độ City/All thay cả Buildings, gồm decor và công trình.")

    if not ask_yes_no("Áp dụng vào XML làm việc?"):
        print("Đã hủy, chưa thay đổi XML.")
        return

    SESSION.apply_xml(new_xml)
    shutil.copy2(donor_path, DONOR_FILE)
    report = (
        f"Time: {datetime.now().isoformat(timespec='seconds')}\n"
        f"Donor: {donor_path}\n"
        f"Mode: {mode}\n"
        f"Changed: {', '.join(changed)}\n"
        f"Target before: {stats['target_before']}\n"
        f"Donor: {stats['donor']}\n"
        f"Target after: {stats['target_after']}\n"
    )
    atomic_write(CLONE_REPORT_FILE, report.encode("utf-8"))
    print("Đã clone vào XML làm việc. Chưa ghi vào game.")
    print("Report:", CLONE_REPORT_FILE)


def inspect_friend_donor_prompt() -> None:
    raw_path = input("Đường dẫn friend_city_*.xml: ").strip().strip('"')
    donor_path = Path(raw_path)
    donor = load_friend_donor(donor_path)
    print("\n--- Thống kê donor ---")
    print("City :", count_layout_objects(donor, "city"))
    print("Zoo  :", count_layout_objects(donor, "zoo"))
    print("Stash:", count_layout_objects(donor, "stash"))
    print("SHA-256:", sha256_bytes(donor))



# =============================================================================
# LOCALINFO + FRIEND MANAGER
# =============================================================================
FRIEND_GROUPS = (
    "FollowedFriends",
    "Followers",
    "RandomFriends",
    "LastRandomFriends",
    "LastHelpFriends",
    "LastHelp",
    "LastHelpers",
    "ClanMembers",
    "NewFriends",
)


@dataclass
class FriendProfile:
    city_id: str
    city_name: str = ""
    level: int = 0
    xp: int = 0
    likes: int = 0
    fver: str = ""
    lang: str = ""
    pic: str = ""
    fetched_city_ver: int = 0
    groups: list[str] | None = None

    def to_dict(self) -> dict[str, Any]:
        return {
            "city_id": self.city_id,
            "city_name": self.city_name,
            "level": self.level,
            "xp": self.xp,
            "likes": self.likes,
            "fver": self.fver,
            "lang": self.lang,
            "pic": self.pic,
            "fetched_city_ver": self.fetched_city_ver,
            "groups": list(self.groups or []),
        }


def safe_int(value: str | None, default: int = 0) -> int:
    try:
        return int(value or default)
    except (TypeError, ValueError):
        return default


def parse_localinfo_metadata(
    xml: bytes,
) -> tuple[dict[str, str], dict[str, FriendProfile]]:
    try:
        root = ET.fromstring(canonical_xml(xml))
    except ET.ParseError as exc:
        raise SaveToolError(f"LocalInfo XML lỗi: {exc}") from exc

    version = root.find("Version")
    aws = root.find("AWS")
    metadata = {
        "version": version.get("version", "") if version is not None else "",
        "fver": version.get("FVer", "") if version is not None else "",
        "game_id": version.get("gameId", "") if version is not None else "",
        "own_city_id": aws.get("cityId", "") if aws is not None else "",
        "token": aws.get("token", "") if aws is not None else "",
    }

    friends: dict[str, FriendProfile] = {}
    for group_name in FRIEND_GROUPS:
        group = root.find(group_name)
        if group is None:
            continue
        for node in group.findall("friend"):
            city_id = (node.get("city_id") or "").strip()
            if not city_id:
                continue

            profile = friends.get(city_id)
            if profile is None:
                profile = FriendProfile(city_id=city_id, groups=[])
                friends[city_id] = profile

            if group_name not in (profile.groups or []):
                assert profile.groups is not None
                profile.groups.append(group_name)

            # Prefer non-empty/newer values when the same friend appears in many groups.
            profile.city_name = node.get("city_name") or profile.city_name
            profile.level = max(profile.level, safe_int(node.get("level")))
            profile.xp = max(profile.xp, safe_int(node.get("xp")))
            profile.likes = max(profile.likes, safe_int(node.get("likes")))
            profile.fver = node.get("fver") or profile.fver
            profile.lang = node.get("lang") or profile.lang
            profile.pic = node.get("pic") or profile.pic
            profile.fetched_city_ver = max(
                profile.fetched_city_ver,
                safe_int(node.get("fetched_city_ver")),
            )

    return metadata, friends


def pull_localinfo_from_device() -> bytes:
    check_device()
    remote_temp = f"/data/local/tmp/ts_localinfo_{uuid.uuid4().hex}.bin"
    try:
        root_shell(
            f"cp {shell_quote(REMOTE_LOCALINFO)} {shell_quote(remote_temp)} && "
            f"chmod 0644 {shell_quote(remote_temp)}"
        )
        WORK_DIR.mkdir(parents=True, exist_ok=True)
        adb("pull", remote_temp, str(LOCALINFO_SOURCE_FILE), timeout=120)
    finally:
        root_shell(f"rm -f {shell_quote(remote_temp)}", check=False)

    data = LOCALINFO_SOURCE_FILE.read_bytes()
    if not data:
        raise SaveToolError("LocalInfo pull về bị rỗng")
    return data


def display_friend_table(items: list[FriendProfile], limit: int | None = None) -> None:
    shown = items if limit is None else items[:limit]
    print("\n STT | Level | Tên thành phố                     | city_id     | Nhóm")
    print("-" * 92)
    for index, friend in enumerate(shown, 1):
        groups = ",".join(friend.groups or [])
        print(
            f"{index:4} | {friend.level:5} | "
            f"{friend.city_name[:32]:32} | {friend.city_id:11} | {groups}"
        )
    if limit is not None and len(items) > limit:
        print(f"... còn {len(items) - limit} kết quả")


def friend_sort_key(friend: FriendProfile) -> tuple[str, int, str]:
    return (friend.city_name.casefold(), -friend.level, friend.city_id)



# =============================================================================
# FRIEND-OF-FRIEND NETWORK DISCOVERY
# =============================================================================
CITY_ID_KEY_NAMES = {
    "cityid",
    "city_id",
    "fetchcityid",
    "fetch_city_id",
    "friendcityid",
    "friend_city_id",
    "ownercityid",
    "owner_city_id",
}

RELATION_HINTS = (
    "friend",
    "honor",
    "follower",
    "followed",
    "helper",
    "visitor",
    "neighbor",
    "neighbour",
    "clan",
    "member",
    "social",
)

CITY_ID_VALUE_RE = re.compile(r"^[A-Za-z0-9_-]{3,64}$")


@dataclass(frozen=True)
class NetworkEdge:
    source_city_id: str
    target_city_id: str
    depth: int
    relation: str
    evidence: str

    def to_dict(self) -> dict[str, Any]:
        return {
            "source_city_id": self.source_city_id,
            "target_city_id": self.target_city_id,
            "depth": self.depth,
            "relation": self.relation,
            "evidence": self.evidence,
        }


def _normalize_city_id_key(key: str) -> str:
    return re.sub(r"[^a-z0-9_]", "", key.casefold())


def _looks_like_city_id(value: Any) -> bool:
    if not isinstance(value, str):
        return False
    value = value.strip()
    return bool(value and CITY_ID_VALUE_RE.fullmatch(value))


def _relation_from_context(context: str) -> str:
    lowered = context.casefold()
    for hint in RELATION_HINTS:
        if hint in lowered:
            return hint
    return "unknown"


def _scan_json_for_city_ids(
    value: Any,
    context: str,
    found: list[tuple[str, str, str]],
) -> None:
    if isinstance(value, dict):
        for key, child in value.items():
            child_context = f"{context}/{key}"
            normalized = _normalize_city_id_key(str(key))
            if normalized in CITY_ID_KEY_NAMES and _looks_like_city_id(child):
                city_id = str(child).strip()
                found.append((city_id, _relation_from_context(child_context), child_context))
            _scan_json_for_city_ids(child, child_context, found)
    elif isinstance(value, list):
        for index, child in enumerate(value):
            _scan_json_for_city_ids(child, f"{context}[{index}]", found)


def extract_related_city_ids(xml: bytes) -> list[tuple[str, str, str]]:
    """
    Return candidate related city IDs as:
        (city_id, relation, evidence)

    This is intentionally conservative:
    - only fields whose key semantically means city_id are accepted;
    - values must look like compact Township identifiers;
    - JSON embedded in XML attributes/text is scanned recursively.
    """
    root = validate_xml_document(xml, "Friend network donor")
    found: list[tuple[str, str, str]] = []

    def walk(node: ET.Element, path: str) -> None:
        current = f"{path}/{node.tag}"

        for key, raw_value in node.attrib.items():
            normalized = _normalize_city_id_key(key)
            if normalized in CITY_ID_KEY_NAMES and _looks_like_city_id(raw_value):
                found.append((
                    raw_value.strip(),
                    _relation_from_context(current),
                    f"{current}/@{key}",
                ))

            stripped = raw_value.strip()
            if stripped.startswith("{") or stripped.startswith("["):
                try:
                    obj = json.loads(stripped)
                except Exception:
                    obj = None
                if obj is not None:
                    _scan_json_for_city_ids(obj, f"{current}/@{key}", found)

        if node.text:
            stripped = node.text.strip()
            if stripped.startswith("{") or stripped.startswith("["):
                try:
                    obj = json.loads(stripped)
                except Exception:
                    obj = None
                if obj is not None:
                    _scan_json_for_city_ids(obj, f"{current}/#text", found)

        for child in list(node):
            walk(child, current)

    walk(root, "")

    # Deduplicate by (id, evidence) while preserving order.
    result: list[tuple[str, str, str]] = []
    seen: set[tuple[str, str]] = set()
    for city_id, relation, evidence in found:
        key = (city_id, evidence)
        if key in seen:
            continue
        seen.add(key)
        result.append((city_id, relation, evidence))
    return result


def inspect_network_ids_prompt() -> None:
    raw_path = input("Đường dẫn friend_city.xml / friend_honor.xml: ").strip().strip('"')
    path = Path(raw_path)
    if not path.is_file():
        raise SaveToolError(f"Không tìm thấy file: {path}")
    raw = path.read_bytes().rstrip(b"\x00")
    xml = canonical_xml(raw)
    validate_xml_document(xml, path.name)

    found = extract_related_city_ids(xml)
    print(f"\nTìm thấy {len(found)} dấu vết city_id.")
    if not found:
        print("Chưa thấy city_id liên quan theo các trường city_id/cityId đã xác minh.")
        return

    print(" STT | city_id                         | relation   | evidence")
    print("-" * 110)
    for index, (city_id, relation, evidence) in enumerate(found, 1):
        print(f"{index:4} | {city_id[:31]:31} | {relation[:10]:10} | {evidence}")



LEVEL_KEY_NAMES = {
    "level", "lvl", "citylevel", "city_level", "playerlevel", "player_level",
}

LEVEL_VAR_NAMES = {
    "level", "citylevel", "playerlevel", "currentlevel",
}


def _valid_level(value: Any) -> int | None:
    try:
        level = int(str(value).strip())
    except (TypeError, ValueError):
        return None
    return level if 1 <= level <= 100000 else None


def _scan_json_for_levels(value: Any, context: str, found: list[tuple[int, str]]) -> None:
    if isinstance(value, dict):
        for key, child in value.items():
            child_context = f"{context}/{key}"
            normalized = _normalize_city_id_key(str(key))
            if normalized in LEVEL_KEY_NAMES:
                level = _valid_level(child)
                if level is not None:
                    found.append((level, child_context))
            _scan_json_for_levels(child, child_context, found)
    elif isinstance(value, list):
        for index, child in enumerate(value):
            _scan_json_for_levels(child, f"{context}[{index}]", found)


def extract_city_level(xml: bytes) -> tuple[int, str, list[tuple[int, str]]]:
    root = validate_xml_document(xml, "FetchCity level scan")
    candidates: list[tuple[int, int, str]] = []

    def add(level: int | None, priority: int, evidence: str) -> None:
        if level is not None:
            candidates.append((priority, level, evidence))

    def walk(node: ET.Element, path: str) -> None:
        current = f"{path}/{node.tag}"

        if node.tag.casefold() == "var":
            var_name = (node.get("name") or "").strip()
            normalized_name = _normalize_city_id_key(var_name)
            if normalized_name in LEVEL_VAR_NAMES:
                for attr_name in ("v", "value", "val"):
                    if node.get(attr_name) is not None:
                        add(
                            _valid_level(node.get(attr_name)),
                            0,
                            f'{current}[@name="{var_name}"]/@{attr_name}',
                        )

        for key, raw_value in node.attrib.items():
            normalized = _normalize_city_id_key(key)
            if normalized in LEVEL_KEY_NAMES:
                add(_valid_level(raw_value), 1, f"{current}/@{key}")

            stripped = raw_value.strip()
            if stripped.startswith("{") or stripped.startswith("["):
                try:
                    obj = json.loads(stripped)
                except Exception:
                    obj = None
                if obj is not None:
                    found: list[tuple[int, str]] = []
                    _scan_json_for_levels(obj, f"{current}/@{key}", found)
                    for level, evidence in found:
                        add(level, 2, evidence)

        if node.text:
            stripped = node.text.strip()
            if stripped.startswith("{") or stripped.startswith("["):
                try:
                    obj = json.loads(stripped)
                except Exception:
                    obj = None
                if obj is not None:
                    found: list[tuple[int, str]] = []
                    _scan_json_for_levels(obj, f"{current}/#text", found)
                    for level, evidence in found:
                        add(level, 2, evidence)

        for child in list(node):
            walk(child, current)

    walk(root, "")

    if not candidates:
        return 0, "", []

    min_priority = min(p for p, _, _ in candidates)
    strongest = [(level, evidence) for p, level, evidence in candidates if p == min_priority]

    counts: dict[int, int] = {}
    for level, _ in strongest:
        counts[level] = counts.get(level, 0) + 1
    selected = max(counts, key=lambda lv: counts[lv])
    evidence = next(ev for lv, ev in strongest if lv == selected)
    all_candidates = [(level, ev) for _, level, ev in candidates]
    return selected, evidence, all_candidates


def _parse_level_filter(raw: str) -> tuple[str, int, int | None]:
    value = raw.strip().replace(" ", "")
    if not value:
        return ">=", 1, None

    m = re.fullmatch(r"(>=|<=|>|<|=)?(\d+)", value)
    if m:
        return m.group(1) or "=", int(m.group(2)), None

    m = re.fullmatch(r"(\d+)-(\d+)", value)
    if m:
        low, high = int(m.group(1)), int(m.group(2))
        if low > high:
            low, high = high, low
        return "range", low, high

    raise SaveToolError(
        "Điều kiện level không hợp lệ. Ví dụ: >100, >=100, =100 hoặc 100-200"
    )


def _level_matches(level: int, op: str, value: int, high: int | None) -> bool:
    if level <= 0:
        return False
    if op == ">":
        return level > value
    if op == ">=":
        return level >= value
    if op == "<":
        return level < value
    if op == "<=":
        return level <= value
    if op == "=":
        return level == value
    if op == "range":
        assert high is not None
        return value <= level <= high
    return False


def _save_level_matches(
    nodes: dict[str, dict[str, Any]],
    op: str,
    value: int,
    high: int | None,
) -> int:
    matches: list[dict[str, Any]] = []

    for city_id, node in nodes.items():
        level = safe_int(str(node.get("level", 0)))
        if _level_matches(level, op, value, high):
            matches.append({
                "city_id": city_id,
                "city_name": node.get("city_name", ""),
                "level": level,
                "depth": safe_int(str(node.get("depth", 0))),
                "source_city_id": node.get("source_city_id", ""),
                "relation": node.get("relation", ""),
                "fetched": bool(node.get("fetched", False)),
                "level_evidence": node.get("level_evidence", ""),
            })

    matches.sort(key=lambda item: (-item["level"], item["city_name"], item["city_id"]))
    condition = f"{value}-{high}" if op == "range" else f"{op}{value}"

    atomic_write(
        FRIEND_NETWORK_MATCHES_JSON,
        json.dumps(
            {"condition": condition, "count": len(matches), "matches": matches},
            ensure_ascii=False,
            indent=2,
        ).encode("utf-8"),
    )

    lines = [
        "city_id\tcity_name\tlevel\tdepth\tsource_city_id\trelation\tfetched\tlevel_evidence"
    ]
    for item in matches:
        fields = [
            item["city_id"],
            str(item["city_name"]).replace("\t", " "),
            str(item["level"]),
            str(item["depth"]),
            str(item["source_city_id"]),
            str(item["relation"]),
            "1" if item["fetched"] else "0",
            str(item["level_evidence"]).replace("\t", " ").replace("\n", " "),
        ]
        lines.append("\t".join(fields))

    atomic_write(
        FRIEND_NETWORK_MATCHES_TSV,
        ("\n".join(lines) + "\n").encode("utf-8"),
    )
    return len(matches)


def _save_network_results(
    nodes: dict[str, dict[str, Any]],
    edges: list[NetworkEdge],
    settings: dict[str, Any],
) -> None:
    FRIEND_NETWORK_DIR.mkdir(parents=True, exist_ok=True)

    payload = {
        "generated_at": datetime.now().isoformat(timespec="seconds"),
        "settings": settings,
        "node_count": len(nodes),
        "edge_count": len(edges),
        "nodes": nodes,
        "edges": [edge.to_dict() for edge in edges],
    }
    atomic_write(
        FRIEND_NETWORK_JSON,
        json.dumps(payload, ensure_ascii=False, indent=2).encode("utf-8"),
    )

    lines = ["source_city_id\ttarget_city_id\tdepth\trelation\tevidence"]
    for edge in edges:
        safe_evidence = edge.evidence.replace("\t", " ").replace("\r", " ").replace("\n", " ")
        lines.append(
            f"{edge.source_city_id}\t{edge.target_city_id}\t{edge.depth}\t"
            f"{edge.relation}\t{safe_evidence}"
        )
    atomic_write(
        FRIEND_NETWORK_EDGES,
        ("\n".join(lines) + "\n").encode("utf-8"),
    )



def _count_level_matches(
    nodes: dict[str, dict[str, Any]],
    op: str,
    value: int,
    high: int | None,
) -> int:
    count = 0
    for node in nodes.values():
        level = safe_int(str(node.get("level", 0)))
        if _level_matches(level, op, value, high):
            count += 1
    return count


def crawl_friend_network_prompt() -> None:
    if not SESSION.friends:
        raise SaveToolError("Chưa có danh sách bạn bè. Tải LocalInfo trước.")
    if not SESSION.localinfo_meta:
        raise SaveToolError("Chưa đọc metadata LocalInfo")

    bver = SESSION.localinfo_meta.get("version", "")
    fver = SESSION.localinfo_meta.get("fver", "")
    own_city_id = SESSION.localinfo_meta.get("own_city_id", "").strip()
    if not bver or not fver:
        raise SaveToolError("LocalInfo thiếu Version/version hoặc Version/FVer")

    print("\nKiểu quét Friend Network:")
    print("1. Sequential - cố định, dễ lập danh sách ổn định")
    print("2. Random     - xáo trộn nhánh, tăng độ đa dạng mỗi lần chạy")
    scan_choice = input("Chọn kiểu quét [1]: ").strip() or "1"
    scan_mode = {"1": "sequential", "2": "random"}.get(scan_choice)
    if scan_mode is None:
        raise SaveToolError("Kiểu quét không hợp lệ")

    max_depth = parse_int(
        input("Độ sâu tối đa [2]: ").strip() or "2",
        "Độ sâu",
        1,
        10,
    )
    target_matches = parse_int(
        input("Số tài khoản cần tìm đủ điều kiện [100]: ").strip() or "100",
        "Số tài khoản mục tiêu",
        1,
        100000,
    )

    safety_max_fetches = parse_int(
        input("Giới hạn FetchCity an toàn [5000]: ").strip() or "5000",
        "Giới hạn FetchCity an toàn",
        target_matches,
        100000,
    )

    level_filter_raw = input(
        "Điều kiện level cần lấy [>100] (vd >100, >=150, 100-200): "
    ).strip() or ">100"
    level_op, level_value, level_high = _parse_level_filter(level_filter_raw)

    delay_raw = input("Nghỉ giữa các request, giây [0.5]: ").strip() or "0.5"
    try:
        request_delay = float(delay_raw)
    except ValueError as exc:
        raise SaveToolError("Delay phải là số") from exc
    if not 0 <= request_delay <= 60:
        raise SaveToolError("Delay phải từ 0 đến 60 giây")

    direct_friends = sorted(SESSION.friends.values(), key=friend_sort_key)
    if scan_mode == "random":
        random.shuffle(direct_friends)
    print("\n--- Friend Network crawler ---")
    print("Seed trực tiếp :", len(direct_friends))
    print("Scan mode      :", scan_mode)
    print("Deduplicate    : ON (global cityId)")
    print("Max depth      :", max_depth)
    print("Target matches :", target_matches)
    print("Safety Fetch   :", safety_max_fetches)
    print("Level filter   :", level_filter_raw)
    print("Delay          :", request_delay, "giây")
    print("Output         :", FRIEND_NETWORK_DIR)
    if not ask_yes_no("Bắt đầu quét mạng bạn-bè-của-bạn?"):
        print("Đã hủy.")
        return

    FRIEND_NETWORK_DIR.mkdir(parents=True, exist_ok=True)

    queue: deque[tuple[str, int, str]] = deque()
    nodes: dict[str, dict[str, Any]] = {}
    edges: list[NetworkEdge] = []
    queued: set[str] = set()
    fetched: set[str] = set()
    failed: dict[str, str] = {}

    if own_city_id:
        nodes[own_city_id] = {
            "city_id": own_city_id,
            "depth": 0,
            "source_city_id": "",
            "relation": "self",
            "fetched": False,
        }

    for profile in direct_friends:
        cid = profile.city_id.strip()
        # Global cityId deduplication: a direct friend appearing in several
        # LocalInfo groups is queued only once.
        if not cid or cid == own_city_id or cid in queued:
            continue
        queued.add(cid)
        queue.append((cid, 1, own_city_id))
        nodes[cid] = {
            **profile.to_dict(),
            "depth": 1,
            "source_city_id": own_city_id,
            "relation": "direct",
            "fetched": False,
        }
        if own_city_id:
            edges.append(NetworkEdge(
                source_city_id=own_city_id,
                target_city_id=cid,
                depth=1,
                relation="direct",
                evidence="LocalInfo",
            ))

    fetch_count = 0
    while queue and fetch_count < safety_max_fetches:
        city_id, depth, parent_city_id = queue.popleft()
        if city_id in fetched:
            continue
        if depth > max_depth:
            continue

        fetch_count += 1
        current_matches = _count_level_matches(
            nodes, level_op, level_value, level_high
        )
        print(
            f"[fetch={fetch_count}/{safety_max_fetches}] "
            f"matches={current_matches}/{target_matches} "
            f"depth={depth} FetchCity {city_id} "
            f"(queue={len(queue)}, found={len(nodes)})"
        )

        out_dir = FRIEND_NETWORK_DIR / "cities" / city_id
        profile = SESSION.friends.get(city_id) if SESSION.friends else None
        city_ver = profile.fetched_city_ver if profile is not None else 0

        try:
            donor, response_obj, response_city_ver = fetch_city_live(
                city_id,
                bver,
                fver,
                city_ver,
                out_dir=out_dir,
            )
            fetched.add(city_id)
            nodes.setdefault(city_id, {"city_id": city_id, "depth": depth})
            nodes[city_id]["fetched"] = True
            nodes[city_id]["response_city_ver"] = response_city_ver

            fetched_level, level_evidence, level_candidates = extract_city_level(donor)
            existing_level = safe_int(str(nodes[city_id].get("level", 0)))

            if fetched_level > 0:
                nodes[city_id]["level"] = fetched_level
                nodes[city_id]["level_evidence"] = level_evidence
                nodes[city_id]["level_candidates"] = [
                    {"level": lv, "evidence": ev}
                    for lv, ev in level_candidates[:50]
                ]
            elif existing_level > 0:
                nodes[city_id]["level"] = existing_level
                nodes[city_id]["level_evidence"] = "LocalInfo"
            else:
                nodes[city_id]["level"] = 0
                nodes[city_id]["level_evidence"] = ""

            print(
                "  -> level:",
                nodes[city_id].get("level", 0) or "?",
                "| match:",
                "YES" if _level_matches(
                    safe_int(str(nodes[city_id].get("level", 0))),
                    level_op,
                    level_value,
                    level_high,
                ) else "no",
            )

            candidates = extract_related_city_ids(donor)

            # Sequential mode is deterministic; Random mode explores different
            # branches on different runs. Global deduplication below still
            # guarantees that the same cityId is fetched at most once per run.
            if scan_mode == "sequential":
                candidates = sorted(
                    candidates,
                    key=lambda item: (item[0], item[1], item[2]),
                )
            else:
                random.shuffle(candidates)

            nodes[city_id]["candidate_city_ids"] = len(candidates)

            discovered_here: set[str] = set()
            for target_id, relation, evidence in candidates:
                target_id = target_id.strip()
                if (
                    not target_id
                    or target_id == city_id
                    or target_id == own_city_id
                    or target_id in discovered_here
                ):
                    continue
                discovered_here.add(target_id)

                target_depth = depth + 1
                edges.append(NetworkEdge(
                    source_city_id=city_id,
                    target_city_id=target_id,
                    depth=target_depth,
                    relation=relation,
                    evidence=evidence,
                ))

                existing = nodes.get(target_id)
                if existing is None or target_depth < int(existing.get("depth", 999999)):
                    nodes[target_id] = {
                        "city_id": target_id,
                        "depth": target_depth,
                        "source_city_id": city_id,
                        "relation": relation,
                        "level": 0,
                        "fetched": target_id in fetched,
                    }

                # Global deduplication across all parents/depth branches.
                # If A and B both reference X, X is fetched only once.
                if (
                    target_depth <= max_depth
                    and target_id not in queued
                    and target_id not in fetched
                ):
                    queued.add(target_id)
                    queue.append((target_id, target_depth, city_id))

            atomic_write(
                out_dir / "discovered_city_ids.json",
                json.dumps(
                    [
                        {
                            "city_id": cid,
                            "relation": relation,
                            "evidence": evidence,
                        }
                        for cid, relation, evidence in candidates
                    ],
                    ensure_ascii=False,
                    indent=2,
                ).encode("utf-8"),
            )

        except Exception as exc:
            failed[city_id] = f"{type(exc).__name__}: {exc}"
            nodes.setdefault(city_id, {"city_id": city_id, "depth": depth})
            nodes[city_id]["fetched"] = False
            nodes[city_id]["error"] = failed[city_id]
            print("  -> ERROR:", failed[city_id])

        current_matches = _count_level_matches(
            nodes, level_op, level_value, level_high
        )

        settings = {
            "scan_mode": scan_mode,
            "deduplicate_city_id": True,
            "max_depth": max_depth,
            "target_matches": target_matches,
            "safety_max_fetches": safety_max_fetches,
            "request_delay": request_delay,
            "bver": bver,
            "fver": fver,
            "own_city_id": own_city_id,
            "level_filter": level_filter_raw,
            "fetch_count": fetch_count,
            "fetched_ok": len(fetched),
            "failed": len(failed),
        }
        _save_network_results(nodes, edges, settings)
        _save_level_matches(nodes, level_op, level_value, level_high)

        if current_matches >= target_matches:
            print(
                f"\nĐã tìm đủ {current_matches}/{target_matches} tài khoản "
                f"thỏa điều kiện {level_filter_raw}. Dừng quét."
            )
            break

        if queue and request_delay > 0:
            time.sleep(request_delay)

    settings = {
        "scan_mode": scan_mode,
        "deduplicate_city_id": True,
        "max_depth": max_depth,
        "target_matches": target_matches,
        "safety_max_fetches": safety_max_fetches,
        "request_delay": request_delay,
        "bver": bver,
        "fver": fver,
        "own_city_id": own_city_id,
        "level_filter": level_filter_raw,
        "fetch_count": fetch_count,
        "fetched_ok": len(fetched),
        "failed": len(failed),
        "remaining_queue": len(queue),
    }
    _save_network_results(nodes, edges, settings)
    match_count = _save_level_matches(nodes, level_op, level_value, level_high)

    depth_counts: dict[int, int] = {}
    for node in nodes.values():
        depth_value = safe_int(str(node.get("depth", 0)))
        depth_counts[depth_value] = depth_counts.get(depth_value, 0) + 1

    print("\n--- KẾT QUẢ ---")
    print("Scan mode    :", scan_mode)
    print("Deduplicate  : ON")
    print("Nodes        :", len(nodes))
    print("Edges        :", len(edges))
    print("Fetch OK     :", len(fetched))
    print("Fetch lỗi    :", len(failed))
    print("Còn trong Q  :", len(queue))
    print("Theo depth   :", dict(sorted(depth_counts.items())))
    print("Khớp level   :", match_count, "/", target_matches, "| điều kiện:", level_filter_raw)
    if match_count >= target_matches:
        print("Trạng thái    : Đã đạt đủ mục tiêu")
    elif not queue:
        print("Trạng thái    : Hết queue trước khi đủ mục tiêu")
    elif fetch_count >= safety_max_fetches:
        print("Trạng thái    : Chạm giới hạn FetchCity an toàn")
    print("Network JSON :", FRIEND_NETWORK_JSON)
    print("Edges TSV    :", FRIEND_NETWORK_EDGES)
    print("Matches JSON :", FRIEND_NETWORK_MATCHES_JSON)
    print("Matches TSV  :", FRIEND_NETWORK_MATCHES_TSV)

# =============================================================================
# FILE + ADB + ROOT
# =============================================================================
def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def atomic_write(path: Path, data: bytes) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_name(f".{path.name}.{uuid.uuid4().hex}.tmp")
    temporary.write_bytes(data)
    os.replace(temporary, path)


def shell_quote(value: str) -> str:
    return "'" + value.replace("'", "'\\''") + "'"


def run_process(command: list[str], timeout: int = 60) -> subprocess.CompletedProcess[str]:
    # Use temporary files instead of subprocess.PIPE to avoid bad descriptor issues
    # seen with some Python 3.14 + Windows console configurations.
    with tempfile.TemporaryFile(mode="w+b") as stdout_file, tempfile.TemporaryFile(
        mode="w+b"
    ) as stderr_file:
        completed = subprocess.run(
            command,
            stdin=subprocess.DEVNULL,
            stdout=stdout_file,
            stderr=stderr_file,
            timeout=timeout,
            check=False,
        )
        stdout_file.seek(0)
        stderr_file.seek(0)
        stdout = stdout_file.read().decode("utf-8", errors="replace")
        stderr = stderr_file.read().decode("utf-8", errors="replace")
    return subprocess.CompletedProcess(command, completed.returncode, stdout, stderr)


def adb(*args: str, timeout: int = 60, check: bool = True) -> subprocess.CompletedProcess[str]:
    if not ADB_PATH.is_file():
        raise SaveToolError(f"Không tìm thấy ADB: {ADB_PATH}")
    result = run_process([str(ADB_PATH), "-s", DEVICE_ID, *args], timeout=timeout)
    if check and result.returncode != 0:
        message = (result.stderr or result.stdout).strip()
        raise SaveToolError(f"ADB lỗi ({result.returncode}): {message}")
    return result


def adb_shell(command: str, timeout: int = 60, check: bool = True):
    return adb("shell", command, timeout=timeout, check=check)


ROOT_PREFIX: str | None = None


def detect_root_prefix() -> str:
    global ROOT_PREFIX
    if ROOT_PREFIX is not None:
        return ROOT_PREFIX
    variants = [
        "su 0 sh -c",
        "su -c",
        "su root sh -c",
    ]
    errors: list[str] = []
    for prefix in variants:
        command = f"{prefix} {shell_quote('id -u')}"
        result = adb_shell(command, check=False)
        output = (result.stdout + "\n" + result.stderr).strip()
        if result.returncode == 0 and re.search(r"(^|\s)0($|\s)", output):
            ROOT_PREFIX = prefix
            return prefix
        errors.append(f"{prefix}: {output or 'no output'}")
    raise SaveToolError("Không tìm được cú pháp root hoạt động:\n" + "\n".join(errors))


def root_shell(command: str, timeout: int = 60, check: bool = True):
    prefix = detect_root_prefix()
    return adb_shell(f"{prefix} {shell_quote(command)}", timeout=timeout, check=check)


def check_device() -> None:
    state = adb("get-state").stdout.strip()
    if state != "device":
        raise SaveToolError(f"Thiết bị {DEVICE_ID} chưa sẵn sàng: {state}")
    uid = root_shell("id -u").stdout.strip()
    if "0" not in uid.split():
        raise SaveToolError(f"Root chưa hoạt động, id -u trả về: {uid!r}")


def pull_save_from_device() -> bytes:
    check_device()
    adb_shell(f"am force-stop {shell_quote(PACKAGE_NAME)}")
    remote_temp = f"/data/local/tmp/ts_simple_{uuid.uuid4().hex}.bin"
    try:
        root_shell(
            f"cp {shell_quote(REMOTE_SAVE)} {shell_quote(remote_temp)} && "
            f"chmod 0644 {shell_quote(remote_temp)}"
        )
        WORK_DIR.mkdir(parents=True, exist_ok=True)
        adb("pull", remote_temp, str(SOURCE_FILE), timeout=120)
    finally:
        root_shell(f"rm -f {shell_quote(remote_temp)}", check=False)
    data = SOURCE_FILE.read_bytes()
    if not data:
        raise SaveToolError("File pull về bị rỗng")
    return data


def make_local_backup(source: bytes, label: str = "save") -> Path:
    BACKUP_DIR.mkdir(parents=True, exist_ok=True)
    timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
    path = BACKUP_DIR / f"{timestamp}_{label}.mGameInfo"
    atomic_write(path, source)
    return path


def write_save_to_device(encoded: bytes, original: bytes) -> tuple[Path, str]:
    if sha256_bytes(original) != sha256_bytes(SOURCE_FILE.read_bytes()):
        raise SaveToolError("Source trong workspace đã thay đổi; hãy tải lại save trước khi ghi")

    local_backup = make_local_backup(original, "before_write")
    atomic_write(OUTPUT_FILE, encoded)

    timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
    remote_upload = f"/data/local/tmp/ts_simple_{uuid.uuid4().hex}_output.bin"
    remote_new = REMOTE_SAVE + ".township_simple.new"
    remote_backup = REMOTE_SAVE + f".township_simple.{timestamp}.bak"

    # Read owner/group/mode before replacement.
    stat_result = root_shell(
        f"stat -c '%u %g %a' {shell_quote(REMOTE_SAVE)}"
    ).stdout.strip().splitlines()
    if not stat_result:
        raise SaveToolError("Không đọc được owner/mode của save gốc")
    parts = stat_result[-1].strip().split()
    if len(parts) != 3:
        raise SaveToolError(f"Kết quả stat không hợp lệ: {stat_result[-1]!r}")
    uid, gid, mode = parts

    try:
        adb("push", str(OUTPUT_FILE), remote_upload, timeout=120)
        root_shell(
            " && ".join(
                [
                    f"cp -p {shell_quote(REMOTE_SAVE)} {shell_quote(remote_backup)}",
                    f"cp {shell_quote(remote_upload)} {shell_quote(remote_new)}",
                    f"chown {uid}:{gid} {shell_quote(remote_new)}",
                    f"chmod {mode} {shell_quote(remote_new)}",
                    f"mv -f {shell_quote(remote_new)} {shell_quote(REMOTE_SAVE)}",
                    f"rm -f {shell_quote(remote_upload)}",
                ]
            ),
            timeout=120,
        )
    except Exception:
        root_shell(f"rm -f {shell_quote(remote_upload)} {shell_quote(remote_new)}", check=False)
        raise

    # Pull back and verify exact encoded bytes and decoded XML.
    readback_temp = f"/data/local/tmp/ts_simple_{uuid.uuid4().hex}_readback.bin"
    readback_local = WORK_DIR / "readback.mGameInfo"
    try:
        root_shell(
            f"cp {shell_quote(REMOTE_SAVE)} {shell_quote(readback_temp)} && "
            f"chmod 0644 {shell_quote(readback_temp)}"
        )
        adb("pull", readback_temp, str(readback_local), timeout=120)
    finally:
        root_shell(f"rm -f {shell_quote(readback_temp)}", check=False)

    readback = readback_local.read_bytes()
    if readback != encoded:
        raise SaveToolError(
            "File đọc lại không giống output. Backup trên thiết bị: " + remote_backup
        )
    return local_backup, remote_backup


def restore_local_backup(path: Path) -> None:
    backup = path.read_bytes()
    # A backup is already a complete container. Use the currently loaded source only
    # for the write safety/permission pipeline.
    write_save_to_device(backup, SOURCE_FILE.read_bytes())


# =============================================================================
# INTERACTIVE SESSION
# =============================================================================
@dataclass
class Session:
    original_container: bytes | None = None
    original_xml: bytes | None = None
    current_xml: bytes | None = None
    source_label: str = ""
    localinfo_container: bytes | None = None
    localinfo_xml: bytes | None = None
    pending_localinfo_xml: bytes | None = None
    pending_pair_templates: tuple[bytes,bytes] | None = None
    localinfo_meta: dict[str, str] | None = None
    friends: dict[str, FriendProfile] | None = None
    selected_friend: FriendProfile | None = None
    donor_xml: bytes | None = None
    donor_path: Path | None = None

    @property
    def loaded(self) -> bool:
        return self.original_container is not None and self.current_xml is not None

    @property
    def changed(self) -> bool:
        return self.loaded and (self.current_xml != self.original_xml or self.pending_localinfo_xml is not None)

    def require_loaded(self) -> None:
        if not self.loaded:
            raise SaveToolError("Chưa tải save. Chọn mục 1 trước.")

    def load_device(self) -> None:
        container = pull_save_from_device()
        xml = decode_save(container)

        localinfo_container = pull_localinfo_from_device()
        localinfo_xml = decode_save(localinfo_container)
        localinfo_meta, friends = parse_localinfo_metadata(localinfo_xml)

        atomic_write(DECODED_FILE, xml)
        atomic_write(MODIFIED_FILE, xml)
        atomic_write(LOCALINFO_DECODED_FILE, localinfo_xml)

        self.original_container = container
        self.original_xml = xml
        self.current_xml = xml
        self.source_label = f"LDPlayer {DEVICE_ID}"
        self.localinfo_container = localinfo_container
        self.localinfo_xml = localinfo_xml
        self.localinfo_meta = localinfo_meta
        self.friends = friends
        self.pending_localinfo_xml = None
        self.pending_pair_templates = None
        self.selected_friend = None
        self.donor_xml = None
        self.donor_path = None

    def load_local(self, path: Path) -> None:
        container = path.read_bytes()
        xml = decode_save(container)
        WORK_DIR.mkdir(parents=True, exist_ok=True)
        atomic_write(SOURCE_FILE, container)
        atomic_write(DECODED_FILE, xml)
        atomic_write(MODIFIED_FILE, xml)
        self.original_container = container
        self.original_xml = xml
        self.current_xml = xml
        self.source_label = str(path)
        self.localinfo_container = None
        self.localinfo_xml = None
        self.localinfo_meta = None
        self.friends = None
        self.pending_localinfo_xml = None
        self.pending_pair_templates = None
        self.selected_friend = None
        self.donor_xml = None
        self.donor_path = None

    def apply_xml(self, new_xml: bytes) -> None:
        self.current_xml = new_xml
        atomic_write(MODIFIED_FILE, new_xml)

    def encode_verify(self) -> bytes:
        self.require_loaded()
        assert self.original_container is not None
        assert self.current_xml is not None
        template = self.pending_pair_templates[0] if self.pending_pair_templates is not None else self.original_container
        encoded = encode_save(self.current_xml, template)
        verified = decode_save(encoded)
        if verified != canonical_xml(self.current_xml):
            raise SaveToolError("Encode/decode round-trip không khớp XML đã sửa")
        atomic_write(OUTPUT_FILE, encoded)
        atomic_write(VERIFY_FILE, verified)
        return encoded


SESSION = Session()


def ask_yes_no(message: str, default: bool = False) -> bool:
    suffix = " [Y/n]: " if default else " [y/N]: "
    answer = input(message + suffix).strip().lower()
    if not answer:
        return default
    return answer in {"y", "yes", "c", "co", "có"}


def show_known_values() -> None:
    SESSION.require_loaded()
    assert SESSION.current_xml is not None
    print("\n--- Giá trị hiện tại ---")
    for name in ("money", "moneyCash", "levelup", "experience", "sexpx", "gameStartDate"):
        try:
            attrs = read_var(SESSION.current_xml, name)
            value = attrs.get("v", "<không có v>")
            if name == "gameStartDate":
                try:
                    display = datetime.fromtimestamp(int(value), UTC_PLUS_7).strftime(
                        "%d/%m/%Y %H:%M:%S UTC+7"
                    )
                    value = f"{value} ({display})"
                except (ValueError, OSError):
                    pass
            print(f"{name:18}: {value}")
        except SaveToolError as exc:
            print(f"{name:18}: {exc}")
    print(f"M3 LVL             : {read_match3_level(SESSION.current_xml)}")
    first_win = read_first_win(SESSION.current_xml)
    print(f"First Win          : {first_win if first_win is not None else '(chưa có)'}")
    lives = read_lives(SESSION.current_xml)
    print(f"LivesSent          : {lives if lives is not None else '(chưa có)'}")
    print(f"Nguồn              : {SESSION.source_label}")
    print(f"Có thay đổi         : {'CÓ' if SESSION.changed else 'KHÔNG'}")


def edit_integer_var_prompt(var_name: str, minimum: int, maximum: int) -> None:
    SESSION.require_loaded()
    assert SESSION.current_xml is not None
    attrs = read_var(SESSION.current_xml, var_name)
    old = attrs.get("v")
    print(f"{var_name} hiện tại: {old}")
    new_value = parse_int(input(f"Nhập {var_name} mới: "), var_name, minimum, maximum)
    print(f"Dự kiến: {old} -> {new_value}")
    if not ask_yes_no("Xác nhận thay đổi?"):
        print("Đã hủy.")
        return
    new_xml, _ = set_integer_var(
        SESSION.current_xml, var_name, new_value, minimum, maximum
    )
    SESSION.apply_xml(new_xml)
    print("Đã cập nhật XML làm việc. Chưa ghi vào game.")


def edit_level_prompt() -> None:
    SESSION.require_loaded()
    assert SESSION.current_xml is not None
    current = read_township_level(SESSION.current_xml)
    print(f"Level hiện tại: {current}")
    level = parse_int(input("Nhập level mới (15..1089, không giảm level): "),
                      "Level", TSVIP_LEVEL_MIN, TSVIP_LEVEL_MAX)
    new_xml, changes = set_township_level(SESSION.current_xml, level)
    for name, (old, new) in changes.items():
        print(f"{name}: {old if old is not None else '(chưa có)'} -> {new}")
    if not ask_yes_no("Xác nhận thay đổi level?"):
        print("Đã hủy.")
        return
    SESSION.apply_xml(new_xml)
    print("Đã cập nhật level và XP trong XML làm việc. Chưa ghi vào game.")
    print("Chọn 51 để encode + backup + ghi vào game, hoặc 50 để xuất local.")


# TSVIP v121 gt1 (m3l) -> qx3.y: update Match3 Vars and LevelInfo.
M3_LEVEL_MIN = 50
M3_LEVEL_MAX = 2_147_483_647  # Java Integer input limit, not a game level cap.


def read_match3_level(xml: bytes) -> int:
    root = validate_xml_document(xml, "M3 LVL")
    candidates = []
    for node in root.iter():
        if node.tag.casefold() in ("var", "dataelem") and node.get("name", "").casefold() in (
            "stlm3", "m3_comp_lvls", "m3ch_mainm3"
        ):
            raw = node.get("value", node.get("v", ""))
            candidates.append(parse_int(raw, "M3 level hiện tại", 0, M3_LEVEL_MAX))
    # Keep the highest recorded progress to avoid decreasing any existing counter.
    return max(candidates, default=0)


def _m3_upsert_field(scope: bytes, name: str, value: str,
                     field_type: str | None, closing_tag: str) -> bytes:
    matches = _level_field_tags(scope, name)
    if len(matches) > 1:
        raise SaveToolError(f"Trường {name} bị trùng trong khối {closing_tag}")
    if matches:
        match = matches[0]
        attrs = parse_attributes(match.group(0))
        attribute = "value" if "value" in attrs else "v"
        tag = replace_attribute(match.group(0), attribute, value)
        return scope[:match.start()] + tag + scope[match.end():]
    endings = list(re.finditer(rb"</" + closing_tag.encode() + rb"\s*>", scope, re.I))
    if len(endings) != 1:
        raise SaveToolError(f"Không xác định được khối {closing_tag} để thêm {name}")
    position = endings[0].start()
    type_attr = f' t="{field_type}"' if field_type is not None else ""
    tag = f'<Var name="{name}" v="{value}"{type_attr}/>'.encode()
    return scope[:position] + b"    " + tag + b"\n" + scope[position:]


def set_match3_level(xml: bytes, level: int) -> tuple[bytes, dict]:
    if type(level) is not int or not M3_LEVEL_MIN <= level <= M3_LEVEL_MAX:
        raise SaveToolError("M3 level phải là số nguyên từ 50 đến 2147483647")
    old = read_match3_level(xml)
    if level < old:
        raise SaveToolError(f"TSVIP không cho giảm M3 level: hiện tại {old}, yêu cầu {level}")
    updated = _m3_upsert_field(xml, "STLM3", str(level), "i", "Global")
    updated = _m3_upsert_field(updated, "CityM3FirstTutorialCompleted", "1", "b", "Global")
    openings = [m for m in re.finditer(rb"<Minigame\b[^>]*>", updated, re.I)
                if parse_attributes(m.group(0)).get("id", "").casefold() == "match3"]
    if len(openings) > 1:
        raise SaveToolError("Có nhiều khối Minigame Match3; không áp dụng thay đổi")
    fields = (("m3_comp_lvls", str(level), "i"),
              ("M3Ch_mainM3", str(level), "i"),
              ("m3_orig_lvl_id", f"st{level}", None))
    level_info = (f'<LevelInfo completedLevelsCount="{level - 1}" '
                  'canFreeRestart="1" moduleType="Match3TS"/>').encode()
    if openings:
        opening = openings[0]
        if opening.group(0).rstrip().endswith(b"/>"):
            end = opening.end()
            body = b""
            opening_tag = re.sub(rb"/\s*>$", b">", opening.group(0))
            closing_tag = b"</Minigame>"
        else:
            closing = re.search(rb"</Minigame\s*>", updated[opening.end():], re.I)
            if closing is None:
                raise SaveToolError("Khối Match3 chưa đóng")
            end = opening.end() + closing.end()
            body = updated[opening.end():opening.end() + closing.start()]
            opening_tag = opening.group(0)
            closing_tag = closing.group(0)
        vars_matches = list(re.finditer(rb"<Vars\b[^>]*>(.*?)</Vars\s*>|<Vars\b[^>]*/>", body, re.I | re.S))
        if len(vars_matches) > 1:
            raise SaveToolError("Có nhiều khối Vars trong Match3")
        vars_block = vars_matches[0].group(0) if vars_matches else b"<Vars></Vars>"
        if vars_block.rstrip().endswith(b"/>"):
            vars_block = re.sub(rb"/\s*>$", b"></Vars>", vars_block)
        for name, value, field_type in fields:
            vars_block = _m3_upsert_field(vars_block, name, value, field_type, "Vars")
        if vars_matches:
            match = vars_matches[0]
            body = body[:match.start()] + vars_block + body[match.end():]
        else:
            body = vars_block + b"\n" + body
        info_matches = list(re.finditer(rb"<LevelInfo\b[^>]*>", body, re.I))
        if len(info_matches) > 1:
            raise SaveToolError("Có nhiều LevelInfo trong Match3")
        if info_matches:
            match = info_matches[0]
            tag = replace_attribute(match.group(0), "completedLevelsCount", str(level - 1))
            body = body[:match.start()] + tag + body[match.end():]
        else:
            body += b"\n" + level_info
        block = opening_tag + body + closing_tag
        updated = updated[:opening.start()] + block + updated[end:]
    else:
        vars_block = b"<Vars></Vars>"
        for name, value, field_type in fields:
            vars_block = _m3_upsert_field(vars_block, name, value, field_type, "Vars")
        block = b'<Minigame id="Match3">' + vars_block + level_info + b"</Minigame>"
        containers = list(re.finditer(rb"<Minigames\b[^>]*>", updated, re.I))
        if len(containers) > 1:
            raise SaveToolError("Có nhiều khối Minigames")
        if containers:
            container = containers[0]
            if container.group(0).rstrip().endswith(b"/>"):
                replacement = re.sub(rb"/\s*>$", b">", container.group(0)) + block + b"</Minigames>"
                updated = updated[:container.start()] + replacement + updated[container.end():]
            else:
                updated = updated[:container.end()] + b"\n" + block + updated[container.end():]
        else:
            # Same qx3.y fallback when the save has no Minigames container.
            for name, value, field_type in fields:
                updated = _m3_upsert_field(updated, name, value, field_type or "string", "Global")
    validate_xml_document(updated, "M3 LVL sau cập nhật")
    if read_match3_level(updated) != level:
        raise SaveToolError("Xác minh M3 LVL thất bại")
    return updated, {"old_level": old, "level": level,
                     "m3_orig_lvl_id": f"st{level}", "completedLevelsCount": level - 1,
                     "match3_block": bool(openings or containers)}


def edit_match3_level_prompt() -> None:
    SESSION.require_loaded()
    assert SESSION.current_xml is not None
    old = read_match3_level(SESSION.current_xml)
    print(f"M3 LVL hiện tại: {old if old else '(chưa có)'}")
    level = parse_int(input("Nhập M3 LVL mới (tối thiểu 50, không giảm): "),
                      "M3 LVL", M3_LEVEL_MIN, M3_LEVEL_MAX)
    new_xml, report = set_match3_level(SESSION.current_xml, level)
    print(f"M3 LVL: {old} -> {level}; mã màn: st{level}; đã hoàn thành: {level - 1}")
    if not report["match3_block"]:
        print("Save không có Minigames: cập nhật các Var theo nhánh dự phòng TSVIP.")
    if not ask_yes_no("Xác nhận thay đổi M3 LVL?"):
        print("Đã hủy.")
        return
    SESSION.apply_xml(new_xml)
    print("Đã cập nhật M3 LVL trong XML làm việc. Chưa ghi vào game.")
    print("Chọn 51 để encode + backup + ghi vào game, hoặc 50 để xuất local.")


# TSVIP v121: uu0 maps "win" to FirstAttemptM3Levels; gt1 uses qx3.v/q.
FIRST_WIN_FIELD = "FirstAttemptM3Levels"
FIRST_WIN_MAX = 2_147_483_647  # Python editor guard for a nonnegative integer counter.


def read_first_win(xml: bytes) -> int | None:
    validate_xml_document(xml, "First Win")
    matches = _level_field_tags(xml, FIRST_WIN_FIELD)
    if not matches:
        return None
    if len(matches) != 1:
        raise SaveToolError("FirstAttemptM3Levels bị trùng; không xác định được bộ đếm")
    attrs = parse_attributes(matches[0].group(0))
    return parse_int(attrs.get("value", attrs.get("v", "")),
                     "First Win hiện tại", 0, FIRST_WIN_MAX)


def set_first_win(xml: bytes, count: int) -> tuple[bytes, dict]:
    if type(count) is not int or not 0 <= count <= FIRST_WIN_MAX:
        raise SaveToolError("First Win phải là số nguyên từ 0 đến 2147483647")
    old = read_first_win(xml)
    # TSVIP replaces the counter value; if absent it adds a Var with t="i" to Global.
    updated = _m3_upsert_field(xml, FIRST_WIN_FIELD, str(count), "i", "Global")
    validate_xml_document(updated, "First Win sau cập nhật")
    if read_first_win(updated) != count:
        raise SaveToolError("Xác minh First Win thất bại")
    return updated, {FIRST_WIN_FIELD: (old, count)}


def edit_first_win_prompt() -> None:
    SESSION.require_loaded()
    assert SESSION.current_xml is not None
    old = read_first_win(SESSION.current_xml)
    print(f"First Win (FirstAttemptM3Levels): {old if old is not None else '(chưa có)'}")
    print("Nhập bộ đếm First Win mới. Mục này không đổi M3 LVL.")
    count = parse_int(input("Nhập số First Win mới (0..2147483647): "),
                      "First Win", 0, FIRST_WIN_MAX)
    new_xml, _ = set_first_win(SESSION.current_xml, count)
    print(f"FirstAttemptM3Levels: {old if old is not None else '(chưa có)'} -> {count}")
    if not ask_yes_no("Xác nhận thay đổi First Win?"):
        print("Đã hủy.")
        return
    SESSION.apply_xml(new_xml)
    print("Đã cập nhật First Win trong XML làm việc. Chưa ghi vào game.")
    print("Chọn 51 để encode + backup + ghi vào game, hoặc 50 để xuất local.")


# TSVIP v121: uu0 maps "liv" to LivesSent; gt1 uses qx3.v/q.
LIVES_FIELD = "LivesSent"
LIVES_MAX = 2_147_483_647  # Python editor guard for a nonnegative integer counter.


def read_lives(xml: bytes) -> int | None:
    validate_xml_document(xml, "Lives")
    matches = _level_field_tags(xml, LIVES_FIELD)
    if not matches:
        return None
    if len(matches) != 1:
        raise SaveToolError("LivesSent bị trùng; không xác định được bộ đếm")
    attrs = parse_attributes(matches[0].group(0))
    return parse_int(attrs.get("value", attrs.get("v", "")),
                     "Lives hiện tại", 0, LIVES_MAX)


def set_lives(xml: bytes, count: int) -> tuple[bytes, dict]:
    if type(count) is not int or not 0 <= count <= LIVES_MAX:
        raise SaveToolError("Lives phải là số nguyên từ 0 đến 2147483647")
    old = read_lives(xml)
    # TSVIP replaces the counter value; if absent it adds a Var with t="i" to Global.
    updated = _m3_upsert_field(xml, LIVES_FIELD, str(count), "i", "Global")
    validate_xml_document(updated, "Lives sau cập nhật")
    if read_lives(updated) != count:
        raise SaveToolError("Xác minh Lives thất bại")
    return updated, {LIVES_FIELD: (old, count)}


def edit_lives_prompt() -> None:
    SESSION.require_loaded()
    assert SESSION.current_xml is not None
    old = read_lives(SESSION.current_xml)
    print(f"Lives (LivesSent): {old if old is not None else '(chưa có)'}")
    print("Nhập bộ đếm mạng đã gửi (LivesSent) mới.")
    count = parse_int(input("Nhập số Lives mới (0..2147483647): "),
                      "Lives", 0, LIVES_MAX)
    new_xml, _ = set_lives(SESSION.current_xml, count)
    print(f"LivesSent: {old if old is not None else '(chưa có)'} -> {count}")
    if not ask_yes_no("Xác nhận thay đổi Lives?"):
        print("Đã hủy.")
        return
    SESSION.apply_xml(new_xml)
    print("Đã cập nhật Lives trong XML làm việc. Chưa ghi vào game.")
    print("Chọn 51 để encode + backup + ghi vào game, hoặc 50 để xuất local.")


# Profile Statistics mapping from TSVIP v121 uu0 and gt1 (not Unlock/Regata tasks).
PROFILE_STAT_FIELDS = {
    "help": ("Achievement_Teamwork",),
    "card": ("FullCardCollections",),
    "regata": ("RegataTasksCompleted", "RegataPoints"),
    "energy": ("expeditionEnergy", "expedition_energy", "ExpeditionEnergyCurrent"),
}
PROFILE_STAT_LABELS = {"help": "Help", "card": "Card", "regata": "Regata (Profile Statistics)",
                       "energy": "Expedition Energy"}
PROFILE_STAT_MAX = 2_147_483_647  # Local guard; not a TSVIP-specific game cap.


def read_profile_stat(xml: bytes, key: str) -> dict[str, int | None]:
    validate_xml_document(xml, "Profile Statistics")
    if key not in PROFILE_STAT_FIELDS:
        raise SaveToolError("Không có thống kê này")
    values = {}
    for name in PROFILE_STAT_FIELDS[key]:
        matches = _level_field_tags(xml, name)
        if len(matches) > 1:
            raise SaveToolError(f"Trường {name} bị trùng")
        if matches:
            attrs = parse_attributes(matches[0].group(0))
            values[name] = parse_int(attrs.get("value", attrs.get("v", "")), name,
                                     0, PROFILE_STAT_MAX)
        else:
            values[name] = None
    return values


def set_profile_stat(xml: bytes, key: str, count: int) -> tuple[bytes, dict]:
    if type(count) is not int or not 0 <= count <= PROFILE_STAT_MAX:
        raise SaveToolError("Giá trị phải là số nguyên từ 0 đến 2147483647")
    old = read_profile_stat(xml, key)
    # TSVIP writes all aliases that exist; if none exists, creates the first name.
    names = [name for name, value in old.items() if value is not None]
    if not names:
        names = [PROFILE_STAT_FIELDS[key][0]]
    updated = xml
    for name in names:
        updated = _m3_upsert_field(updated, name, str(count), "i", "Global")
    verified = read_profile_stat(updated, key)
    if any(verified[name] != count for name in names):
        raise SaveToolError("Xác minh Profile Statistics thất bại")
    return updated, {name: (old[name], count) for name in names}


def edit_profile_stat_prompt(key: str) -> None:
    SESSION.require_loaded()
    assert SESSION.current_xml is not None
    print(PROFILE_STAT_LABELS[key])
    for name, value in read_profile_stat(SESSION.current_xml, key).items():
        print(f"{name}: {value if value is not None else '(chưa có)'}")
    if key == "regata":
        print("Theo TSVIP, cùng giá trị được áp dụng cho các trường thống kê Regata đang có.")
    count = parse_int(input("Nhập giá trị mới (0..2147483647): "), "Giá trị", 0, PROFILE_STAT_MAX)
    updated, changes = set_profile_stat(SESSION.current_xml, key, count)
    for name, (old, new) in changes.items():
        print(f"{name}: {old if old is not None else '(chưa có)'} -> {new}")
    if not ask_yes_no("Xác nhận thay đổi?"):
        print("Đã hủy.")
        return
    SESSION.apply_xml(updated)
    print("Đã cập nhật XML làm việc. Chọn 51 ghi vào game hoặc 50 xuất local.")


# TSVIP qx3.z + ws3 case 12: 41x7 digging map, tutorial flags and CHT completion.
TSVIP_MINE_FIELD = [[{'g': 1}, {'g': 1, 'r': 'm2'}, {'g': 1, 'v': 1}, {'v': 1}, {'v': 1}, {'v': 1}, {'v': 1}], [{'g': 1}, {'g': 1, 'v': 1}, {'v': 1}, {'v': 1}, {'v': 1}, {'v': 1}, {'v': 1}], [{'g': 1, 'v': 1}, {'v': 1}, {'v': 1}, {'v': 1}, {'v': 1}, {'v': 1}, {'v': 1}], [{'g': 1, 'v': 1}, {'v': 1}, {'v': 1}, {'v': 1}, {'v': 1}, {'g': 3, 'v': 1}, {'v': 1}], [{'g': 1, 'v': 1}, {'v': 1}, {'v': 1}, {'v': 1}, {'g': 4, 'v': 1}, {'g': 1}, {'g': 1, 'v': 1}], [{'v': 1}, {'g': 1, 'v': 1}, {'v': 1}, {'g': 4, 'v': 1}, {'g': 1, 'v': 1}, {'g': 1, 'v': 1}, {'g': 1, 'v': 1}], [{'v': 1}, {'v': 1}, {'v': 1}, {'v': 1}, {'v': 1}, {'v': 1}, {'v': 1}], [{'v': 1}, {'v': 1}, {'v': 1}, {'g': 4, 'v': 1}, {'g': 1, 'v': 1}, {'g': 1, 'v': 1}, {'g': 1, 'v': 1}], [{'v': 1}, {'v': 1}, {'g': 1, 'v': 1}, {'g': 1, 'r': 'c'}, {'g': 1, 'v': 1}, {'g': 1}, {'g': 4}], [{'v': 1}, {'g': 1, 'v': 1}, {'v': 1}, {'g': 4, 'v': 1}, {'v': 1}, {'g': 1, 'v': 1}, {'r': 'b'}], [{'v': 1}, {'g': 1, 'v': 1}, {'v': 1}, {'g': 1, 'v': 1}, {'v': 1}, {'g': 1, 'v': 1}, {'g': 1}], [{'v': 1}, {'v': 1}, {'v': 1}, {'v': 1}, {'v': 1}, {'g': 3, 'v': 1}, {'g': 1}], [{'v': 1}, {'v': 1}, {'v': 1}, {'g': 1, 'v': 1}, {'g': 1, 'v': 1}, {'g': 1}, {'g': 1}], [{'v': 1}, {'v': 1}, {'v': 1}, {'g': 1, 'v': 1}, {'g': 2}, {'g': 1}, {'g': 1, 'r': 'o3'}], [{'g': 5, 'v': 1}, {'v': 1}, {'g': 1, 'v': 1}, {'g': 1, 'v': 1}, {'g': 1, 'v': 1}, {'g': 5}, {'g': 4, 'r': 'o1'}], [{'g': 5, 'v': 1}, {'v': 1}, {'v': 1}, {'v': 1}, {'v': 1}, {'g': 5, 'v': 1}, {'g': 1, 'r': 'm2'}], [{'g': 5}, {'g': 5, 'v': 1}, {'g': 5, 'v': 1}, {'g': 1, 'v': 1}, {'v': 1}, {'g': 5, 'v': 1}, {'g': 1, 'r': 'c'}], [{}, {'g': 1}, {}, {'g': 1, 'v': 1}, {'v': 1}, {'g': 1, 'r': 'c', 'v': 1}, {'g': 1}], [{}, {'bi': 'grass1'}, {'g': 1, 'v': 1}, {'v': 1}, {'v': 1}, {'v': 1}, {'g': 1, 'v': 1}], [{}, {'g': 1}, {'g': 1, 'v': 1}, {'v': 1}, {'v': 1}, {'v': 1}, {'g': 1, 'v': 1}], [{'g': 1}, {'g': 1, 'r': 'c'}, {'g': 1, 'r': 'o1', 'v': 1}, {'v': 1}, {'v': 1}, {'v': 1}, {'g': 1, 'v': 1}], [{'g': 1}, {'g': 1, 'r': 'c'}, {'g': 1}, {'g': 1, 'v': 1}, {'g': 1, 'v': 1}, {'v': 1, 'bi': 'mushroom1'}, {'g': 1, 'v': 1}], [{'g': 5}, {'g': 5}, {'g': 5}, {'g': 5}, {'g': 5}, {'g': 5, 'v': 1}, {'g': 1}], [{'b': 'lt'}, {'p': 'cave_t2m', 'b': 't'}, {'p': 'cave_t2', 'b': 't'}, {'p': 'cave_t1', 'b': 't'}, {'p': 'cave_t2', 'b': 't'}, {'b': 'rt'}, {'g': 1}], [{'r': 't1', 'p': 'cave_l', 'b': 'lb'}, {'r': 't2', 'p': 'cave_b2', 'b': 'b'}, {'r': 'b', 'p': 'cave_b2', 'b': 'b'}, {'r': 't1', 'p': 'cave_b1', 'b': 'b'}, {'r': 'B', 'p': 'cave_b2m', 'b': 'b'}, {'r': 't3', 'p': 'cave_r', 'b': 'rb'}, {'g': 5}], [{'g': 5}, {'g': 1}, {'g': 5}, {'g': 5}, {'g': 5}, {'g': 5}, {'g': 5}], [{'g': 1}, {'g': 1, 'r': 'c'}, {'g': 1}, {'g': 1}, {'g': 1}, {}, {'g': 1}], [{'g': 1}, {'g': 1}, {'g': 1, 'r': 'm2'}, {'g': 1, 'r': 'c'}, {}, {}, {'bi': 'grass1'}], [{'g': 1}, {'g': 1}, {'g': 1}, {'g': 1}, {'g': 1}, {'g': 1}, {'g': 1}], [{'g': 1}, {'g': 1}, {'g': 1, 'r': 'c'}, {'g': 1}, {}, {'g': 2}, {'g': 1}], [{'g': 1}, {'g': 1}, {'g': 1}, {'g': 1}, {'g': 1}, {'g': 4, 'r': 'o4'}, {'g': 4}], [{'g': 1}, {'g': 1}, {'g': 1}, {'g': 1, 'r': 'o4'}, {'g': 4, 'r': 'm1'}, {'g': 1}, {'g': 1}], [{'g': 1}, {'g': 1}, {'g': 5}, {'g': 5}, {'g': 5}, {'g': 1}, {'g': 1}], [{'g': 1, 'r': 'o1'}, {'g': 4}, {'g': 5}, {'g': 1, 'r': 'o4'}, {'g': 5}, {'g': 1}, {'g': 1}], [{'g': 1, 'r': 'o1'}, {'g': 4}, {'g': 5}, {'g': 1, 'r': 'o3'}, {'g': 5}, {'g': 1}, {'g': 1, 'r': 'a'}], [{'g': 1}, {'bi': 'grass1'}, {'g': 5}, {'g': 1, 'r': 'o3'}, {'g': 5}, {'g': 1, 'r': 'c'}, {'g': 1}], [{'g': 1}, {'g': 1}, {'g': 4, 'r': 'o1'}, {}, {'g': 1}, {'bi': 'grass1'}, {'g': 1, 'r': 'c'}], [{'bi': 'mushroom2'}, {'g': 1}, {'g': 1}, {}, {'g': 1}, {'g': 1}, {'g': 1}], [{'g': 1}, {'g': 1}, {'g': 4}, {'bi': 'mushroom1'}, {'g': 1}, {'g': 1}, {}], [{'g': 1, 'r': 'c'}, {'g': 1}, {'g': 1}, {'g': 1}, {'g': 1}, {}, {}], [{'g': 1}, {'g': 1}, {'g': 4}, {'g': 1}, {'g': 1}, {'g': 1}, {'g': 1}]]
TSVIP_MINE_FLAGS = [('DiggingTutorShowed', '1', 'b'), ('FirstDiggingClayShowed', '1', 'b'), ('FirstDiggingClayTutorial_state', '18', 'i'), ('FirstDiggingClayTutorialsq0_state', '0', 'i'), ('FirstDiggingHardstoneShowed', '1', 'b'), ('FirstDiggingRoomShowed', '1', 'b'), ('FirstDiggingStoneShowed', '1', 'b'), ('ExtractClayVideoTutorial_state', '18', 'i'), ('ExtractClayVideoTutorialsq0_state', '0', 'i'), ('DestroyClayTutorial_state', '18', 'i'), ('DestroyClayTutorialsq0_state', '0', 'i'), ('DestroyClayShowed', '1', 'b'), ('DestroyClay2Tutorial_state', '18', 'i'), ('DestroyClay2Tutorialsq0_state', '0', 'i'), ('DiggingReady', '1', 'b'), ('DiggingPreVisit', '1', 'b'), ('DiggingVisited', '1', 'b'), ('diggingFullCompleted', '1', 'b'), ('RepairDiggingTutShowed', '1', 'b'), ('NeedArrowOnDigging', '0', 'b'), ('MainDiggingTutShowed', '1', 'b')]
TSVIP_MINE_QUESTS = ("CHT_Digging_Main", "CHT_Digging_OldPlayers",
                     "CHT_Digging_Repair", "CHT_Digging_RepairComplete")


def _mine_objects(xml: bytes) -> list[tuple[re.Match[bytes], str, dict]]:
    result = []
    for match in re.finditer(rb"<Object\b[^>]*>", xml, re.I):
        for attribute, raw in parse_attributes(match.group(0)).items():
            text = html.unescape(raw)
            if not re.search(r'"storeId"\s*:\s*"digging"', text, re.I):
                continue
            try:
                data = json.loads(text)
            except (ValueError, TypeError) as exc:
                raise SaveToolError("JSON của Object digging không hợp lệ") from exc
            if not isinstance(data, dict):
                raise SaveToolError("Object digging phải chứa JSON object")
            if str(data.get("storeId", "")).casefold() == "digging":
                result.append((match, attribute, data))
    if not result:
        raise SaveToolError("Không tìm thấy Object digging có dữ liệu mỏ; chưa sửa save")
    return result


def read_mine_depth(xml: bytes) -> int:
    validate_xml_document(xml, "Mine Depth")
    mines = _mine_objects(xml)
    depths = []
    for _, _, data in mines:
        if type(data.get("depth")) is not int or not 0 <= data["depth"] <= 2_147_483_647:
            raise SaveToolError("Object digging thiếu depth nguyên hợp lệ")
        depths.append(data["depth"])
    if len(mines) != 1:
        raise SaveToolError("Có nhiều Object digging; không xác định được mỏ cần sửa")
    return depths[0]


def set_mine_depth(xml: bytes, depth: int) -> tuple[bytes, dict]:
    if type(depth) is not int or not 100 <= depth <= 2_147_483_647:
        raise SaveToolError("Mine Depth phải là số nguyên từ 100 đến 2147483647 (tối thiểu theo TSVIP)")
    old = read_mine_depth(xml)
    match, attribute, data = _mine_objects(xml)[0]
    data["depth"] = depth
    if data.get("state") == 3:
        data["state"] = 2
    data["flIndex"] = 16
    data["field"] = TSVIP_MINE_FIELD
    tag = replace_attribute(match.group(0), attribute, json.dumps(data, ensure_ascii=False, separators=(",", ":")))
    updated = xml[:match.start()] + tag + xml[match.end():]
    for name, value, field_type in TSVIP_MINE_FLAGS:
        updated = _m3_upsert_field(updated, name, value, field_type, "Global")
    root = validate_xml_document(updated, "Mine Depth trước cập nhật CHT")
    recorded = {node.get("n") for node in root.iter()}
    missing = [name for name in TSVIP_MINE_QUESTS if name not in recorded]
    if missing:
        entries = b"\n".join(f'<v n="{name}"/>'.encode() for name in missing)
        completed = list(re.finditer(rb"</completed\s*>", updated, re.I))
        if len(completed) > 1:
            raise SaveToolError("Có nhiều khối completed; không xác định được CHT")
        if completed:
            pos = completed[0].start()
            updated = updated[:pos] + entries + b"\n" + updated[pos:]
        else:
            cht = list(re.finditer(rb"<CHT\b[^>]*>", updated, re.I))
            if len(cht) > 1:
                raise SaveToolError("Có nhiều khối CHT")
            if cht:
                match = cht[0]
                block = b"<completed>" + entries + b"</completed>"
                if match.group(0).rstrip().endswith(b"/>"):
                    tag = re.sub(rb"/\s*>$", b">", match.group(0)) + block + b"</CHT>"
                    updated = updated[:match.start()] + tag + updated[match.end():]
                else:
                    updated = updated[:match.end()] + block + updated[match.end():]
    validate_xml_document(updated, "Mine Depth sau cập nhật")
    if read_mine_depth(updated) != depth:
        raise SaveToolError("Xác minh độ sâu mỏ thất bại")
    return updated, {"old_depth": old, "depth": depth, "flIndex": 16,
                     "tutorial_flags": len(TSVIP_MINE_FLAGS)}


def edit_mine_depth_prompt() -> None:
    SESSION.require_loaded()
    assert SESSION.current_xml is not None
    old = read_mine_depth(SESSION.current_xml)
    print(f"Mine Depth hiện tại: {old}")
    depth = parse_int(input("Nhập độ sâu mỏ mới (tối thiểu 100): "), "Mine Depth", 100, 2_147_483_647)
    updated, report = set_mine_depth(SESSION.current_xml, depth)
    print(f"Mine Depth: {old} -> {depth}")
    print("Theo TSVIP: đặt lại bản đồ mỏ 41x7, flIndex=16, cập nhật trạng thái sửa mỏ và hướng dẫn.")
    if not ask_yes_no("Xác nhận thay đổi Mine Depth?"):
        print("Đã hủy.")
        return
    SESSION.apply_xml(updated)
    print("Đã cập nhật XML làm việc. Chọn 51 ghi vào game hoặc 50 xuất local.")


# TSVIP v121 if2.m avatar catalog; t2 cases 6/8 and fm case 18.
TSVIP_AVATAR_IDS = ('1', '3', '5', '6', '7', '8', '9', '10', '11', '12', '13', '14', '15', '16', '17', '18', '21', '22', '23', '24', '25', '26', '27', '28', '29', '30', '31', '32', '33', '34', '35', '36', '37', '38', '39', '41', '42', '43', '45', '46', '47', '49', '50', '51', '52', '53', '54', '55', '56', '57', '58', '59', '60', '61', '62', '63', '64', '66', '67', '68', '69', '70', '71', '72', '73', '74', '75', '76', '77', '78', '79', '80', '81', '82', '83', '85', '86', '87', '88', '89', '90', '91', '92', '93', '94', '95', '96', '97', '98', '99', '100', '101', '102', '103', '104', '105', '106', '107', '108', '109', '110', '111', '112', '113', '114', '115', '116', '117', '118', '119', '120', '121', '122', '123', '124', '125', '126', '127', '128', '129', '130', '131', '132', '133', '134', '135', '136', '137', '138', '139', '140', '141', '142', '143', '144', '145', '146', '147', '148', '149', '150', '151', '152', '153', '154', '155', '156', '157', '158', '159', '160', '161', '162', '163', '164', '165', '166', '167', '168', '169', '170', '171', '172', '173', '174', '175', '176', '177', '178', '179', '180', '181', '182', '183', '184', '185', '186', '187', '188', '189', '190', '191', '192', '193', '194', '195', '196', '197', '198', '199', '200', '201', '202', '203', '204', '205', '206', '207', '208', '209', '210', '211', '212', '213', '214', '215', '216', '217', '218', '219', '220', '221', '223', '225', '226', '227', '228', '229', '230', '231', '232', '233', '234', '235', '236', '237', '238', '239', '240', '241', '242', '243', '244', '245', '246', '247', '248', '249', '250', '251', '252', '254', '255', '256', '257', '258', '259', '260', '261', '262', '263', '265', '267', '268', '269', '270', '271', '272', '273', '274', '275', '276', '277', '278', '279', '280', '281', '282', '283', '284', '285', '286', '287', '288', '289', '290', '291', '292', '293', '294', '295', '296', '297', '298', '299', '300', '302', '303', '304', '305', '306', '307', '308', '309', '310', '312', '313', '314', '315', '317', '318', '319', '320', '321', '322', '323', '324', '325', '326', '327', '328', '329', '330', '331', '332', '333', '334', '335', '336', '337', '338', '339', '340', '341', '342', '343', '344', '345', '346', '347', '348', '349', '350', '352', '353', '354', '355', '356', '357', '358', '359', '360', '361', '362', '363', '364', '365', '366', '367', '368', '369', '370', '371', '372', '373', '374', '375', '376', '377', '381', '382', '383', '384', '385', '386', '387', '388', '389', '390', '391', '392', '393', '394', '395', '396', '397', '398')


def avatar_states(xml: bytes) -> dict[str, dict[str, Any]]:
    validate_xml_document(xml, "Avatar")
    catalog = set(TSVIP_AVATAR_IDS)
    result = {avatar_id: {"state": None, "catalog": True} for avatar_id in catalog}
    seen = set()
    for match in re.finditer(rb"<(?:Var|DataElem)\b[^>]*>", xml):
        attrs = parse_attributes(match.group(0))
        name_match = re.fullmatch(r"Unlocked_ava(\d+)", attrs.get("name", ""))
        if name_match is None:
            continue
        avatar_id = name_match.group(1)
        if avatar_id in seen:
            raise SaveToolError(f"Avatar ID {avatar_id} có cờ trùng; chưa áp dụng thay đổi")
        seen.add(avatar_id)
        raw = attrs.get("value", attrs.get("v", ""))
        state = {"1": True, "0": False, "true": True, "false": False}.get(raw.casefold(), raw)
        result[avatar_id] = {"state": state, "catalog": avatar_id in catalog}
    return dict(sorted(result.items(), key=lambda item: int(item[0])))


def parse_avatar_selection(raw: str, available: Iterable[str]) -> list[str]:
    available = set(available)
    selected = set()
    tokens = [token for token in re.split(r"[,;\s]+", raw.strip()) if token]
    if not tokens:
        raise SaveToolError("Chưa nhập ID avatar")
    for token in tokens:
        if re.fullmatch(r"\d+", token):
            avatar_id = str(int(token))
            if avatar_id not in available:
                raise SaveToolError(f"ID {avatar_id} không có trong danh sách TSVIP/save")
            selected.add(avatar_id)
        else:
            match = re.fullmatch(r"(\d+)-(\d+)", token)
            if match is None or int(match[1]) > int(match[2]):
                raise SaveToolError(f"Lựa chọn không hợp lệ: {token}; ví dụ 1,3,5-20")
            low, high = int(match[1]), int(match[2])
            found = {avatar_id for avatar_id in available if low <= int(avatar_id) <= high}
            if not found:
                raise SaveToolError(f"Khoảng {token} không có avatar hợp lệ")
            selected.update(found)
    return sorted(selected, key=int)


def set_avatar_unlocks(xml: bytes, avatar_ids: Iterable[str], unlocked: bool) -> tuple[bytes, dict]:
    if type(unlocked) is not bool:
        raise SaveToolError("Trạng thái avatar phải là True/False")
    states = avatar_states(xml)
    selected = {str(avatar_id) for avatar_id in avatar_ids}
    if not selected or not selected <= states.keys():
        raise SaveToolError("Danh sách avatar trống hoặc chứa ID không hợp lệ")
    for avatar_id in selected:
        state = states[avatar_id]["state"]
        if state is not None and type(state) is not bool:
            raise SaveToolError(f"Avatar {avatar_id} có giá trị cờ chưa hỗ trợ: {state!r}")
    value = "1" if unlocked else "0"
    names = {"Unlocked_ava" + avatar_id for avatar_id in selected}
    updates = []
    seen = set()
    for match in re.finditer(rb"<(?:Var|DataElem)\b[^>]*>", xml):
        attrs = parse_attributes(match.group(0))
        name = attrs.get("name", "")
        if name not in names:
            continue
        seen.add(name)
        is_dataelem = match.group(0).startswith(b"<DataElem")
        attribute = "value" if "value" in attrs else "v"
        tag = replace_attribute(match.group(0), attribute, value)
        tag = replace_attribute(tag, "type" if is_dataelem else "t", "bool" if is_dataelem else "b")
        updates.append((match.start(), match.end(), tag))
    updated = xml
    for start, end, tag in reversed(updates):
        updated = updated[:start] + tag + updated[end:]
    missing = sorted(names - seen, key=lambda name: int(name[len("Unlocked_ava"):]))
    if missing:
        entries = b"\n".join(f'    <Var name="{name}" v="{value}" t="b"/>'.encode() for name in missing) + b"\n"
        endings = list(re.finditer(rb"</Global\s*>", updated))
        if not endings:
            empty = list(re.finditer(rb"<Global\b[^>]*/>", updated))
            if len(empty) == 1:
                match = empty[0]
                replacement = re.sub(rb"/\s*>$", b">", match.group(0)) + entries + b"</Global>"
                updated = updated[:match.start()] + replacement + updated[match.end():]
                entries = b""
            elif empty:
                raise SaveToolError("Có nhiều khối Global")
            else:
                endings = list(re.finditer(rb"</root\s*>", updated))
        if entries:
            if len(endings) != 1:
                raise SaveToolError("Không xác định được Global/root để thêm avatar")
            position = endings[0].start()
            updated = updated[:position] + entries + updated[position:]
    verified = avatar_states(updated)
    if any(verified[avatar_id]["state"] is not unlocked for avatar_id in selected):
        raise SaveToolError("Xác minh trạng thái avatar thất bại")
    unchanged = sum(states[avatar_id]["state"] is unlocked for avatar_id in selected)
    return updated, {"total": len(selected), "added": len(missing),
                     "updated": len(selected) - len(missing) - unchanged,
                     "already_unlocked": unchanged if unlocked else 0,
                     "unchanged": unchanged, "unlocked": unlocked}


def unlock_all_avatars(xml: bytes) -> tuple[bytes, dict]:
    return set_avatar_unlocks(xml, TSVIP_AVATAR_IDS, True)


def print_avatar_list(xml: bytes, state_filter: str = "all") -> None:
    states = avatar_states(xml)
    if state_filter not in ("all", "open", "locked", "missing"):
        raise SaveToolError("Bộ lọc avatar không hợp lệ")
    labels = {True: "ĐÃ MỞ", False: "KHÓA", None: "CHƯA CÓ CỜ"}
    rows = []
    for avatar_id, info in states.items():
        state = info["state"]
        if state_filter == "open" and state is not True:
            continue
        if state_filter == "locked" and state is not False:
            continue
        if state_filter == "missing" and state is not None:
            continue
        label = labels.get(state, f"CỜ LẠ: {state}")
        suffix = "" if info["catalog"] else " [ngoài danh sách APK]"
        rows.append(f"{avatar_id:>4}: {label}{suffix}")
    print("\nID avatar và trạng thái cờ mở khóa (không phải avatar đang dùng)")
    for index in range(0, len(rows), 3):
        print(" | ".join(f"{row:<28}" for row in rows[index:index + 3]))
    print(f"Hiển thị {len(rows)} / {len(states)} avatar. CHƯA CÓ CỜ nghĩa là không có cờ mở khóa trong save.")


def unlock_all_avatars_prompt() -> None:
    # Kept as a compatibility entry point for menu 15.
    SESSION.require_loaded()
    while True:
        assert SESSION.current_xml is not None
        states = avatar_states(SESSION.current_xml)
        opened = sum(info["state"] is True for info in states.values())
        locked = sum(info["state"] is False for info in states.values())
        missing = sum(info["state"] is None for info in states.values())
        print(f"\n--- 15. AVATAR | Mở: {opened} | Khóa: {locked} | Chưa có cờ: {missing} ---")
        print("1. Xem tất cả ID và trạng thái")
        print("2. Xem avatar đã mở")
        print("3. Xem avatar đang khóa")
        print("4. Xem avatar chưa có cờ")
        print("5. Mở khóa các ID chọn")
        print("6. Khóa lại các ID chọn (đặt cờ = 0)")
        print(f"7. Mở tất cả {len(TSVIP_AVATAR_IDS)} avatar trong danh sách TSVIP")
        print(f"8. Khóa tất cả {len(TSVIP_AVATAR_IDS)} avatar trong danh sách TSVIP (đặt cờ = 0)")
        print("0. Quay lại menu chính")
        choice = input("Chọn: ").strip()
        if choice == "0":
            return
        try:
            if choice in ("1", "2", "3", "4"):
                print_avatar_list(SESSION.current_xml, {"1": "all", "2": "open", "3": "locked", "4": "missing"}[choice])
                input("Nhấn Enter để quay lại danh sách...")
                continue
            if choice not in ("5", "6", "7", "8"):
                print("Lựa chọn không hợp lệ.")
                continue
            unlocked = choice in ("5", "7")
            if choice in ("5", "6"):
                raw = input("Nhập ID (vd 1,3,5-20; Enter để hủy): ").strip()
                if not raw:
                    continue
                ids = parse_avatar_selection(raw, states)
                print("ID được chọn:", ", ".join(ids))
            else:
                ids = list(TSVIP_AVATAR_IDS)
            updated, report = set_avatar_unlocks(SESSION.current_xml, ids, unlocked)
            verb = "MỞ KHÓA" if unlocked else "KHÓA LẠI"
            print(f"{verb} {report['total']} avatar | Thêm cờ: {report['added']} | Đổi cờ: {report['updated']} | Đã đúng trạng thái: {report['unchanged']}")
            if not unlocked:
                print("Khóa lại chỉ đặt cờ Unlocked_ava<ID>=0; chưa kiểm chứng hành vi khóa trong game.")
                print("Thao tác không đổi avatar đang chọn; avatar đó có thể nằm trong danh sách khóa.")
            if updated == SESSION.current_xml:
                print("Không có thay đổi.")
                continue
            if not ask_yes_no(f"Xác nhận {verb.lower()} danh sách trên?"):
                print("Đã hủy.")
                continue
            SESSION.apply_xml(updated)
            print("Đã cập nhật XML làm việc. Về menu chính, chọn 43 ghi vào game hoặc 42 xuất local.")
        except SaveToolError as exc:
            print(f"Lỗi: {exc}")
        except KeyboardInterrupt:
            print("\nĐã hủy thao tác.")


# TSVIP DecorationsScreen: p33.a (normal), p33.b (signs), if2.l (Merge/Expedition).
DECORATION_GROUPS = {'normal': ('1400_Christmas_Decoration', '5years', 'Apple_Garden', 'AquariumAtlantic_ancient', 'Arabic_Tent', 'Atlantis_fence', 'Basil_Cath', 'Beach_volleyball', 'BobsleighRace', 'Book_Store', 'Bungalow_hammock', 'CafeTube', 'Cafe_Vineyard', 'Cafe_Waterfall', 'Carousel_Octopus', 'Cars_Exposition', 'Castle_Trampoline', 'Cave_Place', 'ChineseBanner', 'ChineseDog', 'ChineseNYTree', 'ChineseNY_pigStatue', 'Chinese_fence', 'ChocolateFactoryDecor', 'ChristmasBall', 'ChristmasBanner', 'ChristmasCarousel', 'ChristmasTrain_Bridge', 'Christmas_Cafe', 'Christmas_Chorus', 'Christmas_Fair', 'Christmas_GingerbreadMan', 'Christmas_Ice_skating', 'Christmas_Santa_House', 'Christmas_Santas_Reinde', 'Christmas_Snow_fortress', 'Christmas_Snowman', 'Christmas_Urban_tree', 'Christmas_angel', 'Christmas_fence', 'Christmas_gifts', 'Christmas_lantern', 'Christmas_presentsock', 'Christmas_scene', 'Christmas_train', 'Circus_Camping', 'Color_Egg', 'Connect_Station', 'Cover_Gift', 'CowArtist', 'Cowboy_Tower', 'Crab_Cook', 'CraneFountain', 'CustomChuiYingTai', 'CustomDragonBoat', 'CustomDragonHouse', 'CustomDragonHouseDong', 'CustomGuanTangGe', 'CustomMeiGuiChengBao', 'CustomMeiGuiGongMen', 'CustomMeiGuiJianLou', 'CustomPanda', 'CustomQiaoKeLiWuZi', 'CustomQiuShouTuWo', 'CustomSiheyuan', 'CustomTangGuoBaShi', 'CustomTiger2', 'CustomTingYuan', 'CustomYeGuZhou', 'CustomYinDiaoJu', 'CustomYutuShip', 'CustomZiLingGan', 'Cycle_Parking', 'Decor_FlowerShop', 'Decor_Ropepark', 'Decor_TreeHouse', 'Dino_Safe', 'DiscoDecorationSP8', 'DroneRace_plane', 'Easter2017Decor', 'EasterStump', 'EasterVineyard', 'Easter_bunnies', 'Easter_fence', 'Easter_fountain', 'EgyptPapyrusBoat', 'EgyptPharaohStatue', 'EgyptPyramid', 'Fairy_Fountain', 'Fashion_Boutique', 'FinalReward_gardenCinema', 'Flower_Statue', 'Flower_Store', 'Fruit_Football', 'GhostGarden', 'Giant_Snowman', 'Ginger_House', 'GingerbreadManHotChocolate', 'Glamping_Camp', 'Glamping_House', 'GlassBridge', 'Gold_Diggers', 'Gothic_Tower', 'Grape_Press', 'Greenhouse_Predator', 'Hall_Fame', 'Halloween2017Decor', 'Halloween_Organ', 'Halloween_Park', 'Happy_Aquarium', 'Headless_Horseman', 'HelixJump_TreasureIsland', 'Helix_Pazzles', 'Horn_Harvest', 'Horse_Carousel', 'HotDogSwing', 'Hot_Fountain', 'HouseEgyptian', 'House_Garden', 'IceExhibition_runner', 'Installation_Insomnia', 'InstrumentWorkshop', 'JazzClub', 'JurassicPark', 'KidsRailway', 'KingdomCentre', 'LiraFountain', 'LoveLock', 'LoveTunnel', 'Marsh_treasure', 'Mechanic_Car', 'MegaCake', 'MiniTownship', 'Mobile_Market', 'MountainChalet_CozyHouse', 'MountainChalet_HuskyHouse', 'MusicCarousele', 'Music_Scene', 'NewCinema_gatsby', 'New_Year', 'NewyearGlobe', 'Notre_Dame', 'Olympic_Baseballtraining', 'Olympic_Snowmachine', 'Organic_Shop', 'Palace_of_the_sky', 'PaletteSculpture', 'Paris_Street', 'PencilHouse_art', 'PigOscar', 'PinSculpture', 'PirateFort', 'Plank_Decor', 'Plank_Jeep', 'Plank_Shop', 'Plank_Werewolf', 'Pumpkin_House', 'Pumpkin_Metro', 'RainbowArch', 'RestoratorBuild2', 'Rialto_Bridge', 'SailingRaft_treasure', 'SaleSquare', 'Saloon_GrayMouse', 'SantaSleigh', 'Santa_Reception', 'SculptureExhibition_art', 'SeaFence_fence', 'SheepElf_runner', 'SheepSlide', 'ShipTower', 'Ship_Fight', 'Ski_Shop', 'SmallWaterfall', 'Snowman', 'SpaceRocket', 'SpecialBeauty_AlbatrossOnBoat', 'SpecialBeauty_Aquarium', 'SpecialBeauty_AquaticJetpack', 'SpecialBeauty_AstrologerTower', 'SpecialBeauty_AvtoAttraction', 'SpecialBeauty_Banner', 'SpecialBeauty_BathyscaphDive', 'SpecialBeauty_BeePilot', 'SpecialBeauty_BirthdayBanner', 'SpecialBeauty_BoatWithPirateFlag', 'SpecialBeauty_BonfireCamp', 'SpecialBeauty_CaptainStatueSeason', 'SpecialBeauty_China_dragon', 'SpecialBeauty_China_fish', 'SpecialBeauty_China_house', 'SpecialBeauty_China_lantern', 'SpecialBeauty_China_lightTree', 'SpecialBeauty_China_maneki', 'SpecialBeauty_China_monkey', 'SpecialBeauty_CityDay_arch_of_flowers', 'SpecialBeauty_CityDay_boat_of_flowers', 'SpecialBeauty_CityDay_flowerbed_car', 'SpecialBeauty_CityDay_pavlin', 'SpecialBeauty_CityDay_sheeps', 'SpecialBeauty_CommonwealthStatue', 'SpecialBeauty_Digging_Tyrannosaurus', 'SpecialBeauty_Dovecote', 'SpecialBeauty_EasterRabbit', 'SpecialBeauty_EasterSymbol', 'SpecialBeauty_EasterTopiary', 'SpecialBeauty_Easter_ChocolateFoun', 'SpecialBeauty_Easter_EasterBunny', 'SpecialBeauty_Easter_EasterChicken', 'SpecialBeauty_Easter_EasterTree', 'SpecialBeauty_Easter_FabergeEgg', 'SpecialBeauty_Easter_FabergeEgg_blue', 'SpecialBeauty_Easter_RabbitHouse', 'SpecialBeauty_Easter_SpringGirl', 'SpecialBeauty_Excalibur', 'SpecialBeauty_FrogStatue', 'SpecialBeauty_FruitBridge', 'SpecialBeauty_FruitKiosk', 'SpecialBeauty_Ghostbuster', 'SpecialBeauty_GiantWatermelon', 'SpecialBeauty_HelicopterTrampoline', 'SpecialBeauty_HorrorHorses', 'SpecialBeauty_InflatableCastle', 'SpecialBeauty_KidKite', 'SpecialBeauty_KingsThrone', 'SpecialBeauty_LanternGhost', 'SpecialBeauty_MechanicalRodeo', 'SpecialBeauty_MedievilCarrige', 'SpecialBeauty_MedievilTavern', 'SpecialBeauty_MedievilTaverna', 'SpecialBeauty_OctopusChest', 'SpecialBeauty_PirateTavern', 'SpecialBeauty_PumpkinWheel', 'SpecialBeauty_RomanticDinner', 'SpecialBeauty_RuinsDive', 'SpecialBeauty_RunwayAirplane', 'SpecialBeauty_SeaCarousel', 'SpecialBeauty_ShipGun', 'SpecialBeauty_SpiderTree', 'SpecialBeauty_StatueFisherman', 'SpecialBeauty_StatueOfTheCook', 'SpecialBeauty_StatueWorkTogether', 'SpecialBeauty_Sun', 'SpecialBeauty_SwingPlane', 'SpecialBeauty_ThreeHouses', 'SpecialBeauty_Totem', 'SpecialBeauty_TreeBroccoli', 'SpecialBeauty_TruckCamping', 'SpecialBeauty_Valentine_flowercart', 'SpecialBeauty_WaterMill', 'SpecialBeauty_WaterTower', 'SpecialBeauty_ancor', 'SpecialBeauty_animal_tower', 'SpecialBeauty_bioplan', 'SpecialBeauty_birthday_ballon', 'SpecialBeauty_chef_balloon', 'SpecialBeauty_china_dragon2017', 'SpecialBeauty_cockleshell', 'SpecialBeauty_firerooster', 'SpecialBeauty_fishermans_house', 'SpecialBeauty_flooded_tower', 'SpecialBeauty_flyButterfly', 'SpecialBeauty_flyChicken', 'SpecialBeauty_flyCow', 'SpecialBeauty_flyDuck', 'SpecialBeauty_flyElep', 'SpecialBeauty_flyOctopus', 'SpecialBeauty_flyParrot', 'SpecialBeauty_flyPenguin', 'SpecialBeauty_flyPig', 'SpecialBeauty_flyPlane', 'SpecialBeauty_flySheep', 'SpecialBeauty_flyTurtle', 'SpecialBeauty_flyWhale', 'SpecialBeauty_fountain_restourante', 'SpecialBeauty_galorobot', 'SpecialBeauty_harvest_figure', 'SpecialBeauty_ice_cream_cafe', 'SpecialBeauty_jumping_fish', 'SpecialBeauty_mermaid', 'SpecialBeauty_mobile_coffee_truck', 'SpecialBeauty_octopus', 'SpecialBeauty_paukohod', 'SpecialBeauty_perpetumlucerna', 'SpecialBeauty_planeAmphibian', 'SpecialBeauty_plungerDive', 'SpecialBeauty_redBridge', 'SpecialBeauty_seahorse', 'SpecialBeauty_statue_pig', 'SpecialBeauty_topiary_egg', 'SpecialBeauty_walking_castle', 'SpecialBeauty_wealth_bowl', 'SpecialBeauty_whalefountain_fishing', 'Summer_Cafe', 'Surf_Decor', 'Surf_Pool', 'Surf_Rental', 'Surf_Sale', 'Surfingers_Trampoline', 'Sweet_Tree', 'Tiki_Bar', 'TouristParking_treasure', 'Tower_of_Pisa', 'Town_Fair', 'TrainConductor', 'Tree_Market', 'Tree_sakura', 'Trio', 'Trucks_Decotor', 'Trucks_PirateBistro', 'Valentine_Bunny', 'Valentine_CupidsArrow', 'Valentine_Flowerbed', 'Valentine_Gazebo_lovers', 'Valentine_Pond_with_swans', 'Valentine_Statue_Lovers', 'Valentine_Statue_of_cupid', 'Valentine_Swing_lovers', 'Valentine_Teddy_bear', 'Valentine_Teddy_bear2', 'Valentine_Topiary', 'Valentine_cats', 'Valentine_diamond_heart', 'Valentine_flowerbed', 'Valentine_fountain_eternallove', 'Valentine_heartInHands', 'Valentine_heart_pedestal', 'Valentine_justMarried', 'Valentine_key', 'Valentine_lovearch', 'Valentine_lovers_bench', 'Valentine_lovers_cart', 'Valentine_moon_from_heaven', 'Valentine_peacock_inlove', 'Valentine_peacock_inlovemllove', 'Valentine_pigeons_love', 'Valentine_plush_cat', 'Valentine_postsheep', 'Valentine_serenade', 'Valentine_statue_prince', 'Valentine_topiary_hearts', 'Valentine_topiary_heartsmllove', 'Wagon_Mountain', 'Watchtower', 'WaterBungalowSP9', 'Wedding3D_Decor', 'WitchPot', 'WitchStatue_halloween', 'airboat_plank', 'airship_base', 'ancient_bridge', 'apple_tree', 'aquapark_helix', 'aquariumHouse_fishing', 'aquarium_v1', 'arabic_al_ain_palace', 'arabic_horse_statue', 'arabic_jin_lamp', 'arabic_oasis', 'arbor', 'archaeology_atlantis', 'archery_runner', 'asphalt', 'bagrunning_easter', 'ballShooting_helix', 'baloon_castle', 'baloons', 'bamboo_runner', 'baobab', 'bar_fin', 'baseball', 'basketball_1x2', 'beach_dance_floor', 'beach_fruit_mix', 'beach_party_bar', 'beach_yellow_submarine', 'bears_family', 'beauty_3_ballon', 'beauty_5y_monument', 'beauty_Coconut_bar', 'beauty_DivingTower_olympiad', 'beauty_Flower_gates', 'beauty_FootballDog', 'beauty_Goalkeeper', 'beauty_Gong', 'beauty_Luxury_gates', 'beauty_MovieFountain', 'beauty_OlympicFountain', 'beauty_SketebordPlace', 'beauty_SuperheroStand', 'beauty_TrainingGround_olympiad', 'beauty_acacia_giraffe', 'beauty_acrobats_stilts', 'beauty_ancient_drums', 'beauty_ancient_town', 'beauty_animals_pasta', 'beauty_araguaney', 'beauty_arch_balloon', 'beauty_artist_quarter', 'beauty_astronomer_tower', 'beauty_atlantis_aquarium', 'beauty_atlantis_boulevard', 'beauty_atlantis_hotel', 'beauty_atlantis_ruins', 'beauty_atlantis_statue', 'beauty_atlas_hand', 'beauty_balloon_dancer', 'beauty_baloon_flowers', 'beauty_burdzh_halifa', 'beauty_cancer_hermit', 'beauty_candy_bridge', 'beauty_candy_carousel', 'beauty_candy_house', 'beauty_candy_tree', 'beauty_carousel', 'beauty_cave_in_jungle', 'beauty_chalk_elephant', 'beauty_chalk_jiraffe', 'beauty_chalk_lion', 'beauty_chalk_zebra', 'beauty_children_pirates', 'beauty_china_town', 'beauty_coloring_cubes', 'beauty_confectioner_cow', 'beauty_coral_garden', 'beauty_cottage_horn', 'beauty_delonix', 'beauty_diamond', 'beauty_dinosaur', 'beauty_divers_boat', 'beauty_dog_ballon', 'beauty_dogs_arctic', 'beauty_dolphins', 'beauty_dragon_boat', 'beauty_dragon_dance', 'beauty_easter_lantern', 'beauty_easter_stump', 'beauty_elephants', 'beauty_elf_house', 'beauty_experiment_knowledgetower', 'beauty_experiment_laboratory', 'beauty_experiment_monument', 'beauty_experiment_plasma', 'beauty_experiment_projector', 'beauty_finic_palm', 'beauty_fireworkshop', 'beauty_fish_ballon', 'beauty_fish_market', 'beauty_floral_sheeps', 'beauty_flower_vase', 'beauty_flowerhouse', 'beauty_flyHouse', 'beauty_flyMedusa', 'beauty_flyingship', 'beauty_friendBench_fday', 'beauty_ghost_ship', 'beauty_goldberg_machine', 'beauty_gondola', 'beauty_graffiti_competition', 'beauty_greengrocery', 'beauty_halloween_scary_crypt', 'beauty_halloween_skeleton_orchestra', 'beauty_houseMaldives', 'beauty_iceDeer', 'beauty_ice_castle', 'beauty_iceberg', 'beauty_iceberg_penguin', 'beauty_icebreaker', 'beauty_jirafe_dall', 'beauty_juggler', 'beauty_jungle_monk', 'beauty_jungle_riverhouse', 'beauty_jungle_ruins', 'beauty_jungle_sanctuary', 'beauty_jungle_totems', 'beauty_lake_house', 'beauty_large_sundial', 'beauty_luxury_house', 'beauty_mammoth', 'beauty_party_pirates', 'beauty_peacock_statue', 'beauty_pine_tree', 'beauty_pirate_ship_bow', 'beauty_pizzeria_pasta', 'beauty_plane_steam', 'beauty_plane_vought_v173', 'beauty_playground2', 'beauty_plushSheep', 'beauty_polarStation', 'beauty_polar_bear', 'beauty_poseidon', 'beauty_prehistoric_house', 'beauty_primitive_artist', 'beauty_puddleJumper', 'beauty_pyramid_knife', 'beauty_rhino', 'beauty_rhododendron', 'beauty_runner_cablecar', 'beauty_sailboat', 'beauty_saloon', 'beauty_santa_plank', 'beauty_sea_researchers', 'beauty_seahouse_decoration', 'beauty_sequoia', 'beauty_serf_pool', 'beauty_shipUlysses_ancient', 'beauty_ship_pool', 'beauty_simulator_plane', 'beauty_skatingPenguins', 'beauty_snowfortress', 'beauty_snowman_skater', 'beauty_snowslide', 'beauty_solar_system', 'beauty_souvenir_shop', 'beauty_space_cosmonaut_cow', 'beauty_space_mars_rover', 'beauty_space_shuttle', 'beauty_stonehenge', 'beauty_submarine', 'beauty_sweet_hill', 'beauty_swing_giraffe', 'beauty_swing_palm', 'beauty_tarzan_tree', 'beauty_thai_temple', 'beauty_throwing_knives', 'beauty_titans', 'beauty_torchbearer_olympiad', 'beauty_treasure_chest', 'beauty_tree_ballon', 'beauty_triathlon_runner', 'beauty_ufo', 'beauty_venus_flytrap', 'beauty_waterSlide', 'beauty_water_monster', 'beauty_watercraft', 'beauty_winners_place_olympiad', 'beauty_winter_cannon', 'beauty_wisteria', 'beauty_yeti', 'berryTree_knife', 'bigPicnic', 'bigTractor_rescue', 'big_ban', 'birthdaynineDecoration', 'blender_knife', 'boat00_fin', 'boat02_fin', 'bookTree_jungle', 'bridge00_fin', 'bridge01_fin', 'bronze_bull', 'buek1', 'buek2', 'buek3', 'buek4', 'buek5', 'buek6', 'buek7', 'buek8', 'bullStatue', 'bullStatue_runner', 'cactus', 'cafe_rescue', 'camping', 'camping_wildwest', 'candyCastle_helix', 'candyTrain_surfingers', 'candy_fence', 'candy_gate', 'candy_rainbow', 'captainStatue_pirate', 'caramelApple_surfingers', 'carousel_elephants', 'carousel_helix', 'carousel_runner', 'cartRace_blackfriday', 'castle', 'chamber_halloween', 'champion_cup', 'chess_arabic', 'chickchik', 'christmasComing', 'christmasPlace_xmas2022', 'christmasTree_xmas2022', 'christmas_santa_helper', 'christmas_snowball', 'coconutArmchair_bungalow', 'colorFountain_match3', 'contactZoo_rescue', 'cowboyStatue_wildwest', 'craftsmanWorking_egypt', 'crater', 'crocodile', 'curling_runner', 'danceMachine_helix', 'dancingFountains', 'darkForestWithTrainSign', 'deerRiding_plank', 'dirigeablestatue', 'discoForever_music', 'discusThrower_ancient', 'dragon_statue_SP_800', 'dynamometer_rescue', 'easterHammock', 'easterRailroad', 'easterRibbons', 'easter_factory', 'easter_pond', 'easterhouse_tree', 'easternBazar', 'eifel_tower', 'empire_state_v1', 'expandBuy', 'expandBuyAvailable', 'fair_rescue', 'fairy_water', 'falcon_hunting', 'farmmusic', 'figureSkating_xmas2022', 'filmmaking_treasure', 'flag', 'flamingo', 'floating_lanterns', 'flowerUnderHood', 'flower_fence', 'flower_hedge', 'flower_house', 'flower_shop', 'flower_swing', 'flowerbed1', 'flowerbed2', 'flowerbed_daffodils', 'flowerbed_gerbera', 'flowerbed_gladiolus', 'flowerbed_irises', 'flowerbed_poppies', 'flowering_tree', 'flyBee', 'flyDragon', 'flyLantern_santa', 'flyPanda', 'flyValentineBalloons', 'flyValentineCupid', 'flyingShip_treasure', 'foodshow_burger', 'football', 'fountain1', 'fountain2', 'fountain4', 'fountain_swan', 'fountain_tree', 'fountain_whale', 'fountainbig', 'freedom_v1', 'fruitFootball_knife', 'fruitPark_knife', 'fruitSlicing_knife', 'gallery_art', 'gameboy_helix', 'gardens_arabic', 'ghostlyCarriage', 'giantVegetables_rescue', 'girrafe', 'globalFlight_plane', 'gnomes', 'golden_gate', 'gorilla', 'granite_fence', 'gravelroad', 'green', 'green10', 'green12', 'green14', 'green16', 'green18', 'green2', 'green20', 'green5', 'green5_2', 'green8', 'green9', 'green_bird', 'green_bunny', 'green_dolphin', 'green_elephant', 'green_peacock', 'green_tree1', 'green_tree2', 'green_tree3', 'green_turtle', 'greenbox_fin', 'greennilai', 'ground', 'groundroad', 'halloween_castle', 'halloween_cat', 'halloween_fountain', 'halloween_gargoyle', 'halloween_ghost_ship', 'halloween_haunted_house', 'halloween_museum', 'halloween_pump', 'halloween_sarcophagus', 'halloween_scarecrow', 'halloween_tree', 'halloween_witch', 'halloween_witch_hire', 'hay', 'heartTree_valentine', 'hedge', 'helmetOctopus_ancient', 'hockeyField_runner', 'hotSpring_match3', 'house10', 'house40', 'house45', 'house48', 'house56', 'iceArch_arctic', 'iceDragon', 'iceLake', 'iceSculptures_plank', 'ice_dino', 'iglu', 'installation_art', 'island_knife', 'jakaranda', 'jellyBounce', 'jetpack_plane', 'juice_fountain', 'katamaran', 'kitchen_plank', 'koala', 'labyrinth_easter', 'lakehouse_boattrip', 'lakehouse_home', 'landing_fence', 'lastHour_plank', 'lifeguard_hut', 'lion', 'lion_slides', 'lookout_point', 'loveTower', 'loveWings', 'love_bridge', 'love_flowers', 'lovegarden', 'lowriders_rescue', 'luxury_fence', 'mammoth_match3', 'maya_calendar', 'mechDragon_medieval', 'mechStrawman', 'minotaur_ancient', 'monkeys_plank', 'monument1', 'monument2', 'monument3', 'monument4', 'monument5', 'monument_tools', 'movieMonument', 'movieMuseum', 'museum_atlantis', 'musicQuarter_music', 'ninja_knife', 'noodle_shop', 'oasis_egypt', 'oilDerrick', 'olympicVillage_runner', 'organ_music', 'palmHotel', 'palma1', 'palma2', 'palma4', 'palma_totem', 'panda', 'park1_1x1', 'park1_1x2', 'park2_1x1', 'parking', 'parking_common', 'parking_green_side', 'parking_green_yard', 'penguin', 'penguinIcehole_xmas2022', 'petronas', 'phone_box', 'photoStand_valentine', 'photo_v1', 'picnic', 'pinball_helix', 'pineapple_knife', 'pirateShip_treasure', 'pirateStatue_treasure', 'pizzacutting_pasta', 'planeAircraftReward', 'plank1_fin', 'plank3_fin', 'playground', 'plushUnicorn_valentine', 'polarman_arctic', 'pond', 'pondSwans', 'pond_mother_earth', 'pond_with_carp', 'pool', 'poolhall', 'pumpkinrace', 'pyramide', 'quay_fin', 'quiosk_plank', 'radar', 'radiorace_rescue', 'railway_station', 'rainbowFair_helix', 'ratGarden_jump', 'redLiliesPond', 'reef_hedge', 'reserve1x2_v1', 'reserve2x2_v1', 'reserve3x3_v1', 'retro_avto', 'ringGame_surfingers', 'robocafe_cakeshop', 'rockCat_music', 'rodeoHelic_runner', 'roman_chariot', 'rose_bush', 'rugby_stadium', 'sailHotel', 'sailing_race', 'sand', 'sausage_restorator', 'scarab_egypt', 'scarecrow', 'scriptorium_medieval', 'sculptor_ancient', 'seaStation_dive', 'sea_gate', 'seal', 'seasonCinecamera_cinema', 'seasonUfoStudio_cinema', 'shack', 'shark_slide', 'shearedTree', 'shellgame_helix', 'ship', 'shipAttraction_pirate', 'shooting_rescue', 'skatePark', 'skisCow_olympiad', 'slide_match3', 'small_green_tree_04', 'snow', 'snowFight_plank', 'snowboardSheep_olympiad', 'snowboard_runner', 'southernflowers', 'spacegarden', 'spaceneedle_v1', 'sphinx_v1', 'stairs_match3', 'statue_artist', 'statue_boat_gold', 'statue_chemist', 'statue_fireman', 'statue_flyboy', 'statue_footballer', 'statue_general', 'statue_geneticist', 'statue_musican', 'statue_neanderthal', 'statue_policeman', 'statue_thinker', 'statue_tourist', 'statue_writer', 'stork_statue', 'stream_hedge', 'streetCinema_cakeshop', 'sunflower', 'swan', 'sydney_opera', 'tajmahal_v1', 'teahouse', 'tennis', 'thanksgiving_CarrotTree', 'thanksgiving_vegetableBasket', 'thanksgiving_vegetableHouse', 'thanksgiving_vegetablePlace', 'theaterOdeon_ancient', 'throneHall_medieval', 'tiger', 'topiary_castle', 'topiary_competition', 'toyMachine_helix', 'track', 'tractor_and_hay', 'trainchicken', 'travelingTruck_rescue', 'tree_adenium', 'tree_shaping', 'tree_with_stairs', 'trojanHorse_ancient', 'trouveres_medieval', 'turbosledge_santa', 'tvtower_v1', 'ufoClue', 'upsideDownHouse_bungalow', 'vegetables', 'vetryak', 'village_jungle', 'water', 'water_flowers_1', 'water_flowers_2', 'water_park', 'waterfall_mountain_surfingers', 'wateringCan_easter', 'wavePool', 'weeping_willow', 'weightlifter_runner', 'well', 'white_fence', 'whiterose_tree', 'wildpark', 'wildwest_cinema', 'windmill', 'winterYurt_xmas2022', 'wishingWell', 'workshopCrash', 'yacht', 'yacht_fin', 'yellow_roses', 'young_gardeners', 'zebra', 'zoo_caffe', 'zoo_cinema', 'zoo_cocktail_store', 'zoo_contact', 'zoo_decor', 'zoo_eatery', 'zoo_icecream_shop', 'zoo_restaurant', 'zoo_shop'), 'special': ('ExpeditionDecoration', 'ExpeditionDecoration2', 'ExpeditionDecoration3', 'ExpeditionDecoration4', 'ExpeditionDecoration5', 'ExpeditionDecoration6', 'ExpeditionDecoration7', 'ExpeditionDecoration8', 'ExpeditionDecoration9', 'ExpeditionDecoration10', 'ExpeditionDecoration11', 'ExpeditionDecoration12', 'ExpeditionDecoration13', 'ExpeditionDecoration14', 'ExpeditionDecoration15', 'ExpeditionDecoration16', 'ExpeditionDecoration17', 'ExpeditionDecoration18', 'ExpeditionDecoration19', 'ExpeditionDecoration20', 'ExpeditionDecoration21', 'ExpeditionDecoration22', 'ExpeditionDecoration25', 'ExpeditionDecoration34', 'ExpeditionDecoration37', 'ExpeditionDecoration38', 'ExpeditionDecoration39', 'ExpeditionDecoration40', 'ExpeditionDecoration41', 'ExpeditionDecoration43', 'ExpeditionDecoration44', 'ExpeditionDecoration45', 'Merge2Decoration1', 'Merge2Decoration2', 'Merge2Decoration3', 'Merge2Decoration4', 'Merge2Decoration5', 'Merge2Decoration6', 'Merge2Decoration7', 'Merge2Decoration8', 'Merge2Decoration9', 'Merge2Decoration10', 'Merge2Decoration11', 'Merge2Decoration12'), 'sign': ('skin_city_sign_IronCitySign', 'skin_city_sign_MillSign', 'skin_city_sign_SP_790_sign', 'skin_city_sign_TV_city_sign', 'skin_city_sign_arabic_sign', 'skin_city_sign_asian_sign', 'skin_city_sign_birthday_10years', 'skin_city_sign_birthday_sign', 'skin_city_sign_cactus_sign', 'skin_city_sign_christmas_sign', 'skin_city_sign_cinema_sign', 'skin_city_sign_cow_sign', 'skin_city_sign_custom_SheNian', 'skin_city_sign_def_sign', 'skin_city_sign_disco_city_sign', 'skin_city_sign_dry_fountain_sign', 'skin_city_sign_easter_sign', 'skin_city_sign_expedition22_2200_sign', 'skin_city_sign_expedition23_2200_sign', 'skin_city_sign_expedition24_2300_sign', 'skin_city_sign_expedition25_2300_sign', 'skin_city_sign_expedition26_2400_sign', 'skin_city_sign_expedition27_2400_sign', 'skin_city_sign_expedition28_2500_sign', 'skin_city_sign_expedition29_2500_sign', 'skin_city_sign_expedition30_2600_sign', 'skin_city_sign_expedition31_2600_sign', 'skin_city_sign_expedition32_2700_sign', 'skin_city_sign_expedition33_2700_sign', 'skin_city_sign_expedition36_2900_sign', 'skin_city_sign_farm_sign', 'skin_city_sign_farm_signMn', 'skin_city_sign_flowerbed_sign', 'skin_city_sign_frank_halloween', 'skin_city_sign_furniture_sign', 'skin_city_sign_halloween_sign', 'skin_city_sign_harvest_sign', 'skin_city_sign_ilove_sign', 'skin_city_sign_lamp_board_sign', 'skin_city_sign_mechanic_sign', 'skin_city_sign_music_sign', 'skin_city_sign_mystical_events', 'skin_city_sign_neon_sign', 'skin_city_sign_neon_signMvents', 'skin_city_sign_palm_trees', 'skin_city_sign_regatta_2100_sign', 'skin_city_sign_regatta_2300_sign', 'skin_city_sign_regatta_2400_sign', 'skin_city_sign_regatta_3000_sign', 'skin_city_sign_regatta_3100_sign', 'skin_city_sign_rock_sign', 'skin_city_sign_rock_sign1_71', 'skin_city_sign_rock_signM', 'skin_city_sign_ruminant_machine', 'skin_city_sign_smoothiebar_sign', 'skin_city_sign_snowboard_sign', 'skin_city_sign_stone_sign', 'skin_city_sign_vegas_sign', 'skin_city_sign_wild_west_sign', 'skin_city_sign_winged_sign', 'skin_city_sign_wooden_sign')}
DECORATION_FRAGMENTS = {'ExpeditionDecoration': '<ExpeditionDecoration guid=""><base active="1" beenSetOnField="1"/>\n<part1 active="1" beenSetOnField="1"/>\n<part2 active="1" beenSetOnField="1"/>\n<part3 active="1" beenSetOnField="1"/>\n</ExpeditionDecoration>', 'ExpeditionDecoration2': '<ExpeditionDecoration2 guid=""><base active="1" beenSetOnField="1"/>\n<part1 active="1" beenSetOnField="1"/>\n<part2 active="1" beenSetOnField="1"/>\n<part3 active="1" beenSetOnField="1"/>\n<part4 active="1" beenSetOnField="1"/>\n</ExpeditionDecoration2>', 'ExpeditionDecoration3': '<ExpeditionDecoration3 guid=""><base active="1" beenSetOnField="1"/>\n<part1 active="1" beenSetOnField="1"/>\n<part2 active="1" beenSetOnField="1"/>\n<part3 active="1" beenSetOnField="1"/>\n<part4 active="1" beenSetOnField="1"/>\n</ExpeditionDecoration3>', 'ExpeditionDecoration4': '<ExpeditionDecoration4 guid=""><base active="1" beenSetOnField="1"/>\n<part1 active="1" beenSetOnField="1"/>\n<part2 active="1" beenSetOnField="1"/>\n<part3 active="1" beenSetOnField="1"/>\n<part4 active="1" beenSetOnField="1"/>\n</ExpeditionDecoration4>', 'ExpeditionDecoration5': '<ExpeditionDecoration5 guid=""><base active="1" beenSetOnField="1"/>\n<part1 active="1" beenSetOnField="1"/>\n<part2 active="1" beenSetOnField="1"/>\n<part3 active="1" beenSetOnField="1"/>\n<part4 active="1" beenSetOnField="1"/>\n</ExpeditionDecoration5>', 'ExpeditionDecoration6': '<ExpeditionDecoration6 guid=""><base active="1" beenSetOnField="1"/>\n<part1 active="1" beenSetOnField="1"/>\n<part2 active="1" beenSetOnField="1"/>\n<part3 active="1" beenSetOnField="1"/>\n<part4 active="1" beenSetOnField="1"/>\n</ExpeditionDecoration6>', 'ExpeditionDecoration7': '<ExpeditionDecoration7 guid=""><base active="1" beenSetOnField="1"/>\n<part1 active="1" beenSetOnField="1"/>\n<part2 active="1" beenSetOnField="1"/>\n<part3 active="1" beenSetOnField="1"/>\n<part4 active="1" beenSetOnField="1"/>\n</ExpeditionDecoration7>', 'ExpeditionDecoration8': '<ExpeditionDecoration8 guid=""><base active="1" beenSetOnField="1"/>\n<part1 active="1" beenSetOnField="1"/>\n<part2 active="1" beenSetOnField="1"/>\n<part3 active="1" beenSetOnField="1"/>\n<part4 active="1" beenSetOnField="1"/>\n</ExpeditionDecoration8>', 'ExpeditionDecoration9': '<ExpeditionDecoration9 guid=""><base active="1" beenSetOnField="1"/>\n<part1 active="1" beenSetOnField="1"/>\n<part2 active="1" beenSetOnField="1"/>\n<part3 active="1" beenSetOnField="1"/>\n<part4 active="1" beenSetOnField="1"/>\n</ExpeditionDecoration9>', 'ExpeditionDecoration10': '<ExpeditionDecoration10 guid=""><base active="1" beenSetOnField="1"/>\n<part1 active="1" beenSetOnField="1"/>\n<part2 active="1" beenSetOnField="1"/>\n<part3 active="1" beenSetOnField="1"/>\n<part4 active="1" beenSetOnField="1"/>\n</ExpeditionDecoration10>', 'ExpeditionDecoration11': '<ExpeditionDecoration11 guid=""><base active="1" beenSetOnField="1"/>\n<part1 active="1" beenSetOnField="1"/>\n<part2 active="1" beenSetOnField="1"/>\n<part3 active="1" beenSetOnField="1"/>\n<part4 active="1" beenSetOnField="1"/>\n</ExpeditionDecoration11>', 'ExpeditionDecoration12': '<ExpeditionDecoration12 guid=""><base active="1" beenSetOnField="1"/>\n<part1 active="1" beenSetOnField="1"/>\n<part2 active="1" beenSetOnField="1"/>\n<part3 active="1" beenSetOnField="1"/>\n<part4 active="1" beenSetOnField="1"/>\n</ExpeditionDecoration12>', 'ExpeditionDecoration13': '<ExpeditionDecoration13 guid=""><base active="1" beenSetOnField="1"/>\n<part1 active="1" beenSetOnField="1"/>\n<part2 active="1" beenSetOnField="1"/>\n<part3 active="1" beenSetOnField="1"/>\n<part4 active="1" beenSetOnField="1"/>\n</ExpeditionDecoration13>', 'ExpeditionDecoration14': '<ExpeditionDecoration14 guid=""><base active="1" beenSetOnField="1"/>\n<part1 active="1" beenSetOnField="1"/>\n<part2 active="1" beenSetOnField="1"/>\n<part3 active="1" beenSetOnField="1"/>\n<part4 active="1" beenSetOnField="1"/>\n</ExpeditionDecoration14>', 'ExpeditionDecoration15': '<ExpeditionDecoration15 guid=""><base active="1" beenSetOnField="1"/>\n<part1 active="1" beenSetOnField="1"/>\n<part2 active="1" beenSetOnField="1"/>\n<part3 active="1" beenSetOnField="1"/>\n<part4 active="1" beenSetOnField="1"/>\n</ExpeditionDecoration15>', 'ExpeditionDecoration16': '<ExpeditionDecoration16 guid=""><base active="1" beenSetOnField="1"/>\n<part1 active="1" beenSetOnField="1"/>\n<part2 active="1" beenSetOnField="1"/>\n<part3 active="1" beenSetOnField="1"/>\n<part4 active="1" beenSetOnField="1"/>\n</ExpeditionDecoration16>', 'ExpeditionDecoration17': '<ExpeditionDecoration17 guid=""><base active="1" beenSetOnField="1"/>\n<part1 active="1" beenSetOnField="1"/>\n<part2 active="1" beenSetOnField="1"/>\n<part3 active="1" beenSetOnField="1"/>\n<part4 active="1" beenSetOnField="1"/>\n</ExpeditionDecoration17>', 'ExpeditionDecoration18': '<ExpeditionDecoration18 guid=""><base active="1" beenSetOnField="1"/>\n<part1 active="1" beenSetOnField="1"/>\n<part2 active="1" beenSetOnField="1"/>\n<part3 active="1" beenSetOnField="1"/>\n<part4 active="1" beenSetOnField="1"/>\n</ExpeditionDecoration18>', 'ExpeditionDecoration19': '<ExpeditionDecoration19 guid=""><base active="1" beenSetOnField="1"/>\n<part1 active="1" beenSetOnField="1"/>\n<part2 active="1" beenSetOnField="1"/>\n<part3 active="1" beenSetOnField="1"/>\n<part4 active="1" beenSetOnField="1"/>\n</ExpeditionDecoration19>', 'ExpeditionDecoration20': '<ExpeditionDecoration20 guid=""><base active="1" beenSetOnField="1"/>\n<part1 active="1" beenSetOnField="1"/>\n<part2 active="1" beenSetOnField="1"/>\n<part3 active="1" beenSetOnField="1"/>\n<part4 active="1" beenSetOnField="1"/>\n</ExpeditionDecoration20>', 'ExpeditionDecoration21': '<ExpeditionDecoration21 guid=""><base active="1" beenSetOnField="1"/>\n<part1 active="1" beenSetOnField="1"/>\n<part2 active="1" beenSetOnField="1"/>\n<part3 active="1" beenSetOnField="1"/>\n<part4 active="1" beenSetOnField="1"/>\n</ExpeditionDecoration21>', 'Merge2Decoration1': '<Merge2Decoration1 guid=""><base active="1" beenSetOnField="1"/>\n<part1 active="1" beenSetOnField="1"/>\n<part2 active="1" beenSetOnField="1"/>\n<part3 active="1" beenSetOnField="1"/>\n</Merge2Decoration1>', 'Merge2Decoration2': '<Merge2Decoration2 guid=""><base active="1" beenSetOnField="1"/>\n<part1 active="1" beenSetOnField="1"/>\n<part2 active="1" beenSetOnField="1"/>\n<part3 active="1" beenSetOnField="1"/>\n</Merge2Decoration2>', 'Merge2Decoration3': '<Merge2Decoration3 guid=""><base active="1" beenSetOnField="1"/>\n<part1 active="1" beenSetOnField="1"/>\n<part2 active="1" beenSetOnField="1"/>\n<part3 active="1" beenSetOnField="1"/>\n</Merge2Decoration3>', 'Merge2Decoration4': '<Merge2Decoration4 guid=""><base active="1" beenSetOnField="1"/>\n<part1 active="1" beenSetOnField="1"/>\n<part2 active="1" beenSetOnField="1"/>\n<part3 active="1" beenSetOnField="1"/>\n</Merge2Decoration4>', 'Merge2Decoration5': '<Merge2Decoration5 guid=""><base active="1" beenSetOnField="1"/>\n<part1 active="1" beenSetOnField="1"/>\n<part2 active="1" beenSetOnField="1"/>\n<part3 active="1" beenSetOnField="1"/>\n</Merge2Decoration5>', 'Merge2Decoration6': '<Merge2Decoration6 guid=""><base active="1" beenSetOnField="1"/>\n<part1 active="1" beenSetOnField="1"/>\n<part2 active="1" beenSetOnField="1"/>\n<part3 active="1" beenSetOnField="1"/>\n</Merge2Decoration6>', 'Merge2Decoration7': '<Merge2Decoration7 guid=""><base active="1" beenSetOnField="1"/>\n<part1 active="1" beenSetOnField="1"/>\n<part2 active="1" beenSetOnField="1"/>\n<part3 active="1" beenSetOnField="1"/>\n</Merge2Decoration7>', 'Merge2Decoration8': '<Merge2Decoration8 guid=""><base active="1" beenSetOnField="0"/>\n<part1 active="1" beenSetOnField="1"/>\n<part2 active="1" beenSetOnField="1"/>\n</Merge2Decoration8>', 'Merge2Decoration9': '<Merge2Decoration9 guid=""><base active="1" beenSetOnField="1"/>\n<part1 active="1" beenSetOnField="1"/>\n</Merge2Decoration9>', 'Merge2Decoration10': '<Merge2Decoration10 guid=""><base active="1" beenSetOnField="1"/>\n<part1 active="1" beenSetOnField="1"/>\n<part2 active="1" beenSetOnField="1"/>\n</Merge2Decoration10>', 'Merge2Decoration11': '<Merge2Decoration11 guid=""><base active="1" beenSetOnField="1"/>\n<part1 active="1" beenSetOnField="1"/>\n<part2 active="1" beenSetOnField="1"/>\n</Merge2Decoration11>', 'Merge2Decoration12': '<Merge2Decoration12 guid=""><base active="1" beenSetOnField="1"/>\n<part1 active="1" beenSetOnField="1"/>\n<part2 active="1" beenSetOnField="1"/>\n</Merge2Decoration12>'}


def _decor_block(xml: bytes, tag: str) -> re.Match[bytes] | None:
    matches = list(re.finditer(rb"<" + tag.encode() + rb"\b[^>]*?/>|<" + tag.encode() + rb"\b[^>]*>.*?</" + tag.encode() + rb"\s*>", xml, re.S))
    if len(matches) > 1:
        raise SaveToolError(f"Có nhiều khối {tag}; không áp dụng thay đổi")
    return matches[0] if matches else None


def _decor_replace_block(xml: bytes, tag: str, block: bytes) -> bytes:
    match = _decor_block(xml, tag)
    if match:
        return xml[:match.start()] + block + xml[match.end():]
    endings = list(re.finditer(rb"</root\s*>", xml))
    if len(endings) != 1:
        raise SaveToolError("Không xác định được root để thêm Decoration")
    pos = endings[0].start()
    return xml[:pos] + b"\n" + block + b"\n" + xml[pos:]


def decoration_inventory(xml: bytes) -> dict[str, int]:
    root = validate_xml_document(xml, "Decoration")
    stashes = root.findall("BuildingsStash")
    if len(stashes) > 1:
        raise SaveToolError("Có nhiều BuildingsStash")
    result = {}
    if stashes:
        for node in stashes[0].findall("Building"):
            decoration_id = node.get("id", "")
            if decoration_id in result:
                raise SaveToolError(f"Decoration {decoration_id} bị trùng trong kho")
            result[decoration_id] = parse_int(node.get("count", ""), decoration_id, 0, 2_147_483_647)
    return result


def set_decorations(xml: bytes, ids: Iterable[str], count: int) -> tuple[bytes, dict]:
    if type(count) is not int or not 1 <= count <= 20:
        raise SaveToolError("Số lượng Decoration phải từ 1 đến 20 (theo TSVIP)")
    known = set().union(*DECORATION_GROUPS.values())
    selected = set(ids)
    if not selected or not selected <= known:
        raise SaveToolError("Danh sách Decoration trống hoặc có ID ngoài danh sách TSVIP")
    inventory = decoration_inventory(xml)
    match = _decor_block(xml, "BuildingsStash")
    stash = match.group(0) if match else b"<BuildingsStash></BuildingsStash>"
    if stash.rstrip().endswith(b"/>"):
        stash = re.sub(rb"/\s*>$", b"></BuildingsStash>", stash)
    new_items = []
    for decoration_id in sorted(selected):
        quantity = 1 if decoration_id in DECORATION_GROUPS["sign"] else count
        matches = [m for m in re.finditer(rb"<Building\b[^>]*>", stash)
                   if html.unescape(parse_attributes(m.group(0)).get("id", "")) == decoration_id]
        if len(matches) > 1:
            raise SaveToolError(f"Decoration {decoration_id} bị trùng")
        if matches:
            item = matches[0]
            tag = replace_attribute(item.group(0), "count", str(quantity))
            stash = stash[:item.start()] + tag + stash[item.end():]
        else:
            new_items.append(f'<Building id="{xml_escape_attribute(decoration_id)}" count="{quantity}"/>'.encode())
    if new_items:
        pos = stash.rfind(b"</BuildingsStash")
        stash = stash[:pos] + b"\n" + b"\n".join(new_items) + b"\n" + stash[pos:]
    updated = _decor_replace_block(xml, "BuildingsStash", stash)
    fragment_ids = selected & DECORATION_FRAGMENTS.keys()
    if fragment_ids:
        match = _decor_block(updated, "FragmentedBeautyManager")
        manager = match.group(0) if match else b"<FragmentedBeautyManager><Buildings></Buildings></FragmentedBeautyManager>"
        if manager.rstrip().endswith(b"/>"):
            manager = re.sub(rb"/\s*>$", b"><Buildings></Buildings></FragmentedBeautyManager>", manager)
        buildings_match = _decor_block(manager, "Buildings")
        buildings = buildings_match.group(0) if buildings_match else b"<Buildings></Buildings>"
        if buildings.rstrip().endswith(b"/>"):
            buildings = re.sub(rb"/\s*>$", b"></Buildings>", buildings)
        for decoration_id in sorted(fragment_ids):
            replacement = DECORATION_FRAGMENTS[decoration_id].encode()
            item = _decor_block(buildings, decoration_id)
            if item:
                buildings = buildings[:item.start()] + replacement + buildings[item.end():]
            else:
                pos = buildings.rfind(b"</Buildings")
                buildings = buildings[:pos] + b"\n" + replacement + b"\n" + buildings[pos:]
        if buildings_match:
            manager = manager[:buildings_match.start()] + buildings + manager[buildings_match.end():]
        else:
            pos = manager.rfind(b"</FragmentedBeautyManager")
            manager = manager[:pos] + buildings + manager[pos:]
        updated = _decor_replace_block(updated, "FragmentedBeautyManager", manager)
    verified = decoration_inventory(updated)
    for decoration_id in selected:
        quantity = 1 if decoration_id in DECORATION_GROUPS["sign"] else count
        if verified.get(decoration_id) != quantity:
            raise SaveToolError(f"Xác minh Decoration {decoration_id} thất bại")
    return updated, {"selected": len(selected), "added": len(selected - inventory.keys()),
                     "fragments": len(fragment_ids), "count": count,
                     "no_fragment_template": sorted((selected & set(DECORATION_GROUPS["special"])) - DECORATION_FRAGMENTS.keys())}


def decoration_prompt() -> None:
    SESSION.require_loaded()
    group_labels = {"normal": "Đồ trang trí thường", "special": "Merge / Expedition", "sign": "Biển tên thành phố"}
    while True:
        assert SESSION.current_xml is not None
        print("\n--- 16. DECORATION ---")
        print("1. Xem danh sách và số lượng trong kho")
        print("2. Thêm/cập nhật các món chọn")
        print("3. Thêm/cập nhật tất cả trong một nhóm")
        print("4. Thêm/cập nhật toàn bộ ba nhóm")
        print("0. Quay lại menu chính")
        choice = input("Chọn: ").strip()
        if choice == "0":
            return
        try:
            if choice not in ("1", "2", "3", "4"):
                print("Lựa chọn không hợp lệ.")
                continue
            if choice != "4":
                print("1. Đồ trang trí thường | 2. Merge / Expedition | 3. Biển tên thành phố")
                group = {"1": "normal", "2": "special", "3": "sign"}.get(input("Chọn nhóm: ").strip())
                if group is None:
                    raise SaveToolError("Nhóm không hợp lệ")
                ids = DECORATION_GROUPS[group]
            else:
                group = "all"
                ids = tuple(dict.fromkeys(item for values in DECORATION_GROUPS.values() for item in values))
            if choice in ("1", "2"):
                inventory = decoration_inventory(SESSION.current_xml)
                for index, decoration_id in enumerate(ids, 1):
                    print(f"{index:4}. {decoration_id:<50} kho: {inventory.get(decoration_id, 0)}")
                if choice == "1":
                    input("Nhấn Enter để quay lại...")
                    continue
                raw = input("Chọn STT (vd 1,3,5-10; Enter để hủy): ").strip()
                if not raw:
                    continue
                indices = parse_avatar_selection(raw, (str(n) for n in range(1, len(ids) + 1)))
                ids = tuple(ids[int(index) - 1] for index in indices)
            count = 1 if group == "sign" else parse_int(input("Số lượng mỗi món (1..20) [1]: ").strip() or "1", "Số lượng", 1, 20)
            updated, report = set_decorations(SESSION.current_xml, ids, count)
            print(f"Áp dụng {report['selected']} món; thêm mới {report['added']}; hoàn thành {report['fragments']} Merge/Expedition.")
            print("Đặt số lượng trong kho bằng giá trị nhập; biển tên luôn là 1.")
            if report["fragments"]:
                print("Các món Merge/Expedition được chọn sẽ nhận trạng thái hoàn thành theo mẫu TSVIP.")
            if report["no_fragment_template"]:
                print("APK chưa có mẫu hoàn thành cho các món sau; chỉ thêm vào kho:", ", ".join(report["no_fragment_template"]))
            if updated == SESSION.current_xml:
                print("Không có thay đổi.")
                continue
            if not ask_yes_no("Xác nhận cập nhật Decoration?"):
                print("Đã hủy.")
                continue
            SESSION.apply_xml(updated)
            print("Đã cập nhật XML làm việc. Về menu chính, chọn 43 ghi vào game hoặc 42 xuất local.")
        except SaveToolError as exc:
            print(f"Lỗi: {exc}")
        except KeyboardInterrupt:
            print("\nĐã hủy thao tác.")


# TSVIP fm case 15 -> ws3 case 6: TownGround d="..." n->y; remove expandBuy objects.
def unlock_land(xml: bytes) -> tuple[bytes, dict]:
    validate_xml_document(xml, "Land")
    span = find_unique_direct_child(xml, "TownGround", "root")
    ground = xml[span.start:span.end]
    changed_cells = 0
    changed_rows = 0
    def patch_row(match: re.Match[bytes]) -> bytes:
        nonlocal changed_cells, changed_rows
        row = match.group(1)
        changed_cells += row.count(b"n")
        if b"n" in row:
            changed_rows += 1
        return b'd="' + row.replace(b"n", b"y") + b'"'
    ground = re.sub(rb'd="([^"]+)"', patch_row, ground)
    updated = xml[:span.start] + ground + xml[span.end:]
    # Apply the TSVIP removal within Buildings blocks only, preserving other content.
    blocks = list(re.finditer(rb"<Buildings\b[^>]*>.*?</Buildings\s*>", updated, re.S))
    removed = 0
    for block in reversed(blocks):
        body = block.group(0)
        def remove_expansion(match: re.Match[bytes]) -> bytes:
            nonlocal removed
            if b"expandBuy" in match.group(0):
                removed += 1
                return b""
            return match.group(0)
        body = re.sub(rb"<Object\b[^>]*/>\s*\n?", remove_expansion, body)
        updated = updated[:block.start()] + body + updated[block.end():]
    validate_xml_document(updated, "Land sau mở")
    return updated, {"cells": changed_cells, "rows": changed_rows, "removed_expand_buy": removed}


def land_prompt() -> None:
    SESSION.require_loaded()
    assert SESSION.current_xml is not None
    updated, report = unlock_land(SESSION.current_xml)
    print(f"Land: mở {report['cells']} ô trong {report['rows']} hàng; bỏ {report['removed_expand_buy']} Object expandBuy.")
    if updated == SESSION.current_xml:
        print("Không có đất khóa/expandBuy cần sửa theo thuật toán TSVIP.")
        return
    if not ask_yes_no("Xác nhận mở đất theo TSVIP?"):
        print("Đã hủy.")
        return
    SESSION.apply_xml(updated)
    print("Đã cập nhật XML làm việc. Chọn 51 ghi vào game hoặc 50 xuất local.")


# TSVIP px3.n + hx3 case 1: collection counters, ArtInfo and museum tutorial flags.
TSVIP_MUSEUM_ARTIFACTS = ('a1', 'a2', 'a3', 'a4', 'a5', 'a6', 'a7', 'a8', 'a9', 'a10', 'a11', 'a12', 'a13', 'a14', 'a15', 'a16', 'a17', 'a18', 'a19', 'a20', 'a21', 'a22', 'a23', 'a24', 'a25', 'a26', 'a27', 'a28', 'a29', 'a30', 'a31', 'a32', 'a33', 'a34', 'a35', 'a36', 'a37', 'a38', 'a39', 'a40', 'a41', 'a42', 'a43', 'a44', 'a45', 'a46', 'a47', 'a48', 'a49', 'a50', 'a51', 'a52', 'a53', 'a54', 'a55', 'a56', 'a57', 'a58', 'a59', 'a60', 'a61', 'a62', 'a63', 'a64', 'a65', 'a66', 'a67', 'a68', 'a69', 'a70', 'a71', 'a72', 'a73', 'a74', 'a75', 'a76', 'a77', 'a78', 'a79', 'a80', 'a81', 'a82', 'a83', 'a84', 'a85', 'a86', 'a87', 'a88', 'a89', 'a90', 'a91', 'a92', 'a93', 'a94', 'a95', 'a96', 'a97', 'a98', 'a99', 'a100', 'a101', 'a102', 'a103', 'a104', 'a105', 'a106', 'a107', 'a108', 'a109', 'a110', 'a111', 'a112', 'a113', 'a114', 'a115', 'a116', 'a117', 'a118', 'a119', 'a120', 'a121', 'a122', 'a123', 'a124', 'a125', 'a126', 'a127', 'a128', 'a129', 'a130', 'a131', 'a132', 'a133', 'a134', 'a135', 'a136', 'a137', 'a138', 'a139', 'a140', 'a141', 'a142', 'a143', 'a144', 'a145', 'a146', 'a147', 'a148', 'a149', 'a150', 'a231', 'a232', 'a233', 'a234', 'a235', 'a236', 'a237', 'a238', 'a239', 'a240', 'a311', 'a312', 'a313', 'a314', 'a315', 'a316', 'a317', 'a318', 'a319', 'a320', 'a321', 'a322', 'a323', 'a324', 'a325', 'a326', 'a327', 'a328', 'a329', 'a330', 'a331', 'a332', 'a333', 'a334', 'a335', 'a336', 'a337', 'a338', 'a339', 'a440', 'a341', 'a342', 'a343', 'a344', 'a345', 'a347', 'a349', 'a352', 'a353', 'a355', 'a357', 'a360', 'a362', 'a363', 'a365')
TSVIP_MUSEUM_ORIGINS = {'a151': 'i4discoveredName', 'a152': 'islands:oceanChest', 'a153': 'islands:oceanChest', 'a154': 'islands:oceanChest', 'a155': 'islands:oceanChest', 'a156': 'islands:oceanChest', 'a157': 'islands:oceanChest', 'a158': 'islands:oceanChest', 'a159': 'i4discoveredName', 'a160': 'i2discoveredName', 'a161': 'i3discoveredName', 'a162': 'islands:oceanChest', 'a163': 'islands:oceanChest', 'a164': 'islands:oceanChest', 'a165': 'islands:oceanChest', 'a166': 'i3discoveredName'}
TSVIP_MUSEUM_FLAGS = ("museumThanksShowed", "museumUpdateShowed", "RequestedDiggingMuseumResources",
                      "DiggingRegeneratedForMuseum", "diggingFullCompleted")


def unlock_museum(xml: bytes, timestamp: float | None = None) -> tuple[bytes, dict]:
    root = validate_xml_document(xml, "Museum")
    collection_ids = set(range(1, 70))
    for node in root.iter("Var"):
        match = re.fullmatch(r"RewartCol_(\d+)", node.get("name", ""))
        if match:
            collection_ids.add(int(match[1]))
    updated = xml
    for collection_id in sorted(collection_ids):
        updated = _m3_upsert_field(updated, f"RewartCol_{collection_id}", "3", "i", "Global")
    artifacts = set(TSVIP_MUSEUM_ARTIFACTS) | TSVIP_MUSEUM_ORIGINS.keys()
    matches = list(root.iter("ArtInfo"))
    if len(matches) > 1:
        raise SaveToolError("Có nhiều ArtInfo; không áp dụng thay đổi")
    if matches:
        for node in matches[0].iter():
            for raw in node.attrib.values():
                for match in re.finditer(r'"id"\s*:\s*"(a\d+)"', raw):
                    artifacts.add(match[1])
    date = float(time.time() if timestamp is None else timestamp)
    if not 0 <= date < float("inf"):
        raise SaveToolError("Timestamp Museum không hợp lệ")
    entries = []
    for artifact_id in sorted(artifacts, key=lambda name: int(name[1:])):
        data = {"id": artifact_id, "count": 3, "met": 0 if artifact_id in TSVIP_MUSEUM_ORIGINS else 1}
        if artifact_id in TSVIP_MUSEUM_ORIGINS:
            data["from"] = TSVIP_MUSEUM_ORIGINS[artifact_id]
        # Build date with exactly one decimal place as TSVIP's Locale.US format.
        text = json.dumps(data, ensure_ascii=False, separators=(",", ":"))[:-1] + f',"date":{date:.1f},"ind":1}}'
        entries.append(f'    <aInfo i="{xml_escape_attribute(text)}"/>'.encode())
    artinfo = b"<ArtInfo>\r\n" + b"\r\n".join(entries) + b"\r\n</ArtInfo>"
    updated = _decor_replace_block(updated, "ArtInfo", artinfo)
    for name in TSVIP_MUSEUM_FLAGS:
        updated = _m3_upsert_field(updated, name, "1", "b", "Global")
    verified = validate_xml_document(updated, "Museum sau hoàn thành")
    info = verified.find("ArtInfo")
    if info is None or len(info.findall("aInfo")) != len(artifacts):
        raise SaveToolError("Xác minh ArtInfo thất bại")
    for collection_id in collection_ids:
        if read_var(updated, f"RewartCol_{collection_id}").get("v") != "3":
            raise SaveToolError("Xác minh bộ sưu tập Museum thất bại")
    return updated, {"collections": len(collection_ids), "artifacts": len(artifacts)}


def museum_prompt() -> None:
    SESSION.require_loaded()
    assert SESSION.current_xml is not None
    updated, report = unlock_museum(SESSION.current_xml)
    print(f"Museum: hoàn thành {report['collections']} bộ sưu tập; đặt {report['artifacts']} hiện vật với count=3.")
    print("Theo TSVIP: dựng lại ArtInfo, cập nhật ngày và các cờ hướng dẫn bảo tàng.")
    if not ask_yes_no("Xác nhận hoàn thành Museum?"):
        print("Đã hủy.")
        return
    SESSION.apply_xml(updated)
    print("Đã cập nhật XML làm việc. Chọn 51 ghi vào game hoặc 50 xuất local.")


# TSVIP fm cases 16/17, qx3.d, ws3 cases 8/9/11: owned card quantity 461.
TSVIP_CARD_QUANTITY = 461


def _dataelem_spans(xml: bytes) -> list[tuple[int, int, dict[str, str]]]:
    stack = []
    spans = []
    for match in re.finditer(rb"<DataElem\b[^>]*>|</DataElem\s*>", xml):
        tag = match.group(0)
        if tag.startswith(b"</"):
            if not stack:
                raise SaveToolError("DataElem đóng không khớp")
            start, attrs = stack.pop()
            spans.append((start, match.end(), attrs))
        elif tag.rstrip().endswith(b"/>"):
            spans.append((match.start(), match.end(), parse_attributes(tag)))
        else:
            stack.append((match.start(), parse_attributes(tag)))
    if stack:
        raise SaveToolError("DataElem chưa đóng")
    return spans


def update_owned_cards(xml: bytes, all_cards: bool) -> tuple[bytes, dict]:
    validate_xml_document(xml, "Owned Cards")
    modern = [(a, b, attrs) for a, b, attrs in _dataelem_spans(xml) if attrs.get("name") == "OwnedCards"]
    if len(modern) > 1:
        raise SaveToolError("Có nhiều OwnedCards hiện đại; chưa áp dụng thay đổi")
    if modern:
        start, end, attrs = modern[0]
        block = xml[start:end]
        if block.rstrip().endswith(b"/>"):
            block = re.sub(rb"/\s*>$", b"></DataElem>", block)
        def patch_counter(match: re.Match[bytes]) -> bytes:
            attrs = parse_attributes(match.group(0))
            if attrs.get("name") in ("generatedCount", "inStockCount", "maxInStockCount"):
                return replace_attribute(match.group(0), "value", str(TSVIP_CARD_QUANTITY))
            return match.group(0)
        block = re.sub(rb"<DataElem\b[^>]*>", patch_counter, block)
        removed = 0
        if all_cards:
            # TSVIP excludes card_149 in the modern array branch.
            items = []
            for a, b, attrs in _dataelem_spans(block):
                if attrs.get("type") != "dataStore":
                    continue
                element = ET.fromstring(block[a:b])
                card_ids = [child.get("value") for child in element
                            if child.tag == "DataElem" and child.get("name") == "cardId"]
                if "card_149" in card_ids:
                    items.append((a, b))
            for a, b in sorted(items, reverse=True):
                block = block[:a] + block[b:]
                removed += 1
        root = ET.fromstring(block)
        existing = [node.get("value", "") for node in root.iter("DataElem") if node.get("name") == "cardId"]
        if len(existing) != len(set(existing)):
            raise SaveToolError("cardId bị trùng trong OwnedCards")
        missing = []
        if all_cards:
            desired = [f"card_{n:02d}" for n in range(1, 161) if n != 149]
            missing = [card_id for card_id in desired if card_id not in existing]
            additions = []
            for card_id in missing:
                additions.append((f'<DataElem type="dataStore"><DataElem name="cardId" type="string" value="{card_id}"/>'
                                  '<DataElem name="generatedCount" type="int" value="461"/>'
                                  '<DataElem name="inStockCount" type="int" value="461"/>'
                                  '<DataElem name="isNew" type="bool" value="false"/>'
                                  '<DataElem name="maxInStockCount" type="int" value="461"/></DataElem>').encode())
            pos = block.rfind(b"</DataElem")
            block = block[:pos] + b"\n".join(additions) + block[pos:]
        updated = xml[:start] + block + xml[end:]
        count = len(existing) + len(missing)
        report = {"format": "DataElem array", "cards": count, "added": len(missing), "removed": removed}
    else:
        match = _decor_block(xml, "OwnedCards")
        if match:
            block = match.group(0)
            count = 0
            def patch_card(match: re.Match[bytes]) -> bytes:
                nonlocal count
                count += 1
                return replace_attribute(match.group(0), "count", str(TSVIP_CARD_QUANTITY))
            block = re.sub(rb"<Card\b[^>]*>", patch_card, block)
            updated = xml[:match.start()] + block + xml[match.end():]
            report = {"format": "OwnedCards legacy", "cards": count, "added": 0, "removed": 0}
            # TSVIP legacy fallback updates existing cards only, even in All Card.
            if not count and all_cards:
                raise SaveToolError("OwnedCards legacy rỗng; TSVIP chưa có nhánh bổ sung phù hợp")
        elif all_cards:
            # Exact TSVIP no-container fallback: unpadded IDs 1..160, exclude 159.
            cards = [f'<Card id="card_{n}" count="461"/>'.encode() for n in range(1, 161) if n != 159]
            block = b"<OwnedCards>" + b"\n".join(cards) + b"</OwnedCards>"
            endings = list(re.finditer(rb"</Global\s*>", xml))
            if len(endings) != 1:
                raise SaveToolError("Không xác định được Global để tạo OwnedCards legacy")
            pos = endings[0].start()
            updated = xml[:pos] + block + b"\n" + xml[pos:]
            report = {"format": "OwnedCards legacy mới", "cards": len(cards), "added": len(cards), "removed": 0}
        else:
            raise SaveToolError("Không có OwnedCards; My Card chỉ xử lý thẻ hiện có")
    validate_xml_document(updated, "Owned Cards sau cập nhật")
    return updated, report


def cards_prompt(all_cards: bool) -> None:
    SESSION.require_loaded()
    assert SESSION.current_xml is not None
    updated, report = update_owned_cards(SESSION.current_xml, all_cards)
    label = "All Card" if all_cards else "My Card"
    print(f"{label}: {report['format']} | {report['cards']} thẻ | thêm {report['added']} | bỏ {report['removed']}")
    print("Số lượng thẻ = 461 theo TSVIP. Không thay bộ đếm FullCardCollections.")
    if all_cards and report["format"] == "OwnedCards legacy":
        print("Save dùng OwnedCards legacy: theo TSVIP, chỉ tăng các thẻ đang có.")
    if updated == SESSION.current_xml:
        print("Không có thay đổi.")
        return
    if not ask_yes_no(f"Xác nhận áp dụng {label}?"):
        print("Đã hủy.")
        return
    SESSION.apply_xml(updated)
    print("Đã cập nhật XML làm việc. Chọn 51 ghi vào game hoặc 50 xuất local.")


# TSVIP fm case 14: patch the existing SeasonTicket only.
def unlock_golden_pass(xml: bytes) -> tuple[bytes, dict]:
    validate_xml_document(xml, "Golden Pass")
    matches = list(re.finditer(rb"<SeasonTicket\b[^>]*>", xml))
    if len(matches) != 1:
        raise SaveToolError(f"Cần đúng một SeasonTicket; tìm thấy {len(matches)}. Không tạo mùa vé mới.")
    match = matches[0]
    old = parse_attributes(match.group(0))
    tag = replace_attribute(match.group(0), "premium", "1")
    tag = replace_attribute(tag, "score", "1002")
    updated = xml[:match.start()] + tag + xml[match.end():]
    validate_xml_document(updated, "Golden Pass sau cập nhật")
    attrs = parse_attributes(tag)
    if attrs.get("premium") != "1" or attrs.get("score") != "1002":
        raise SaveToolError("Xác minh Golden Pass thất bại")
    return updated, {"premium": (old.get("premium"), "1"), "score": (old.get("score"), "1002")}


def golden_pass_prompt() -> None:
    SESSION.require_loaded()
    assert SESSION.current_xml is not None
    updated, report = unlock_golden_pass(SESSION.current_xml)
    for name, (old, new) in report.items():
        print(f"SeasonTicket {name}: {old if old is not None else '(chưa có)'} -> {new}")
    if updated == SESSION.current_xml:
        print("Golden Pass đã ở trạng thái này.")
        return
    if not ask_yes_no("Xác nhận mở Golden Pass theo TSVIP?"):
        print("Đã hủy.")
        return
    SESSION.apply_xml(updated)
    print("Đã cập nhật XML làm việc. Chọn 51 ghi vào game hoặc 50 xuất local.")


# TSVIP if2.c skin catalog, if2.d/e/f stickers, fi2 Profile and qx3.b achievements.
TSVIP_SKINS = {'Airplane': ('Skin_Airplane_movie', 'Skin_Airplane_christmas2022', 'Skin_Airplane_easter2023', 'Skin_Airplane_sweet', 'Skin_Airplane_winterSport', 'Skin_Airplane_ireland', 'Skin_Airplane_spy', 'Skin_Airplane_allinclusive', 'Skin_Airplane_fashion', 'Skin_Airplane_arab', 'Skin_Airplane_SP3', 'Skin_Airplane_SP3:2', 'Skin_Airplane_SP7', 'Skin_Airplane_SP7:2', 'Skin_Airplane_SP9', 'Skin_Airplane_halloween2021', 'Skin_Airplane_halloween2021:2', 'Skin_Airplane_space', 'Skin_Airplane_rock', 'Skin_Airplane_classicmusic', 'Skin_Airplane_Halloween2025', 'Skin_Airplane_carnival_70', 'Skin_Airplane_culinary_74'), 'Airport': ('Skin_Airport_christmas2022', 'Skin_Airport_sweet', 'Skin_Airport_winterSport', 'Skin_Airport_ireland', 'Skin_Airport_spy', 'Skin_Airport_allinclusive', 'Skin_Airport_arab', 'Skin_Airport_SP3', 'Skin_Airport_SP7', 'Skin_Airport_SP9', 'Skin_Airport_space', 'Skin_Airport_rock', 'Skin_Airport_halloween2021', 'Skin_Airport_easter2023', 'Skin_Airport_classicmusic', 'Skin_Airport_fashion', 'Skin_Airport_movie', 'Skin_Airport_Halloween2025', 'Skin_Airport_carnival_70', 'Skin_Airport_culinary_74'), 'Chicken': ('Skin_Chicken_travel', 'Skin_Chicken_theatrical', 'Skin_Chicken_sport', 'Skin_Chicken_cinderella', 'Skin_Chicken_jungle', 'Skin_Chicken_sweet', 'Skin_Chicken_christmas2023', 'Skin_Chicken_ireland', 'Skin_Chicken_hellas', 'Skin_Chicken_allinclusive', 'Skin_Chicken_birthday2024', 'Skin_Chicken_birthday2024c', 'Skin_Chicken_halloween2024', 'Skin_Chicken_fashion', 'Skin_Chicken_disco', 'Skin_Chicken_mars2025', 'Skin_Chicken_cny2025', 'Skin_Chicken_Birthday_2025', 'Skin_Chicken_Birthday_2025s', 'Skin_Chicken_Knight', 'Skin_Chicken_christmas_67', 'Skin_Chicken_broadway_69', 'Skin_Chicken_easter_72', 'Skin_Chicken_culinary_74'), 'Cow': ('Skin_Cow_movie', 'Skin_Cow_christmas2022', 'Skin_Cow_valentine', 'Skin_Cow_mars', 'Skin_Cow_sweet2', 'Skin_Cow_sweet', 'Skin_Cow_birthday', 'Skin_Cow_halloween2023', 'Skin_Cow_winterSport', 'Skin_Cow_CNY', 'Skin_Cow_easter2024', 'Skin_Cow_spy', 'Skin_Cow_atlantis', 'Skin_Cow_italy2024', 'Skin_Cow_birthday2024', 'Skin_Cow_pirate2024', 'Skin_Cow_festival', 'Skin_Cow_arab', 'Skin_Cow_arctic', 'Skin_Cow_japan', 'Skin_Cow_pirate20', 'Skin_Cow_classicmusic', 'Skin_Cow_Birthday_2025', 'Skin_Cow_france_68', 'Skin_Cow_carnival_70', 'Skin_Cow_celebrity_73'), 'Fortress': ('Skin_Fortress_aztecs', 'Skin_Fortress_Pirate1', 'Skin_Fortress_Pirate2', 'Skin_Fortress_Pirate3', 'Skin_Fortress_Gatsby1', 'Skin_Fortress_Gatsby2', 'Skin_Fortress_Gatsby3', 'Skin_Fortress_Halloween2021_1', 'Skin_Fortress_Halloween2021_2', 'Skin_Fortress_Halloween2021_3', 'Skin_Fortress_Christmas', 'Skin_Fortress_paris', 'Skin_Fortress_easter', 'Skin_Fortress_prehistoric', 'Skin_Fortress_christmas_3200'), 'Harbor': ('Skin_Harbor_ST1', 'Skin_Harbor_SP9', 'Skin_Harbor_paris', 'Skin_Harbor_venice', 'Skin_Harbor_halloween2022', 'Skin_Harbor_valentinesDay', 'Skin_Harbor_nordicGod', 'Skin_Harbor_jungle', 'Skin_Harbor_christmas2023', 'Skin_Harbor_CNY', 'Skin_Harbor_hellas', 'Skin_Harbor_wildwest2024', 'Skin_Harbor_birthday2024', 'Skin_Harbor_egypt', 'Skin_Harbor_allinclusive2025', 'Skin_Harbor_arctic', 'Skin_Harbor_japan', 'Skin_Harbor_Knight', 'Skin_Harbor_ST8', 'Skin_Harbor_ST35', 'Skin_Harbor_ST43', 'Skin_Harbor_ST51', 'Skin_Harbor_broadway_69', 'Skin_Harbor_easter_72'), 'Helicopter': ('Skin_Helicopter_Resort', 'Skin_Helicopter_Travel', 'Skin_Helicopter_Sport', 'Skin_Helicopter_cinderella', 'Skin_Helicopter_detective', 'Skin_Helicopter_halloween2023', 'Skin_Helicopter_brazil', 'Skin_Helicopter_easter2024', 'Skin_Helicopter_atlantis', 'Skin_Helicopter_pirate2024', 'Skin_Helicopter_disco', 'Skin_Helicopter_mars2025', 'Skin_Helicopter_Ufo', 'Skin_Helicopter_Ufo:2', 'Skin_Helicopter_Robot', 'Skin_Helicopter_Robot:2', 'Skin_Helicopter_Sleigh', 'Skin_Helicopter_Sleigh:2', 'Skin_Helicopter_Gatsby', 'Skin_Helicopter_Arabic', 'Skin_Helicopter_travel', 'Skin_Helicopter_Harvest', 'Skin_Helicopter_masquerade', 'Skin_Helicopter_cny2025', 'Skin_Helicopter_Birthday_2025', 'Skin_Helicopter_christmas_67', 'Skin_Helicopter_butterfly_71', 'Skin_Helicopter_italian_75', 'Skin_Helicopter_sport'), 'HelicopterPlace': ('Skin_HelicopterPlace_Travel', 'Skin_HelicopterPlace_Sport', 'Skin_HelicopterPlace_cinderella', 'Skin_HelicopterPlace_detective', 'Skin_HelicopterPlace_halloween2023', 'Skin_HelicopterPlace_brazil', 'Skin_HelicopterPlace_easter2024', 'Skin_HelicopterPlace_atlantis', 'Skin_HelicopterPlace_pirate2024', 'Skin_HelicopterPlace_disco', 'Skin_HelicopterPlace_mars2025', 'Skin_HelicopterPlace_masquerade', 'Skin_HelicopterPlace_cny2025', 'Skin_HelicopterPlace_Sleigh', 'Skin_HelicopterPlace_Harvest', 'Skin_HelicopterPlace_Arabic', 'Skin_HelicopterPlace_Resort', 'Skin_HelicopterPlace_Ufo', 'Skin_HelicopterPlace_Robot', 'Skin_HelicopterPlace_Gatsby', 'Skin_HelicopterPlace_christmas_67', 'Skin_HelicopterPlace_butterfly_71', 'Skin_HelicopterPlace_Birthday_2025', 'Skin_HelicopterPlace_italian_75'), 'Pig': ('Skin_Pig_CNY', 'Skin_Pig_valentinesDay'), 'Sheep': ('Skin_Sheep_halloween2022', 'Skin_Sheep_lunarNY2022', 'Skin_Sheep_easter2023', 'Skin_Sheep_nordicGod', 'Skin_Sheep_detective', 'Skin_Sheep_sweet', 'Skin_Sheep_robinHood', 'Skin_Sheep_brazil', 'Skin_Sheep_rocknroll', 'Skin_Sheep_knight', 'Skin_Sheep_wildwest2024', 'Skin_Sheep_birthday2024', 'Skin_Sheep_birthday2024s', 'Skin_Sheep_birthday2025', 'Skin_Sheep_egypt', 'Skin_Sheep_christmas2024', 'Skin_Sheep_allinclusive2025', 'Skin_Sheep_hellas2025', 'Skin_Sheep_masquerade', 'Skin_Sheep_Birthday_2025', 'Skin_Sheep_Halloween2025', 'Skin_Sheep_Gatsby', 'Skin_Sheep_butterfly_71', 'Skin_Sheep_italian_75'), 'Ship': ('Skin_Ship_ST1', 'Skin_Ship_SP9', 'Skin_Ship_paris', 'Skin_Ship_venice', 'Skin_Ship_halloween2022', 'Skin_Ship_valentinesDay', 'Skin_Ship_nordicGod', 'Skin_Ship_jungle', 'Skin_Ship_christmas2023', 'Skin_Ship_CNY', 'Skin_Ship_hellas', 'Skin_Ship_wildwest2024', 'Skin_Ship_birthday2024', 'Skin_Ship_egypt', 'Skin_Ship_allinclusive2025', 'Skin_Ship_arctic', 'Skin_Ship_japan', 'Skin_Ship_Knight', 'Skin_Ship_broadway_69', 'Skin_Ship_easter_72'), 'Train': ('Skin_Train_prehistoric', 'Skin_Train_theatrical', 'Skin_Train_lunarNY2022', 'Skin_Train_mars', 'Skin_Train_robinHood', 'Skin_Train_rocknroll', 'Skin_Train_knight', 'Skin_Train_italy2024', 'Skin_Train_halloween2024', 'Skin_Train_christmas2024', 'Skin_Train_festival', 'Skin_Train_hellas2025', 'Skin_Train_easter', 'Skin_Train_christmas', 'Skin_Train_SP5', 'Skin_Train_SP8', 'Skin_Train_western', 'Skin_Train_SP2', 'Skin_Train_SP2:2', 'Skin_Train_ST45', 'Skin_Train_ST50', 'Skin_Train_ST47', 'Skin_Train_ST24', 'Skin_Train_Gatsby', 'Skin_Train_france_68', 'Skin_Train_celebrity_73'), 'TrainStation': ('Skin_TrainStation_SP2', 'Skin_TrainStation_SP5', 'Skin_TrainStation_SP8', 'Skin_TrainStation_western', 'Skin_TrainStation_christmas', 'Skin_TrainStation_easter', 'Skin_TrainStation_prehistoric', 'Skin_TrainStation_theatrical', 'Skin_TrainStation_lunarNY2022', 'Skin_TrainStation_mars', 'Skin_TrainStation_robinHood', 'Skin_TrainStation_rocknroll', 'Skin_TrainStation_knight', 'Skin_TrainStation_italy2024', 'Skin_TrainStation_halloween2024', 'Skin_TrainStation_christmas2024', 'Skin_TrainStation_festival', 'Skin_TrainStation_hellas2025', 'Skin_TrainStation_Gatsby', 'Skin_TrainStation_france_68', 'Skin_TrainStation_celebrity_73')}
TSVIP_STICKERS = {'Standard': ('st1', 'st2', 'st3', 'st4', 'st5', 'st6', 'st7', 'st8', 'st9', 'st10', 'st11', 'st12', 'st13', 'st14', 'st15', 'st16', 'st17', 'st18', 'st19', 'st20', 'st21', 'st22', 'st23', 'st24', 'st25', 'st26', 'st27', 'st28', 'st29', 'st30', 'st31', 'st32', 'st33', 'st34', 'st35', 'st36', 'st37', 'st38', 'st39', 'st40', 'st41', 'st42', 'st43', 'st44', 'st45', 'st46', 'st47', 'st48', 'st49', 'st50', 'st51', 'st52', 'st53', 'st54', 'st55', 'st56', 'st57', 'st58', 'st59', 'st60', 'st61', 'st62', 'st63', 'st64', 'st65', 'st66', 'st67', 'st68', 'st69', 'st70', 'st71', 'st72', 'st73', 'st74', 'st75', 'st76', 'st77', 'st78', 'st79', 'st80'), 'Special': ('sp1', 'sp2', 'sp3', 'sp4', 'sp5', 'sp6', 'sp7', 'sp8', 'sp9', 'sp10', 'sp11', 'sp12', 'sp13', 'sp14', 'sp15', 'sp16', 'sp17', 'sp18', 'sp19', 'sp20', 'sp21', 'sp22', 'sp23', 'sp24', 'sp25', 'sp26', 'sp27'), 'VIP': ('v1', 'v2', 'v3'), 'Other': ('desc',)}
TSVIP_PROFILE = {'UnlockedBadges': ('UVIgUB8QfkY4NA44Bz0XVw0vCBEWXQ==', 'USVTHSoRQlMJCDkDWRI/DykOExRTNys=', 'UVIgUB8QfkM4NA44Bz0XVw0vCBEWXQ==', 'USVTHSoRQlYJCDkDWRI/DykOExRTNys=', 'UVIgUB8QfkA4NA44Bz0XVw0vCBEWXQ==', 'USVTHSoRQlUJCDkDWRI/DykOExRTNys=', 'UVIgUB8QfkE4NA44Bz0XVw0vCBEWXQ==', 'USVTHSoRQlQJCDkDWRI/DykOExRTNys=', 'VRsrKRc4Zl4UFAUpVw84CH0QVzMnERINWg==', 'GC4qFQIJX3o9QURqCTkMGRU/MSEXEA9UUlE=', 'USVTHSoRQlIJCDkDWRI/DykOExRTNys=', 'UVIgUB8Qfkc4NA44Bz0XVw0vCBEWXQ==', 'UVIgUB8QfkQ4NA44Bz0XVw0vCBEWXQ==', 'USVTHSoRQlEJCDkDWRI/DykOExRTNys=', 'USVTHSoRQlAJCDkDWRI/DykOExRTNys=', 'UVIgUB8QfkU4NA44Bz0XVw0vCBEWXQ=='), 'UnlockedExpRanks': ('ciIfESAGOAQUVgApVw84CH0QVzMnERINWg==', 'ciIfESAGOAQUVgEpVw84CH0QVzMnERINWg==', 'PxceLTU3ASA9A0FqCTkMGRU/MSEXEA9UUlE=', 'PxceLTU3ASA9A0BqCTkMGRU/MSEXEA9UUlE=', 'ciIfESAGOAQUVg8pVw84CH0QVzMnERINWg==', 'ciIfESAGOAQUVg4pVw84CH0QVzMnERINWg==', 'PxceLTU3ASA9A09qCTkMGRU/MSEXEA9UUlE=', 'PxceLTU3ASA9A05qCTkMGRU/MSEXEA9UUlE=', 'PxceLTU3ASA9AkZqCTkMGRU/MSEXEA9UUlE=', 'PxceLTU3ASA9AkdqCTkMGRU/MSEXEA9UUlE=', 'ciIfESAGOAQUVwcpVw84CH0QVzMnERINWg==', 'ciIfESAGOAQUVwYpVw84CH0QVzMnERINWg==', 'ciIfESAGOAQUVwUpVw84CH0QVzMnERINWg==', 'ciIfESAGOAQUVwQpVw84CH0QVzMnERINWg==', 'PxceLTU3ASA9AkRqCTkMGRU/MSEXEA9UUlE=', 'PxceLTU3ASA9AkVqCTkMGRU/MSEXEA9UUlE=', 'PxceLTU3ASA9AkJqCTkMGRU/MSEXEA9UUlE=', 'PxceLTU3ASA9AkNqCTkMGRU/MSEXEA9UUlE=', 'ciIfESAGOAQUVwMpVw84CH0QVzMnERINWg==', 'ciIfESAGOAQUVwIpVw84CH0QVzMnERINWg=='), 'UnlockedFrames': ('VFBKNx5FUig9Gy0tFgIwCCM=', 'VEdYLhJsA3U9Gy0tFgIwCCM=', 'VEdYLhJsA3Y9Gy0tFgIwCCM=', 'VEdYLhJsA3c9Gy0tFgIwCCM=', 'VEdYLhJsA3A9Gy0tFgIwCCM=', 'VEdYLhJsA3I9Gy0tFgIwCCM=', 'VEdYLhJsA3M9Gy0tFgIwCCM=', 'VEdYLhJsA3w9Gy0tFgIwCCM=', 'VEdYLhJsA309Gy0tFgIwCCM=', 'VEdYLhJsA3E9Gy0tFgIwCCM=', 'VEdYLhJsAnQ9Gy0tFgIwCCM=', 'VEdYLhJsAnU9Gy0tFgIwCCM='), 'UnlockedStyles': ('festival', 'easter', 'cooking', 'neon', 'bubble', 'glow', 'train')}
TSVIP_ACHIEVEMENTS = {'marketBoom': {'Achievement_MarketBoom': 16000}, 'miner': {'Achievement_Miner': 14000}, 'earthCenter': {'Achievement_EarthCenter': 17000}, 'strategyReserv': {'Achievement_StrategyReserv': 3500}, 'factoryUpgrader': {'Achievement_FactoryUpgrader': 42}, 'collector': {'Achievement_Collector': 25}, 'teamwork': {'Achievement_Teamwork': 20000}, 'casinoGame': {'Achievement_CasinoGame': 4000}, 'sendShips': {'Achievement_sendShips': 18000}, 'islandGoods': {'Achievement_islandGoods': 110000}, 'collectBacon': {'Achievement_CollectBacon': 15500}, 'collectHoney': {'Achievement_CollectHoney': 14500}, 'collectorIslands': {'Achievement_CollectorIslands': 30}, 'progressWave': {'Achievement_progressWave': 165}, 'downFeather': {'Achievement_DownFeather': 14000}, 'metropolis': {'Achievement_IncreasedPopulation': 29000, 'Achievement_IncreasedPopulation_Current': 12000}, 'community_developer': {'Achievement_CommunityDeveloper': 70, 'Achievement_CommunityDeveloper_Current': 70}, 'entrepreneur': {'Achievement_FillOrders': 7100}, 'lead_Architect': {'Achievement_BuiltHouses': 130, 'Achievement_BuiltHouses_Current': 26}, 'population_boom': {'Achievement_IncreasedPopulation': 29000, 'Achievement_IncreasedPopulation_Current': 12000}, 'construction_manager': {'Achievement_BuiltFactories': 45, 'Achievement_BuiltFactories_Current': 45}, 'endless_fields': {'Achievement_PlowedFields': 740000}, 'magnate': {'Achievement_EarneCoins': 700000000}, 'wacky_farmer': {'Achievement_GetFields': 132}, 'urbanist_club': {'Achievement_ExpandField': 390}, 'honorary_freeman': {'Achievement_EnteredGame': 235, 'Achievement_EnteredGame_Current': 15}, 'senior_train_driver': {'Achievement_SentTrain': 2300}, 'road_champ': {'Achievement_BuiltRoad': 440, 'Achievement_BuiltRoad_Current': 440}, 'production_genius': {'Achievement_ProducedProducts': 400000}, 'customer_service_pro': {'Achievement_FillOrders': 7100}, 'model_chicken_coop': {'Achievement_CollectEggs': 60000}, 'milky_way': {'Achievement_CollectMilk': 108000}, 'mushroom': {'Achievement_CollectMushroom': 14600}, 'wool_art': {'Achievement_CollectWool': 21200}, 'seaweed': {'Achievement_seaweed': 20000}, 'donate': {'Achievement_donate': 12500}, 'regataChampion': {'Achievement_regataChampion': 1}, 'match3_achievement': {'Achievement_CompleteMatch3Levels': 56000}}
PROFILE_ITEM_LABELS = {'UnlockedBadges': ('Sunflower', 'Large Sunflower', 'House', 'Large House', 'Bell', 'Large Bell', 'Compass', 'Large Compass', 'City', 'Large City', 'Pepper', 'Large Pepper', 'Watermelon', 'Large Watermelon', 'Large Acorn', 'Acorn'), 'UnlockedExpRanks': ('Lizard', 'Boat', 'Large Lizard', 'Large Boat', 'Bat', 'Swords', 'Large Swords', 'Large Bat', 'Train Large', 'Tornado Large', 'Train', 'Tornado', 'Bull', 'Large Bull', 'Research', 'Large Research', 'Boat', 'Large UFO', 'Large Boat', 'UFO'), 'UnlockedFrames': ('Pink', 'Galaxy', 'Ice', 'CNY', 'Flower', 'Easter', 'Fire', 'Neon', 'Dragon', 'Buoy', 'Train', 'Pumpkin')}
PROFILE_GROUP_LABELS = {"UnlockedBadges": "Huy hiệu", "UnlockedExpRanks": "Danh hiệu",
                        "UnlockedFrames": "Khung", "UnlockedStyles": "Phong cách"}


def unlock_skins(xml: bytes, selection: Mapping[str, Iterable[str]]) -> tuple[bytes, dict]:
    validate_xml_document(xml, "Skin")
    match = _decor_block(xml, "Skins")
    block = match.group(0) if match else b"<Skins></Skins>"
    if block.rstrip().endswith(b"/>"):
        block = re.sub(rb"/\s*>$", b"></Skins>", block)
    added = 0
    for group, raw_ids in selection.items():
        selected = set(raw_ids)
        if group not in TSVIP_SKINS or not selected <= set(TSVIP_SKINS[group]):
            raise SaveToolError("Skin chứa nhóm/ID không hợp lệ")
        if not selected:
            continue
        matches = [m for m in re.finditer(rb"<type\b[^>]*>", block)
                   if parse_attributes(m.group(0)).get("id") == group]
        if len(matches) > 1:
            raise SaveToolError(f"Nhóm Skin {group} bị trùng")
        current = set()
        if matches:
            attrs = parse_attributes(matches[0].group(0))
            current = {x for x in html.unescape(attrs.get("available", "")).split("|") if x}
        combined = current | selected
        added += len(selected - current)
        ordered = [x for x in TSVIP_SKINS[group] if x in combined] + sorted(combined - set(TSVIP_SKINS[group]))
        value = "|".join(ordered) + "|"
        if matches:
            item = matches[0]
            tag = replace_attribute(item.group(0), "available", value)
            tag = replace_attribute(tag, "needViewUpgradeEffect", "0")
            block = block[:item.start()] + tag + block[item.end():]
        else:
            tag = f'<type id="{xml_escape_attribute(group)}" available="{xml_escape_attribute(value)}" needViewUpgradeEffect="0"/>'.encode()
            pos = block.rfind(b"</Skins")
            block = block[:pos] + tag + b"\n" + block[pos:]
    updated = _decor_replace_block(xml, "Skins", block)
    validate_xml_document(updated, "Skin sau mở")
    return updated, {"added": added, "groups": len(selection)}


def unlock_stickers(xml: bytes, ids: Iterable[str]) -> tuple[bytes, dict]:
    validate_xml_document(xml, "Stickers")
    catalog = tuple(x for group in TSVIP_STICKERS.values() for x in group)
    selected = set(ids)
    if not selected or not selected <= set(catalog):
        raise SaveToolError("Stickers chứa ID không hợp lệ")
    matches = _level_field_tags(xml, "UnlockedChatEmoji")
    if len(matches) > 1:
        raise SaveToolError("UnlockedChatEmoji bị trùng")
    existing = set()
    if matches:
        attrs = parse_attributes(matches[0].group(0))
        existing = {x for x in html.unescape(attrs.get("v", attrs.get("value", ""))).split(",") if x}
    combined = existing | selected
    # TSVIP delimiter is ,ID,,ID,; preserve unknown IDs already in the save.
    ordered = [x for x in catalog if x in combined] + sorted(combined - set(catalog))
    value = "".join(f",{x}," for x in ordered)
    updated = _m3_upsert_field(xml, "UnlockedChatEmoji", value, "s", "Global")
    validate_xml_document(updated, "Stickers sau mở")
    return updated, {"added": len(selected - existing), "total": len(combined)}


def unlock_profile(xml: bytes, selection: Mapping[str, Iterable[str]]) -> tuple[bytes, dict]:
    validate_xml_document(xml, "Profile")
    updated = xml
    total = 0
    for field, raw_ids in selection.items():
        selected = set(raw_ids)
        if field not in TSVIP_PROFILE or not selected <= set(TSVIP_PROFILE[field]):
            raise SaveToolError("Profile chứa nhóm/ID không hợp lệ")
        if not selected:
            continue
        ordered = [x for x in TSVIP_PROFILE[field] if x in selected]
        if field == "UnlockedStyles" and "glow" in selected:
            ordered.append("animatedUnderwaterViolet")
        value = ",".join(ordered)
        matches = [m for m in re.finditer(rb"<DataElem\b[^>]*>", updated)
                   if parse_attributes(m.group(0)).get("name") == field]
        if len(matches) > 1:
            raise SaveToolError(f"{field} bị trùng")
        if matches:
            item = matches[0]
            tag = replace_attribute(item.group(0), "value", value)
            tag = replace_attribute(tag, "type", "string")
            updated = updated[:item.start()] + tag + updated[item.end():]
        else:
            anchors = [m for m in re.finditer(rb"<DataElem\b[^>]*>", updated)
                       if parse_attributes(m.group(0)).get("name") == "UnlockedAvatars"]
            if len(anchors) != 1:
                raise SaveToolError(f"Thiếu {field} và không xác định được UnlockedAvatars để chèn đúng vị trí TSVIP")
            tag = f'<DataElem name="{field}" type="string" value="{xml_escape_attribute(value)}"/>'.encode()
            pos = anchors[0].start()
            updated = updated[:pos] + tag + b"\n" + updated[pos:]
        total += len(ordered)
    validate_xml_document(updated, "Profile sau cập nhật")
    return updated, {"items": total, "groups": len(selection)}


def unlock_achievements(xml: bytes, ids: Iterable[str]) -> tuple[bytes, dict]:
    validate_xml_document(xml, "Achievements")
    selected = set(ids)
    if not selected or not selected <= TSVIP_ACHIEVEMENTS.keys():
        raise SaveToolError("Achievements chứa ID không hợp lệ")
    updated = xml
    for achievement in TSVIP_ACHIEVEMENTS:
        if achievement not in selected:
            continue
        updated = _m3_upsert_field(updated, "AchReward_" + achievement, "4", "i", "Global")
        for field, value in TSVIP_ACHIEVEMENTS[achievement].items():
            updated = _m3_upsert_field(updated, field, str(value), "i", "Global")
    validate_xml_document(updated, "Achievements sau mở")
    return updated, {"achievements": len(selected)}


def unlock_catalog_states(xml: bytes, kind: str, group: str, ids: Iterable[str]) -> dict[str, bool]:
    root = validate_xml_document(xml, "Danh sách mở khóa")
    current = set()
    if kind == "skin":
        for node in root.findall("Skins/type"):
            if node.get("id") == group:
                current.update(x for x in node.get("available", "").split("|") if x)
    elif kind == "stickers":
        for node in root.iter():
            if node.get("name") == "UnlockedChatEmoji":
                current.update(x for x in node.get("v", node.get("value", "")).split(",") if x)
    elif kind == "profile":
        for node in root.iter("DataElem"):
            if node.get("name") == group:
                current.update(node.get("value", "").split(","))
    else:
        for node in root.iter():
            name = node.get("name", "")
            if name.startswith("AchReward_") and node.get("v", node.get("value")) == "4":
                current.add(name[len("AchReward_"):])
    return {item: item in current for item in ids}


def unlock_catalog_prompt(kind: str) -> None:
    SESSION.require_loaded()
    catalogs = {"skin": TSVIP_SKINS, "stickers": TSVIP_STICKERS, "profile": TSVIP_PROFILE,
                "achievements": {"Achievements": tuple(TSVIP_ACHIEVEMENTS)}}
    labels = {"skin": "Skin", "stickers": "Stickers", "profile": "Profile", "achievements": "Achievements"}
    catalog = catalogs[kind]
    groups = list(catalog)
    while True:
        assert SESSION.current_xml is not None
        print(f"\n--- {labels[kind]} ---")
        print("1. Xem danh sách / trạng thái | 2. Mở các mục chọn | 3. Mở cả nhóm | 4. Mở tất cả | 0. Quay lại")
        choice = input("Chọn: ").strip()
        if choice == "0":
            return
        try:
            if choice not in ("1", "2", "3", "4"):
                print("Lựa chọn không hợp lệ.")
                continue
            if choice != "4":
                for index, group in enumerate(groups, 1):
                    print(f"{index}. {PROFILE_GROUP_LABELS.get(group, group)} ({len(catalog[group])})")
                index = parse_int(input("Chọn nhóm: "), "Nhóm", 1, len(groups))
                group = groups[index - 1]
                ids = catalog[group]
                if choice in ("1", "2"):
                    states = unlock_catalog_states(SESSION.current_xml, kind, group, ids)
                    for index, item in enumerate(ids, 1):
                        names = PROFILE_ITEM_LABELS.get(group, ()) if kind == "profile" else ()
                        display = names[index - 1] if index <= len(names) else item
                        print(f"{index:4}. {display} | {'ĐÃ MỞ / ĐÃ ÁP DỤNG' if states[item] else 'CHƯA CÓ CỜ MỞ'}")
                    if choice == "1":
                        input("Nhấn Enter để quay lại...")
                        continue
                    raw = input("Chọn STT (vd 1,3,5-10; Enter để hủy): ").strip()
                    if not raw:
                        continue
                    indices = parse_avatar_selection(raw, (str(n) for n in range(1, len(ids) + 1)))
                    ids = tuple(ids[int(i) - 1] for i in indices)
                selection = {group: ids}
            else:
                selection = catalog
            if kind == "skin":
                updated, report = unlock_skins(SESSION.current_xml, selection)
            elif kind == "profile":
                print("Theo TSVIP, danh sách trong các nhóm Profile được chọn sẽ được THAY bằng lựa chọn này.")
                updated, report = unlock_profile(SESSION.current_xml, selection)
            elif kind == "stickers":
                updated, report = unlock_stickers(SESSION.current_xml, (item for values in selection.values() for item in values))
            else:
                print("Theo TSVIP: AchReward=4, đặt các bộ đếm về ngưỡng hoàn thành cố định trong APK.")
                updated, report = unlock_achievements(SESSION.current_xml, (item for values in selection.values() for item in values))
            print("Dự kiến:", report)
            if updated == SESSION.current_xml:
                print("Không có thay đổi.")
                continue
            if not ask_yes_no(f"Xác nhận áp dụng {labels[kind]}?"):
                print("Đã hủy.")
                continue
            SESSION.apply_xml(updated)
            print("Đã cập nhật XML làm việc. Về menu chính, chọn 43 ghi vào game hoặc 42 xuất local.")
        except SaveToolError as exc:
            print(f"Lỗi: {exc}")
        except KeyboardInterrupt:
            print("\nĐã hủy thao tác.")



# TSVIP v121: bp (Barn), a0 (inventory/Zoo), qx3 (Academy/Market/Advantages), px3 (roads/Train).
TSVIP_ACADEMY = {'Factory': {'bagfactory': {'level': '39', 'slx': '32161994', 'xpBonus': '100', 'moneyBonus': '100', 'timeBonus': '100', 'shelfBonus': '2'}, 'bakery': {'level': '53', 'slx': '32162008', 'xpBonus': '100', 'moneyBonus': '100', 'timeBonus': '100', 'shelfBonus': '2'}, 'bouquetfactory': {'level': '53', 'slx': '32162008', 'xpBonus': '100', 'moneyBonus': '100', 'timeBonus': '100', 'shelfBonus': '2'}, 'cakefactory': {'level': '53', 'slx': '32162008', 'xpBonus': '100', 'moneyBonus': '100', 'timeBonus': '100', 'shelfBonus': '2'}, 'candyfactory': {'level': '53', 'slx': '32162008', 'xpBonus': '100', 'moneyBonus': '100', 'timeBonus': '100', 'shelfBonus': '2'}, 'chipsfactory': {'level': '53', 'slx': '32162008', 'xpBonus': '100', 'moneyBonus': '100', 'timeBonus': '100', 'shelfBonus': '2'}, 'chocolatefactory': {'level': '53', 'slx': '32162008', 'xpBonus': '100', 'moneyBonus': '100', 'timeBonus': '100', 'shelfBonus': '2'}, 'clothingfactory': {'level': '38', 'slx': '32161995', 'xpBonus': '100', 'moneyBonus': '100', 'timeBonus': '100', 'shelfBonus': '2'}, 'coffeefactory': {'level': '38', 'slx': '32161995', 'xpBonus': '100', 'moneyBonus': '100', 'timeBonus': '100', 'shelfBonus': '2'}, 'cottonfactory': {'level': '53', 'slx': '32162008', 'xpBonus': '100', 'moneyBonus': '100', 'timeBonus': '100', 'shelfBonus': '2'}, 'dollfactory': {'level': '38', 'slx': '32161995', 'xpBonus': '100', 'moneyBonus': '100', 'timeBonus': '100', 'shelfBonus': '2'}, 'drinksfactory': {'level': '38', 'slx': '32161995', 'xpBonus': '100', 'moneyBonus': '100', 'timeBonus': '100', 'shelfBonus': '2'}, 'factory_music_instruments': {'level': '53', 'slx': '32162008', 'xpBonus': '100', 'moneyBonus': '100', 'timeBonus': '100', 'shelfBonus': '2'}, 'fastfoodfactory': {'level': '53', 'slx': '32162008', 'xpBonus': '100', 'moneyBonus': '100', 'timeBonus': '100', 'shelfBonus': '2'}, 'featherfactory': {'level': '38', 'slx': '32161995', 'xpBonus': '100', 'moneyBonus': '100', 'timeBonus': '100', 'shelfBonus': '2'}, 'frenchrestaurant': {'level': '43', 'slx': '32161990', 'xpBonus': '100', 'moneyBonus': '100', 'timeBonus': '100', 'shelfBonus': '2'}, 'furniturefactory': {'level': '38', 'slx': '32161995', 'xpBonus': '100', 'moneyBonus': '100', 'timeBonus': '100', 'shelfBonus': '2'}, 'gardeningfactory': {'level': '38', 'slx': '32161995', 'xpBonus': '100', 'moneyBonus': '100', 'timeBonus': '100', 'shelfBonus': '2'}, 'holidayfactory': {'level': '38', 'slx': '32161995', 'xpBonus': '100', 'moneyBonus': '100', 'timeBonus': '100', 'shelfBonus': '2'}, 'hotdogfactory': {'level': '38', 'slx': '32161995', 'xpBonus': '100', 'moneyBonus': '100', 'timeBonus': '100', 'shelfBonus': '2'}, 'housewaresfactory': {'level': '53', 'slx': '32162008', 'xpBonus': '100', 'moneyBonus': '100', 'timeBonus': '100', 'shelfBonus': '2'}, 'icecreamfactory': {'level': '52', 'slx': '32162009', 'xpBonus': '100', 'moneyBonus': '100', 'timeBonus': '100', 'shelfBonus': '2'}, 'italyfoodfactory': {'level': '38', 'slx': '32161995', 'xpBonus': '100', 'moneyBonus': '100', 'timeBonus': '100', 'shelfBonus': '2'}, 'jamfactory': {'level': '53', 'slx': '32162008', 'xpBonus': '100', 'moneyBonus': '100', 'timeBonus': '100', 'shelfBonus': '2'}, 'jewelryfactory': {'level': '23', 'slx': '32162042', 'xpBonus': '100', 'timeBonus': '100', 'shelfBonus': '2'}, 'kitchenwarefactory': {'level': '38', 'slx': '32161995', 'xpBonus': '100', 'moneyBonus': '100', 'timeBonus': '100', 'shelfBonus': '2'}, 'mexfoodfactory': {'level': '53', 'slx': '32162008', 'xpBonus': '100', 'moneyBonus': '100', 'timeBonus': '100', 'shelfBonus': '2'}, 'milkfactory': {'level': '53', 'slx': '32162008', 'xpBonus': '100', 'moneyBonus': '100', 'timeBonus': '100', 'shelfBonus': '2'}, 'mill': {'level': '13', 'slx': '32162016', 'timeBonus': '100', 'shelfBonus': '2'}, 'paperfactory': {'level': '53', 'slx': '32162008', 'xpBonus': '100', 'moneyBonus': '100', 'timeBonus': '100', 'shelfBonus': '2'}, 'petfactory': {'level': '38', 'slx': '32161995', 'xpBonus': '100', 'moneyBonus': '100', 'timeBonus': '100', 'shelfBonus': '2'}, 'roasterfactory': {'level': '43', 'slx': '32161990', 'xpBonus': '100', 'moneyBonus': '100', 'timeBonus': '100', 'shelfBonus': '2'}, 'scentfactory': {'level': '38', 'slx': '32161995', 'xpBonus': '100', 'moneyBonus': '100', 'timeBonus': '100', 'shelfBonus': '2'}, 'semifinishedfactory': {'level': '38', 'slx': '32161995', 'xpBonus': '100', 'moneyBonus': '100', 'timeBonus': '100', 'shelfBonus': '2'}, 'shoefactory': {'level': '53', 'slx': '32162008', 'xpBonus': '100', 'moneyBonus': '100', 'timeBonus': '100', 'shelfBonus': '2'}, 'spongefactory': {'level': '53', 'slx': '32162008', 'xpBonus': '100', 'moneyBonus': '100', 'timeBonus': '100', 'shelfBonus': '2'}, 'stationeryfactory': {'level': '38', 'slx': '32161995', 'xpBonus': '100', 'moneyBonus': '100', 'timeBonus': '100', 'shelfBonus': '2'}, 'sugarfactory': {'level': '53', 'slx': '32162008', 'xpBonus': '100', 'moneyBonus': '100', 'timeBonus': '100', 'shelfBonus': '2'}, 'sushifactory': {'level': '38', 'slx': '32161995', 'xpBonus': '100', 'moneyBonus': '100', 'timeBonus': '100', 'shelfBonus': '2'}, 'tea_factory': {'level': '53', 'slx': '32162008', 'xpBonus': '100', 'moneyBonus': '100', 'timeBonus': '100', 'shelfBonus': '2'}, 'vegancafe': {'level': '38', 'slx': '32161995', 'xpBonus': '100', 'moneyBonus': '100', 'timeBonus': '100', 'shelfBonus': '2'}, 'wheelfactory': {'level': '52', 'slx': '32162009', 'xpBonus': '100', 'moneyBonus': '100', 'timeBonus': '100', 'shelfBonus': '2'}}, 'Train': {'1': {'level': '31', 'slx': '32162034', 'xpBonus': '100', 'timeBonus': '100'}, '2': {'level': '31', 'slx': '32162034', 'xpBonus': '100', 'timeBonus': '100'}, '3': {'level': '31', 'slx': '32162034', 'xpBonus': '100', 'timeBonus': '100'}}, 'Island': {'i1': {'level': '31', 'slx': '32162034', 'timeBonus': '99', 'probability2': '10', 'probability3': '10'}, 'i2': {'level': '31', 'slx': '32162034', 'timeBonus': '99', 'probability2': '10', 'probability3': '10'}, 'i3': {'level': '31', 'slx': '32162034', 'timeBonus': '99', 'probability2': '10', 'probability3': '10'}, 'i4': {'level': '31', 'slx': '32162034', 'timeBonus': '99', 'probability2': '10', 'probability3': '10'}, 'i5': {'level': '31', 'slx': '32162034', 'timeBonus': '99', 'probability2': '10', 'probability3': '10'}}}
TSVIP_BARN_PRODUCTS = ['wheat', 'corn', 'carrot', 'sugarcane', 'cotton', 'strawberry', 'tomat', 'pine', 'potato', 'cacao', 'rubberTree', 'rubber', 'silk', 'shelk', 'pepper', 'rice', 'roseSeed', 'jasmine', 'coffee', 'soybean', 'teabush', 'mint', 'peanut', 'lavender', 'cork', 'aloeLeaves', 'milk', 'egg', 'wool', 'bacon', 'honeycomb', 'mushroom', 'downFeather', 'bigFeather', 'clay', 'apple', 'peach', 'watermelon', 'plum', 'grapes', 'fish', 'shrimp', 'lobster', 'scallop', 'pearl', 'seaweed', 'banana', 'coconut', 'pineapple', 'olive', 'lemon', 'aloe', 'mango1', 'avocado', 'cowfeed', 'chickenfeed', 'sheepfeed', 'pigfeed', 'beefeed', 'mushroomfeed', 'flour', 'bread', 'cookie', 'bagel', 'pizza', 'potatobread', 'bananabread', 'mushroomPie', 'strudel', 'marinepizza', 'dough', 'cream', 'cheese', 'butter', 'yogurt', 'peachyogurt', 'sugar', 'syrup', 'caramel', 'candy', 'caramelapple', 'jellybeans', 'toffee', 'candystick', 'lollipop', 'honeycandy', 'fruitjelly', 'chocobar', 'teacandies', 'mintlollipops', 'cottonCandy', 'chocolate', 'icecream', 'frozenyogurt', 'fruitice', 'eskimo', 'pineapplesorbet', 'roseSorbet', 'parfait', 'mintchocolateicecream', 'muffin', 'brownie', 'cupcake', 'doughnut', 'cheesecake', 'limepie', 'coconutmacaroon', 'honeycake', 'strawberrycake', 'weddingcake', 'coffeecake', 'chocolatecake', 'carrotcake', 'mintcake', 'tiramisu', 'honeycaramel', 'fruitmix', 'chips', 'popcorn', 'cornchips', 'granola', 'canape', 'glazedbacon', 'puffedrice', 'saltedpeanut', 'frenchfries', 'sandwich', 'cheeseburger', 'bakedpotatoes', 'fishburger', 'fish_chips', 'peanot_crepes', 'hot_dog', 'corndog', 'cheese_coney', 'carrot_hotdog', 'taco', 'nachos', 'burrito', 'jalapeno', 'falafel', 'hummus', 'guacamole', 'bacon_eggs', 'pancake', 'milkshake', 'grap_fizz', 'chocolate_smoothie', 'watermelon_fresh', 'tropical_mix', 'cold_tea', 'minticetea', 'applefresh', 'espresso', 'cappuccino', 'mokachino', 'hot_chocolate', 'blacktea', 'whitetea', 'rosetea', 'tibettea', 'oolong', 'appletea', 'coconut_raf', 'teabags', 'woolfabric', 'cottonfabric', 'silkfabric', 'nylonthread', 'shirt', 'sweater', 'coat', 'hat', 'suit', 'tiroleanHat', 'eveningdress', 'dress', 'flipflops', 'sandals', 'sneakers', 'boots', 'heels', 'downBoots', 'downJacket', 'bathrobeslippers', 'paper', 'papertowel', 'wallpapers', 'book', 'stickers', 'marker', 'eraser', 'corkboard', 'table', 'chair', 'couch', 'bed', 'floor_lamp', 'pillow', 'duvet', 'tissue', 'dispenser', 'lounge', 'sushi', 'lobster_nigiri', 'scallopsushi', 'soup', 'misosoup', 'corn_soup', 'mushroomSoup', 'gazpacho', 'bouillabaisse', 'seaweedsalad', 'mushroomSalad', 'seafood_salad', 'nicoise', 'rice_noodle', 'thai_sauce', 'sauce', 'quiche', 'fried_fish', 'rice_casserole', 'baked_lobster', 'lobster_newburg', 'scallopskew', 'grilledMeat', 'ratatouille', 'profiteroles', 'gyoza', 'readylunch', 'frozenvegetables', 'seafoodcocktail', 'oliveoil', 'bruschetta', 'arrabbiata', 'ravioli', 'lasagna', 'mole', 'vegancheesecake', 'jam', 'strawberry_jam', 'peach_jam', 'watermelon_jam', 'plum_jam', 'grapes_jam', 'roseJam', 'mushroom_jam', 'applejam', 'peanut_butter', 'ketchup', 'driedMushrooms', 'tofu', 'soymilk', 'custard', 'brownCandle', 'perfumeBottle', 'flowerSoap', 'lotionBottle', 'aromatic_oil', 'air_freshener', 'creammask', 'toothpaste', 'vitamin_cocktail', 'pendant', 'ring', 'pearlneck', 'earrings', 'diadem', 'featherEarrings', 'toys', 'ball', 'shuttlecock', 'Plasticine', 'ragdoll', 'puppet', 'chinadoll', 'barbie', 'ukulele', 'saxophone', 'drum', 'accordion', 'panpipe', 'pettoy', 'cattoy', 'waterbowl', 'catcave', 'catlitter', 'airballoon', 'soapBubbles', 'lei', 'pinata', 'clover', 'bridebouquet', 'sweetbouquet', 'basketbouquet', 'teacoffeebouquet', 'driedflowers', 'summerbouquet', 'vegetablebouquet', 'toolset', 'irrigationhose', 'flowertub', 'gardengnome', 'brush', 'clothesline', 'plunger', 'duster', 'gloves', 'plastic', 'glue', 'dumbbell', 'plasticbottle', 'wheel', 'mug', 'frypan', 'teapot', 'cutlery', 'teaceremonykit', 'potstand', 'newbackpack', 'basket', 'handbag', 'suitcase', 'kidsbag', 'Brick', 'Glass', 'Plita', 'hammerMat', 'nailMat', 'paintRedMat', 'axe', 'powersaw', 'pick', 'TNT', 'jackhammer', 'drill']
TSVIP_ZOO_ANIMALS = {'paddock_bear': 'Bears', 'paddock_flamingo': 'Flamingos', 'paddock_zebra': 'Zebras', 'paddock_penguin': 'Penguins', 'paddock_monkey': 'Chimpanzees', 'paddock_lion': 'Lions', 'paddock_hippo': 'Hippos', 'paddock_girrafe': 'Giraffes', 'paddock_polar_bear': 'Polar Bears', 'paddock_koala': 'Koalas', 'paddock_elephant': 'Elephants', 'paddock_crocodile': 'Crocodiles', 'paddock_kangaroo': 'Kangaroos', 'paddock_seal': 'Fur Seals', 'paddock_gorilla': 'Gorillas', 'paddock_panda': 'Giant Pandas', 'paddock_beaver': 'Beavers', 'paddock_rhino': 'Rhinoceroses', 'paddock_muskOx': 'Muskoxen', 'paddock_tiger': 'Tigers', 'paddock_peacock': 'Peacocks', 'paddock_turtle': 'Giant Tortoises', 'paddock_camel': 'Camels', 'paddock_deer': 'Reindeer', 'paddock_toucan': 'Toucans', 'paddock_skunk': 'Skunks', 'paddock_ostrich': 'Ostriches', 'paddock_panther': 'Black Panthers', 'paddock_arcticfox': 'Arctic Foxes', 'paddock_platypus': 'Platypuses', 'paddock_boar': 'Wild Boars', 'paddock_gazelle': 'Gazelles', 'paddock_pelican': 'Pelicans', 'paddock_lynx': 'Lynx', 'paddock_parrot': 'Macaws', 'paddock_raccoon': 'Raccoons', 'paddock_tapir': 'Tapirs', 'paddock_walrus': 'Walruses', 'paddock_laski': 'Martens', 'paddock_crane': 'Black Crowned Cranes', 'paddock_snow_monkey': 'Snow Monkeys', 'paddock_porcupine': 'Porcupines', 'paddock_eagle': 'Bald Eagles', 'paddock_fennec': 'Fennec Foxes', 'paddock_WhiteOwl': 'Snowy Owls', 'paddock_armadillo': 'Three-Banded Armadillos', 'paddock_redPanda': 'Red Pandas', 'paddock_polarwolf': 'Arctic Wolves', 'paddock_anteater': 'Anteaters', 'paddock_llama': 'Llamas'}
TSVIP_ADVANTAGES = {'SP_BoostSpeedUpBuildings': '100', 'SP_BoostSpeedUpHarvest': '100', 'SP_BoostSpeedUpFarms': '100', 'SP_BoostStorageCapacity': '999', 'SP_BoostSpeedUpAir': '100', 'SP_BoostTrainMats': '3', 'SP_MarketPremium': '100', 'SP_BoostOrderCoins': '100', 'SP_BoostMineRocket': '3', 'SP_BoostClanHelpRequest': '2'}
TSVIP_QUANTITIES = {'m3Line': ('m3Line', None), 'm3Bomb': ('m3Bomb', None), 'm3RainbowBall': ('m3RainbowBall', None), 'm3Mallet': ('m3Mallet', None), 'm3HorizontalLine': ('m3HorizontalLine', None), 'm3VerticalLine': ('m3VerticalLine', None), 'm3Reshuffle': ('m3Reshuffle', None), 'BoostProductFarm': ('BoostProductFarm', None), 'BoostDoubleFactory': ('BoostDoubleFactory', None), 'BoostSpeedUpTrains': ('BoostSpeedUpTrains', None), 'BoostMoneyOrder': ('BoostMoneyOrder', None), 'BoostTimeFactory': ('BoostTimeFactory', None), 'BoostTimeSmeltery': ('BoostTimeSmeltery', None), 'BoostTimeMarket': ('BoostTimeMarket', None), 'BoostSpeedUpShips': ('BoostSpeedUpShips', None), 'BoostAirportCoins': ('BoostAirportCoins', None), 'BoostMaxDonate': ('BoostMaxDonate', None), 'BoostStorageCapacity': ('BoostStorageCapacity', None), 'BoostHeartsZoo': ('BoostHeartsZoo', None), 'BoostClanHelpRequest': ('BoostClanHelpRequest', None), 'BoostLanternMine': ('BoostLanternMine', None), 'BoostProbabilityIslands': ('BoostProbabilityIslands', None), 'BoostProductHarvest': ('BoostProductHarvest', None), 'BoostSpeedUpDealer': ('BoostSpeedUpDealer', None), 'BoostSpeedUpHarvest': ('BoostSpeedUpHarvest', None), 'BoostSpeedUpOrder': ('BoostSpeedUpOrder', None), 'gem1': ('gem1', 'sgc1x'), 'gem2': ('gem2', 'sgc2x'), 'gem3': ('gem3', 'sgc3x'), 'GoldBullion': ('GoldBullionCounter', 'sgbcx'), 'SilverBullion': ('SilverBullionCounter', 'ssbcx'), 'BronzeBullion': ('BronzeBullionCounter', 'sbbcx'), 'PlatinumBullion': ('PlatinumBullionCounter', 'spbcx'), 'm1': ('m1', 'sm1x'), 'm2': ('m2', 'sm2x'), 'm3': ('m3', 'sm3x'), 'o1': ('o1', None), 'o2': ('o2', None), 'o3': ('o3', None), 'o4': ('o4', None), 'o5': ('o5', None), 'clovers': ('clovers', None)}
TSVIP_COUPONS = ['CouponUpgradeFactory', 'CouponUpgradeIsland', 'CouponUpgradeTrain', 'CouponLoadTrainAirport', 'freeExpansion', 'freeAmbarInc', 'CouponHireDealer']
TSVIP_QUANTITY_LABELS = {'m3Line': 'Đường Thẳng', 'm3Bomb': 'Bom', 'm3RainbowBall': 'Cầu Vồng', 'm3Mallet': 'Búa', 'm3HorizontalLine': 'Ngang', 'm3VerticalLine': 'Dọc', 'm3Reshuffle': 'Xáo Trộn', 'BoostProductFarm': 'x2 Thu Hoạch', 'BoostDoubleFactory': 'x2 Nhà Máy', 'BoostSpeedUpTrains': 'Tăng Tốc Tàu', 'BoostMoneyOrder': 'Giảm Đơn Hàng', 'BoostTimeFactory': 'Tăng Tốc Nhà Máy', 'BoostTimeSmeltery': 'Tăng Tốc Lò', 'BoostTimeMarket': 'Tăng Tốc Chợ', 'BoostSpeedUpShips': 'Tăng Tốc Tàu Biển', 'BoostAirportCoins': 'Xu Sân Bay', 'BoostMaxDonate': 'Tặng Tối Đa', 'BoostStorageCapacity': 'Sức Chứa', 'BoostHeartsZoo': 'Tim Sở Thú', 'BoostClanHelpRequest': 'Yêu Cầu Giúp Đỡ', 'BoostLanternMine': 'Đèn Mỏ', 'BoostProbabilityIslands': 'Xác Suất Đảo', 'BoostProductHarvest': 'Sản Xuất Thu Hoạch', 'BoostSpeedUpDealer': 'Tăng Tốc Người Bán', 'BoostSpeedUpHarvest': 'Tăng Tốc Thu Hoạch', 'BoostSpeedUpOrder': 'Tăng Tốc Đơn', 'gem1': 'Đá Quý 1', 'gem2': 'Đá Quý 2', 'gem3': 'Đá Quý 3', 'GoldBullion': 'GoldBullion', 'SilverBullion': 'SilverBullion', 'BronzeBullion': 'BronzeBullion', 'PlatinumBullion': 'PlatinumBullion', 'm1': 'Cuốc Chim', 'm2': 'Thuốc Nổ', 'm3': 'Cưa Máy', 'o1': 'Quặng Đồng', 'o2': 'Quặng Vàng', 'o3': 'Quặng Bạc', 'o4': 'Quặng Bạch Kim', 'o5': 'Quặng Đồng Đỏ', 'clovers': 'clovers', 'CouponUpgradeFactory': 'Phiếu Nâng Cấp Nhà Máy', 'CouponUpgradeIsland': 'Phiếu Nâng Cấp Đảo', 'CouponUpgradeTrain': 'Phiếu Nâng Cấp Tàu', 'CouponLoadTrainAirport': 'Phiếu Tàu/Sân Bay', 'freeExpansion': 'Mở Rộng Miễn Phí', 'freeAmbarInc': 'Ô Kho Miễn Phí', 'CouponHireDealer': 'Phiếu Thuê Thương Nhân'}

def _advanced_integer(value: int, label: str, maximum: int = 2_147_483_647) -> int:
    if type(value) is not int or not 0 <= value <= maximum:
        raise SaveToolError(f"{label}: cần số nguyên từ 0 đến {maximum}")
    return value


def _advanced_block(xml: bytes, name: str) -> bytes:
    match = _decor_block(xml, name)
    if match is None:
        raise SaveToolError(f"Save chưa có khối {name}")
    block = match.group(0)
    opening = block[:block.index(b'>') + 1]
    if opening.rstrip().endswith(b'/>' ):
        block = re.sub(rb'/\s*>$', b'>', opening) + b'</' + name.encode() + b'>'
    return block


def _advanced_field(xml: bytes, name: str, value: str, field_type: str = 'i') -> bytes:
    """Scope global counters so identically named fields elsewhere stay untouched."""
    global_name = 'Global' if _decor_block(xml, 'Global') else 'Globals'
    block = _advanced_block(xml, global_name)
    block = _m3_upsert_field(block, name, value, field_type, global_name)
    return _decor_replace_block(xml, global_name, block)


def _advanced_read(xml: bytes, name: str) -> str:
    global_name = 'Global' if _decor_block(xml, 'Global') else 'Globals'
    block = _advanced_block(xml, global_name)
    matches = _level_field_tags(block, name)
    if len(matches) > 1:
        raise SaveToolError(f"Trường {name} bị trùng")
    if not matches:
        return '0'
    attrs = parse_attributes(matches[0].group(0))
    return html.unescape(attrs.get('value', attrs.get('v', '0')))


def barn_capacity(level: int) -> int:
    _advanced_integer(level, 'Barn level')
    if level <= 3:
        return 50 + 20 * level
    if level <= 39:
        return 110 + (level - 3) * 25
    if level <= 59:
        return 1010 + (level - 39) * 50
    if level <= 100:
        return 2010 + (level - 59) * 75
    return 5085 + (level - 100) * 75


def set_barn_level(xml: bytes, level: int) -> bytes:
    _advanced_integer(level, 'Barn level')
    xml = _advanced_field(xml, 'WareHouseCashUpgrade', str(level))
    return _advanced_field(xml, 'WHUdup', str((level ^ 514698188) & 0xffffffff))


def barn_product_field(product: str) -> str:
    if product not in TSVIP_BARN_PRODUCTS:
        raise SaveToolError(f"Sản phẩm không có trong TSVIP: {product}")
    direct = {'Brick', 'Glass', 'Plita', 'axe', 'powersaw', 'hammerMat',
              'nailMat', 'paintRedMat', 'pick', 'TNT', 'jackhammer', 'drill'}
    return product if product in direct else product + 'Counter'


def set_barn_products(xml: bytes, products: Iterable[str], count: int) -> bytes:
    _advanced_integer(count, 'Số lượng')
    for product in dict.fromkeys(products):
        name = barn_product_field(product)
        xml = _advanced_field(xml, name, str(count), 'i' if count else None)
        global_name = 'Global' if _decor_block(xml, 'Global') else 'Globals'
        block = _advanced_block(xml, global_name)
        matches = _level_field_tags(block, name)
        tag = matches[0].group(0)
        if tag.startswith(b'<Var'):
            new = replace_attribute(tag, 't', 'i') if count else re.sub(rb'\s+t\s*=\s*([\'"])[^\'"]*\1', b'', tag)
            block = block[:matches[0].start()] + new + block[matches[0].end():]
            xml = _decor_replace_block(xml, global_name, block)
    return xml


def set_academy(xml: bytes, kind: str, ids: Iterable[str], bonuses: dict | None = None) -> bytes:
    if kind not in TSVIP_ACADEMY:
        raise SaveToolError('Nhóm Academy không hợp lệ')
    ids = list(dict.fromkeys(ids))
    if not ids or any(item not in TSVIP_ACADEMY[kind] for item in ids):
        raise SaveToolError('Chọn ID Academy trong danh sách TSVIP')
    bonuses = bonuses or {}
    allowed = {'timeBonus', 'products'} if kind == 'Island' else {'timeBonus', 'xpBonus', 'moneyBonus', 'shelfBonus'}
    if set(bonuses) - allowed:
        raise SaveToolError('Tên bonus Academy không hợp lệ')
    for key, value in bonuses.items():
        _advanced_integer(value, key, 2 if key == 'shelfBonus' else 101 if kind == 'Island' and key == 'timeBonus' else 100)
    match = _decor_block(xml, 'Upgrade')
    block = _advanced_block(xml, 'Upgrade') if match else b'<Upgrade version="4"></Upgrade>'
    for item in ids:
        template = TSVIP_ACADEMY[kind][item]
        attrs = {'id': item, 'level': template['level'], 'slx': template['slx']}
        if kind == 'Island':
            speed = bonuses.get('timeBonus', 101)
            attrs.update(timeBonus=str(101 if speed == 100 else speed),
                         probability2=str(bonuses.get('products', 100)),
                         probability3=str(bonuses.get('products', 100)))
        else:
            for key in ('xpBonus', 'moneyBonus', 'timeBonus', 'shelfBonus'):
                if key in template or (kind == 'Train' and key == 'moneyBonus' and key in bonuses):
                    attrs[key] = str(bonuses.get(key, 2 if key == 'shelfBonus' else 100))
        tags = [m for m in re.finditer(rb'<' + kind.encode() + rb'\b[^>]*?/\s*>', block)
                if html.unescape(parse_attributes(m.group(0)).get('id', '')) == item]
        if len(tags) > 1:
            raise SaveToolError(f'Academy {kind} {item} bị trùng')
        tag = tags[0].group(0) if tags else b'<' + kind.encode() + b'/>'
        for key, value in attrs.items():
            tag = replace_attribute(tag, key, value)
        if tags:
            block = block[:tags[0].start()] + tag + block[tags[0].end():]
        else:
            block = block.replace(b'</Upgrade>', b'\n    ' + tag + b'\n</Upgrade>')
    return _decor_replace_block(xml, 'Upgrade', block)


def _json_attribute_rows(xml: bytes, attribute: str = 'v') -> list:
    rows = []
    for match in re.finditer(rb'<[A-Za-z_][\w:.-]*\b[^>]*>', xml):
        attrs = parse_attributes(match.group(0))
        raw = attrs.get(attribute)
        if raw is None:
            continue
        try:
            data = json.loads(html.unescape(raw))
        except (ValueError, TypeError):
            continue
        if isinstance(data, dict):
            rows.append((match, data))
    return rows


def _json_replace_tag(xml: bytes, match, data: dict, attribute: str = 'v') -> bytes:
    tag = replace_attribute(match.group(0), attribute, json.dumps(data, ensure_ascii=False, separators=(',', ':')))
    return xml[:match.start()] + tag + xml[match.end():]


def zoo_card_inventory(xml: bytes) -> tuple:
    infos = list(re.finditer(rb'<ZooInfo\b[^>]*>', xml))
    infos = [m for m in infos if 'Paddocks' in parse_attributes(m.group(0))]
    if len(infos) != 1:
        raise SaveToolError('Cần một ZooInfo có thuộc tính Paddocks')
    try:
        data = json.loads(html.unescape(parse_attributes(infos[0].group(0))['Paddocks']))
    except ValueError as exc:
        raise SaveToolError('Paddocks không phải JSON hợp lệ') from exc
    if not isinstance(data, dict) or not isinstance(data.get('list'), list):
        raise SaveToolError('Paddocks thiếu list động vật')
    return infos[0], data


def set_zoo_cards(xml: bytes, ids: Iterable[str], now: int | None = None) -> bytes:
    selected = set(ids)
    if not selected or selected - TSVIP_ZOO_ANIMALS.keys():
        raise SaveToolError('Chọn động vật trong danh sách TSVIP')
    match, data = zoo_card_inventory(xml)
    now = int(time.time()) if now is None else now
    changed = 0
    for paddock in data['list']:
        if not isinstance(paddock, dict) or paddock.get('type') not in selected:
            continue
        members = paddock.get('members', [])
        if not isinstance(members, list):
            raise SaveToolError('members động vật không hợp lệ')
        for member in members:
            if isinstance(member, dict):
                member.update(piecesCount=30, status=3)
                if 'unlockTime' in member and int(member['unlockTime']) <= now:
                    member.pop('unlockTime')
        paddock['count'] = len(members)
        if paddock.get('rewardCollected'):
            paddock['rewardCollected'] = False
        changed += 1
    if not changed:
        raise SaveToolError('Chưa có chuồng động vật được chọn trong save')
    return _json_replace_tag(xml, match, data, 'Paddocks')


def set_market_slots(xml: bytes, count: int) -> bytes:
    if type(count) is not int or not 1 <= count <= 9999:
        raise SaveToolError('Số ô Market phải từ 1 đến 9999')
    rows = [(m, d) for m, d in _json_attribute_rows(xml)
            if d.get('storeId') == 'citymarket' and 'slotsCount' in d]
    if len(rows) != 1:
        raise SaveToolError('Cần một Object citymarket có slotsCount')
    match, data = rows[0]
    data['slotsCount'] = count
    return _json_replace_tag(xml, match, data)


def _timed_multiplier(xml: bytes, entities: Iterable[str], days: int, now: int) -> bytes:
    _advanced_integer(days, 'Số ngày', 36500)
    match = _decor_block(xml, 'TimedEntityManager')
    block = _advanced_block(xml, 'TimedEntityManager') if match else b'<TimedEntityManager configVersion="1"></TimedEntityManager>'
    for entity in entities:
        tags = [m for m in re.finditer(rb'<item\b[^>]*?/\s*>', block)
                if parse_attributes(m.group(0)).get('entityType') == entity]
        if len(tags) > 1:
            raise SaveToolError(f'Timed entity {entity} bị trùng')
        if not days:
            if tags:
                block = block[:tags[0].start()] + block[tags[0].end():]
            continue
        tag = (f'<item entityType="{entity}" timeEnd="{now + days * 86400}" '
               'multiplier="2.0000000000000000" isAttemptsMode="0" attemptsCount="0"/>').encode()
        if tags:
            block = block[:tags[0].start()] + tag + block[tags[0].end():]
        else:
            block = block.replace(b'</TimedEntityManager>', tag + b'\n</TimedEntityManager>')
    return _decor_replace_block(xml, 'TimedEntityManager', block)


def set_advantages(xml: bytes, values: dict, mine_days: int | None = None) -> bytes:
    if set(values) - TSVIP_ADVANTAGES.keys():
        raise SaveToolError('Tên Advantages không hợp lệ')
    if values:
        for key, value in values.items():
            _advanced_integer(value, key)
        season = _advanced_block(xml, 'SeasonTicket')
        season = re.sub(rb'<Vars\b([^>]*)/\s*>', rb'<Vars\1></Vars>', season)
        # TSVIP maps MineRocket to DiggingPremiumLevel outside SeasonTicket.
        for key, value in values.items():
            if key == 'SP_BoostMineRocket':
                xml = _advanced_field(xml, 'DiggingPremiumLevel', '1' if value else '0')
            else:
                season = _m3_upsert_field(season, key, str(value), 'i', 'Vars')
        scores = {'396', '531'} | {score for key, score in {'SP_BoostTrainMats':'3',
                  'SP_BoostOrderCoins':'36', 'SP_MarketPremium':'111', 'SP_BoostSpeedUpFarms':'336'}.items()
                  if values.get(key, 0) > 0}
        road = _decor_block(season, 'PremiumRoad')
        if road and any(v > 0 for k,v in values.items() if k != 'SP_BoostMineRocket'):
            block = road.group(0)
            block = re.sub(rb'<Stage\b[^>]*>', lambda m: replace_attribute(m.group(0), 'rewardGiven', '1')
                           if parse_attributes(m.group(0)).get('score') in scores else m.group(0), block)
            season = season[:road.start()] + block + season[road.end():]
        xml = _decor_replace_block(xml, 'SeasonTicket', season)
    if mine_days is not None:
        xml = _timed_multiplier(xml, ['MineMultiplier'], mine_days, int(time.time()))
    return xml


def golden_pass_stages(xml: bytes, road: str) -> list:
    if road not in ('FreeRoad', 'PremiumRoad'):
        raise SaveToolError('Road không hợp lệ')
    season = _advanced_block(xml, 'SeasonTicket')
    block = _advanced_block(season, road)
    return [m.group(0) for m in re.finditer(rb'<Stage\b[^>]*/>|<Stage\b[^>]*>.*?</Stage\s*>', block, re.S)]


def edit_golden_pass_stages(xml: bytes, road: str, indices: Iterable[int],
                            reward_type: str | None = None, count: int | None = None,
                            given: bool | None = None, subrewards: list | None = None) -> bytes:
    stages = golden_pass_stages(xml, road)
    indices = set(indices)
    if not indices or any(type(i) is not int or i < 1 or i > len(stages) for i in indices):
        raise SaveToolError('STT Stage không hợp lệ')
    if count is not None:
        _advanced_integer(count, 'Reward count')
    if reward_type is not None and not re.fullmatch(r'[A-Za-z0-9_]+', reward_type):
        raise SaveToolError('Reward type không hợp lệ')
    if given is not None and type(given) is not bool:
        raise SaveToolError('rewardGiven phải là bật/tắt')
    season = _advanced_block(xml, 'SeasonTicket')
    block = _advanced_block(season, road)
    index = 0
    def patch_stage(match):
        nonlocal index
        index += 1
        if index not in indices:
            return match.group(0)
        stage = match.group(0)
        opening_end = stage.index(b'>') + 1
        opening = stage[:opening_end]
        if given is not None:
            opening = replace_attribute(opening, 'rewardGiven', '1') if given else re.sub(rb'\s+rewardGiven\s*=\s*([\'"])[^\'"]*\1', b'', opening)
        stage = opening + stage[opening_end:]
        reward = re.search(rb'<Reward\b[^>]*?/\s*>|<Reward\b[^>]*>.*?</Reward\s*>', stage, re.S)
        if reward_type is None and count is None and subrewards is None:
            return stage
        if reward is None:
            raise SaveToolError(f'Stage {index} chưa có Reward')
        reward_block = reward.group(0)
        end = reward_block.index(b'>') + 1
        tag = reward_block[:end]
        attrs = parse_attributes(tag)
        if reward_type is not None:
            tag = replace_attribute(tag, 'type', reward_type)
        if count is not None:
            tag = replace_attribute(tag, 'count', str(count))
        final_type = reward_type or attrs.get('type')
        if final_type == 'ST_Chest' and subrewards is not None:
            tag = re.sub(rb'/\s*>$', b'>', tag)
            children = b''
            for item in subrewards:
                if not isinstance(item, dict) or not re.fullmatch(r'[A-Za-z0-9_]+', item.get('type', '')):
                    raise SaveToolError('SubReward: cần type hợp lệ')
                amount = _advanced_integer(item.get('count', 0), 'SubReward count')
                flag = ' rewardGiven="1"' if item.get('rewardGiven', False) else ''
                children += f'<SubReward type="{item["type"]}" count="{amount}"{flag}/>'.encode()
            replacement = tag + children + b'</Reward>'
        elif final_type != 'ST_Chest':
            replacement = re.sub(rb'/\s*>$|>$', b'/>', tag)
        else:
            replacement = tag + reward_block[end:]
        return stage[:reward.start()] + replacement + stage[reward.end():]
    block = re.sub(rb'<Stage\b[^>]*/>|<Stage\b[^>]*>.*?</Stage\s*>', patch_stage, block, flags=re.S)
    season = _decor_replace_block(season, road, block)
    return _decor_replace_block(xml, 'SeasonTicket', season)


def train_inventory(xml: bytes) -> tuple:
    containers = list(re.finditer(rb'<Trains\b[^>]*>.*?</Trains\s*>', xml, re.S))
    found = []
    for container in containers:
        rows = [(m, d) for m, d in _json_attribute_rows(container.group(0))
                if any(f'productId_{n}' in d or f'productCount_{n}' in d for n in range(1, 6))]
        if rows:
            found.append((container, rows))
    if len(found) != 1:
        raise SaveToolError('Cần một khối Trains có dữ liệu toa tàu')
    return found[0]


def edit_train_wagons(xml: bytes, train_index: int, wagons: Iterable[int], values: dict) -> bytes:
    container, rows = train_inventory(xml)
    if type(train_index) is not int or not 1 <= train_index <= len(rows):
        raise SaveToolError('STT tàu không hợp lệ')
    wagons = set(wagons)
    if not wagons or any(type(n) is not int or not 1 <= n <= 5 for n in wagons):
        raise SaveToolError('Toa tàu phải từ 1 đến 5')
    allowed = {'productId', 'productCount', 'orderBlue', 'orderBlueTime', 'cardPack', 'productDone'}
    if not values or set(values) - allowed:
        raise SaveToolError('Trường toa tàu không hợp lệ')
    for key, value in values.items():
        if key == 'productCount':
            if type(value) is not int or not -2_147_483_648 <= value <= 2_147_483_647:
                raise SaveToolError('productCount nằm ngoài giới hạn int32')
        elif key in ('orderBlue', 'orderBlueTime', 'productDone'):
            _advanced_integer(value, key)
        elif not isinstance(value, str) or (value and not re.fullmatch(r'[A-Za-z0-9_]+', value)):
            raise SaveToolError(f'{key} không hợp lệ')
    match, data = rows[train_index - 1]
    for n in wagons:
        if not any(f'{key}_{n}' in data for key in ('productId', 'productCount')):
            raise SaveToolError(f'Tàu chưa có toa {n}; không thêm toa mới')
        for key, value in values.items():
            field = f'cardPack{n}' if key == 'cardPack' else f'{key}_{n}'
            data[field] = value
        if values.get('orderBlue') == 0:
            data.pop(f'cardPack{n}', None)
        if values.get('productDone') == 0:
            for key in list(data):
                if key in (f'productDone_{n}', f'orderId_{n}', f'checked_{n}') or key.startswith(f'orderFriend_{n}_'):
                    data.pop(key)
    block = _json_replace_tag(container.group(0), match, data)
    return xml[:container.start()] + block + xml[container.end():]


def _quantity_data_field(xml: bytes, name: str, count: int, ancestor: str | None = None) -> bytes:
    scopes = [(0, len(xml), {})] if ancestor is None else [row for row in _dataelem_spans(xml) if row[2].get('name') == ancestor]
    edits = []
    for start, end, _ in scopes:
        for match in _level_field_tags(xml[start:end], name):
            tag = match.group(0)
            if not tag.startswith(b'<DataElem'):
                continue
            edits.append((start + match.start(), start + match.end(), replace_attribute(tag, 'value', str(count))))
    edits = list({(a,b):c for a,b,c in edits}.items())
    if not edits:
        raise SaveToolError(f'Save chưa có {ancestor or "DataElem"}/{name}')
    for (start,end), tag in sorted(edits, reverse=True):
        xml = xml[:start] + tag + xml[end:]
    return xml


def set_quantities(xml: bytes, values: dict, now: int | None = None) -> bytes:
    now = int(time.time()) if now is None else now
    coupon_values = {}
    for key, count in values.items():
        _advanced_integer(count, key)
        if key in TSVIP_QUANTITIES:
            name, mirror = TSVIP_QUANTITIES[key]
            xml = _advanced_field(xml, name, str(count))
            if mirror:
                xml = _advanced_field(xml, mirror, str((count ^ 509438470) & 0xffffffff))
        elif key in TSVIP_COUPONS:
            coupon_values[key] = count
        elif key == 'lives_inf_days':
            _advanced_integer(count, key, 36500)
            matches = _level_field_tags(xml, 'Lives_infTime_Match3')
            if count == 0:
                for m in reversed(matches):
                    xml = xml[:m.start()] + xml[m.end():]
            else:
                block = _advanced_block(xml, 'Minigames')
                # Prefer Match3 Vars; refuse ambiguity instead of inserting in another minigame.
                minis = [m for m in re.finditer(rb'<Minigame\b[^>]*>.*?</Minigame\s*>', block, re.S)
                         if parse_attributes(m.group(0).split(b'>',1)[0]+b'>').get('id','').lower() == 'match3']
                if len(minis) != 1:
                    raise SaveToolError('Chưa có một Minigame Match3 để đặt vô hạn mạng')
                mini = minis[0]
                part = re.sub(rb'<Vars\b([^>]*)/\s*>', rb'<Vars\1></Vars>', mini.group(0))
                part = _m3_upsert_field(part, 'Lives_infTime_Match3', str(now + count*86400), 'i', 'Vars')
                block = block[:mini.start()] + part + block[mini.end():]
                xml = _decor_replace_block(xml, 'Minigames', block)
        elif key == 'booster2x_days':
            entities = ['CouponsM3','ShortContest2Note','WeeklyMissionsMultiplier','MayorsQuestsMultiplier',
                        'Competition1vs1Multiplier','Merge2EnergyMultiplier','ShortContestNote','BigContestCup',
                        'ExpeditionEnergyMultiplier','ArcheryMultiplier','EventScoreMultiplier','RoomScoreMultiplier',
                        'CascadeMultiplier','SeasonMiniGameProgressMultiplier','RegataMiniGameProgressMultiplier']
            xml = _timed_multiplier(xml, entities, count, now)
        elif key in ('currency_provider_amount', 'train_journey_amount'):
            if key == 'train_journey_amount':
                scopes = [r for r in _dataelem_spans(xml) if r[2].get('name') == 'TrainJourney']
                if len(scopes) != 1:
                    raise SaveToolError('Cần một TrainJourney')
                a,b,_ = scopes[0]
                xml = xml[:a] + _quantity_data_field(xml[a:b], 'Amount', count, 'CurrencyProvider') + xml[b:]
            else:
                xml = _quantity_data_field(xml, 'Amount', count, 'CurrencyProvider')
        elif key == 'star':
            scopes = [r for r in _dataelem_spans(xml) if not xml[r[0]:r[1]].rstrip().endswith(b'/>' ) and re.search(rb'<DataElem\b[^>]*\bname=[\'"]first[\'"][^>]*\bvalue=[\'"]TradeLogic[\'"]', xml[r[0]:r[1]])]
            if not scopes:
                raise SaveToolError('Save chưa có TradeLogic')
            a,b,_ = min(scopes, key=lambda r:r[1]-r[0])
            part = xml[a:b]
            for name in ('additionalTokens','currentTokens','lastSeenTokens'):
                part = _quantity_data_field(part, name, count)
            xml = xml[:a] + part + xml[b:]
        elif key == 'match3_moves':
            block = _advanced_block(xml, 'Minigames')
            minis = [m for m in re.finditer(rb'<Minigame\b[^>]*>.*?</Minigame\s*>', block, re.S)
                     if parse_attributes(m.group(0).split(b'>',1)[0]+b'>').get('id','').lower() == 'match3']
            if len(minis) != 1:
                raise SaveToolError('Cần một Minigame Match3')
            mini = minis[0]; part = mini.group(0)
            info = list(re.finditer(rb'<LevelInfo\b[^>]*>', part))
            if len(info) != 1:
                raise SaveToolError('Cần một LevelInfo Match3')
            m = info[0]
            part = part[:m.start()] + replace_attribute(m.group(0), 'addMovesUntilCompletion', str(count)) + part[m.end():]
            block = block[:mini.start()] + part + block[mini.end():]
            xml = _decor_replace_block(xml, 'Minigames', block)
        else:
            raise SaveToolError(f'Quantities không hỗ trợ {key}')
    if coupon_values:
        old = _advanced_read(xml, 'GivingOffersDeferred')
        pairs = {}
        if old != '0':
            for entry in old.split(','):
                if ':' in entry:
                    name, amount = entry.rsplit(':',1)
                    pairs[name.strip()] = parse_int(amount.strip(), name, 0, 2_147_483_647)
        pairs.update(coupon_values)
        xml = _advanced_field(xml, 'GivingOffersDeferred', ','.join(f'{k}:{v}' for k,v in pairs.items() if v > 0), None)
    return xml


def _advanced_select(ids: Iterable[str]) -> list[str]:
    ids = list(ids)
    raw = input('Chọn STT (1,3,5-10), all = tất cả, 0 = quay lại: ').strip()
    if raw == '0':
        return []
    if raw.lower() in ('all', '*'):
        return ids
    selected = parse_avatar_selection(raw, [str(n) for n in range(1, len(ids)+1)])
    return [ids[int(n)-1] for n in selected]


def _advanced_apply(xml: bytes, label: str) -> None:
    validate_xml_document(xml, label)
    if xml == SESSION.current_xml:
        print('Không có thay đổi.')
    elif ask_yes_no(f'Áp dụng {label} vào XML đang chỉnh sửa?', default=False):
        SESSION.apply_xml(xml)
        print('Đã cập nhật. Chọn 50 để xuất/verify hoặc 51 để encode + ghi game.')


def barn_prompt() -> None:
    SESSION.require_loaded()
    while True:
        try:
            xml = SESSION.current_xml
            level = parse_int(_advanced_read(xml, 'WareHouseCashUpgrade'), 'Barn level', 0, 2_147_483_647)
            print(f'\nBarn: cấp {level}, sức chứa cơ bản {barn_capacity(level)}')
            print('1. Đặt cấp kho  2. Xem/chỉnh sản phẩm  0. Quay lại')
            choice = input('Chọn: ').strip()
            if choice == '0': return
            if choice == '1':
                raw = input('Cấp kho mới (trống = hủy): ').strip()
                if not raw: continue
                value = parse_int(raw, 'Cấp kho', 0, 2_147_483_647)
                print(f'Sức chứa cơ bản mới: {barn_capacity(value)} (chưa tính boost).')
                _advanced_apply(set_barn_level(xml, value), 'Barn level')
            elif choice == '2':
                for n, product in enumerate(TSVIP_BARN_PRODUCTS,1):
                    print(f'{n:3}. {product}: {_advanced_read(xml,barn_product_field(product))}')
                selected = _advanced_select(TSVIP_BARN_PRODUCTS)
                if selected:
                    count = parse_int(input('Số lượng mới: ').strip(), 'Số lượng', 0, 2_147_483_647)
                    _advanced_apply(set_barn_products(xml, selected, count), f'{len(selected)} sản phẩm Barn')
            else: print('Lựa chọn không hợp lệ.')
        except (SaveToolError, ValueError) as exc:
            print(f'Lỗi: {exc}')


def academy_prompt() -> None:
    SESSION.require_loaded()
    while True:
        try:
            print('\nAcademy: 1. Nhà máy  2. Tàu hỏa  3. Đảo  0. Quay lại')
            choice = input('Chọn: ').strip()
            if choice == '0': return
            kind = {'1':'Factory','2':'Train','3':'Island'}.get(choice)
            if not kind:
                print('Lựa chọn không hợp lệ.'); continue
            xml = SESSION.current_xml
            block = _decor_block(xml, 'Upgrade')
            existing = {}
            if block:
                for m in re.finditer(rb'<' + kind.encode() + rb'\b[^>]*>', block.group(0)):
                    attrs = parse_attributes(m.group(0)); existing[attrs.get('id')] = attrs
            ids = list(TSVIP_ACADEMY[kind])
            for n, item in enumerate(ids,1):
                print(f'{n:2}. {item}: {existing.get(item,"chưa nâng cấp")} -> cấp TSVIP {TSVIP_ACADEMY[kind][item]["level"]}')
            selected = _advanced_select(ids)
            if not selected: continue
            print('Cấp và slx theo TSVIP; để trống bonus dùng mặc định TSVIP.')
            keys = ['timeBonus','products'] if kind == 'Island' else ['xpBonus','moneyBonus','timeBonus','shelfBonus'] if kind == 'Factory' else ['xpBonus','timeBonus','moneyBonus']
            bonuses = {}
            for key in keys:
                maximum = 2 if key == 'shelfBonus' else 101 if kind == 'Island' and key == 'timeBonus' else 100
                raw = input(f'{key} (0..{maximum}): ').strip()
                if raw: bonuses[key] = parse_int(raw, key, 0, maximum)
            _advanced_apply(set_academy(xml, kind, selected, bonuses), f'Academy {kind}: {len(selected)} mục')
        except SaveToolError as exc:
            print(f'Lỗi: {exc}')


def zoo_cards_prompt() -> None:
    SESSION.require_loaded()
    while True:
        try:
            xml = SESSION.current_xml
            _, data = zoo_card_inventory(xml)
            present = {p.get('type'):p for p in data['list'] if isinstance(p,dict)}
            ids = list(TSVIP_ZOO_ANIMALS)
            print('\nZoo Card: hoàn thành thẻ động vật (30 mảnh, status=3).')
            for n,item in enumerate(ids,1):
                p = present.get(item)
                state = ', '.join(f'{m.get("piecesCount",0)}/30; trạng thái {m.get("status",0)}' for m in p.get('members',[]) if isinstance(m,dict)) if p else 'chưa có trong save'
                print(f'{n:2}. {TSVIP_ZOO_ANIMALS[item]} ({item}): {state}')
            selected = _advanced_select(ids)
            if not selected: return
            available = [item for item in selected if item in present]
            if len(available) < len(selected): print(f'Bỏ qua {len(selected)-len(available)} chuồng chưa có trong save.')
            if available: _advanced_apply(set_zoo_cards(xml, available), f'Zoo Card: {len(available)} loài')
        except (SaveToolError, ValueError) as exc:
            print(f'Lỗi: {exc}'); return


def market_prompt() -> None:
    SESSION.require_loaded()
    while True:
        try:
            xml = SESSION.current_xml
            rows = [d for _,d in _json_attribute_rows(xml) if d.get('storeId') == 'citymarket']
            if len(rows) != 1: raise SaveToolError('Không xác định được citymarket')
            print(f'\nMarket: {rows[0].get("slotsCount","không có slotsCount")} ô. TSVIP cho phép 1..9999.')
            raw = input('Số ô mới (0 = quay lại): ').strip()
            if raw == '0': return
            _advanced_apply(set_market_slots(xml,parse_int(raw,'Số ô',1,9999)), 'Market slots')
        except SaveToolError as exc:
            print(f'Lỗi: {exc}')
            if not rows or len(rows) != 1: return


def advantages_prompt() -> None:
    SESSION.require_loaded()
    while True:
        try:
            xml = SESSION.current_xml
            print('\nAdvantages: 1. Xem/chọn bonus Golden Pass  2. Mine x2 (ngày)  0. Quay lại')
            choice = input('Chọn: ').strip()
            if choice == '0': return
            if choice == '1':
                season = _advanced_block(xml, 'SeasonTicket')
                ids = list(TSVIP_ADVANTAGES)
                for n,key in enumerate(ids,1):
                    tags = _level_field_tags(season,key)
                    current = parse_attributes(tags[0].group(0)).get('v','0') if len(tags)==1 else '0'
                    if key == 'SP_BoostMineRocket': current = _advanced_read(xml,'DiggingPremiumLevel')
                    print(f'{n:2}. {key}: {current}; mặc định TSVIP {TSVIP_ADVANTAGES[key]}')
                selected = _advanced_select(ids)
                if not selected: continue
                values = {}
                for key in selected:
                    raw = input(f'{key} (trống = {TSVIP_ADVANTAGES[key]}, 0 = tắt): ').strip()
                    values[key] = parse_int(raw or TSVIP_ADVANTAGES[key], key, 0, 2_147_483_647)
                _advanced_apply(set_advantages(xml, values), 'Advantages')
            elif choice == '2':
                days = parse_int(input('Mine x2: số ngày (0 = tắt): ').strip(),'Số ngày',0,36500)
                _advanced_apply(set_advantages(xml,{},days), 'Mine x2')
            else: print('Lựa chọn không hợp lệ.')
        except SaveToolError as exc:
            print(f'Lỗi: {exc}')


def golden_pass_editor_prompt() -> None:
    SESSION.require_loaded()
    while True:
        try:
            xml = SESSION.current_xml
            season = _advanced_block(xml, 'SeasonTicket')
            print('\nGolden Pass Editor:',parse_attributes(season.split(b'>',1)[0]+b'>'))
            print('1. FreeRoad  2. PremiumRoad  3. Sửa premium/score  0. Quay lại')
            choice = input('Chọn: ').strip()
            if choice == '0': return
            if choice == '3':
                opening_end = season.index(b'>')+1; opening = season[:opening_end]
                premium = input('premium (0/1, trống = giữ): ').strip()
                score = input('score (trống = giữ): ').strip()
                if premium: opening = replace_attribute(opening,'premium',str(parse_int(premium,'premium',0,1)))
                if score: opening = replace_attribute(opening,'score',str(parse_int(score,'score',0,2_147_483_647)))
                _advanced_apply(_decor_replace_block(xml,'SeasonTicket',opening+season[opening_end:]), 'Golden Pass premium/score')
                continue
            road = {'1':'FreeRoad','2':'PremiumRoad'}.get(choice)
            if not road:
                print('Lựa chọn không hợp lệ.'); continue
            stages = golden_pass_stages(xml,road)
            if not stages: raise SaveToolError('Road chưa có Stage')
            for n,stage in enumerate(stages,1):
                print(f'{n:2}. {stage.decode("utf-8")}')
            selected = _advanced_select([str(n) for n in range(1,len(stages)+1)])
            if not selected: continue
            print('Các giá trị trống giữ nguyên; nhận thưởng 0 sẽ xóa rewardGiven.')
            rtype = input('Reward type (vd cash, ST_Chest): ').strip() or None
            raw_count = input('Reward count: ').strip()
            count = parse_int(raw_count,'Reward count',0,2_147_483_647) if raw_count else None
            raw_given = input('rewardGiven (0/1): ').strip()
            given = bool(parse_int(raw_given,'rewardGiven',0,1)) if raw_given else None
            subrewards = None
            if rtype == 'ST_Chest':
                raw = input('SubReward JSON [{"type":"cash","count":100,"rewardGiven":false}] (trống giữ, [] xóa): ').strip()
                if raw:
                    try: subrewards = json.loads(raw)
                    except ValueError as exc: raise SaveToolError('SubReward JSON không hợp lệ') from exc
                    if not isinstance(subrewards,list): raise SaveToolError('SubReward cần JSON array')
            new = edit_golden_pass_stages(xml,road,[int(v) for v in selected],rtype,count,given,subrewards)
            _advanced_apply(new, f'Golden Pass Editor {road}, {len(selected)} Stage')
        except SaveToolError as exc:
            print(f'Lỗi: {exc}')


def quantities_prompt() -> None:
    SESSION.require_loaded()
    groups = {'1':list(TSVIP_QUANTITIES), '2':list(TSVIP_COUPONS),
              '3':['lives_inf_days','booster2x_days'],
              '4':['currency_provider_amount','train_journey_amount','star','match3_moves']}
    while True:
        try:
            xml = SESSION.current_xml
            print('\nQuantities: 1. Booster/Lab/Mỏ/Thỏi/Quặng/Cỏ ba lá  2. Coupons  3. Thời gian boost  4. Token/Star/M3 moves  0. Quay lại')
            choice = input('Chọn: ').strip()
            if choice == '0': return
            ids = groups.get(choice)
            if not ids:
                print('Lựa chọn không hợp lệ.'); continue
            for n,key in enumerate(ids,1):
                current = _advanced_read(xml,TSVIP_QUANTITIES[key][0]) if key in TSVIP_QUANTITIES else 'chỉnh trong dữ liệu riêng'
                print(f'{n:2}. {TSVIP_QUANTITY_LABELS.get(key,key)} [{key}]: {current}')
            selected = _advanced_select(ids)
            if not selected: continue
            values = {}
            for key in selected:
                maximum = 36500 if key.endswith('_days') else 2_147_483_647
                values[key] = parse_int(input(f'{key}: ').strip(),key,0,maximum)
            _advanced_apply(set_quantities(xml,values),f'Quantities: {len(values)} mục')
        except SaveToolError as exc:
            print(f'Lỗi: {exc}')


def train_prompt() -> None:
    SESSION.require_loaded()
    while True:
        try:
            xml = SESSION.current_xml
            _, rows = train_inventory(xml)
            print('\nTrain: chỉnh toa hiện có (khác nâng cấp tàu trong Academy).')
            for n,(_,data) in enumerate(rows,1):
                print(f'Tàu {n}:')
                for wagon in range(1,6):
                    details = {k:v for k,v in data.items() if k in [f'{key}_{wagon}' for key in ('productId','productCount','productDone','orderBlue','orderBlueTime')] or k == f'cardPack{wagon}'}
                    if details: print(f'  Toa {wagon}: {details}')
            raw = input('STT tàu (0 = quay lại): ').strip()
            if raw == '0': return
            train = parse_int(raw,'Tàu',1,len(rows))
            data = rows[train-1][1]
            wagon_ids = [str(n) for n in range(1,6) if f'productId_{n}' in data or f'productCount_{n}' in data]
            print('Các toa có thể sửa:', ', '.join(wagon_ids))
            raw = input('Chọn số toa (1,3 hoặc 1-5), all = tất cả, 0 = hủy: ').strip()
            if raw == '0': continue
            selected = wagon_ids if raw.lower() in ('all', '*') else parse_avatar_selection(raw, wagon_ids)
            if not selected: continue
            print('Để trống giữ nguyên. productDone=0 đặt lại toa và xóa orderId/checked/orderFriend theo TSVIP.')
            values = {}
            for key in ('productId','productCount','orderBlue','orderBlueTime','cardPack','productDone'):
                raw = input(f'{key}: ').strip()
                if not raw: continue
                if key in ('productId','cardPack'): values[key] = '' if raw == '-' else raw
                else: values[key] = parse_int(raw,key,-2_147_483_648 if key == 'productCount' else 0,2_147_483_647)
            if values:
                _advanced_apply(edit_train_wagons(xml,train,[int(v) for v in selected],values),f'Train {train}, {len(selected)} toa')
        except SaveToolError as exc:
            print(f'Lỗi: {exc}')
            if 'Cần một khối Trains' in str(exc): return


def edit_date_prompt() -> None:
    SESSION.require_loaded()
    assert SESSION.current_xml is not None
    attrs = read_var(SESSION.current_xml, "gameStartDate")
    old_timestamp = attrs.get("v", "")
    try:
        old_display = datetime.fromtimestamp(int(old_timestamp), UTC_PLUS_7).strftime(
            "%d/%m/%Y %H:%M:%S UTC+7"
        )
    except (ValueError, OSError):
        old_display = "không đọc được"
    print(f"Ngày hiện tại: {old_timestamp} ({old_display})")
    year = parse_int(input("Năm mới: "), "Năm", 1970, 2100)
    month = parse_int(input("Tháng mới: "), "Tháng", 1, 12)
    dt = datetime(year, month, 1, tzinfo=UTC_PLUS_7)
    print(f"Dự kiến: 01/{month:02d}/{year} 00:00:00 UTC+7 ({int(dt.timestamp())})")
    if not ask_yes_no("Xác nhận thay đổi?"):
        print("Đã hủy.")
        return
    new_xml, _ = set_game_start_month(SESSION.current_xml, year, month)
    SESSION.apply_xml(new_xml)
    print("Đã cập nhật XML làm việc. Chưa ghi vào game.")


def edit_any_var_prompt() -> None:
    SESSION.require_loaded()
    assert SESSION.current_xml is not None
    var_name = input("Var name cần sửa: ").strip()
    if not var_name:
        raise SaveToolError("Tên Var không được rỗng")
    attrs = read_var(SESSION.current_xml, var_name)
    print("Thuộc tính hiện tại:", attrs)
    raw = input('Nhập thuộc tính cần sửa, ví dụ v=123,t=i: ').strip()
    updates = parse_update_pairs(raw)
    if "name" in updates:
        raise SaveToolError("Không cho đổi thuộc tính name của Var")
    print("Thay đổi:", updates)
    if not ask_yes_no("Xác nhận thay đổi?"):
        print("Đã hủy.")
        return
    new_xml, changes = patch_var(SESSION.current_xml, var_name, updates)
    SESSION.apply_xml(new_xml)
    print("Đã sửa:", changes)


def parse_key_value_pairs(raw: str) -> dict[str, str]:
    result: dict[str, str] = {}
    if not raw.strip():
        return result
    for part in raw.split(","):
        if "=" not in part:
            raise SaveToolError(f"Thiếu dấu '=' trong {part!r}")
        key, value = part.split("=", 1)
        key = key.strip()
        value = value.strip()
        if not key:
            raise SaveToolError("Tên thuộc tính không được rỗng")
        result[key] = value
    return result


def parse_update_pairs(raw: str) -> dict[str, str]:
    result = parse_key_value_pairs(raw)
    if not result:
        raise SaveToolError("Phải có ít nhất một thuộc tính cần sửa")
    return result


def edit_any_tag_prompt() -> None:
    SESSION.require_loaded()
    assert SESSION.current_xml is not None
    tag_name = input("Tên tag, ví dụ Trung: ").strip()
    if not tag_name:
        raise SaveToolError("Tên tag không được rỗng")
    selector = parse_key_value_pairs(
        input('Điều kiện tìm tag, ví dụ set1=abc,a1=1982: ')
    )
    if not selector:
        raise SaveToolError("Cần ít nhất một thuộc tính ổn định để tìm đúng tag")
    attrs = read_tag_attributes(SESSION.current_xml, tag_name, selector)
    print("Tag hiện tại:", attrs)
    updates = parse_update_pairs(
        input('Thuộc tính cần sửa, ví dụ name=3000,value=0: ')
    )
    overlap = set(selector) & set(updates)
    if overlap:
        raise SaveToolError(
            "Không sửa thuộc tính đang dùng làm điều kiện tìm tag: " + ", ".join(overlap)
        )
    print("Thay đổi:", updates)
    if not ask_yes_no("Xác nhận thay đổi?"):
        print("Đã hủy.")
        return
    new_xml, changes = patch_tag_attributes(
        SESSION.current_xml, tag_name, selector, updates
    )
    SESSION.apply_xml(new_xml)
    print("Đã sửa:", changes)




# TSVIP v121: qx3.t tasks, xz2 SendBox, xg4.l V1, yt1.v V3, mk3 tutorial templates.
TSVIP_TUTORIAL_FIXES = {'market': {'label': '1. Fix City Market Tutorial', 'fields': {'TutorialDealerFreeDayNotice': '<Var name="TutorialDealerFreeDayNotice" v="1" t="b"/>', 'SkipDealerWelcomeTutorialOnce': '<Var name="SkipDealerWelcomeTutorialOnce" v="0"/>', 'ReportedFreeMarketSlots': '<Var name="ReportedFreeMarketSlots" v="200" t="i"/>'}}, 'mine': {'label': '2. Fix Digging Mine Tutorial', 'fields': {'DiggingReady': '<Var name="DiggingReady" v="1" t="b"/>', 'DiggingPreVisit': '<Var name="DiggingPreVisit" v="1" t="b"/>', 'DiggingVisited': '<Var name="DiggingVisited" v="1" t="b"/>', 'diggingFullCompleted': '<Var name="diggingFullCompleted" v="1" t="b"/>', 'NeedArrowOnDigging': '<Var name="NeedArrowOnDigging" v="0" t="b"/>', 'RepairDiggingTutShowed': '<Var name="RepairDiggingTutShowed" v="1" t="b"/>', 'RequestedDiggingMuseumResources': '<Var name="RequestedDiggingMuseumResources" v="1" t="b"/>', 'DiggingTutorShowed': '<Var name="DiggingTutorShowed" v="1"/>', 'FirstDiggingClayShowed': '<Var name="FirstDiggingClayShowed" v="1"/>', 'FirstDiggingClayTutorial_state': '<Var name="FirstDiggingClayTutorial_state" v="18"/>', 'FirstDiggingClayTutorialsq0_state': '<Var name="FirstDiggingClayTutorialsq0_state" v="0"/>', 'FirstDiggingHardstoneShowed': '<Var name="FirstDiggingHardstoneShowed" v="1"/>', 'FirstDiggingRoomShowed': '<Var name="FirstDiggingRoomShowed" v="1"/>', 'FirstDiggingStoneShowed': '<Var name="FirstDiggingStoneShowed" v="1"/>', 'ExtractClayVideoTutorial_state': '<Var name="ExtractClayVideoTutorial_state" v="18"/>', 'ExtractClayVideoTutorialsq0_state': '<Var name="ExtractClayVideoTutorialsq0_state" v="0"/>', 'DestroyClayTutorial_state': '<Var name="DestroyClayTutorial_state" v="18"/>', 'DestroyClayTutorialsq0_state': '<Var name="DestroyClayTutorialsq0_state" v="0"/>', 'DestroyClayShowed': '<Var name="DestroyClayShowed" v="1"/>', 'DestroyClay2Tutorial_state': '<Var name="DestroyClay2Tutorial_state" v="18" t="i"/>', 'DestroyClay2Tutorialsq0_state': '<Var name="DestroyClay2Tutorialsq0_state" v="0" t="i"/>', 'DestroyClay2Showed': '<Var name="DestroyClay2Showed" v="1" t="b"/>'}}, 'train': {'label': '3. Fix Train Tutorial', 'fields': {'SkinTutorialShowedFor_Train': '<Var name="SkinTutorialShowedFor_Train" v="1" t="b"/>', 'SkinTutorialShowedFor_TrainStation': '<Var name="SkinTutorialShowedFor_TrainStation" v="1" t="b"/>'}}, 'helicopter': {'label': '4. Fix Helicopter Tutorial', 'fields': {'SkinTutorialShowedFor_Helicopter': '<Var name="SkinTutorialShowedFor_Helicopter" v="1" t="b"/>', 'SkinTutorialShowedFor_HelicopterPlace': '<Var name="SkinTutorialShowedFor_HelicopterPlace" v="1" t="b"/>'}}, 'port': {'label': '5. Fix Island- Ship/Port Tutorial', 'fields': {'HarborBoatSend_state': '<Var name="HarborBoatSend_state" v="18" t="i"/>', 'HarborBoatSendsq0_state': '<Var name="HarborBoatSendsq0_state" v="0" t="i"/>', 'HarborFirstLook_state': '<Var name="HarborFirstLook_state" v="18" t="i"/>', 'HarborFirstLooksq0_state': '<Var name="HarborFirstLooksq0_state" v="0" t="i"/>', 'HarborFirstLook2_state': '<Var name="HarborFirstLook2_state" v="18" t="i"/>', 'HarborFirstLook2sq0_state': '<Var name="HarborFirstLook2sq0_state" v="0" t="i"/>', 'harborFullCompleted': '<Var name="harborFullCompleted" v="1" t="b"/>', 'HarborTutorShowed': '<Var name="HarborTutorShowed" v="1" t="b"/>', 'HarborTutor2Showed': '<Var name="HarborTutor2Showed" v="1" t="b"/>', 'NeedArrowOnHarbor': '<Var name="NeedArrowOnHarbor" v="0" t="b"/>', 'RepairHarborTutShowed': '<Var name="RepairHarborTutShowed" v="1" t="b"/>', 'tutorial_finished_step': '<Var name="tutorial_finished_step" v="RepairHarbor"/>', 'SkinTutorialShowedFor_Harbor': '<Var name="SkinTutorialShowedFor_Harbor" v="1" t="b"/>', 'IslandInterfaceVisited': '<Var name="IslandInterfaceVisited" v="1" t="i"/>', 'IslandsMapShowed': '<Var name="IslandsMapShowed" v="1" t="b"/>', 'Tutorial:IslandsDailyChest:Showed': '<Var name="Tutorial:IslandsDailyChest:Showed" v="1"/>'}}, 'industry': {'label': '6. Fix Industry Academy Tutorial', 'fields': {'IndustryAcademyTutShowed': '<Var name="IndustryAcademyTutShowed" v="1" t="b"/>', 'AcademyReady': '<Var name="AcademyReady" v="1" t="b"/>', 'BuildAcademyTutShowed': '<Var name="BuildAcademyTutShowed" v="1" t="b"/>'}}, 'airport': {'label': '7. Fix Airport Tutorial', 'fields': {'AirFirstLook_state': '<Var name="AirFirstLook_state" v="18" t="i"/>', 'AirFirstLooksq0_state': '<Var name="AirFirstLooksq0_state" v="0" t="i"/>', 'AirTutorialShowed': '<Var name="AirTutorialShowed" v="1" t="b"/>', 'AirTutorShowed': '<Var name="AirTutorShowed" v="1" t="b"/>', 'airportFullCompleted': '<Var name="airportFullCompleted" v="1" t="b"/>', 'NeedArrowOnAir': '<Var name="NeedArrowOnAir" v="0" t="b"/>', 'sendAirplaneCount': '<Var name="sendAirplaneCount" v="1" t="i"/>', 'SkinTutorialShowedFor_Airplane': '<Var name="SkinTutorialShowedFor_Airplane" v="1" t="b"/>', 'SkinTutorialShowedFor_Airport': '<Var name="SkinTutorialShowedFor_Airport" v="1" t="b"/>', 'PlaneAccelerationTutorialsq0_state': '<Var name="PlaneAccelerationTutorialsq0_state" v="0"/>', 'PlaneAccelerationTutorial_state': '<Var name="PlaneAccelerationTutorial_state" v="10"/>', 'PlaneCompetitionTutorial_state': '<Var name="PlaneCompetitionTutorial_state" v="10"/>', 'PlaneCompetitionTutorialsq0_state': '<Var name="PlaneCompetitionTutorialsq0_state" v="0"/>', 'PlaneFinishTutorial_state': '<Var name="PlaneFinishTutorial_state" v="10"/>', 'PlaneFinishTutorialsq0_state': '<Var name="PlaneFinishTutorialsq0_state" v="0"/>', 'PlaneProduceFuelTutorial_state': '<Var name="PlaneProduceFuelTutorial_state" v="10"/>', 'PlaneProduceFuelTutorialsq0_state': '<Var name="PlaneProduceFuelTutorialsq0_state" v="0"/>', 'PlaneStartTutorialsq0_state': '<Var name="PlaneStartTutorialsq0_state" v="0"/>', 'PlaneStartTutorial_state': '<Var name="PlaneStartTutorial_state" v="10"/>', 'PlaneSecondStartTutorial_state': '<Var name="PlaneSecondStartTutorial_state" v="10"/>', 'PlaneSecondStartTutorialsq0_state': '<Var name="PlaneSecondStartTutorialsq0_state" v="0"/>', 'PlaneShowedTipsCount': '<Var name="PlaneShowedTipsCount" v="94" t="i"/>'}}, 'zoo': {'label': '8. Fix Zoo tutorial', 'fields': {'NeedArrowOnZoo': '<Var name="NeedArrowOnZoo" v="0" t="b"/>', 'OldZooVisited': '<Var name="OldZooVisited" v="0" t="b"/>', 'RequestedZooResources': '<Var name="RequestedZooResources" v="1" t="b"/>', 'ZooVisited': '<Var name="ZooVisited" v="1" t="b"/>', 'ZooWasRecovered': '<Var name="ZooWasRecovered" v="1" t="b"/>', 'TutorialZooShowed': '<Var name="TutorialZooShowed" v="1" t="b"/>', 'ZooRepairReminderShowed': '<Var name="ZooRepairReminderShowed" v="1" t="b"/>', 'ZooRepairShowed': '<Var name="ZooRepairShowed" v="1" t="b"/>', 'TutorialBusStopRepairedShowed': '<Var name="TutorialBusStopRepairedShowed" v="1" t="b"/>', 'BusStationReady': '<Var name="BusStationReady" v="1" t="b"/>', 'bus_stationFullCompleted': '<Var name="bus_stationFullCompleted" v="1" t="b"/>'}}, 'smeltery': {'label': '9. Fix Smeltery Tutorial', 'fields': {'InitialSmelteryReady': '<Var name="InitialSmelteryReady" v="1" t="b"/>', 'SmelteryProductionEverWasStarted': '<Var name="SmelteryProductionEverWasStarted" v="1" t="b"/>', 'BuildSmelteryTutShowed': '<Var name="BuildSmelteryTutShowed" v="1" t="b"/>'}}}
TSVIP_CLONE_STAT_FIELDS = ['sexpx', 'experience', 'levelup', 'gameStartDate', 'WareHouseCashUpgrade', 'WHUdup', 'townName', 'likes', 'Glass', 'gemsSpent', 'freeIncAmbarCapacity', 'dayInGame', 'hammerMat', 'jackhammer', 'nailMat', 'gem1', 'gem2', 'gem3', 'm1', 'm2', 'm3', 'MyBadge', 'MyTheme', 'clovers', 'MyFrame', 'MyStyle', 'FullCardCollections', 'UnlockedChatEmoji', 'FullCardSets', 'AchievementBuyStatue', 'Achievement_Teamwork', 'GHash', 'paintRedMat', 'powersaw', 'expeditionFreeTNT', 'expeditionEnergy', 'Plita', 'drill', 'LivesSent', 'sm1x', 'sm2x', 'sm3x', 'MyPicture', 'sgc1x', 'sgc2x', 'sgc3x', 'sgc4x', 'Brick', 'freeExpansionCount', 'FirstAttemptM3Levels', 'DaysEnteredGame', 'RegataTasksCompleted', 'TimeInGame', 'TNT', 'axe', 'pick', 'o1', 'o3', 'o2', 'o4', 'clayCounter', 'm3Bomb', 'm3HorizontalLine', 'm3Mallet', 'm3Reshuffle', 'm3VerticalLine', 'm3RainbowBall', 'm3Airplane']
TSVIP_CLONE_STAT_PREFIXES = ['match3', 'Match3', 'Unlocked_ava', 'Achievement_', 'AchReward', 'Boost', 'M3', 'm3', 'Counterx']
TSVIP_CLONE_STAT_GROUPS = [['moneyCash'], ['money'], ['levelup'], ['m3_comp_lvls', 'M3Ch_mainM3', 'STLM3'], ['FirstAttemptM3Levels'], ['LivesSent'], ['Achievement_Teamwork'], ['FullCardCollections'], ['RegataTasksCompleted', 'RegataPoints'], ['gameStartDate', 'startDate'], ['expeditionEnergy', 'expedition_energy', 'ExpeditionEnergyCurrent'], ['depth', 'mine_depth']]


def _clone_field_value(xml: bytes, name: str, default: str = '') -> str:
    global_block = _decor_block(xml, 'Global')
    tags = _level_field_tags(global_block.group(0), name) if global_block else []
    if not tags: tags = _level_field_tags(xml, name)
    if not tags:
        return default
    values = {html.unescape(a.get('value', a.get('v', ''))) for a in (parse_attributes(m.group(0)) for m in tags)}
    if len(values) != 1:
        raise SaveToolError(f'{name} có nhiều giá trị khác nhau; không thể clone')
    return next(iter(values))


def _clone_tag_attrs(xml: bytes, name: str) -> dict:
    tags = list(re.finditer(rb'<' + name.encode() + rb'\b[^>]*>', xml))
    if len(tags) > 1:
        raise SaveToolError(f'Tag {name} bị trùng')
    return {k:html.unescape(v) for k,v in parse_attributes(tags[0].group(0)).items()} if tags else {}


def _clone_patch_opening(xml: bytes, name: str, values: dict) -> bytes:
    tags = list(re.finditer(rb'<' + name.encode() + rb'\b[^>]*>', xml))
    if len(tags) != 1:
        raise SaveToolError(f'Cần đúng một tag {name}')
    m = tags[0]; tag = m.group(0)
    for key,value in values.items(): tag = replace_attribute(tag,key,str(value))
    return xml[:m.start()] + tag + xml[m.end():]


def regatta_task_inventory(xml: bytes) -> tuple:
    center = _advanced_block(xml, 'RegataCenter')
    regatta = _advanced_block(center, 'Regata')
    tasks = []
    for m in re.finditer(rb'<FreeTask\b[^>]*>', regatta, re.I):
        attrs = parse_attributes(m.group(0)); task_id = html.unescape(attrs.get('id', ''))
        if not task_id: continue
        target = task_id[7:] if task_id.lower().startswith('match3_') else task_id
        target = re.sub(r'_\d+$', '', target)
        if target:
            tasks.append({'id':task_id,'target':target,'num':html.unescape(attrs.get('num','1')),
                          'ver':html.unescape(attrs.get('ver','1'))})
    # APK comparator places Match3 first, keeping the order within each group.
    tasks.sort(key=lambda item:not item['id'].lower().startswith('match3_'))
    old = len(list(re.finditer(rb'<MyOldTask\b',regatta)))
    return center,regatta,tasks,old


def set_regatta_tasks(xml: bytes, count: int, now: int | None = None) -> bytes:
    _advanced_integer(count,'Số nhiệm vụ',10000)
    center,regatta,tasks,_ = regatta_task_inventory(xml)
    if not tasks:
        raise SaveToolError('Regatta chưa có FreeTask làm mẫu; hãy tải save có nhiệm vụ')
    city_id = _clone_field_value(_advanced_block(xml,'Global'),'cityId')
    if not city_id: raise SaveToolError('Thiếu cityId trong Global')
    now = int(time.time()) if now is None else now
    regatta = re.sub(rb'<MyOldTask\b[^>]*?/\s*>\s*|<MyOldTask\b[^>]*>.*?</MyOldTask\s*>\s*',b'',regatta,flags=re.S|re.I)
    generated = []
    for n in range(count):
        task = tasks[n % len(tasks)]
        values = dict(id=task['id'], type='event_order', eventType='Match3',target=task['target'],
                      user=city_id,num=task['num'],ver=task['ver'],takenCounter=str(n+1),score='150',realEndTime=str(now))
        tag = b'<MyOldTask/>'
        for k,v in values.items(): tag = replace_attribute(tag,k,v)
        generated.append(tag)
    # qx3.t inserts the records immediately before Regata/Vars.
    vars_open = re.search(rb'<Vars\b[^>]*>',regatta)
    if vars_open is None: raise SaveToolError('Regata thiếu Vars để ghi nhiệm vụ')
    regatta = regatta[:vars_open.start()] + b'\n'.join(generated) + b'\n' + regatta[vars_open.start():]
    regatta = re.sub(rb'<Vars\b([^>]*)/\s*>',rb'<Vars\1></Vars>',regatta)
    for name in ('TakingTask','visited','HaveTeamList'):
        regatta = _m3_upsert_field(regatta,name,'0','b','Vars')
    center = _decor_replace_block(center,'Regata',regatta)
    result = _decor_replace_block(xml,'RegataCenter',center)
    validate_xml_document(result,'Regatta task')
    return result


def fix_tutorial_categories(xml: bytes, categories: Iterable[str]) -> bytes:
    categories = list(dict.fromkeys(categories))
    if not categories or set(categories) - TSVIP_TUTORIAL_FIXES.keys():
        raise SaveToolError('Chọn nhóm tutorial trong danh sách TSVIP')
    block = _advanced_block(xml,'Global') if _decor_block(xml,'Global') else b'<Global></Global>'
    for category in categories:
        for name,template in TSVIP_TUTORIAL_FIXES[category]['fields'].items():
            matches = _level_field_tags(block,name)
            if len(matches)>1: raise SaveToolError(f'Tutorial {name} bị trùng')
            tag = template.encode()
            if matches:
                m = matches[0]
                block = block[:m.start()] + tag + block[m.end():]
            else:
                block = block.replace(b'</Global>',b'    '+tag+b'\n</Global>')
    result = _decor_replace_block(xml,'Global',block)
    validate_xml_document(result,'Fix tutorial')
    return result


def _clone_remove_fields(xml: bytes, names: Iterable[str]) -> bytes:
    names = set(names)
    for match in reversed(list(re.finditer(rb'<(?:Var|DataElem)\b[^>]*?/\s*>',xml))):
        if parse_attributes(match.group(0)).get('name') in names:
            xml = xml[:match.start()] + xml[match.end():]
    return xml


def _clone_optional_block(target: bytes, donor: bytes, name: str, report: list) -> bytes:
    span = _clone_optional_root_span(donor,name)
    if span is None:
        report.append(f'Bỏ qua {name}: donor chưa có');return target
    result = _clone_upsert_root_block(target,name,donor[span.start:span.end])
    report.append(name)
    return result


def _clone_copy_profile_field(target: bytes, donor: bytes, name: str) -> bytes:
    donor_tags = [m for m in _level_field_tags(donor,name) if m.group(0).startswith(b'<DataElem')]
    if not donor_tags: return target
    if len(donor_tags)!=1: raise SaveToolError(f'Donor {name} bị trùng')
    target_tags = [m for m in _level_field_tags(target,name) if m.group(0).startswith(b'<DataElem')]
    if len(target_tags)>1: raise SaveToolError(f'Target {name} bị trùng')
    if target_tags:
        m = target_tags[0];return target[:m.start()]+donor_tags[0].group(0)+target[m.end():]
    anchors = [m for m in _level_field_tags(target,'UnlockedAvatars') if m.group(0).startswith(b'<DataElem')]
    if len(anchors)!=1: raise SaveToolError(f'Thiếu vị trí Profile/UnlockedAvatars để thêm {name}')
    pos = anchors[0].start()
    return target[:pos]+donor_tags[0].group(0)+b'\n'+target[pos:]


def clone_city_v1(target: bytes, donor: bytes, options: Iterable[str]) -> tuple[bytes,list]:
    options = set(options)
    allowed = {'stats','zoo','city','airscore','skins','decor','stickers','badges','titles','frames','styles','avatars','ccsecrets'}
    if not options or options - allowed: raise SaveToolError('Tùy chọn Clone v1 không hợp lệ')
    validate_xml_document(target,'Target');validate_xml_document(donor,'Donor')
    report = []
    if 'city' in options:
        donor_tg = get_direct_child_block(donor,'TownGround')
        target_id = _clone_field_value(target,'cityId');donor_id = _clone_field_value(donor,'cityId')
        def rewrite_users(block):
            if not target_id or not donor_id or target_id==donor_id:return block
            return re.sub(rb'<[A-Za-z_][\w:.-]*\b[^>]*>',lambda m:replace_attribute(m.group(0),'user',target_id)
                          if html.unescape(parse_attributes(m.group(0)).get('user',''))==donor_id else m.group(0),block)
        donor_tg = rewrite_users(donor_tg)
        target = replace_direct_child_block(target,'TownGround',donor_tg)
        # Some saves place Buildings inside TownGround; others use a sibling.
        donor_buildings = _clone_optional_root_span(donor,'Buildings')
        target_buildings = _clone_optional_root_span(target,'Buildings')
        if donor_buildings:
            block = rewrite_users(donor[donor_buildings.start:donor_buildings.end])
            target = _clone_upsert_root_block(target,'Buildings',block)
        elif ET.fromstring(donor_tg).find('Buildings') is not None:
            if target_buildings:target=target[:target_buildings.start]+target[target_buildings.end:]
        else:raise SaveToolError('Donor không có Buildings trong City')
        report.extend(['TownGround','Buildings (City)'])
    if 'zoo' in options:
        for name in ('Zoo','ZooInfo','ZooQuests'):target=_clone_optional_block(target,donor,name,report)
    if 'stats' in options:
        donor_global = _advanced_block(donor,'Global')
        selected = {}
        for match in re.finditer(rb'<Var\b[^>]*?/\s*>',donor_global):
            attrs=parse_attributes(match.group(0));name=attrs.get('name','')
            if name in TSVIP_CLONE_STAT_FIELDS or name.lower().startswith(tuple(p.lower() for p in TSVIP_CLONE_STAT_PREFIXES)) or ('airscore' in options and name=='AirScore'):
                if name in selected:raise SaveToolError(f'Donor Var {name} bị trùng')
                selected[name]=match.group(0)
        block=_advanced_block(target,'Global')
        for name,tag in selected.items():
            matches=_level_field_tags(block,name)
            if len(matches)>1:raise SaveToolError(f'Target Var {name} bị trùng')
            if name=='WareHouseCashUpgrade':
                value=min(parse_int(parse_attributes(tag).get('v','0'),name,0,2_147_483_647),238)
                tag=replace_attribute(tag,'v',str(value))
            if matches:
                m=matches[0];block=block[:m.start()]+tag+block[m.end():]
            else:block=block.replace(b'</Global>',tag+b'\n</Global>')
        target=_decor_replace_block(target,'Global',block)
        # Keep the Barn duplicate consistent after TSVIP's cap at 238.
        if 'WareHouseCashUpgrade' in selected:
            level=int(_clone_field_value(target,'WareHouseCashUpgrade','0'))
            target=_advanced_field(target,'WHUdup',str((level^514698188)&0xffffffff))
        for group in TSVIP_CLONE_STAT_GROUPS:
            values=[_clone_field_value(donor,name) for name in group]
            value=next((v for v in values if v!=''),None)
            if value is not None:
                for name in group:target=_advanced_field(target,name,value)
        for name in ('M3Ch_mainM3','m3_comp_lvls'):
            value=_clone_field_value(donor,name)
            if value:
                # M3 counters also live in Minigame Vars, beyond Global.
                target=re.sub(rb'<(?:Var|DataElem)\b[^>]*>',lambda m:replace_attribute(m.group(0),'value' if 'value' in parse_attributes(m.group(0)) else 'v',value)
                              if parse_attributes(m.group(0)).get('name')==name else m.group(0),target)
        if 'airscore' in options:target=_clone_optional_block(target,donor,'AirInfo',report)
        target=_clone_optional_block(target,donor,'ArtInfo',report)
        report.append(f'Stats: {len(selected)} Var và {len(TSVIP_CLONE_STAT_GROUPS)} nhóm alias')
    for key,name in [('skins','Skins'),('decor','BuildingsStash'),('stickers','FragmentedBeautyManager')]:
        if key in options:target=_clone_optional_block(target,donor,name,report)
    for key,name in [('badges','UnlockedBadges'),('titles','UnlockedExpRanks'),('frames','UnlockedFrames'),('styles','UnlockedStyles')]:
        if key in options:target=_clone_copy_profile_field(target,donor,name);report.append(name)
    if 'avatars' in options:
        for m in re.finditer(rb'<Var\b[^>]*?/\s*>',donor):
            attrs=parse_attributes(m.group(0));name=attrs.get('name','')
            if re.fullmatch(r'Unlocked_ava\d+',name):target=_advanced_field(target,name,attrs.get('v','0'),'b')
        report.append('Avatar flags')
    if 'ccsecrets' in options:
        target=_clone_remove_fields(target,['CCSecretM','CCSecretApps','CCSecretB','CCSecretInstall']);report.append('Xóa CCSecret')
    validate_xml_document(target,'Clone City v1')
    return target,report


TSVIP_V3_LOCAL_TEMPLATE = b'<root><Version version="" FVer="" timestamp="" gameId=""/><AWS cityId="" token=""/><Friends updated="0.0000000000000000"/><FollowedFriends/><Followers/><RandomFriends remain_time="17926.0000000000000000" end_time="" dirty="1"/><LastRandomFriends/><LastHelpers/><ClanMembers/><NewFriends/><PushNotifDeviceInfo abtests="" advId="" bver="" cityId="" deviceToken="" deviceType="" fver="" gameId="" geoip="" lang="" location="" lvl="" model="" osver="" platform="g" pname="" tz="" timestamp=""/><Minigames/></root>'


def clone_city_v3(target: bytes, donor: bytes, old_local: bytes, remove_secrets: bool = True,
                  keep_airscore: bool = False) -> tuple[bytes,bytes,list]:
    validate_xml_document(target,'Target');validate_xml_document(donor,'Donor');validate_xml_document(old_local,'LocalInfo')
    aws=_clone_tag_attrs(old_local,'AWS');push=_clone_tag_attrs(old_local,'PushNotifDeviceInfo');version=_clone_tag_attrs(old_local,'Version')
    city_id=aws.get('cityId') or push.get('cityId','')
    game_id=version.get('gameId') or push.get('gameId','')
    timestamp=version.get('timestamp') or push.get('timestamp','0')
    if not city_id or not game_id:raise SaveToolError('Clone v3 cần cityId/gameId tài khoản hiện tại trong LocalInfo')
    bver=_clone_field_value(donor,'Version','38.1.1');fver=_clone_field_value(donor,'FVer','3810')
    local=TSVIP_V3_LOCAL_TEMPLATE
    local=_clone_patch_opening(local,'Version',{'version':bver,'FVer':fver,'timestamp':timestamp,'gameId':game_id})
    local=_clone_patch_opening(local,'AWS',{'cityId':city_id,'token':aws.get('token','')})
    try:end_time=str(float(timestamp)+17926.0) if float(timestamp)>0 else ''
    except ValueError:raise SaveToolError('LocalInfo timestamp không hợp lệ')
    local=_clone_patch_opening(local,'RandomFriends',{'end_time':end_time})
    groups=[]
    for m in _level_field_tags(donor,'group'):
        attrs=parse_attributes(m.group(0));value=html.unescape(attrs.get('value',''))
        if value.startswith(('ts_ios_gp_old_','ts_gp_new_')):
            groups.append(value.rsplit('_',1)[0]+':'+value)
    data={'abtests':'|'.join(dict.fromkeys(groups)),'advId':push.get('advId',''),'bver':bver,'cityId':city_id,
          'deviceToken':push.get('deviceToken',''),'deviceType':push.get('deviceType',''),'fver':fver,'gameId':game_id,
          'geoip':_clone_field_value(donor,'GeoIp','BD'),'lang':_clone_field_value(donor,'DeviceLang','en'),
          'location':_clone_field_value(donor,'Country','US'),'lvl':_clone_field_value(donor,'levelup','3'),
          'model':_clone_field_value(donor,'Device'),'osver':_clone_field_value(donor,'OS'),'platform':'g',
          'pname':_clone_field_value(donor,'townName'),'tz':_clone_field_value(donor,'currencyStatDelay','21600'),'timestamp':timestamp}
    local=_clone_patch_opening(local,'PushNotifDeviceInfo',data)
    mini_ids=list(dict.fromkeys(html.unescape(parse_attributes(m.group(0)).get('id','')) for m in re.finditer(rb'<Minigame\b[^>]*>',donor)))
    if mini_ids:
        minis=b'<Minigames>'+b''.join(('<Minigame id="'+xml_escape_attribute(i)+'"><LocalVars/></Minigame>').encode() for i in mini_ids if i)+b'</Minigames>'
        local=_decor_replace_block(local,'Minigames',minis)
    # V3 uses the entire donor save, retaining account identity from old LocalInfo.
    result=donor
    replacements={}
    for field,value in [('gameId',game_id),('cityId',city_id)]:
        old=_clone_field_value(donor,field)
        if old and value:replacements[old]=value
    donor_adv=_clone_field_value(donor,'advId');own_adv=push.get('advId','')
    if donor_adv and own_adv:
        replacements['-'.join(donor_adv.split('-')[:3])]='-'.join(own_adv.split('-')[:3])
    promo=_clone_field_value(donor,'PromoCode');own_promo=_clone_field_value(target,'PromoCode')
    if promo and own_promo:replacements[promo]=own_promo
    # Simultaneous substitution avoids chaining colliding identity values.
    replacements={xml_escape_attribute(k).encode():xml_escape_attribute(v).encode() for k,v in replacements.items() if k!=v}
    if replacements:
        pattern=re.compile(b'|'.join(re.escape(k) for k in sorted(replacements,key=len,reverse=True)))
        result=re.sub(rb'([\"\'])(.*?)\1', lambda a:a.group(1)+pattern.sub(lambda m:replacements[m.group(0)],a.group(2))+a.group(1),result,flags=re.S)
    # A save timestamp is not an identity token. Other fields (factoryTime,
    # timers, etc.) can have the same value, and must retain donor values.
    save_time_tags=_level_field_tags(result,'saveGlobalTime')
    if len(save_time_tags)>1:raise SaveToolError('Donor có saveGlobalTime trùng; không áp dụng V3')
    if save_time_tags:
        match=save_time_tags[0];attrs=parse_attributes(match.group(0))
        attribute='value' if 'value' in attrs else 'v'
        result=result[:match.start()]+replace_attribute(match.group(0),attribute,timestamp)+result[match.end():]
    for name in ('reportProgressLogSeqTeamId','teamId'):
        result=re.sub(rb'<DataElem\b[^>]*>',lambda m:replace_attribute(m.group(0),'value','') if parse_attributes(m.group(0)).get('name')==name else m.group(0),result)
    if _decor_block(result,'RegataCenter'):
        result=_decor_replace_block(result,'RegataCenter',b'<RegataCenter version="-1" clanId="" partedRegataIds=""><GeneratedSeasonStoreItems/></RegataCenter>')
    clan=re.search(rb'<MyClan\b.*?(?:</LastHelperIds\s*>|<LastHelperIds\s*/>)',result,re.S)
    if clan:
        blank=b'<MyClan id="" leaderId="" name="" desc="" geoip="" reqLevel="19" rActivity="0" type="0" lang="en" mCount="0" tag="" regataType="0" regataBType="0" flagSym="0" flagBack="0" flagPat="0" flagCol="0" league="0" flagCountry="1" flagViewType="0" canRestore="0"/><ChatLivesInbox/><FriendIds/><FollowedFriendIds/><FollowerIds/><NewFollowerIds/><InvitedFriends/><LastHelperIds/>'
        result=result[:clan.start()]+blank+result[clan.end():]
    elif _decor_block(result,'MyClan'):
        # A compact save may omit the adjacent LastHelperIds. Reset just its clan block.
        result=_decor_replace_block(result,'MyClan',b'<MyClan id="" leaderId="" name=""/>')
    result=_clone_remove_fields(result,['MyClanId'])
    if not keep_airscore:
        result=re.sub(rb'<Var\b[^>]*>',lambda m:replace_attribute(m.group(0),'v','0') if parse_attributes(m.group(0)).get('name','').startswith('AirScore') else m.group(0),result)
    if remove_secrets:result=_clone_remove_fields(result,['CCSecretM','CCSecretApps','CCSecretB','CCSecretInstall'])
    validate_xml_document(result,'Clone v3 mGameInfo');validate_xml_document(local,'Clone v3 LocalInfo')
    return result,local,['Toàn bộ donor mGameInfo','Giữ cityId/gameId/token/thiết bị của tài khoản hiện tại',
                         'Tạo lại LocalInfo, xóa danh sách bạn/clan cũ','Reset Regata/team/clan của donor',
                         'Giữ PromoCode của target', 'AirScore giữ' if keep_airscore else 'AirScore = 0']


def send_card_defaults(xml: bytes, local: bytes | None) -> dict:
    meta=parse_localinfo_metadata(local)[0] if local else {}
    result={'sender':meta.get('own_city_id') or _clone_field_value(xml,'cityId'),
            'token':meta.get('token',''),'bver':meta.get('version') or _clone_field_value(xml,'Version','35.1.0'),
            'fver':meta.get('fver') or _clone_field_value(xml,'FVer','3510'),
            'name':_clone_field_value(xml,'townName'),'pic':_clone_field_value(xml,'MyPicture'),
            'collection':'','end_time':''}
    for m in _level_field_tags(xml,'configId'):
        attrs=parse_attributes(m.group(0));value=html.unescape(attrs.get('value',''))
        found=re.fullmatch(r'CardCollections_(\d+)',value)
        if found:
            endings=_level_field_tags(xml[m.end():m.end()+1000],'endTime')
            if endings:
                result['collection']=found[1]
                result['end_time']=parse_attributes(endings[0].group(0)).get('value','')
                break
    return result


def prepare_send_card(sender: str, recipient: str, card_number: int, collection: str,
                       end_time: int, send_counter: int, token: str, name: str = '', pic: str = '',
                       bver: str = '35.1.0', fver: str = '3510', master_key: bytes | None = None,
                       iv: bytes | None = None, seed: str | None = None) -> PreparedRequest:
    for value,label in [(sender,'Sender'),(recipient,'Recipient')]:
        if not re.fullmatch(r'[A-Za-z0-9_-]+',value):raise SaveToolError(f'{label} City ID không hợp lệ')
    if sender==recipient:raise SaveToolError('Sender và Recipient phải khác nhau')
    if type(card_number) is not int or not 1<=card_number<=160:raise SaveToolError('Số card phải từ 1 đến 160')
    for value,label in [(end_time,'col_et'),(send_counter,'sendCounter')]:_advanced_integer(value,label,9_223_372_036_854_775_807)
    if not collection or not token:raise SaveToolError('Send card cần col_id và ts-token hiện tại')
    if master_key is None or len(master_key) not in (16,24,32):
        raise SaveToolError('Send card cần master AES key hợp lệ do TSVIP cấp; FetchCity key không được tự coi là SendBox key')
    if any('\n' in v or '\r' in v for v in (token,bver,fver)):raise SaveToolError('HTTP header không hợp lệ')
    box={'afg':3,'box_type':'collections_send_card','card_id':f'card_{card_number:02d}',
         'col_et':end_time,'col_id':collection,'friend_type':'send_friend',
         'from':{'city_id':sender,'friend_city_name':name,'pic':pic},
         'seed':seed if seed is not None else str(struct.unpack('<q',os.urandom(8))[0]),
         'sendCounter':send_counter,'set_id':f'set_{(card_number-1)//10+1:02d}','to':recipient,'type':'box'}
    body_json=json.dumps({'box':json.dumps(box,ensure_ascii=False,separators=(',',':')),'cityId':sender,'to_cityId':recipient},ensure_ascii=False,separators=(',',':'))
    iv=os.urandom(12) if iv is None else iv
    if len(iv)!=12:raise SaveToolError('SendBox IV phải 12 byte')
    encrypted=AESGCM(master_key).encrypt(iv,gzip.compress(body_json.encode(),mtime=0),None)
    ciphertext,tag=encrypted[:-16],encrypted[-16:]
    headers={'Accept-Encoding':'identity','Content-Type':'application/octet-stream','IsNewClanUIEnabled':'true',
             'User-Agent':f'Township/{bver} (Android 13)','ts-bp':'g','ts-bver':bver,'ts-fver':fver,
             'ts-gpid':'new','ts-id':'002'+iv.hex()+tag.hex(),'ts-token':token,'x-version':bver}
    return PreparedRequest('https://township.playrix.com/api/1/SendBox?cityId='+quote(sender,safe=''),headers,ciphertext,body_json)


def send_card_live(prepared: PreparedRequest, master_key: bytes) -> dict:
    try:
        response=requests.post(prepared.url,headers=prepared.headers,data=prepared.body,timeout=(15,30),allow_redirects=False)
    except requests.RequestException as exc:
        # Do not retry: the server may have accepted the card before a timeout.
        raise SaveToolError('SendBox lỗi kết nối; trạng thái gửi chưa rõ, kiểm tra trong game trước khi gửi lại') from exc
    if not 200<=response.status_code<300:
        raise SaveToolError(f'SendBox HTTP {response.status_code}: '+response.content[:150].decode('utf-8','replace'))
    raw=response.content;tsid=response.headers.get('ts-id','')
    if tsid:
        if len(tsid)!=59 or not tsid.startswith('002'):raise SaveToolError('Phản hồi SendBox có ts-id không hợp lệ')
        try:raw=AESGCM(master_key).decrypt(bytes.fromhex(tsid[3:27]),raw+bytes.fromhex(tsid[27:59]),None)
        except Exception as exc:raise SaveToolError('SendBox HTTP thành công nhưng không xác thực được phản hồi; kiểm tra trong game') from exc
    try:raw=gzip.decompress(raw)
    except (OSError,EOFError):pass
    if not raw: return {'http':response.status_code,'status':'HTTP accepted','verified':False}
    try:result=json.loads(raw)
    except ValueError:return {'http':response.status_code,'status':'HTTP accepted','verified':False,'response':raw.decode('utf-8','replace')[:150]}
    if isinstance(result,dict):
        if result.get('error') or result.get('ok') is False or result.get('success') is False:
            raise SaveToolError('SendBox bị server từ chối: '+str(result.get('error') or result.get('message') or result)[:150])
        return {'http':response.status_code,'status':'Server response','verified':True,'response':result}
    return {'http':response.status_code,'status':'HTTP accepted','verified':False,'response':result}


def _clone_choose_donor() -> bytes | None:
    print('\nNguồn donor: 1. Donor đã tải  2. File XML/save local  3. City ID (FetchCity)  4. Bạn bè LocalInfo  0. Hủy')
    choice=input('Chọn: ').strip()
    if choice=='0':return None
    if choice=='1':
        donor=SESSION.donor_xml
        if donor is None and DONOR_FILE.is_file():donor=load_friend_donor(DONOR_FILE)
        if donor is None:raise SaveToolError('Chưa có donor')
    elif choice=='2':
        path=Path(input('Đường dẫn donor: ').strip().strip('"'))
        donor=load_friend_donor(path);SESSION.donor_path=path
    elif choice in ('3','4'):
        if choice=='4':
            if not SESSION.friends:raise SaveToolError('Chưa có danh sách bạn bè; tải LocalInfo trước')
            items=sorted(SESSION.friends.values(),key=friend_sort_key);display_friend_table(items)
            index=parse_int(input('STT bạn (0 = hủy): ').strip(),'STT',0,len(items))
            if not index:return None
            city_id=items[index-1].city_id
        else:city_id=input('City ID donor: ').strip()
        if not re.fullmatch(r'[A-Za-z0-9_-]+',city_id):raise SaveToolError('City ID không hợp lệ')
        meta=SESSION.localinfo_meta or {}
        bver=input(f'bver [{meta.get("version") or "38.1.1"}]: ').strip() or meta.get('version') or '38.1.1'
        fver=input(f'fver [{meta.get("fver") or "3810"}]: ').strip() or meta.get('fver') or '3810'
        donor,_,_=fetch_city_live(city_id,bver,fver,0)
        SESSION.donor_path=FRIENDS_DIR/city_id/'friend_city.xml'
    else:raise SaveToolError('Lựa chọn donor không hợp lệ')
    SESSION.donor_xml=donor
    return donor


def regatta_tasks_prompt() -> None:
    SESSION.require_loaded()
    _,_,tasks,old=regatta_task_inventory(SESSION.current_xml)
    print(f'\nRegatta task: {len(tasks)} FreeTask, {old} MyOldTask hiện có.')
    for task in tasks:print(task)
    print('Đặt lại danh sách nhiệm vụ đã hoàn thành, 150 điểm/mục, ưu tiên Match3 theo TSVIP.')
    raw=input('Số MyOldTask mới (0..10000; trống = hủy): ').strip()
    if not raw:return
    count=parse_int(raw,'Số nhiệm vụ',0,10000)
    _advanced_apply(set_regatta_tasks(SESSION.current_xml,count),f'Regatta task: {count} mục')


def tutorial_fix_prompt() -> None:
    SESSION.require_loaded()
    ids=list(TSVIP_TUTORIAL_FIXES)
    print('\nFix tutorial bug (9 nhóm từ TSVIP):')
    for n,key in enumerate(ids,1):print(f'{n}. {TSVIP_TUTORIAL_FIXES[key]["label"]} ({len(TSVIP_TUTORIAL_FIXES[key]["fields"])} cờ)')
    selected=_advanced_select(ids)
    if selected:_advanced_apply(fix_tutorial_categories(SESSION.current_xml,selected),f'Fix tutorial: {len(selected)} nhóm')


def clone_city_v1_prompt() -> None:
    SESSION.require_loaded();donor=_clone_choose_donor()
    if donor is None:return
    options={'city':'City','zoo':'Zoo/ZooInfo/ZooQuests','stats':'Stats/level/kho/M3',
             'airscore':'AirScore/AirInfo','skins':'Skins','decor':'Decoration stash',
             'stickers':'FragmentedBeautyManager (mục Stickers của Clone TSVIP)',
             'badges':'Huy hiệu','titles':'Danh hiệu','frames':'Khung','styles':'Phong cách','avatars':'Avatar','ccsecrets':'Xóa CCSecret'}
    print('\nClone City v1 — chọn phần cần sao chép:')
    for n,(key,label) in enumerate(options.items(),1):print(f'{n:2}. {label}')
    selected=_advanced_select(options)
    if not selected:return
    result,report=clone_city_v1(SESSION.current_xml,donor,selected)
    print('Thay đổi:', '; '.join(report))
    print('City ID tài khoản:',_clone_field_value(SESSION.current_xml,'cityId'))
    _advanced_apply(result,'Clone City v1')


def clone_city_v3_prompt() -> None:
    SESSION.require_loaded()
    if SESSION.localinfo_xml is None:raise SaveToolError('Clone v3 cần LocalInfo tài khoản hiện tại; tải cùng save hoặc mở file LocalInfo')
    donor=_clone_choose_donor()
    if donor is None:return
    remove=ask_yes_no('Xóa CCSecret của donor?',default=True)
    keep=ask_yes_no('Giữ AirScore/AirInfo của donor?',default=False)
    game,local,report=clone_city_v3(SESSION.current_xml,donor,SESSION.localinfo_xml,remove,keep)
    print('\nClone v3:', '; '.join(report))
    print('Sẽ thay cả mGameInfo và LocalInfo; tài khoản:',(SESSION.localinfo_meta or {}).get('own_city_id',''))
    if not ask_yes_no('Áp dụng Clone v3 vào hai XML đang chỉnh sửa?',default=False):return
    apply_clone_v3_session(game,local)
    print('Đã chuẩn bị hai XML. Chọn 50 để xuất/verify cả hai, hoặc 51 để ghi game.')


def send_card_prompt() -> None:
    SESSION.require_loaded()
    defaults=send_card_defaults(SESSION.current_xml,SESSION.localinfo_xml)
    print('\nSend card: gửi qua SendBox API, không cần encode mGameInfo.')
    sender=input(f'Sender City ID [{defaults["sender"]}]: ').strip() or defaults['sender']
    recipients=[]
    if SESSION.friends:
        items=sorted(SESSION.friends.values(),key=friend_sort_key);display_friend_table(items)
        selected=_advanced_select([f.city_id for f in items])
        recipients.extend(selected)
    raw=input('Recipient City ID thêm (phân cách dấu phẩy; trống = bỏ qua): ').strip()
    if raw:recipients.extend(v for v in re.split(r'[,;\s]+',raw) if v)
    recipients=list(dict.fromkeys(recipients))
    if not recipients:return
    print('Card 1..160: card_01..card_160; set_01..set_16, mỗi set 10 card.')
    raw=input('Số card (1,3,5-10; 0 = hủy): ').strip()
    if raw=='0':return
    cards=[int(v) for v in parse_avatar_selection(raw,[str(n) for n in range(1,161)])]
    collection=input(f'col_id [{defaults["collection"] or "bắt buộc nhập"}]: ').strip() or defaults['collection']
    end_time=parse_int(input(f'col_et Unix seconds [{defaults["end_time"] or "bắt buộc nhập"}]: ').strip() or defaults['end_time'],'col_et',1,9_223_372_036_854_775_807)
    counter=parse_int(input('sendCounter bắt đầu [1]: ').strip() or '1','sendCounter',0,2_147_483_647)
    from getpass import getpass
    token=getpass('ts-token (trống = dùng AWS token từ LocalInfo): ').strip() or defaults['token']
    print('TSVIP nhận master AES key từ server khi đăng nhập. Nhập key đó dạng hex (16/24/32 byte).')
    raw_key=getpass('Master AES key hex (trống = hủy): ').strip()
    if not raw_key:return
    try:key=bytes.fromhex(raw_key)
    except ValueError as exc:raise SaveToolError('Master AES key hex không hợp lệ') from exc
    name=input(f'Tên sender [{defaults["name"]}]: ').strip() or defaults['name']
    pic=input(f'pic [{defaults["pic"]}]: ').strip() or defaults['pic']
    prepared=[]
    for recipient in recipients:
        for card in cards:
            prepared.append(prepare_send_card(sender,recipient,card,collection,end_time,counter,token,name,pic,defaults['bver'],defaults['fver'],key))
            counter+=1
    print(f'Sẽ gửi {len(prepared)} card: sender {sender}, người nhận {", ".join(recipients)}, card {cards}, col_id {collection}, col_et {end_time}.')
    if not ask_yes_no('Xác nhận gửi card qua API?',default=False):return
    records=[]
    for request in prepared:
        payload=json.loads(request.plaintext_json);box=json.loads(payload['box'])
        try:
            result=send_card_live(request,key)
            record={'card':box['card_id'],'recipient':box['to'],'result':result}
            print(box['card_id'],'->',box['to'],result['status'], '(HTTP thành công; kiểm tra hộp thư trong game)')
        except SaveToolError as exc:
            record={'card':box['card_id'],'recipient':box['to'],'error':str(exc)}
            records.append(record);print('Dừng gửi:',exc);break
        records.append(record)
    # No auth token, AES key, or plaintext request is written to this report.
    path=WORK_DIR/f'send_card_{datetime.now().strftime("%Y%m%d_%H%M%S")}_{uuid.uuid4().hex[:8]}.json'
    atomic_write(path,json.dumps(records,ensure_ascii=False,indent=2).encode())
    print('Kết quả:',path)

CLONE_LOCAL_OUTPUT = WORK_DIR / 'LocalInfo_output.xml'
CLONE_LOCAL_MODIFIED = WORK_DIR / 'LocalInfo_modified.xml'


def _clone_optional_root_span(xml: bytes, name: str) -> XmlElementSpan | None:
    matches=[span for span in direct_child_spans(xml) if span.tag==name]
    if len(matches)>1:raise SaveToolError(f'Tag root/{name} bị trùng')
    return matches[0] if matches else None


def _clone_upsert_root_block(xml: bytes, name: str, block: bytes) -> bytes:
    span = _clone_optional_root_span(xml, name)
    if span:
        return xml[:span.start]+block+xml[span.end:]
    closing = list(re.finditer(rb'</root\s*>',xml))
    if len(closing)!=1: raise SaveToolError('Thiếu thẻ đóng root')
    pos=closing[0].start()
    return xml[:pos]+block+b'\n'+xml[pos:]


def apply_clone_v3_session(game: bytes, local: bytes) -> None:
    SESSION.require_loaded()
    if SESSION.localinfo_container is None: raise SaveToolError('Thiếu container LocalInfo gốc')
    # Verify both containers before accepting either XML into the session.
    for xml,template in [(game,SESSION.original_container),(local,SESSION.localinfo_container)]:
        if decode_save(encode_save(xml,template))!=canonical_xml(xml):
            raise SaveToolError('Clone v3 encode/decode không khớp')
    atomic_write(CLONE_LOCAL_MODIFIED,local)
    SESSION.pending_pair_templates=None
    SESSION.apply_xml(game)
    SESSION.pending_localinfo_xml=local


def encode_pending_localinfo() -> bytes:
    if SESSION.pending_localinfo_xml is None or SESSION.localinfo_container is None:
        raise SaveToolError('Không có LocalInfo Clone v3 đang chờ')
    template=SESSION.pending_pair_templates[1] if SESSION.pending_pair_templates is not None else SESSION.localinfo_container
    encoded=encode_save(SESSION.pending_localinfo_xml,template)
    if decode_save(encoded)!=canonical_xml(SESSION.pending_localinfo_xml):
        raise SaveToolError('LocalInfo encode/decode không khớp')
    atomic_write(CLONE_LOCAL_OUTPUT,encoded)
    return encoded


def _clone_read_remote(remote: str, label: str) -> bytes:
    temporary='/data/local/tmp/ts_pair_'+uuid.uuid4().hex+'.bin'
    local=WORK_DIR/('pair_readback_'+label+'.bin')
    try:
        root_shell(f'cp {shell_quote(remote)} {shell_quote(temporary)} && chmod 0644 {shell_quote(temporary)}')
        adb('pull',temporary,str(local),timeout=120)
        return local.read_bytes()
    finally:
        root_shell(f'rm -f {shell_quote(temporary)}',check=False)


def write_clone_pair_to_device(game: bytes, local: bytes) -> tuple[Path,list[str]]:
    SESSION.require_loaded()
    originals=[SESSION.original_container,SESSION.localinfo_container]
    if any(v is None for v in originals):raise SaveToolError('Thiếu hai container gốc')
    for path,original in zip([SOURCE_FILE,LOCALINFO_SOURCE_FILE],originals):
        if not path.is_file() or path.read_bytes()!=original:
            raise SaveToolError('Source game/LocalInfo đã thay đổi; tải lại cả hai trước khi ghi')
    check_device();adb_shell(f'am force-stop {shell_quote(PACKAGE_NAME)}')
    remotes=[REMOTE_SAVE,REMOTE_LOCALINFO];outputs=[OUTPUT_FILE,CLONE_LOCAL_OUTPUT]
    for remote,original,label in zip(remotes,originals,['game','local']):
        if _clone_read_remote(remote,label)!=original:
            raise SaveToolError('Save trên thiết bị khác file đã tải; tải lại cả hai trước khi ghi Clone v3')
    stamp=datetime.now().strftime('%Y%m%d_%H%M%S')+'_'+uuid.uuid4().hex[:8]
    backup_dir=BACKUP_DIR/('clone_v3_'+stamp);backup_dir.mkdir(parents=True)
    for name,original in zip(['mGameInfo.xml','LocalInfo.xml'],originals):atomic_write(backup_dir/name,original)
    uploads=['/data/local/tmp/ts_pair_'+uuid.uuid4().hex+'.bin' for _ in remotes]
    staged=[remote+'.township_simple.'+stamp+'.new' for remote in remotes]
    backups=[remote+'.township_simple.'+stamp+'.bak' for remote in remotes]
    permissions=[]
    for remote in remotes:
        parts=root_shell(f"stat -c '%u %g %a' {shell_quote(remote)}").stdout.strip().split()
        if len(parts)!=3 or any(not re.fullmatch(r'\d+',v) for v in parts):raise SaveToolError('Owner/mode không hợp lệ')
        permissions.append(parts)
    atomic_write(outputs[0],game);atomic_write(outputs[1],local)
    backups_ready=False
    try:
        for output,upload in zip(outputs,uploads):adb('push',str(output),upload,timeout=120)
        root_shell(' && '.join(f'cp -p {shell_quote(remote)} {shell_quote(backup)}' for remote,backup in zip(remotes,backups)))
        backups_ready=True
        commands=[]
        for upload,new,(uid,gid,mode) in zip(uploads,staged,permissions):
            commands.extend([f'cp {shell_quote(upload)} {shell_quote(new)}',f'chown {uid}:{gid} {shell_quote(new)}',f'chmod {mode} {shell_quote(new)}'])
        root_shell(' && '.join(commands),timeout=120)
        # Game is stopped. Two renames are sequential; any detected failure rolls both back.
        root_shell(' && '.join(f'mv -f {shell_quote(new)} {shell_quote(remote)}' for new,remote in zip(staged,remotes)),timeout=120)
        for remote,expected,label in zip(remotes,[game,local],['game','local']):
            if _clone_read_remote(remote,label)!=expected:raise SaveToolError('Readback Clone v3 không khớp')
    except Exception as exc:
        if backups_ready:
            try:
                # Run separately so failure restoring one file does not skip the other.
                failures=[]
                for remote,backup in zip(remotes,backups):
                    result=root_shell(f'cp -p {shell_quote(backup)} {shell_quote(remote)}',check=False)
                    if result.returncode:failures.append(remote)
                if failures:raise SaveToolError('Không khôi phục được: '+', '.join(failures))
                for remote,original,label in zip(remotes,originals,['game','local']):
                    if _clone_read_remote(remote,label)!=original:raise SaveToolError('Rollback readback không khớp')
            except Exception as rollback:
                raise SaveToolError(f'Ghi Clone v3 lỗi; rollback chưa xác minh: {rollback}. Backup: {backup_dir}; {backups}') from exc
            raise SaveToolError(f'Ghi Clone v3 lỗi; đã khôi phục hai file gốc. Backup: {backup_dir}') from exc
        raise
    finally:
        root_shell('rm -f '+' '.join(shell_quote(v) for v in uploads+staged),check=False)
    return backup_dir,backups


def save_clone_pair_to_device() -> None:
    game=SESSION.encode_verify();local=encode_pending_localinfo()
    backup,remote=write_clone_pair_to_device(game,local)
    SESSION.original_container=game;SESSION.original_xml=SESSION.current_xml
    SESSION.localinfo_container=local;SESSION.localinfo_xml=SESSION.pending_localinfo_xml
    SESSION.localinfo_meta,SESSION.friends=parse_localinfo_metadata(SESSION.localinfo_xml)
    SESSION.selected_friend=None;SESSION.pending_localinfo_xml=None;SESSION.pending_pair_templates=None
    atomic_write(SOURCE_FILE,game);atomic_write(DECODED_FILE,SESSION.current_xml)
    atomic_write(LOCALINFO_SOURCE_FILE,local);atomic_write(LOCALINFO_DECODED_FILE,SESSION.localinfo_xml)
    print('Đã ghi và đọc lại xác minh cả mGameInfo + LocalInfo.')
    print('Backup hai file:',backup);print('Backup trên thiết bị:',remote)


TSVIP_FRESH_TOWN_ASSET_SHA256 = '05a3f251b8d90f45c8117c1b57634b4acea6019f9bd977769885ba7310bcf9ea'
TSVIP_FRESH_TOWN_ASSET = (
    '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'
    'FdKx7Kq2kXpE9h+F6UEmzUCQr7NoSJqqQlL/Aud+qg6e1HjvVsUhtYFHthEJB2Qt1si3xkrkYaic8SXqznrvMVpGYG/TsG3i5qDY'
    'wCoSd4BSXsfQayE/nzmqb3Xo78NjDZBA9pSkP1d8p8LKTKMyzAmQosIy4LG6dJvace7Y/TNmGZNm2S6JmKJlnZa/rvSz2L87O2XF'
    'o+clWf/XV9kwNAUC6dSPoFpNswnTa5zl13BJSZySwAg+Cohnk0w8aIPScF9JZma9yGzK66N+t1fcxI7QbtOfRpJxmsMzOrv022i1'
    'wh+FasjmRiE9EwQ2mwOoa2b9Jq9vegTYOdM86mbB/SzPFgzP4sjeeBL5w9UxvB3Vrhe60OFWZenO7gKhnzEjIOSSiARuBM9vtTga'
    'IJ5SRThrjiIMWzXkh4R3mALcBmRTJwU4x5amkQiOukW4Sp1UhjDnOWegcPIcc7tLoL7HjJwCCa43MrQIxLNNBhbqMx6u8J68eywp'
    'LZQrWuceFjCHXpUIXHKuEUTRQWoq6Mb0TYsEYKUBYZWxMsGMS7YU8Mfkvh7uUUfg7oMdisdjH6wLRp3OvDvR+aJD80bspdN+FVmc'
    'VROaC2PW92IjtUv7S9qfUfFyGGXfqdTxRWoegLLEzIjpQTI6TwXNMSy05EMi30VdDaOOcu9yKI0yL+jI8jpU0HZqnzuJ6t/udNsh'
    'mmKBejW29Q4dNOmrs3U5ciKDXcvFBCpcKqf53O0U1FsT2rvfT5nmFpKGvz1zBo78U0r6R1i8Ixr4lMoueeaHCJnr9Ed1bv/DH4Jb'
    'GR7si81MnBTfMqTVd9spQ+/by6jU8QymBX7wxP+Pqc91W0Yx/TLsc+HIqfh/y3s0X4Yr1McEfIs4KiFusnFU6HyqtqsvynnJaDPF'
    'miV1Jp/NVDkVJ5wiYGimMnRc9qnu/zIIV9JweYRvLItpnHITtBEplMrK12O5XBIy5nVse6uNHdLyfGCeXU21z1SlMa56F1A7qC2d'
    '4RiqrcFCdb5c1lqDa84o4jx2pyXQ0r4Uqqn08SpSCIJdyESKL2nDKnFB4wQoIEhpHDS4v9Wntkl8iD9zB8Xf0oq63eoayacL3RHl'
    'PSpPZ4fg80BbiaaUYyVOoivgIlheSK/rVfvI339Lj5jWL++QfUqY/zC7QxeW3ASQtGXkyn/J3/Te6/2SSS+ANXHZmO8Dd1eB+UHd'
    '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'
    '2U7iL3U='
)
# TSVIP: lm0 (ZIP backup), so/us3 (history and restore), es1/vs3/qf2.p (fresh town payload).
ACCOUNT_BACKUP_DIR = WORK_DIR / 'a_TS_Files'
BACKUP_MAX_BYTES = 32 * 1024 * 1024


def backup_account_info(game_xml: bytes, local_xml: bytes) -> dict[str,str]:
    meta,_=parse_localinfo_metadata(local_xml)
    push=_clone_tag_attrs(local_xml,'PushNotifDeviceInfo')
    return {'city_id':meta.get('own_city_id') or _clone_field_value(game_xml,'cityId','UnknownID'),
            'name':push.get('pname') or _clone_field_value(game_xml,'townName','GuestUser'),
            'level':_clone_field_value(game_xml,'levelup','0'),
            'version':meta.get('version',''),'fver':meta.get('fver','')}


def _backup_safe_component(value: str) -> str:
    value=re.sub(r'[\\/:*?"<>|\x00-\x1f]','',value).strip(' .')[:100]
    return value if value and value not in ('.','..') else 'Unknown'


def create_account_backup(game: bytes, local: bytes, directory: Path | None = None, label: str = '') -> Path:
    game_xml=decode_save(game);local_xml=decode_save(local)
    validate_xml_document(game_xml,'Backup mGameInfo');validate_xml_document(local_xml,'Backup LocalInfo')
    info=backup_account_info(game_xml,local_xml)
    folder=(directory or ACCOUNT_BACKUP_DIR)/(_backup_safe_component(info['name'])+'_'+_backup_safe_component(info['city_id']))
    folder.mkdir(parents=True,exist_ok=True)
    # Preserve TSVIP's level/date prefix and add time/nonce to avoid overwriting today's backup.
    stamp=datetime.now().strftime('%d-%m-%Y_%H%M%S')
    path=folder/f'lvl_{_backup_safe_component(info["level"])}_date_{stamp}_{uuid.uuid4().hex[:8]}.zip'
    doc=(f'# TS Vip Backup Info\n\nBackup Date: {datetime.now().isoformat(timespec="seconds")}\n'
         f'City ID: {info["city_id"]}\nCity Name: {info["name"]}\nLevel: {info["level"]}\n'
         f'Version: {info["version"]}\nFVer: {info["fver"]}\nSource: {label}\n\n'
         f'SHA256 mGameInfo.xml: {sha256_bytes(game)}\nSHA256 LocalInfo.xml: {sha256_bytes(local)}\n')
    stream=io.BytesIO()
    with zipfile.ZipFile(stream,'w',zipfile.ZIP_DEFLATED) as archive:
        archive.writestr('LocalInfo.xml',local)
        archive.writestr('mGameInfo.xml',game)
        archive.writestr('read_info.md',doc.encode())
    result=stream.getvalue()
    verified_game,verified_local,_,_=read_account_backup_bytes(result)
    if (verified_game,verified_local)!=(game,local):raise SaveToolError('ZIP backup không khớp hai file gốc')
    atomic_write(path,result)
    return path


def read_account_backup_bytes(raw: bytes) -> tuple[bytes,bytes,dict,str]:
    if len(raw)>2*BACKUP_MAX_BYTES:raise SaveToolError('ZIP quá lớn')
    try:
        with zipfile.ZipFile(io.BytesIO(raw)) as archive:
            entries=archive.infolist();names=[v.filename for v in entries]
            if len(entries)>64 or len(names)!=len(set(names)):raise SaveToolError('ZIP có quá nhiều file hoặc tên bị trùng')
            if any(v.file_size>BACKUP_MAX_BYTES for v in entries) or sum(v.file_size for v in entries)>2*BACKUP_MAX_BYTES:
                raise SaveToolError('ZIP giải nén quá lớn')
            if any(name.startswith(('/', '\\')) or '\\' in name or '..' in name.split('/') for name in names):
                raise SaveToolError('ZIP có đường dẫn không hợp lệ')
            if not {'LocalInfo.xml','mGameInfo.xml'}<=set(names):raise SaveToolError('ZIP phải có LocalInfo.xml và mGameInfo.xml ở thư mục gốc')
            game=archive.read('mGameInfo.xml');local=archive.read('LocalInfo.xml')
            if 'read_info.md' in names:
                if archive.getinfo('read_info.md').file_size>1024*1024:raise SaveToolError('read_info.md quá lớn')
                doc=archive.read('read_info.md').decode('utf-8','replace')
            else:doc=''
    except (zipfile.BadZipFile,RuntimeError,EOFError,OSError,ValueError,zlib.error) as exc:
        raise SaveToolError('Không đọc được ZIP backup: '+str(exc)) from exc
    gx=decode_save(game);lx=decode_save(local)
    validate_xml_document(gx,'Backup mGameInfo');validate_xml_document(lx,'Backup LocalInfo')
    for name,data in [('mGameInfo.xml',game),('LocalInfo.xml',local)]:
        checks=re.findall(r'^SHA256 '+re.escape(name)+r': ([0-9a-fA-F]{64})\s*$',doc,re.M)
        if checks and (len(checks)!=1 or checks[0].lower()!=sha256_bytes(data)):
            raise SaveToolError(f'SHA256 backup {name} không khớp')
    return game,local,backup_account_info(gx,lx),doc


def read_account_backup(path: Path) -> tuple[bytes,bytes,dict,str]:
    if not path.is_file():raise SaveToolError(f'Không tìm thấy ZIP: {path}')
    if path.stat().st_size>2*BACKUP_MAX_BYTES:raise SaveToolError('ZIP quá lớn')
    return read_account_backup_bytes(path.read_bytes())


def current_account_containers(edited: bool = False) -> tuple[bytes,bytes]:
    SESSION.require_loaded()
    if SESSION.localinfo_container is None or SESSION.localinfo_xml is None:
        raise SaveToolError('Cần tải cả mGameInfo và LocalInfo (mục 1 hoặc mở LocalInfo mục 44)')
    if not edited:return SESSION.original_container,SESSION.localinfo_container
    game=SESSION.encode_verify()
    local=encode_pending_localinfo() if SESSION.pending_localinfo_xml is not None else SESSION.localinfo_container
    return game,local


def stage_account_pair(game: bytes, local: bytes) -> None:
    current_account_containers()
    game_xml=decode_save(game);local_xml=decode_save(local)
    validate_xml_document(game_xml,'mGameInfo thay thế');validate_xml_document(local_xml,'LocalInfo thay thế')
    # Each incoming file keeps its own codec seed/container size.
    for xml,template in [(game_xml,game),(local_xml,local)]:
        if decode_save(encode_save(xml,template))!=canonical_xml(xml):raise SaveToolError('Hai file thay thế không qua encode/decode')
    atomic_write(CLONE_LOCAL_MODIFIED,local_xml)
    SESSION.apply_xml(game_xml)
    SESSION.pending_localinfo_xml=local_xml
    SESSION.pending_pair_templates=(game,local)


def backup_prompt() -> None:
    print('\nBackup TSVIP — ZIP gồm mGameInfo.xml + LocalInfo.xml + read_info.md')
    print('1. Hai file hiện tại trên LDPlayer (theo TSVIP)')
    print('2. Hai file gốc đã tải vào phiên làm việc')
    print('3. Hai file đã chỉnh sửa (encode + verify, chưa ghi game)')
    print('0. Hủy')
    choice=input('Chọn: ').strip()
    if choice=='0':return
    if choice=='1':
        check_device();adb_shell(f'am force-stop {shell_quote(PACKAGE_NAME)}')
        game=_clone_read_remote(REMOTE_SAVE,'backup_game');local=_clone_read_remote(REMOTE_LOCALINFO,'backup_local')
    elif choice in ('2','3'):game,local=current_account_containers(choice=='3')
    else:raise SaveToolError('Lựa chọn Backup không hợp lệ')
    path=create_account_backup(game,local,label='device' if choice=='1' else 'edited' if choice=='3' else 'loaded original')
    print('Đã backup và kiểm tra ZIP:',path)


def history_prompt() -> None:
    root_raw=input(f'Thư mục backup [{ACCOUNT_BACKUP_DIR}] (hoặc đường dẫn ZIP): ').strip().strip('"')
    root=Path(root_raw) if root_raw else ACCOUNT_BACKUP_DIR
    files=[root] if root.is_file() else sorted(root.rglob('*.zip'),key=lambda p:p.stat().st_mtime,reverse=True) if root.is_dir() else []
    if not files:print('Chưa có ZIP backup. Dùng mục 39 để tạo backup.');return
    keyword=input('Lọc tên / City ID / level (Enter = tất cả): ').strip().casefold()
    rows=[]
    for path in files:
        try:
            _,_,info,_=read_account_backup(path)
            text=f'{info["name"]} | City {info["city_id"]} | LV {info["level"]} | {path.name}'
            error=''
        except Exception as exc:text=path.name+' | ZIP lỗi';error=str(exc)
        if not keyword or keyword in text.casefold():rows.append((path,text,error))
    if not rows:print('Không có backup khớp bộ lọc.');return
    for index,(_,text,_) in enumerate(rows,1):print(f'{index:3}. {text}')
    number=parse_int(input('Chọn backup (0 = hủy): '),'Backup',0,len(rows))
    if not number:return
    path,text,error=rows[number-1];print(path)
    print('1. Xem thông tin  2. Mở để chỉnh sửa / xuất  3. Khôi phục vào LDPlayer  4. Xóa ZIP  0. Hủy')
    choice=input('Chọn: ').strip()
    if choice=='0':return
    if choice=='4':
        if ask_yes_no(f'Xóa ZIP backup {path.name}?',False):path.unlink();print('Đã xóa ZIP đã chọn.')
        return
    if error:raise SaveToolError(error)
    game,local,info,doc=read_account_backup(path)
    if choice=='1':print(text);print(doc or '(ZIP TSVIP không có read_info.md)');return
    if choice not in ('2','3'):raise SaveToolError('Lựa chọn History không hợp lệ')
    originals=current_account_containers()
    print(f'Thay toàn bộ hai file bằng backup của City {info["city_id"]}, LV {info["level"]}.')
    if not ask_yes_no('Áp dụng backup này? Thay đổi chưa lưu sẽ được backup riêng.',False):return
    if SESSION.changed:
        edited=current_account_containers(True)
        print('Backup thay đổi chưa lưu:',create_account_backup(*edited,label='pre-restore edited'))
    print('Backup hai file gốc:',create_account_backup(*originals,label='pre-restore original'))
    stage_account_pair(game,local)
    if choice=='3':save_to_device_prompt()
    else:print('Đã mở cả hai XML. Chọn 50 xuất/verify hoặc 51 để ghi game.')


def new_towncity_payload() -> tuple[bytes,bytes,dict]:
    # qf2.p: SHA256 password -> AES-GCM; nonce is the first 12 bytes of images.dat.
    asset=base64.b64decode(TSVIP_FRESH_TOWN_ASSET)
    if sha256_bytes(asset)!=TSVIP_FRESH_TOWN_ASSET_SHA256:raise SaveToolError('Mẫu New Towncity bị thay đổi')
    try:raw=AESGCM(hashlib.sha256(b'MySuperSecretPassword123').digest()).decrypt(asset[:12],asset[12:],None)
    except Exception as exc:raise SaveToolError('Không giải mã được mẫu New Towncity') from exc
    game,local,info,_=read_account_backup_bytes(raw)
    return game,local,info


def new_towncity_prompt() -> None:
    originals=current_account_containers()
    print('\nNew Towncity TSVIP — thay toàn bộ mGameInfo và LocalInfo bằng mẫu thành phố mới.')
    print('1. Mẫu images.dat có sẵn trong TSVIP v121')
    print('2. ZIP thành phố mới của bạn')
    print('0. Hủy')
    choice=input('Chọn: ').strip()
    if choice=='0':return
    if choice=='1':game,local,info=new_towncity_payload()
    elif choice=='2':
        path=Path(input('Đường dẫn ZIP: ').strip().strip('"'))
        game,local,info,_=read_account_backup(path)
    else:raise SaveToolError('Lựa chọn New Towncity không hợp lệ')
    print(f'Mẫu: {info["name"]} | City ID: {info["city_id"]} | Level: {info["level"]} | Version: {info["version"]}/{info["fver"]}')
    print('Chức năng thay cả thông tin tài khoản bằng mẫu; không đăng ký City ID mới với server.')
    if choice=='1':print('Mẫu APK thực tế LV 3, version 27.0.1; nhãn Level 1 của TSVIP không đúng với dữ liệu mẫu.')
    if not ask_yes_no('Backup rồi áp dụng New Towncity vào hai XML đang chỉnh sửa?',False):return
    if SESSION.changed:print('Backup thay đổi chưa lưu:',create_account_backup(*current_account_containers(True),label='pre-new-town edited'))
    print('Backup hai file gốc:',create_account_backup(*originals,label='pre-new-town original'))
    stage_account_pair(game,local)
    print('Đã chuẩn bị New Towncity. Chọn 50 để xuất cả hai file hoặc 51 để backup + ghi game.')


def save_to_device_prompt() -> None:
    SESSION.require_loaded()
    if not SESSION.changed:
        print("Không có thay đổi để lưu.")
        return
    assert SESSION.original_container is not None
    assert SESSION.current_xml is not None

    print("\nChương trình sẽ:")
    print("  1. Encode bằng seed/kích thước container gốc")
    print("  2. Decode lại để xác minh")
    print("  3. Tạo backup local và backup trên thiết bị")
    print("  4. Ghi atomically vào save")
    print("  5. Pull lại và so sánh byte")
    if not ask_yes_no("Tiếp tục ghi vào LDPlayer?"):
        print("Đã hủy.")
        return

    if SESSION.pending_localinfo_xml is not None:
        save_clone_pair_to_device()
        return
    encoded = SESSION.encode_verify()
    local_backup, remote_backup = write_save_to_device(
        encoded, SESSION.original_container
    )
    print("GHI THÀNH CÔNG")
    print("Backup local :", local_backup)
    print("Backup device:", remote_backup)
    print("Output        :", OUTPUT_FILE)

    # Output becomes the new base for subsequent edits.
    SESSION.original_container = encoded
    SESSION.original_xml = SESSION.current_xml
    atomic_write(SOURCE_FILE, encoded)
    atomic_write(DECODED_FILE, SESSION.current_xml)


def export_local_output_prompt() -> None:
    SESSION.require_loaded()
    if not SESSION.changed:
        print("Không có thay đổi để encode.")
        return
    encoded = SESSION.encode_verify()
    print("Đã encode và verify local:", OUTPUT_FILE)
    print("SHA-256:", sha256_bytes(encoded))
    if SESSION.pending_localinfo_xml is not None:
        encode_pending_localinfo()
        print("LocalInfo đã encode/verify:", CLONE_LOCAL_OUTPUT)
        print("Phải dùng cả mGameInfo output và LocalInfo output cùng nhau.")


def restore_backup_prompt() -> None:
    backups = sorted(BACKUP_DIR.glob("*.mGameInfo"), reverse=True)
    if not backups:
        print("Chưa có backup local.")
        return
    print("\n--- Backup local ---")
    for index, path in enumerate(backups, 1):
        print(f"{index:2}. {path.name}")
    choice = parse_int(input("Chọn số backup (0 để hủy): "), "Lựa chọn", 0, len(backups))
    if choice == 0:
        return
    selected = backups[choice - 1]
    print("Sẽ khôi phục:", selected)
    if not ask_yes_no("Xác nhận khôi phục vào LDPlayer?"):
        return
    if not SOURCE_FILE.exists():
        current = pull_save_from_device()
        atomic_write(SOURCE_FILE, current)
    restore_local_backup(selected)
    print("Đã khôi phục. Hãy chọn mục 1 để tải lại save.")


def load_prompt() -> None:
    print("1. Lấy mGameInfo + LocalInfo trực tiếp từ LDPlayer")
    print("2. Mở một file local")
    choice = input("Chọn: ").strip()
    if choice == "1":
        SESSION.load_device()
    elif choice == "2":
        path = Path(input("Đường dẫn file: ").strip().strip('"'))
        if not path.is_file():
            raise SaveToolError(f"Không tìm thấy file: {path}")
        SESSION.load_local(path)
    else:
        raise SaveToolError("Lựa chọn không hợp lệ")
    print("Đã decode mGameInfo:", DECODED_FILE)
    if SESSION.localinfo_xml is not None:
        print("Đã decode LocalInfo:", LOCALINFO_DECODED_FILE)
        print("Số city_id khác nhau:", len(SESSION.friends or {}))
    show_known_values()



def load_localinfo_file_prompt() -> None:
    if SESSION.pending_localinfo_xml is not None:
        raise SaveToolError("Đang có hai file thay thế chưa lưu; xuất/ghi hoặc hoàn tác trước khi mở LocalInfo khác")
    path = Path(input("Đường dẫn LocalInfo.xml gốc hoặc đã decode: ").strip().strip('"'))
    if not path.is_file():
        raise SaveToolError(f"Không tìm thấy file: {path}")
    raw = path.read_bytes()
    xml = decode_save(raw)
    meta, friends = parse_localinfo_metadata(xml)
    SESSION.localinfo_container = raw
    SESSION.localinfo_xml = xml
    SESSION.localinfo_meta = meta
    SESSION.friends = friends
    SESSION.selected_friend = None
    atomic_write(LOCALINFO_SOURCE_FILE, raw)
    atomic_write(LOCALINFO_DECODED_FILE, xml)
    print(f"Đã đọc LocalInfo: {len(friends)} thành phố khác nhau")
    print("Version:", meta.get("version"), "| FVer:", meta.get("fver"))
    print("Own city:", meta.get("own_city_id"))


def list_friends_prompt() -> None:
    if not SESSION.friends:
        raise SaveToolError("Chưa có danh sách bạn bè. Tải LocalInfo trước.")
    items = sorted(SESSION.friends.values(), key=friend_sort_key)
    keyword = input("Tìm theo tên/city_id (Enter = tất cả): ").strip().casefold()
    if keyword:
        items = [
            f for f in items
            if keyword in f.city_name.casefold() or keyword in f.city_id.casefold()
        ]
    if not items:
        print("Không tìm thấy bạn phù hợp.")
        return
    display_friend_table(items)


def select_friend_prompt() -> None:
    if not SESSION.friends:
        raise SaveToolError("Chưa có danh sách bạn bè.")
    items = sorted(SESSION.friends.values(), key=friend_sort_key)
    keyword = input("Nhập tên hoặc city_id để lọc: ").strip().casefold()
    if keyword:
        items = [
            f for f in items
            if keyword in f.city_name.casefold() or keyword in f.city_id.casefold()
        ]
    if not items:
        raise SaveToolError("Không tìm thấy bạn phù hợp")
    display_friend_table(items)
    choice = parse_int(input("Chọn STT (0 để hủy): "), "Lựa chọn", 0, len(items))
    if choice == 0:
        return
    selected = items[choice - 1]
    SESSION.selected_friend = selected
    SESSION.donor_xml = None
    SESSION.donor_path = None
    atomic_write(
        SELECTED_FRIEND_FILE,
        json.dumps(selected.to_dict(), ensure_ascii=False, indent=2).encode("utf-8"),
    )
    print("Đã chọn:", selected.city_name, "|", selected.city_id)
    print("Level:", selected.level, "| fver:", selected.fver)
    print("fetched_city_ver:", selected.fetched_city_ver)


def fetch_selected_friend_prompt() -> None:
    if SESSION.selected_friend is None:
        raise SaveToolError("Chưa chọn bạn bè")
    if not SESSION.localinfo_meta:
        raise SaveToolError("Chưa đọc metadata LocalInfo")

    selected = SESSION.selected_friend
    bver = SESSION.localinfo_meta.get("version", "")
    fver = SESSION.localinfo_meta.get("fver", "")
    if not bver or not fver:
        raise SaveToolError("LocalInfo thiếu Version/version hoặc Version/FVer")

    print("\n--- FetchCity trực tiếp ---")
    print("Tên    :", selected.city_name)
    print("city_id:", selected.city_id)
    print("bver   :", bver)
    print("fver   :", fver)
    print("cityVer:", selected.fetched_city_ver)
    if not ask_yes_no("Gửi request FetchCity tới Playrix?"):
        print("Đã hủy.")
        return

    out_dir = FRIENDS_DIR / selected.city_id
    donor, response_obj, city_ver = fetch_city_live(
        selected.city_id,
        bver,
        fver,
        selected.fetched_city_ver,
        out_dir=out_dir,
    )
    SESSION.donor_xml = donor
    SESSION.donor_path = out_dir / "friend_city.xml"
    shutil.copy2(SESSION.donor_path, DONOR_FILE)

    profile = selected.to_dict()
    profile["response_city_ver"] = city_ver
    atomic_write(
        out_dir / "profile.json",
        json.dumps(profile, ensure_ascii=False, indent=2).encode("utf-8"),
    )

    print("FETCHCITY THÀNH CÔNG")
    print("Donor:", SESSION.donor_path)
    print("cityVer response:", city_ver)
    print("City :", count_layout_objects(donor, "city"))
    print("Zoo  :", count_layout_objects(donor, "zoo"))
    print("Stash:", count_layout_objects(donor, "stash"))



def fetch_manual_cityid_prompt() -> None:
    """
    Fetch an arbitrary Township cityId without requiring it to exist in
    SESSION.friends / LocalInfo friend groups.

    bver/fver default to LocalInfo metadata when available.
    cityVer defaults to 0, which asks the server for the current city payload.
    """
    city_id = input("Nhập cityId thủ công: ").strip()
    if not city_id:
        raise SaveToolError("cityId không được để trống")
    if not CITY_ID_VALUE_RE.fullmatch(city_id):
        raise SaveToolError(
            "cityId có ký tự không hợp lệ. Chỉ dùng chữ, số, _, - (3-64 ký tự)."
        )

    if not SESSION.localinfo_meta:
        raise SaveToolError(
            "Chưa có LocalInfo metadata. Hãy tải LocalInfo trước để tool tự lấy bver/fver."
        )

    bver = (SESSION.localinfo_meta.get("version", "") or "").strip()
    fver = (SESSION.localinfo_meta.get("fver", "") or "").strip()
    if not bver or not fver:
        raise SaveToolError(
            "LocalInfo thiếu Version/@version hoặc Version/@FVer."
        )

    # Manual cityId does not require the user to know cityVer.
    # 0 requests the current city payload.
    city_ver = 0

    print("\n--- MANUAL FETCHCITY ---")
    print("cityId :", city_id)
    print("bver   :", bver, "(auto từ LocalInfo)")
    print("fver   :", fver, "(auto từ LocalInfo)")
    print("cityVer:", city_ver, "(auto)")

    if not ask_yes_no("Gửi FetchCity với cityId này?"):
        print("Đã hủy.")
        return

    out_dir = FRIENDS_DIR / f"manual_{city_id}"
    donor, response_obj, response_city_ver = fetch_city_live(
        city_id,
        bver,
        fver,
        city_ver,
        out_dir=out_dir,
    )

    fetched_level, level_evidence, _ = extract_city_level(donor)

    # Make the manually entered city behave like a selected friend so the
    # existing donor inspection/clone UI can be reused unchanged.
    manual_profile = FriendProfile(
        city_id=city_id,
        city_name=f"Manual:{city_id}",
        level=fetched_level,
        fver=fver,
        fetched_city_ver=response_city_ver,
        groups=["ManualCityId"],
    )
    SESSION.selected_friend = manual_profile
    SESSION.donor_xml = donor
    SESSION.donor_path = out_dir / "friend_city.xml"
    shutil.copy2(SESSION.donor_path, DONOR_FILE)

    profile = manual_profile.to_dict()
    profile["request_city_ver"] = city_ver
    profile["response_city_ver"] = response_city_ver
    profile["level_evidence"] = level_evidence
    profile["source"] = "manual_city_id"
    atomic_write(
        out_dir / "profile.json",
        json.dumps(profile, ensure_ascii=False, indent=2).encode("utf-8"),
    )

    print("\nMANUAL FETCHCITY THÀNH CÔNG")
    print("Donor :", SESSION.donor_path)
    print("Level :", fetched_level if fetched_level > 0 else "?")
    print("cityVer response:", response_city_ver)
    print("City  :", count_layout_objects(donor, "city"))
    print("Zoo   :", count_layout_objects(donor, "zoo"))
    print("Stash :", count_layout_objects(donor, "stash"))

    if SESSION.loaded:
        print("\nDonor đã sẵn sàng để clone vào save đang mở.")
        if ask_yes_no("Clone ngay City / Zoo / Stash / All?"):
            mode = choose_clone_mode()
            assert SESSION.current_xml is not None
            new_xml, changed, stats = clone_friend_layout(
                SESSION.current_xml,
                donor,
                mode,
            )
            SESSION.apply_xml(new_xml)
            print("Đã clone vào XML làm việc. Chưa ghi vào game.")
            print("Mode  :", mode)
            print("Blocks:", ", ".join(changed))
            print("Target trước:", stats["target_before"])
            print("Donor       :", stats["donor"])
            print("Target sau  :", stats["target_after"])
            print("Dùng mục 51 để encode + backup + ghi vào LDPlayer.")
    else:
        print(
            "Chưa mở mGameInfo. Donor đã được lưu; tải save rồi dùng mục Clone."
        )


def inspect_current_donor_prompt() -> None:
    donor = SESSION.donor_xml
    if donor is None and DONOR_FILE.is_file():
        donor = load_friend_donor(DONOR_FILE)
        SESSION.donor_xml = donor
        SESSION.donor_path = DONOR_FILE
    if donor is None:
        raise SaveToolError("Chưa có donor. Hãy FetchCity trước.")
    print("\n--- Donor hiện tại ---")
    if SESSION.selected_friend:
        print("Bạn:", SESSION.selected_friend.city_name, SESSION.selected_friend.city_id)
    print("File :", SESSION.donor_path)
    print("City :", count_layout_objects(donor, "city"))
    print("Zoo  :", count_layout_objects(donor, "zoo"))
    print("Stash:", count_layout_objects(donor, "stash"))
    print("SHA-256:", sha256_bytes(donor))


def clone_current_donor_prompt() -> None:
    SESSION.require_loaded()
    assert SESSION.current_xml is not None
    donor = SESSION.donor_xml
    if donor is None:
        if DONOR_FILE.is_file():
            donor = load_friend_donor(DONOR_FILE)
        else:
            raise SaveToolError("Chưa có donor. Hãy FetchCity trước.")

    mode = choose_clone_mode()
    new_xml, changed, stats = clone_friend_layout(SESSION.current_xml, donor, mode)

    print("\n--- Báo cáo clone ---")
    if SESSION.selected_friend:
        print("Bạn:", SESSION.selected_friend.city_name, SESSION.selected_friend.city_id)
    print("Mode:", mode)
    print("Blocks:", ", ".join(changed))
    print("Target trước:", stats["target_before"])
    print("Donor       :", stats["donor"])
    print("Target sau  :", stats["target_after"])
    if not ask_yes_no("Áp dụng vào XML làm việc?"):
        print("Đã hủy.")
        return

    SESSION.apply_xml(new_xml)
    print("Đã clone vào XML làm việc. Chưa ghi vào game.")


def reset_changes() -> None:
    SESSION.require_loaded()
    assert SESSION.original_xml is not None
    if SESSION.changed and not ask_yes_no("Hủy toàn bộ thay đổi chưa lưu?"):
        return
    SESSION.pending_localinfo_xml = None
    SESSION.pending_pair_templates = None
    SESSION.current_xml = SESSION.original_xml
    atomic_write(MODIFIED_FILE, SESSION.original_xml)
    print("Đã hoàn tác XML làm việc về trạng thái ban đầu.")


def print_menu() -> None:
    print("\n" + "=" * 72)
    print(" TOWNSHIP SIMPLE + DIRECT FETCHCITY v0.4.21")
    print("=" * 72)
    print(" 1. Tải/decode mGameInfo + LocalInfo")
    print(" 2. Xem tiền / level / XP / ngày tạo")
    print(" 3. Sửa money")
    print(" 4. Sửa moneyCash")
    print(" 5. Sửa tháng/năm tạo tài khoản")
    print(" 6. Set Level game Township (TSVIP)")
    print(" 7. Match 3 level (M3 LVL)")
    print(" 8. First Win (1st Win)")
    print(" 9. Lives (LivesSent)")
    print("10. Help (Profile Statistics)")
    print("11. Card (Profile Statistics)")
    print("12. Regata (Profile Statistics)")
    print("13. Expedition Energy")
    print("14. Mine Depth")
    print("15. Avatar (xem / chọn / mở / khóa)")
    print("16. Decoration (chọn / tất cả / số lượng)")
    print("17. Land (mở đất)")
    print("18. Museum (hoàn thành bảo tàng)")
    print("19. All Card")
    print("20. My Card")
    print("21. Golden Pass")
    print("22. Skin")
    print("23. Stickers")
    print("24. Profile (huy hiệu / danh hiệu / khung / phong cách)")
    print("25. Achievements")
    print("26. Barn (cấp kho / sản phẩm)")
    print("27. Golden Pass Editor")
    print("28. Academy (Academi)")
    print("29. Zoo Card")
    print("30. Advantages")
    print("31. Market")
    print("32. Quantities")
    print("33. Train")
    print("34. Regatta task")
    print("35. Send card")
    print("36. Clone City v1")
    print("37. Clone City v3")
    print("38. Fix tutorial bug")
    print("39. Backup")
    print("40. History")
    print("41. New Towncity")
    print("42. Sửa một <Var> bất kỳ")
    print("43. Sửa nhiều thuộc tính của tag bất kỳ")
    print("44. Mở LocalInfo từ file local")
    print("45. Xem/tìm danh sách bạn bè")
    print("46. Chọn bạn bè")
    print("47. FetchCity trực tiếp từ Playrix")
    print("48. Xem donor vừa tải")
    print("49. Clone City / Zoo / Stash / All")
    print("50. Encode + verify local (chưa ghi game)")
    print("51. Encode + backup + ghi vào LDPlayer")
    print("52. Hoàn tác các thay đổi chưa lưu")
    print("53. Khôi phục từ backup local")
    print("54. Quét XML friend/honor để tìm city_id liên quan")
    print("55. Friend Network: Sequential / Random + lọc trùng")
    print("56. Manual City ID: nhập cityId -> FetchCity + clone")
    print(" 0. Thoát")
    print("-" * 72)
    friend_text = "CHƯA CHỌN"
    if SESSION.selected_friend is not None:
        friend_text = (
            f"{SESSION.selected_friend.city_name} "
            f"({SESSION.selected_friend.city_id})"
        )
    donor_text = "CÓ" if SESSION.donor_xml is not None else "KHÔNG"
    print(
        f"Save: {'ĐÃ TẢI' if SESSION.loaded else 'CHƯA TẢI'} | "
        f"Thay đổi: {'CÓ' if SESSION.changed else 'KHÔNG'} | "
        f"Bạn: {friend_text} | Donor: {donor_text}"
    )


def main() -> int:
    WORK_DIR.mkdir(parents=True, exist_ok=True)
    BACKUP_DIR.mkdir(parents=True, exist_ok=True)

    actions = {
        "1": load_prompt,
        "2": show_known_values,
        "3": lambda: edit_integer_var_prompt("money", 0, 2_000_000_000),
        "4": lambda: edit_integer_var_prompt("moneyCash", 0, 2_000_000_000),
        "5": edit_date_prompt,
        "6": edit_level_prompt,
        "7": edit_match3_level_prompt,
        "8": edit_first_win_prompt,
        "9": edit_lives_prompt,
        "10": lambda: edit_profile_stat_prompt("help"),
        "11": lambda: edit_profile_stat_prompt("card"),
        "12": lambda: edit_profile_stat_prompt("regata"),
        "13": lambda: edit_profile_stat_prompt("energy"),
        "14": edit_mine_depth_prompt,
        "15": unlock_all_avatars_prompt,
        "16": decoration_prompt,
        "17": land_prompt,
        "18": museum_prompt,
        "19": lambda: cards_prompt(True),
        "20": lambda: cards_prompt(False),
        "21": golden_pass_prompt,
        "22": lambda: unlock_catalog_prompt("skin"),
        "23": lambda: unlock_catalog_prompt("stickers"),
        "24": lambda: unlock_catalog_prompt("profile"),
        "25": lambda: unlock_catalog_prompt("achievements"),
        "26": barn_prompt,
        "27": golden_pass_editor_prompt,
        "28": academy_prompt,
        "29": zoo_cards_prompt,
        "30": advantages_prompt,
        "31": market_prompt,
        "32": quantities_prompt,
        "33": train_prompt,
        "34": regatta_tasks_prompt,
        "35": send_card_prompt,
        "36": clone_city_v1_prompt,
        "37": clone_city_v3_prompt,
        "38": tutorial_fix_prompt,
        "39": backup_prompt,
        "40": history_prompt,
        "41": new_towncity_prompt,
        "42": edit_any_var_prompt,
        "43": edit_any_tag_prompt,
        "44": load_localinfo_file_prompt,
        "45": list_friends_prompt,
        "46": select_friend_prompt,
        "47": fetch_selected_friend_prompt,
        "48": inspect_current_donor_prompt,
        "49": clone_current_donor_prompt,
        "50": export_local_output_prompt,
        "51": save_to_device_prompt,
        "52": reset_changes,
        "53": restore_backup_prompt,
        "54": inspect_network_ids_prompt,
        "55": crawl_friend_network_prompt,
        "56": fetch_manual_cityid_prompt,
    }

    while True:
        print_menu()
        choice = input("Chọn chức năng: ").strip()
        if choice == "0":
            if SESSION.changed and not ask_yes_no("Có thay đổi chưa lưu. Vẫn thoát?"):
                continue
            return 0
        action = actions.get(choice)
        if action is None:
            print("Lựa chọn không hợp lệ.")
            continue
        try:
            action()
        except KeyboardInterrupt:
            print("\nĐã hủy thao tác.")
        except Exception as exc:
            print(f"\n[ERROR] {type(exc).__name__}: {exc}")
        input("\nNhấn Enter để tiếp tục...")


