#!/usr/bin/env python3
"""Local UI for the Patch-Post-Verification workflow.

The service is deliberately loopback-only. Firmware is held in a per-job
directory below webapp/jobs and each download is served by an opaque job id.
"""

from __future__ import annotations

import cgi
import hashlib
import json
import os
import re
import shutil
import struct
import subprocess
import time
import uuid
from http import HTTPStatus
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path
from urllib.parse import parse_qs, urlparse


ROOT = Path(__file__).resolve().parent.parent
APP_DIR = Path(__file__).resolve().parent
JOB_ROOT = APP_DIR / "jobs"
MAGIC_DIR = ROOT / "Patch-Post-Verification" / "bin"
MAX_UPLOAD_BYTES = 512 * 1024 * 1024
BTHD_MAGIC = 0x42544844
PLACEHOLDER_IMAGE_ADDR = 0xAAAAAAAACCCCCCCC


class FirmwareError(ValueError):
    pass


def read_u32(data: bytes | bytearray, offset: int) -> int:
    if offset < 0 or offset + 4 > len(data):
        raise FirmwareError(f"Invalid 32-bit field offset: 0x{offset:X}")
    return struct.unpack_from("<I", data, offset)[0]


def read_u64(data: bytes | bytearray, offset: int) -> int:
    if offset < 0 or offset + 8 > len(data):
        raise FirmwareError(f"Invalid 64-bit field offset: 0x{offset:X}")
    return struct.unpack_from("<Q", data, offset)[0]


def write_u32(data: bytearray, offset: int, value: int) -> None:
    struct.pack_into("<I", data, offset, value)


def write_u64(data: bytearray, offset: int, value: int) -> None:
    struct.pack_into("<Q", data, offset, value)


def header(data: bytes | bytearray) -> tuple[int, int]:
    if len(data) < 0x200 or read_u32(data, 0) != BTHD_MAGIC:
        raise FirmwareError("Expected a complete BTHD trusted-firmware image.")
    image_addr = read_u64(data, 0x28)
    image_size = read_u32(data, 0x30)
    if image_size == 0 or 0x200 + image_size + 0x60 > len(data):
        raise FirmwareError("BTHD image is incomplete or has an invalid mImgSize.")
    return image_addr, image_size


def footer(data: bytes | bytearray, image_size: int) -> int:
    offset = 0x200 + image_size
    if offset + 0x60 > len(data):
        raise FirmwareError("Signed-image footer is outside the file.")
    return offset


def region(data: bytes | bytearray, footer_offset: int, index: int) -> tuple[int, int]:
    """Return (size, offset) for payload/cert/priv/debug region index 0..4."""
    field = footer_offset + 0x10 + index * 0x10
    return read_u64(data, field), read_u64(data, field + 8)


def ensure_range(start: int, length: int, total: int, label: str) -> None:
    if start < 0 or length < 0 or start + length > total:
        raise FirmwareError(f"{label} (0x{start:X} + 0x{length:X}) is outside the input file.")


def signed_image_end(data: bytes) -> int:
    """Return the end of all BTHD signed regions, excluding partition padding."""
    _, image_size = header(data)
    footer_offset = footer(data, image_size)
    end = footer_offset + 0x60
    for index in range(5):
        size, offset = region(data, footer_offset, index)
        if size:
            ensure_range(offset, size, len(data), "Signed-image region")
            end = max(end, offset + size)
    return end


def format_address(value: int | None) -> str:
    return "未确定" if value is None else f"0x{value:08X}"


def aarch64_entry_literals(payload: bytes) -> list[int]:
    """Recover 64-bit LDR-literal values referenced in the first 0x100 bytes."""
    values: list[int] = []
    for offset in range(0, min(len(payload) - 3, 0x100), 4):
        instruction = read_u32(payload, offset)
        if instruction & 0xFF000000 != 0x58000000:  # LDR Xt, #imm19
            continue
        imm19 = (instruction >> 5) & 0x7FFFF
        if imm19 & 0x40000:
            imm19 -= 0x80000
        literal_offset = offset + imm19 * 4
        if 0 <= literal_offset <= len(payload) - 8:
            values.append(read_u64(payload, literal_offset))
    return values


def infer_load_address(stage: str, data: bytes) -> dict[str, object]:
    """Return a transparent static candidate, never an asserted runtime fact."""
    image_addr, image_size = header(data)
    footer_offset = footer(data, image_size)
    payload_size, payload_offset = region(data, footer_offset, 0)
    ensure_range(payload_offset, payload_size, len(data), "Payload")
    payload = data[payload_offset : payload_offset + payload_size]
    evidence = [f"BTHD payload: file+0x{payload_offset:X}, size 0x{payload_size:X}"]
    result: dict[str, object] = {
        "stage": stage,
        "header_address": f"0x{image_addr:016X}",
        "payload_size": payload_size,
        "candidate": None,
        "confidence": "无法静态确定",
        "kind": "未知",
        "evidence": evidence,
        "sha256": hashlib.sha256(data).hexdigest(),
    }
    if image_addr not in {0, PLACEHOLDER_IMAGE_ADDR} and image_addr <= 0xFFFFFFFF:
        result.update(candidate=image_addr, confidence="高", kind="BTHD 头确认")
        evidence.append("BTHD mImgAddr 不是占位值，直接作为候选。")
        return result
    if image_addr == PLACEHOLDER_IMAGE_ADDR:
        evidence.append("BTHD mImgAddr = 0xAAAAAAAACCCCCCCC，为厂商占位值，已忽略。")
    if payload.startswith((b"TEECONFIG_HEADER", b"TEE_CONFIG_HEADER")):
        result.update(kind="配置数据", confidence="不适用")
        evidence.append("payload 以 TEECONFIG_HEADER 开头；需要从 SML 的加载逻辑推断位置。")
        return result

    literals = aarch64_entry_literals(payload)
    runtime_literals = sorted({value for value in literals if 0x80000000 <= value <= 0xFFFFFFFF})
    if len(runtime_literals) >= 2:
        high_bytes = {value >> 24 for value in runtime_literals}
        span = runtime_literals[-1] - runtime_literals[0]
        if len(high_bytes) == 1 and span < 0x1000000:
            candidate = runtime_literals[0] & 0xFF000000
            result.update(candidate=candidate, confidence="中", kind="AArch64 启动 literal 推断")
            evidence.append(
                "入口 LDR literal 引用 "
                + ", ".join(f"0x{value:08X}" for value in runtime_literals[:4])
                + f"；按同一 16 MiB 运行区推断基址 {format_address(candidate)}。"
            )
            return result
    if literals:
        evidence.append("入口存在 AArch64 literal，但未形成可验证的同一运行区候选。")
    else:
        evidence.append("入口未发现可用于静态推断的 AArch64 LDR literal。")
    return result


def payload_layout(data: bytes) -> tuple[bool, int, int, int | None]:
    """Return raw flag, payload offset, payload length, and footer offset."""
    if len(data) >= 4 and read_u32(data, 0) == BTHD_MAGIC:
        _, image_size = header(data)
        footer_offset = footer(data, image_size)
        payload_size, payload_offset = region(data, footer_offset, 0)
        ensure_range(payload_offset, payload_size, len(data), "Payload")
        return False, payload_offset, payload_size, footer_offset
    return True, 0, len(data), None


def pack_patch_data(modified: bytes, magic: bytes, load_addr: int) -> tuple[bytes, dict[str, int]]:
    """Python implementation of diff_tool/difftool.c's file transformation."""
    _, magic_image_size = header(magic)
    magic_footer = footer(magic, magic_image_size)
    modified_is_raw, modified_offset, modified_size, modified_footer = payload_layout(modified)
    payload_size, payload_offset = region(magic, magic_footer, 0)
    ensure_range(payload_offset, payload_size, len(magic), "Magic payload")
    if modified_size < payload_size:
        raise FirmwareError("Modified payload is shorter than the original payload.")
    ensure_range(modified_offset, payload_size, len(modified), "Modified payload")

    opcode = magic[0x203]
    if opcode == 0x14:
        shellcode_size, initial_capacity, architecture = 0x70, 0x80, "AArch64"
    elif opcode == 0xEA:
        shellcode_size, initial_capacity, architecture = 0x94, 0x15C, "ARM32"
    else:
        raise FirmwareError("Magic image has no recognised magic32/magic64 jump instruction.")

    original_payload = magic[payload_offset : payload_offset + payload_size]
    new_payload = modified[modified_offset : modified_offset + payload_size]
    entries: list[tuple[int, bytes]] = []
    offset = 0
    while offset + 4 <= payload_size:
        if original_payload[offset : offset + 4] == new_payload[offset : offset + 4]:
            offset += 4
            continue
        start = offset
        while offset + 4 <= payload_size and original_payload[offset : offset + 4] != new_payload[offset : offset + 4]:
            offset += 4
        entries.append(((load_addr + start) & 0xFFFFFFFF, new_payload[start:offset]))

    # BTHD modified input may have changed the contiguous cert/private/debug block.
    if not modified_is_raw and modified_footer is not None:
        original_regions = [region(magic, magic_footer, i) for i in range(1, 5)]
        nonempty = [(offset, size) for size, offset in original_regions if size]
        if nonempty:
            start = min(offset for offset, _ in nonempty)
            end = max(offset + size for offset, size in nonempty)
            modified_regions = [region(modified, modified_footer, i) for i in range(1, 5)]
            original_cert_offset = original_regions[0][1]
            modified_cert_offset = modified_regions[0][1]
            modified_start = modified_cert_offset + (start - original_cert_offset)
            length = end - start
            ensure_range(start, length, len(magic), "Original extra-data block")
            ensure_range(modified_start, length, len(modified), "Modified extra-data block")
            old_block, new_block = magic[start:end], modified[modified_start : modified_start + length]
            local = 0
            while local + 4 <= length:
                if old_block[local : local + 4] == new_block[local : local + 4]:
                    local += 4
                    continue
                begin = local
                while local + 4 <= length and old_block[local : local + 4] != new_block[local : local + 4]:
                    local += 4
                entries.append(((load_addr + start + begin - 0x200) & 0xFFFFFFFF, new_block[begin:local]))

    patch_data = bytearray()
    for address, words in entries:
        patch_data.extend(struct.pack("<II", address, len(words) // 4))
        patch_data.extend(words)
    patch_data.extend(b"\0\0\0\0")

    magic_start = payload_offset + payload_size
    old_add_length = (magic_footer - magic_start) + 0x10
    if len(patch_data) > initial_capacity:
        new_add_length = (0x10 + shellcode_size + len(patch_data) + 0xFF) & ~0xFF
        add_delta = new_add_length - old_add_length
        capacity = new_add_length - 0x10 - shellcode_size
    else:
        add_delta, capacity = 0, initial_capacity

    if add_delta > 0:
        output = bytearray(len(magic) + add_delta)
        output[:0x200] = magic[:0x200]
        write_u32(output, 0x30, magic_image_size + add_delta)
        output[0x200:0x210] = magic[0x200:0x210]
        output[payload_offset : payload_offset + payload_size] = magic[payload_offset : payload_offset + payload_size]
        output[magic_start : magic_start + shellcode_size] = magic[magic_start : magic_start + shellcode_size]
        patch_offset = magic_start + shellcode_size
        output[patch_offset : patch_offset + len(patch_data)] = patch_data
        new_footer = magic_footer + add_delta
        output[new_footer : new_footer + 0x60] = magic[magic_footer : magic_footer + 0x60]
        # Match difftool.c: cert offset is always shifted; optional regions
        # shift only when they are present.
        for index in range(1, 5):
            size, offset = region(output, new_footer, index)
            if index == 1 or size:
                write_u64(output, new_footer + 0x18 + index * 0x10, offset + add_delta)
        output[new_footer + 0x60 :] = magic[magic_footer + 0x60 :]
    else:
        output = bytearray(magic)
        patch_offset = magic_start + shellcode_size
        output[patch_offset : patch_offset + len(patch_data)] = patch_data
        output[patch_offset + len(patch_data) : patch_offset + capacity] = b"\0" * (capacity - len(patch_data))

    return bytes(output), {
        "architecture": architecture,
        "patch_entries": len(entries),
        "patch_data_bytes": len(patch_data),
        "expanded_bytes": add_delta,
        "output_bytes": len(output),
    }


def clean_filename(name: str | None, fallback: str) -> str:
    name = Path(name or fallback).name
    return re.sub(r"[^A-Za-z0-9._-]", "_", name) or fallback


def cleanup_jobs() -> None:
    JOB_ROOT.mkdir(parents=True, exist_ok=True)
    cutoff = time.time() - 24 * 60 * 60
    for job in JOB_ROOT.iterdir():
        try:
            if job.is_dir() and job.stat().st_mtime < cutoff:
                shutil.rmtree(job)
        except OSError:
            pass


class App(BaseHTTPRequestHandler):
    server_version = "UnisocPatchUI/1.0"

    def log_message(self, fmt: str, *args: object) -> None:
        print(f"[{self.log_date_time_string()}] {fmt % args}")

    def json_response(self, status: int, data: dict) -> None:
        body = json.dumps(data).encode("utf-8")
        self.send_response(status)
        self.send_header("Content-Type", "application/json; charset=utf-8")
        self.send_header("Content-Length", str(len(body)))
        self.end_headers()
        self.wfile.write(body)

    def parse_form(self) -> cgi.FieldStorage:
        content_length = int(self.headers.get("Content-Length", "0"))
        if content_length > MAX_UPLOAD_BYTES * 2 + 1024 * 1024:
            raise FirmwareError("Request is too large. Uploads are limited to 512 MiB each.")
        return cgi.FieldStorage(
            fp=self.rfile,
            headers=self.headers,
            environ={"REQUEST_METHOD": "POST", "CONTENT_TYPE": self.headers.get("Content-Type", "")},
        )

    def save_upload(self, form: cgi.FieldStorage, key: str, job: Path) -> tuple[Path, str]:
        field = form[key] if key in form else None
        if field is None or getattr(field, "file", None) is None:
            raise FirmwareError(f"Missing required upload: {key}.")
        filename = clean_filename(field.filename, f"{key}.bin")
        path = job / f"{key}-{filename}"
        remaining = MAX_UPLOAD_BYTES
        with path.open("wb") as target:
            while chunk := field.file.read(1024 * 1024):
                remaining -= len(chunk)
                if remaining < 0:
                    raise FirmwareError("Firmware upload exceeds the 512 MiB limit.")
                target.write(chunk)
        if path.stat().st_size == 0:
            raise FirmwareError("Uploaded firmware is empty.")
        return path, filename

    def create_job(self) -> tuple[str, Path]:
        cleanup_jobs()
        job_id = uuid.uuid4().hex
        job = JOB_ROOT / job_id
        job.mkdir(parents=True)
        return job_id, job

    def do_GET(self) -> None:
        parsed = urlparse(self.path)
        if parsed.path == "/":
            page = (APP_DIR / "index.html").read_bytes()
            self.send_response(HTTPStatus.OK)
            self.send_header("Content-Type", "text/html; charset=utf-8")
            self.send_header("Content-Length", str(len(page)))
            self.end_headers()
            self.wfile.write(page)
            return
        if parsed.path == "/download":
            query = parse_qs(parsed.query)
            job_id = (query.get("job") or [""])[0]
            artifact = clean_filename((query.get("file") or [""])[0], "")
            path = JOB_ROOT / job_id / artifact
            if len(job_id) != 32 or not path.is_file() or path.parent != JOB_ROOT / job_id:
                self.send_error(HTTPStatus.NOT_FOUND, "Artifact not found")
                return
            self.send_response(HTTPStatus.OK)
            self.send_header("Content-Type", "application/octet-stream")
            self.send_header("Content-Disposition", f'attachment; filename="{artifact}"')
            self.send_header("Content-Length", str(path.stat().st_size))
            self.end_headers()
            with path.open("rb") as source:
                shutil.copyfileobj(source, self.wfile)
            return
        self.send_error(HTTPStatus.NOT_FOUND)

    def do_POST(self) -> None:
        try:
            if self.path == "/api/prepare":
                self.prepare_magic()
            elif self.path == "/api/build":
                self.build_patch()
            elif self.path == "/api/run":
                self.run_all()
            elif self.path == "/api/infer-uboot":
                self.infer_uboot()
            else:
                self.send_error(HTTPStatus.NOT_FOUND)
        except FirmwareError as error:
            self.json_response(HTTPStatus.BAD_REQUEST, {"error": str(error)})
        except subprocess.TimeoutExpired:
            self.json_response(HTTPStatus.INTERNAL_SERVER_ERROR, {"error": "magic 工具执行超过 60 秒，已停止。"})
        except Exception as error:  # Keep UI errors actionable without exposing a traceback.
            self.json_response(HTTPStatus.INTERNAL_SERVER_ERROR, {"error": f"服务端异常：{error}"})

    def prepare_magic(self) -> None:
        form = self.parse_form()
        architecture = form.getfirst("architecture", "")
        if architecture not in {"32", "64"}:
            raise FirmwareError("Architecture must be ARM32 or AArch64.")
        job_id, job = self.create_job()
        source, original_name = self.save_upload(form, "original", job)
        header(source.read_bytes())
        executable = MAGIC_DIR / f"magic{architecture}.exe"
        if not executable.is_file():
            raise FirmwareError(f"Missing bundled tool: {executable.name}")
        result = subprocess.run(
            [str(executable), str(source)], cwd=job, capture_output=True, text=True, timeout=60, check=False
        )
        output = job / "patched.bin"
        if result.returncode != 0 or not output.is_file():
            message = (result.stderr or result.stdout or "magic tool failed").strip()
            raise FirmwareError(message[-1000:])
        artifact = f"{Path(original_name).stem}_magic{architecture}.bin"
        output.rename(job / artifact)
        self.json_response(HTTPStatus.OK, {
            "job": job_id,
            "file": artifact,
            "download": f"/download?job={job_id}&file={artifact}",
            "summary": {"architecture": "ARM32" if architecture == "32" else "AArch64", "output_bytes": (job / artifact).stat().st_size},
        })

    def build_patch(self) -> None:
        form = self.parse_form()
        address_text = form.getfirst("load_address", "").strip()
        try:
            load_address = int(address_text, 0)
        except ValueError as error:
            raise FirmwareError("Load address must be hexadecimal, for example 0x9F000000.") from error
        if not 0 <= load_address <= 0xFFFFFFFF:
            raise FirmwareError("Load address must fit in a 32-bit runtime patch entry.")
        job_id, job = self.create_job()
        modified, _ = self.save_upload(form, "modified", job)
        magic_field = form["magic"] if "magic" in form else None
        if magic_field is not None and getattr(magic_field, "file", None) is not None and magic_field.filename:
            magic, magic_name = self.save_upload(form, "magic", job)
        else:
            source_job = form.getfirst("magic_job", "")
            source_file = clean_filename(form.getfirst("magic_file", ""), "")
            if not re.fullmatch(r"[0-9a-f]{32}", source_job) or not source_file:
                raise FirmwareError("Generate a magic image first or upload one manually.")
            source = JOB_ROOT / source_job / source_file
            if not source.is_file() or source.parent != JOB_ROOT / source_job:
                raise FirmwareError("The generated magic image is no longer available. Generate it again.")
            magic_name = source_file
            magic = job / f"magic-{magic_name}"
            shutil.copyfile(source, magic)
        output, summary = pack_patch_data(modified.read_bytes(), magic.read_bytes(), load_address)
        artifact = f"{Path(magic_name).stem}_final.bin"
        (job / artifact).write_bytes(output)
        self.json_response(HTTPStatus.OK, {
            "job": job_id,
            "file": artifact,
            "download": f"/download?job={job_id}&file={artifact}",
            "summary": summary,
        })

    def run_all(self) -> None:
        """One-shot path: original -> magic -> final image in one local job."""
        form = self.parse_form()
        architecture = form.getfirst("architecture", "")
        if architecture not in {"32", "64"}:
            raise FirmwareError("请选择 ARM32 或 AArch64 架构。")
        address_text = form.getfirst("load_address", "").strip()
        try:
            load_address = int(address_text, 0)
        except ValueError as error:
            raise FirmwareError("加载地址必须是十六进制，例如 0x9F000000。") from error
        if not 0 <= load_address <= 0xFFFFFFFF:
            raise FirmwareError("加载地址必须在 32 位范围内。")
        job_id, job = self.create_job()
        original, original_name = self.save_upload(form, "original", job)
        original_data = original.read_bytes()
        modified, _ = self.save_upload(form, "modified", job)
        modified_data = modified.read_bytes()
        partition_size = len(original_data)
        logical_end = signed_image_end(original_data)
        trailing_data = original_data[logical_end:]
        # magic tools append their framework after the signed image. Supplying
        # a full partition dump would unnecessarily grow the output file.
        original.write_bytes(original_data[:logical_end])
        executable = MAGIC_DIR / f"magic{architecture}.exe"
        if not executable.is_file():
            raise FirmwareError(f"缺少内置工具：{executable.name}")
        result = subprocess.run(
            [str(executable), str(original)], cwd=job, capture_output=True, text=True, timeout=60, check=False
        )
        generated_magic = job / "patched.bin"
        if result.returncode != 0 or not generated_magic.is_file():
            message = (result.stderr or result.stdout or "magic tool failed").strip()
            raise FirmwareError(f"生成 magic 镜像失败：{message[-800:]}")
        magic_name = f"{Path(original_name).stem}_magic{architecture}.bin"
        magic = job / magic_name
        generated_magic.rename(magic)
        output, summary = pack_patch_data(modified_data, magic.read_bytes(), load_address)
        if len(output) <= partition_size:
            # Keep the output partition-sized when its framework fits into the
            # original tail slack.
            output += trailing_data[: partition_size - len(output)]
            output_mode = "保持原分区大小"
            appended_bytes = 0
        else:
            # The full original tail follows the shifted signed image, so no
            # data is discarded when the framework cannot fit in the partition.
            output += trailing_data
            output_mode = "超出原分区，已追加"
            appended_bytes = len(output) - partition_size
        artifact = f"{Path(original_name).stem}_final.bin"
        (job / artifact).write_bytes(output)
        summary["magic_file"] = magic_name
        summary["signed_image_bytes"] = logical_end
        summary["reserved_padding_bytes"] = len(trailing_data)
        summary["source_partition_bytes"] = partition_size
        summary["final_partition_bytes"] = len(output)
        summary["output_mode"] = output_mode
        summary["appended_bytes"] = appended_bytes
        self.json_response(HTTPStatus.OK, {
            "job": job_id,
            "file": artifact,
            "download": f"/download?job={job_id}&file={artifact}",
            "summary": summary,
        })

    def infer_uboot(self) -> None:
        form = self.parse_form()
        job_id, job = self.create_job()
        image, filename = self.save_upload(form, "uboot", job)
        report = infer_load_address("uboot", image.read_bytes())
        report["filename"] = filename
        self.json_response(HTTPStatus.OK, {"job": job_id, "report": report})


def main() -> None:
    JOB_ROOT.mkdir(parents=True, exist_ok=True)
    port = int(os.environ.get("UNISOC_PATCH_UI_PORT", "8788"))
    server = ThreadingHTTPServer(("127.0.0.1", port), App)
    print(f"Unisoc Patch UI listening at http://127.0.0.1:{port}")
    try:
        server.serve_forever()
    except KeyboardInterrupt:
        pass
    finally:
        server.server_close()


if __name__ == "__main__":
    main()
