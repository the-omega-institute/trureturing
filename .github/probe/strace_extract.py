#!/usr/bin/env python3
"""Extract repository path accesses from `strace -ff -y` traces.

Usage: strace_extract.py --repository DIR --traces DIR --unit NAME --output FILE

Reads every trace file under --traces (one file per traced task, written by
`strace -f -ff -qq -y -s 4096 -e trace=%file,getdents64,fchdir`) and writes one
JSON object describing the accesses that fall inside --repository:

  read     paths opened successfully for reading (files)
  write    paths opened with a write or create flag
  stat     paths whose metadata or existence was queried successfully
  missing  paths probed that did not exist (ENOENT / ENOTDIR)
  listed   directories whose entries were read (getdents64)
  exec     executed programs with argv and working directory
"""
import argparse
import json
import os
import re
import sys
from pathlib import Path

SYSCALL = re.compile(r"^(?P<name>[a-z0-9_]+)\((?P<args>.*)\)\s+=\s+(?P<ret>-?\d+|\?)(?P<rest>.*)$")
FD_PATH = re.compile(r"^(?:AT_FDCWD|-?\d+)<(?P<path>(?:[^>\\]|\\.)*)>")
CSTRING = re.compile(r'"((?:[^"\\]|\\.)*)"')
ERRNO = re.compile(r"^\s*([A-Z0-9_]+)\s")

AT_CALLS = {
    "openat", "openat2", "newfstatat", "fstatat64", "statx", "faccessat", "faccessat2",
    "readlinkat", "mkdirat", "unlinkat", "utimensat", "fchmodat", "fchownat",
    "name_to_handle_at", "inotify_add_watch", "execveat",
}
PLAIN_CALLS = {"open", "stat", "lstat", "access", "readlink", "chdir", "execve", "truncate",
               "statfs", "getxattr", "lgetxattr", "listxattr", "llistxattr", "creat"}
WRITE_FLAGS = ("O_WRONLY", "O_RDWR", "O_CREAT", "O_TRUNC", "O_APPEND")


def unescape(text):
    out = bytearray()
    i = 0
    raw = text.encode("utf-8", "surrogateescape")
    while i < len(raw):
        c = raw[i]
        if c != 0x5C:
            out.append(c)
            i += 1
            continue
        nxt = raw[i + 1:i + 2]
        if nxt == b"x" and i + 3 < len(raw) + 1:
            out.append(int(raw[i + 2:i + 4], 16))
            i += 4
        elif nxt and nxt in b"01234567":
            j = i + 1
            while j < len(raw) and j < i + 4 and raw[j:j + 1] in b"01234567":
                j += 1
            out.append(int(raw[i + 1:j], 8))
            i = j
        else:
            mapping = {b"n": 10, b"t": 9, b"r": 13, b"v": 11, b"f": 12, b'"': 34, b"\\": 92}
            out.append(mapping.get(nxt, nxt[0] if nxt else 92))
            i += 2
    return out.decode("utf-8", "surrogateescape")


def split_args(args):
    parts, depth, cur, in_str, esc = [], 0, [], False, False
    for ch in args:
        if in_str:
            cur.append(ch)
            if esc:
                esc = False
            elif ch == "\\":
                esc = True
            elif ch == '"':
                in_str = False
            continue
        if ch == '"':
            in_str = True
        elif ch in "[{(<":
            depth += 1
        elif ch in "]})>":
            depth -= 1
        elif ch == "," and depth == 0:
            parts.append("".join(cur).strip())
            cur = []
            continue
        cur.append(ch)
    if cur:
        parts.append("".join(cur).strip())
    return parts


def fd_dir(arg):
    m = FD_PATH.match(arg)
    return unescape(m.group("path")) if m else None


def first_string(arg):
    m = CSTRING.match(arg.strip())
    return unescape(m.group(1)) if m else None


class Collector:
    def __init__(self, repository):
        self.repository = os.path.realpath(repository)
        self.sets = {k: set() for k in ("read", "write", "stat", "missing", "listed")}
        self.exec = []

    def rel(self, absolute):
        if absolute is None:
            return None
        norm = os.path.normpath(absolute)
        root = self.repository
        if norm == root:
            return "."
        if norm.startswith(root + os.sep):
            return norm[len(root) + 1:]
        return None

    def add(self, kind, absolute):
        rel = self.rel(absolute)
        if rel is not None:
            self.sets[kind].add(rel)


def resolve(base, path):
    if path is None:
        return None
    if path.startswith("/"):
        return path
    if base is None:
        return None
    return os.path.join(base, path)


def process_file(trace, col, unresolved):
    cwd = None
    pending_exec = None
    for raw in trace.open("r", encoding="utf-8", errors="surrogateescape"):
        line = raw.rstrip("\n")
        m = SYSCALL.match(line)
        if not m:
            continue
        name, args, ret, rest = m.group("name"), m.group("args"), m.group("ret"), m.group("rest")
        parts = split_args(args)
        ok = ret != "?" and not ret.startswith("-")
        errno = None
        if not ok:
            em = ERRNO.match(rest)
            errno = em.group(1) if em else None
        # Track the working directory from AT_FDCWD annotations.
        for part in parts[:1]:
            if part.startswith("AT_FDCWD<"):
                cwd = fd_dir(part)
                if pending_exec is not None and pending_exec.get("cwd") is None:
                    pending_exec["cwd"] = col.rel(cwd) if col.rel(cwd) is not None else cwd
        if name == "getdents64":
            if ok and parts:
                col.add("listed", fd_dir(parts[0]))
            continue
        if name == "fchdir":
            if ok and parts:
                cwd = fd_dir(parts[0]) or cwd
            continue
        if name == "execve" or name == "execveat":
            path = first_string(parts[0] if name == "execve" else parts[1])
            argv = CSTRING.findall(parts[1] if name == "execve" else parts[2]) if len(parts) > 1 else []
            absolute = resolve(cwd, path)
            entry = {"path": col.rel(absolute) if col.rel(absolute) is not None else path,
                     "argv": [unescape(a) for a in argv], "ok": ok, "cwd": None}
            if ok:
                col.exec.append(entry)
                pending_exec = entry
                col.add("read", absolute)
            elif errno in ("ENOENT", "ENOTDIR"):
                col.add("missing", absolute)
            continue
        if name == "chdir":
            path = first_string(parts[0]) if parts else None
            if ok:
                cwd = resolve(cwd, path)
            continue
        if name in AT_CALLS:
            if len(parts) < 2:
                continue
            base = fd_dir(parts[0])
            path = first_string(parts[1])
            if path is None:
                continue
            if path == "" and base is not None:
                absolute = base
            else:
                absolute = resolve(base if not path.startswith("/") else None, path)
                if absolute is None:
                    unresolved.append(line[:300])
                    continue
        elif name in PLAIN_CALLS:
            path = first_string(parts[0]) if parts else None
            absolute = resolve(cwd, path)
            if absolute is None:
                if path is not None:
                    unresolved.append(line[:300])
                continue
        else:
            continue
        if not ok:
            if errno in ("ENOENT", "ENOTDIR"):
                col.add("missing", absolute)
            continue
        if name in ("openat", "openat2", "open", "creat"):
            flags = parts[2] if name != "open" and len(parts) > 2 else (parts[1] if len(parts) > 1 else "")
            if name == "creat" or any(flag in flags for flag in WRITE_FLAGS):
                col.add("write", absolute)
            elif "O_DIRECTORY" in flags:
                col.add("stat", absolute)
            else:
                col.add("read", absolute)
        elif name in ("mkdirat", "unlinkat"):
            col.add("write", absolute)
        else:
            col.add("stat", absolute)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--repository", required=True)
    parser.add_argument("--traces", required=True)
    parser.add_argument("--unit", required=True)
    parser.add_argument("--output", required=True)
    args = parser.parse_args()
    col = Collector(args.repository)
    unresolved = []
    files = sorted(p for p in Path(args.traces).rglob("*") if p.is_file())
    for trace in files:
        process_file(trace, col, unresolved)
    result = {"unit": args.unit, "repository": col.repository, "trace_files": len(files),
              "unresolved_samples": unresolved[:50], "unresolved": len(unresolved)}
    for key, values in col.sets.items():
        result[key] = sorted(values)
    seen = set()
    execs = []
    for entry in col.exec:
        key = json.dumps(entry, sort_keys=True)
        if key not in seen:
            seen.add(key)
            execs.append(entry)
    result["exec"] = execs
    Path(args.output).write_text(json.dumps(result, indent=1, sort_keys=True), encoding="utf-8")
    print(f"PROBE_EXTRACT unit={args.unit} files={len(files)} " +
          " ".join(f"{k}={len(v)}" for k, v in col.sets.items()) + f" exec={len(execs)} unresolved={len(unresolved)}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
