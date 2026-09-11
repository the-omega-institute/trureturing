"""Reuse expanded row bytes with filesystem clones and a fresh report header."""

import ctypes
import json
import os
import pathlib
import sys

from incremental import atomic_json
from streaming import digest, file_stamp


def cache_key(rows, modules, scopes, emitter):
    return digest([rows, modules, scopes, emitter])


def clone(source, destination):
    # APFS shares data extents. Other filesystems retain the streaming emitter;
    # unsupported clones never trigger an unbounded in-memory or byte copy.
    if sys.platform != "darwin":
        return False
    function = ctypes.CDLL(None, use_errno=True).clonefile
    function.argtypes = [ctypes.c_char_p, ctypes.c_char_p, ctypes.c_int]
    function.restype = ctypes.c_int
    return function(os.fsencode(source), os.fsencode(destination), 0) == 0


def restore_rows(cache, address, destination, header):
    folder = cache / address[7:]
    record, data = folder / "complete.json", folder / "census.json"
    if not record.is_file() or not data.is_file():
        return False
    value = json.loads(record.read_bytes())
    if value["header_bytes"] != len(header) or value["stamp"] != file_stamp(data):
        return False
    if not clone(data, destination):
        return False
    if file_stamp(data) != value["stamp"]:
        pathlib.Path(destination).unlink()
        raise ValueError("IE-C044 expanded row cache changed during clone")
    with pathlib.Path(destination).open("r+b") as output:
        output.write(header)
    return True


def store_rows(cache, address, source, header_bytes):
    folder = cache / address[7:]
    folder.mkdir(parents=True, exist_ok=True)
    data = folder / "census.json"
    temporary = folder / ("census." + str(os.getpid()) + ".tmp")
    if not clone(source, temporary):
        return False
    (folder / "complete.json").unlink(missing_ok=True)
    os.replace(temporary, data)
    atomic_json(folder / "complete.json", {"header_bytes": header_bytes, "stamp": file_stamp(data)})
    return True
