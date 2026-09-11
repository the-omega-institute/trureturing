"""Fixed-buffer publication of JSON objects and disk-backed JSONL arrays."""

import json


BUFFER_BYTES = 64 * 1024


def object_prefix(out, fields):
    """Write a canonical object except its closing brace, without a whole DOM encoding."""
    previous = None
    encoder = json.JSONEncoder(sort_keys=True, separators=(",", ":"), ensure_ascii=True)
    for piece in encoder.iterencode(fields):
        if previous is not None:
            for start in range(0, len(previous), BUFFER_BYTES):
                out.write(previous[start:start + BUFFER_BYTES].encode("ascii"))
        previous = piece
    if previous != "}":
        raise ValueError("expected object envelope")


def jsonl_elements(source, out, separator=b","):
    """Copy records as array elements, retaining only one byte across buffers.

    Canonical JSON escapes embedded newlines. Keeping the final byte pending
    lets us drop only the terminal newline, even when a record spans buffers.
    The bound is independent of the size of a row or its upstream frontier.
    """
    tail, count = b"", 0
    while block := source.read(BUFFER_BYTES):
        data = tail + block
        body, tail = data[:-1], data[-1:]
        count += body.count(b"\n")
        out.write(body.replace(b"\n", separator))
    if tail and tail != b"\n":
        out.write(tail)
    return count + bool(tail)
