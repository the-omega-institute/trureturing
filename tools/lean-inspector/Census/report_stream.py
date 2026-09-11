"""Read one truth-export module at a time with the standard JSON decoder."""

import json


def fields(path, chunk_size=65536, array_field="nodes"):
    """Yield metadata fields and individual nodes, never the full node array.

    Space is one maximum module JSON value plus a fixed input buffer. The
    decoder owns strings/escapes/numbers; this reader handles delimiters only.
    """
    with open(path, encoding="utf-8") as source:
        buffer, ended = "", False
        decoder = json.JSONDecoder()

        def more():
            nonlocal buffer, ended
            block = source.read(chunk_size)
            buffer += block
            ended = not block

        def peek():
            nonlocal buffer
            while True:
                buffer = buffer.lstrip()
                if buffer or ended:
                    return buffer[:1]
                more()

        def take(expected):
            nonlocal buffer
            if peek() != expected:
                raise ValueError("IE-C044 invalid export JSON delimiter: expected " + expected)
            buffer = buffer[1:]

        def value():
            nonlocal buffer
            peek()
            while True:
                try:
                    result, end = decoder.raw_decode(buffer)
                    # A number may end at a buffer boundary. Obtain its next
                    # delimiter before accepting the decoder's current prefix.
                    if end == len(buffer) and not ended:
                        more()
                        continue
                    if end < len(buffer) and buffer[end] not in " \r\n\t,}]:":
                        if ended:
                            raise ValueError("IE-C044 invalid export JSON value suffix")
                        more()
                        continue
                    buffer = buffer[end:]
                    return result
                except json.JSONDecodeError:
                    if ended:
                        raise ValueError("IE-C044 truncated or invalid export JSON")
                    more()

        take("{")
        seen = set()
        if peek() != "}":
            while True:
                key = value()
                if not isinstance(key, str) or key in seen:
                    raise ValueError("IE-C044 invalid or duplicate export field")
                seen.add(key)
                take(":")
                if key == array_field:
                    take("[")
                    if peek() != "]":
                        while True:
                            yield key, value()
                            if peek() == "]":
                                break
                            take(",")
                            if peek() == "]":
                                raise ValueError("IE-C044 trailing export node comma")
                    take("]")
                else:
                    yield key, value()
                if peek() == "}":
                    break
                take(",")
                if peek() == "}":
                    raise ValueError("IE-C044 trailing export field comma")
        take("}")
        if array_field not in seen or peek():
            raise ValueError("IE-C044 missing nodes or trailing export JSON")
