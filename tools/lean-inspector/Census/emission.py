"""Shared structured Lean Name decoder for census artifact consumers."""


def parse_name_key(text):
    data = text.encode("utf-8")

    def parse(offset):
        if data[offset:offset + 2] == b"n0":
            return ["anonymous"], offset + 2
        tag = data[offset:offset + 3]
        if tag not in (b"ns(", b"nn("):
            raise ValueError("invalid structured Name")
        parent, offset = parse(offset + 3)
        if data[offset:offset + 1] != b",":
            raise ValueError("invalid Name separator")
        end = offset + 1
        while end < len(data) and 48 <= data[end] <= 57:
            end += 1
        value = int(data[offset + 1:end])
        if tag == b"ns(":
            if data[end:end + 1] != b":":
                raise ValueError("invalid Name length")
            value, end = data[end + 1:end + 1 + value].decode("utf-8"), end + 1 + value
        if data[end:end + 1] != b")":
            raise ValueError("invalid Name terminator")
        return ["str" if tag == b"ns(" else "num", parent, value], end + 1

    value, offset = parse(0)
    if offset != len(data):
        raise ValueError("trailing Name bytes")
    return value
