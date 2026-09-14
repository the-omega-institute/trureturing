"""Fixed-buffer JSON projection; skipped values and copied arrays never form a DOM."""

import codecs
import hashlib
import io
import json
import re


BUFFER_BYTES = 65536
SPACE = re.compile(r"[ \t\r\n]*")
STRING = re.compile(r'[^"\\\x00-\x1f]+')
DIGITS = re.compile(r"[0-9]+")


class Reader:
    def __init__(self, source, chunk_size=BUFFER_BYTES):
        self.source, self.chunk_size = source, chunk_size
        self.buffer, self.position, self.ended = "", 0, False
        self.utf8 = codecs.getincrementaldecoder("utf-8")()
        self.sha256 = hashlib.sha256()

    def char(self):
        while self.position == len(self.buffer) and not self.ended:
            block = self.source.read(self.chunk_size)
            self.sha256.update(block)
            self.ended = not block
            self.buffer = self.utf8.decode(block, final=self.ended)
            self.position = 0
        return self.buffer[self.position:self.position + 1]

    def peek(self):
        while self.char():
            self.position = SPACE.match(self.buffer, self.position).end()
            if self.position < len(self.buffer):
                break
        return self.char()

    def take(self, expected, out=None):
        if self.peek() != expected:
            raise ValueError("invalid JSON: expected " + expected)
        self.position += 1
        if out is not None:
            out.write(expected.encode())

    def span(self, pattern, out):
        match = pattern.match(self.buffer, self.position)
        if not match:
            return False
        if out is not None:
            out.write(match[0].encode("utf-8"))
        self.position = match.end()
        return True

    def string(self, out):
        self.take('"', out)
        while self.char() != '"':
            if self.span(STRING, out):
                continue
            if self.char() != "\\":
                raise ValueError("invalid or truncated JSON string")
            self.position += 1
            escape = self.char()
            if not escape or escape not in '"\\/bfnrtu':
                raise ValueError("invalid JSON escape")
            self.position += 1
            text = "\\" + escape
            if escape == "u":
                for _ in range(4):
                    digit = self.char()
                    if not digit or digit not in "0123456789abcdefABCDEF":
                        raise ValueError("invalid JSON unicode escape")
                    self.position += 1
                    text += digit
            if out is not None:
                out.write(text.encode())
        self.position += 1
        if out is not None:
            out.write(b'"')

    def digits(self, out):
        if not self.char() or not self.span(DIGITS, out):
            raise ValueError("invalid JSON number")
        while self.char() and self.span(DIGITS, out):
            pass

    def number(self, out):
        if self.char() == "-":
            self.take("-", out)
        if self.char() == "0":
            self.take("0", out)
        else:
            self.digits(out)
        if self.char() == ".":
            self.take(".", out)
            self.digits(out)
        if self.char() in ("e", "E"):
            self.take(self.char(), out)
            if self.char() in ("+", "-"):
                self.take(self.char(), out)
            self.digits(out)

    def value(self, out=None):
        """Validate and optionally copy one value; return array/object nonemptiness."""
        char = self.peek()
        if char == '"':
            self.string(out)
        elif char in ("[", "{"):
            end = "]" if char == "[" else "}"
            self.take(char, out)
            nonempty = self.peek() != end
            if nonempty:
                while True:
                    if char == "{":
                        self.string(out)
                        self.take(":", out)
                    self.value(out)
                    if self.peek() == end:
                        break
                    self.take(",", out)
            self.take(end, out)
            return nonempty
        elif char in ("t", "f", "n"):
            literal = {"t": "true", "f": "false", "n": "null"}[char]
            for expected in literal:
                if self.char() != expected:
                    raise ValueError("invalid JSON literal")
                self.position += 1
            if out is not None:
                out.write(literal.encode())
        elif char and char in "-0123456789":
            self.number(out)
        else:
            raise ValueError("invalid or truncated JSON value")

    def decoded(self):
        out = io.BytesIO()
        self.value(out)
        return json.loads(out.getvalue())

    def object_keys(self):
        self.take("{")
        if self.peek() != "}":
            while True:
                if self.peek() != '"':
                    raise ValueError("invalid JSON object key")
                key = self.decoded()
                self.take(":")
                yield key
                if self.peek() == "}":
                    break
                self.take(",")
        self.take("}")


def projected_object(reader, scalars, children=None):
    result = {}
    for key in reader.object_keys():
        if key in result:
            raise ValueError("duplicate projected field: " + key)
        if key in scalars:
            result[key] = reader.decoded()
        elif children and key in children:
            result[key] = children[key]()
        else:
            reader.value()
    return result


def rows(reader, leaves):
    """Decode row identities and scalar readings; spool prerequisite bytes separately."""
    def prerequisites():
        if reader.peek() != "[":
            raise ValueError("direct_frozen_prerequisites must be an array")
        nonempty = reader.value(leaves)
        return nonempty

    def readings():
        if reader.peek() == "n":
            return reader.decoded()
        return projected_object(reader, {"core_or_frozen_support", "value_constant_count"},
                                {"direct_frozen_prerequisites": prerequisites})

    seen = False
    for key in reader.object_keys():
        if key != "rows":
            reader.value()
            continue
        if seen:
            raise ValueError("duplicate rows")
        seen = True
        reader.take("[")
        if reader.peek() != "]":
            while True:
                leaves.seek(0)
                leaves.truncate()
                row = projected_object(reader, {"theorem_name", "statement_id", "owning_module",
                                                "generated_candidate", "status"}, {"readings": readings})
                yield row
                if reader.peek() == "]":
                    break
                reader.take(",")
        reader.take("]")
    if not seen or reader.peek():
        raise ValueError("missing rows or trailing JSON")
