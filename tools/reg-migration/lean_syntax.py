from __future__ import annotations

import re
from pathlib import Path
from typing import Any, Iterable

from .model import Registration, Root, Seal, Span, Template


_REG_RE = re.compile(r"(?m)^(?P<indent>[ \t]*)(?P<kind>register_information_theorem|information_theorem)\b")
_TPL_RE = re.compile(r"(?m)^(?P<indent>[ \t]*)register_information_template\b")
_SEAL_RE = re.compile(r"(?m)^(?P<indent>[ \t]*)#seal_information_theory\b")
_ROOT_RE = re.compile(r"(?m)^(?P<indent>[ \t]*)(?:run_cmd\s+)?(?:do\s+)?(?:LeanInformationAudit\.)?RootCatalogs\.declare\s*\{")
_BOUNDARY_RE = re.compile(
    r"(?m)^(?P<indent>[ \t]*)(?:register_information_theorem|information_theorem|"
    r"register_information_template|#seal_information_theory|run_cmd|namespace|section|end|"
    r"#print|#check|#eval|open|set_option|attribute|local\s+notation|(?:private\s+)?(?:noncomputable\s+)?"
    r"(?:def|theorem|lemma|example|abbrev|opaque|instance|inductive|structure|class))\b"
)


def _skip_string(text: str, i: int) -> int:
    quote = text[i]
    i += 1
    while i < len(text):
        if text[i] == "\\":
            i += 2
        elif text[i] == quote:
            return i + 1
        else:
            i += 1
    return len(text)


def _matching(text: str, start: int, opening: str = "{", closing: str = "}") -> int:
    """Return the matching delimiter, respecting strings and Lean comments."""
    depth = 0
    i = start
    block = 0
    while i < len(text):
        if block:
            if text.startswith("/-", i):
                block += 1
                i += 2
            elif text.startswith("-/", i):
                block -= 1
                i += 2
            else:
                i += 1
            continue
        if text.startswith("--", i):
            nl = text.find("\n", i)
            i = len(text) if nl < 0 else nl + 1
            continue
        if text.startswith("/-", i):
            block = 1
            i += 2
            continue
        if text[i] in "\"'":
            i = _skip_string(text, i)
            continue
        if text[i] == opening:
            depth += 1
        elif text[i] == closing:
            depth -= 1
            if depth == 0:
                return i
        i += 1
    raise ValueError(f"unclosed {opening} at {start}")


def _line_end(text: str, pos: int) -> int:
    i = text.find("\n", pos)
    return len(text) if i < 0 else i + 1


def _command_end(text: str, start: int, indent: str) -> int:
    """Find the next same-level Lean command.

    Terms in registration commands are balanced, but can contain newlines at
    depth zero.  A same-or-less-indented known command is therefore a safer
    boundary than newline splitting and retains multiline readouts and proofs.
    """
    base = len(indent.expandtabs(2))
    for match in _BOUNDARY_RE.finditer(text, _line_end(text, start)):
        candidate = match.start()
        indentation = len(match.group("indent").expandtabs(2))
        if indentation <= base and candidate > start:
            return candidate
    return len(text)


def _clean_name(value: str) -> str:
    value = value.strip()
    if value.startswith("_root_."):
        value = value[7:]
    return value


def _after_keyword(body: str, keyword: str, stop: Iterable[str] = ()) -> str | None:
    m = re.search(rf"\b{re.escape(keyword)}\b", body)
    if not m:
        return None
    tail = body[m.end() :]
    if stop:
        positions = [tail.find(word) for word in stop if tail.find(word) >= 0]
        if positions:
            tail = tail[: min(positions)]
    return tail.strip()


def _term_after(body: str, keyword: str, next_keywords: Iterable[str]) -> str | None:
    m = re.search(rf"\b{re.escape(keyword)}\b", body)
    if not m:
        return None
    start = m.end()
    # Parenthesised terms are common in readout/escape clauses.
    while start < len(body) and body[start].isspace():
        start += 1
    if start < len(body) and body[start] == "(":
        try:
            end = _matching(body, start, "(", ")")
            return body[start + 1 : end].strip()
        except ValueError:
            return None
    depth = {"(": 0, "[": 0, "{": 0}
    i = start
    while i < len(body):
        c = body[i]
        if c in "\"'":
            i = _skip_string(body, i)
            continue
        if c in depth:
            depth[c] += 1
        elif c == ")" and depth["("]:
            depth["("] -= 1
        elif c == "]" and depth["["]:
            depth["["] -= 1
        elif c == "}" and depth["{"]:
            depth["{"] -= 1
        if all(v == 0 for v in depth.values()):
            for word in next_keywords:
                if re.match(rf"\s+{re.escape(word)}\b", body[i:]):
                    return body[start:i].strip()
        i += 1
    return body[start:].strip()


def _quoted_string(value: str) -> str:
    m = re.match(r'\s*"((?:\\.|[^"\\])*)"', value, re.S)
    return bytes(m.group(1), "utf8").decode("unicode_escape") if m else value.strip()


def _parse_options(prefix: str) -> dict[str, Any]:
    options: dict[str, Any] = {}
    for m in re.finditer(r"(?m)^\s*set_option\s+([\w.]+)\s+([^\s]+)", prefix):
        name, value = m.group(1), m.group(2)
        if value in {"true", "false"}:
            parsed: Any = value == "true"
        elif re.fullmatch(r"-?\d+", value):
            parsed = int(value)
        elif value.startswith('"'):
            parsed = _quoted_string(value)
        else:
            parsed = value
        options[name] = parsed
    return options


def _parse_registration(path: Path, span: Span, body: str, options: dict[str, Any], namespace: str | None = None) -> Registration:
    kind = body.lstrip().split(None, 1)[0]
    m = re.search(r"\b(?:register_information_theorem|information_theorem)\s+([^\s]+)", body)
    raw_theorem = m.group(1) if m else ""
    explicit_root = raw_theorem.startswith("_root_.")
    theorem = _clean_name(raw_theorem) if m else ""
    if theorem and not theorem.startswith(("D5.", "PredictiveThermodynamic.", "Lean.", "LeanInformationAudit.", "_private.")):
        if namespace and not explicit_root and "." not in theorem:
            theorem = namespace + "." + theorem
        elif "." not in theorem:
            # A file without a namespace normally uses its module path.
            # This is only a fallback; compiled-key matching remains the
            # authoritative source of identity.
            theorem = theorem
    arena_match = re.search(r"\bin\s+([^\s]+)", body)
    arena = _clean_name(arena_match.group(1)) if arena_match else ""
    occurrence = bool(re.search(r"\bobject_arena\s+([^\s]+)\s+catalog\s+([^\s]+)", body))
    object_arena = catalog = None
    if occurrence:
        om = re.search(r"\bobject_arena\s+([^\s]+)\s+catalog\s+([^\s]+)", body)
        object_arena, catalog = _clean_name(om.group(1)), _clean_name(om.group(2))
    primitive = _term_after(body, "primitives", ["realization", "variation", "sensitivity", "escape"])
    realization = None
    rm = re.search(r"\brealization\s+(.+?)(?=\s+(?:variation|sensitivity|escape)\b|\s*$)", body, re.S)
    if rm:
        value = rm.group(1).strip()
        if value.startswith("inline"):
            rest = value[6:].lstrip()
            # inline term := proof; split at the first top-level :=
            marker = _top_level_marker(rest, ":=")
            if marker is not None:
                realization = None
                inline = (rest[:marker].strip(), rest[marker + 2 :].strip())
            else:
                inline = (rest, "")
        else:
            inline = None
            realization = value
    else:
        inline = None
    variation = _identifier_after(body, "variation")
    sensitivity = _identifier_after(body, "sensitivity")
    readout = _term_after(body, "via", ["primitives", "output_evidence", "escape"])
    output = _term_after(body, "output_evidence", ["escape"])
    source = bool(re.search(r"\bescape\s+from\s+source\s*\(", body))
    escape_source = _term_after(body, "source", [")", "escape"])
    escape_from = None if source else _term_after(body, "from", ["escape"])
    cont = None
    cm = re.search(r"\bescape\s+continues\s*\(\s*(.*?)\s*\)\s*$", body, re.S)
    if cm:
        cont = cm.group(1).strip()
    source_record = _identifier_after(body, "realizes")
    finite_bridge = _identifier_after(body, "finite via")
    if source_record and source:
        # `realizes` is present in source and finite-source forms.
        pass
    finite_source = bool(re.search(r"\bfinite\s+via\b", body))
    native = kind == "information_theorem"
    inline_bridge = locals().get("inline")
    return Registration(
        path=path,
        span=span,
        theorem=theorem,
        arena=arena,
        object_arena=object_arena,
        catalog=catalog,
        primitive=primitive,
        realization=realization,
        variation=variation,
        sensitivity=sensitivity,
        readout=readout,
        output_evidence=output,
        escape_from=escape_from,
        escape_from_source=escape_source,
        continuation=cont,
        source_record=source_record,
        finite_bridge=finite_bridge,
        inline_bridge=inline_bridge,
        native=native,
        occurrence=occurrence,
        source=source,
        finite_source=finite_source,
        options=options,
    )


def _top_level_marker(text: str, marker: str) -> int | None:
    depths = {"(": 0, "[": 0, "{": 0}
    i = 0
    while i < len(text):
        if text[i] in "\"'":
            i = _skip_string(text, i)
            continue
        if text.startswith(marker, i) and all(v == 0 for v in depths.values()):
            return i
        if text[i] in depths:
            depths[text[i]] += 1
        elif text[i] == ")" and depths["("]:
            depths["("] -= 1
        elif text[i] == "]" and depths["["]:
            depths["["] -= 1
        elif text[i] == "}" and depths["{"]:
            depths["{"] -= 1
        i += 1
    return None


def _identifier_after(body: str, keyword: str) -> str | None:
    m = re.search(rf"\b{re.escape(keyword)}\s+([^\s()]+)", body)
    return _clean_name(m.group(1)) if m else None


def _field_body(block: str, field: str) -> str:
    m = re.search(rf"\b{field}\s*:=\s*#?\[", block)
    if not m:
        return "#[]"
    start = block.find("[", m.start())
    try:
        end = _matching(block, start, "[", "]")
    except ValueError:
        return block[start:]
    return block[start : end + 1]


def _parse_root(path: Path, span: Span, block: str, options: dict[str, Any]) -> Root:
    root_match = re.search(r"\brootId\s*:=\s*`([^,\s}]+)", block)
    root_id = root_match.group(1) if root_match else ""
    companion = re.search(r"\bcompanionPrefix\s*:=\s*some\s+`([^,\s}]+)", block)
    return Root(
        path=path,
        span=span,
        root_id=root_id,
        expected=_field_body(block, "expected"),
        source=_field_body(block, "source"),
        baseline=_field_body(block, "baseline"),
        companion_prefix=companion.group(1) if companion else None,
    )


def _parse_template(path: Path, span: Span, body: str, options: dict[str, Any]) -> Template:
    m = re.search(r"register_information_template\s+([^\s]+)", body)
    name = _clean_name(m.group(1)) if m else ""
    version = int(re.search(r"\bconstructors\s+(\d+)", body).group(1)) if re.search(r"\bconstructors\s+(\d+)", body) else 1
    cm = re.search(r"\bconstructors\s+\d+\s*\[([^]]*)\]", body, re.S)
    constructors = [_clean_name(x) for x in cm.group(1).split(",") if x.strip()] if cm else []
    return Template(path, span, name, version, constructors, options)


def _parse_seal(path: Path, span: Span, body: str, options: dict[str, Any]) -> Seal:
    # The old seal owns the containing root module.
    module = ".".join(path.with_suffix("").parts)
    return Seal(path, span, module, options)


def parse_repository(repo: Path) -> tuple[list[Registration], list[Template], list[Root], list[Seal], list[tuple[Path, Span, str]]]:
    registrations: list[Registration] = []
    templates: list[Template] = []
    roots: list[Root] = []
    seals: list[Seal] = []
    notations: list[tuple[Path, Span, str]] = []
    for path in sorted((repo / "Reg").rglob("*.lean")):
        text = path.read_text(encoding="utf-8")
        events: list[tuple[int, str, re.Match[str]]] = []
        for regex, kind in ((_REG_RE, "reg"), (_TPL_RE, "template"), (_SEAL_RE, "seal"), (_ROOT_RE, "root")):
            events.extend((m.start(), kind, m) for m in regex.finditer(text))
        for m in re.finditer(r"(?m)^[ \t]*local\s+notation\b.*$", text):
            end = _line_end(text, m.start())
            notations.append((path, Span(m.start(), end), text[m.start():end]))
        events.sort(key=lambda item: item[0])
        for start, kind, match in events:
            if kind == "root":
                brace = text.find("{", start, match.end() + 1)
                try:
                    close = _matching(text, brace)
                except ValueError:
                    continue
                end = close + 1
                roots.append(_parse_root(path, Span(start, end), text[brace:end], _parse_options(text[:start])))
                continue
            end = _command_end(text, start, match.groupdict().get("indent", ""))
            body = text[start:end]
            options = _parse_options(text[:start])
            span = Span(start, end)
            if kind == "reg":
                # The source namespace is lexical context for short theorem
                # identifiers.  Use the nearest authored Reg namespace;
                # explicit `_root_` names were already normalized above.
                prefix = None
                for ns in re.finditer(r"(?m)^\s*namespace\s+([^\s]+)", text[:start]):
                    prefix = ns.group(1)
                if prefix and prefix.startswith("Reg."):
                    prefix = prefix[4:]
                registrations.append(_parse_registration(path, span, body, options, prefix))
            elif kind == "template":
                templates.append(_parse_template(path, span, body, options))
            else:
                seals.append(_parse_seal(path, span, body, options))
        # Three production roots are supplied by a support contract constant
        # (`run_cmd RootCatalogs.declare Support.contract`) rather than a
        # literal.  Keep an explicit root obligation for each such command;
        # the compiled input snapshot supplies its ordered rows.
        for match in re.finditer(r"(?m)^[ \t]*(?:run_cmd\s+)?(?:LeanInformationAudit\.)?RootCatalogs\.declare\s+([^\s{][^\n]*)", text):
            if "{" in match.group(1):
                continue
            if any(root.path == path and root.span.start == match.start() for root in roots):
                continue
            module = ".".join(path.with_suffix("").parts[path.with_suffix("").parts.index("Reg"):])
            end = _line_end(text, match.start())
            roots.append(Root(path, Span(match.start(), end), module, "#[]", "#[]", "#[]", None))
    return registrations, templates, roots, seals, notations
