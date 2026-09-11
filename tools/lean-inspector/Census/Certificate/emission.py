"""Emit pure Lean data from successful Lean query results, without importing targets."""

import json
import re

from Certificate.config import PREFIX_BITS, MAX_LEAF_IDS
from emission import parse_name_key


def statement_nat(wire):
    if not isinstance(wire, str) or not re.fullmatch(r"sha256:[0-9a-f]{64}", wire):
        raise ValueError("IE-C036 component=statement_id_format")
    value = int(wire[7:], 16)
    if "sha256:" + format(value, "064x") != wire:
        raise ValueError("IE-C036 component=statement_id_nat")
    return value


def validate_identity_inputs(rows, report_keys):
    """IE-C044 > IE-C035 > IE-C036, before Name decoding or literal packing."""
    seen = set()
    for _, _, wire in report_keys:
        if wire in seen:
            raise ValueError("IE-C044 component=frozen_keys duplicate statement identity")
        seen.add(wire)
    seen = set()
    for row in rows:
        wire = row["statement_id"]
        if wire in seen:
            raise ValueError("IE-C035 DuplicateAnalysisDisposition statement_id=" + wire)
        seen.add(wire)
    for _, _, wire in report_keys:
        statement_nat(wire)
    for row in rows:
        statement_nat(row["statement_id"])


def string(value):
    return json.dumps(value, ensure_ascii=False)


def name(value):
    if value == ["anonymous"]:
        return "Lean.Name.anonymous"
    tag, parent, part = value
    if tag == "str":
        return f"(Lean.Name.str {name(parent)} {string(part)})"
    if tag == "num" and isinstance(part, int):
        return f"(Lean.Name.num {name(parent)} {part})"
    raise ValueError("invalid structured Lean name")


def pack_ids(values):
    """Least significant digit first; arity is emitted separately, including zero."""
    if not 1 <= len(values) <= 100 or any(not 0 <= value < 2 ** 256 for value in values):
        raise ValueError("IE-C036 component=statement_id_nat or chunk_arity")
    packed = 0
    for value in reversed(values):
        packed = (packed << 256) | value
    return packed


def chunked_keys(declaration, keys, public=False):
    # Hex numeral syntax is still a Nat literal in Lean. It avoids decimal
    # conversion limits for these 25,600-bit values; no id is a JSON number.
    ordered = sorted(statement_nat(wire) for _, wire in keys)
    chunks = []
    definitions = []
    for start in range(0, len(ordered), 100):
        chunk = f"{declaration}.chunk{start // 100}"
        values = ordered[start:start + 100]
        chunks.append(f"decodeIds {len(values)} {chunk}")
        definitions.append(f"noncomputable def {chunk} : Nat := 0x{pack_ids(values):x}\n")
    definitions.append(("public " if public else "") + f"noncomputable def {declaration} : List Nat := "
                       + "List.flatten [" + ", ".join(chunks) + "]\n")
    return "".join(definitions)


def range_tree(rows, report_keys, b=PREFIX_BITS, max_leaf_ids=MAX_LEAF_IDS):
    if not isinstance(b, int) or not 0 <= b <= 256 or max_leaf_ids < 1:
        raise ValueError("invalid prefix bits or leaf bound")
    inventory = [(row["theorem_name"], row["statement_id"]) for row in rows]
    report = [(parse_name_key(key), wire) for _, key, wire in report_keys]
    nodes = {}

    def split(inv, rep, depth, prefix):
        module = f"CensusRun.Range{depth}_{prefix}"
        node = dict(module=module, inv=inv, rep=rep, depth=depth, prefix=prefix, children=[])
        if depth < b or max(len(inv), len(rep)) > max_leaf_ids:
            if depth == 256:
                raise ValueError("IE-C035 unsplittable duplicate identity range")
            cut = (prefix * 2 + 1) << (255 - depth)
            def halves(keys):
                return ([key for key in keys if statement_nat(key[1]) < cut],
                        [key for key in keys if statement_nat(key[1]) >= cut])
            il, ir = halves(inv)
            rl, rr = halves(rep)
            node["children"] = [split(il, rl, depth + 1, prefix * 2),
                                split(ir, rr, depth + 1, prefix * 2 + 1)]
            # Internal nodes export only their two references and scalar metadata.
            node["inv"], node["rep"] = [], []
        node["count"] = len(inv)
        nodes[module] = node
        return module

    split(inventory, report, 0, 0)
    return nodes


def range_source(node, scope=None):
    scope = scope or node["module"]
    k, b = node["prefix"], node["depth"]
    lo, hi = k << (256 - b), (k + 1) << (256 - b)
    children = node["children"]
    header = "module\n" + ("".join(f"public import {child}\n" for child in children)
        if children else "public import LeanInformationAudit.Census.Certificate\n")
    body = header + "open LeanInformationAudit\n"
    body += f"@[expose] public def {scope}.n : Nat := {node['count']}\n"
    body += f"@[expose] public def {scope}.k : Nat := {k}\n"
    body += f"@[expose] public def {scope}.b : Nat := {b}\n"
    body += f"@[expose] public def {scope}.leaf : Nat := {0 if children else 1}\n"
    if children:
        left, right = children
        for side in ["manifestKeys", "reportKeys"]:
            body += f"@[expose] public noncomputable def {scope}.{side} : List Nat := List.append {left}.{side} {right}.{side}\n"
        proof = f"range_join {left}.facts {right}.facts (by decide +kernel)"
    else:
        body += chunked_keys(scope + ".manifestKeys", node["inv"], public=True)
        body += chunked_keys(scope + ".reportKeys", node["rep"], public=True)
        body += f"public theorem {scope}.ascending : strictlyAscending {scope}.manifestKeys = true := by decide +kernel\n"
        body += f"public theorem {scope}.range : inRange {k} {b} {scope}.manifestKeys = true := by decide +kernel\n"
        body += f"public theorem {scope}.length : {scope}.manifestKeys.length = {scope}.n := by decide +kernel\n"
        body += f"public theorem {scope}.equality : {scope}.manifestKeys = {scope}.reportKeys := by rfl\n"
        proof = f"⟨{scope}.ascending, (by decide +kernel), {scope}.length, {scope}.equality⟩"
    body += f"public theorem {scope}.facts : RangeCertificate {lo} {hi} {scope}.manifestKeys {scope}.n {scope}.reportKeys := {proof}\n"
    return body


def bucket_sources(rows, report_keys, b=PREFIX_BITS, max_leaf_ids=MAX_LEAF_IDS):
    return {module: range_source(node) for module, node in range_tree(rows, report_keys, b, max_leaf_ids).items()
            if module != "CensusRun.Range0_0"}


def manifest_source(rows, report_keys, head, digest, root, b=PREFIX_BITS, max_leaf_ids=MAX_LEAF_IDS):
    root_name = ["anonymous"]
    for part in root.split("."):
        root_name = ["str", root_name, part]
    tree = range_tree(rows, report_keys, b, max_leaf_ids)
    scope = root.rsplit(".", 1)[0] if "." in root else root
    body = range_source(tree["CensusRun.Range0_0"], scope)
    return (body + f"@[expose] public def {scope}.prefixBits : Nat := {b}\n"
        + f"@[expose] public def {scope}.leafBound : Nat := {max_leaf_ids}\n"
        + f"@[expose] public noncomputable def {scope}.manifest : CensusKeyManifest :=\n"
        + f"  {{ headSha := {string(head)}, reportSha256 := {string(digest)},\n"
        + f"    censusRoot := {name(root_name)}, keys := {scope}.manifestKeys }}\n")


def write_manifest(directory, rows, report_keys, head, digest, root, b=PREFIX_BITS):
    validate_identity_inputs(rows, report_keys)
    for module, source in bucket_sources(rows, report_keys, b).items():
        write_module(directory, module, source)
    return write_module(directory, root, manifest_source(rows, report_keys, head, digest, root, b))


def write_module(directory, module, contents):
    path = directory.joinpath(*module.split(".")).with_suffix(".lean")
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(contents, encoding="utf-8")
    return path
