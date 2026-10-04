#!/usr/bin/env python3
"""Compare raw v2 registration verdicts using Python 3.12+ (standard library).

Usage: reg-verdict-compare.py BEFORE AFTER [--mapping FILE|-]
       [--before-seal ROOT FILE] [--after-seal ROOT FILE]

The mapping is UTF-8 JSON Lines, one exact field relocation per line:
{"schema":"reg-verdict-relocations-v1","field":"root",
 "before":"Reg.Example","after":"Reg.Catalogs.Example"}
Allowed roles are the four movable occurrence fields, module, source_path and
declaration_name. Names are opaque Lean display strings, including private and
quoted components. No prefix replacement or inferred relocation is performed.
Unlisted values retain their identity. Endpoints must exist in their respective
reports and the effective mapping must be injective, including unmoved values.

Each side validates its own versions; compatibility versions may differ. This
tool compares report data, without loading Lean or rerunning either judge.
Full record/certificate differences are printed, including identity changes.
Exit 0 means agreement within the checked report scope, 1 means a verdict or
semantic difference, and 2 means an input/schema/mapping/bijection error.
Without complete explicit per-root seal artifacts, seal and overall remain
not_checked even when the report comparison exits 0. D5 bytes, producer success
and the check-delta selection for DTR-Unregistered require separate validation.
All results go to stdout; the program creates no files.
"""

from __future__ import annotations

import argparse
from collections import Counter
from dataclasses import dataclass, field
import json
from pathlib import Path, PurePosixPath
import re
import sys


KEY_FIELDS = ("root", "registration_module", "theorem", "object_arena", "catalog")
MOVABLE = set(KEY_FIELDS) - {"theorem"}
MAP_FIELDS = MOVABLE | {"module", "source_path", "declaration_name"}
SEAL_SUFFIXES = {"__information_unit", "__primitive_realization", "__information_catalog",
                 "__lowers_escape", "__trivial_in_catalog", "__catalog_irredundant",
                 "__catalog_redundant", "__escape_enriched", "__zero_state_enumeration",
                 "__catalog_suite", "__system_catalog_irredundant",
                 "__system_catalog_not_irredundant"}
RECORD_FIELDS = {"key", "registration_source_path", "statement_identity", "binding_source_path",
                 "state", "diagnostic", "certificate", "unit_name", "realization_name",
                 "escape_from", "escape_continues", "bridge_kind"}
CERT_FIELDS = {"key", "evidence_ref", "plan_identity", "descriptor_identity", "actual_identity",
               "argument_inputs", "extraction_inputs"}


class InputError(ValueError):
    pass


def require(condition, message):
    if not condition:
        raise InputError(message)


def fields(value, required, label, optional=()):
    require(isinstance(value, dict), f"{label}: object required")
    require(set(required) <= value.keys() <= set(required) | set(optional),
            f"{label}: missing or unknown fields")


def string(value, label, nullable=False):
    if value is None and nullable:
        return value
    require(isinstance(value, str) and bool(value), f"{label}: nonempty string required")
    return value


def array(value, label):
    require(isinstance(value, list), f"{label}: array required (null is not empty)")
    return value


def natural(value, label, maximum=None):
    require(type(value) is int and value >= 0 and (maximum is None or value <= maximum),
            f"{label}: nonnegative integer required")
    return value


def digest(value, label, tagged=False, empty=False):
    if empty and value == "":
        return value
    require(isinstance(value, str) and re.fullmatch(
        r"sha256:[0-9a-f]{64}" if tagged else r"[0-9a-f]{64}", value) is not None,
        f"{label}: lowercase SHA-256 required")
    return value


def unique(values, label):
    require(len(values) == len(set(values)), f"{label}: duplicate/ambiguous occurrence")


def read_key(value):
    fields(value, KEY_FIELDS, "occurrence key")
    return tuple(string(value[f], f"key.{f}") for f in KEY_FIELDS)


def path_module(value):
    string(value, "source path")
    path = PurePosixPath(value)
    require(not path.is_absolute() and ".." not in path.parts and "\\" not in value
            and str(path) == value and path.suffix == ".lean", "noncanonical Lean source path")
    return value[:-5].replace("/", ".")


def strict_object(pairs):
    result = {}
    for name, value in pairs:
        require(name not in result, f"duplicate JSON member: {name}")
        result[name] = value
    return result


def reject_constant(value):
    raise InputError(f"nonfinite JSON number: {value}")


def load_json(text):
    return json.loads(text, object_pairs_hook=strict_object, parse_constant=reject_constant)


def read_json(path):
    with Path(path).open(encoding="utf-8") as source:
        return load_json(source.read())


def validate_slots(row):
    origin, continuation = row["escape_from"], row["escape_continues"]
    if origin is not None:
        fields(origin, {"name", "type_identity", "object_identity"}, "escape_from")
        string(origin["name"], "escape_from.name")
        for f in ("type_identity", "object_identity"):
            digest(origin[f], f"escape_from.{f}")
    if continuation is not None:
        fields(continuation, {"kind", "declaration_name", "statement_identity", "chain_name"},
               "escape_continues")
        if continuation["kind"] == "open":
            require(all(continuation[f] is None for f in
                        ("declaration_name", "statement_identity", "chain_name")),
                    "open continuation cannot carry a certificate")
        else:
            require(continuation["kind"] in ("witness", "empty"), "unknown escape continuation")
            string(continuation["declaration_name"], "continuation declaration")
            string(continuation["chain_name"], "continuation chain")
            digest(continuation["statement_identity"], "continuation statement")


def expr_path(value):
    array(value, "source expression path")
    require(1 <= len(value) <= 256 and all(x in ("fn", "arg", "domain", "body", "type", "value")
                                         for x in value), "invalid source expression path")
    return value


def validate_source_binding(value, row):
    fields(value, {"source_owner", "source_name", "source_type_identity", "telescope_size",
                   "level_count", "coordinates", "coordinate_paths", "readouts", "registration_identity"},
           "source_binding", {"definition_entry", "finite_projection"})
    string(value["source_owner"], "source owner")
    require(value["source_owner"].startswith("D5.") and value["source_name"] == row["key"]["theorem"]
            and value["source_type_identity"] == row["statement_identity"],
            "source binding retargets occurrence")
    digest(value["source_type_identity"], "source type")
    digest(value["registration_identity"], "registration identity")
    for f in ("telescope_size", "level_count"):
        natural(value[f], f, 64)
    coords = array(value["coordinates"], "coordinates")
    for x in coords:
        natural(x, "coordinate", 255)
    require(len(coords) <= 64 and all(a < b for a, b in zip(coords, coords[1:])),
            "source coordinate order/count")
    coord_paths = array(value["coordinate_paths"], "coordinate paths")
    require(len(coords) == len(coord_paths), "source coordinate/path count differs")
    for p in coord_paths:
        expr_path(p)
    readouts = array(value["readouts"], "readouts")
    require(1 <= len(readouts) <= 64, "source role count")
    paths = []
    for r in readouts:
        required = {"path", "state_binder", "scope_size", "scope_paths", "occurrence_identity"}
        extra = {"function_operand"} if "function_operand" in r else (
            {"state_operand", "boolean_predicate"} if "state_operand" in r else set())
        fields(r, required | extra, "readout")
        p = expr_path(r["path"])
        paths.append(tuple(p))
        digest(r["occurrence_identity"], "readout identity")
        size = natural(r["scope_size"], "scope_size", 256)
        binder = natural(r["state_binder"], "state_binder", 255)
        scopes = array(r["scope_paths"], "scope paths")
        operand = "function_operand" in r or "state_operand" in r
        require(size == len(scopes) and (binder == 0 and (not coords or coords[-1] < size)
                if operand else binder < size and (not coords or coords[-1] < binder)),
                "source scope bounds")
        for i, scope in enumerate(scopes):
            expr_path(scope)
            require(scope[-1] == "body" and p[:len(scope)] == scope
                    and (i == 0 or len(scopes[i - 1]) < len(scope)
                         and scope[:len(scopes[i - 1])] == scopes[i - 1]),
                    "invalid source lexical ancestor")
        require(all(c < size and coord_paths[i] == scopes[c] for i, c in enumerate(coords)),
                "source captured coordinate differs")
        if "function_operand" in r:
            require(r["function_operand"] is True, "invalid function operand")
        if "state_operand" in r:
            require(all(x in ("fn", "arg") for x in expr_path(r["state_operand"]))
                    and type(r["boolean_predicate"]) is bool, "invalid state operand")
    unique(paths, "source readouts")
    if "definition_entry" in value:
        d = value["definition_entry"]
        fields(d, {"path", "reference_identity", "owner", "name", "type_identity", "body_identity"},
               "source definition")
        require(d["path"] in ([], ["arg"]), "invalid definition entry path")
        for f in ("reference_identity", "type_identity", "body_identity"):
            digest(d[f], f"definition.{f}")
        require(d["owner"] == value["source_owner"], "definition owner differs")
        string(d["name"], "definition name")
    if "finite_projection" in value:
        fields(value["finite_projection"], {"family_arena", "bridge"}, "finite projection")
        for f in ("family_arena", "bridge"):
            string(value["finite_projection"][f], f)


def validate_record(row, module_path):
    fields(row, RECORD_FIELDS, "binding record")
    k = read_key(row["key"])
    require(path_module(row["registration_source_path"]) == row["key"]["registration_module"],
            "registration module/source owner differs")
    digest(row["statement_identity"], "statement_identity")
    for f in ("unit_name", "realization_name"):
        string(row[f], f)
    for f in ("binding_source_path", "diagnostic"):
        string(row[f], f, nullable=True)
    require(row["state"] in ("undeclared", "declared_unresolved", "declared_validated"),
            "unknown binding state")
    require(row["bridge_kind"] in ("legacy", "forward", "witness", "source-equivalence"),
            "unknown bridge_kind")
    validate_slots(row)
    cert = row["certificate"]
    if row["state"] == "declared_validated":
        fields(cert, CERT_FIELDS | ({"source_binding"} if row["bridge_kind"] == "source-equivalence" else set()),
               "certificate")
        require(read_key(cert["key"]) == k and row["diagnostic"] is None,
                "copied certificate or contradictory result")
        for f in ("evidence_ref", "plan_identity", "descriptor_identity", "actual_identity"):
            digest(cert[f], f"certificate.{f}")
        for f in ("argument_inputs", "extraction_inputs"):
            inputs = array(cert[f], f)
            names = []
            for item in inputs:
                fields(item, {"name", "owner", "type_identity", "body_identity"}, f)
                names.append(string(item["name"], "input name"))
                string(item["owner"], "input owner")
                digest(item["type_identity"], "input type")
                digest(item["body_identity"], "input body", empty=True)
            unique(names, f)
        if row["bridge_kind"] == "source-equivalence":
            validate_source_binding(cert["source_binding"], row)
            origin = row["escape_from"]
            require(origin is not None and origin["name"] == row["key"]["theorem"]
                    and origin["type_identity"] == row["statement_identity"]
                    and origin["object_identity"] == cert["actual_identity"]
                    and row["escape_continues"] is not None
                    and row["escape_continues"]["kind"] == "open", "source slots differ from binding")
    else:
        require(cert is None, "unresolved/undeclared cannot carry a certificate")
    if row["state"] == "undeclared":
        require(row["binding_source_path"] is None and module_path == row["registration_source_path"],
                "undeclared record has wrong owner")
    else:
        require(row["binding_source_path"] == module_path, "binding producer owner differs")
        if row["state"] == "declared_unresolved":
            require(row["diagnostic"] is not None, "unresolved diagnostic missing")
    return k


def generated_seal(name):
    suffix = name.rsplit(".", 1)[-1]
    return suffix in SEAL_SUFFIXES or suffix.startswith("__kernel_collision_")


@dataclass
class Report:
    records: dict = field(default_factory=dict)
    modules: dict = field(default_factory=dict)
    declarations: dict = field(default_factory=dict)
    seals: dict = field(default_factory=dict)
    support: dict = field(default_factory=lambda: {f: set() for f in MAP_FIELDS})
    versions: set = field(default_factory=set)


def read_report(path):
    raw = read_json(path)
    fields(raw, {"schema", "modules"}, "raw report")
    require(raw["schema"] == "stratalint-raw-lean-report-v2", "unsupported raw report schema")
    report = Report()
    for m in array(raw["modules"], "modules"):
        fields(m, {"module", "source_path", "source_sha256", "imports", "declarations",
                   "information_registration_errors", "information_templates"},
               "module", {"utility_refutation"})
        name = string(m["module"], "module name")
        require(name not in report.modules, f"duplicate module: {name}")
        require(path_module(m["source_path"]) == name, "module/source owner differs")
        digest(m["source_sha256"], "source hash", tagged=True)
        imports = [string(x, "import") for x in array(m["imports"], "imports")]
        unique(imports, "imports")
        errors = [string(x, "registration error") for x in
                  array(m["information_registration_errors"], "registration errors")]
        unique(errors, "registration errors")
        report.modules[name] = {"source_path": m["source_path"], "errors": errors}
        report.support["module"].add(name)
        report.support["source_path"].add(m["source_path"])
        for d in array(m["declarations"], "declarations"):
            fields(d, {"name", "name_key", "kind", "include_in_statement", "axioms",
                       "type_sha256", "statement_id"}, "declaration")
            dn = string(d["name"], "declaration name")
            string(d["name_key"], "name_key")
            require(d["kind"] in ("axiom", "def", "theorem", "opaque", "quotient",
                                  "constructor", "recursor", "inductive"), "unknown declaration kind")
            require(type(d["include_in_statement"]) is bool, "invalid declaration visibility")
            for f in ("type_sha256", "statement_id"):
                digest(d[f], f, tagged=True)
            unique([string(x, "axiom") for x in array(d["axioms"], "axioms")], "axioms")
            require((name, dn) not in report.declarations, f"duplicate declaration in {name}: {dn}")
            report.declarations[name, dn] = d["kind"]
            report.support["declaration_name"].add(dn)
            if generated_seal(dn):
                report.seals[name, dn] = d["kind"]
        e = m["information_templates"]
        fields(e, {"schema_version", "compatibility_version", "inventory", "registered", "records"},
               "information_templates")
        require(type(e["schema_version"]) is int and e["schema_version"] == 1,
                "unsupported information_templates schema")
        require(natural(e["compatibility_version"], "compatibility_version") > 0,
                "compatibility_version must be positive")
        report.versions.add(e["compatibility_version"])
        lists = {}
        for f in ("inventory", "registered"):
            lists[f] = [read_key(x) for x in array(e[f], f)]
            unique(lists[f], f)
        rows = array(e["records"], "records")
        keys = [validate_record(row, m["source_path"]) for row in rows]
        unique(keys, "records")
        require(set(lists["inventory"]) == set(lists["registered"]) == set(keys),
                f"inventory/registered/records bijection differs in {name}")
        for k, row in zip(keys, rows):
            require(k not in report.records, "duplicate occurrence owner across modules")
            report.records[k] = row
            for f in MOVABLE:
                report.support[f].add(row["key"][f])
    require(len(report.versions) <= 1, "mixed compatibility versions within one report")
    return report


class Relocations:
    def __init__(self, path, before, after):
        self.rules = {f: {} for f in MAP_FIELDS}
        if path is not None:
            if path == "-":
                lines = sys.stdin
                self.read(lines)
            else:
                with Path(path).open(encoding="utf-8") as lines:
                    self.read(lines)
        for f, rules in self.rules.items():
            for old, new in rules.items():
                require(old in before.support[f] and new in after.support[f],
                        f"mapping endpoint missing for {f}: {old} -> {new}")
            mapped = [rules.get(x, x) for x in sorted(before.support[f])]
            unique(mapped, f"noninjective effective {f} mapping")

    def read(self, lines):
        for i, line in enumerate(lines, 1):
            if not line.strip():
                continue
            row = load_json(line)
            fields(row, {"schema", "field", "before", "after"}, f"mapping line {i}")
            require(row["schema"] == "reg-verdict-relocations-v1", "unsupported mapping schema")
            f = row["field"]
            require(f in MAP_FIELDS, f"forbidden mapping role: {f}")
            old, new = string(row["before"], "mapping before"), string(row["after"], "mapping after")
            require(old not in self.rules[f], f"duplicate mapping source for {f}: {old}")
            self.rules[f][old] = new
            unique(list(self.rules[f].values()), f"noninjective {f} mapping")

    def get(self, role, value):
        return self.rules[role].get(value, value)

    def key(self, key):
        return tuple(self.get(f, v) if f in MOVABLE else v for f, v in zip(KEY_FIELDS, key))


def dtr_projection(row):
    # DeclaredTemplateBindingRule.Finding: slots precede the binding-state switch.
    if row["escape_from"] is None or row["escape_continues"] is None or row["state"] == "undeclared":
        code = "DTR-Undeclared"
    elif row["state"] == "declared_validated" and row["certificate"]["evidence_ref"] is not None:
        code = "DTR-Declared"
    else:
        code = "DTR-Evidence"
    return {"code": code, "admission_effect": "Observe"}


def walk_diff(before, after, path=()):
    if type(before) is not type(after):
        yield path, before, after
    elif isinstance(before, dict):
        for key in sorted(before.keys() | after.keys()):
            if key not in before or key not in after:
                yield path + (key,), before.get(key), after.get(key)
            else:
                yield from walk_diff(before[key], after[key], path + (key,))
    elif isinstance(before, list):
        for i in range(max(len(before), len(after))):
            if i >= len(before) or i >= len(after):
                yield path + (str(i),), before[i] if i < len(before) else None, after[i] if i < len(after) else None
            else:
                yield from walk_diff(before[i], after[i], path + (str(i),))
    elif before != after:
        yield path, before, after


def pointer(path):
    return "/" + "/".join(str(x).replace("~", "~0").replace("/", "~1") for x in path)


def difference(path, old, new, gate, category, **context):
    return dict(context, path=pointer(path), before=old, after=new, gate=gate, category=category)


def record_rule(path, old, new, mapping):
    if path[0] == "key" or path[:2] == ("certificate", "key"):
        role = path[-1]
        return mapping.get(role, old) != new if role in MOVABLE else old != new, "relocation"
    if path[0] in ("registration_source_path", "binding_source_path"):
        return mapping.get("source_path", old) != new, "relocation"
    if path[0] in ("unit_name", "realization_name") or path in (
            ("escape_from", "name"), ("escape_continues", "declaration_name"),
            ("escape_continues", "chain_name")):
        return mapping.get("declaration_name", old) != new, "relocation"
    if path == ("diagnostic",):
        return False, "diagnostic"
    if path == ("escape_from", "object_identity"):
        return False, "identity"
    if path[0] == "certificate" and len(path) > 1:
        if path[1] in CERT_FIELDS - {"key"}:
            return False, "identity"
        if path[1] == "source_binding":
            if path[-1] in ("registration_identity", "occurrence_identity", "reference_identity",
                             "type_identity", "body_identity"):
                return False, "identity"
            if path[-1] in ("source_owner", "owner"):
                return mapping.get("module", old) != new, "relocation"
            if path[-1] in ("name", "family_arena", "bridge"):
                return mapping.get("declaration_name", old) != new, "relocation"
    return True, "semantic"


def read_seals(arguments, report):
    products = {}
    for root, path in arguments:
        string(root, "seal root")
        require(root in report.modules and root not in products, "seal root missing or duplicate")
        raw = read_json(path)
        fields(raw, {"schema", "catalog_mode", "arenas"}, "seal artifact")
        require(raw["schema"] == "lean-intrinsic-information-escape-seal"
                and raw["catalog_mode"] == "single-compilation-leave-one-out", "unsupported seal schema/mode")
        arena_ids = []
        verdicts, certificates = [], []
        def reference(name):
            string(name, "seal declaration reference")
            require((root, name) in report.declarations, f"seal declaration missing at root {root}: {name}")
        def rate(value):
            fields(value, {"numerator", "denominator"}, "seal rate")
            for f in value:
                natural(value[f], f)
        for a in array(raw["arenas"], "seal arenas"):
            fields(a, {"arena", "catalog", "verdict", "verdict_certificate", "state_card",
                       "off_diagonal_pair_count", "full_escape_count", "full_escape_rate", "theorems"}, "seal arena")
            arena_ids.append((string(a["arena"], "arena"), string(a["catalog"], "catalog")))
            reference(a["catalog"])
            reference(a["verdict_certificate"])
            verdicts.append(a["verdict_certificate"])
            require(a["verdict"] in ("irredundant", "redundant"), "unknown seal verdict")
            for f in ("state_card", "off_diagonal_pair_count", "full_escape_count"):
                natural(a[f], f)
            rate(a["full_escape_rate"])
            for i, row in enumerate(array(a["theorems"], "seal theorems")):
                fields(row, {"theorem", "unit", "index", "primitive_count", "primitive_axes",
                             "primitive_kernel_address", "unique_capture_count", "full_escape_count",
                             "without_escape_count", "unique_capture_by_role_signature", "gain_rate",
                             "lowers_escape", "certificate", "proof_method"}, "seal member")
                string(row["theorem"], "seal theorem")
                reference(row["unit"])
                reference(row["certificate"])
                certificates.append(row["certificate"])
                require(row["index"] == i, "seal member index/order differs")
                for f in ("index", "primitive_count", "unique_capture_count", "full_escape_count", "without_escape_count"):
                    natural(row[f], f)
                for x in array(row["primitive_axes"], "primitive axes"):
                    string(x, "primitive axis")
                require(isinstance(row["primitive_kernel_address"], str), "kernel address must be string")
                require(isinstance(row["unique_capture_by_role_signature"], dict), "role signature histogram required")
                for x in row["unique_capture_by_role_signature"].values():
                    natural(x, "signature count")
                rate(row["gain_rate"])
                require(type(row["lowers_escape"]) is bool, "lowers_escape must be Boolean")
                string(row["proof_method"], "proof_method")
        unique(arena_ids, "seal arenas")
        unique(verdicts, "seal verdict certificates")
        unique(certificates, "seal member certificates")
        expected_verdicts = {name for owner, name in report.seals if owner == root
                             and name.endswith((".__catalog_irredundant", ".__catalog_redundant"))}
        expected_members = {name for owner, name in report.seals if owner == root
                            and name.endswith((".__lowers_escape", ".__trivial_in_catalog"))}
        require(bool(expected_verdicts) and set(verdicts) == expected_verdicts
                and set(certificates) == expected_members,
                "seal artifact does not cover the root's verdict/member declarations")
        products[root] = raw
    return products


def compare(before, after, mapping, before_seals, after_seals):
    aligned = {mapping.key(k): k for k in before.records}
    require(len(aligned) == len(before.records), "ambiguous mapped occurrence")
    missing = sorted(aligned.keys() - after.records.keys())
    extra = sorted(after.records.keys() - aligned.keys())
    require(not missing and not extra,
            f"occurrence bijection differs: missing={len(missing)} extra={len(extra)}; "
            f"missing_keys={missing[:3]} extra_keys={extra[:3]}")
    differences = []
    for target, source in sorted(aligned.items()):
        old, new = before.records[source], after.records[target]
        context = {"before_key": old["key"], "after_key": new["key"]}
        for path, a, b in walk_diff(old, new):
            gate, category = record_rule(path, a, b, mapping)
            differences.append(difference(path, a, b, gate, category, **context))
        if dtr_projection(old) != dtr_projection(new):
            differences.append(difference(("dtr_projection",), dtr_projection(old), dtr_projection(new),
                                          True, "semantic", **context))
    # The report contains kernel-published seal declarations, not numerical seals.
    mapped_seals = {(mapping.get("module", owner), mapping.get("declaration_name", name)): (owner, name)
                    for owner, name in before.seals}
    require(len(mapped_seals) == len(before.seals), "ambiguous mapped seal declaration")
    for target in sorted(mapped_seals.keys() | after.seals.keys()):
        source = mapped_seals.get(target)
        old = before.seals.get(source) if source else None
        new = after.seals.get(target)
        if old != new:
            differences.append(difference(("seal_declarations", *target), old, new, True, "semantic"))
        elif source != target:
            differences.append(difference(("seal_declarations", *target), list(source), list(target), False, "relocation"))
    errors = []
    for owner, module in sorted(before.modules.items()):
        target = mapping.get("module", owner)
        new = after.modules.get(target)
        old_errors, new_errors = module["errors"], new["errors"] if new else []
        if old_errors != new_errors:
            errors.append(dict(before_module=owner, after_module=target, before=old_errors, after=new_errors))
    mapped_modules = {mapping.get("module", owner) for owner in before.modules}
    for owner in sorted(after.modules.keys() - mapped_modules):
        if after.modules[owner]["errors"]:
            errors.append(dict(before_module=None, after_module=owner, before=[], after=after.modules[owner]["errors"]))
    seals_left = {mapping.get("module", root): (root, artifact) for root, artifact in before_seals.items()}
    require(seals_left.keys() == after_seals.keys(), "seal product roots differ")
    for root, (_, old) in sorted(seals_left.items()):
        for path, a, b in walk_diff(old, after_seals[root]):
            role = "declaration_name" if path[-1] in ("unit", "catalog", "certificate", "verdict_certificate") else (
                "object_arena" if path[-1] == "arena" else None)
            gate = mapping.get(role, a) != b if role else True
            differences.append(difference(("seal_products", root, *path), a, b, gate,
                                          "relocation" if role else "semantic"))
    required_roots = {owner for owner, name in before.seals
                      if name.endswith((".__catalog_irredundant", ".__catalog_redundant"))}
    required_after = {owner for owner, name in after.seals
                      if name.endswith((".__catalog_irredundant", ".__catalog_redundant"))}
    seal_checked = bool(before_seals) and required_roots <= before_seals.keys() and required_after <= after_seals.keys()
    inconsistent = any(x["gate"] for x in differences) or bool(errors)
    return dict(schema="reg-verdict-comparison-v1", result="different" if inconsistent else "consistent",
                overall="different" if inconsistent else ("consistent" if seal_checked else "not_checked"),
                seal="checked" if seal_checked else "not_checked", matched_records=len(aligned),
                before_states=dict(sorted(Counter(r["state"] for r in before.records.values()).items())),
                after_states=dict(sorted(Counter(r["state"] for r in after.records.values()).items())),
                compatibility_versions={"before": sorted(before.versions), "after": sorted(after.versions)},
                differences=differences, information_registration_errors=errors,
                seal_declarations={"before": len(before.seals), "after": len(after.seals),
                                   "matched": len(mapped_seals.keys() & after.seals.keys())},
                seal_roots={"before": sorted(before_seals), "after": sorted(after_seals),
                            "missing_before": sorted(required_roots - before_seals.keys()),
                            "missing_after": sorted(required_after - after_seals.keys())},
                coverage={"records": "checked", "dtr_occurrence_projection": "checked",
                          "dtr_unregistered_selection": "not_checked", "d5_bytes": "not_checked",
                          "producer_success": "not_checked"}), int(inconsistent)


class Parser(argparse.ArgumentParser):
    def error(self, message):
        raise InputError(message)


def main(argv=None):
    try:
        parser = Parser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
        parser.add_argument("before")
        parser.add_argument("after")
        parser.add_argument("--mapping", help="JSON Lines field relocations; - reads stdin")
        parser.add_argument("--before-seal", nargs=2, action="append", default=[], metavar=("ROOT", "FILE"))
        parser.add_argument("--after-seal", nargs=2, action="append", default=[], metavar=("ROOT", "FILE"))
        args = parser.parse_args(argv)
        before, after = read_report(args.before), read_report(args.after)
        mapping = Relocations(args.mapping, before, after)
        left_seals, right_seals = read_seals(args.before_seal, before), read_seals(args.after_seal, after)
        result, code = compare(before, after, mapping, left_seals, right_seals)
    except (ValueError, OSError, UnicodeError, TypeError, KeyError, IndexError, RecursionError) as error:
        result = dict(schema="reg-verdict-comparison-v1", result="input_error", overall="not_checked",
                      error=str(error))
        code = 2
    print(json.dumps(result, ensure_ascii=False, sort_keys=True, separators=(",", ":"), allow_nan=False))
    return code


if __name__ == "__main__":
    sys.exit(main())
