#!/usr/bin/env python3
"""Reproduce this report from the current raw report and captured kernel edges.

This is evidence authoring code, not an admission judge. Proof-shape assessments
are explicit metadata. Full Lean names are the join key; D5 module paths are not
assumed to be Lean namespaces.
"""
import hashlib
import json
from pathlib import Path
import subprocess

ROOT = Path(__file__).resolve().parents[3]
OUT = Path(__file__).resolve().parent
RAW = ROOT / ".lake/build/stratalint/raw-lean-report.json"
raw_bytes = RAW.read_bytes()
modules = {m["module"]: m for m in json.loads(raw_bytes)["modules"]}
base = "D5.S3.ConceptDynamics.ZfcTermRewriting."
upstream = "https://github.com/FormalizedFormalLogic/Foundation/blob/30a16ffa93d79d73ab4d02427fa00f50e039bf29/Foundation/Syntax/Predicate/Rew.lean"

def compact_maps(data):
    """Keep each complete record on one line within the 1000-line data cap."""
    def atom(value):
        return json.dumps(value, ensure_ascii=False, separators=(",", ":"))
    fields = []
    for key, value in data.items():
        if isinstance(value, dict):
            encoded = "{\n" + ",\n".join("    " + atom(k) + ":" + atom(v) for k, v in value.items()) + "\n  }"
        elif isinstance(value, list):
            encoded = "[\n" + ",\n".join("    " + atom(v) for v in value) + "\n  ]"
        else:
            encoded = atom(value)
        fields.append("  " + atom(key) + ":" + encoded)
    return "{\n" + ",\n".join(fields) + "\n}\n"

# Full declaration name, local source range, upstream range, declared shape,
# concrete API purpose. These are source observations, not a machine verdict.
source_rows = [
    ("Rew.fixitr_bvar", "32-36", "639-643", "bind-only", "Bound-index law for the existing finite fixitr API."),
    ("Rew.fixitr_fvar", "38-52", "645-659", "bind-only", "Free-index law for the existing finite fixitr API."),
    ("Semiterm.rew_eq_of_funEqOn", "62-72", "715-725", "bind-only", "Term rewriting extensionality on the term's actual free-variable support."),
    ("Semiterm.lMap_bind", "79-81", "732-734", "bind-only", "Transport term binding through the existing language-map API."),
    ("Semiterm.lMap_map", "83-85", "736-738", "bind-only", "Transport bound/free-variable maps through language maps."),
    ("Semiterm.lMap_bShift", "87-88", "740-741", "bind-only", "Transport binder shifting through language maps."),
    ("Semiterm.fvar?_rew", "92-106", "756-770", "bind-only", "Free-variable provenance law used by the fvar_rew document selector."),
    ("Semiterm.fvar?_bShift", "108-110", "772-774", "bind-only", "Free-variable support law used by the fvar_bShift document selector."),
    ("Semiterm.toEmpty", "112-120", "776-784", "definition", "Retype a term with empty support as ClosedSemiterm, retaining its support proof."),
    ("Semiterm.emb_toEmpty", "122-124", "786-788", "bind-only", "Recovery law for the toEmpty conversion API."),
    ("Rewriting", "137-141", "808-812", "class", "Indexed formula action and quantifier-lift fields used by the formula operations below."),
    ("SyntacticRewriting", "143-144", "814-815", "definition", "Specialize the rewriting interface to natural-number free variables."),
    ("Rewriting.«term_▹_»", "152-153", "823-824", "macro", "Notation for the existing Rewriting.app projection."),
    ("Rewriting.smul_ext'", "155", "826", "bind-only", "Rewrite-equality congruence for the formula action."),
    ("Rewriting.subst", "157", "840", "definition", "Apply Rew.subst to a formula and a Fin-indexed substitution vector."),
    ("Rewriting.«term_⇜_»", "159-160", "842-843", "macro", "Notation for the existing formula substitution API."),
    ("Rewriting.shift", "162-163", "845-846", "definition", "Lift Rew.shift to a connective homomorphism on formulas."),
    ("Rewriting.free", "165", "848", "definition", "Remove the final bound slot and introduce free variable zero."),
    ("Rewriting.shifts", "167", "852", "definition", "Apply the formula shift to each list member."),
    ("«term_⁺»", "169-170", "854-855", "macro", "Scoped notation for formula-list shifting."),
    ("Rewriting.shifts_nil", "172", "857", "bind-only", "Empty-list computation law used by the shifts_nil document selector."),
    ("Rewriting.shifts_cons", "174", "859", "bind-only", "Cons computation law used by the shifts_cons document selector."),
    ("Rewriting.shifts_neg", "176-177", "861-862", "bind-only", "List-negation compatibility used by the shifts_neg document selector."),
    ("Rewriting.emb", "179", "864", "definition", "Embed formulas from an empty free-label type through the rewriting action."),
    ("substNotation", "187-193", "872-878", "macro", "Slash syntax expands to formula substitution with a Fin-indexed vector."),
    ("ReflectiveRewriting", "197-199", "887-889", "class", "Record identity action for the existing formula-rewriting interface."),
    ("TransitiveRewriting", "201-205", "891-895", "class", "Record composition action for the existing formula-rewriting interface."),
    ("InjMapRewriting", "207-210", "897-900", "class", "Record injectivity for injective bound/free-variable maps."),
    ("LawfulSyntacticRewriting", "212-213", "902-903", "class", "Group the three inherited rewriting interfaces without asserting a new equality."),
    ("LawfulSyntacticRewriting.shift_conj₂", "223-229", "930-936", "bind-only", "Finite-conjunction shift law used by the shift_conj_two document selector."),
    ("LawfulSyntacticRewriting.app_subst_fbar_zero_comp_shift_eq_free", "234-235", "951-953", "bind-only", "Formula-level use of the frozen term substitution/shift/free identity."),
]
compat_rows = [
    ("Semiterm.fvar_rew", "27-32", "756-770", "bind-only", "Semiterm.fvar?_rew"),
    ("Semiterm.fvar_bShift", "34-36", "772-774", "bind-only", "Semiterm.fvar?_bShift"),
    ("RewThreeCompat.shift_conj_two", "47-48", "930-936", "bind-only", "LawfulSyntacticRewriting.shift_conj₂"),
    ("RewThreeCompat.app_subst_fbar_zero_comp_shift_eq_free", "52-54", "951-953", "bind-only", "LawfulSyntacticRewriting.app_subst_fbar_zero_comp_shift_eq_free"),
    ("RewThreeCompat.shifts_nil", "58-60", "857", "bind-only", "Rewriting.shifts_nil"),
    ("RewThreeCompat.shifts_cons", "62-64", "859", "bind-only", "Rewriting.shifts_cons"),
    ("RewThreeCompat.shifts_neg", "66-68", "861-862", "bind-only", "Rewriting.shifts_neg"),
    ("RewThreeCompat.emb", "70-72", "864", "definition", "Rewriting.emb"),
    ("RewThreeCompat.substNotation", "74-77", "840; 872-878", "definition", "Rewriting.subst"),
]

states = {}
for m, data in modules.items():
    path = ROOT / "Golden/Frozen/state" / (m.replace(".", "/") + ".lean.json")
    if path.is_file():
        states[m] = json.loads(path.read_text())["statement_id"]
decls = {m: {d["name"]: d for d in x["declarations"]} for m, x in modules.items()}

def direct_frozen(externals):
    result = []
    for item in sorted(set(externals)):
        mod, name = item.split(":", 1)
        if mod not in states:
            continue
        d = decls.get(mod, {}).get(name)
        result.append({
            "gid": mod.replace(".", "/"),
            "statement_id": states[mod],
            "declaration_name": name,
            "declaration_statement_id": d["statement_id"] if d and d.get("include_in_statement") else None,
            "identity_scope": "module GID plus exact Lean declaration name" if d and d.get("include_in_statement") else "module only; no independently reported declaration identity",
        })
    return result

capture = json.loads((OUT / "current-prerequisites.json").read_text())
current = {r["constant"]["name"]: r for r in capture["constants"]}
history = json.loads((OUT / "historical-capture-bindings.json").read_text())
historical_decls = {(r["module"], r["name"]): r for r in history["declarations"]}
for mod, binding in history["modules"].items():
    assert "sha256:" + hashlib.sha256((OUT / binding["edge_file"]).read_bytes()).hexdigest() == binding["edge_sha256"]
for mod, sha in capture["source_sha256"].items():
    assert modules[mod]["source_sha256"].removeprefix("sha256:") == sha
    assert hashlib.sha256((ROOT / (mod.replace(".", "/") + ".lean")).read_bytes()).hexdigest() == sha
assert capture["exit_code"] == 0
assert capture["probe_sha256"] == "sha256:" + hashlib.sha256((OUT / "current-prerequisites.lean").read_bytes()).hexdigest()

def identity(ep):
    mod, name = ep["module"], ep["name"]
    d = decls.get(mod, {}).get(name)
    return {**ep, "module_gid": mod.replace(".", "/") if mod else None,
            "frozen_module_statement_id": states.get(mod),
            "declaration_statement_id": d["statement_id"] if d and d.get("include_in_statement") else None,
            "identity_scope": "included canonical report declaration" if d and d.get("include_in_statement") else "no independently included report identity; not fabricated"}

def through_auxiliaries(name):
    pending = [(ep, [name, ep["name"]]) for ep in current[name]["dependencies"]]
    seen, leaves, helpers = set(), {}, {}
    while pending:
        ep, path = pending.pop(0)
        n = ep["name"]
        if n in seen or n == name:
            continue
        seen.add(n)
        if ep["auxiliary"]:
            assert n in current, f"uncaptured reached auxiliary: {n}"
            helpers[n] = {**identity(ep), "path": path}
            pending.extend((dep, path + [dep["name"]]) for dep in current[n]["dependencies"])
        else:
            leaves[n] = {**identity(ep), "path": path}
    return [leaves[n] for n in sorted(leaves)], [helpers[n] for n in sorted(helpers)]

records = []
for suffix, metadata, edgefile in [
    ("RewThree", source_rows, "proof-edges-rewthree.json"),
    ("RewThreeCompat", compat_rows, "proof-edges-compat.json"),
]:
    mod = base + suffix
    edges = json.loads((OUT / edgefile).read_text())
    source_index = {}
    for name, local, original, shape, purpose in metadata:
        full = "LO.FirstOrder." + name
        assert full in decls[mod], f"unresolved full-name join: {full}"
        source_index[full] = (local, original, shape, purpose)
    assert len(source_index) == len(metadata) and source_index
    for d in modules[mod]["declarations"]:
        if not d.get("include_in_statement"):
            continue
        name = d["name"]
        assert name in current, f"current included declaration not captured: {name}"
        ep = current[name]["constant"]
        old = historical_decls.get((mod, name))
        history_key = ep["user_name"] + (" (private)" if name != ep["user_name"] else "")
        historical_match = old is not None and old["kind"] == d["kind"] and old["statement_id"] == d["statement_id"]
        leaves, helpers = through_auxiliaries(name)
        meta = source_index.get(name)
        generated = meta is None
        generated_owner = None
        if meta:
            local, original, shape, purpose = meta
            upstream_name = "LO.FirstOrder." + purpose if suffix == "RewThreeCompat" else name
            if suffix == "RewThreeCompat":
                purpose = "Exact selector consumed by Blueprint/D5/S3/ConceptDynamics/ZfcTermRewriting/RewThree.scribe.cs; forwards " + upstream_name + "."
        else:
            # Generated artifacts have no independent upstream source declaration.
            local, original = None, None
            owners = [n for n in source_index if ep["user_name"].startswith(n + ".")]
            if owners and "_aux" not in name:
                generated_owner = max(owners, key=len)
                local, original = source_index[generated_owner][:2]
            shape = "bind-only" if d["kind"] == "theorem" else "definition"
            if "macroRules" in name or "unexpand" in name:
                shape = "macro"
            purpose = "Compiler-generated companion of the retained source commands; no independent API/coverage necessity or escape credit claimed."
            upstream_name = None
        records.append({
            "module": mod, "module_gid": mod.replace(".", "/"), "name": name,
            "kind": d["kind"], "statement_id": d["statement_id"],
            "authored_source_command": not generated, "proof_shape": shape,
            "source_lines": local, "upstream_source_lines": original,
            "generated_from_source_command": generated_owner,
            "upstream_declaration": upstream_name,
            "upstream_source": upstream,
            "visibility": "private" if name.startswith("_private.") else "public",
            "utility": {"kind": "none", "reason": "General syntax API, retained laws or generated companions; no bounded enumeration, checker, numeric reduction or certified finite instance.", "basis": "not-applicable(kind=none)"},
            "historical_capture": {
                "file": edgefile, "key": history_key,
                "same_statement_and_kind": historical_match,
                "source_matches_current": history["modules"][mod]["source_sha256"] == modules[mod]["source_sha256"],
                "dependency_capture": "Internal edges expand auxiliaries; external_deps are raw direct D5 constants. Historical data, not a current expanded external claim.",
                "captured": historical_match and history_key in edges.get("kinds", {}),
                "direct_frozen_dependencies": direct_frozen(edges.get("external_deps", {}).get(history_key, [])) if historical_match else None,
                "module_internal_dependencies": sorted(set(edges.get("edges", {}).get(history_key, []))) if historical_match else None,
                "limit": "Missing capture is unknown, not a verified empty dependency set. Changed identities do not inherit historical capture."},
            "current_raw_direct_frozen_dependencies": [identity(e) for e in current[name]["dependencies"] if e["module"] != mod and e["module"] in states],
            "current_frozen_prerequisites_through_auxiliaries": [e for e in leaves if e["module"] != mod and e["module"] in states],
            "current_module_internal_dependencies_through_auxiliaries": [e for e in leaves if e["module"] == mod],
            "current_auxiliaries_expanded": helpers,
            "current_external_nonfrozen_boundary": [e for e in leaves if e["module"] != mod and e["module"] not in states],
            "dependency_capture": "Current raw type/value edges in current-prerequisites.json; auxiliary-only traversal, stopping at each nonauxiliary boundary. Not full transitive closure or live-path analysis.",
            "axioms": d["axioms"],
            "escape_witness": "none; upstream retention/forwarding and generated companions receive no new escape credit",
            "admission_basis": "rule-11-upstream-wrapper" if not generated else "generated companion under module rule-11-upstream-wrapper basis; no independent deposit claim",
            "api_necessity": purpose,
        })

assert sum(r["authored_source_command"] for r in records) == 40
document = {
    "schema": "rewthree-declaration-audit-v2",
    "historical_capture_bindings": "historical-capture-bindings.json",
    "current_capture_sha256": "sha256:" + hashlib.sha256((OUT / "current-prerequisites.json").read_bytes()).hexdigest(),
    "counts": {"included": len(records), "public": sum(r["visibility"] == "public" for r in records), "private": sum(r["visibility"] == "private" for r in records), "authored_source_commands": 40, "theorems": sum(r["kind"] == "theorem" for r in records)},
    "input_head": subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip(),
    "raw_report_sha256": "sha256:" + hashlib.sha256(raw_bytes).hexdigest(),
    "source_sha256": {base + s: modules[base + s]["source_sha256"] for s in ("RewThree", "RewThreeCompat")},
    "scope": "Evidence for the retained rewriting API and its Scribe selectors; not a complete CSA or a new mathematical result.",
    "reported_excluded_declarations": [
        {"module": base + suffix, "name": d["name"], "kind": d["kind"],
         "declaration_statement_id": None, "identity_scope": "excluded by canonical report; no included declaration identity",
         "current_capture_key": d["name"], "independent_content_credit": False}
        for suffix in ("RewThree", "RewThreeCompat")
        for d in modules[base + suffix]["declarations"] if not d.get("include_in_statement")],
    "records": records,
}
(OUT / "declaration-audit.json").write_text(compact_maps(document))

lines = ["# RewThree declaration evidence", "", "This table joins source commands to the kernel report by full Lean name. The previous empty table compared unqualified source names with `LO.FirstOrder...` names; it was an evidence-generation failure, not a zero-declaration result.", "", f"Input HEAD: `{document['input_head']}`.", f"Raw Lean report SHA-256: `{document['raw_report_sha256']}`.", "", "The input HEAD identifies the pre-repair checkout; source/report hashes bind the current uncommitted repair. [declaration-audit.json](declaration-audit.json) records every included report declaration, including the private toEmpty splitter. Historical raw external edges and current prerequisites through auxiliaries are separate, with exact identities, helper paths, axioms, utility, source mapping and limits. These are evidence records, not new mathematics or a complete CSA.", "", "For every authored theorem below, `proof_shape=bind-only`, `escape_witness=none`, and `admission_basis=rule-11-upstream-wrapper`. Definitions, classes and macros use their stated shape and the same upstream basis. The exact upstream is [Foundation Rew.lean at 30a16ffa](" + upstream + ").", "", "| Public source declaration | Kind / proof_shape | Local lines | Exact upstream lines | Current frozen prerequisites through auxiliaries |", "| --- | --- | --- | --- | --- |"]
for r in records:
    if not r["authored_source_command"]:
        continue
    lines.append(f"| `{r['name']}` | {r['kind']} / {r['proof_shape']} | {r['module'].split('.')[-1]}:{r['source_lines']} | {r['upstream_source_lines']} | {len(r['current_frozen_prerequisites_through_auxiliaries'])}; exact GID + statement IDs in JSON |")
lines += ["", f"Authored source-command rows: **40**. Included kernel-report records: **{len(records)}** (public **{document['counts']['public']}**, private **{document['counts']['private']}**). Historical audit: **94 public records / 95 included**. Generated records have no independent source declaration or novelty claim; their JSON entries record the parent source-command range when identified by a declaration prefix, and separate historical missing captures from current captured edges. All current included rows have capture; no absent generated statement identity is invented.", "", "The machine data do not determine proof shape. The bind-only assessment follows the retained-upstream/forwarding basis recorded in `Library/ConceptDynamics/foundation2026firstorder.md`; it does not reclassify upstream induction proofs as newly authored content.", ""]
(OUT / "declaration-shapes.md").write_text("\n".join(lines))
print(f"AUDIT_OK authored=40 included={len(records)} public={document['counts']['public']} private={document['counts']['private']}")
