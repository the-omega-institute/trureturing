#!/usr/bin/env python3
"""Emit state membership, declaration inventory and source facts for a deposit delivery."""
import json, os, re, subprocess, sys, pathlib

GEN = re.compile(
    r'\.(eq_def|eq_\d+|match_\d+(_\d+)*|proof_\d+(_\d+)*|sizeOf_spec|_sizeOf_inst|_sizeOf_\d+|_f|_sunfold'
    r'|_unsafe_rec|_mutual|injEq|inj|noConfusion\w*|noConfusionType|rec|recOn|casesOn|mk\.\w+|below|brecOn'
    r'|ibelow|binductionOn|ctorIdx|_flat_ctor)$|\._sizeOf')
# Attributes and declaration modifiers may precede the keyword.
AUTHORED = re.compile(
    r'^(?!\s*private\b)(?:@\[[^\]]*\]\s*)*(?:protected\s+)?(?:noncomputable\s+)?'
    r'(theorem|lemma|def|abbrev|instance|structure|inductive|class)\s+'
    r'([A-Za-z_][\w\'.]*)', re.M)


SELFTEST_CASES = [
    # (source line, expected parsed name or None) — positives first, then negative controls.
    ("theorem plain_one : True := trivial", "plain_one"),
    ("@[simp] theorem attributed : True := trivial", "attributed"),
    ("@[simp, norm_cast] theorem two_attributes : True := trivial", "two_attributes"),
    ("protected theorem protected_one : True := trivial", "protected_one"),
    ("@[simp] protected theorem attributed_protected : True := trivial", "attributed_protected"),
    ("noncomputable def ncdef : Nat := 0", "ncdef"),
    ("structure Pair where", "Pair"),
    ("private theorem hidden : True := trivial", None),
    ("private def hidden_def : Nat := 0", None),
    ("  theorem indented_is_not_top_level : True := trivial", None),
    ("example : True := trivial", None),
]


def selftest() -> int:
    """Check authored declaration names and modifier boundaries."""
    failures = []
    for line, expected in SELFTEST_CASES:
        got = [m.group(2) for m in AUTHORED.finditer(line)]
        actual = got[0] if got else None
        if actual != expected:
            failures.append(f"{line!r} expected {expected!r} got {actual!r}")
    for f in failures:
        print("FAIL", f)
    print(f"SELFTEST cases={len(SELFTEST_CASES)} failures={len(failures)}")
    return 1 if failures else 0


def git(w, *a):
    return subprocess.run(["git", "-C", w, *a], capture_output=True, text=True).stdout.strip()


def decl_name(key: str, module_comps: list[str]) -> str:
    comps = re.findall(r'\d+:([^)]+)\)', key)
    if comps[:len(module_comps)] == module_comps:
        return '.'.join(comps[len(module_comps):])
    return '.'.join(comps) if comps else key


def main(worktree: str, readings: str | None) -> int:
    w = worktree
    head = git(w, "rev-parse", "HEAD")
    branch = git(w, "rev-parse", "--abbrev-ref", "HEAD")
    base = git(w, "merge-base", "HEAD", "origin/dev")
    changed = [p for p in git(w, "diff", "--name-only", "origin/dev...HEAD").splitlines() if p]
    states = [p for p in changed if p.startswith("Golden/Frozen/state/") and pathlib.Path(w, p).is_file()]
    cover = [p for p in changed if p.startswith("Meta/Digestion/backfill/")]
    if len(states) != 1:
        print(f"BODY_FACTS_FAIL expected one changed state record, found {len(states)}", file=sys.stderr)
        return 3
    record = json.loads(pathlib.Path(w, states[0]).read_bytes())
    if set(record) != {"statement_id", "declarations"}:
        print("BODY_FACTS_FAIL state keys must be statement_id and declarations", file=sys.stderr)
        return 3
    module_path = states[0][len("Golden/Frozen/state/"):-5]
    module_comps = module_path[:-5].split("/")
    decls = [(decl_name(d["declaration_name_key"], module_comps), d["kind"]) for d in record["declarations"]]
    src = pathlib.Path(w, module_path).read_text(encoding="utf-8")
    authored_names = [m.group(2) for m in AUTHORED.finditer(src)]
    surviving = [t for t in decls if not GEN.search(t[0]) and "_private." not in t[0] and t[1] not in ("constructor", "recursor")]
    authored = [t for t in surviving if t[0] in set(authored_names)]
    unmatched = [t for t in surviving if t[0] not in set(authored_names)]
    missing = [n for n in authored_names if n not in {t[0] for t in surviving}]
    imports = re.findall(r'^\s*(?:public\s+)?import\s+([^\n]+)', src, re.M)

    edges = []
    for c in cover:
        try:
            import yaml  # type: ignore
            y = yaml.safe_load(open(os.path.join(w, c)).read()) or {}
            for g in (y.get("coverage_gids") or []):
                edges.append((os.path.basename(c)[:-5], g.get("gid")))
        except Exception:
            pass

    print(f"head: `{head}`; branch: `{branch}`; merge-base with local origin/dev: `{base}`")
    print(f"Changed paths: {len(changed)}; state records: {len(states)}; digestion paths: {len(cover)}")
    print(f"State record: `{states[0]}`; module statement_id: `{record['statement_id']}`")
    print("Source imports: " + (", ".join(imports) or "none"))
    if edges:
        print("Coverage: " + "; ".join(f"{a} → {g}" for a, g in edges))
    print(f"Included declarations: {len(decls)}; authored public matches: {len(authored)}; unclassified: {len(unmatched)}")
    print("| Declaration | kind |")
    print("|---|---|")
    for name, kind in authored + unmatched:
        print(f"| `{name}` | {kind} |")
    if missing:
        print("Source names absent from included inventory: " + ", ".join(missing))
    if readings and pathlib.Path(readings).exists():
        print(f"\n### 门读数(逐门退出码,本次重做脚本记录)\n")
        print(pathlib.Path(readings).read_text().rstrip())
    return 0


if __name__ == "__main__":
    if "--selftest" in sys.argv:
        sys.exit(selftest())
    sys.exit(main(sys.argv[1], sys.argv[2] if len(sys.argv) > 2 else None))
