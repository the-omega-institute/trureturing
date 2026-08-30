#!/usr/bin/env python3
"""compose_envelope.py WORKTREE OUT.json [--worker RESULT.json]... [--lane L] [--pr N] [--pass K] [--note TEXT]
(--worker may repeat: a fix-flight result carries no attestations; pass the ORIGINAL deposit result first, then the fix result — later records only fill fields the earlier ones lack)

Thin caller (glue, 第 11 条 辨析): the branch truth comes from the typed verb
  StrataLint review-envelope --base <merge-base origin/dev HEAD> --head <HEAD>
run inside WORKTREE (canonical: dotnet run --project tools/StrataLint.Cli/StrataLint.Cli.csproj --configuration Release);
this script only derives the two revisions with git, forwards the verb's JSON, and copies WHITELISTED
per-atom fields from the worker result (by atom_id only — never the whole conclusion).
Fail-fast: 64 usage / bad --pr --pass / missing worker file, 65 not a worktree, 66 no origin/dev, 67 the verb's typed
conflict outcome (exit 3, REVIEW_ENVELOPE_CONFLICT: a quarantined atom holds a receipt) forwarded mechanically, 69 any other
verb rejection (its REVIEW_ENVELOPE_INVALID line relayed verbatim), 70 the verb's output is not JSON / wrong schema tag /
echoed base-head differ from the request. Sentinel: COMPOSE_OK deposited=<n> ejected=<m> head=<sha9>. Idempotent.
The verb is invoked through tools/scripts/agent/review_envelope.sh (the single linkage-visible caller).
"""
import json, os, re, subprocess, sys

WHITELIST = ("clause_matrix", "tautology_check", "encoded_scope_hypotheses", "known_source_defects",
             "public_statement_shape", "findings_closed", "primitives_used", "closure", "frozen_owner_reused",
             "mathlib_trail", "third_party_trail", "local_proof_attempt", "retrieval_receipts", "primitives_inspected")


def git(wt, *args):
    return subprocess.check_output(["git", "-C", wt, *args], text=True).strip()


def usage(code=64):
    sys.stderr.write(__doc__)
    sys.exit(code)


def main(argv):
    if len(argv) < 3:
        usage()
    wt, out = argv[1], argv[2]
    opts = {"worker": [], "lane": None, "pr": None, "pass": None, "note": ""}
    i = 3
    while i < len(argv):
        key = argv[i].lstrip("-")
        if key not in opts or i + 1 >= len(argv):
            usage()
        if key == "worker":
            opts["worker"].append(argv[i + 1])
        else:
            opts[key] = argv[i + 1]
        i += 2
    for key in ("pr", "pass"):
        if opts[key] is not None and not re.fullmatch(r"[0-9]+", opts[key]):
            sys.stderr.write(f"COMPOSE_BAD_INT --{key}={opts[key]}\n")
            sys.exit(64)
    if any(not os.path.isfile(path) for path in opts["worker"]):
        sys.stderr.write(f"COMPOSE_WORKER_MISSING {opts['worker']}\n")
        sys.exit(64)
    if not (os.path.isdir(os.path.join(wt, ".git")) or os.path.isfile(os.path.join(wt, ".git"))):
        sys.stderr.write(f"COMPOSE_NOT_A_WORKTREE {wt}\n")
        sys.exit(65)
    try:
        base = git(wt, "merge-base", "origin/dev", "HEAD")
    except subprocess.CalledProcessError:
        sys.stderr.write("COMPOSE_NO_ORIGIN_DEV\n")
        sys.exit(66)
    head = git(wt, "rev-parse", "HEAD")
    branch = git(wt, "rev-parse", "--abbrev-ref", "HEAD")

    verb_script = os.path.join(os.path.dirname(os.path.abspath(__file__)), "review_envelope.py")
    verb = subprocess.run([sys.executable, verb_script, wt, base, head], capture_output=True, text=True)
    if verb.returncode == 3:
        # typed outcome of the verb (REVIEW_ENVELOPE_CONFLICT, exit 3): forwarded mechanically as 67.
        sys.stderr.write(verb.stderr.strip() + "\n")
        sys.stderr.write("COMPOSE_DEPOSITED_AND_QUARANTINED\n")
        sys.exit(67)
    if verb.returncode != 0:
        sys.stderr.write(verb.stderr.strip() + "\n")  # the verb's own REVIEW_ENVELOPE_INVALID line, verbatim
        sys.stderr.write(f"COMPOSE_VERB_FAILED rc={verb.returncode}\n")
        sys.exit(69)
    try:
        truth = json.loads(verb.stdout)
    except json.JSONDecodeError as error:
        sys.stderr.write(f"COMPOSE_VERB_SCHEMA_MISMATCH (not JSON: {error})\n")
        sys.exit(70)
    if not isinstance(truth, dict) or truth.get("schema") != "stratalint-review-envelope-v1" or not all(k in truth for k in ("base", "head", "deposited", "ejected", "extended")):
        shape = truth.get("schema") if isinstance(truth, dict) else f"non-object JSON ({type(truth).__name__})"
        sys.stderr.write(f"COMPOSE_VERB_SCHEMA_MISMATCH {shape}\n")
        sys.exit(70)
    if truth["base"] != base or truth["head"] != head:
        sys.stderr.write(f"COMPOSE_VERB_REVISION_MISMATCH verb={truth['base'][:9]}..{truth['head'][:9]} requested={base[:9]}..{head[:9]}\n")
        sys.exit(70)

    worker, per_atom = {}, {}
    for path in opts["worker"]:
        with open(path, encoding="utf-8") as fh:
            loaded = json.load(fh)
        loaded = loaded.get("conclusion", loaded)
        for key, value in loaded.items():          # earlier results win; later ones only fill gaps
            worker.setdefault(key, value)
        for record in list(loaded.get("atoms", []) or []) + list(loaded.get("quarantined_atoms", []) or []):
            if isinstance(record, dict) and record.get("atom_id"):
                merged = per_atom.setdefault(record["atom_id"], {})
                for key, value in record.items():
                    merged.setdefault(key, value)

    # Single-deposit fix-flight envelopes carry the per-atom attestations at conclusion level; with exactly
    # one deposited atom and no per-atom record for it, that level IS the per-atom record (unambiguous).
    # With two or more deposited atoms, conclusion-level fields are never attributed (round-1 finding).
    single = len(truth["deposited"]) + len(truth["extended"]) == 1
    conclusion_level = {k: v for k, v in worker.items() if k in WHITELIST} if single else {}

    atoms = []
    for d in truth["deposited"]:
        atom = {"atom_id": d["atom_id"], "outcome": "deposited", "gid": d["gid"], "receipt": d["receipt"], "bind_only": None}
        record = per_atom.get(d["atom_id"]) or conclusion_level
        atom.update({k: v for k, v in record.items() if k in WHITELIST})
        atoms.append(atom)
    for x in truth["extended"]:
        # hosted extension: the existing receipt gained hosted_extensions (never rewritten); the review target is the added GIDs.
        atom = {"atom_id": x["atom_id"], "outcome": "extended", "gid": x["gid"], "receipt": x["receipt"], "added_gids": x["added_gids"], "bind_only": None}
        record = per_atom.get(x["atom_id"]) or conclusion_level
        atom.update({k: v for k, v in record.items() if k in WHITELIST})
        atoms.append(atom)
    for e in truth["ejected"]:
        atom = {"atom_id": e["atom_id"], "outcome": "ejected", "gid": None, "ejection_class": e["blocker_class"],
                "retry_when": e["reentry_condition"], "justification": e["justification"], "source_id": e["source_id"],
                "tautology_check": "n/a (ejected)", "known_source_defects": [], "encoded_scope_hypotheses": []}
        atom.update({k: v for k, v in per_atom.get(e["atom_id"], {}).items() if k in WHITELIST and k != "tautology_check"})
        atoms.append(atom)

    # worker ejections outside the quarantine alphabet (statement-unformalizable / statement-defect) have no branch
    # record by rule, but must still appear for the two-way ejection audit (#4183 pass-1 finding).
    seen = {atom["atom_id"] for atom in atoms}
    for atom_id, record in per_atom.items():
        if atom_id not in seen and record.get("outcome") == "ejected":
            atom = {"atom_id": atom_id, "outcome": "ejected", "gid": None, "ejection_class": record.get("ejection_class"),
                    "retry_when": record.get("retry_when"), "durable_record": "none by rule (not a quarantine class; worker envelope + PR body only)",
                    "tautology_check": "n/a (ejected)", "known_source_defects": record.get("known_source_defects", []), "encoded_scope_hypotheses": [],
                    "notes": record.get("notes")}
            atom.update({k: v for k, v in record.items() if k in WHITELIST and k not in atom})
            atoms.append(atom)

    env = {"conclusion": {
        "lane": opts["lane"] or branch.split("/")[-1], "branch": branch, "base": base, "head": head,
        "fix_of_pr": int(opts["pr"]) if opts["pr"] else None, "review_pass": int(opts["pass"]) if opts["pass"] else None,
        "atoms": atoms, "deposited_count": len(truth["deposited"]), "extended_count": len(truth["extended"]), "ejected_count": sum(1 for atom in atoms if atom["outcome"] == "ejected"),
        "kind": "deposit PR" if truth["deposited"] else ("hosted-extension PR" if truth["extended"] else "data-only quarantine PR (zero deposits)"),
        "orchestrator_note": opts["note"], "branch_diff_name_status": git(wt, "diff", "--name-status", base, "HEAD"),
        "log_ref": worker.get("log_ref") or [os.path.dirname(path) + "/worklog.md" for path in opts["worker"]],
        "composer": "tools/scripts/agent/review_envelope.py (branch-derived truth) + compose_envelope.py (whitelisted worker attestations)"}}
    with open(out, "w", encoding="utf-8") as fh:
        json.dump(env, fh, ensure_ascii=False, indent=1)
    print(f"COMPOSE_OK deposited={len(truth['deposited'])} extended={len(truth['extended'])} ejected={len(truth['ejected'])} head={head[:9]}")


if __name__ == "__main__":
    main(sys.argv)
