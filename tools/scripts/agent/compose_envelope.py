#!/usr/bin/env python3
"""compose_envelope.py WORKTREE OUT.json [--worker RESULT.json] [--lane L] [--pr N] [--pass K] [--note TEXT]

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
    opts = {"worker": None, "lane": None, "pr": None, "pass": None, "note": ""}
    i = 3
    while i < len(argv):
        key = argv[i].lstrip("-")
        if key not in opts or i + 1 >= len(argv):
            usage()
        opts[key] = argv[i + 1]
        i += 2
    for key in ("pr", "pass"):
        if opts[key] is not None and not re.fullmatch(r"[0-9]+", opts[key]):
            sys.stderr.write(f"COMPOSE_BAD_INT --{key}={opts[key]}\n")
            sys.exit(64)
    if opts["worker"] is not None and not os.path.isfile(opts["worker"]):
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

    wrapper = os.path.join(os.path.dirname(os.path.abspath(__file__)), "review_envelope.sh")
    verb = subprocess.run(["/bin/bash", wrapper, wt, base, head], capture_output=True, text=True)
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
    if not isinstance(truth, dict) or truth.get("schema") != "stratalint-review-envelope-v1" or not all(k in truth for k in ("base", "head", "deposited", "ejected")):
        sys.stderr.write(f"COMPOSE_VERB_SCHEMA_MISMATCH {truth.get('schema')}\n")
        sys.exit(70)
    if truth["base"] != base or truth["head"] != head:
        sys.stderr.write(f"COMPOSE_VERB_REVISION_MISMATCH verb={truth['base'][:9]}..{truth['head'][:9]} requested={base[:9]}..{head[:9]}\n")
        sys.exit(70)

    worker = {}
    if opts["worker"]:
        with open(opts["worker"], encoding="utf-8") as fh:
            loaded = json.load(fh)
        worker = loaded.get("conclusion", loaded)
    per_atom = {}
    for record in list(worker.get("atoms", []) or []) + list(worker.get("quarantined_atoms", []) or []):
        if isinstance(record, dict) and record.get("atom_id"):
            per_atom.setdefault(record["atom_id"], record)

    # Single-deposit fix-flight envelopes carry the per-atom attestations at conclusion level; with exactly
    # one deposited atom and no per-atom record for it, that level IS the per-atom record (unambiguous).
    # With two or more deposited atoms, conclusion-level fields are never attributed (round-1 finding).
    conclusion_level = {k: v for k, v in worker.items() if k in WHITELIST} if len(truth["deposited"]) == 1 else {}

    atoms = []
    for d in truth["deposited"]:
        atom = {"atom_id": d["atom_id"], "outcome": "deposited", "gid": d["gid"], "receipt": d["receipt"], "bind_only": None}
        record = per_atom.get(d["atom_id"]) or conclusion_level
        atom.update({k: v for k, v in record.items() if k in WHITELIST})
        atoms.append(atom)
    for e in truth["ejected"]:
        atom = {"atom_id": e["atom_id"], "outcome": "ejected", "gid": None, "ejection_class": e["blocker_class"],
                "retry_when": e["reentry_condition"], "justification": e["justification"], "source_id": e["source_id"],
                "tautology_check": "n/a (ejected)", "known_source_defects": [], "encoded_scope_hypotheses": []}
        atom.update({k: v for k, v in per_atom.get(e["atom_id"], {}).items() if k in WHITELIST and k != "tautology_check"})
        atoms.append(atom)

    env = {"conclusion": {
        "lane": opts["lane"] or branch.split("/")[-1], "branch": branch, "base": base, "head": head,
        "fix_of_pr": int(opts["pr"]) if opts["pr"] else None, "review_pass": int(opts["pass"]) if opts["pass"] else None,
        "atoms": atoms, "deposited_count": len(truth["deposited"]), "ejected_count": len(truth["ejected"]),
        "kind": "data-only quarantine PR (zero deposits)" if not truth["deposited"] else "deposit PR",
        "orchestrator_note": opts["note"], "branch_diff_name_status": git(wt, "diff", "--name-status", base, "HEAD"),
        "log_ref": worker.get("log_ref") or (os.path.dirname(opts["worker"]) + "/worklog.md" if opts["worker"] else None),
        "composer": "StrataLint review-envelope (typed) via tools/scripts/agent/compose_envelope.py"}}
    with open(out, "w", encoding="utf-8") as fh:
        json.dump(env, fh, ensure_ascii=False, indent=1)
    print(f"COMPOSE_OK deposited={len(truth['deposited'])} ejected={len(truth['ejected'])} head={head[:9]}")


if __name__ == "__main__":
    main(sys.argv)
