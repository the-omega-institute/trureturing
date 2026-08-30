#!/usr/bin/env python3
"""compose_envelope.py WORKTREE OUT.json [--worker RESULT.json] [--lane L] [--pr N] [--pass K] [--note TEXT]

Derive a pre-merge review envelope FROM THE BRANCH, not from prose:
  base  = merge-base origin/dev HEAD, head = HEAD (git-derived, never typed);
  deposited atoms = receipts ADDED under Meta/Digestion/formalizations/ (atom_id, primary_gid);
  ejected atoms   = residual-open YAML files whose diff ADDS a `quarantine:` block
                    (atom_id from the filename, blocker_class / reentry_condition / justification from HEAD).
Whitelisted per-atom fields (clause_matrix, tautology_check, encoded_scope_hypotheses, known_source_defects,
public_statement_shape, findings_closed, primitives_used) are copied from the worker envelope when --worker is given;
nothing else from the worker is carried (its prose describes a state the branch may no longer have).
Fail-fast: exit 64 usage/bad --pr/--pass, 65 not a worktree, 66 no origin/dev, 67 a deposited atom is also quarantined (in HEAD, not only this diff), 68 no outcome derivable.
Sentinel on success: COMPOSE_OK deposited=<n> ejected=<m> head=<sha9>.
"""
import json, os, re, subprocess, sys

WHITELIST = ("clause_matrix", "tautology_check", "encoded_scope_hypotheses", "known_source_defects",
             "public_statement_shape", "findings_closed", "primitives_used", "closure", "frozen_owner_reused")


def git(wt, *args):
    return subprocess.check_output(["git", "-C", wt, *args], text=True).strip()


def usage(code=64):
    sys.stderr.write(__doc__)
    sys.exit(code)


def parse_quarantine(text):
    """Return the quarantine mapping from a residual-open YAML (single-line scalars only)."""
    block = {}
    m = re.search(r"^\s*quarantine:\s*$", text, re.M)
    if not m:
        return None
    for line in text[m.end():].splitlines():
        mm = re.match(r'^\s{4}(justification|reentry_condition|blocker_class):\s*(.*?)\s*$', line)
        if mm:
            value = mm.group(2)
            if len(value) >= 2 and value[0] == value[-1] and value[0] in ('"', "'"):
                value = value[1:-1]
            block[mm.group(1)] = value
        elif line.strip() and not line.startswith("    "):
            break
    return block or None


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
    names = git(wt, "diff", "--name-status", base, "HEAD")
    worker = {}
    if opts["worker"]:
        with open(opts["worker"], encoding="utf-8") as fh:
            loaded = json.load(fh)
        worker = loaded.get("conclusion", loaded)
    worker_atoms = {a.get("atom_id"): a for a in worker.get("atoms", []) if isinstance(a, dict)}
    for q in worker.get("quarantined_atoms", []) or []:
        if isinstance(q, dict) and q.get("atom_id"):
            worker_atoms.setdefault(q["atom_id"], q)
        # a bare atom_id string carries no whitelisted fields; the YAML record is the source anyway

    deposited, ejected = [], []
    for line in names.splitlines():
        status, path = line.split("\t")[0], line.split("\t")[-1]
        if status.startswith("A") and path.startswith("Meta/Digestion/formalizations/") and path.endswith(".v1.json"):
            with open(os.path.join(wt, path), encoding="utf-8") as fh:
                receipt = json.load(fh)
            atom = {"atom_id": receipt["atom_id"], "outcome": "deposited", "gid": receipt.get("primary_gid"),
                    "receipt": path, "bind_only": None}
            src = worker_atoms.get(receipt["atom_id"], {})  # per-atom record only; never the whole conclusion
            for key in WHITELIST:
                if key in src:
                    atom[key] = src[key]
            deposited.append(atom)
        elif status[0] in "AM" and "/residual-open/" in path and path.endswith(".yaml"):
            try:
                before = git(wt, "show", f"{base}:{path}")
            except subprocess.CalledProcessError:
                before = ""  # file did not exist at base: every quarantine block in HEAD is new
            after = git(wt, "show", f"HEAD:{path}")
            if parse_quarantine(before) is None and (block := parse_quarantine(after)):
                atom_id = os.path.basename(path)[:-len(".yaml")]
                atom = {"atom_id": atom_id, "outcome": "ejected", "gid": None,
                        "ejection_class": block.get("blocker_class"), "retry_when": block.get("reentry_condition"),
                        "justification": block.get("justification"), "durable_record": path + " receipts.quarantine",
                        "tautology_check": "n/a (ejected)", "known_source_defects": [], "encoded_scope_hypotheses": []}
                src = worker_atoms.get(atom_id, {})
                for key in ("mathlib_trail", "third_party_trail", "local_proof_attempt", "retrieval_receipts", "primitives_inspected"):
                    if key in src:
                        atom[key] = src[key]
                ejected.append(atom)
    head_quarantined = set()
    for line in names.splitlines():
        path = line.split("\t")[-1]
        if line[0] in "AM" and "/residual-open/" in path and path.endswith(".yaml") and parse_quarantine(git(wt, "show", f"HEAD:{path}")):
            head_quarantined.add(os.path.basename(path)[:-len(".yaml")])
    for atom in deposited:
        try:
            if parse_quarantine(git(wt, "show", "HEAD:" + next(l.split("\t")[-1] for l in names.splitlines() if l.split("\t")[-1].endswith(atom["atom_id"] + ".yaml")))):
                head_quarantined.add(atom["atom_id"])
        except StopIteration:
            pass
    overlap = {a["atom_id"] for a in deposited} & (head_quarantined | {a["atom_id"] for a in ejected})
    if overlap:
        sys.stderr.write(f"COMPOSE_DEPOSITED_AND_QUARANTINED {sorted(overlap)}\n")
        sys.exit(67)
    if not deposited and not ejected:
        sys.stderr.write("COMPOSE_NO_OUTCOME (no added receipt, no added quarantine block)\n")
        sys.exit(68)
    env = {"conclusion": {
        "lane": opts["lane"] or branch.split("/")[-1], "branch": branch, "base": base, "head": head,
        "fix_of_pr": int(opts["pr"]) if opts["pr"] else None, "review_pass": int(opts["pass"]) if opts["pass"] else None,
        "atoms": deposited + ejected, "deposited_count": len(deposited), "ejected_count": len(ejected),
        "kind": "data-only quarantine PR (zero deposits)" if not deposited and ejected else "deposit PR",
        "orchestrator_note": opts["note"], "branch_diff_name_status": names,
        "log_ref": worker.get("log_ref") or (os.path.dirname(opts["worker"]) + "/worklog.md" if opts["worker"] else None),
        "composer": "tools/scripts/agent/compose_envelope.py (branch-derived; worker fields whitelisted)"}}
    with open(out, "w", encoding="utf-8") as fh:
        json.dump(env, fh, ensure_ascii=False, indent=1)
    print(f"COMPOSE_OK deposited={len(deposited)} ejected={len(ejected)} head={head[:9]}")


if __name__ == "__main__":
    main(sys.argv)
