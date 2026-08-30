#!/usr/bin/env python3
"""review_envelope.py WORKTREE BASE HEAD — branch-derived review truth for a formalization PR (no tests by owner ruling, #4163).

Prints JSON {schema, base, head, deposited[], extended[], ejected[]} derived ONLY from `git` objects of WORKTREE:
  deposited = receipts (Meta/Digestion/formalizations/*.v1.json) added in HEAD relative to BASE;
  extended  = existing receipts that gained hosted_extensions (root fields and prior extensions byte-unchanged);
  ejected   = ledger entries (Meta/Digestion/backfill/*/residual-open/*.yaml) whose receipts.quarantine block is new in HEAD.
Fail-fast exits: 64 usage, 65 no outcome, 66 invalid change (deleted receipt / rewritten receipt / path-atom mismatch), 3 conflict
(an atom quarantined in HEAD also holds a receipt in HEAD).  Everything else in the envelope is the worker's attestation, not truth.
"""
import json, re, subprocess, sys

RECEIPTS = "Meta/Digestion/formalizations/"
SUFFIX = ".v1.json"
LEDGER = re.compile(r"^Meta/Digestion/backfill/([^/]+)/residual-open/[^/]+\.ya?ml$")
QUAR = re.compile(r"^\s{2,}quarantine:\s*$", re.M)


def git(wt, *args):
    return subprocess.run(["git", "-C", wt, *args], check=True, capture_output=True, text=True).stdout


def show(wt, rev, path):
    return subprocess.run(["git", "-C", wt, "show", f"{rev}:{path}"], check=True, capture_output=True, text=True).stdout


def receipt(wt, rev, path):
    doc = json.loads(show(wt, rev, path))
    if not isinstance(doc, dict) or doc.get("schema") != "digestion-formalization-v1":
        die(66, f"REVIEW_ENVELOPE_INVALID receipt schema: {rev}:{path}")
    if path != RECEIPTS + doc.get("atom_id", "") + SUFFIX:
        die(66, f"REVIEW_ENVELOPE_INVALID receipt path/atom mismatch: {rev}:{path}")
    return doc


def die(code, message):
    sys.stderr.write(message + "\n")
    sys.exit(code)


def main(argv):
    if len(argv) != 4:
        die(64, "usage: review_envelope.py WORKTREE BASE HEAD")
    wt, base, head = argv[1:4]
    base, head = git(wt, "rev-parse", base).strip(), git(wt, "rev-parse", head).strip()
    deposited, extended, ejected = [], [], []
    for line in git(wt, "diff", "--name-status", base, head).splitlines():
        status, _, path = line.partition("\t")
        if path.startswith(RECEIPTS) and path.endswith(SUFFIX):
            if status == "A":
                doc = receipt(wt, head, path)
                deposited.append({"atom_id": doc["atom_id"], "gid": doc["primary_gid"], "receipt": path})
            elif status == "M":
                old, new = receipt(wt, base, path), receipt(wt, head, path)
                root = {k: v for k, v in old.items() if k != "hosted_extensions"}
                root_new = {k: v for k, v in new.items() if k != "hosted_extensions"}
                old_ext, new_ext = old.get("hosted_extensions", []), new.get("hosted_extensions", [])
                added = [e["gid"] for e in new_ext if e not in old_ext]
                if root != root_new or any(e not in new_ext for e in old_ext) or not added:
                    die(66, f"REVIEW_ENVELOPE_INVALID rewritten receipt (only hosted_extensions may be appended): {path}")
                extended.append({"atom_id": new["atom_id"], "gid": new["primary_gid"], "receipt": path, "added_gids": sorted(added)})
            else:
                die(66, f"REVIEW_ENVELOPE_INVALID receipt {status}: {path}")
        elif LEDGER.match(path) and status in ("A", "M"):
            text = show(wt, head, path)
            if not QUAR.search(text):
                continue
            if status == "M" and QUAR.search(show(wt, base, path)):
                continue  # quarantine already present in base: not this branch's outcome
            atom = re.search(r"^\s*atom_id:\s*(\S+)", text, re.M)
            block = text[QUAR.search(text).end():]
            fields = {k: (re.search(rf"^\s+{k}:\s*(.*)$", block, re.M) or [None, ""])[1].strip().strip('"\'') for k in ("justification", "reentry_condition", "blocker_class")}
            ejected.append({"atom_id": atom.group(1) if atom else path, "source_id": LEDGER.match(path).group(1), **fields})
    head_receipts = {p for p in git(wt, "ls-tree", "-r", "--name-only", head, RECEIPTS).splitlines()}
    for e in ejected:
        if RECEIPTS + e["atom_id"] + SUFFIX in head_receipts:
            die(3, f"REVIEW_ENVELOPE_CONFLICT {e['atom_id']} is quarantined and receipted in head")
    if not (deposited or extended or ejected):
        die(65, "REVIEW_ENVELOPE_INVALID no outcome: head adds no receipt, no hosted extension and no quarantine block relative to base")
    print(json.dumps({"schema": "stratalint-review-envelope-v1", "base": base, "head": head, "deposited": deposited, "extended": extended, "ejected": ejected}, ensure_ascii=False, indent=1))


if __name__ == "__main__":
    main(sys.argv)
