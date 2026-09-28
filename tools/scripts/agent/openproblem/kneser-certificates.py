#!/usr/bin/env python3
"""Regenerate the three Kneser CNFs and independently check UNSAT proofs.

Requires Python 3, python-sat, and an explicitly supplied drat-trim binary.
"""

import argparse
from itertools import combinations
from pathlib import Path
import subprocess
import tempfile

from pysat.solvers import Glucose3


F32 = [
    (1,4,5,6),(1,4,5,7),(1,4,5,8),(1,4,6,7),(1,4,6,8),(1,4,7,8),
    (1,5,6,7),(1,5,6,8),(1,5,7,8),(1,6,7,8),(2,3,4,5),(2,3,4,6),
    (2,3,4,7),(2,3,4,8),(2,3,5,6),(2,3,5,7),(2,3,5,8),(2,3,6,7),
    (2,3,6,8),(2,3,7,8),(2,4,6,8),(2,5,6,8),(3,4,5,6),(3,4,5,7),
    (3,4,5,8),(3,5,6,7),(3,5,6,8),(3,5,7,8),(4,5,6,7),(4,5,7,8),
    (4,6,7,8),(5,6,7,8),
]

F61 = [
    (1,2,6,9,10),(1,2,7,8,9),(1,2,7,8,10),(1,2,8,9,10),(1,3,8,9,10),
    (1,4,5,6,9),(1,4,5,7,9),(1,4,5,9,10),(1,4,6,7,10),(1,4,6,9,10),
    (1,4,7,9,10),(1,4,8,9,10),(1,5,6,7,9),(1,5,6,7,10),(1,5,6,8,10),
    (1,5,6,9,10),(1,5,7,8,10),(1,5,7,9,10),(1,5,8,9,10),(1,6,7,9,10),
    (1,6,8,9,10),(2,3,4,5,8),(2,3,4,6,7),(2,3,4,6,8),(2,3,4,6,9),
    (2,3,4,7,8),(2,3,4,8,9),(2,3,5,6,7),(2,3,5,7,8),(2,3,5,7,9),
    (2,3,6,7,8),(2,3,6,7,9),(2,3,6,7,10),(2,3,6,8,9),(2,3,6,8,10),
    (2,3,6,9,10),(2,3,7,8,9),(2,3,7,9,10),(2,3,8,9,10),(2,4,5,6,8),
    (2,4,5,7,8),(2,4,5,8,10),(2,4,6,7,8),(2,5,6,7,8),(2,5,6,8,10),
    (2,6,7,8,9),(2,6,7,8,10),(2,6,8,9,10),(3,4,5,6,7),(3,4,5,6,8),
    (3,4,5,6,9),(3,4,5,7,8),(3,4,5,7,9),(3,4,5,7,10),(3,4,5,8,9),
    (3,4,5,8,10),(3,4,5,9,10),(3,4,6,9,10),(3,4,7,8,10),(3,4,7,9,10),
    (3,6,7,9,10),
]


def triangle_cnf(family):
    assert len(family) == len(set(family))
    masks = [sum(1 << (p - 1) for p in member) for member in family]
    edges = {pair: i for i, pair in enumerate(combinations(range(len(family)), 2), 1)}
    clauses = []
    triangles = 0
    for a, b, c in combinations(range(len(family)), 3):
        if masks[a] & masks[b] & masks[c]:
            continue
        triangles += 1
        terms = [edges[(a,b)], edges[(a,c)], edges[(b,c)]]
        clauses.extend((terms, [-x for x in terms]))
    return len(edges), triangles, clauses


def certify(label, family, expected, checker):
    variables, triangles, clauses = triangle_cnf(family)
    assert (len(family), triangles) == expected
    with Glucose3(bootstrap_with=clauses, with_proof=True) as solver:
        if solver.solve():
            raise RuntimeError(f"{label}: CNF is SAT")
        proof = solver.get_proof()
    if not proof or proof[-1].strip() != "0":
        raise RuntimeError(f"{label}: solver proof does not end with empty clause")
    with tempfile.TemporaryDirectory(prefix="kneser-cert-") as directory:
        cnf_path = Path(directory) / "instance.cnf"
        proof_path = Path(directory) / "proof.drat"
        cnf_path.write_text(f"p cnf {variables} {len(clauses)}\n" +
                            "".join(" ".join(map(str, clause)) + " 0\n" for clause in clauses),
                            encoding="ascii")
        proof_path.write_text("\n".join(proof) + "\n", encoding="ascii")
        checked = subprocess.run([str(checker), str(cnf_path), str(proof_path), "-U"],
                                 text=True, capture_output=True, check=False)
        if checked.returncode or "s VERIFIED" not in checked.stdout + checked.stderr:
            raise RuntimeError(f"{label}: drat-trim failed: {checked.stdout} {checked.stderr}")
    print(f"{label}: {len(family)} vertices, {triangles} triangles, "
          f"{len(clauses)} clauses, {len(proof)} proof lines, VERIFIED")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--drat-trim", required=True, type=Path, help="path to drat-trim binary")
    args = parser.parse_args()
    checker = args.drat_trim.expanduser().resolve()
    if not checker.is_file():
        parser.error(f"drat-trim binary is missing: {checker}")
    if not checker.stat().st_mode & 0o111:
        parser.error(f"drat-trim binary is not executable: {checker}")
    certify("V(6,3)", list(combinations(range(1,7), 3)), (20,480), checker)
    certify("F32", F32, (32,1211), checker)
    certify("F61", F61, (61,7119), checker)


if __name__ == "__main__":
    main()
