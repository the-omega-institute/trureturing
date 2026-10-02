#!/usr/bin/env python3
"""Finite SAT audit for a five-prime pair palette.

This is a fixed finite branch only.  It does not address unrestricted
Erdos #7 and does not use private-point or irredundancy assumptions: the
UNSAT result is therefore stronger for this palette than the requested
whole-cover-plus-triple-owner condition.

The palette is the five primes and every pair product.  A Boolean variable
R(i,a) means that modulus MODULI[i] is assigned residue a.  Clauses impose
one residue per modulus, coverage of every point in one CRT period, and for
every non-coprime pair and every point the implication

  R(i,x mod m_i) and R(j,x mod m_j) -> some third owner at x.

At-most-one clauses use a sequential cardinality encoding.  The report
records the exact formula dimensions and two independent PySAT backends.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from fractions import Fraction
from itertools import combinations
from math import gcd, lcm, prod
from pathlib import Path

from pysat.card import CardEnc, EncType
from pysat.solvers import Solver
import pysat

PRIMES = (3, 5, 7, 11, 13)
MODULI = tuple(sorted(PRIMES + tuple(p * q for p, q in combinations(PRIMES, 2))))
PERIOD = lcm(*MODULI)
BASE_VARIABLES = sum(MODULI)


def offsets() -> tuple[int, ...]:
    out: list[int] = []
    cursor = 0
    for modulus in MODULI:
        out.append(cursor)
        cursor += modulus
    return tuple(out)


OFFSETS = offsets()


def residue_var(index: int, residue: int) -> int:
    return OFFSETS[index] + residue + 1


def build_formula() -> tuple[list[list[int]], int, dict[str, int]]:
    clauses: list[list[int]] = []
    top_id = BASE_VARIABLES
    counts = {"one_residue": 0, "at_most_one": 0, "coverage": 0, "triple_owner": 0}
    for index, modulus in enumerate(MODULI):
        clauses.append([residue_var(index, residue) for residue in range(modulus)])
        counts["one_residue"] += 1
        encoded = CardEnc.atmost(
            lits=[residue_var(index, residue) for residue in range(modulus)],
            bound=1,
            top_id=top_id,
            encoding=EncType.seqcounter,
        )
        clauses.extend(encoded.clauses)
        counts["at_most_one"] += len(encoded.clauses)
        top_id = encoded.nv
    for point in range(PERIOD):
        clauses.append([residue_var(i, point % modulus) for i, modulus in enumerate(MODULI)])
        counts["coverage"] += 1
        for i, j in combinations(range(len(MODULI)), 2):
            if gcd(MODULI[i], MODULI[j]) == 1:
                continue
            third = [
                residue_var(k, point % modulus)
                for k, modulus in enumerate(MODULI)
                if k not in (i, j)
            ]
            clauses.append(
                [-residue_var(i, point % MODULI[i]), -residue_var(j, point % MODULI[j]), *third]
            )
            counts["triple_owner"] += 1
    return clauses, top_id, counts


def check_palette() -> None:
    assert all(modulus % 2 == 1 and modulus > 1 for modulus in MODULI)
    assert len(set(MODULI)) == len(MODULI)
    assert PERIOD == 15015
    assert all(
        divisor == 1 or divisor in MODULI
        for modulus in MODULI
        for divisor in range(3, modulus + 1, 2)
        if modulus % divisor == 0
    )


def solve_backend(name: str, clauses: list[list[int]]) -> dict[str, object]:
    with Solver(name=name, bootstrap_with=clauses) as solver:
        answer = solver.solve()
        return {
            "backend": name,
            "status": "SAT" if answer else "UNSAT",
            "boolean_result": bool(answer),
            "clause_count_seen": solver.nof_clauses(),
            "variable_count_seen": solver.nof_vars(),
        }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, default=Path(__file__).with_suffix(".json"))
    args = parser.parse_args()
    check_palette()
    clauses, total_variables, counts = build_formula()
    backends = [solve_backend("cadical153", clauses), solve_backend("glucose4", clauses)]
    assert all(row["status"] == "UNSAT" for row in backends)
    result = {
        "schema": "five-prime-pair-triple-owner-unsat-v1",
        "scope": (
            "Fixed distinct odd divisor-closed palette only. UNSAT excludes whole coverage "
            "plus triple ownership for this palette; no unrestricted Erdos #7 conclusion."
        ),
        "primes": list(PRIMES),
        "moduli": list(MODULI),
        "period": PERIOD,
        "reciprocal_sum": str(sum((Fraction(1, modulus) for modulus in MODULI), Fraction(0))),
        "base_variable_count": BASE_VARIABLES,
        "total_variable_count": total_variables,
        "clause_count": len(clauses),
        "clause_categories": counts,
        "encoding": {
            "residue_choice": "exactly one residue per modulus",
            "coverage": "at least one selected class owns every x in 0..period-1",
            "triple_owner": (
                "for every gcd(m_i,m_j)>1 and every x, simultaneous ownership by i,j "
                "implies at least one owner k distinct from i,j"
            ),
            "at_most_one": "sequential cardinality encoding",
        },
        "solver_library": "python-sat",
        "solver_library_version": getattr(pysat, "__version__", "unknown"),
        "backends": backends,
        "proof_artifact": False,
        "source_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
    }
    args.output.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(json.dumps({k: result[k] for k in ("period", "base_variable_count", "total_variable_count", "clause_count", "backends")}))


if __name__ == "__main__":
    main()
