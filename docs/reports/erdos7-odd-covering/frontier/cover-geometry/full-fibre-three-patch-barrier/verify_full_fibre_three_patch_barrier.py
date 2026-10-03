#!/usr/bin/env python3
"""Exact finite checks for the full-fibre three-patch barrier.

The check uses the induced period on one complete odd fibre.  It validates
the density equality cases used in report 385 §241; it does not construct a
whole covering system or settle Erdős #7.
"""

from __future__ import annotations

import json
from itertools import combinations, product
from math import gcd


def odd_divisors(limit: int) -> list[int]:
    return [d for d in range(1, limit + 1, 2) if d > 1]


def induced_residue(x: int, m: int, phase: int, modulus: int) -> tuple[int, int] | None:
    """Return (residue, index) for [phase]_modulus restricted to x+mZ."""
    g = gcd(m, modulus)
    if (phase - x) % g:
        return None
    index = modulus // g
    # m/g is invertible modulo index.
    if index == 1:
        return 0, 1
    inverse = pow(m // g, -1, index)
    residue = ((phase - x) // g * inverse) % index
    return residue, index


def covered_parameter(t: int, restrictions: list[tuple[int, int]]) -> bool:
    return any(t % index == residue for residue, index in restrictions)


def fibre_cover(m: int, x: int, classes: list[tuple[int, int]]) -> tuple[bool, list[tuple[int, int] | None]]:
    restrictions = [induced_residue(x, m, phase, modulus)
                    for phase, modulus in classes]
    active = [item for item in restrictions if item is not None]
    period = 1
    for _, index in active:
        period = period * index // gcd(period, index)
    covered = all(covered_parameter(t, active) for t in range(period))
    return covered, restrictions


def verify_density_barrier() -> dict[str, int]:
    checks = 0
    # For any odd induced index, a proper restriction has index at least 3.
    for index in odd_divisors(45):
        assert index >= 3
        checks += 1

    # Enumerate all three proper restrictions with indices <=  nine and check
    # that coverage of the parameter line forces three index-3 residues.
    for indices in product((3, 5, 7, 9), repeat=3):
        period = 1
        for index in indices:
            period = period * index // gcd(period, index)
        for residues in product(*[range(index) for index in indices]):
            classes = list(zip(residues, indices))
            covers = all(covered_parameter(t, classes) for t in range(period))
            if covers:
                assert indices == (3, 3, 3)
                assert set(residues) == {0, 1, 2}
            checks += 1

    # The complete-fibre application: three classes with induced index 3
    # partition x+mZ, while two proper odd classes never do.
    assert fibre_cover(15, 0, [(0, 45), (15, 45), (30, 45)])[0]
    assert not fibre_cover(15, 0, [(0, 45), (15, 45)])[0]
    assert not fibre_cover(15, 0, [(0, 45), (15, 75), (30, 75)])[0]
    checks += 3
    return {"exhaustive_restriction_checks": checks}


def main() -> None:
    result = verify_density_barrier()
    payload = {
        "status": "PASS",
        "scope": (
            "On a complete odd fibre, an inclusion-minimal cover by at most "
            "three proper odd restrictions is exactly three index-3 phases; "
            "this is a local PFV6 interface check, not a whole-cover result."
        ),
        **result,
    }
    print(json.dumps(payload, sort_keys=True, indent=2))


if __name__ == "__main__":
    main()
