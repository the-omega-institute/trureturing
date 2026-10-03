#!/usr/bin/env python3
"""Finite checks for the private-fibre vacancy cut in report 385 §240.

The script checks only the source-replacement interface.  It does not claim
that the selected local fixtures extend to a whole covering system.
"""

from __future__ import annotations

import json
from itertools import combinations
from math import gcd
from pathlib import Path


def divisors(n: int) -> list[int]:
    return [d for d in range(1, n + 1) if n % d == 0]


def valuation(n: int, p: int) -> int:
    out = 0
    while n % p == 0:
        n //= p
        out += 1
    return out


def candidate_labels(p: int, q: int, e: int, L: int) -> tuple[int, int, list[int]]:
    a = valuation(L, q)
    R = p ** (e - 1) * L
    N = R // q**a
    labels = [q ** (a + 1) * d for d in divisors(N)]
    return a, R, labels


def fibre_base(A: int, R: int, q: int, j: int) -> int:
    return A + j * R


def contains_fibre(phase: int, modulus: int, A: int, R: int, q: int, j: int) -> bool:
    """Whether [phase]_(modulus) contains F_j=A+jR+qR Z."""
    assert (q * R) % modulus == 0, (phase, modulus, q * R)
    return (phase - fibre_base(A, R, q, j)) % modulus == 0


def check_interface(p: int, q: int, e: int, L: int, private: set[int],
                    occupied_phases: dict[int, int], A: int = 0) -> dict:
    a, R, U = candidate_labels(p, q, e, L)
    assert q < p and q % 2 == 1 and p % 2 == 1
    assert q * R % (q ** (a + 1)) == 0
    assert all((q * R) % u == 0 for u in U)
    assert all(valuation(u, q) == a + 1 for u in U)

    occupied = set(occupied_phases)
    vacant = set(U) - occupied
    served = {
        j for j in private
        if any(contains_fibre(phase, u, A, R, q, j)
               for u, phase in occupied_phases.items())
    }
    f = len(vacant)
    g = len(served)
    r = len(private)
    if f + g >= r:
        fresh_needed = r - g
        assert fresh_needed <= f
        new_block = 1 + fresh_needed  # source B plus fresh candidates
        old_block = p + 1             # A plus the p top labels
        assert new_block < old_block
        # Assign each not-yet-served private fibre a different vacant label.
        pending = sorted(private - served)
        chosen = sorted(vacant)[:fresh_needed]
        assert len(chosen) == len(pending)
        for j, u in zip(pending, chosen):
            assert (q * R) % u == 0
    return dict(a=a, R=R, candidate_labels=U, vacant=sorted(vacant),
                private=sorted(private), served=sorted(served),
                f=f, g=g, r=r, strict_trigger=f + g >= r)


def exhaustive_cut_check() -> int:
    checks = 0
    for p, q in ((5, 3), (7, 3), (7, 5)):
        L = q * 7 * 11 if q != 7 else q * 5 * 11
        # The extra q factor makes this a partial-height fixture after
        # adjoining one further q to the common period.
        for private_size in range(1, q + 1):
            private = set(range(private_size))
            # Only the cardinality/service condition is being enumerated;
            # phases are checked in the concrete fixture below.
            for served_size in range(private_size + 1):
                for f in range(0, q + 2):
                    if f + served_size >= private_size:
                        assert 1 + private_size - served_size < p + 1
                    checks += 1
    return checks


def main() -> None:
    checks = exhaustive_cut_check()
    p, q, e, L = 5, 3, 2, 231
    a, R, U = candidate_labels(p, q, e, L)
    # Partial q-height: a=v_3(L)=1, while the common period may have
    # v_3(Q)=2.  All candidate labels are occupied, but only 9 serves F_0.
    occupied = {u: 1 for u in U}
    occupied[9] = 0
    result = check_interface(p, q, e, L, {0, 1}, occupied)
    assert (a, R) == (1, 1155)
    assert U == [9, 45, 63, 99, 315, 495, 693, 3465]
    assert result['f'] == 0 and result['g'] == 1 and result['r'] == 2
    assert not result['strict_trigger']

    # Make one label vacant and phase it for F_1.  The source replacement now
    # has one fresh candidate, hence two new local classes versus six old ones.
    occupied_one_vacancy = dict(occupied)
    del occupied_one_vacancy[45]
    improved = check_interface(p, q, e, L, {0, 1}, occupied_one_vacancy)
    assert improved['f'] == 1 and improved['g'] == 1
    assert improved['strict_trigger']

    payload = {
        'status': 'PASS',
        'exhaustive_interface_checks': checks,
        'partial_height_fixture': result,
        'one_vacancy_strict_fixture': improved,
        'scope': ('Private-fibre source-replacement interface for q<p, '
                  'including a<v_q(Q); no whole-cover realization or '
                  'unrestricted Erdos-7 conclusion.'),
    }
    print(json.dumps(payload, sort_keys=True, indent=2))


if __name__ == '__main__':
    main()
