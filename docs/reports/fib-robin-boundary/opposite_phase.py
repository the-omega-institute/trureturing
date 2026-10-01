#!/usr/bin/env python3
"""Exact common-source diagnostics for opposite-parity Fibonacci sums.

The finite phase table is exhaustive at its stated modulus. Huge examples use
two modular algorithms, never construct a huge Fibonacci integer, and report
failure of sufficient stopping tests only. They are not Robin counterexamples.
"""

import argparse
from fractions import Fraction as Q
import hashlib
import json
from math import gcd, prod
from pathlib import Path
import sys

sys.dont_write_bytecode = True

from index_stopping import (BASE, D, PRIMES, STOP, fib_mod_doubling,
                            fib_mod_matrix, valuation)

TA = Q(10**12, 10**12 + 315367)


def fib(j, modulus):
    x = fib_mod_doubling(j, modulus)
    assert x == fib_mod_matrix(j, modulus)
    return x


def rational(x):
    return [x.numerator, x.denominator]


def phase_table():
    modulus, period = 9240, 240
    assert (fib(period, modulus), fib(period+1, modulus)) == (0, 1)
    values, x, y = [], 0, 1
    for j in range(period):
        assert x == fib(j, modulus)
        values.append(x)
        x, y = y, (x+y) % modulus
    rows = []
    for even in range(0, period, 2):
        for odd in range(1, period, 2):
            if (values[even]+values[odd]) % modulus == 0:
                rows.append([even, odd, values[even], values[odd]])
    assert [row[:2] for row in rows] == [[118, 119], [118, 121],
                                       [238, 1], [238, 239]]
    # Realize both relative index orders; residues are never sorted as indices.
    realizations = []
    for even, odd, _, _ in rows:
        for even_is_high in (False, True):
            e, o = even+period, odd+period
            if even_is_high:
                e += 2*period
            else:
                o += 2*period
            a, b = max(e, o), min(e, o)
            assert a-b >= 3 and b >= 2 and (a-b) % 2 == 1
            assert (fib(a, modulus)+fib(b, modulus)) % modulus == 0
            realizations.append([a, b])
    return {'modulus': modulus, 'period': period,
            'complete_even_odd_pairs_checked': (period//2)**2,
            'rows_even_odd_fib_even_fib_odd': rows,
            'legal_realizations_in_both_orders': realizations}


def seed_checks():
    fs = [0, 1]
    for _ in range(1, 302):
        fs.append(fs[-1]+fs[-2])
    norms = identities = missing = 0
    for k in range(3, 202, 2):
        a, b = fs[k-1]+1, fs[k]
        g = gcd(a, b)
        lucas = fs[k-1]+fs[k+1]
        assert a*a+a*b-b*b == lucas
        assert g == (2 if k % 3 == 0 else 1)
        assert lucas % (g*g) == 0
        norms += 1
        for j in range(2, 101):
            v = fs[j+k]+fs[j]
            assert v == a*fs[j]+b*fs[j+1]
            identities += 1
            if k == 3:
                assert v == 2*fs[j+2]
            if k % 5 == 0:
                assert lucas % 11 == 0 and v % 11 != 0
                missing += 1
    return {'odd_gaps': [3, 201], 'lower_indices': [2, 100],
            'norm_and_gcd_checks': norms, 'response_identities': identities,
            'missing_eleven_checks': missing}


def high_source(period, expected):
    a, b, k = 2*period-1, period-2, period+1
    assert period >= 6 and period % 6 == 0 and k % 3 == 1
    assert a-b == k and a % 2 != b % 2
    response_exponents = [e-BASE[p] for p, e in zip(PRIMES, expected)]
    core = prod(p**e for p, e in zip(PRIMES, response_exponents))
    assert (fib(period, core), fib(period+1, core)) == (0, 1)
    assert (fib(a, core), fib(b, core)) == (1, core-1)
    assert (fib(k-1, core)+fib(k+1, core)) % core == 1
    observed = []
    for p, e in zip(PRIMES, expected):
        modulus = p**(e+1)
        residue = 5040*(fib(a, modulus)+fib(b, modulus)) % modulus
        assert residue and valuation(residue, p) == e and e > STOP[p]
        observed.append({'p': p, 'modulus': modulus, 'residue': residue,
                         'exact_n_valuation': e})
    eta = prod(1-Q(1, p**(e+1)) for p, e in zip(PRIMES, expected))
    return {'period': period, 'indices': [a, b], 'gap': k,
            'response_core': core, 'primitive_norm_mod_core': 1,
            'observations': observed, 'eta_five': rational(eta),
            'passes_global_joint_stop': eta <= TA}


def lifted_periods():
    # A small explicit instance of the general matrix-period lifting argument.
    r, p0 = prod(PRIMES), 240
    assert (fib(p0, r), fib(p0+1, r)) == (0, 1)
    rows = []
    for t in range(1, 13):
        period, modulus = p0*r**(t-1), r**t
        assert (fib(period, modulus), fib(period+1, modulus)) == (0, 1)
        a, b = 2*period-1, period-2
        assert (fib(a, modulus), fib(b, modulus)) == (1, modulus-1)
        assert (fib(period, modulus)+fib(period+2, modulus)) % modulus == 1
        rows.append({'t': t, 'period': period, 'modulus': modulus})
    return rows


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--out', type=Path, required=True, help='output directory')
    args = ap.parse_args()
    if not __debug__:
        ap.error('optimized Python disables the exact checks; run without -O')
    low = high_source(2*D, (21, 13, 9, 7, 6))
    high = high_source(2**26*3**18*5**12*7**9*11**8, (31, 21, 13, 11, 9))
    deficit_sum = sum((Q(1, p**(e+1)) for p, e in zip(PRIMES, (31, 21, 13, 11, 9))), Q(0))
    assert deficit_sum < Q(1, 10**9) < 1-TA
    assert not high['passes_global_joint_stop']
    source_dir = Path(__file__).resolve().parent
    result = {'status': 'PASS', 'scope': 'finite exact diagnostics, not a Robin proof',
              'phase_table': phase_table(), 'odd_gap_seeds': seed_checks(),
              'high_core_sources': [low, high], 'lifted_periods': lifted_periods(),
              'joint_stop_threshold': rational(TA),
              'high_source_deficit_sum': rational(deficit_sum),
              'sources': {name: hashlib.sha256((source_dir/name).read_bytes()).hexdigest()
                          for name in ('opposite_phase.py', 'index_stopping.py')}}
    args.out.mkdir(parents=True, exist_ok=True)
    output = json.dumps(result, indent=2, sort_keys=True)+'\n'
    (args.out/'opposite_phase.json').write_text(output)
    print(output, end='')


if __name__ == '__main__':
    main()
