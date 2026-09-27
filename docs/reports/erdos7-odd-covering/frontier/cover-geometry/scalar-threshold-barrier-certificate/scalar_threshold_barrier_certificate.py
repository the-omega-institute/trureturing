#!/usr/bin/env python3
"""Exact fixed-order scalar threshold certificate, using only the standard library.

Evaluate all 378675 integer-grid objectives as Fractions. The mathematical
real-to-integer reduction is supplied in Chapter 40. Every high-product
tail remains in its exact full first moment. The JSON is deterministic:
execution time is printed only to stdout. Run from any working directory
with --output FILE. Checks remain enabled under Python -O.
"""
import argparse
from fractions import Fraction as F
from hashlib import sha256
from math import prod
from pathlib import Path
from time import monotonic
import json
import sys

PRIMES = (5, 7, 11, 13, 17, 19)
LIMIT = 16
EXPECTED = F(38015512875791085444068380947478658842921999427,
             37918700535989642067334158824877050925450000000)
MODEL = {
    'prime_order': list(PRIMES),
    'independent_runs': True,
    'deterministic_thresholds': True,
    'root_positive_depth_tail': 'Pr(K_0 >= a) = 2/3**a for integer a >= 1',
    'threshold_domain': '0 <= t_i < p_i-2',
    'child_positive_depth_tail': 'Pr(K_i >= a) = min(1,(p_i-1)/((p_i-2-t_i)*p_i**a)) for integer a >= 1',
    'objective': 'sum_i E[(prod_(0 <= j < i)(1+K_j)-1-t_i)_+]/(p_i-2-t_i)',
}


def require(condition, message):
    if not condition:
        raise ArithmeticError(message)


def low_law(p, beta):
    cap = F(p - 1, beta)
    return {1: 1 - cap / p, **{n: cap * F(p - 1, p ** n) for n in range(2, LIMIT + 1)}}


def convolve(left, right):
    out = {n: F(0) for n in range(1, LIMIT + 1)}
    for a, wa in left.items():
        for b in range(1, LIMIT // a + 1):
            out[a * b] += wa * right[b]
    return out


def hinges(mean, law, maximum):
    # h[T]=E[(Y-T)+]; h[T+1]-h[T] = -Pr(Y>T).
    result = {1: mean - 1}
    cdf = F(0)
    for T in range(1, maximum):
        cdf += law[T]
        result[T + 1] = result[T] - 1 + cdf
    return result


def compute():
    options = {p: [(t, p - 2 - t, low_law(p, p - 2 - t)) for t in range(p - 2)]
               for p in PRIMES}
    initial = {1: F(1, 3), **{n: F(4, 3 ** n) for n in range(2, LIMIT + 1)}}
    count, above_one, first, second = 0, 0, None, None

    def visit(i, law, mean, accumulated, schedule, costs):
        nonlocal count, above_one, first, second
        p = PRIMES[i]
        profile = hinges(mean, law, p - 2)
        for t, beta, child in options[p]:
            cost = profile[t + 1] / beta
            value = accumulated + cost
            if i + 1 == len(PRIMES):
                count += 1
                above_one += value > 1
                row = (value, schedule + (t,), costs + (cost,))
                if first is None or value < first[0]:
                    second, first = first, row
                elif second is None or value < second[0]:
                    second = row
            else:
                visit(i + 1, convolve(law, child), mean * F(beta + 1, beta),
                      value, schedule + (t,), costs + (cost,))

    visit(0, initial, F(2), F(0), (), ())
    require(count == prod(p - 2 for p in PRIMES) == 378675, 'Complete grid size mismatch')
    require(above_one == count, 'A grid objective is at most one')
    require(first[0] == EXPECTED and first[1] == (0, 1, 3, 5, 7, 9), 'Exact minimum mismatch')
    require(1 < first[0] < second[0], 'Exact strict separation mismatch')
    require(second[1] == (0, 1, 3, 5, 7, 8), 'Runner-up schedule mismatch')
    model_bytes = (json.dumps(MODEL, sort_keys=True, separators=(',', ':')) + '\n').encode()
    return {
        'schema': 'scalar-threshold-barrier-certificate-v1',
        'scope': 'Exact fixed-order independent-run additive-hinge model on all integer grid points. The real-parameter reduction is an ordinary analytic proof in Chapter 40, not a Lean certificate.',
        'model': MODEL,
        'model_input_encoding': 'UTF-8 JSON, sort_keys=True, separators=(comma,colon), followed by one LF',
        'model_input_sha256': sha256(model_bytes).hexdigest(),
        'producer_sha256': sha256(Path(__file__).read_bytes()).hexdigest(),
        'external_input_files': [],
        'integer_threshold_ranges': [list(range(p - 2)) for p in PRIMES],
        'retained_positive_product_states': list(range(1, LIMIT + 1)),
        'full_mean_retained_exactly': True,
        'grid_points': count,
        'grid_points_strictly_above_one': above_one,
        'minimum': str(first[0]),
        'minimizer': list(first[1]),
        'minimum_stage_costs': list(map(str, first[2])),
        'runner_up': str(second[0]),
        'runner_up_schedule': list(second[1]),
        'runner_up_stage_costs': list(map(str, second[2])),
        'strict_excess_over_one': str(first[0] - 1),
        'method': 'Exact Fractions; successive hinge differences; source-oriented low-product convolution; no rounding or high-product tail truncation.',
    }


def main():
    if sys.version_info < (3, 10):
        raise SystemExit('Python 3.10 or later is required')
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True, help='Deterministic JSON certificate path')
    args = parser.parse_args()
    started = monotonic()
    result = compute()
    payload = (json.dumps(result, indent=2) + '\n').encode()
    args.output.write_bytes(payload)
    print('PASS: all 378675 exact grid objectives exceed one; minimum and runner-up separated.')
    print('model_input_sha256=' + result['model_input_sha256'])
    print('producer_sha256=' + result['producer_sha256'])
    print('certificate_sha256=' + sha256(payload).hexdigest())
    print(f'elapsed_seconds={monotonic() - started:.6f}')


if __name__ == '__main__':
    main()
