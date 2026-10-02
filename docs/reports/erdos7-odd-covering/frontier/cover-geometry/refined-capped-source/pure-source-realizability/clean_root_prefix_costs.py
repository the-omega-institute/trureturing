#!/usr/bin/env python3
"""Exact input-cost arithmetic only; no layout/source evaluation or optimization."""
import argparse
from fractions import Fraction as F
import hashlib
import json
import math
from pathlib import Path

DEFAULT_SOURCE = Path(__file__).resolve().with_name('retained_factorial_hinge.json')
DEFAULT_RESULT = Path(__file__).resolve().with_suffix('.json')
SOURCE_SHA256 = '1e76928fa5e63ca221913ad6cdd7ba0db4a54ab093a3a2c26086e1e08b1710e5'


def derive(source):
    raw = source.read_bytes()
    if hashlib.sha256(raw).hexdigest() != SOURCE_SHA256:
        raise ValueError('Report827 dependency SHA256 mismatch')
    saved = json.loads(raw)
    if saved.get('schema') != 'e7-retained-factorial-hinge-result-v1':
        raise ValueError('wrong source result schema')
    record = saved['fixed_candidate_C']
    exact = record['exact']
    M, L, tail = (F(exact[k]) for k in ('M', 'L', 'tail'))
    if not (M > 0 and L > 0 and tail >= 0):
        raise ValueError('invalid inherited scalar signs')
    budget = 12 * L - tail
    old_primes = (5, 7, 11, 13, 17, 19, 23)
    prefixes = (
        (45, 2, (5,)),
        (315, 2, (5, 7)),
        (945, 3, (5, 7)),
        (3465, 2, (5, 7, 11)),
        (45045, 2, (5, 7, 11, 13)),
    )
    rows = []
    for period, ternary_depth, included in prefixes:
        if period != 3 ** ternary_depth * math.prod(included):
            raise ValueError('prefix period mismatch')
        omitted = [q for q in old_primes if q not in included]
        # At exponent e >= 1 there are at most (q-1)q^(e-1)
        # nonzero first-root survivor cells. Sum all such exponents exactly.
        coefficient = math.prod(1 + F(q, (q - 1) ** 2) for q in omitted) - 1
        lower = M * coefficient
        gap = lower - budget
        labels = (ternary_depth + 1) * 2 ** len(included)
        rows.append({
            'prefix_period': period,
            'numerical_label_count_including_unit': labels,
            'omitted_primes': omitted,
            'prefix_h16_identically_zero': labels <= 16,
            'tail_lower_coefficient': str(coefficient),
            'tail_lower': str(lower),
            'tail_lower_decimal': float(lower),
            'tail_lower_minus_h16_budget': str(gap),
            'excluded_at_h16_by_this_lower_bound': gap >= 0,
            'scope': 'necessary lower bound on a complete first-moment remainder, not an upper certificate',
        })
    if [r['excluded_at_h16_by_this_lower_bound'] for r in rows] != [True, True, True, True, False]:
        raise ValueError('unexpected exact budget comparison')
    layouts = 3 ** 192 * 2 ** 1280 * 5 ** 128
    return {
        'schema': 'e7-clean-root-prefix-costs-v1',
        'source_result_sha256': hashlib.sha256(raw).hexdigest(),
        'source_scope': record['scope'],
        'inherited_exact': {k: str(F(exact[k])) for k in ('M', 'L', 'tail')},
        'h16_hinge_plus_remainder_budget': str(budget),
        'h16_hinge_plus_remainder_budget_decimal': float(budget),
        'prefix_tail_obstructions': rows,
        'shallow_clean_root_compression': {
            'J': 2,
            'E_q': 1,
            'numerical_labels': 3 * 2 ** 7,
            'ambient_incidence_states_before_zero_u': 5 * 4 * 3 ** 6,
            'phase_table_count_exact': str(layouts),
            'phase_table_count_formula': '3^192 * 2^1280 * 5^128',
            'phase_table_count_log10_display': math.log10(layouts),
        },
        'performed': 'read inherited scalar outputs; rational necessary-cost bounds and combinatorial size counts',
        'not_performed': ['source reconstruction', 'new source-point evaluation', 'query-layout enumeration', 'solver', 'kernel optimization', 'new gate evaluation'],
    }


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--source', type=Path, default=DEFAULT_SOURCE)
    parser.add_argument('--result', '--compare', type=Path, default=DEFAULT_RESULT)
    parser.add_argument('--write-result', action='store_true')
    args = parser.parse_args()
    result = derive(args.source)
    if args.write_result:
        args.result.write_text(json.dumps(result, indent=2) + '\n')
    elif json.loads(args.result.read_text()) != result:
        raise ValueError('saved result mismatch')
    print(json.dumps({
        'status': 'exact input-cost arithmetic passed',
        'prefixes': len(result['prefix_tail_obstructions']),
        'scope': result['performed'],
    }))


if __name__ == '__main__':
    main()
