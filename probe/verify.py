#!/usr/bin/env python3
'''Independent exact-integer experiments for Ayad–Bouchenna Problem 1.'''
import argparse
import json
import math
from pathlib import Path
from time import perf_counter


def reverse_arithmetic(base, value):
    result = 0
    while value:
        value, digit = divmod(value, base)
        result = result * base + digit
    return result


def lean_model(base, value):
    digits = []
    while value:
        value, digit = divmod(value, base)
        digits.append(digit)
    return sum(digit * base**i for i, digit in enumerate(reversed(digits)))


def digit_string(base, value):
    if base == 2:
        return format(value, 'b')
    if base == 10:
        return str(value)
    if base == 16:
        return format(value, 'x')
    # Independent most-significant-first, place-value extraction for base 3.
    width = 1
    while base**width <= value:
        width += 1
    chars = []
    for exponent in range(width - 1, -1, -1):
        place = base**exponent
        digit = value // place
        chars.append('0123456789abcdef'[digit])
        value -= digit * place
    return ''.join(chars)


def enumerate_property():
    rows = []
    for base in range(2, 17):
        survivors = []
        for divisor in range(1, 401):
            failures = 0
            # Deliberately examine every requested multiple, even after a failure.
            for multiplier in range(1, 4001):
                failures += reverse_arithmetic(base, divisor * multiplier) % divisor != 0
            if failures == 0:
                survivors.append(divisor)
        expected = [n for n in range(1, 401) if (base * base - 1) % n == 0]
        row = dict(base=base, survivors=survivors, expected=expected,
                   extras=sorted(set(survivors)-set(expected)),
                   missing=sorted(set(expected)-set(survivors)), tested=1600000)
        rows.append(row)
        print(json.dumps(row), flush=True)
        if row['extras'] or row['missing']:
            return dict(rows=rows, failed=True)
    return dict(rows=rows, failed=False, total_multiples=24000000)


def faithfulness():
    rows = []
    for base in (2, 3, 10, 16):
        mismatches = []
        trailing_zero_cases = 0
        for value in range(1, 100001):
            actual = lean_model(base, value)
            expected = int(digit_string(base, value)[::-1], base)
            if actual != expected:
                mismatches.append(dict(m=value, actual=actual, expected=expected))
            trailing_zero_cases += value % base == 0
        rows.append(dict(base=base, tested=100000, trailing_zero_cases=trailing_zero_cases,
                         mismatches=mismatches))
    return dict(rows=rows, failed=any(row['mismatches'] for row in rows))


def order(base, modulus):
    value = base % modulus
    period = 1
    while value != 1:
        value = value * base % modulus
        period += 1
        assert period <= modulus
    return period


def construction():
    rows = []
    failures = []
    max_exponent = 0
    for base in range(2, 12):
        count = 0
        for n in range(2, 60):
            if math.gcd(base, n) != 1:
                continue
            period = order(base, n)
            if period < 2 or (base * base - 1) % n == 0:
                continue
            c = (-(1 + base)) % n
            if c == 0:
                c = n
            exponents = [0, 1] + [i*period for i in range(1, c+1)]
            m = sum(base**e for e in exponents)
            r = reverse_arithmetic(base, m)
            formula = sum(base**(c*period-e) for e in exponents)
            if not (m > 0 and m % n == 0 and r % n != 0 and r == formula):
                failures.append(dict(base=base, n=n, T=period, c=c,
                                     m_mod_n=m%n, reverse_mod_n=r%n))
            count += 1
            max_exponent = max(max_exponent, c*period)
        rows.append(dict(base=base, cases=count))
    edge_counts = dict(n_one=0, T_one=0, T_two=0, B_two_nondivisor=0,
                       leading_one=0, leading_one_noncoprime=0)
    for base in range(2, 17):
        for n in range(1, 401):
            power = base
            while power <= n:
                power *= base
            m = n * ((power+n-1)//n)
            assert power <= m < 2*power <= base*power
            assert reverse_arithmetic(base, m) % base == 1
            assert m % n == 0
            edge_counts['leading_one'] += 1
            if math.gcd(n, base) != 1:
                assert reverse_arithmetic(base, m) % n != 0
                edge_counts['leading_one_noncoprime'] += 1
            if n == 1:
                assert all(reverse_arithmetic(base, t) % n == 0 for t in range(1, 4001))
                edge_counts['n_one'] += 1
            elif math.gcd(n, base) == 1:
                period = order(base, n)
                if period in (1, 2):
                    assert (base*base-1) % n == 0
                    edge_counts['T_one' if period == 1 else 'T_two'] += 1
                if base == 2 and (base*base-1) % n != 0:
                    edge_counts['B_two_nondivisor'] += 1
    return dict(rows=rows, cases=sum(r['cases'] for r in rows), failures=failures,
                failure_count=len(failures), max_exponent=max_exponent, edges=edge_counts,
                failed=bool(failures))


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('step', choices=['enumerate', 'faithfulness', 'construction'])
    args = parser.parse_args()
    start = perf_counter()
    result = {'enumerate': enumerate_property, 'faithfulness': faithfulness,
              'construction': construction}[args.step]()
    result['elapsed_seconds'] = perf_counter() - start
    Path('probe', args.step + '.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))
    raise SystemExit(1 if result['failed'] else 0)


if __name__ == '__main__':
    main()
