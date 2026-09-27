#!/usr/bin/env python3
"""A nonempty saturated actual PA marginal with unbounded lift cost.

Small literal CRT families check the construction and private witnesses.
The arbitrary-depth obstruction is the companion report's partition proof;
the large-depth certificate below uses a rational formula, not enumeration.
"""
from fractions import Fraction as F
from math import prod
from pathlib import Path
import json

Q = (5, 7, 11, 13, 17, 19)
D = prod(Q[1:])
rH = prod((F(p, p - 1) for p in Q), start=F(1)) - 1
other = prod((1 + F(p, p - 1) for p in Q[1:]), start=F(1))
target = F(566, 49)
checks = []


def check(name, claim):
    if not claim or name in checks:
        raise ValueError(name)
    checks.append(name)


def crt(a, m, b, n):
    return (a + m * ((b - a) * pow(m, -1, n) % n)) % (m * n)


def family(h, N):
    J = 2 * 3**h - 1
    K = 5**J * D
    rs = [r for r in range(1, 3**(h + 1)) if r % 3 in (0, 1)]
    check(f'h{h}N{N}: head inventory and final residue',
          len(rs) == J and rs[-1] % 3 == 1)
    rows = []

    def add(kind, j, e, t, digit=0):
        d = 1 if kind == 'pure3' else 5**j * D
        qphase = 0 if digit == 0 else crt(digit * 5**(j - 1), 5**j, 0, D)
        a = crt(t, 3**e, qphase, d)
        rows.append(dict(kind=kind, j=j, e=e, d=d, t=t,
                         qphase=qphase, m=3**e * d, a=a))

    add('pure3', 0, 1, 2)
    for j, r in enumerate(rs, 1):
        add('Q_shallow', j, 0, 0, 1)
        add('mixed_shallow', j, 1, 1, 2)
        add('head', j, h + 1, r)
    for e in range(h + 2, N + 1):
        for v in (1, 2):
            add('deep', v, e, v * 3**(e - 1))
    check(f'h{h}N{N}: distinct odd numerical labels',
          len(rows) == len({r['m'] for r in rows}) == 1 + 3 * J + 2 * (N - h - 1)
          and all(r['m'] > 1 and r['m'] % 2 for r in rows))
    check(f'h{h}N{N}: fixed CRT projections',
          all(r['a'] % r['d'] == r['qphase'] and r['a'] % 3**r['e'] == r['t'] for r in rows))
    check(f'h{h}N{N}: saturated prescribed shallow selector',
          all(len({r['qphase'] for r in rows if r['j'] == j and r['e'] <= h}) == 2
              for j in range(1, J + 1)))
    # Exact finite profiles of the first nonzero 5-digit; the zero-prefix
    # category contains every deeper or zero 5-adic point.
    shallow = [r for r in rows if r['kind'] in ('Q_shallow', 'mixed_shallow')]
    for j in range(1, J + 1):
        for digit in (1, 2, 3, 4):
            x = digit * 5**(j - 1)
            active = [r for r in shallow if x % 5**r['j'] == r['qphase'] % 5**r['j']]
            check(f'h{h}N{N}: PA trigger j{j}digit{digit}',
                  len(active) == (1 if digit in (1, 2) else 0))
    check(f'h{h}N{N}: zero-prefix PA row unchanged',
          all(r['qphase'] % 5**r['j'] != 0 for r in shallow))
    trigger5 = sum((F(2, 5**j) for j in range(1, J + 1)), F())
    check(f'h{h}N{N}: exact finite PA trigger mass',
          trigger5 == (1 - F(1, 5**J)) / 2)
    check(f'h{h}N{N}: both actual PA rows have mass one',
          F(19, 18) * F(18, 19) == 1 and F(19, 18) < F(9, 5))
    forced = [t for t in range(3**N)
              if all(not (r['qphase'] == 0 and t % 3**r['e'] == r['t']) for r in rows)]
    check(f'h{h}N{N}: common Q cylinder forces zero ternary word', forced == [0])
    for i, r in enumerate(rows):
        if r['kind'] == 'pure3':
            xq, t = 1, 2
        elif r['kind'] == 'Q_shallow':
            xq, t = crt(5**(r['j'] - 1), 5**J, 0, D), 0
        elif r['kind'] == 'mixed_shallow':
            xq, t = crt(2 * 5**(r['j'] - 1), 5**J, 0, D), rs[-1]
        else:
            xq, t = 0, r['t']
        w = crt(t, 3**N, xq, K)
        r['private_witness'] = w
        check(f'h{h}N{N}: private witness {i}',
              [a['m'] for a in rows if w % a['m'] == a['a']] == [r['m']])
    return dict(h=h, N=N, J=J, Q_period=K, original_count=len(rows),
                actual_originals=rows, PA_trigger5_mass=trigger5,
                forced_cylinder_mass=F(1, K),
                lift_growth_coefficient=(J + F(5, 4)) * other / K)


check('Haar Q query norm', rH == F(157435, 165888))
pa_bound = F(19, 18) * rH
check('nonempty actual PA query bound', pa_bound == F(2991265, 2985984) and pa_bound < 2)
small = [family(h, N) for h in (1, 2) for N in range(h + 1, h + 4)]
J = 5
coefficient = (J + F(5, 4)) * other / (5**J * D)
check('h1 exact forced-fibre growth coefficient', coefficient == F(37, 148838400))
large_N = 50_000_000
large_lower = rH + (large_N + F(1, 2)) * coefficient
check('large symbolic complete-query lower', large_lower == F(2108386799, 157593600))
check('prescribed actual PA lift crosses target', large_lower > target)
good_upper = F(3, 4) + F(7, 4) * rH / (1 - F(1, D))
check('alternative same-u law remains good',
      good_upper == F(517222215343, 214540959744) and good_upper < 3)


def encode(value):
    if isinstance(value, F):
        return str(value)
    if isinstance(value, dict):
        return {k: encode(v) for k, v in value.items()}
    if isinstance(value, list):
        return [encode(v) for v in value]
    return value


result = dict(scope='One prescribed actual nonempty PA input from saturated shallow projections; arbitrary supported lifts preserving its marginal. Auxiliary selectors and changed marginals are not obstructed.',
              PA_query_upper=pa_bound, PA_density_upper=F(19, 18),
              small_actual_families=small, symbolic_h=1, symbolic_N=large_N,
              symbolic_original_count=1 + 3 * J + 2 * (large_N - 2),
              lift_growth_coefficient=coefficient, complete_lift_lower=large_lower,
              alternative_fixed_u_query_upper=good_upper,
              checks=checks, check_count=len(checks), new_Lean=False)
out = Path(__file__).with_suffix('.json')
out.write_text(json.dumps(encode(result), indent=2) + '\n')
print(json.dumps(dict(checks=len(checks), lower=str(large_lower),
                      alternative_upper=str(good_upper), output=str(out))))
