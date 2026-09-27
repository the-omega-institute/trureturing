#!/usr/bin/env python3
"""Exact checks for whole-root reserves with arbitrary pure-3 originals.

Python 3.9+ standard library only. Place beside the pinned inputs or pass
--source-dir. Fractions decide every comparison; floats are display-only.
The ordinary proof supplies arbitrary phases and unbounded finite heights.
The finite examples are interface controls, not new noncoverage instances.
"""
from argparse import ArgumentParser
from fractions import Fraction as F
from hashlib import sha256
from itertools import product
from math import gcd, prod
from pathlib import Path
import json

INPUTS = {
    'height_three_clipping_envelope.json':
        '276d7e266a86ed8e5a1c9da2982b219725c2738bc4ad19da1243bf8575543685',
    'four_level_query_hinge_lift.json':
        'b224c79716585f16b52aeda277810a1a001a4f2d92d3e092cfc1cc41345dbcfd',
}
Q = (5, 7, 11, 13, 17, 19)


def exact(value):
    value = F(value)
    return {'exact': str(value), 'decimal': float(value)}


def crt(a, m, b, n):
    if gcd(m, n) != 1:
        raise ValueError('CRT requires coprime moduli')
    return (a + m * (((b-a) * pow(m, -1, n)) % n)) % (m*n)


def main():
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--source-dir', type=Path, default=Path(__file__).resolve().parent)
    parser.add_argument('--output', type=Path, default=Path(__file__).with_suffix('.json'))
    args = parser.parse_args()
    checks, inputs, provenance = [], {}, []

    def need(name, condition):
        if not condition:
            raise ValueError('FAILED: ' + name)
        checks.append(name)

    for name, expected in INPUTS.items():
        raw = (args.source_dir/name).read_bytes()
        need('pinned input ' + name, sha256(raw).hexdigest() == expected)
        inputs[name] = json.loads(raw)
        provenance.append({'path': name, 'sha256': expected})
    env = inputs['height_three_clipping_envelope.json']
    hinge = inputs['four_level_query_hinge_lift.json']
    B, target = F(env['B']), F(env['target'])
    alpha = min(F(c['alpha']['exact']) for c in hinge['corners'])
    need('same supplier query bound', B == F(hinge['B']['exact']))
    need('same source mass corner set', {F(c['alpha']) for c in env['corners']} ==
         {F(c['alpha']['exact']) for c in hinge['corners']})
    need('same continuation target', target == F(566, 49))

    gate_coefficient = (target-B)/(1+B)
    load_threshold = 27*(gate_coefficient-1)/(2*gate_coefficient-1)

    def coefficient(u):
        return (27-u)/(27-2*u)

    need('positive strict load threshold in stated domain', 2 < load_threshold < 9)
    need('load threshold is exact certificate equality',
         coefficient(load_threshold) == gate_coefficient)
    need('load threshold fraction', load_threshold ==
         F(20750635627803642642318, 10004205239367061830851))

    capacities = []
    for u in (F(0), F(1), F(2), load_threshold, F(4), F(8)):
        M, lam = (18-u)/(27-2*u), 1/(27-2*u)
        t = 18*lam
        need('valid uniform root parameters ' + str(u), F(1, 2) <= M < 1 and t > 0)
        need('individual and joint reserves ' + str(u),
             t*(F(1, 2)-u/18) == 1-M and t*(F(3, 2)-u/9) == 1)
        need('complete query coefficient ' + str(u), M+t/2 == coefficient(u))
        for h in (2, 4, 8, 40):
            need('all query heights u=' + str(u) + ' h=' + str(h),
                 sum((t/F(3**(e-1)) for e in range(2, h+1)), F(0)) +
                 t/F(2*3**(h-1)) == t/2)
        N = B+coefficient(u)*(1+B)
        density = 27*t/alpha
        haar = alpha*(566-49*N)*(27-2*u)/299376
        need('density and continuation identity ' + str(u),
             density == 486*lam/alpha and
             haar == ((566-49*N)/567)/(density*F(616, 567)))
        capacities.append({'load_cap': exact(u), 'M': exact(M), 'lambda': exact(lam),
                           'coefficient': exact(coefficient(u)), 'query_upper': exact(N),
                           'density_upper': exact(density),
                           'continuation_expression': exact(haar),
                           'strict_positive_continuation': bool(haar > 0)})

    N2 = B+F(25, 23)*(1+B)
    H2 = alpha*(566-49*N2)*23/299376
    need('two-load exact query upper', N2 == F(954033422610567164877, 82756918465638658925))
    need('two-load strict query gate', N2 < target)
    need('two-load exact positive Haar continuation',
         H2 == F(92778143633689872577, 10483863107625824716800000) and H2 > F(1, 113000))

    # All choices of zero or one pure original at each of depths1,2,3.
    # This checks arbitrary phases, missing depths, and nested/dead entries.
    # It does not replace the general union argument at arbitrary height.
    pattern_count, weight_controls = 0, 0
    for phases in product([None] + list(range(3)),
                          [None] + list(range(9)),
                          [None] + list(range(27))):
        roots = [r for r in range(3) if r != phases[0]][:2]
        pure = [(3**(i+1), a) for i, a in enumerate(phases) if a is not None]
        losses = []
        for r in roots:
            cells = list(range(r, 27, 3))
            losses.append(F(sum(any(z % m == a for m, a in pure) for z in cells), 9))
        if len(roots) != 2 or sum(losses) > F(1, 2):
            raise ValueError('pure root union budget failed')
        for u in (F(0), F(2), F(4), F(8)):
            M, t = (18-u)/(27-2*u), 18/(27-2*u)
            lower = [1-p-u/18 for p in losses]
            w2 = min(M, t*lower[1])
            weights = (1-w2, w2)
            if not (sum(weights) == 1 and all(0 < w <= M and w <= t*k
                                              for w, k in zip(weights, lower))):
                raise ValueError('constant post-restriction root weights failed')
            weight_controls += 1
        pattern_count += 1
    need('complete depth-three pure pattern controls', pattern_count == 1120)
    need('fixed-weight controls include sparse and overlapping pure patterns', weight_controls == 4480)

    # Exact product source of the parametric six-cofactor control family.
    actual_RQ = prod((1+F(q, (q-1)*(q-2)) for q in Q), start=F(1))-1
    simultaneous_mass = prod((F(1, q-2) for q in Q), start=F(1))
    need('actual full-height product-source query norm', actual_RQ == F(214267985, 147806208))
    need('six simultaneous active cofactors have positive source mass', simultaneous_mass == F(1, 378675))
    old_actual_upper = actual_RQ+F(27, 23)*(1+actual_RQ)
    need('older method succeeds on control source with its actual query norm',
         old_actual_upper == F(7352083433, 1699771392) and old_actual_upper < target)

    families = []
    for H in (3, 4, 8, 40):
        rows = [{'m': 3, 'phase': 1, 'e': 1, 'q': 1, 'Q_phase': 0, 't': 1, 'name': 'pure1'}]
        for e in range(2, H+1):
            t = 2*3**(e-1)
            rows.append({'m': 3**e, 'phase': t, 'e': e, 'q': 1,
                         'Q_phase': 0, 't': t, 'name': 'pure'+str(e)})
        for q, deep in zip(Q, (3, 12, 21, 2, 5, 8)):
            rows.extend([
                {'m': q, 'phase': 0, 'e': 0, 'q': q, 'Q_phase': 0, 't': 0, 'name': str(q)+'-shallow0'},
                {'m': 3*q, 'phase': crt(2, 3, 1, q), 'e': 1, 'q': q, 'Q_phase': 1, 't': 2, 'name': str(q)+'-shallow1'},
                {'m': 81*q, 'phase': crt(deep, 81, 2, q), 'e': 4, 'q': q, 'Q_phase': 2, 't': deep, 'name': str(q)+'-deep4'},
            ])
        need('distinct original numerical labels H='+str(H),
             len(rows) == H+18 and len({r['m'] for r in rows}) == len(rows) and
             all(r['m'] > 1 and r['m'] % 2 for r in rows))
        need('mandatory shallow selector H='+str(H),
             all(r['Q_phase'] in (0, 1) for r in rows if r['q'] > 1 and r['e'] <= 3))
        need('three actual phases through height four H='+str(H),
             all({r['Q_phase'] for r in rows if r['q'] == q} == {0, 1, 2} for q in Q))
        pure_rows = [r for r in rows if r['q'] == 1 and r['e'] >= 2]
        deep_rows = [r for r in rows if r['q'] > 1 and r['e'] == 4]
        cylinders = pure_rows + deep_rows
        need('all pure-tail and residual cylinders are disjoint H='+str(H),
             all((a['t']-b['t']) % (3**min(a['e'], b['e'])) != 0
                 for i, a in enumerate(cylinders) for b in cylinders[i+1:]))
        p0 = sum((F(1, 3**(e-1)) for e in range(2, H+1)), F(0))
        epsilon = F(1, 2*3**(H-1))
        c0, c2 = 1-p0-F(1, 9), F(8, 9)
        need('pure budget exact finite sum H='+str(H), p0 == F(1, 2)-epsilon)
        need('two root exact extreme reserves H='+str(H), c0 == F(7, 18)+epsilon)
        need('both branch loads equal two at simultaneous point H='+str(H),
             all(sum((F(54, 3**r['e']) for r in deep_rows if r['t'] % 3 == root), F(0)) == 2
                 for root in (0, 2)))
        whole_pure_mass = (2-p0)/3
        root_C = (c2+F(1, 2))/(c0+c2)
        whole_C = 1/(2*(whole_pure_mass-F(2, 27)))
        power = F(3)**(3-H)
        need('exact root versus whole-pure uniform coefficients H='+str(H),
             root_C == 25/(23+power) and whole_C == 27/(23+power))
        need('common-B certificate comparison H='+str(H), root_C < gate_coefficient < whole_C)
        witnesses = []
        for original in rows:
            point, period = original['t'], 3**max(H, 4)
            for q in Q:
                residue = original['Q_phase'] if original['q'] == q else 3
                point = crt(point, period, residue, q)
                period *= q
            hits = [r['name'] for r in rows if point % r['m'] == r['phase']]
            need('private residue H='+str(H)+' '+original['name'], hits == [original['name']])
            witnesses.append({'original': original['name'], 'residue': str(point), 'period': str(period)})
        families.append({'pure_height': H, 'originals': rows, 'private_witnesses': witnesses,
                         'p0': exact(p0), 'c0_min': exact(c0), 'c2_min': exact(c2),
                         'whole_pure_Haar_mass': exact(whole_pure_mass),
                         'root_uniform_coefficient': exact(root_C),
                         'whole_pure_uniform_coefficient': exact(whole_C)})

    output = {'schema': 'arbitrary-pure-root-reserve-v1', 'sources': provenance,
              'scope': ['Ordinary root-reserve corollary, not new Lean or unrestricted Erdos7.',
                        'Arbitrary pure3 phases and finite heights; shallow two-phase and root-load hypotheses remain.',
                        'The finite star families already admit older noncoverage certificates.',
                        'Generic B interface comparisons do not exclude using the smaller actual R_Q.'],
              'B': exact(B), 'alpha_min': exact(alpha), 'target': exact(target),
              'strict_load_threshold': exact(load_threshold), 'uniform_parameters': capacities,
              'pure_pattern_count': pattern_count, 'fixed_weight_controls': weight_controls,
              'actual_source_RQ': exact(actual_RQ), 'all_six_active_mass': exact(simultaneous_mass),
              'successful_older_actual_source_bound': exact(old_actual_upper),
              'families': families, 'check_count': len(checks), 'checks': checks}
    args.output.write_text(json.dumps(output, indent=2, sort_keys=True)+'\n')
    print(json.dumps({'checks': len(checks), 'output': str(args.output),
                      'query_upper_at_two': exact(N2), 'Haar_lower_at_two': exact(H2)}, sort_keys=True))


if __name__ == '__main__':
    main()
