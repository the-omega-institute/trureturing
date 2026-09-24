#!/usr/bin/env python3
"""Computable complete omitted tails for the actual116/124 head bridge.

All five prefix remainders and the complementary positive-seven tail
recover98/109 exactly on each whole K face. The theorem is profile125.
"""
import argparse
from fractions import Fraction as F
from hashlib import sha256
import importlib.util
from itertools import product
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
CERTIFICATE = 'certificates/source_norms/cover-geometry/complete_off_face_omitted_tails.json'
PINS = {
    'certificate_io.py': '2318639f574d9f6fab4c7187c2736cde559e1925a5f9fa657afe0b8334f7d02b',
    'frontier/source-budgets/source_cost_endpoint_attainment.py': '9c22b67d249f21e86e0292189c7808db023fd9c45090911f7c58bffa6b6d1ea2',
}
ROOT = (0, 0, 1, 1, 1)
CARRIERS = tuple(product((-1, 0, 1), (-1, 0, 1, 2, 3, 4)))
SELECTED = ((0, 2), (3, 0), (1, 2), (4, 0))
HEAD = frozenset(((0, 0), (1, 0), (2, 0), (0, 1), (1, 1), (2, 1)))


def require(condition, message):
    if not condition:
        raise ValueError(message)


def module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    require(spec is not None and spec.loader is not None, 'Loadable input '+str(path))
    result = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(result)
    return result


def encode(value):
    if isinstance(value, F):
        return str(value)
    if isinstance(value, dict):
        return {str(k): encode(v) for k, v in value.items()}
    if isinstance(value, (tuple, list)):
        return [encode(v) for v in value]
    return value


def rational(value):
    require(isinstance(value, (int, F)) and not isinstance(value, bool), 'Exact rational input')
    return F(value)


def label_cap(branches, raw_coefficient, prime, depth):
    """Branches are(c,error,H); every original label has this assigned cap."""
    require(branches and isinstance(prime, int) and prime > 1 and isinstance(depth, int) and depth >= 0,
            'Nonempty family and integer prime/depth')
    q = F(1, prime**depth)
    return min(raw_coefficient*q, max(c*q+min(e, H*q) for c, e, H in branches))


def complete_series(branches, raw_coefficient, prime, start, omitted=()):
    branches = tuple(tuple(map(rational, branch)) for branch in branches)
    raw_coefficient = rational(raw_coefficient)
    require(branches and all(min(branch) >= 0 for branch in branches) and raw_coefficient >= 0,
            'Positive reference, excess mass and raw cap')
    require(prime > 1 and isinstance(prime, int) and isinstance(start, int) and start >= 0,
            'Complete geometric family')
    omitted = frozenset(omitted)
    require(all(isinstance(n, int) and n >= start for n in omitted), 'Exact removed original depths')
    N = start
    for c, e, H in branches:
        if e > 0:
            crossing = start
            while H*F(1, prime**crossing) > e:
                crossing += 1
            N = max(N, crossing)
    finite = sum((label_cap(branches, raw_coefficient, prime, n)
                  for n in range(start, N) if n not in omitted), F(0))
    tail_coefficient = min(raw_coefficient, max(c+(H if e > 0 else 0) for c, e, H in branches))
    geometric = F(1, prime**N)/(1-F(1, prime))
    geometric -= sum((F(1, prime**n) for n in omitted if n >= N), F(0))
    require(geometric >= 0, 'All omitted original labels removed before complete summation')
    return {'upper': finite+tail_coefficient*geometric, 'crossing': N,
            'tail_coefficient': tail_coefficient, 'omitted': sorted(omitted)}


def complete_tails(dat, pi, defects, z):
    """dat=source.data(theta); defects uses E5,E15,E3,E5d,E15d,omega,rho.

    E5/E15 include the r/5 and r1/5 shallow losses. rho is the same
    actual residual as the bounded head, not a fresh allowance per tail.
    z is the original pure5 survivor mass and is not recoverable from dat.
    """
    require(len(dat) == 5, 'Original source data tuple')
    d, n, eta = tuple(tuple(map(rational, row)) for row in dat[:3])
    s, z = rational(dat[3]), rational(z)
    require(len(d) == len(n) == len(eta) == 5 and all(F(1, 4) <= v <= 1 for v in d)
            and all(F(1, 18) <= v <= F(1, 9) for v in eta)
            and all(0 <= n[i] <= eta[i]*d[i] for i in range(5)) and sum(n) == s,
            'Necessary actual effective-source bounds, not a realizability certificate')
    h, h0, h1, D = sum(eta), sum(eta[:2]), sum(eta[2:]), max(d)
    require(F(1, 2) <= h <= F(5, 9) and h1 > h0, 'Effective ternary source and root1 capacity branch')
    require(F(3, 4) <= z <= 1 and D <= z, 'Actual pure5 survivor mass')
    pi = tuple(map(rational, pi))
    require(len(pi) == 18 and min(pi) >= 0 and sum(pi) == 1, 'One actual normalized shallow carrier mixture')
    t = tuple(sum(v*(int(ROOT[l] == u)+int(l == c)) for v, (u, c) in zip(pi, CARRIERS)) for l in range(5))
    a = tuple(1-v/5 for v in t)
    require(min(a) >= F(3, 5), 'Positive exact shallow3/9 density')
    needed = ('E5', 'E15', 'E3', 'E5d', 'E15d', 'omega', 'rho')
    require(set(defects) == set(needed), 'Explicit complete shared defect coordinates')
    E5, E15, E3, E5d, E15d, omega, rho = (rational(defects[k]) for k in needed)
    require(min(E5, E15, E3, E5d, E15d, omega, rho) >= 0
            and E5 <= h/25 and E15 <= h1/25 and E3 <= D/90
            and E5d <= h/100 and E15d <= h1/100
            and E5+E15+E3+E5d+E15d+omega <= rho, 'One actual shared capacity and union-error budget')
    kappa = h1/(h1-h0)
    c3 = max(a[l]*d[l]-F(1+ROOT[l], 20) for l in range(5))
    eps3 = E5+E5d+kappa*(E15+E15d)+omega
    c5, eps5 = sum(eta[l]*a[l] for l in range(5))-F(1, 90), E3+(z-D)/90+omega
    root1_coeff = sum(eta[l]*a[l] for l in range(2, 5))
    root0_dominated = h0 <= root1_coeff
    root_branches = ((root1_coeff, omega, h1-root1_coeff),)
    if not root0_dominated:
        root_branches += ((h0, F(0), F(0)),)
    families = {
        'pure3': {'prime': 3, 'start': 3, 'raw': D, 'branches': ((c3, eps3, D-c3),)},
        'pure5': {'prime': 5, 'start': 2, 'raw': h, 'branches': ((c5, eps5, h-c5),)},
        'root5': {'prime': 5, 'start': 2, 'raw': h1,
                  'branches': root_branches},
        'cell5': {'prime': 5, 'start': 2, 'raw': max(eta),
                  'branches': tuple((eta[l]*a[l], omega, eta[l]*(1-a[l])) for l in range(5))},
    }
    require(c3 >= F(1, 20) and c5 >= F(13, 45) and root1_coeff >= 0,
            'All survivor-excess references are positive')
    def cap(name, depth):
        row = families[name]
        return label_cap(row['branches'], row['raw'], row['prime'], depth)
    selected = (cap('pure5', 2), cap('pure3', 3), cap('root5', 2), cap('pure3', 4))
    remainders, detail = {}, {}
    for k in range(5):
        omissions = {'pure3': ({3} if k >= 2 else set()) | ({4} if k >= 4 else set()),
                     'pure5': {2} if k >= 1 else set(), 'root5': {2} if k >= 3 else set(), 'cell5': set()}
        rows = {name: complete_series(row['branches'], row['raw'], row['prime'], row['start'], omissions[name])
                for name, row in families.items()}
        remainders[k] = sum(row['upper'] for row in rows.values())+F(1, 72)
        detail[k] = rows
    require(all(remainders[k] == remainders[0]-sum(selected[:k]) for k in range(5)),
            'Exact removal of the same assigned original-label cap terms')
    root_n = max(sum(n[:2]), sum(n[2:]))
    C = root_n+max(n)+D/18+(h+h1+max(eta))/4+F(1, 72)
    positive7 = C/5-F(6, 35)*(root_n+h/5)
    require(positive7 >= 0, 'All complementary positive-seven cap coefficients remain nonnegative')
    return {'old_remainders': remainders, 'selected_caps': selected, 'positive7': positive7,
            'family_parameters': families, 'complete_series': detail, 'raw_old_nonunit_cap': C,
            'raw_deep_mixed': F(1, 72), 'actual_source_mass': s, 'z': z,
            'root0_raw_dominated': root0_dominated, 'root_wrong_price': kappa,
            'shared_defects': dict(defects), 'unused_named_defect_budget': rho-E5-E15-E3-E5d-E15d-omega}


def finite_case(parent, constructor, source, mode):
    A, B, P, height = 27, 125, 343, 3
    sources = [constructor.source(a, b, 'off-diagonal') for a, b in product(range(4), repeat=2) if a+b]
    old = [(x, y) for x, y in product(range(A), range(B))
           if not any(x % 3**a == ra and y % 5**b == rb for a, ra, b, rb in sources)]
    pure7 = (1 << P)-1
    for e in range(1, 4):
        for v in range(6*7**(e-1), P, 7**e):
            pure7 &= ~(1 << v)
    seven_mass = pure7.bit_count()
    original = []
    for e in range(1, 4):
        for a, b, ra, rb, family in ((1, 0, 1, 0, 'shallow'), (2, 0, 3, 0, 'shallow'),
                                    (3, 0, 3 if mode != 'root-spill' else 7, 0, 'E3')):
            original.append((a, b, e, ra, rb, family))
        for b in range(1, 4):
            original.append((0, b, e, 0, 4, 'E5' if b == 1 else 'E5d'))
            root = (b+e) % 3 if mode == 'wrong-roots' else 1
            original.append((1, b, e, root, 4, 'E15' if b == 1 else 'E15d'))
    labels = []
    for a, b, e, ra, rb, family in original:
        re = ((a+1)*(b+1)+e*e) % 7**e
        seven = sum(1 << v for v in range(re, P, 7**e)) & pure7
        labels.append((a, b, ra, rb, F(6, 5*7**e), seven, family))
    mu, survival, Vfamily = {}, {}, {name: F(0) for name in ('shallow', 'E3', 'E5', 'E15', 'E5d', 'E15d')}
    virtual_mass, deleted_mass = F(0), F(0)
    for x, y in old:
        union, virtual = 0, F(0)
        for a, b, ra, rb, u, seven, family in labels:
            if x % 3**a == ra and y % 5**b == rb:
                virtual += u
                union |= seven
                Vfamily[family] += u/(A*B)
        deletion = F(union.bit_count(), seven_mass)
        require(deletion <= virtual, 'The actual same-label union is dominated by its virtual caps')
        survival[x, y] = pure7 & ~union
        mu[x, y] = (1-deletion)/(A*B)
        virtual_mass += virtual/(A*B)
        deleted_mass += deletion/(A*B)
    parameter = parent.parameter(height)
    dat = source.data(parameter)
    d, n, eta, s, _ = dat
    h, h1, D = sum(eta), sum(eta[2:]), max(d)
    lam = 1-F(1, 7**height)
    pi = tuple(lam if c == (1, 1) else 1-lam if c == (-1, -1) else F(0) for c in CARRIERS)
    t = tuple(lam*(int(ROOT[l] == 1)+int(l == 1)) for l in range(5))
    old_rest = D/18+(h+h1+max(eta))/4+F(1, 72)
    S0 = s-(sum(t[l]*n[l] for l in range(5))+old_rest)/5
    defects = {'E5': h/25-Vfamily['E5'], 'E15': h1/25-Vfamily['E15'],
               'E3': D/90-Vfamily['E3'], 'E5d': h/100-Vfamily['E5d'],
               'E15d': h1/100-Vfamily['E15d'], 'omega': virtual_mass-deleted_mass,
               'rho': sum(mu.values())-S0}
    result = complete_tails(dat, pi, defects, parameter[4])
    checks, digest = 0, sha256()
    for name, aa, bb in (('pure3', 3, 0), ('pure3', 4, 0), ('pure5', 0, 2),
                         ('pure5', 0, 3), ('root5', 1, 2), ('root5', 1, 3),
                         ('cell5', 2, 2), ('cell5', 2, 3)):
        row = result['family_parameters'][name]
        upper = label_cap(row['branches'], row['raw'], row['prime'], aa if bb == 0 else bb)
        coarse_a, coarse_b = min(aa, height), min(bb, height)
        masses = {}
        for (x, y), value in mu.items():
            key = (x % 3**coarse_a, y % 5**coarse_b)
            masses[key] = masses.get(key, F(0))+value
        lift = F(1, 3**(aa-coarse_a)*5**(bb-coarse_b))
        for residue, value in masses.items():
            require(value*lift <= upper, 'Every actual finite original cylinder obeys its assigned survivor cap')
            digest.update(json.dumps(encode([name, aa, bb, residue, value*lift, upper]), separators=(',', ':')).encode())
            checks += 1
    def observed_old(a, b, pattern):
        ra, rb = (pattern+a*a+2*b) % 3**a, (pattern*(b+1)+a+2*b*b) % 5**b
        ca, cb = min(a, height), min(b, height)
        value = sum(v for (x, y), v in mu.items() if x % 3**ca == ra % 3**ca and y % 5**cb == rb % 5**cb)
        return value/F(3**max(a-height, 0)*5**max(b-height, 0))
    tail_checks = []
    for k, pattern in product(range(5), range(3)):
        finite = sum(observed_old(a, b, pattern) for a, b in product(range(5), repeat=2)
                     if (a, b) not in HEAD and (a, b) not in SELECTED[:k])
        require(finite <= result['old_remainders'][k], 'Independent finite original omitted loads fit the complete tail')
        tail_checks.append({'prefix': k, 'pattern': pattern, 'finite_load': finite, 'complete_upper': result['old_remainders'][k]})
    positive = F(0)
    for a, b, e in product(range(4), range(4), range(1, 4)):
        if a+b == 0 or (a, b, e) in ((1, 0, 1), (0, 1, 1)):
            continue
        ra, rb, re = (a*a+b+e) % 3**a, (a+2*b*b+e) % 5**b, (2*a+b+e*e) % 7**e
        seven = sum(1 << v for v in range(re, P, 7**e))
        positive += sum(F((mask & seven).bit_count(), A*B*seven_mass) for (x, y), mask in survival.items()
                        if x % 3**a == ra and y % 5**b == rb)
    require(positive <= result['positive7'], 'Actual independent positive-seven complement fits its complete assigned raw cap series')
    return {'mode': mode, 'defects': defects, 'tail_interface': result, 'cylinder_checks': checks,
            'cylinder_digest': digest.hexdigest(), 'finite_tail_checks': tail_checks,
            'finite_positive7_complement': positive}


def calculate(base):
    require(sha256((base/'certificate_io.py').read_bytes()).hexdigest() == PINS['certificate_io.py'], 'Pinned IO')
    io = module('off_tail_io', base/'certificate_io.py')
    for path, pin in PINS.items():
        require(sha256(io.read_artifact_bytes(base/path)).hexdigest() == pin, 'Pinned input '+path)
    parent = module('off_tail_parent', base/'frontier/source-budgets/source_cost_endpoint_attainment.py')
    source = parent.load(base, 'verify_joint_frontier.py', 'off_tail_source')
    constructor = parent.load(base, 'frontier/source-budgets/sharp_source_mass_endpoints.py', 'off_tail_constructor')
    zero = {name: F(0) for name in ('E5', 'E15', 'E3', 'E5d', 'E15d', 'omega', 'rho')}
    faces = []
    for orientation, beta in product(range(2), ((F(1, 4), F(0), F(0)), (F(0), F(1, 4), F(0)),
                                              (F(0), F(0), F(1, 4)), (F(1, 12),)*3)):
        deficit = tuple(F(1, 2) if l == orientation else F(0) for l in range(5))
        late = tuple(F(1, 72) if l == orientation else F(0) for l in range(5))
        parameter = (deficit, (F(0), F(1, 4)), (F(0), F(0))+beta, late, F(3, 4))
        pi = tuple(F(int(c == (1, 1-orientation))) for c in CARRIERS)
        result = complete_tails(source.data(parameter), pi, zero, F(3, 4))
        expected_selected = (F(2, 125), F(7, 270), F(4, 375), F(7, 810))
        require(result['selected_caps'] == expected_selected and result['positive7'] == F(779, 12600)
                and all(result['old_remainders'][k] == F(163, 1800)-sum(expected_selected[:k]) for k in range(5)),
                'Exact98/109 selected, omitted and positive-seven constants on both complete beta faces')
        faces.append({'orientation': orientation, 'beta': beta, 'old_remainders': result['old_remainders'],
                      'positive7': result['positive7'], 'endpoint_difference': F(0)})
    cases = [finite_case(parent, constructor, source, mode) for mode in ('aligned', 'root-spill', 'wrong-roots')]
    return encode({'schema': 'erdos7-complete-off-face-omitted-tails-v1', 'source_sha256': {**PINS, **parent.PINS},
                   'whole_face_checks': faces, 'actual_finite_cases': cases,
                   'cylinder_checks': sum(c['cylinder_checks'] for c in cases),
                   'scope': 'Ordinary computable complete omitted-tail interface for116/124, recovering all98/109 R_k and Zplus exactly. Actual source, independent original residues, whole exponent tails and one common defect vector. No new global K or Lean claim.'})


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base', type=Path, default=Path(__file__).resolve().parents[2])
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument('--write', action='store_true')
    mode.add_argument('--check', action='store_true')
    args = parser.parse_args()
    result = calculate(args.base)
    io = module('off_tail_writer', args.base/'certificate_io.py')
    if args.check:
        require(json.loads(io.read_artifact_bytes(args.base/CERTIFICATE)) == result, 'Exact semantic complete off-face tail certificate')
    elif args.write:
        io.write_certificate_text(args.base/CERTIFICATE, json.dumps(result, indent=2)+'\n')
    else:
        print(json.dumps(result, indent=2))
    print('PASS: complete off-face omitted tails, every98/109 endpoint constant and actual independent original-cylinder checks.')


if __name__ == '__main__':
    try:
        main()
    except (ValueError, ArithmeticError, OSError, KeyError, TypeError, json.JSONDecodeError) as error:
        print('FAIL: '+str(error), file=sys.stderr)
        sys.exit(1)
