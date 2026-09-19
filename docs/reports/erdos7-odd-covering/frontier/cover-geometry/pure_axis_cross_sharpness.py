#!/usr/bin/env python3
"""The existing161 actual original-label family saturates the pure3/pure5 cross."""
import argparse
from fractions import Fraction as F
from itertools import product
from pathlib import Path
from hashlib import sha256
import importlib.util
import json
import sys

sys.dont_write_bytecode = True
CERTIFICATE = 'certificates/source_norms/cover-geometry/pure_axis_cross_sharpness.json'
PINS = {'certificate_io.py': '3bab29ebc23defcae75e775fb182d2aa0d83d71ba1ae3b168ed8e9bc7a8c1fe2', 'frontier/source-budgets/source_mass_compatibility.py': 'f65f0be22b250ab94d7da847a45b49c39355c15499f9cde8f18f267ca3365645', 'frontier/cover-geometry/full_family_five_cap_sharpness.py': '496c56e41467437a4da82282c05eca5f27dad0ced4c8c012507078e063339bde', 'certificates/source_norms/cover-geometry/full_family_five_cap_sharpness.json': 'e02d99267f8e22953c4e52f3391a4e929f5814e30e371a2d991e02620b3e8fd5', 'frontier/endpoint-bounds/k_face_complete_ratio.py': 'e94a6532ff6951d464a224f1a56415aaea90251c520c7b06fc9afe4e6a82c5db', 'certificates/source_norms/endpoint-bounds/k_face_complete_ratio.json': 'ccb1debedef1dc49cbc6a31e01c712f156992dc238bd0576e4f51ee8dd6f6888', 'frontier/moments-survival/pure_three_joint_moments.py': 'dcd5dae8b9ff0ef9c79f7ad7a52183079226815d2bf229f3ebcae349b9d70351', 'certificates/source_norms/moments-survival/pure_three_joint_moments.json': 'ed70ad34510621ef839a4dc770c5fe0c7000f6995141d64f2e3e300bc4aa9e4b', 'frontier/moments-survival/pure_five_joint_moments.py': 'ce2e635e296e720d241fa413ab18efe8cbeb4c2f80ecdc21e25573ee728d1ea7', 'certificates/source_norms/moments-survival/pure_five_joint_moments.json': '672543e3f551cf12e8d4a1c87c72c2f274d2d8a1ea93f327b7ca96afb8b6bc54'}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    value = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(value)
    return value


def finite(source, repacked, N):
    A, B, C = 3**N, 5**N, 7**N
    full = (1 << B)-1
    masks = {}

    def mask(b, r):
        key = (b, r)
        if key not in masks:
            masks[key] = sum(1 << y for y in range(r, B, 5**b))
        return masks[key]

    raw = [full]*A
    labels = []
    for a, b in product(range(N+1), repeat=2):
        if a+b == 0:
            continue
        aa, ra, bb, rb = source.source_label(a, b, 398)
        for x in range(ra, A, 3**aa):
            raw[x] &= full ^ mask(bb, rb)
        labels.append(source.crt_label(aa, ra, bb, rb, 0, 0))
    groups = {j: [0]*A for j in range(1, 6)}
    old_cofactor_sum = F(0)
    for a, b in product(range(N+1), repeat=2):
        if a+b == 0:
            continue
        j, aa, ra, bb, rb = repacked.mixed_label(a, b)
        oldj, oa, ora, ob, orb = source.mixed_label(a, b)
        bm = mask(bb, rb)
        count = sum((raw[x] & bm).bit_count() for x in range(ra, A, 3**aa))
        original_count = sum((raw[x] & mask(ob, orb)).bit_count() for x in range(ora, A, 3**oa))
        require(count == original_count, 'Every161 original old cofactor mass stays unchanged')
        old_cofactor_sum += F(count, A*B)
        for x in range(ra, A, 3**aa):
            require(groups[j][x] & bm == 0, 'Actual old cylinders disjoint within seven class')
            groups[j][x] |= bm
        for e in range(1, N+1):
            labels.append(source.crt_label(aa, ra, bb, rb, e, j*7**(e-1)))
    seven = [0]*C
    for j, e in product(range(1, 7), range(1, N+1)):
        for z in range(j*7**(e-1), C, 7**e):
            require(seven[z] == 0, 'All seven rays are disjoint')
            seven[z] = j
        if j == 6:
            labels.append(source.crt_label(0, 0, 0, 0, e, 6*7**(e-1)))
    require(len(labels) == len({m for m, r in labels}) == (N+1)**3-1,
            'Exactly one actual residue for every original nonunit odd modulus')
    u = F(sum(v != 6 for v in seven), C)
    kap = F(sum(v == 1 for v in seven), C)/u
    require(u == (5+F(1, C))/6 and kap == (1-F(1, C))/(5+F(1, C)),
            'Same physical pure-seven normalization as161')
    t = sum((F(1, 3**a) for a in range(3, N+1)), F(0))
    beta = sum((F(1, 5**b) for b in range(2, N+1)), F(0))
    q = beta+F(1, 5)
    require(old_cofactor_sum == F(4, 9)+t+q/9-t*q, 'Same complete161 cap equality')
    S = F(sum(v.bit_count() for v in raw), A*B)-kap*old_cofactor_sum
    require(S == F(5, 9)-t-q-kap*(F(4, 9)+t+q/9-t*q), 'Same exact saturated source approach')

    def test3(a):
        return (1, 1) if a == 1 else (2, 4) if a == 2 else (a, 2*3**(a-1))

    def test5(b):
        return (1, 3) if b == 1 else (b, 4*5**(b-1))

    pairs = []
    total = F(0)
    for a, b in product(range(1, N+1), repeat=2):
        aa, ra = test3(a)
        bb, rb = test5(b)
        bm = mask(bb, rb)
        n_raw = sum((raw[x] & bm).bit_count() for x in range(ra, A, 3**aa))
        deleted = [sum((raw[x] & groups[j][x] & bm).bit_count() for x in range(ra, A, 3**aa))
                   for j in range(1, 6)]
        require(all(z == 0 for z in deleted[1:]), 'Only the old cofactor3 seven class can hit cross tests')
        value = F(n_raw, A*B)-kap*F(sum(deleted), A*B)
        if b == 1:
            expected = (1-kap)*F(2, 45) if a == 1 else (1-kap)*F(1, 45) if a == 2 else F(1, 5*3**a)
        else:
            expected = (1-kap)*F(1, 3*5**b) if a == 1 else (1-kap)*F(1, 9*5**b) if a == 2 else F(1, 3**a*5**b)
        require(value == expected, 'All independent original cross intersections have their exact finite value')
        total += value
        pairs.append((a, b, str(value)))
    exact = (1-kap)/15+t/5+(4*(1-kap)/9+t)*beta
    truncated_limit_weights = F(4, 75)+t/5+(F(16, 45)+t)*beta
    require(total == exact and total-truncated_limit_weights == (F(1, 5)-kap)*(F(1, 15)+4*beta/9),
            'Exact finite cross, including physical7 correction in the finite normalization')
    eps3, eps5 = F(1, 18)-t, F(1, 20)-beta
    seven_correction = (F(1, 5)-kap)*(F(1, 15)+4*beta/9)
    limit_gap = eps3/4+(F(16, 45)+t)*eps5-seven_correction
    require(F(17, 200)-total == limit_gap > 0 and eps3/4 == F(1, 8*3**N)
            and seven_correction <= F(8, 375*7**N) < eps3/4,
            'Exact full finite error and its positive direction')
    # These marginal moments use this same actual survivor and the same tests.
    root1 = (1-kap)*(F(1, 3)-7*q/9)-2*kap*q/3
    cell3 = (1-kap)*(1-2*q)/9-2*kap*q/9
    deep3 = t*(1-2*q-kap*q)
    mean3 = root1+cell3+deep3
    moment3 = 3*mean3+2*cell3
    h = F(5, 9)-t
    first5 = (h-F(1, 9)-kap*(F(1, 3)+t))/5
    deep5 = (h-kap*(F(4, 9)+t))*beta
    mean5, moment5 = first5+deep5, 3*(first5+deep5)
    count3 = [sum(x % 3**aa == ra for aa, ra in (test3(a) for a in range(1, N+1))) for x in range(A)]
    count5 = [sum(y % 5**bb == rb for bb, rb in (test5(b) for b in range(1, N+1))) for y in range(B)]
    require(max(count3) == 2 and max(count5) == 1, 'Nested shallow three pair and disjoint deep/five tests')
    def integrate_product(f3, f5):
        raw_value = sum(f3[x]*f5[y] for x in range(A) for y in range(B) if (raw[x] >> y) & 1)
        removed = sum(f3[x]*f5[y] for j in groups for x in range(A) for y in range(B)
                      if ((raw[x] & groups[j][x]) >> y) & 1)
        return F(raw_value, A*B)-kap*F(removed, A*B)
    require(integrate_product(count3, [1]*B) == mean3
            and integrate_product([z*z+2*z for z in count3], [1]*B) == moment3,
            'Same-family first and quadratic pure-three moments')
    require(integrate_product([1]*A, count5) == mean5
            and integrate_product([1]*A, [z*z+2*z for z in count5]) == moment5,
            'Same-family first and quadratic pure-five moments')
    if N == 3:
        period = A*B*C
        alive = bytearray(b'\1')*period
        for modulus, residue in labels:
            alive[residue::modulus] = b'\0'*len(alive[residue::modulus])
        z3 = [sum(x % 3**aa == ra for aa, ra in (test3(a) for a in range(1, N+1))) for x in range(A)]
        z5 = [sum(y % 5**bb == rb for bb, rb in (test5(b) for b in range(1, N+1))) for y in range(B)]
        literal = F(sum(z3[n % A]*z5[n % B] for n, v in enumerate(alive) if v), period)/u
        require(literal == total, 'Independent literal full CRT cross moment')
        require(F(sum(alive), period)/u == S, 'Independent literal full CRT complete survivor mass')
    return {'N': N, 'labels': len(labels), 'S': str(S), 'cross': str(total),
            'truncated_limit_weights': str(truncated_limit_weights),
            'seven_correction': str(total-truncated_limit_weights), 'pairs': pairs,
            'three_tail_error': str(eps3), 'five_tail_error': str(eps5),
            'exact_gap_below_complete_limit': str(limit_gap),
            'pure_three_mean': str(mean3), 'pure_three_moment_lambda2': str(moment3),
            'pure_five_mean': str(mean5), 'pure_five_moment_lambda2': str(moment5),
            'label_sha256': sha256(json.dumps(sorted(labels)).encode()).hexdigest(),
            'literal_CRT_period': A*B*C if N == 3 else None}


def encode(value):
    if isinstance(value, F):
        return str(value)
    if isinstance(value, dict):
        return {str(k): encode(v) for k, v in value.items()}
    if isinstance(value, (tuple, list)):
        return [encode(v) for v in value]
    return value


def calculate(base):
    require(sha256((base/'certificate_io.py').read_bytes()).hexdigest() == PINS['certificate_io.py'], 'Pinned IO')
    io = module('axis_cross_io', base/'certificate_io.py')
    read = lambda name: json.loads(io.read_artifact_bytes(io.named_artifact(base/'certificates/source_norms', name+'.json')))
    predecessor = read('full_family_five_cap_sharpness')
    square_record = read('k_face_complete_ratio')
    three_record, five_record = read('pure_three_joint_moments'), read('pure_five_joint_moments')
    pins = dict(PINS)
    for record in (predecessor, square_record, three_record, five_record):
        for path, pin in record['source_sha256'].items():
            require(path not in pins or pins[path] == pin, 'Consistent existing input '+path)
            pins[path] = pin
    for path, pin in pins.items():
        require(sha256(io.read_artifact_bytes(base/path)).hexdigest() == pin, 'Pinned source '+path)
    source = module('axis_cross_source', base/'frontier/source-budgets/source_mass_compatibility.py')
    repacked = module('axis_cross_repack', base/'frontier/cover-geometry/full_family_five_cap_sharpness.py')
    square = module('axis_cross_square', base/'frontier/endpoint-bounds/k_face_complete_ratio.py')
    three = module('axis_cross_three', base/'frontier/moments-survival/pure_three_joint_moments.py')
    five = module('axis_cross_five', base/'frontier/moments-survival/pure_five_joint_moments.py')
    require(all(pins.get(p) == h for p, h in repacked.PINS.items()), 'Every constructor input is pinned')
    one_three_tail, one_five_tail = F(1, 18), F(1, 20)
    pieces = [square.cylinder_cap(1, 1, True), square.cylinder_cap(2, 1, True),
              one_three_tail/5, 25*square.cylinder_cap(1, 2, True)*one_five_tail,
              25*square.cylinder_cap(2, 2, True)*one_five_tail,
              one_three_tail*one_five_tail]
    require(pieces == [F(8, 225), F(4, 225), F(1, 90), F(1, 75), F(1, 225), F(1, 360)]
            and sum(pieces) == F(17, 200), 'All six complete arbitrary-cylinder cross pieces')
    mixed = (9*pieces[0]+15*pieces[1]
             +(3*F(4, 15)+5*F(4, 45))*square.weighted_tail(5, 2)
             +square.weighted_tail(3, 3)*square.weighted_tail(5, 1))
    require(mixed == F(593, 450) and mixed-2*sum(pieces) == F(1033, 900),
            'Only the two pure-axis ordered pairs are isolated in each mixed LCM bin')
    lcm_checks = []
    for a, b in product(range(1, 5), repeat=2):
        labels = tuple(product(range(a+1), range(b+1)))
        all_pairs = [(u, v) for u, v in product(labels, repeat=2)
                     if (max(u[0], v[0]), max(u[1], v[1])) == (a, b)]
        pure = [(u, v) for u, v in all_pairs
                if (u == (a, 0) and v == (0, b)) or (v == (a, 0) and u == (0, b))]
        require(len(all_pairs) == (2*a+1)*(2*b+1) and len(pure) == 2,
                'Independent ordered original-label LCM count')
        lcm_checks.append({'a': a, 'b': b, 'ordered_pairs': len(all_pairs), 'pure_axis_pairs': 2})
    checks = [finite(source, repacked, N) for N in (3, 4, 5)]
    for row, old in zip(checks, predecessor['checks']):
        require(row['N'] == old['height'] and row['labels'] == old['labels']
                and row['label_sha256'] == old['original_label_sha256']
                and row['S'] == old['survivor_mass'], 'Exactly the existing161 family, not a relaxed replacement')
    t, beta, kap = F(1, 18), F(1, 20), F(1, 5)
    limit = (1-kap)/15+t/5+(4*(1-kap)/9+t)*beta
    require(limit == sum(pieces), 'The actual common-family complete limit attains the upper bound')
    marginal = {'pure_three_mean': F(49, 360), 'pure_three_moment_lambda2': F(19, 40),
                'pure_five_mean': F(37, 450), 'pure_five_moment_lambda2': F(37, 150)}
    require(marginal['pure_three_moment_lambda2'] == 3*marginal['pure_three_mean']+2*F(1, 30)
            and marginal['pure_five_moment_lambda2'] == 3*marginal['pure_five_mean']
            and marginal['pure_three_moment_lambda2'] < three.envelope(F(2)) == F(34, 45)
            and marginal['pure_five_moment_lambda2'] < five.envelope(F(2)) == F(49, 180),
            'Cross equality does not simultaneously saturate either improved marginal moment bound')
    return encode({'schema': 'erdos7-pure-axis-cross-sharpness-v1', 'source_sha256': pins,
                   'complete_upper_pieces': pieces, 'cross_upper': sum(pieces),
                   'ordered_cross_upper': 2*sum(pieces), 'old_mixed_lcm_block': mixed,
                   'remaining_mixed_label_block': mixed-2*sum(pieces),
                   'lcm_pair_checks': lcm_checks, 'actual_finite_checks': checks,
                   'actual_cross_limit': limit, 'actual_ordered_cross_limit': 2*limit,
                   'actual_marginal_limits': marginal,
                   'improved_marginal_bounds_lambda2': (three.envelope(F(2)), five.envelope(F(2))),
                   'scope': 'Ordinary sharp bound for the isolated complete pure3/pure5 cross on the saturated K faces, attained in the actual finite-family limit of the unchanged161 original labels and their common normalized seven measure. Every source and mixed7 label remains. Does not establish sharpness of the total square, simultaneous marginal extrema, any52-cost or global comparison, a cover, or Lean verification.'})


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base', type=Path, default=Path(__file__).resolve().parents[2])
    modes = parser.add_mutually_exclusive_group()
    modes.add_argument('--write', action='store_true')
    modes.add_argument('--check', action='store_true')
    args = parser.parse_args()
    result = calculate(args.base)
    io = module('axis_cross_writer', args.base/'certificate_io.py')
    if args.write:
        io.write_certificate_text(args.base/CERTIFICATE, json.dumps(result, indent=2)+'\n')
    elif args.check:
        require(json.loads(io.read_artifact_bytes(args.base/CERTIFICATE)) == result, 'Exact actual pure-axis cross certificate')
    print('PASS: unchanged161 actual families attain pure-axis cross17/200; the total square remains a separate problem.')


if __name__ == '__main__':
    try:
        main()
    except (ValueError, ArithmeticError, OSError, KeyError, TypeError, json.JSONDecodeError) as error:
        print('FAIL: '+str(error), file=sys.stderr)
        sys.exit(1)
