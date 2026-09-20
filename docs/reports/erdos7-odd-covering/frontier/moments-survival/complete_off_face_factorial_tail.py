#!/usr/bin/env python3
"""Complete off-face factorial tail with one original six-label head.

Profile128 transports112's head and108's complete pair complement.
Only12500 head layouts per source are enumerated; no source LP is run.
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
ROOT = (0, 0, 1, 1, 1)
HEAD = frozenset(product(range(3), range(2)))
CERTIFICATE = 'certificates/source_norms/moments-survival/complete_off_face_factorial_tail.json'
PINS = {
    'certificate_io.py': '2318639f574d9f6fab4c7187c2736cde559e1925a5f9fa657afe0b8334f7d02b',
    'verify_joint_frontier.py': '0b5cd35851d36f3af83aee19e02267cb05abc8bf07611a12083fca6f3d9bd765',
    'frontier/retained-transport/finite_source_face_transport.py': '04c99f1a0c6e1781734531923705863fbc9843c610f6d4933a81c89429aa5291',
    'frontier/comparison-bounds/complete_off_face_cost.py': '0d53ac6dc99eac6db322525d94375c498e61cb1c5cacd8776327c70d311306c8',
    'frontier/cover-geometry/complete_off_face_omitted_tails.py': '33e8c164c64790483ba512c984e8090cf5c44b92bf6ca1cb08a17cb56a93201d',
    'frontier/moments-survival/whole_factorial_same_head.py': '845768cfb7c67a9683c92e4ecaacee40dfc22d6b7f6c8791b5169917650e5c24',
    'frontier/endpoint-bounds/k_face_common_seven_hinges.py': 'c382bed2ef52cc22c624c33f8aa2b1313df3a43935916f985c9c11060433c1e3',
}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    require(spec is not None and spec.loader is not None, 'Loadable input '+str(path))
    value = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(value)
    return value


def encode(value):
    if isinstance(value, F):
        return str(value)
    if isinstance(value, dict):
        return {str(k): encode(v) for k, v in value.items()}
    if isinstance(value, (tuple, list)):
        return [encode(v) for v in value]
    return value


def geometric(prime, start, slope=0, intercept=1):
    """Exact sum of (slope*n+intercept)*prime^-n, n>=start."""
    require(prime > 1 and start >= 0 and slope >= 0
            and slope*start+intercept >= 0, 'Nonnegative complete weighted geometric series')
    ratio = F(1, prime)
    return ratio**start*((slope*start+intercept)/(1-ratio)+slope*ratio/(1-ratio)**2)


def weighted_family(tails, row, slope, intercept):
    """The identical125 assigned cap, with a nonnegative linear count weight."""
    prime, start = row['prime'], row['start']
    crossing = tails.complete_series(row['branches'], row['raw'], prime, start)
    N = crossing['crossing']
    require(slope >= 0 and slope*start+intercept >= 0, 'Nonnegative LCM multiplicities')
    prefix = sum(((slope*n+intercept)*tails.label_cap(row['branches'], row['raw'], prime, n)
                  for n in range(start, N)), F(0))
    return prefix+crossing['tail_coefficient']*geometric(prime, N, slope, intercept)


def clipped_line(mass, coefficient, prime, start):
    """Complete sum min(mass,coefficient*prime^-n), with no omitted tail."""
    require(mass >= 0 and coefficient >= 0, 'Positive excess mass and cylinder coefficient')
    if mass == 0 or coefficient == 0:
        return F(0)
    N = start
    while coefficient/F(prime**N) > mass:
        N += 1
    return (N-start)*mass+coefficient*geometric(prime, N)


def clipped_product(mass, coefficient, first3=3, first5=1):
    """Complete double sum min(mass,coefficient*3^-a*5^-b)."""
    require(mass >= 0 and coefficient >= 0 and first3 >= 0 and first5 >= 0,
            'Positive double-tail data')
    if mass == 0 or coefficient == 0:
        return F(0)
    N = first3
    while coefficient/F(3**N*5**first5) > mass:
        N += 1
    rows = sum((clipped_line(mass, coefficient/F(3**a), 5, first5)
                for a in range(first3, N)), F(0))
    return rows+coefficient*geometric(3, N)*geometric(5, first5)


def pair_multiplicities(a, b):
    """Ordered O-by-O and O-by-all multiplicities at LCM exponents(a,b)."""
    if (a, b) in HEAD:
        return 0, 0
    if b <= 1:
        return (2*a-5)*(2*b+1), (2*a-2)*(2*b+1)
    if a <= 2:
        return (2*a+1)*(2*b-3), (2*a+1)*(2*b-1)
    return (2*a+1)*(2*b+1)-12, (2*a+1)*(2*b+1)-6


def complete_pairs(tails, tail_data, dat):
    """Known nonnegative cap-subseries only; no unknown moments subtracted."""
    d, n, eta, s, _ = dat
    D, h, h1, em = max(d), sum(eta), sum(eta[2:]), max(eta)
    N3, N9 = max(sum(n[:2]), sum(n[2:])), max(n)
    a0, aw = geometric(3, 3), geometric(3, 3, 2, 1)
    b1, bw1 = geometric(5, 1), geometric(5, 1, 2, 1)
    b2, bw2 = geometric(5, 2), geometric(5, 2, 2, 1)
    raw_linear = s+N3+N9+D*a0+(h+h1+em)*b1+a0*b1
    raw_square = s+3*N3+5*N9+D*aw+(h+3*h1+5*em)*bw1+aw*bw1
    families = tail_data['family_parameters']
    old_pure = {
        'pure3': weighted_family(tails, families['pure3'], 2, -6),
        'pure5': weighted_family(tails, families['pure5'], 2, -4),
        'root5': weighted_family(tails, families['root5'], 6, -10),
        'cell5': weighted_family(tails, families['cell5'], 10, -16),
    }
    old_mixed = geometric(3, 3, 6, -16)/5+aw*bw2-13*a0*b2
    old_old = (sum(old_pure.values())+old_mixed)/2
    old_raw = (D*geometric(3, 3, 2, -2)
               +(h+3*h1+5*em)*geometric(5, 2, 2, -1)
               +F(3, 5)*geometric(3, 3, 2, -2)+aw*bw2-6*a0*b2)
    old_positive7 = old_raw/5
    positive7_positive7 = (F(4, 15)*raw_square-raw_linear/5)/2
    require(min(tuple(old_pure.values())+(old_mixed, old_old, old_raw, positive7_positive7)) >= 0,
            'Complete nonnegative distinct-pair cap blocks')
    return {'old_old_distinct': old_old, 'old_positive7': old_positive7,
            'positive7_positive7_distinct': positive7_positive7,
            'tail_distinct_pairs': old_old+old_positive7+positive7_positive7,
            'weighted_old_pure_blocks_before_halving': old_pure,
            'weighted_old_mixed_before_halving': old_mixed,
            'raw_old_linear_cap': raw_linear, 'raw_old_square_cap': raw_square}


class FactorialHead:
    """One actual source, original head and shared capacity/union vector.

    Case is126's actual-source record; reference_cell optionally swaps
    the canonical root0 cells. Numeric domain checks do not prove that
    arbitrary parameter records are realizable by original families.
    """
    def __init__(self, finite, tails, case):
        self.case, self.point = case, case['point']
        self.w = finite.weights(self.point, case['q'])
        self.omega = case['defects']['omega']
        self.reference_cell = case.get('reference_cell', 1)
        sigma, z, D, E27 = case['sigma'], case['parameter'][4], max(case['dat'][0]), case['E27']
        require(0 <= sigma <= F(2, 27) and 0 <= E27 <= case['defects']['E3']
                and self.reference_cell in (0, 1), 'Actual concentrated27 domain and contained defect')
        require(len(case['qslots']) == 5 and sum(case['qslots']) == z
                and all(0 <= x <= F(1, 5) for x in case['qslots']), 'Actual common pure5 slot masses')
        require(tuple(self.point['d']) == tuple(case['dat'][0])
                and tuple(self.point['n']) == tuple(case['dat'][1])
                and tuple(self.point['eta']) == tuple(case['dat'][2]), 'One actual effective source')
        gap = F(1, 135)-sigma/72
        self.error27 = (z-D)/135+D*E27/(27*gap)
        require(self.error27 >= 0, 'Positive ideal27 defect upper')
        self.tail_data = tails.complete_tails(case['dat'], case['pi'], case['defects'], z)
        self.pairs = complete_pairs(tails, self.tail_data, case['dat'])
        self.head_caps, self.raw_rows = [], []
        for c, j in product(range(5), repeat=2):
            i = 5*c+j
            U, p, descendant = (self.point[k][i] for k in ('caps', 'pre', 'descendant'))
            credit = case['qslots'][j]/135 if c == self.reference_cell else F(0)
            error = min(self.error27, credit) if c == self.reference_cell else F(0)
            self.head_caps.append(min(U, max(F(0), self.w[i]*U-credit+error+self.omega)))
            self.raw_rows.append(6*U+p/9+3*descendant/20+F(int(descendant > 0), 360))
        self.old_cache = {}

    def load(self, layout):
        require(len(layout) == 7 and all(0 <= x < bound for x, bound in
                    zip(layout, (2, 5, 5, 2, 5, 5, 5))), 'Independent original head labels')
        r3, c9, s5, r15, s15, c45, s45 = layout
        return tuple(1+int(ROOT[c] == r3)+int(c == c9)+int(j == s5)
                     +int(ROOT[c] == r15 and j == s15)+int(c == c45 and j == s45)
                     for c, j in product(range(5), repeat=2))

    def old_coefficients(self, z):
        p, d = self.point['pre'], self.point['descendant']
        return (max(sum(p[5*c+j]*z[5*c+j] for j in range(5)) for c in range(5)),
                max(sum(d[5*c+j]*z[5*c+j] for c in range(5)) for j in range(5)),
                max(sum(d[5*c+j]*z[5*c+j] for c in range(5) if ROOT[c] == r)
                    for r, j in product(range(2), range(5))),
                max(x*y for x, y in zip(d, z)), max(z))

    def old_cross(self, h):
        if h not in self.old_cache:
            baseline = self.old_coefficients(tuple(w*x for w, x in zip(self.w, h)))
            excess = self.old_coefficients(tuple((1-w)*x for w, x in zip(self.w, h)))
            mass = max(h)*self.omega
            nominal = sum(v*q for v, q in zip(baseline, (F(1, 18), F(1, 20), F(1, 20), F(1, 20), F(1, 72))))
            error = (clipped_line(mass, excess[0], 3, 3)
                     +sum(clipped_line(mass, v, 5, 2) for v in excess[1:4])
                     +clipped_product(mass, excess[4]))
            self.old_cache[h] = (nominal, error)
        return self.old_cache[h]

    def components(self, layout, B=None):
        actual_B = self.load(layout)
        B = actual_B if B is None else tuple(B)
        require(B == actual_B, 'Same original six-head load, including any supplied cached values')
        r3, c9, s5, r15, s15, c45, s45 = layout
        compatible = r3 == ROOT[c9] == r15 and s5 == s15
        full = compatible and c45 == c9 and s45 == s5
        head = self.head_caps[5*c9+s5] if full else F(0)
        nominal, error = self.old_cross(tuple(max(v-4, 0) for v in B))
        seven = (self.raw_rows[5*c45+s45]+(self.raw_rows[5*c9+s5] if compatible else 0))/5
        return {'head': head, 'old_cross_baseline': nominal, 'old_cross_error': error,
                'positive7_cross': seven, 'head_total': head+nominal+error+seven}

    def factorial_upper(self, layout, B=None):
        return self.components(layout, B)['head_total']+self.pairs['tail_distinct_pairs']


def structural_checks(tails):
    bound = 8
    labels = tuple(product(range(bound+1), repeat=2))
    old = tuple(x for x in labels if x not in HEAD)
    oo, oa = {}, {}
    for x, y in product(old, labels):
        key = max(x[0], y[0]), max(x[1], y[1])
        oa[key] = oa.get(key, 0)+1
        if y not in HEAD:
            oo[key] = oo.get(key, 0)+1
    for a, b in labels:
        require(pair_multiplicities(a, b) == (oo.get((a, b), 0), oa.get((a, b), 0)),
                'Independent original-label LCM multiplicity enumeration')
    line_checks = 0
    for prime, start, mass, c, H in product((3, 5), (2, 3), (F(0), F(1, 10000), F(1, 10)),
                                          (F(1, 5), F(2, 3)), (F(0), F(1, 3))):
        row = {'prime': prime, 'start': start, 'raw': c+H,
               'branches': ((c, mass, H),)}
        for slope, intercept in ((0, 1), (2, -2*start), (6, 1)):
            N = max(start+3, tails.complete_series(row['branches'], row['raw'], prime, start)['crossing']+2)
            prefix = sum((slope*n+intercept)*tails.label_cap(row['branches'], row['raw'], prime, n)
                         for n in range(start, N))
            coefficient = c+(H if mass > 0 else 0)
            require(weighted_family(tails, row, slope, intercept)
                    == prefix+coefficient*geometric(prime, N, slope, intercept),
                    'Entire weighted cap family equals a later finite prefix plus its complete tail')
            line_checks += 1
    product_checks = 0
    for mass, coefficient, a0, b0 in product((F(0), F(1, 10**6), F(1, 100), F(1)),
                                            (F(0), F(1, 5), F(2)), (3, 4), (1, 2)):
        total = clipped_product(mass, coefficient, a0, b0)
        row = clipped_line(mass, coefficient/F(3**a0), 5, b0)
        column = clipped_line(mass, coefficient/F(5**b0), 3, a0)
        require(total == row+clipped_product(mass, coefficient, a0+1, b0)
                and total == column+clipped_product(mass, coefficient, a0, b0+1),
                'Two independent complete double-tail partitions agree')
        product_checks += 1
    phi = lambda v: F(max(v-5, 0)*(v-4), 2)
    multiplier = F(243, 91)
    require(all(max(v*v-81, 0) <= multiplier*phi(v) for v in range(1, 19))
            and multiplier*phi(18) == 18*18-81, 'Raw81 full-domain majorant is sharp at load18')
    require((243-182, -9*243, 20*243+81*182) == (61, -1089-18*61, 18*1089)
            and F(1089, 61) > 17 and F(1089, 61) < 18,
            'The remaining polynomial is(v-18)(61v-1089)/182, nonnegative on integer v>=10')
    return {'lcm_exponent_box': bound, 'ordered_old_all_pairs': len(old)*len(labels),
            'weighted_series_checks': line_checks, 'double_tail_partition_checks': product_checks,
            'raw81_factorial_majorant': multiplier, 'sharp_integer_load': 18}


def calculate(base):
    require(sha256((base/'certificate_io.py').read_bytes()).hexdigest() == PINS['certificate_io.py'], 'Pinned IO')
    io = module('off_factorial_io', base/'certificate_io.py')
    for path, pin in PINS.items():
        require(sha256(io.read_artifact_bytes(base/path)).hexdigest() == pin, 'Pinned input '+path)
    finite = module('off_factorial_finite', base/'frontier/retained-transport/finite_source_face_transport.py')
    tails = module('off_factorial_tails', base/'frontier/cover-geometry/complete_off_face_omitted_tails.py')
    source = module('off_factorial_source', base/'verify_joint_frontier.py')
    actual = module('off_factorial_actual', base/'frontier/comparison-bounds/complete_off_face_cost.py')
    old = module('off_factorial_face', base/'frontier/moments-survival/whole_factorial_same_head.py')
    bridge = module('off_factorial_bridge', base/'frontier/endpoint-bounds/k_face_common_seven_hinges.py')
    reference = old.FactorialHead(bridge)
    checks = structural_checks(tails)
    cases = [actual.face_case(finite, source)]+[actual.actual_398_case(finite, source, N) for N in (5, 8)]
    results = []
    for case in cases:
        problem = FactorialHead(finite, tails, case)
        best, witnesses, count, digest = F(-1), [], 0, sha256()
        for layout in product(range(2), range(5), range(5), range(2), range(5), range(5), range(5)):
            parts = problem.components(layout)
            if case['height'] is None:
                old_parts = tuple(F(v, old.HEAD_SCALE) for v in reference.component_numerators(layout))
                require((parts['head'], parts['old_cross_baseline'], parts['positive7_cross']) == old_parts
                        and parts['old_cross_error'] == 0, 'Every face head recovers112 component by component')
            count += 1
            digest.update(json.dumps(encode([layout, parts]), separators=(',', ':')).encode())
            value = parts['head_total']
            if value > best:
                best, witnesses = value, [{'layout': layout, 'components': parts}]
            elif value == best:
                witnesses.append({'layout': layout, 'components': parts})
        upper = best+problem.pairs['tail_distinct_pairs']
        if case['height'] is None:
            require(problem.pairs['tail_distinct_pairs'] == F(2539, 3600)
                    and best == F(139, 900) and upper == F(619, 720), 'Complete exact108/112 face recovery')
        require(count == 12500, 'All independent six-head layouts, without source LPs')
        results.append({'source_height': case['height'], 'sigma': case['sigma'],
                        'defects': case['defects'], 'E27': case['E27'],
                        'pair_partition': problem.pairs, 'head_maximum': best,
                        'factorial_tail_upper': upper, 'maximizing_witnesses': witnesses,
                        'layout_count': count, 'all_layout_components_sha256': digest.hexdigest(),
                        'distinct_old_cross_patterns': len(problem.old_cache)})
        print('Checked complete factorial tail at height '+str(case['height'])+': '+str(upper), flush=True)
    transports = []
    for orientation, first_beta, spread in product(range(2), range(2, 5), (False, True)):
        beta = [F(0)]*3
        beta[first_beta-2] = F(1, 5) if spread else F(1, 4)
        if spread:
            beta[(first_beta-1) % 3] = F(1, 25)
            beta[first_beta % 3] = F(1, 100)
        beta = tuple(beta)
        case = actual.face_case(finite, source)
        deficit = tuple(F(1, 2) if c == orientation else F(0) for c in range(5))
        late = tuple(F(1, 72) if c == orientation else F(0) for c in range(5))
        parameter = (deficit, (F(0), F(1, 4)), (F(0), F(0))+beta, late, F(3, 4))
        pi = tuple(F(int(pair == (1, 1-orientation))) for pair in finite.CARRIERS)
        case.update(parameter=parameter, pi=pi, dat=source.data(parameter), reference_cell=1-orientation,
                    point=finite.source_point(parameter, pi, F(0), first_beta, F(0)))
        problem = FactorialHead(finite, tails, case)
        require(problem.pairs['tail_distinct_pairs'] == F(2539, 3600), 'Whole-beta and both-orientation pair transport')
        swap = list((1, 0, 2, 3, 4) if orientation else range(5))
        swap[2], swap[first_beta] = swap[first_beta], swap[2]
        require(all(problem.head_caps[5*swap[c]+j] == reference.head_caps[c][j]
                    and problem.raw_rows[5*swap[c]+j] == reference.raw_rows[c][j]
                    and problem.w[5*swap[c]+j] == reference.w[c][j]
                    and problem.point['pre'][5*swap[c]+j] == reference.pre[c][j]
                    and problem.point['descendant'][5*swap[c]+j] == reference.descendant[c][j]
                    for c, j in product(range(5), repeat=2)), 'All head and descendant tables transport on each whole face')
        transports.append({'orientation': orientation, 'first_beta': first_beta,
                           'beta': beta, 'endpoint_difference': F(0)})
    return {'schema': 'erdos7-complete-off-face-factorial-tail-v1', 'source_sha256': PINS,
            'structural_checks': checks, 'complete_source_cases': results, 'face_transports': transports,
            'scope': 'General ordinary same-head complete factorial-tail interface using actual116/121/125 data, all original labels and infinite tails, and one shared capacity/union-error vector. Numeric maxima concern only the face and genuine398 heights5 and8. No source-LP enumeration, uniform all-source bound, new global K, Lean verification or Erdos7 resolution.'}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base', type=Path, default=Path(__file__).resolve().parents[2])
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument('--check', action='store_true')
    mode.add_argument('--output', type=Path)
    args = parser.parse_args()
    result = encode(calculate(args.base))
    io = module('off_factorial_writer', args.base/'certificate_io.py')
    if args.check:
        require(json.loads(io.read_artifact_bytes(args.base/CERTIFICATE)) == result, 'Exact complete off-face factorial certificate')
    if args.output is not None:
        io.write_certificate_text(args.output, json.dumps(result, indent=2)+'\n')
    print('PASS:37500 independent heads, full pair complements and clipped double tails; exact112 face recovery.')
    print('No new global comparison or uniform maximization over all actual sources.')


if __name__ == '__main__':
    main()
