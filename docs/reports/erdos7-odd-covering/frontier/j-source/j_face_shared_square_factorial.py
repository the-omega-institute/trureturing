#!/usr/bin/env python3
"""Shared saturated-J square/factorial heads and complete LCM tail moments."""
import argparse
from fractions import Fraction as F
from functools import lru_cache
from hashlib import sha256
import importlib.util
from itertools import product
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
CERTIFICATE = 'certificates/source_norms/j-source/j_face_shared_square_factorial.json'
PINS = {'certificate_io.py': '287582353eeb0674f4e80530ebf268228b023f6088d14c819488a56111d0b232', 'frontier/j-source/j_face_coupled_seven_heads.py': '740d2656fc47a056c4f8ea2ca13e024784b96794ac364b21a91c89024cfc9587', 'certificates/source_norms/j-source/j_face_coupled_seven_heads.json': 'babf0e35f264666a21d97447cf603216e43644c6919b0b83949e968f259f0851', 'frontier/complete_off_face_factorial_tail.py': '8447e1cd50d6452a881413067858188344d22631c7b73b74734b3006a244d047', 'profile-notes/128-the-complete-factorial-tail-retains-its-head-off-the-face.md': '9c070de9ab953772260c316b96846a874c5799449d0fa4baf72d90d6b33df4e3', 'profile-notes/j-source/130-the-whole-j-face-forces-source-anti-alignment.md': '8691917a65ffd00f27dd3e81deb07717cc7b012be5fb1cc5a8337f9da0a66990', 'profile-notes/transport/199-one-six-label-head-controls-the-square-and-both-complete-crosses.md': '1ff5cca5dc8b15a13571b5f7ec91e4f1964c595bf7039a3abed9ba3f6fd6638d', 'profile-notes/j-source/219-one-late-source-split-controls-complete-saturated-j-heads.md': '1364b183a11ce2a331c6dfe54ae64f0cf9321461ff3b7981890db0fcc84a536d'}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    require(spec is not None and spec.loader is not None, 'Loadable original mathematical provider')
    value = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(value)
    return value


def encode(value):
    if isinstance(value, F):
        return str(value)
    if isinstance(value, dict):
        return {str(k): encode(v) for k, v in value.items()}
    if isinstance(value, (list, tuple)):
        return [encode(v) for v in value]
    return value


def complete_tail(factorial):
    g = factorial.geometric
    a0, aw = g(3, 3), g(3, 3, 2, 1)
    b1, bw1, b2, bw2 = g(5, 1), g(5, 1, 2, 1), g(5, 2), g(5, 2, 2, 1)
    surviving = tuple(map(F, ('11/20', '13/30', '1/3', '1/9')))
    raw = tuple(map(F, ('1/4', '1/8', '1/12', '3/4', '1/2', '1/3', '1/9')))
    s, N3, N9, D, h, h1, em = raw
    linear = s+N3+N9+D*a0+(h+h1+em)*b1+a0*b1
    square = s+3*N3+5*N9+D*aw+(h+3*h1+5*em)*bw1+aw*bw1
    pure = dict(zip(('pure3', 'pure5', 'root5', 'cell5'),
                    (surviving[0]*g(3, 3, 2, -6), surviving[1]*g(5, 2, 2, -4),
                     surviving[2]*g(5, 2, 6, -10), surviving[3]*g(5, 2, 10, -16))))
    mixed = g(3, 3, 6, -16)/5+aw*bw2-13*a0*b2
    old_old = (sum(pure.values())+mixed)/2
    old_raw = D*g(3, 3, 2, -2)+(h+3*h1+5*em)*g(5, 2, 2, -1)
    old_raw += F(3, 5)*g(3, 3, 2, -2)+aw*bw2-6*a0*b2
    old_seven = old_raw/5
    seven_seven = (F(4, 15)*square-linear/5)/2
    pairs = old_old+old_seven+seven_seven
    old_diagonal = surviving[0]*a0+sum(surviving[1:])*b2+a0*b1
    seven_diagonal = linear/5
    ordered = 2*pairs+old_diagonal+seven_diagonal
    require(min(tuple(pure.values())+(mixed, old_old, old_raw, seven_seven)) >= 0,
            'Complete nonnegative cap subseries, including distinct positive7 pairs')
    require((linear, square, pairs, old_diagonal, ordered)
            == (F(3, 4), F(57, 16), F(5089, 7200), F(53, 600), F(5947, 3600)),
            'All complete J LCM tails and restored diagonals')
    # Independently count every pair at its LCM in a finite prefix.
    # The general finite-difference formulas in128 supply all-height coverage.
    labels = list(product(range(8), repeat=2))
    omitted = [q for q in labels if q not in factorial.HEAD]
    oo = {q: 0 for q in labels}
    oa = dict(oo)
    for a, b in omitted:
        for c, d in labels:
            target = (max(a, c), max(b, d))
            oa[target] += 1
            oo[target] += int((c, d) not in factorial.HEAD)
    for q in labels:
        require((oo[q], oa[q]) == factorial.pair_multiplicities(*q),
                'Independent original-label LCM count agrees with the complete polynomial partition')
    return {'surviving_pure_coefficients': surviving, 'raw_cofactor_coefficients': raw,
            'raw_old_linear_cap': linear, 'raw_old_square_cap': square,
            'weighted_old_pure_before_halving': pure, 'weighted_old_mixed_before_halving': mixed,
            'old_old_distinct': old_old, 'old_positive7': old_seven,
            'positive7_positive7_distinct': seven_seven, 'distinct_tail_pairs': pairs,
            'old_diagonal': old_diagonal, 'positive7_diagonal': seven_diagonal,
            'complete_ordered_tail_square': ordered, 'independent_lcm_prefix_counts': len(labels)}


class JMomentHead:
    def __init__(self, provider):
        self.provider = provider
        pre, raw, descendant, density = provider.source_tables(provider.LO)
        self.pre, self.descendant, self.w = (tuple(v for row in table for v in row)
                                            for table in (pre, descendant, density))
        require(min(self.w) == F(2, 5) and len(self.pre) == len(self.descendant) == 25,
                'Actual J normalized pre-table, absolute descendants and retained density')
        self.masks = ([tuple(F(1) for _ in range(25))],
                      [tuple(F(provider.ROOT[c] == r) for c, s in product(range(5), repeat=2)) for r in range(2)],
                      [tuple(F(c == k) for c, s in product(range(5), repeat=2)) for k in range(5)],
                      [tuple(F(s == k) for c, s in product(range(5), repeat=2)) for k in range(5)],
                      [tuple(F(provider.ROOT[c] == r and s == t) for c, s in product(range(5), repeat=2))
                       for r, t in product(range(2), range(5))],
                      [tuple(F(c == k and s == t) for c, s in product(range(5), repeat=2))
                       for k, t in product(range(5), repeat=2)])
        require([len(g) for g in self.masks] == [1, 2, 5, 5, 10, 25], 'All six raw-head mask families')

    @lru_cache(None)
    def old_tail(self, z):
        p, d, root = self.pre, self.descendant, self.provider.ROOT
        coefficients = (max(sum(p[5*c+s]*z[5*c+s] for s in range(5)) for c in range(5)),
                        max(sum(d[5*c+s]*z[5*c+s] for c in range(5)) for s in range(5)),
                        max(sum(d[5*c+s]*z[5*c+s] for c in range(5) if root[c] == r)
                            for r, s in product(range(2), range(5))),
                        max(a*b for a, b in zip(d, z)), max(z))
        return sum(c*w for c, w in zip(coefficients, (F(1, 18), F(1, 20), F(1, 20), F(1, 20), F(1, 72))))

    @lru_cache(None)
    def lp(self, z, theta):
        #219 accepts integer inputs but divides its minimum by120.
        #Fraction coefficients preserve exactness even for a constant integer head.
        value = self.provider.raw_source_lp(tuple(map(F, z)), theta)
        require(isinstance(value, F) and value >= 0, 'Exact nonnegative J source LP')
        return value

    @lru_cache(None)
    def raw_row(self, z, theta):
        return sum(max(self.lp(tuple(a*b for a, b in zip(z, mask)), theta) for mask in family)
                   for family in self.masks)+self.old_tail(z)

    def components(self, layout, theta):
        j = self.provider
        r, c, s, rr, t, cc, u = layout
        B = tuple(1+int(j.ROOT[a] == r)+int(a == c)+int(b == s)
                  +int(j.ROOT[a] == rr and b == t)+int(a == cc and b == u)
                  for a, b in product(range(5), repeat=2))
        require(min(B) >= 1 and max(B) <= 6, 'One independent original six-label head')
        square = tuple(x*x for x in B)
        head_before = self.lp(tuple(a*b for a, b in zip(self.w, square)), theta)
        corrections = j.deletion_correction(square)
        old_cross = self.old_tail(tuple(a*b for a, b in zip(self.w, B)))
        raw = self.raw_row(B, theta)
        h = tuple(max(x-4, 0) for x in B)
        phi = tuple(F(max(x-5, 0)*(x-4), 2) for x in B)
        phi_before = self.lp(tuple(a*b for a, b in zip(self.w, phi)), theta)
        phi_corrections = j.deletion_correction(phi)
        phi_old = self.old_tail(tuple(a*b for a, b in zip(self.w, h)))
        compatible = r == j.ROOT[c] == rr and s == t
        masks = [tuple(F(a == cc and b == u) for a, b in product(range(5), repeat=2))]
        if compatible:
            masks.append(tuple(F(a == c and b == s) for a, b in product(range(5), repeat=2)))
        require(all(h[i] <= sum(mask[i] for mask in masks) for i in range(25)),
                'The same factorial cross is bounded by45 plus its compatible original intersection')
        phi_seven = sum(self.raw_row(mask, theta) for mask in masks)/5
        head = head_before-sum(corrections)
        phi_head = phi_before-sum(phi_corrections)
        require(min(head, old_cross, raw, phi_head, phi_old, phi_seven) >= 0,
                'Nonnegative complete corrected head/cross bounds')
        return {'square_head_before_corrections': head_before, 'square_deletion_corrections': corrections,
                'square_head': head, 'square_old_cross': old_cross, 'square_positive7_raw_row': raw,
                'combined_square_head': head+2*old_cross+F(2, 5)*raw,
                'factorial_head_before_corrections': phi_before, 'factorial_deletion_corrections': phi_corrections,
                'factorial_head': phi_head, 'factorial_old_cross': phi_old,
                'factorial_positive7_cross': phi_seven,
                'combined_factorial_head': phi_head+phi_old+phi_seven}


def calculate(base):
    require(PINS, 'Final proof input pins')
    io = module('j_moment_io', base/'certificate_io.py')
    prior = json.loads(io.read_artifact_bytes(base/'certificates/source_norms/j-source/j_face_coupled_seven_heads.json'))
    pins = dict(PINS)
    for path, pin in prior['source_sha256'].items():
        require(path not in pins or pins[path] == pin, 'Consistent219 source closure')
        pins[path] = pin
    for path, pin in pins.items():
        require(sha256(io.read_artifact_bytes(base/path)).hexdigest() == pin, 'Pinned mathematical input '+path)
    j = module('j_moment_source', base/'frontier/j-source/j_face_coupled_seven_heads.py')
    factorial = module('j_moment_tail', base/'frontier/complete_off_face_factorial_tail.py')
    geometry = prior['geometry']
    require(tuple(map(F, geometry['late_split_interval'])) == (j.LO, j.HI)
            and F(geometry['source_mass']) == F(1, 4) and F(geometry['survivor_mass']) == F(3, 20)
            and F(prior['complete_mean_upper']) == F(16, 25),
            'Both original saturated J faces and complete common-theta interval')
    problem, tail = JMomentHead(j), complete_tail(factorial)
    for theta in (j.LO, j.HI):
        normalized, _, descendant, density = j.source_tables(theta)
        require(encode(normalized) == geometry['normalized_deep_ternary_coefficients'], 'Bound normalized deep3 source table')
        require(encode(descendant) == geometry['absolute_descendant_five_coefficients']
                and encode(density) == geometry['retained_survivor_density']
                and problem.lp((1,)*25, theta) == F(1, 4), 'Bound J tables and exact raw source mass')
    best = {'square': F(-1), 'factorial': F(-1)}
    witnesses = {k: [] for k in best}
    digest, count, layouts = sha256(), 0, 0
    for layout in j.layouts():
        for theta in (j.LO, j.HI):
            parts = problem.components(layout, theta)
            row = {'layout': layout, 'theta': theta, 'components': parts}
            digest.update(json.dumps(encode(row), separators=(',', ':')).encode())
            for name in best:
                value = parts['combined_'+name+'_head']
                if value > best[name]:
                    best[name], witnesses[name] = value, [row]
                elif value == best[name]:
                    witnesses[name].append(row)
            count += 1
        layouts += 1
        if layouts % 2500 == 0:
            print('Checked '+str(layouts)+' original heads on both theta endpoints', flush=True)
    Q = best['square']+tail['complete_ordered_tail_square']
    T5 = best['factorial']+tail['distinct_tail_pairs']
    require(layouts == 12500 and count == 25000 and (Q, T5) == (F(371, 80), F(6353, 7200)),
            'Every original J layout/endpoint and exact complete moment maxima')
    require(all(isinstance(v, F) for v in (Q, T5, *best.values())), 'Exact moment outputs')
    return encode({'schema': 'erdos7-j-face-shared-square-factorial-v1', 'source_sha256': pins,
                   'geometry': geometry, 'survivor_mass': F(3, 20), 'complete_mean_upper': F(16, 25),
                   'complete_square_upper': Q, 'complete_factorial_upper': T5,
                   'original_head_count': layouts, 'endpoint_record_count': count,
                   'all_endpoint_components_sha256': digest.hexdigest(),
                   'combined_head_maxima': best, 'maximizing_witnesses': witnesses,
                   'complete_tail_partition': tail,
                   'scope': 'Both whole actual saturated J faces, all original independent labels and the single common theta interval. One six-label layout controls its square and both complete crosses before maximization; the same-head factorial inequality retains every distinct omitted pair. Convexity of each complete bound gives the endpoint reduction. No min-of-affines endpoint substitution, actual-attainment claim, off-face/global52-cost comparison, Lean or unrestricted Erdos7 resolution.'})


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base', type=Path, default=Path(__file__).resolve().parents[2])
    modes = parser.add_mutually_exclusive_group()
    modes.add_argument('--write', action='store_true')
    modes.add_argument('--check', action='store_true')
    args = parser.parse_args()
    result = calculate(args.base)
    io = module('j_moment_output', args.base/'certificate_io.py')
    if args.write:
        io.write_certificate_text(args.base/CERTIFICATE, json.dumps(result, indent=2)+'\n')
    else:
        require(result == json.loads(io.read_artifact_bytes(args.base/CERTIFICATE)), 'Exact complete J moment certificate')
    print('PASS: complete J square='+result['complete_square_upper']+'; factorial='+result['complete_factorial_upper']
          +'; all12500 original heads and complete infinite tails.')


if __name__ == '__main__':
    try:
        main()
    except (ValueError, ArithmeticError, OSError, KeyError, TypeError, json.JSONDecodeError) as error:
        print('FAIL: '+str(error), file=sys.stderr)
        raise SystemExit(1)
