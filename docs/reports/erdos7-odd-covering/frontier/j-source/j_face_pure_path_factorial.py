#!/usr/bin/env python3
"""Whole saturated-J factorial tails retain their original prime-path cells."""
import argparse
from collections import Counter
from fractions import Fraction as F
from hashlib import sha256
import importlib.util
from itertools import product
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
CERTIFICATE = 'certificates/source_norms/j-source/j_face_pure_path_factorial.json'
PINS = {'certificate_io.py': '287582353eeb0674f4e80530ebf268228b023f6088d14c819488a56111d0b232', 'frontier/j-source/j_face_shared_square_factorial.py': 'a1c0eadad11cc55fb6faea96942465a89ade2bff95394f01ed47e83bc0bfd99d', 'certificates/source_norms/j-source/j_face_shared_square_factorial.json': '3dc47204d75eb3ed31658205918d7101adcab7138be1c77b075726d7b6155751', 'profile-notes/j-source/130-the-whole-j-face-forces-source-anti-alignment.md': '8691917a65ffd00f27dd3e81deb07717cc7b012be5fb1cc5a8337f9da0a66990', 'profile-notes/168-the-first-five-support-lowers-the-complete-factorial-bound.md': '8c1a8d1030188dc7c08058ec8165db7bb2fe2f043c1dd072bf76477356fa8683', 'profile-notes/174-the-pure-three-factorial-tail-retains-its-original-head.md': 'b9a5fb0081cf162bc123aade7cb18483323f8ef28b4ef1f07421aa3c63ad6ab3'}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    require(spec is not None and spec.loader is not None, 'Loadable mathematical provider')
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


C3 = tuple(map(F, ('11/20', '2/5', '1/5', '2/5', '2/5')))
C5 = tuple(map(F, ('0', '1/10', '29/90', '13/30', '4/15')))
PAIR3, PAIR5 = F(11, 720), F(13, 2400)


class JPathFactorialHead:
    def __init__(self, j, moment):
        self.j, self.moment = j, moment

    def components(self, layout):
        p, j = self.moment, self.j
        r, c, s, rr, t, cc, u = layout
        B = tuple(1+int(j.ROOT[a] == r)+int(a == c)+int(b == s)
                  +int(j.ROOT[a] == rr and b == t)+int(a == cc and b == u)
                  for a, b in product(range(5), repeat=2))
        h = tuple(max(v-4, 0) for v in B)
        phi = tuple(F(max(v-5, 0)*(v-4), 2) for v in B)
        wh = tuple(a*b for a, b in zip(p.w, h))
        wphi = tuple(a*b for a, b in zip(p.w, phi))
        A3 = tuple(sum(p.pre[5*a+k]*wh[5*a+k] for k in range(5)) for a in range(5))
        Q3 = max(a/18+cap/36 for a, cap in zip(A3, C3))
        delta3 = Q3-max(A3)/18-PAIR3
        A5 = tuple(sum(p.descendant[5*a+k]*wh[5*a+k] for a in range(5)) for k in range(5))
        Qrow = max(a/20+cap/80 for a, cap in zip(A5, C5))
        K = tuple(v-1-int(k == s) for v, (a, k) in zip(B, product(range(5), repeat=2)))
        G, H = tuple(int(v == 4) for v in K), tuple(int(v >= 3) for v in K)
        require(all(h[i] == G[i]+int(i % 5 == s)*H[i] for i in range(25)),
                'The original first-five event retains the overlapping two-unit hinge')
        O5G = max(sum(p.descendant[5*a+k]*p.w[5*a+k]*G[5*a+k]
                      for a in range(5)) for k in range(5))/20
        e = min(C5[s], sum(p.descendant[5*a+s]*p.w[5*a+s]*H[5*a+s] for a in range(5)))
        Qcond = O5G+max(C5[s]/80+e/20, max(C5[k]/80 for k in range(5) if k != s))
        Q5 = min(Qrow, Qcond)
        delta5 = Q5-max(A5)/20-PAIR5
        require(delta3 <= 0 and delta5 <= 0 and min(Q3, Q5) >= 0,
                'Both replacements improve their own complete nonnegative pair blocks')
        masks = [tuple(F(a == cc and b == u) for a, b in product(range(5), repeat=2))]
        if r == j.ROOT[c] == rr and s == t:
            masks.append(tuple(F(a == c and b == s) for a, b in product(range(5), repeat=2)))
        require(all(h[i] <= sum(mask[i] for mask in masks) for i in range(25)),
                'The inherited positive-seven cross uses the same original head')
        corrections = sum(j.deletion_correction(phi))
        old_cross = p.old_tail(wh)
        endpoints = []
        for theta in (j.LO, j.HI):
            head = p.lp(wphi, theta)-corrections
            seven = sum(p.raw_row(mask, theta) for mask in masks)/5
            old = head+old_cross+seven
            endpoints.append({'theta': theta, 'factorial_head': head,
                              'complete_old_cross': old_cross, 'complete_positive7_cross': seven,
                              'old_combined_head': old, 'new_combined_head': old+delta3+delta5})
        return {'layout': layout, 'pure3_cross_coefficients': A3, 'pure3_joint_block': Q3,
                'pure3_change': delta3, 'pure5_cross_coefficients': A5,
                'pure5_row_block': Qrow, 'pure5_conditioned_block': Qcond,
                'pure5_joint_block': Q5, 'pure5_change': delta5,
                'endpoint_records': endpoints}


def calculate(base):
    require(PINS, 'Pinned proof inputs')
    io = module('j_path_io', base/'certificate_io.py')
    prior = json.loads(io.read_artifact_bytes(base/'certificates/source_norms/j-source/j_face_shared_square_factorial.json'))
    pins = dict(PINS)
    for path, pin in prior['source_sha256'].items():
        require(path not in pins or pins[path] == pin, 'Consistent241 source closure')
        pins[path] = pin
    for path, pin in pins.items():
        require(sha256(io.read_artifact_bytes(base/path)).hexdigest() == pin, 'Pinned input '+path)
    j = module('j_path_source', base/'frontier/j-source/j_face_coupled_seven_heads.py')
    moment = module('j_path_moment', base/'frontier/j-source/j_face_shared_square_factorial.py')
    factorial = module('j_path_tail', base/'frontier/complete_off_face_factorial_tail.py')
    tail = moment.complete_tail(factorial)
    require(encode(tail) == prior['complete_tail_partition'], 'Entire inherited LCM pair partition')
    require(tail['weighted_old_pure_before_halving']['pure3']/2 == PAIR3
            and tail['weighted_old_pure_before_halving']['pure5']/2 == PAIR5,
            'Exactly the two disjoint unordered pure-prime pair charges')
    require(C3 == (F(11,20), F(2,5), F(2,5)-F(1,5), F(2,5), F(2,5)),
            'J ternary projection with the first beta cell retained')
    require(C5 == (0, F(13,30)-F(1,3), F(13,30)-F(1,9), F(13,30),
                   F(13,30)-(F(1,2)+F(1,3))/5),
            'J five-slot projection with alpha, beta and distinct H deletions')
    require(max(C3) == F(11,20) and max(C5) == F(13,30),
            'The previous global density caps dominate every new cell cap')
    problem = JPathFactorialHead(j, moment.JMomentHead(j))
    best, oldbest = F(-1), F(-1)
    witnesses, histogram3, histogram5 = [], Counter(), Counter()
    digest, count = sha256(), 0
    for layout in j.layouts():
        parts = problem.components(layout)
        digest.update(json.dumps(encode(parts), separators=(',', ':')).encode())
        histogram3[str(parts['pure3_change'])] += 1
        histogram5[str(parts['pure5_change'])] += 1
        for row in parts['endpoint_records']:
            oldbest = max(oldbest, row['old_combined_head'])
            value = row['new_combined_head']
            if value > best:
                best, witnesses = value, []
            if value == best:
                witnesses.append({'layout': layout, 'parts': parts, 'endpoint': row})
        count += 1
        if count % 2500 == 0:
            print('Checked '+str(count)+' original J heads and both complete prime-path blocks', flush=True)
    pairs = tail['distinct_tail_pairs']
    require(count == 12500 and oldbest+pairs == F(prior['complete_factorial_upper']),
            'All original layouts and the unchanged old complete bound')
    require(best+pairs == F(6313,7200) and oldbest-best == F(1,180),
            'Exact complete J factorial bound and strict gain')
    return encode({'schema': 'erdos7-j-face-pure-path-factorial-v1', 'source_sha256': pins,
        'geometry': prior['geometry'], 'survivor_mass': prior['survivor_mass'],
        'complete_mean_upper': prior['complete_mean_upper'],
        'pure3_cell_density_caps': C3, 'pure5_slot_density_caps': C5,
        'replaced_pure3_pair_charge': PAIR3, 'replaced_pure5_pair_charge': PAIR5,
        'complete_tail_partition': tail, 'original_head_count': count,
        'endpoint_record_count': 2*count, 'all_head_components_sha256': digest.hexdigest(),
        'pure3_change_histogram': dict(sorted(histogram3.items())),
        'pure5_change_histogram': dict(sorted(histogram5.items())),
        'old_complete_factorial_upper': oldbest+pairs, 'complete_factorial_upper': best+pairs,
        'complete_improvement': oldbest-best, 'combined_head_maximum': best,
        'maximizing_witnesses': witnesses,
        'scope': 'Both whole actual saturated J faces, independent original labels, common late parameter and complete infinite exponent tails. Bellman bounds control changing prime-path cells, not only nested tests. The square and all52-cost consumer are separate. No source attainment, off-face, Lean or unrestricted Erdos7 resolution.'})


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base', type=Path, default=Path(__file__).resolve().parents[2])
    modes = parser.add_mutually_exclusive_group()
    modes.add_argument('--write', action='store_true')
    modes.add_argument('--check', action='store_true')
    args = parser.parse_args()
    result = calculate(args.base)
    io = module('j_path_writer', args.base/'certificate_io.py')
    if args.write:
        io.write_certificate_text(args.base/CERTIFICATE, json.dumps(result, indent=2)+'\n')
    else:
        require(result == json.loads(io.read_artifact_bytes(args.base/CERTIFICATE)),
                'Exact complete J pure-path factorial certificate')
    print('PASS:complete J factorial <= '+result['complete_factorial_upper']
          +'; gain='+result['complete_improvement']+'; all12500 original heads and complete tails.')


if __name__ == '__main__':
    main()
