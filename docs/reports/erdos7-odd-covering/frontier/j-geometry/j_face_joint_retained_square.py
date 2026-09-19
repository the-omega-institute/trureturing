#!/usr/bin/env python3
"""One exact joint-survivor dual sharpens the complete saturated-J square."""
import argparse
from fractions import Fraction as F
from hashlib import sha256
import importlib.util
from itertools import product
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
CERTIFICATE = 'certificates/source_norms/j-geometry/j_face_joint_retained_square.json'
PINS = {'certificate_io.py': '2318639f574d9f6fab4c7187c2736cde559e1925a5f9fa657afe0b8334f7d02b', 'frontier/j-geometry/j_face_shared_square_factorial.py': '19f35e9bcac13999e3912fd5d5a2d43ddcef667e5913d4b6d8ec4c171c911e44', 'certificates/source_norms/j-geometry/j_face_shared_square_factorial.json': '1db541160baeed8896d715a0250856ef98cfc7c0968d3ec2d18ea0efeb3dc2ce', 'frontier/j-geometry/j_face_coupled_seven_heads.py': '78b6846a4eaa01ed568eb96e8c49dca67d0a19df094bc1e28ba5214100dc70a0', 'profile-notes/129-192/130-the-whole-j-face-forces-source-anti-alignment.md': 'c9c11d0250836f7abc67eed901716f867b7a916a9797afcaa14b3f70584e33a8', 'profile-notes/193-256/219-one-late-source-split-controls-complete-saturated-j-heads.md': 'd0f78950c8ca3040b2a90c5b5d470655cd53e68f39b54d531f793915490ff73d', 'profile-notes/193-256/241-one-original-j-head-controls-complete-square-and-factorial-moments.md': 'a6900d40ccc370e3565d4784c653c213667f736088082cf1ac622153fe807d06'}
CONTROLLER = (1, 4, 2, 1, 2, 4, 2)
INEQUALITY_DUAL = {2: '12/5', 7: '9/5', 12: '12', 17: '12', 20: '5', 21: '5',
                  22: '32', 23: '5', 24: '9/5', 25: '2/27', 28: '3', 33: '3',
                  36: '3', 37: '3', 38: '15', 39: '3', 40: '3', 41: '3', 42: '3',
                  43: '15', 44: '3', 45: '3', 46: '8', 47: '8', 48: '35', 49: '8', 50: '8'}
EQUALITY_DUAL = ('0', '0', '3', '1', '0', '0', '-3', '0', '0', '0', '0',
                 '-3', '-3', '-8', '0', '0', '-6/5', '-6/5', '0')


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
    if isinstance(value, (tuple, list)):
        return [encode(v) for v in value]
    return value


def head_load(j, layout):
    r, c, s, rr, t, cc, u = layout
    return tuple(1+int(j.ROOT[a] == r)+int(a == c)+int(b == s)
                 +int(j.ROOT[a] == rr and b == t)+int(a == cc and b == u)
                 for a, b in product(range(5), repeat=2))


class JointSurvivorLP:
    """101 nonnegative variables: x25,y25,e3_25,e5_25,t; no solver dependency."""
    def __init__(self, j):
        self.rows, self.rhs, self.equalities, self.erhs = [], [], [], []

        def add(row, rhs):
            self.rows.append(row)
            self.rhs.append(rhs)

        def equal(row, rhs):
            self.equalities.append(row)
            self.erhs.append(rhs)

        _, caps, _, density = j.source_tables(j.LO)
        raw_caps = tuple(v for row in caps for v in row)
        w = tuple(v for row in density for v in row)
        for i, cap in enumerate(raw_caps):
            row = {i: F(1)}
            if i == 17:
                row[100] = j.HI-j.LO
            if i == 22:
                row[100] = -(j.HI-j.LO)
            add(row, cap)
        add({100: F(1)}, F(1))
        for i in range(25):
            add({25+i: F(1), 50+i: F(1), 75+i: F(1), i: -w[i]}, F(0))
        groups = (tuple(range(5)), tuple(range(5, 10)), tuple(range(10, 25)))
        for group, mass in zip(groups, (F(1, 24), F(1, 12), F(1, 8))):
            equal({i: F(1) for i in group}, mass)
        equal({25+i: F(1) for i in range(25)}, F(3, 20))
        for s in range(5):
            equal({50+s: F(1), 55+s: F(1)}, j.QSLOTS[s]/90)
        for c in range(5):
            equal({75+5*c+s: F(1) for s in range(5)}, j.ETA[c]*(1+int(c >= 2))/100)
        for i in range(10, 25):
            add({50+i: F(1)}, F(0))
        for c in range(5):
            equal({5*c+4: F(1)}, j.ETA[c]/5)
        require(len(self.rows) == 66 and len(self.equalities) == 19
                and all(0 <= i <= 100 for row in self.rows+self.equalities for i in row),
                'Exactly the101-variable joint actual-source model')

    def check_dual(self, B):
        objective = (F(0),)*25+tuple(F(v*v) for v in B)+(F(0),)*51
        y = tuple(F(INEQUALITY_DUAL.get(i, '0')) for i in range(66))
        z = tuple(map(F, EQUALITY_DUAL))
        require(len(objective) == 101 and len(z) == 19 and min(y) >= 0,
                'Every inequality multiplier is nonnegative; equality multipliers are unrestricted')
        margins = tuple(sum(row.get(i, F(0))*price for row, price in zip(self.rows, y))
                        +sum(row.get(i, F(0))*price for row, price in zip(self.equalities, z))
                        -objective[i] for i in range(101))
        require(min(margins) >= 0, 'All101 exact dual column inequalities')
        upper = sum(a*b for a, b in zip(self.rhs, y))+sum(a*b for a, b in zip(self.erhs, z))
        require(upper == F(2593, 1800), 'Exact same-source survivor-square head upper')
        return {'objective': objective, 'nonzero_inequality_duals': INEQUALITY_DUAL,
                'equality_duals': z, 'all_column_margins': margins,
                'minimum_column_margin': min(margins), 'head_square_upper': upper}

    def specification(self):
        return {'nonnegative_variable_count': 101,
                'variable_blocks': {'raw_source': [0, 25], 'actual_survivor': [25, 50],
                                    'pure3deep_deletion': [50, 75], 'deep5_deletion': [75, 100],
                                    'normalized_late_parameter': [100, 101]},
                'inequality_count': len(self.rows), 'equality_count': len(self.equalities),
                'inequality_rows': self.rows, 'inequality_rhs': self.rhs,
                'equality_rows': self.equalities, 'equality_rhs': self.erhs}


def old_complete_bound(j, problem, layout, tail):
    B = head_load(j, layout)
    require(min(B) >= 1 and max(B) <= 6, 'Independent original six-label head')
    square = tuple(v*v for v in B)
    weighted = tuple(w*v for w, v in zip(problem.w, square))
    corrections = j.deletion_correction(square)
    old_cross = 2*problem.old_tail(tuple(w*v for w, v in zip(problem.w, B)))
    crosses = tuple(old_cross+F(2, 5)*problem.raw_row(B, theta)+tail for theta in (j.LO, j.HI))
    heads = tuple(problem.lp(weighted, theta)-sum(corrections) for theta in (j.LO, j.HI))
    return {'head_square_endpoint_uppers': heads, 'twice_old_cross': old_cross,
            'complete_cross_tail_endpoint_uppers': crosses,
            'complete_square_endpoint_uppers': tuple(a+b for a, b in zip(heads, crosses))}


def calculate(base):
    require(PINS, 'Final mathematical input pins')
    io = module('joint_j_square_io', base/'certificate_io.py')
    prior = json.loads(io.read_artifact_bytes(base/'certificates/source_norms/j-geometry/j_face_shared_square_factorial.json'))
    pins = dict(PINS)
    for path, pin in prior['source_sha256'].items():
        require(path not in pins or pins[path] == pin, 'Consistent241 source closure')
        pins[path] = pin
    for path, pin in pins.items():
        require(sha256(io.read_artifact_bytes(base/path)).hexdigest() == pin, 'Pinned mathematical input '+path)
    j = module('joint_j_source', base/'frontier/j-geometry/j_face_coupled_seven_heads.py')
    moment = module('joint_j_moments', base/'frontier/j-geometry/j_face_shared_square_factorial.py')
    require(F(prior['complete_square_upper']) == F(371, 80)
            and F(prior['complete_factorial_upper']) == F(6353, 7200)
            and F(prior['survivor_mass']) == F(3, 20) and F(prior['complete_mean_upper']) == F(16, 25)
            and tuple(map(F, prior['geometry']['late_split_interval'])) == (j.LO, j.HI),
            'The complete same-J domain, actual mass, mean and inherited factorial theorem')
    problem, lp = moment.JMomentHead(j), JointSurvivorLP(j)
    dual = lp.check_dual(head_load(j, CONTROLLER))
    tail = F(prior['complete_tail_partition']['complete_ordered_tail_square'])
    require(tail == F(5947, 3600), 'All241 ordered tail pairs and both complete diagonals')
    controller = old_complete_bound(j, problem, CONTROLLER, tail)
    cross = max(controller['complete_cross_tail_endpoint_uppers'])
    target = dual['head_square_upper']+cross
    require(cross == F(11431, 3600) and target == F(5539, 1200), 'Same-layout complete controller comparison')
    digest, count, retained = sha256(), 0, 0
    old_max, other_max, all_max = F(-1), F(-1), F(-1)
    other_witnesses = []
    for layout in j.layouts():
        parts = old_complete_bound(j, problem, layout, tail)
        old_upper = max(parts['complete_square_endpoint_uppers'])
        old_max = max(old_max, old_upper)
        if layout == CONTROLLER:
            require(parts == controller, 'The same original complete controller')
            adopted = min(old_upper, target)
            retained += 1
        else:
            require(old_upper <= target, 'Every remaining original layout has a complete241 upper below the new target')
            adopted = old_upper
            if old_upper > other_max:
                other_max, other_witnesses = old_upper, [{'layout': layout, 'components': parts}]
            elif old_upper == other_max:
                other_witnesses.append({'layout': layout, 'components': parts})
        all_max = max(all_max, adopted)
        digest.update(json.dumps(encode({'layout': layout, 'components': parts, 'adopted_upper': adopted}),
                                 separators=(',', ':')).encode())
        count += 1
        if count % 2500 == 0:
            print('Checked '+str(count)+' complete original J layouts', flush=True)
    require(count == 12500 and retained == 1 and other_max == F(16439, 3600)
            and old_max == F(371, 80) and all_max == target, 'Complete12500-layout partition and both exact maxima')
    return encode({'schema': 'erdos7-j-face-joint-retained-square-v1', 'source_sha256': pins,
                   'geometry': prior['geometry'], 'survivor_mass': F(3, 20), 'complete_mean_upper': F(16, 25),
                   'complete_square_upper': all_max, 'previous_complete_square_upper': old_max,
                   'complete_square_improvement': old_max-all_max,
                   'complete_factorial_upper': F(prior['complete_factorial_upper']),
                   'complete_tail_partition': prior['complete_tail_partition'],
                   'joint_source_model': lp.specification(), 'exact_retained_head_dual': dual,
                   'controller_layout': CONTROLLER, 'controller_original_components': controller,
                   'controller_complete_uniform_cross_tail': cross, 'controller_complete_upper': target,
                   'original_head_count': count, 'joint_dual_head_count': retained,
                   'other_complete_head_count': count-retained, 'other_head_maximum': other_max,
                   'other_maximizing_witnesses': other_witnesses,
                   'all_complete_head_components_sha256': digest.hexdigest(),
                   'scope': 'Both whole actual saturated J faces. One101-column exact rational dual retains raw/source/deletion masses and the source-free H column over the full late-split interval; all12500 original layouts retain complete241 crosses and tails. The new LP is not reduced to theta endpoints. Factorial6353/7200 is inherited from241. No optimization dependency, stronger deletion product assumption, actual-attainment claim, off-face/global52-cost comparison, Lean or unrestricted Erdos7 result.'})


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base', type=Path, default=Path(__file__).resolve().parents[2])
    modes = parser.add_mutually_exclusive_group()
    modes.add_argument('--write', action='store_true')
    modes.add_argument('--check', action='store_true')
    args = parser.parse_args()
    result = calculate(args.base)
    io = module('joint_j_square_output', args.base/'certificate_io.py')
    if args.write:
        io.write_certificate_text(args.base/CERTIFICATE, json.dumps(result, indent=2)+'\n')
    else:
        require(result == json.loads(io.read_artifact_bytes(args.base/CERTIFICATE)), 'Exact complete retained-J square certificate')
    print('PASS: complete J square='+result['complete_square_upper']+'; inherited factorial='
          +result['complete_factorial_upper']+'; one exact101-column dual and all12500 complete original heads.')


if __name__ == '__main__':
    try:
        main()
    except (ValueError, ArithmeticError, OSError, KeyError, TypeError, json.JSONDecodeError) as error:
        print('FAIL: '+str(error), file=sys.stderr)
        raise SystemExit(1)
