#!/usr/bin/env python3
"""Uniform actual-source factorial tails, retaining the original head."""
import argparse
from fractions import Fraction as F
from hashlib import sha256
import importlib.util
from itertools import product
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
CERTIFICATE = 'certificates/source_norms/uniform_factorial_neighborhood.json'
ROOT = (0, 0, 1, 1, 1)
PINS = {
    'certificate_io.py': '287582353eeb0674f4e80530ebf268228b023f6088d14c819488a56111d0b232',
    'frontier/complete_off_face_factorial_tail.py': '8447e1cd50d6452a881413067858188344d22631c7b73b74734b3006a244d047',
    'frontier/uniform_k_neighborhood_cost.py': '2868fc48d2b02e889402f7c2cbf89cd4236d28a3d575b53cf3cbdf48cd2dd781',
}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    require(spec is not None and spec.loader is not None, 'Loadable input')
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


class UniformFactorialHead:
    """Outer tables, not a synthetic actual-source case or a realizability claim."""
    def __init__(self, factorial, tails, finite, face, parameters):
        self.factorial, self.tails = factorial, tails
        self.par = par = parameters
        self.delta, self.rho = par['delta'], par['rho']
        d, r = self.delta, self.rho
        self.reference = factorial.FactorialHead(finite, tails, face)
        self.pre, self.descendant, self.caps = [], [], []
        self.wupper, self.wlower = [], []
        self.qsum = min(F(2, 5), r/par['gap'])
        self.eta_upper = ((1+d)/18,)+(F(1, 9),)*4
        self.q_lower = tuple(max(F(0), v) for v in
                             (F(0), F(1, 5)-d/4, F(1, 5)-d/4, F(3, 20), F(1, 5)-2*par['rbar']))
        self.error27 = d/360+par['Cbar']*r
        self.head_caps, self.raw_rows = [], []
        for c, j in product(range(5), repeat=2):
            i = 5*c+j
            old_p = face['point']['pre'][i]
            p = old_p+(par['v0'] if c < 2 else par['v1']) if j == 3 else old_p
            descendant = self.eta_upper[c] if old_p > 0 else F(0)
            U = self.eta_upper[c]*p
            wstar = self.reference.w[i]
            upper = min(F(1), wstar+(d/5 if c else 0)+(self.qsum if j == 4 else 0))
            lower = max(F(0), wstar-(d/5 if c else 2*d/5))
            require(0 <= p <= F(1, 5) and 0 <= lower <= upper <= 1,
                    'Positive uniform source and density envelopes')
            self.pre.append(p); self.descendant.append(descendant); self.caps.append(U)
            self.wupper.append(upper); self.wlower.append(lower)
            credit = max(F(0), self.q_lower[j]/135-self.error27) if c == 1 else F(0)
            self.head_caps.append(min(U, max(F(0), upper*U-credit+r)))
            self.raw_rows.append(6*U+p/9+3*descendant/20+F(int(descendant > 0), 360))
        self.pairs = self.complete_pairs()
        self.old_cache = {}

    def coefficients(self, values):
        return (max(sum(self.pre[5*c+j]*values[5*c+j] for j in range(5)) for c in range(5)),
                max(sum(self.descendant[5*c+j]*values[5*c+j] for c in range(5)) for j in range(5)),
                max(sum(self.descendant[5*c+j]*values[5*c+j] for c in range(5) if ROOT[c] == r)
                    for r, j in product(range(2), range(5))),
                max(x*y for x, y in zip(self.descendant, values)), max(values))

    def old_cross(self, h):
        if h not in self.old_cache:
            f = self.factorial
            base = self.coefficients(tuple(w*v for w, v in zip(self.wupper, h)))
            cap = self.coefficients(tuple((1-w)*v for w, v in zip(self.wlower, h)))
            mass = max(h)*self.rho
            nominal = sum(v*q for v, q in zip(base, (F(1, 18), F(1, 20), F(1, 20), F(1, 20), F(1, 72))))
            error = (f.clipped_line(mass, cap[0], 3, 3)
                     +sum(f.clipped_line(mass, v, 5, 2) for v in cap[1:4])
                     +f.clipped_product(mass, cap[4]))
            self.old_cache[h] = nominal, error
        return self.old_cache[h]

    def components(self, layout):
        r3, c9, s5, r15, s15, c45, s45 = layout
        load = self.reference.load(layout)
        compatible = r3 == ROOT[c9] == r15 and s5 == s15
        full = compatible and c45 == c9 and s45 == s5
        head = self.head_caps[5*c9+s5] if full else F(0)
        nominal, error = self.old_cross(tuple(max(v-4, 0) for v in load))
        seven = (self.raw_rows[5*c45+s45]+(self.raw_rows[5*c9+s5] if compatible else 0))/5
        return {'head': head, 'old_cross_baseline': nominal, 'old_cross_error': error,
                'positive7_cross': seven, 'head_total': head+nominal+error+seven}

    def complete_pairs(self):
        f, par, d = self.factorial, self.par, self.delta
        eps = (par['kbar']*self.rho, self.rho+d/240, self.rho, self.rho)
        weighted = {}
        for j, (name, prime, start, slope, intercept) in enumerate(
                (('pure3', 3, 3, 2, -6), ('pure5', 5, 2, 2, -4),
                 ('root5', 5, 2, 6, -10), ('cell5', 5, 2, 10, -16))):
            row = {'prime': prime, 'start': start, 'raw': par['c'][j]+par['H'][j],
                   'branches': ((par['c'][j], eps[j], par['H'][j]),)}
            weighted[name] = f.weighted_family(self.tails, row, slope, intercept)
        a0, aw = f.geometric(3, 3), f.geometric(3, 3, 2, 1)
        b1, bw1 = f.geometric(5, 1), f.geometric(5, 1, 2, 1)
        b2, bw2 = f.geometric(5, 2), f.geometric(5, 2, 2, 1)
        mixed = f.geometric(3, 3, 6, -16)/5+aw*bw2-13*a0*b2
        old_old = (sum(weighted.values())+mixed)/2
        raw = (F(1, 4)+d/2, F(5, 36)+d/2, F(1, 12)+d/2,
               F(3, 4)+d/4, F(1, 2)+d/18, F(1, 3), F(1, 9), F(1))
        linear_weights = (F(1), F(1), F(1), a0, b1, b1, b1, a0*b1)
        square_weights = (F(1), F(3), F(5), aw, bw1, 3*bw1, 5*bw1, aw*bw1)
        pair_prices = tuple((4*q/15-p/5)/2 for p, q in zip(linear_weights, square_weights))
        require(min(pair_prices) > 0, 'Combine every P77 LCM weight before upper-bounding its raw cap')
        positive_positive = sum(p*v for p, v in zip(pair_prices, raw))
        _, _, _, D, h, h1, em, _ = raw
        old_positive = (D*f.geometric(3, 3, 2, -2)
                        +(h+3*h1+5*em)*f.geometric(5, 2, 2, -1)
                        +F(3, 5)*f.geometric(3, 3, 2, -2)+aw*bw2-6*a0*b2)/5
        return {'old_old_distinct': old_old, 'old_positive7': old_positive,
                'positive7_positive7_distinct': positive_positive,
                'tail_distinct_pairs': old_old+old_positive+positive_positive,
                'weighted_old_pure_blocks_before_halving': weighted,
                'weighted_old_mixed_before_halving': mixed,
                'raw_coefficient_upper': raw, 'positive7_pair_prices': pair_prices}


def calculate(base):
    for path, pin in PINS.items():
        require(sha256((base/path).read_bytes()).hexdigest() == pin, 'Pinned input '+path)
    io = module('uniform_factorial_io', base/'certificate_io.py')
    factorial = module('uniform_factorial_existing', base/'frontier/complete_off_face_factorial_tail.py')
    uniform = module('uniform_factorial_radius', base/'frontier/uniform_k_neighborhood_cost.py')
    # Reuse the producer's transitive source pins as well as direct files.
    for path, pin in factorial.PINS.items():
        require(sha256(io.read_artifact_bytes(base/path)).hexdigest() == pin, 'Pinned factorial input '+path)
    cost = module('uniform_factorial_cost', base/'frontier/complete_off_face_cost.py')
    finite = module('uniform_factorial_finite', base/'frontier/finite_source_face_transport.py')
    tails = module('uniform_factorial_tails', base/'frontier/complete_off_face_omitted_tails.py')
    source = module('uniform_factorial_source', base/'verify_joint_frontier.py')
    face = cost.face_case(finite, source)
    actual_case = cost.actual_398_case(finite, source, 12)
    actual = factorial.FactorialHead(finite, tails, actual_case)
    results = []
    for delta, rho in ((F(0), F(0)), (F(1, 10000), F(1, 100000))):
        par = uniform.parameters(delta, rho)
        problem = UniformFactorialHead(factorial, tails, finite, face, par)
        count, digest, best, witness = 0, sha256(), F(-1), None
        if rho:
            require(actual_case['sigma'] <= delta and actual_case['defects']['rho'] <= rho, 'Actual finite family in uniform rectangle')
            require(all(x <= y for x, y in zip(actual.point['pre'], problem.pre))
                    and all(x <= y for x, y in zip(actual.point['descendant'], problem.descendant))
                    and all(x <= y for x, y in zip(actual.point['caps'], problem.caps))
                    and all(lo <= w <= hi for lo, w, hi in zip(problem.wlower, actual.w, problem.wupper)),
                    'Actual finite tables are squeezed by uniform bounds')
            require(actual.pairs['tail_distinct_pairs'] <= problem.pairs['tail_distinct_pairs'], 'Actual full pair tail is dominated')
        for layout in product(range(2), range(5), range(5), range(2), range(5), range(5), range(5)):
            parts = problem.components(layout)
            reference = actual.components(layout) if rho else problem.reference.components(layout)
            for key in ('head', 'old_cross_baseline', 'old_cross_error', 'positive7_cross', 'head_total'):
                require(reference[key] <= parts[key] if rho else reference[key] == parts[key],
                        'Every original head component is dominated, with exact face recovery')
            value = parts['head_total']
            if value > best:
                best, witness = value, {'layout': layout, 'components': parts}
            digest.update(json.dumps(encode([layout, parts]), separators=(',', ':')).encode())
            count += 1
        upper = best+problem.pairs['tail_distinct_pairs']
        if not rho:
            require(best == F(139, 900) and problem.pairs['tail_distinct_pairs'] == F(2539, 3600)
                    and upper == F(619, 720), 'Full112 and128 face bound recovered')
        else:
            require(F(619, 720) < upper < F(9, 10), 'Nonzero source-uniform factorial bound below9/10')
        require(count == 12500, 'All original six-head layouts')
        results.append({'delta': delta, 'rho_radius': rho, 'parameters': par,
                        'pre_upper': problem.pre, 'descendant_upper': problem.descendant,
                        'caps_upper': problem.caps, 'density_lower': problem.wlower, 'density_upper': problem.wupper,
                        'raw_five_slot_lower': problem.q_lower, 'error27_upper': problem.error27,
                        'pair_partition': problem.pairs, 'head_maximum': best, 'maximizing_witness': witness,
                        'complete_factorial_upper': upper, 'original_head_count': count,
                        'distinct_old_cross_patterns': len(problem.old_cache), 'head_components_sha256': digest.hexdigest()})
    return encode({'schema': 'erdos7-uniform-factorial-neighborhood-v1', 'source_sha256': {**factorial.PINS, **PINS},
                   'radius_results': results, 'actual_finite_example_height': 12,
                   'scope': 'Uniform whole-source neighborhood factorial bound retaining each original head and all distinct-pair tails. Outer tables are not actual source records. No new global K, Lean verification or unrestricted solution.'})


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base', type=Path, default=Path(__file__).resolve().parents[1])
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument('--write', action='store_true')
    mode.add_argument('--check', action='store_true')
    args = parser.parse_args()
    result = calculate(args.base)
    io = module('uniform_factorial_writer', args.base/'certificate_io.py')
    if args.write:
        io.write_certificate_text(args.base/CERTIFICATE, json.dumps(result, indent=2)+'\n')
    elif args.check:
        require(json.loads(io.read_artifact_bytes(args.base/CERTIFICATE)) == result, 'Exact uniform-factorial certificate')
    for row in result['radius_results']:
        print('PASS: delta='+row['delta']+', rho<='+row['rho_radius']+', complete T5<='+row['complete_factorial_upper'])


if __name__ == '__main__':
    try:
        main()
    except (ValueError, ArithmeticError, OSError, KeyError, TypeError, json.JSONDecodeError) as error:
        print('FAIL: '+str(error), file=sys.stderr)
        sys.exit(1)
