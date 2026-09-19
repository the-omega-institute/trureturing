#!/usr/bin/env python3
"""Exact scalar positive-seven source extrema at the off-diagonal endpoint.

Complete geometric tails, fixed original35 block layouts, and explicit
finite original-label constructions. Ordinary proofs in profile54 supply
universal bounds and limiting quantifiers. Default read-only; --output
writes exact rational JSON. Standard library only; supports python3 -I -O.
"""
import argparse
from collections import defaultdict
from fractions import Fraction as F
from hashlib import sha256
import importlib.util
from itertools import product
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
PINS = {'frontier/source_cost_endpoint_attainment.py':
        'b7daf5ab9c8656d922681e298b030c199c5f9bcc36af7a43e84a5bef156fb68f'}
BPLUS, BMINUS = (2, 3, 1, 1, 1), (1, 1, 2, 2, 3)
CELLS = (0, 3, 1, 4, 7)


def require(condition, message):
    if not condition:
        raise ValueError(message)


def load(base, path, name):
    file = base/path
    require(sha256(file.read_bytes()).hexdigest() == PINS[path], 'Source pin: '+path)
    spec = importlib.util.spec_from_file_location(name, file)
    require(spec is not None and spec.loader is not None, 'Loadable source: '+path)
    result = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(result)
    return result


class ScalarCost:
    """Independent evaluation of scalar costs with proved affine tails."""
    def __init__(self, source, tag):
        self.source, self.tag = source, tag
        degree, self.slope, self.constant, self.cut = source.zero5_cost_metadata(tag)
        require(degree == 1, 'Affine scalar source cost')
        require(self.slope >= 0, 'Nonnegative affine slope')
        self.tail0, self.tail1 = (4*x for x in source.geom(5, self.cut)[:2])
        for v in range(1, self.cut+3):
            require(self.f(v) >= 0 and self.f(v+1) >= self.f(v), 'Nonnegative increasing scalar cost')
            require(self.f(v+2)-2*self.f(v+1)+self.f(v) >= 0, 'Discrete scalar convexity')
        require(all(self.f(v) == self.slope*v+self.constant
                    for v in (self.cut, self.cut+1)), 'Affine metadata entrance')

    def f(self, v):
        return self.source.zero5_cost(self.tag, v)

    def deep(self, fn, start, step, slope, cut):
        if step == 0:
            return F(0)
        entry = max(0, self.source.ceilq(F(cut-start, step)))
        value = sum((F(1, 3**(k+3))*(fn(start+(k+1)*step)-fn(start+k*step))
                     for k in range(entry)), F(0))
        at = start+entry*step
        require(fn(at+step)-fn(at) == fn(at+2*step)-fn(at+step) == slope*step,
                'Exact geometric affine-tail entrance')
        return value+slope*step*self.source.geom(3, entry+3)[0]

    def D(self, start, step=1):
        return self.deep(self.f, start, step, self.slope, self.cut)

    def q(self, n, v):
        return (self.f(n*v)-self.f(n))/n

    def bar(self, v):
        return sum((F(4, 5**n)*self.q(n, v) for n in range(2, self.cut)), F(0)) \
            + self.tail0*self.slope*(v-1)-self.f(v)/5

    def Dbar(self, start):
        return self.deep(self.bar, start, 1, F(0), self.cut)

    def pure_q(self, n, b, eta):
        return sum(eta[l]*self.q(n, b[l]) for l in range(5)) \
            + max(self.deep(lambda v: self.q(n, v), b[l], 1, self.slope,
                            self.source.ceilq(F(self.cut, n))) for l in range(5))

    def envelopes(self, dat):
        d, masses, eta, _, _ = dat
        bases = self.source.BASES
        zero = [sum(masses[l]*self.f(b[l])+eta[l]*self.bar(b[l]) for l in range(5))
                + max(d[l]*self.D(b[l])+self.Dbar(b[l]) for l in range(5)) for b in bases]
        pure = {n: [self.pure_q(n, b, eta) for b in bases] for n in range(2, self.cut)}
        affine = [sum(eta[l]*(b[l]-1) for l in range(5))+F(1, 18) for b in bases]
        positive = []
        for ci in range(len(bases)):
            val = sum((F(4, 5**n)*(sum(eta)*self.f(n)+pure[n][ci]+(n-2)*max(pure[n]))
                       for n in range(2, self.cut)), F(0))
            val += sum(eta)*(self.slope*self.tail1+self.constant*self.tail0)
            val += self.slope*(self.tail0*affine[ci]
                               +(self.tail1-2*self.tail0)*max(affine))
            positive.append(val)
        pairs = []
        for bi, b in enumerate(bases):
            for ci, c in enumerate(bases):
                gaps = [(self.f(2*b[l])+self.f(2*c[l]))/2-self.f(b[l]+c[l]) for l in range(5)]
                require(min(gaps) >= 0, 'Nonnegative exact shallow Jensen gap')
                lower = sum(eta[l]*gaps[l] for l in range(5))-max(gaps)/9
                pairs.append({'zero': bi, 'positive': ci, 'lower_gap': lower,
                              'value': zero[bi]+positive[ci]-F(4, 25)*lower,
                              'nonnegative_gap_value': zero[bi]+positive[ci]
                                  -F(4, 25)*max(F(0), lower)})
        corrected = max(row['value'] for row in pairs)
        old = self.source.zero5_raw(self.tag, dat)
        require(old == max(zero)+max(positive), 'Independent old-source envelope reconstruction')
        return old, corrected, pairs

    def pure_mixed_integral(self, k, sign, eta, height=None):
        if sign == 'minus':
            baseline = tuple((k+1)*x for x in BMINUS)
            chains = [(4, k+1)]
        else:
            baseline = tuple(BPLUS[l]+k*BMINUS[l] for l in range(5))
            chains = [(1, 1), (4, k)]
        value = sum(eta[l]*self.f(baseline[l]) for l in range(5))
        for cell, step in chains:
            if height is None:
                value += self.D(baseline[cell], step)
            else:
                value += sum((F(1, 3**a)*(self.f(baseline[cell]+(a-2)*step)
                                           -self.f(baseline[cell]+(a-3)*step))
                              for a in range(3, height+1)), F(0))
        return value

    def actual_integral(self, dat, sign, height=None):
        d, masses, eta, _, _ = dat
        b, cell = (BMINUS, 4) if sign == 'minus' else (BPLUS, 1)
        value = sum(masses[l]*self.f(b[l]) for l in range(5))
        if height is None:
            value += d[cell]*self.D(3)
            end = self.cut-1
        else:
            value += d[cell]*sum((F(1, 3**a)*(self.f(a+1)-self.f(a))
                                  for a in range(3, height+1)), F(0))
            end = height
        for k in range(1, end+1):
            value += F(1, 5**k)*(self.pure_mixed_integral(k, sign, eta, height)
                                 -self.pure_mixed_integral(k-1, sign, eta, height))
        if height is None:
            mean_minus = sum(eta[l]*BMINUS[l] for l in range(5))+F(1, 18)
            value += self.source.geom(5, self.cut)[0]*self.slope*mean_minus
        return value


def finite_histograms(constructor, height):
    """Actual forbidden masks and two independently labelled original tests."""
    A, B = 3**height, 5**height
    all5 = (1 << B)-1
    state = [all5]*A
    for a, b in product(range(height+1), repeat=2):
        if a+b == 0:
            continue
        aa, ra, bb, rb = constructor.source(a, b, 'off-diagonal')
        removed = sum(1 << y for y in range(rb, B, 5**bb))
        for x in range(ra, A, 3**aa):
            state[x] &= all5 ^ removed
    nested = [sum(1 << y for y in range(4, B, 5**b)) for b in range(1, height+1)]
    strata = [all5 ^ nested[0]]+[nested[b-1] ^ nested[b] for b in range(1, height)]+[nested[-1]]
    hist = {sign: defaultdict(int) for sign in ('minus', 'plus')}
    for l, cell in enumerate(CELLS):
        for x in range(cell, A, 9):
            minus = 1+sum(x % (3**a) == 7 % (3**a) for a in range(1, height+1))
            plus = 1+int(x % 3 == 0)+sum(x % (3**a) == 3 for a in range(2, height+1))
            for k, mask in enumerate(strata):
                count = (state[x] & mask).bit_count()
                hist['minus'][l, (k+1)*minus] += count
                hist['plus'][l, plus+k*minus] += count
    return hist, A*B


def seven_checks(constructor, height):
    """Exact finite pure7 and source-free nested class4 cylinder counts."""
    period = 7**height
    survivor = bytearray(b'\1')*period
    forbidden = bytearray(period)
    classes = set()
    for a, b in product(range(height+1), repeat=2):
        if a+b:
            classes.add(constructor.mixed(a, b, 'off-diagonal')[0])
    require(classes == {1, 2, 3, 5}, 'Actual mixed7 classes omit class4')
    for j in classes | {6}:
        for e in range(1, height+1):
            for z in range(j*7**(e-1), period, 7**e):
                forbidden[z] = 1
                if j == 6:
                    survivor[z] = 0
    u = F(sum(survivor), period)
    require(u == (5+F(1, period))/6, 'Finite actual pure7 surviving mass')
    counts = defaultdict(int)
    for z in range(period):
        active = sum(z % (7**e) == 4 for e in range(1, height+1))
        if active:
            require(forbidden[z] == 0, 'Nested class4 tests avoid every actual forbidden seven cylinder')
        if survivor[z]:
            counts[1+active] += 1
    probabilities = {n: F(count, sum(survivor)) for n, count in sorted(counts.items())}
    require(probabilities[1] == 1-F(1, 7)/u, 'Finite first count probability')
    for n in range(2, height+1):
        require(probabilities[n] == (F(1, 7**(n-1))-F(1, 7**n))/u,
                'Finite nested middle count probability')
    require(probabilities[height+1] == F(1, period)/u, 'Finite last count retains the full tail')
    return {'height': height, 'pure7_mass': u, 'count_probabilities': probabilities,
            'mixed_classes': sorted(classes)}


def original_test_labels(constructor, height, threshold):
    labels = []
    for a, b, e in product(range(height+1), repeat=3):
        if a+b+e == 0:
            continue
        sign = 'minus' if e == 0 or (threshold == 5 and e == 1) else 'plus'
        ternary = 7 if b > 0 or sign == 'minus' else (0 if a <= 1 else 3)
        ra, rb, re = ternary % (3**a), 4 % (5**b), 4 % (7**e)
        modulus, residue = constructor.crt(a, ra, b, rb, e, re)
        require(all(residue % m == r for m, r in ((3**a, ra), (5**b, rb), (7**e, re))),
                'Original test CRT preserves all chosen block coordinates')
        labels.append((modulus, residue))
    require(len(labels) == len(set(m for m, _ in labels)) == (height+1)**3-1,
            'Exactly one genuine original residue per nonunit test label')
    return {'height': height, 'threshold': threshold, 'distinct_original_moduli': len(labels)}


def calculate(base):
    parent = load(base, 'frontier/source_cost_endpoint_attainment.py', 'positive_attainment')
    source = parent.load(base, 'verify_joint_frontier.py', 'positive_source')
    constructor = parent.load(base, 'frontier/sharp_source_mass_endpoints.py', 'positive_constructor')
    for path, pin in parent.PINS.items():
        require(sha256((base/path).read_bytes()).hexdigest() == pin, 'Parent source pin: '+path)
    dat = source.data(list(source.vertices())[404])
    require(dat[3:] == (F(1, 4), F(3, 20)) and source.BASES[1] == BPLUS
            and source.BASES[9] == BMINUS, 'Same off-diagonal endpoint and actual test baselines')
    expected = {(4, 1): (F(482, 8575), F(482, 8575), 'plus'),
                (4, 2): (F(187, 17150), F(187, 17150), 'plus'),
                (5, 1): (F(110031, 2401000), F(108369, 2401000), 'minus'),
                (5, 2): (F(4523, 480200), F(4523, 480200), 'plus'),
                (5, 3): (F(771, 480200), F(771, 480200), 'plus')}
    costs, rows, exception_pairs = {}, [], []
    for (t, e), (expected_old, expected_sharp, sign) in expected.items():
        cost = ScalarCost(source, ('seven_block', (('h', F(t)), e)))
        costs[t, e] = cost
        old, corrected, pairs = cost.envelopes(dat)
        actual = cost.actual_integral(dat, sign)
        require(old == expected_old and corrected == actual == expected_sharp,
                'Exact old/sharp/actual source block '+str((t, e)))
        require(max(p['nonnegative_gap_value'] for p in pairs) == corrected,
                'Raw profile51 and positive-part Jensen corrections have the same endpoint maximum')
        rows.append({'threshold': t, 'positive7_block': e, 'old_envelope': old,
                     'sharp_envelope': corrected, 'actual_integral': actual, 'test': sign,
                     'controllers': [p for p in pairs if p['value'] == corrected]})
        if (t, e) == (5, 1):
            exception_pairs = pairs
    linear = ScalarCost(source, ('h', F(0)))
    linear_actual = linear.actual_integral(dat, 'plus')-dat[3]
    linear_old = source.zero5_raw(('h', F(0)), dat)-dat[3]
    require(linear_actual == linear_old == F(1, 2), 'Sharp full affine source norm')
    for t, e in ((4, 3), (5, 4)):
        cost = ScalarCost(source, ('seven_block', (('h', F(t)), e)))
        require(cost.slope == -cost.constant == F(6, 5*7**e), 'Complete affine seven-block entrance')
        require(cost.actual_integral(dat, 'plus') == source.zero5_raw(cost.tag, dat) == F(3, 5*7**e),
                'First affine block exact attainment')
        costs[t, e] = cost
    exceptional = costs[5, 1]
    require(exceptional.f(1) == 0 and exceptional.f(2) == F(117, 12005)
            and exceptional.slope == F(6, 35) and exceptional.constant == -F(4881, 12005)
            and all(exceptional.f(v) == F(6, 35)*v-F(4881, 12005)
                    for v in range(3, exceptional.cut+1)), 'Exact exceptional scalar cost formula')
    j5 = sum((F(4, 5**n)*exceptional.f(n) for n in range(2, exceptional.cut)), F(0))
    j5 += exceptional.slope*exceptional.tail1+exceptional.constant*exceptional.tail0
    constant = sum(dat[2])*j5+exceptional.slope*F(1, 20)*F(1, 2)
    require(constant == F(2424, 300125), 'Derived positive-block affine constant')
    corner_scores = [(max(p['nonnegative_gap_value'] for p in exception_pairs if p['zero'] == b)-constant)*7203000
                     for b in range(10)]
    raw_corner_scores = [(max(p['value'] for p in exception_pairs if p['zero'] == b)-constant)*7203000
                         for b in range(10)]
    require(corner_scores == [220173, 255453, 201943, 202918, 203893,
                             235854, 249367, 241451, 257131, 266931],
            'Independent reconstruction of all ten exceptional corner scores')
    finite = []
    for height in (3, 4):
        hist, period = finite_histograms(constructor, height)
        finite_dat = source.data(parent.parameter(height))
        for sign in ('minus', 'plus'):
            require(F(sum(hist[sign].values()), period) == finite_dat[3], 'Actual finite source histogram mass')
        for (t, e), cost in costs.items():
            for sign in ('minus', 'plus'):
                actual = sum(F(count, period)*cost.f(v) for (_, v), count in hist[sign].items())
                formula = cost.actual_integral(finite_dat, sign, height)
                require(actual == formula, 'Original-label finite mask versus nested formula')
                finite.append({'height': height, 'threshold': t, 'block': e,
                               'test': sign, 'integral': actual})
    delta = expected[5, 1][0]-expected[5, 1][1]
    require(delta == F(831, 1200500), 'Sharp first-positive7 loss')
    sums = {4: expected[4, 1][1]+expected[4, 2][1]+F(1, 490),
            5: sum(expected[5, e][1] for e in (1, 2, 3))+F(1, 3430)}
    require(sums[4] == F(593, 8575), 'Complete positive7 source sum at four')
    complements = {}
    for t in (4, 5):
        constant7 = dat[3]*F(1, 5*7**(t-1))
        zero7 = source.zero5_raw(('seven_block', (('h', F(t)), 0)), dat)
        old_complement = source.raw357(F(t), dat)-zero7
        old_sum = sums[t]+(delta if t == 5 else 0)
        require(old_complement == constant7+old_sum, 'Existing positive7 complement includes its constant')
        complements[t] = {'constant': constant7, 'old': old_complement,
                          'sharp': constant7+sums[t]}
    return {'schema': 'erdos7-positive-seven-source-extrema-v1', 'source_vertex': 404,
            'source_sha256': {**PINS, **parent.PINS}, 'source_extrema': rows,
            'exceptional_baseline_pairs': exception_pairs,
            'exceptional_affine_constant': constant,
            'exceptional_scaled_corner_scores': corner_scores,
            'exceptional_raw_gap_scaled_corner_scores': raw_corner_scores,
            'sharp_source_sums': sums, 'sharp_first_block_loss': delta,
            'positive7_complements': complements,
            'affine_source_norm': linear_actual,
            'finite_original35_checks': finite,
            'finite_seven_checks': [seven_checks(constructor, h) for h in (2, 3, 4)],
            'finite_original357_test_labels': [original_test_labels(constructor, h, t)
                                               for h in (3, 4) for t in (4, 5)],
            'scope': ('Scalar positive-seven source35 block extrema, compatible with the same '
                      'actual endpoint forbidden families. Ordinary arguments supply complete '
                      'tails and limits. No full357 hinge/deletion extremum, global K bound, '
                      'Lean verification or unrestricted Erdos7 resolution is claimed.')}


def encode(value):
    if isinstance(value, F):
        return str(value)
    if isinstance(value, dict):
        return {str(k): encode(v) for k, v in value.items()}
    if isinstance(value, (tuple, list)):
        return [encode(v) for v in value]
    return value


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base', type=Path, default=Path(__file__).resolve().parents[1])
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    result = calculate(args.base)
    if args.output is not None:
        args.output.write_text(json.dumps(encode(result), indent=2)+'\n')
    print('PASS:five positive7 source extrema,500 baseline pairs,28 finite original35 tests,3 actual pure7 laws and4 original357 label families.')
    print('Sharp c5,1 loss831/1200500; source35 block extrema only, complete357 remains open.')


if __name__ == '__main__':
    main()
