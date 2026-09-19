#!/usr/bin/env python3
"""Exact source-cost extrema at the actual off-diagonal endpoint.

Read-only standard-library experiment; --output writes exact rational JSON.
Checks original-source finite histograms, all-depth integral formulas and
finite source-envelope maxima. General comparison and limiting quantifiers
are proved in profile51, not inferred from finite sampling here.
"""
import argparse
from collections import defaultdict
from fractions import Fraction as F
from hashlib import sha256
import importlib.util
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
PINS = {
    'verify_joint_frontier.py': '85341d7f8fa2d0b109697bc17b005a7e75f7f6ec412fd2eb3d26383cf9fce24f',
    'frontier/moments-survival/full_absorbed_survival_hinges.py': '3c5b0ba6df9c11bbba8a9b1a31824b504072e4659a2f0a9aa8348a0fe9e8e79d',
    'frontier/source-budgets/sharp_source_mass_endpoints.py': '79bb947d96c36895069f58568d7a5de2c22aa561753f03352e9eb741313147d9',
}
CELLS, BASELINE = (0, 3, 1, 4, 7), (1, 1, 2, 2, 3)
WEIGHTS = (1, 2, 0, 0, 0)


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


def parameter(height):
    t = sum((F(1, 3**a) for a in range(3, height+1)), F(0))
    q = sum((F(1, 5**b) for b in range(1, height+1)), F(0))
    return (tuple(map(F, (9*t, 0, 0, 0, 0))), tuple(map(F, (0, q))),
            tuple(map(F, (0, 0, q, 0, 0))), tuple(map(F, (0, 0, 0, t*q, 0))), 1-q)


def finite_formula(source, height, cost, weights):
    d, n, eta, _, _ = source.data(parameter(height))
    g = lambda l, v: cost.g(weights[l], v)
    value = sum(n[l]*g(l, BASELINE[l]) for l in range(5))
    value += d[4]*sum((F(1, 3**a)*(g(4, a+1)-g(4, a))
                      for a in range(3, height+1)), F(0))
    for b in range(1, height+1):
        difference = sum(eta[l]*(g(l, (b+1)*BASELINE[l])-g(l, b*BASELINE[l]))
                         for l in range(5))
        difference += sum((F(1, 3**a)*(g(4, (b+1)*(a+1))-g(4, (b+1)*a)
                           -g(4, b*(a+1))+g(4, b*a))
                           for a in range(3, height+1)), F(0))
        value += F(1, 5**b)*difference
    return value


def finite_histogram(constructor, height):
    """Enumerate actual source masks independently of their cell-mass formulas."""
    a_mod, b_mod = 3**height, 5**height
    all_five = (1 << b_mod)-1
    state = [all_five]*a_mod
    for a in range(height+1):
        for b in range(height+1):
            if a+b == 0:
                continue
            aa, ra, bb, rb = constructor.source(a, b, 'off-diagonal')
            removed = sum(1 << y for y in range(rb, b_mod, 5**bb))
            for x in range(ra, a_mod, 3**aa):
                state[x] &= all_five ^ removed
    nested = [sum(1 << y for y in range(4, b_mod, 5**b))
              for b in range(1, height+1)]
    strata = ([all_five ^ nested[0]]
              + [nested[b-1] ^ nested[b] for b in range(1, height)] + [nested[-1]])
    require(sum(mask.bit_count() for mask in strata) == b_mod, 'Exact nested-five partition')
    histogram = defaultdict(int)
    for l, cell in enumerate(CELLS):
        for x in range(cell, a_mod, 9):
            three_load = 1+sum(x % (3**a) == 7 % (3**a) for a in range(1, height+1))
            for five_load, mask in enumerate(strata, 1):
                histogram[l, five_load*three_load] += (state[x] & mask).bit_count()
    return histogram, a_mod*b_mod


def limiting_integral(source, cost, weights, dat):
    """Two complete geometric tails for the explicit nested original test."""
    d, n, eta, _, _ = dat
    g = lambda l, v: cost.g(weights[l], v)
    initial = sum(n[l]*g(l, BASELINE[l]) for l in range(5))+d[4]*cost.dg[weights[4], 3]
    positive = F(0)
    mean_three = sum(eta[l]*BASELINE[l] for l in range(5))+F(1, 18)
    for b in range(1, cost.cut):
        difference = sum(eta[l]*(g(l, (b+1)*BASELINE[l])-g(l, b*BASELINE[l]))
                         for l in range(5))
        def deep(m):
            return cost.deep(lambda v: g(4, m*v), 3,
                             max(3, (cost.cut+m-1)//m), F(m))
        difference += deep(b+1)-deep(b)
        positive += F(1, 5**b)*difference
    # At every b>=cut, each cell-cost increment is exactly B3.
    positive += source.geom(5, cost.cut)[0]*mean_three
    return initial+positive


def jensen_envelope(source, cost, weights, dat):
    """All100 baseline pairs; complete n-tail and affine Jensen lower bound."""
    d, n, eta, _, _ = dat
    initial = [sum(n[l]*cost.gs[weights[l], b[l]]+eta[l]*cost.bs[weights[l], b[l]]
                   for l in range(5))
               + max(d[l]*cost.dg[weights[l], b[l]]+cost.db[weights[l], b[l]]
                     for l in range(5)) for b in source.BASES]
    pure = {nn: [sum(eta[l]*cost.qs[nn, weights[l], b[l]] for l in range(5))
                 + max(cost.dq[nn, weights[l], b[l]] for l in range(5))
                 for b in source.BASES] for nn in range(2, cost.cut)}
    affine = [sum(eta[l]*(b[l]-1) for l in range(5))+F(1, 18) for b in source.BASES]
    positive = []
    for ci in range(len(source.BASES)):
        value = sum(F(4, 5**nn)*(sum(eta[l]*cost.g(weights[l], nn) for l in range(5))
                    + pure[nn][ci]+(nn-2)*max(pure[nn])) for nn in range(2, cost.cut))
        value += cost.tail1*sum(eta)
        value -= cost.tail0*sum(eta[l]*(cost.offset+F(weights[l], 5)*cost.C) for l in range(5))
        value += cost.tail0*affine[ci]+(cost.tail1-2*cost.tail0)*max(affine)
        positive.append(value)
    candidates = []
    for bi, b in enumerate(source.BASES):
        for ci, c in enumerate(source.BASES):
            gaps = tuple((cost.g(weights[l], 2*b[l])+cost.g(weights[l], 2*c[l]))/2
                         -cost.g(weights[l], b[l]+c[l]) for l in range(5))
            require(min(gaps) >= 0, 'Exact shallow Jensen gaps are nonnegative')
            lower = sum(eta[l]*gaps[l] for l in range(5))-max(gaps)/9
            candidates.append((initial[bi]+positive[ci]-F(4, 25)*lower, bi, ci, lower))
    best = max(v for v, _, _, _ in candidates)
    return best, [[bi, ci, lower] for v, bi, ci, lower in candidates if v == best]


def calculate(base):
    source = load(base, 'verify_joint_frontier.py', 'attainment_source')
    full = load(base, 'frontier/moments-survival/full_absorbed_survival_hinges.py', 'attainment_full')
    actual = load(base, 'frontier/source-budgets/sharp_source_mass_endpoints.py', 'attainment_constructor')
    require(source.BASES[9] == BASELINE, 'Original shallow test is root1 and cell4')
    dat = source.data(list(source.vertices())[404])
    require(dat[3:] == (F(1, 4), F(3, 20)) and dat[0][4] == F(1, 2), 'Same actual off-diagonal source endpoint')
    costs = {t: full.CellCost(source, t, F(1)) for t in (4, 5)}
    finite = []
    for height in (3, 4, 5):
        histogram, period = finite_histogram(actual, height)
        source_mass = source.data(parameter(height))[3]
        require(F(sum(histogram.values()), period) == source_mass, 'Actual source histogram total')
        for threshold, cost in costs.items():
            for weights in (WEIGHTS, (0, 0, 0, 0, 0)):
                direct = sum(F(count, period)*cost.g(weights[l], z)
                             for (l, z), count in histogram.items())
                formula = finite_formula(source, height, cost, weights)
                require(direct == formula, 'Original-source histogram equals exact nested-test integral')
                finite.append({'height': height, 'threshold': threshold, 'weights': weights,
                               'period35': period, 'integral': direct})
            tail = F(1, 7**height)
            finite_weights = tuple((1-tail)*w for w in WEIGHTS)
            finite_cost = sum(F(count, period)*cost.g(finite_weights[l], z)
                              for (l, z), count in histogram.items())
            limit_cost = finite_formula(source, height, cost, WEIGHTS)
            require(0 <= finite_cost-limit_cost <= F(2, 5)*tail*source_mass,
                    'Exact finite carrier-mixture cost error has uniform seven-tail bound')
    expected = {(4, WEIGHTS): F(382661, 2572500),
                (5, WEIGHTS): F(179394011, 1620675000),
                (4, (0, 0, 0, 0, 0)): F(1148669, 7717500),
                (5, (0, 0, 0, 0, 0)): F(179422823, 1620675000)}
    limiting = []
    for threshold, cost in costs.items():
        for weights in (WEIGHTS, (0, 0, 0, 0, 0)):
            value = limiting_integral(source, cost, weights, dat)
            old, _ = cost.operator(weights, dat)
            improved, controllers = jensen_envelope(source, cost, weights, dat)
            require(value == improved == expected[threshold, weights],
                    'Constructed exact integral attains universal two-baseline upper comparison')
            if weights == WEIGHTS or threshold == 5:
                require(value == old, 'Exact original absorbed/psi5 source-envelope attainment')
            else:
                require(old == F(6975217, 46305000) and old-value == F(83203, 46305000),
                        'Exact sharp unabsorbed psi4 source correction')
            limiting.append({'threshold': threshold, 'weights': weights, 'actual_integral': value,
                             'old_envelope': old, 'sharp_envelope': improved, 'gap': old-value,
                             'paired_layout_controllers': controllers})
    return {'schema': 'erdos7-offdiagonal-source-cost-attainment-v1', 'source_vertex': 404,
            'source_sha256': PINS, 'finite_original_source_checks': finite,
            'limiting_integrals': limiting, 'common_actual_mass_limit': F(3, 20),
            'limiting_carrier': [0, 1],
            'scope': ('The same actual off-diagonal source families and original tensor35 test '
                      'attain all four sharp source costs in profile51. The ordinary proof '
                      'supplies arbitrary-height bounds and convergence. These source35 '
                      'extrema do not assert attainment of complete357 tests, their '
                      'positive7 source complements, or the full K comparison. No Lean '
                      'verification or unrestricted Erdos7 resolution is claimed.')}


def encode(value):
    if isinstance(value, F):
        return str(value)
    if isinstance(value, dict):
        return {k: encode(v) for k, v in value.items()}
    if isinstance(value, (tuple, list)):
        return [encode(v) for v in value]
    return value


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    result = calculate(Path(__file__).resolve().parents[2])
    if args.output is not None:
        args.output.write_text(json.dumps(encode(result), indent=2)+'\n')
    print('PASS:12 actual-source cost integrals, exact nested-test formulas, finite carrier tails and400 baseline pairs.')
    print('The same off-diagonal construction attains g4/g5/psi5 source bounds and the sharper psi4 supremum; complete357 and Erdos7 remain open.')


if __name__ == '__main__':
    main()
