#!/usr/bin/env python3
"""Exact premises for sharp source35 costs at every real threshold T >= 5.

The ordinary proof in profile52 supplies the unbounded quantifier through
primitive-hinge positivity, affinity on unit intervals and a geometric
tail estimate. This standard-library checker reconstructs its finite
rational premises using complete geometric tails, not depth truncation.
Read-only by default; --output writes an exact rational JSON result.
"""
import argparse
from fractions import Fraction as F
from hashlib import sha256
import importlib.util
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
PINS = {
    'frontier/source-budgets/source_cost_endpoint_attainment.py':
        '860816267cfc11da898d207f1eb48486c6630d1dd3d00a785417a244188af47d',
}
WITNESS = (9, 4)


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


def branch_values(source, tag, dat):
    """All fixed-baseline/deep-cell zero5 costs, including exact tails."""
    d, n, eta, _, _ = dat
    result = {}
    for bi, b in enumerate(source.BASES):
        initial = sum(n[l]*source.zero5_cost(tag, b[l])
                      + eta[l]*source.zero5_centered_correction(tag, b[l])
                      for l in range(5))
        for j in range(5):
            result[bi, j] = initial+source.zero5_common_deep(tag, b[j], d[j])
    require(len(result) == 50, 'Ten distinct baselines by five deep cells')
    return result


def branch_gaps(source, tag, dat):
    values = branch_values(source, tag, dat)
    return {key: values[WITNESS]-value for key, value in values.items()}


def branch_record(values):
    return [{'baseline': b, 'deep_cell': j, 'gap': value}
            for (b, j), value in sorted(values.items())]


def calculate(base):
    parent = load(base, 'frontier/source-budgets/source_cost_endpoint_attainment.py',
                  'spectrum_source_attainment')
    source = parent.load(base, 'verify_joint_frontier.py', 'spectrum_source')
    full = parent.load(base, 'frontier/moments-survival/full_absorbed_survival_hinges.py',
                       'spectrum_full')
    # Validate the complete parent dependency identity, including its actual
    # source constructor. No constructor experiment is repeated here.
    for path, pin in parent.PINS.items():
        require(sha256((base/path).read_bytes()).hexdigest() == pin,
                'Parent source pin: '+path)
    parameters = list(source.vertices())
    require(len(parameters) == 1296, 'Inherited ordered parameter vertices')
    dat = source.data(parameters[404])
    d, n, eta, s, D = dat
    require(d == (F(3, 4), F(3, 4), F(1, 4), F(1, 2), F(1, 2))
            and n == (F(1, 24), F(1, 12), F(1, 36), F(1, 24), F(1, 18))
            and eta == (F(1, 18), F(1, 9), F(1, 9), F(1, 9), F(1, 9))
            and (s, D) == (F(1, 4), F(3, 20)), 'Exact theta404 source data')
    require(source.ROOT == (0, 0, 1, 1, 1)
            and source.BASES[9] == (1, 1, 2, 2, 3)
            and len(set(source.BASES)) == 10, 'Inherited shallow geometry')
    require(sum(eta[:2]) == F(1, 6) and sum(eta[2:]) == F(1, 3)
            and eta[4] == max(eta) == F(1, 9), 'Common pure-cost maximizer geometry')
    require(d[4]-F(1, 5) == F(3, 10)
            and max(d)-F(1, 5) == F(11, 20)
            and 3*(d[4]-F(1, 5)) >= max(d)-F(1, 5),
            'Primitive deep domination when competitor baseline is at most two')

    low = {u: branch_gaps(source, ('h', F(u)), dat) for u in range(6)}
    branches = set(low[0])
    bad = sorted(key for key in branches if min(low[u][key] for u in range(4)) < 0)
    expected_bad = [(1, j) for j in range(5)]+[(4, 0), (4, 1)]
    expected_bad += [(6, j) for j in range(5)]+[(9, 0), (9, 1)]
    require(bad == expected_bad, 'Exact fourteen possibly negative primitive branches')
    require(min(low[u][key] for u in range(4) for key in branches) == -F(1, 24),
            'Primitive lower floor on the initial unit intervals')
    require(all(low[u][key] >= 0 for u in range(4) for key in branches if key not in bad),
            'All remaining branches nonnegative below threshold three')
    minima = {u: min(low[u][key] for key in bad) for u in low}
    require(tuple(minima.values()) == (-F(1, 24), -F(1, 24), -F(1, 120),
                                       F(11, 1800), F(7, 27000), F(527, 405000)),
            'Complete rational primitive endpoint minima')
    positive_buffer = min(minima[u] for u in (3, 4, 5))
    require(positive_buffer == F(7, 27000), 'Uniform positive buffer on [3,5]')

    recurrence_base = []
    for u in (3, 4, 5):
        tag = ('h', F(u))
        Q2 = source.zero5_centered_correction(tag, 2)+source.zero5_cost(tag, 2)/5
        D3 = source.zero5_convex_pure_deep(tag, 1, 3)
        require(Q2 >= F(3, 2)*D3, 'Primitive Q/deep inequality at '+str(u))
        require(D3 == 3*source.zero5_convex_pure_deep(tag, 1, 2)
                == 9*source.zero5_convex_pure_deep(tag, 1, 1),
                'Deep shift identities at the recurrence base')
        require(low[u][1, 1] == Q2/6-D3/4,
                'Exact exceptional root-zero branch difference')
        recurrence_base.append({'u': u, 'Q2': Q2, 'D3': D3,
                                'difference': Q2-F(3, 2)*D3})
    require([row['Q2'] for row in recurrence_base] ==
            [F(3, 25), F(11, 375), F(32, 1875)], 'Exact Q recurrence values')
    require([row['D3'] for row in recurrence_base] ==
            [F(1, 18), F(1, 54), F(1, 162)], 'Exact deep recurrence values')
    require(F(2, 15)/F(1, 9) == F(6, 5) > 1, 'Strict shift-two ratio improvement')

    initial = []
    crosschecks = []
    for threshold in range(5, 22):
        tag = ('seven_block', (('h', F(threshold)), 0))
        gaps = branch_gaps(source, tag, dat)
        require(all(value >= 0 for value in gaps.values()),
                'All fifty source branches at threshold '+str(threshold))
        initial.append({'T': threshold,
                        'minimum_nonwitness_gap': min(v for k, v in gaps.items() if k != WITNESS),
                        'gaps': branch_record(gaps)})
        if threshold in (5, 12, 21):
            # A distinct exact implementation and the explicit original
            # tensor integral check the branch-to-envelope identification.
            cost = full.CellCost(source, F(threshold), F(0))
            weights = (0,)*5
            direct = parent.limiting_integral(source, cost, weights, dat)
            old, controllers = cost.operator(weights, dat)
            canonical = source.zero5_raw(tag, dat)
            require(direct == old == canonical,
                    'Actual tensor integral reaches the source envelope at '+str(threshold))
            crosschecks.append({'T': threshold, 'actual_integral': direct,
                                'envelope': old, 'maximizing_baselines': controllers})

    tail_to_term = (F(6, 5)*F(1, 7**7))/source.zero7_probability(5)
    require(tail_to_term == F(1, 294), 'Geometric seven-tail to selected-term ratio')
    tail_buffer = positive_buffer-F(1, 24)*tail_to_term
    require(tail_buffer == F(311, 2646000) > 0,
            'One selected positive seven term dominates every negative tail term')
    return {
        'schema': 'erdos7-sharp-source-stoploss-spectrum-v1',
        'source_vertex': 404, 'source_sha256': {**PINS, **parent.PINS},
        'witness_baseline': 9, 'witness_deep_cell': 4,
        'bad_primitive_branches': bad,
        'primitive_minima': minima,
        'primitive_endpoint_gaps': {u: branch_record(row) for u, row in low.items()},
        'primitive_recurrence_base': recurrence_base,
        'initial_integer_threshold_checks': initial,
        'actual_tensor_crosschecks': crosschecks,
        'uniform_tail_buffer': tail_buffer,
        'counts': {'primitive_endpoint_branches': 300,
                   'initial_threshold_branches': 850, 'actual_tensor_crosschecks': 3},
        'scope': ('Finite exact premises for profile52: the same actual off-diagonal '
                  'source/test sequence attains the scalar source35 envelope for every '
                  'real T >= 5. The ordinary proof supplies the unbounded quantifier '
                  'and convergence. This is not a complete357 or final K extremum, '
                  'a Lean verification, or a resolution of unrestricted Erdos #7.'),
    }


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
    parser.add_argument('--base', type=Path, default=Path(__file__).resolve().parents[2],
                        help='Report root containing the pinned source helpers')
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    result = calculate(args.base)
    if args.output is not None:
        args.output.write_text(json.dumps(encode(result), indent=2)+'\n')
    print('PASS:300 primitive endpoint branches,850 initial threshold branches,3 actual tensor crosschecks.')
    print('Exact recurrence premises and tail buffer311/2646000 support the ordinary proof for all real T>=5.')
    print('Scope:scalar source35 costs; complete357 and unrestricted Erdos7 remain open.')


if __name__ == '__main__':
    main()
