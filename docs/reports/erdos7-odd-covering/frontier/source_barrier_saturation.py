#!/usr/bin/env python3
"""Compute exact saturation of the current 47 source comparison barriers.

Python3.9+ standard library. Default is read-only; --output writes the computed
exact JSON. The result bounds this fixed relaxation at its six control points,
not an actual covering family. It does not regenerate the profile39 certificate
or claim a new complete-domain upper certificate.
"""
from fractions import Fraction as F
from functools import lru_cache
from hashlib import sha256
from pathlib import Path
import argparse
import importlib.util
import json
import sys

sys.dont_write_bytecode = True
SELECTED = (398, 410, 422, 616, 628, 640)
CERTIFICATE = 'certificates/source_norms/shared_source_deficits.json'


def require(condition, message):
    if not condition:
        raise ValueError(message)


def encode(value):
    if isinstance(value, F):
        return str(value)
    if isinstance(value, dict):
        return {str(k): encode(v) for k, v in value.items()}
    if isinstance(value, (tuple, list)):
        return [encode(v) for v in value]
    return value


def unique(pairs):
    result = {}
    for key, value in pairs:
        require(key not in result, 'Duplicate JSON key: '+key)
        result[key] = value
    return result


def module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    require(spec is not None and spec.loader is not None, 'Loadable source: '+str(path))
    result = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(result)
    return result


def hull(lines):
    """Exact upper hull of affine lines; None means the first unbounded interval."""
    by_slope = {}
    for a, b in lines:
        by_slope[a] = max(b, by_slope.get(a, b))
    result = []
    for a, b in sorted(by_slope.items()):
        start = None
        while result:
            old_a, old_b, old_start = result[-1]
            start = (old_b-b)/(a-old_a)
            if old_start is None or start > old_start:
                break
            result.pop()
        result.append((a, b, start if result else None))
    return tuple(result)


def active(lines, constant):
    return next((a, b) for a, b, start in reversed(lines)
                if start is None or start <= constant)


def value(terms, constant):
    return sum(weight*max(a*constant+b for a, b, _ in lines)
               for weight, lines in terms)


def intercept(terms):
    return sum(weight*lines[-1][1] for weight, lines in terms)


def slope(terms, constant):
    return sum(weight*active(lines, constant)[0] for weight, lines in terms)


def cap_terms(dat, costs, correction, cofactor_count=5):
    require(cofactor_count in (5, 6), 'Five or six paid pure3 cofactors')
    selected, tail_coefficient = ((F(13, 243), F(1, 486)) if cofactor_count == 5
                                  else (F(40, 729), F(1, 1458)))
    require(selected+tail_coefficient == F(1, 18), 'Complete deep cofactor mass')
    d, n, eta, s, D = dat
    widths = tuple(9*x for x in eta)
    signed = [(n[j], -costs[j]*n[j]-correction[j]*eta[j]/5) for j in range(5)]
    deep = [(d[j], -costs[j]*d[j]-correction[j]/5) for j in range(5)]
    tail = [(d[j], -costs[j]*d[j]) for j in range(5)]
    weighted = [(widths[j], -costs[j]*widths[j]) for j in range(5)]

    def root(lines):
        return [(sum(a for a, b in part), sum(b for a, b in part))
                for part in (lines[:2], lines[2:])]

    summed = [(sum(a for a, b in weighted), sum(b for a, b in weighted))]
    terms = ((F(1), hull([(F(0), F(0))]+root(signed))),
             (F(1), hull([(F(0), F(0))]+signed)),
             (selected, hull(deep)), (tail_coefficient, hull(tail)),
             (F(1, 36), hull(summed)), (F(1, 36), hull(root(weighted))),
             (F(1, 36), hull(weighted)), (F(1, 72), hull([(F(1), -v) for v in costs])))
    require(sum(weight*lines[-1][0] for weight, lines in terms) == 5*(s-D),
            'Every branch eventual slope is exactly the complete mass-loss cap')
    return terms


def crossing(raw, terms, loss, start, target):
    """First C>=start with raw+W(C)/5-C*loss<=target, using exact hull intervals."""
    current = start
    breaks = sorted({x for weight, lines in terms for a, b, x in lines
                     if x is not None and x > start})
    for end in breaks+[None]:
        current_value = raw+value(terms, current)/5-current*loss
        if current_value <= target:
            return current
        derivative = slope(terms, current)/5-loss
        require(derivative <= 0, 'Every fully charged branch is nonincreasing')
        if derivative < 0:
            candidate = current+(current_value-target)/(-derivative)
            if end is None or candidate <= end:
                return candidate
        require(end is not None, 'Every branch reaches its finite asymptote')
        current = end
    raise ValueError('No branch crossing')


class Experiment:
    def __init__(self, base):
        self.base = base
        io = module('barrier_saturation_io', base/'certificate_io.py')
        self.io = io
        raw = io.read_artifact_bytes(base/CERTIFICATE)
        self.previous = json.loads(raw, object_pairs_hook=unique)
        require(self.previous['schema'] == 'erdos7-shared-source-deficits-v1', 'Current source certificate')
        pins = self.previous['source_sha256'] | self.previous['helper_sha256']
        for name, pin in pins.items():
            require(sha256(io.read_artifact_bytes(base/name)).hexdigest() == pin,
                    'Current direct source pin: '+name)
        self.pins = pins | {CERTIFICATE: sha256(raw).hexdigest()}
        self.source = module('barrier_saturation_source', base/'verify_joint_frontier.py')
        self.fixed = module('barrier_saturation_fixed', base/'frontier/fixed_cost.py')
        ap = module('barrier_saturation_ap', base/'frontier/ap_schedule.py')
        self.linear = module('barrier_saturation_linear', base/'frontier/shared_linear_refinement.py')
        inputs = json.loads(io.read_artifact_bytes(base/'certificates/ap_schedule_norms.json'),
                            object_pairs_hook=unique)
        inventory, groups, _ = ap.inventory(self.source, self.fixed, inputs)
        self.specs = inventory[:41]
        self.quadratic_specs = inventory[41:]
        self.outside = F(self.previous['source_profiles']['quadratic_tail_weight'])
        self.layout = module('source_saturation_layout', base/'frontier/layout_gap.py')
        quadratic_inputs = json.loads(io.read_artifact_bytes(base/'certificates/source_norms/retained_quadratic_inputs.json'), object_pairs_hook=unique)
        norm_record = json.loads(io.read_artifact_bytes(base/'certificates/source_norms/retained_quadratic_tests.json'), object_pairs_hook=unique)
        self.quadratic_constants = tuple(F(row['constant']) for row in quadratic_inputs['constants'])
        self.pairs = ((0, 0), (0, 1), (0, 2), (1, 0), (2, 0))
        require(tuple(tuple(row['tuple']) for row in quadratic_inputs['constants']) == self.pairs
                and self.quadratic_constants == tuple(F(row['C']) for row in norm_record['norms']),
                'Five exact quadratic costs and published constants')
        self.psis = tuple(ap.psi_record(self.source, self.layout, pair) for pair in self.pairs)
        group_weights = {'R17': F(1), 'R19': self.source.P17, 'R5': self.source.EXTRA5}
        tail_weight = sum(group_weights[g['name']]*g['tail_coefficient'] for g in groups)
        self.weights = tuple(group_weights[s['name']] for s in self.specs[:40])+(tail_weight,)
        require(len(inventory) == 46 and len(self.weights) == 41 and min(self.weights) > 0,
                'Complete positive AP cost inventory')
        self.parameters = list(self.source.vertices())
        self.changes = {row['index']: row for row in self.previous['linear_refinement']['changes']}
        self.squares = {row['index']: row for row in self.previous['square_barrier_refinement']['changes']}
        require(tuple(self.changes) == tuple(self.squares) == SELECTED
                and self.previous['square_barrier_refinement']['source_barrier'] == '45',
                'Same six controls and fixed square barrier45')
        self.thresholds = self.previous['linear_refinement']['thresholds']
        require(len(self.thresholds) == 41, 'Complete published linear thresholds')
        for spec, threshold, weight in zip(self.specs, self.thresholds, self.weights):
            values = [self.source.zero5_cost(spec['tag'], v) for v in (1, 2, 3, 4)]
            expected = max(spec['joint'], max(values[j]+3*(values[j+1]-values[j]) for j in range(3)))
            require(F(threshold['constant']) == expected and threshold['name'] == spec['name']
                    and threshold['tuple'] == spec['tuple'], 'Exact current cost and threshold')
        require(self.previous['maximizers']['bound'] == list(SELECTED)
                and self.previous['maximizers']['combined'] == list(SELECTED),
                'All selected rows control the currently published J and K')

    @lru_cache(None)
    def positive(self, ci, eta):
        source = self.source
        zero = self.specs[ci]['zero']
        degree, a, z, cutoff = source.zero5_cost_metadata(zero)
        require(degree == 1 and a >= 0 and cutoff >= 2, 'Complete eventually affine source tail')
        psi = lambda v: source.zero5_cost(zero, v)
        x = sum(eta)
        tails = tuple(4*t for t in source.geom(5, cutoff))
        first = tuple(source.affine(F(0), 'id', 1, b, eta, source.ONES) for b in source.BASES)
        raw = {n: tuple(source.zero5_scaled_pure(zero, n, b, eta) for b in source.BASES)
               for n in range(2, cutoff)}
        constant = sum(F(4, 5**n)*psi(n) for n in range(2, cutoff))+a*tails[1]+z*tails[0]
        values = tuple(sum(F(4, 5**n)*(raw[n][li]-psi(n)*x
                           +(n-2)*(max(raw[n])-psi(n)*x))/n for n in range(2, cutoff))
                       +a*tails[0]*(first[li]-x)
                       +a*(tails[1]-2*tails[0])*(max(first)-x)+constant*x for li in range(10))
        rebuilt = sum(F(4*(n-1), 5**n)*(max(raw[n])-psi(n)*x)/n for n in range(2, cutoff))
        rebuilt += a*(tails[1]-tails[0])*(max(first)-x)+constant*x
        require(rebuilt == source.zero5_positive_with_constant(zero, eta) and max(values) <= rebuilt,
                'All positive5 source tails retained exactly')
        return values

    def linear_direction(self, index, ci, proposed=None):
        source = self.source
        dat = source.data(self.parameters[index])
        d, n, eta, s, D = dat
        spec, start = self.specs[ci], F(self.thresholds[ci]['constant'])
        zero, tag = spec['zero'], spec['tag']
        common = source.zero7_raw(tag, dat)-source.zero5_raw(zero, dat)
        positives = self.positive(ci, eta)
        branches = []
        for bi, layout in enumerate(spec['layouts']):
            b = layout['baseline']
            costs = tuple(source.zero5_cost(tag, v) for v in b)
            unit = layout['joint'][1]
            base = common+sum(n[j]*layout['psi'][j]+eta[j]*layout['correction'][j] for j in range(5))
            base += max(source.zero5_common_deep(zero, b[j], d[j]) for j in range(5))
            for li, c in enumerate(source.BASES):
                correction = tuple(v*t for v, t in zip(unit, c))
                terms = cap_terms(dat, costs, correction)
                raw = base+positives[li]
                k = tuple(start-v for v in costs)
                require(value(terms, start) == self.linear.event_cap(dat, k, correction),
                        'Affine hull reproduces the current empty-safe event cap')
                branches.append((bi, li, raw, terms, raw+intercept(terms)/5,
                                 raw+value(terms, start)/5-start*(s-D)))
        require(len(branches) == 100, 'All independent original layout pairs')
        limit = max(branch[4] for branch in branches)
        initial = max(branch[5] for branch in branches)
        published = self.changes[index]['directions'][ci]
        require(published['name'] == spec['name'] and published['tuple'] == spec['tuple']
                and F(published['weight']) == self.weights[ci]
                and F(published['constant']) == start
                and start*D-initial == F(published['new_margin']),
                'Exact reconstruction of each profile39 source margin')
        star = max(crossing(raw, terms, s-D, start, limit)
                   for bi, li, raw, terms, low, old in branches)
        at = lambda C: max(raw+value(terms, C)/5-C*(s-D)
                           for bi, li, raw, terms, low, old in branches)
        require(at(star) == limit and star >= start,
                'Reported constant exactly reaches the full independent-layout envelope limit')
        if star > start:
            require(at((star+start)/2) > limit, 'Strict decrease before the least saturation point')
        else:
            require(initial == limit, 'Already saturated threshold')
        if proposed is not None:
            require(proposed == star and at(proposed) == limit,
                    'One globally fixed constant is least and saturated at all six controls')
        weight = self.weights[ci]
        return {'index': ci, 'name': spec['name'], 'tuple': spec['tuple'], 'weight': weight,
                'current_constant': start, 'saturation_constant': star,
                'constant_increase': star-start, 'weighted_budget': weight*(star-start),
                'current_fully_charged_cost': initial, 'limiting_fully_charged_cost': limit,
                'weighted_raw_gain': weight*(initial-limit), 'already_saturated': initial == limit,
                'limit_controllers': [[bi, li] for bi, li, raw, terms, low, old in branches if low == limit]}



    @staticmethod
    def distance(eta, b, c):
        delta = tuple(x-y for x, y in zip(b, c))
        return sum(w*v*v for w, v in zip(eta, delta)) - (
            max((0,)+delta)**2+max((0,)+tuple(-v for v in delta))**2)/F(18)

    @lru_cache(None)
    def quadratic_positive(self, ci, eta):
        source = self.source
        zero, psi, _, _, _ = self.psis[ci]
        degree, a, z, cutoff = source.zero5_cost_metadata(zero)
        require(degree == 2 and cutoff >= 2, 'Complete quadratic source tail')
        x = sum(eta)
        tails = tuple(4*t for t in source.geom(5, cutoff))
        squares = tuple(source.sq_value(F(0), b, eta, source.ONES) for b in source.BASES)
        raw = {n: tuple(source.zero5_scaled_pure(zero, n, b, eta) for b in source.BASES)
               for n in range(2, cutoff)}
        constant = sum(F(4, 5**n)*psi(n) for n in range(2, cutoff))+a*tails[2]+z*tails[0]
        result = tuple(sum(F(4, 5**n)*(raw[n][li]-psi(n)*x
                           +(n-2)*(max(raw[n])-psi(n)*x))/n for n in range(2, cutoff))
                       +a*tails[1]*(squares[li]-x)
                       +a*(tails[2]-2*tails[1])*(max(squares)-x)+constant*x for li in range(10))
        rebuilt = sum(F(4*(n-1), 5**n)*(max(raw[n])-psi(n)*x)/n for n in range(2, cutoff))
        rebuilt += a*(tails[2]-tails[1])*(max(squares)-x)+constant*x
        require(rebuilt == source.zero5_positive_with_constant(zero, eta) and max(result) <= rebuilt,
                'Complete quadratic geometric tail reconstructs the source comparison')
        return result

    @staticmethod
    def settle(dat, start, branches, proposed):
        s, D = dat[3:]
        require(len(branches) == 100, 'All independent original layout pairs')
        limit = max(branch[4] for branch in branches)
        initial = max(branch[5] for branch in branches)
        star = max(crossing(raw, terms, s-D, start, limit)
                   for bi, li, raw, terms, low, old in branches)
        at = lambda C: max(raw+value(terms, C)/5-C*(s-D)
                           for bi, li, raw, terms, low, old in branches)
        require(at(star) == limit and star >= start, 'Exact least branch-envelope saturation point')
        if star > start:
            require(at((star+start)/2) > limit, 'Strict remaining gain before saturation')
        else:
            require(initial == limit, 'Current barrier already saturated')
        if proposed is not None:
            require(proposed == star and at(proposed) == limit,
                    'Same globally fixed constant saturates every selected parameter')
        return {'current_constant': start, 'saturation_constant': star,
                'constant_increase': star-start, 'current_margin': start*D-initial,
                'current_fully_charged_cost': initial, 'limiting_fully_charged_cost': limit,
                'raw_gain': initial-limit, 'already_saturated': initial == limit,
                'limit_controllers': [[bi, li] for bi, li, raw, terms, low, old in branches if low == limit]}

    def quadratic_direction(self, index, ci, proposed=None):
        source = self.source
        dat = source.data(self.parameters[index])
        d, n, eta, s, D = dat
        start, spec = self.quadratic_constants[ci], self.quadratic_specs[ci]
        zero, psi, curve, _, _ = self.psis[ci]
        tag = spec['tag']
        common = source.zero7_raw(tag, dat)-source.zero5_raw(zero, dat)
        positives = self.quadratic_positive(ci, eta)
        branches = []
        for bi, b in enumerate(source.BASES):
            costs = tuple(source.zero5_cost(tag, v) for v in b)
            increments = tuple(source.zero5_cost(tag, v+1)-source.zero5_cost(tag, v) for v in b)
            baseline = sum(n[j]*psi(b[j])+eta[j]*source.zero5_centered_correction(zero, b[j])
                           for j in range(5))
            baseline += max(source.zero5_common_deep(zero, b[j], d[j]) for j in range(5))
            for li, c in enumerate(source.BASES):
                correction = tuple(v*t for v, t in zip(increments, c))
                k = tuple(start-v for v in costs)
                require(all(0 <= v <= kk for v, kk in zip(correction, k)),
                        'Every full three-event quadratic floor')
                terms = cap_terms(dat, costs, correction, 6)
                raw = common+baseline+positives[li]-F(4, 25)*curve*self.distance(eta, b, c)
                cap = self.fixed._cofactor_cap(dat, k, correction, 6)
                require(value(terms, start) == cap, 'Exact six-cofactor quadratic cap reconstruction')
                branches.append((bi, li, raw, terms, raw+intercept(terms)/5,
                                 raw+cap/5-start*(s-D)))
        result = self.settle(dat, start, branches, proposed)
        require(result['current_margin'] >= 0, 'Nonnegative retained quadratic margin')
        return {'index': ci, 'tuple': self.pairs[ci], 'kind': 'quadratic', **result}

    def square_direction(self, index, proposed=None):
        source = self.source
        dat = source.data(self.parameters[index])
        d, n, eta, s, D = dat
        start = F(45)
        pure = tuple(sum(w*x*x for w, x in zip(eta, b))+max(F(x+1, 9) for x in b)
                     for b in source.BASES)
        base = tuple(sum((mass+w/4)*x*x for mass, w, x in zip(n, eta, b))
                     +max((a+F(1, 4))*F(x+1, 9) for a, x in zip(d, b)) for b in source.BASES)
        global35 = max(base)+F(5, 8)*max(pure)
        branches = []
        for bi, b in enumerate(source.BASES):
            costs = tuple(F(x*x) for x in b)
            for ci, c in enumerate(source.BASES):
                correction = tuple(F((2*x+1)*y) for x, y in zip(b, c))
                terms = cap_terms(dat, costs, correction, 6)
                selected = base[bi]+F(9, 20)*pure[ci]+F(7, 40)*max(pure)
                selected -= F(4, 25)*self.distance(eta, b, c)
                raw = F(6, 5)*selected+F(7, 15)*global35
                cap = self.fixed._cofactor_cap(dat, tuple(start-v for v in costs), correction, 6)
                require(value(terms, start) == cap, 'Exact source-square six-cofactor cap')
                branches.append((bi, ci, raw, terms, raw+intercept(terms)/5,
                                 raw+cap/5-start*(s-D)))
        result = self.settle(dat, start, branches, proposed)
        require(result['current_margin'] == F(self.squares[index]['refined_source_margin'])
                and result['already_saturated'], 'Published square45 margin already at exact envelope limit')
        return {'kind': 'square', **result}

    def run(self):
        previous, source = self.previous, self.source
        rows, constants = [], None
        old_J, old_K = F(previous['bound']), F(previous['combined'])
        q0 = F(919, 924)
        for index in SELECTED:
            linear = [self.linear_direction(index, ci, None if constants is None else constants[ci])
                      for ci in range(41)]
            quadratic = [self.quadratic_direction(index, ci, None if constants is None else constants[41+ci])
                         for ci in range(5)]
            square = self.square_direction(index, None if constants is None else constants[46])
            if constants is None:
                constants = tuple(row['saturation_constant'] for row in linear+quadratic+[square])
            dat = source.data(self.parameters[index])
            D = dat[4]
            delta = q0*D-source.raw357(F(4), dat)/6-F(4, 33)*source.raw357(F(5), dat)
            delta -= source.raw357(F(5, 2), dat)/22
            require(delta > 0, 'Actual AP survival denominator')
            linear_gain = sum(row['weighted_raw_gain'] for row in linear)
            quadratic_gain = sum(row['raw_gain'] for row in quadratic)
            linear_budget = sum(row['weighted_budget'] for row in linear)
            quadratic_budget = sum(row['constant_increase'] for row in quadratic)
            require(square['raw_gain'] == square['constant_increase'] == 0,
                    'Raising square45 has no further benefit at any of the six controls')
            old_Mquad = sum(row['current_margin'] for row in quadratic)+self.outside*square['current_margin']
            require(old_Mquad == F(self.squares[index]['refined_Mquad']),
                    'All five independent quadratic margins reconstruct the complete published Mquad')
            old_M41 = sum(row['weight']*(row['current_constant']*D-row['current_fully_charged_cost'])
                          for row in linear)
            require(old_M41 == F(self.changes[index]['refined_M41']),
                    'All41 independent margins reconstruct the complete published M41')
            H = source.AC*F(previous['H16'])+F(previous['H41'])
            require(old_J == source.WHOLE_CONST+(H*D-source.AC*old_Mquad-old_M41)/delta,
                    'Same-source J reconstructed at each published control')
            finite81, _ = source.ap_product_distribution(((11, F(5, 3)), (13, F(12, 7))), 9)
            raw81 = sum(prob*n*n*source.square357(F(81, n*n), dat)
                        for n, prob in finite81.items() if n < 7)
            t81 = (F(previous['A81'])*D+raw81-F(previous['cG'])*square['current_margin'])/delta
            require(old_K == old_J+t81, 'Same-source combined K reconstructed at every control')
            gain = linear_gain+source.AC*quadratic_gain
            budget = linear_budget+source.AC*quadratic_budget
            joint, combined = old_J-gain/delta, old_K-gain/delta
            coefficients = {key: F(v) for key, v in previous['coefficients'].items()}
            for key in ('bound', 'combined'):
                coefficients[key] -= budget+q0*gain/delta
            coefficients['Gamma13'] -= quadratic_budget+q0*quadratic_gain/delta
            require(min(coefficients.values()) > 0, 'All four fixed-target endpoint coefficients remain positive')
            rows.append({'index': index, 'D': D, 'Delta': delta, 'bound': joint, 'combined': combined,
                         'bound_gain': gain/delta, 'weighted_raw_gain': gain,
                         'linear_bound_gain': linear_gain/delta,
                         'quadratic_bound_gain': source.AC*quadratic_gain/delta,
                         'additional_H41': linear_budget, 'additional_H16': quadratic_budget,
                         'additional_weighted_H': budget, 'coefficients': coefficients,
                         'linear_directions': linear, 'quadratic_directions': quadratic,
                         'square_direction': square})
        require(all(row['bound'] == rows[0]['bound'] and row['combined'] == rows[0]['combined']
                    and row['additional_weighted_H'] == rows[0]['additional_weighted_H']
                    and row['weighted_raw_gain'] == rows[0]['weighted_raw_gain'] for row in rows),
                'Identical six-control limits with a single47-barrier vector')
        first = rows[0]
        require(first['bound_gain'] < F(1) and first['combined'] > 528,
                'Constant tuning leaves the fixed relaxation far above403')
        return {'schema': 'erdos7-source-barrier-saturation-experiment-v1',
                'initial_square_barrier': F(45), 'square45_already_saturated': True,
                'control_points': list(SELECTED), 'directions': 47, 'original_layout_checks': 28200,
                'already_saturated_linear_directions': sum(r['already_saturated'] for r in first['linear_directions']),
                'already_saturated_quadratic_directions': sum(r['already_saturated'] for r in first['quadratic_directions']),
                'additional_H41': first['additional_H41'], 'additional_H16': first['additional_H16'],
                'additional_weighted_H': first['additional_weighted_H'],
                'linear_bound_gain_limit': first['linear_bound_gain'],
                'quadratic_bound_gain_limit': first['quadratic_bound_gain'],
                'weighted_raw_gain_limit': first['weighted_raw_gain'],
                'additional_bound_gain_limit': first['bound_gain'],
                'additional_bound_gain_decimal': float(first['bound_gain']),
                'control_bound_limit': first['bound'], 'control_bound_limit_decimal': float(first['bound']),
                'control_combined_limit': first['combined'],
                'control_combined_limit_decimal': float(first['combined']),
                'remaining_before_core_error': first['combined']-403,
                'saturation_constants': constants, 'rows': rows, 'source_sha256': self.pins,
                'experiment_sha256': sha256(Path(__file__).read_bytes()).hexdigest(),
                'scope': 'Exact saturation of all47 comparison constants increased above their current profile39 values. All comparison formulas, independent layouts and full tails fixed. One vector attains all six control limits; square45 is already saturated. No actual-family lower bound, full1296 new upper certificate, fallback replay, Lean result, Erdos counterexample or unrestricted solution.'}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, help='Optional path for the complete exact JSON result')
    args = parser.parse_args()
    result = Experiment(Path(__file__).resolve().parent.parent).run()
    if args.output is not None:
        args.output.write_text(json.dumps(encode(result), indent=2)+'\n')
    summary = {k: v for k, v in result.items() if k not in ('rows', 'saturation_constants', 'source_sha256')}
    print(json.dumps(encode(summary), indent=2))


if __name__ == '__main__':
    try:
        main()
    except (ValueError, ArithmeticError, OSError, KeyError, TypeError, json.JSONDecodeError) as error:
        print('FAIL: '+str(error), file=sys.stderr)
        sys.exit(1)
