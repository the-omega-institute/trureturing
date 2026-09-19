"""Retain original 5,15,45 events with 41 globally fixed cost barriers.

The global refined margin is separately concave and dominates the preceding
margin plus the barrier increase times D. This evaluator improves six vertices
and retains certified lower bounds at every other vertex. The patched table
itself is not claimed to be concave. The consumer charges the complete H41
increase and checks every target vertex before continuous extension.
"""
from fractions import Fraction as F
from functools import lru_cache
from hashlib import sha256

SELECTED = (398, 410, 422, 616, 628, 640)
UNCHANGED_BARRIERS = (('R17', (0, 0)), ('R17', (0, 1)), ('R17', (1, 0)),
                      ('R19', (0, 0)), ('R19', (0, 1)), ('R19', (1, 0)),
                      ('R5', (0, 0)))


def require(condition, message):
    if not condition:
        raise ValueError(message)


def event_cap(dat, k, correction):
    """Keep empty shallow carriers in the signed three-event cofactor cap."""
    d, n, eta, _, _ = dat
    signed = tuple(k[j]*n[j]-correction[j]*eta[j]/5 for j in range(5))
    deep = tuple(k[j]*d[j]-correction[j]/5 for j in range(5))
    require(all(value >= kk/20 >= 0 for value, kk in zip(deep, k)),
            'Three-event floor preserves the global nonnegative deep lower bound')
    root = lambda values: max(sum(values[:2]), sum(values[2:]))
    kw = tuple(9*eta[j]*k[j] for j in range(5))
    value = max(F(0), root(signed))+max((F(0),)+signed)
    value += F(13, 243)*max(deep)+F(1, 486)*max(k[j]*d[j] for j in range(5))
    value += (sum(kw)+root(kw)+max(kw))/36+max(k)/72
    return value


def refine(source, fixed, ap, ap_inputs, rows):
    """Return certified vertex margin lower bounds and exact check statistics.

    Each original test retains its independent b and c choices. Only the actual
    forbidden-family parameters and survivor law are shared. The unchanged
    Gamma13 and T81 interfaces are owned by the caller.
    """
    inventory, groups, _ = ap.inventory(source, fixed, ap_inputs)
    specs, bases = inventory[:41], source.BASES
    require(len(inventory) == 46 and len(specs) == 41 and len(bases) == 10,
            'Complete AP45 cost and shallow-layout inventories')
    group_weights = {'R17': F(1), 'R19': source.P17, 'R5': source.EXTRA5}
    tail_weight = sum(group_weights[group['name']]*group['tail_coefficient']
                      for group in groups)
    weights = tuple(group_weights[spec['name']] for spec in specs[:40])+(tail_weight,)
    require(min(weights) > 0, 'Positive complete linear-cost weights')
    thresholds, unchanged_barriers, increases = [], [], []
    for ci, spec in enumerate(specs):
        tag, zero = spec['tag'], spec['zero']
        values = tuple(source.zero5_cost(spec['tag'], v) for v in (1, 2, 3, 4))
        increments = tuple(values[i+1]-values[i] for i in range(3))
        require(0 <= increments[0] <= increments[1] <= increments[2],
                'Nonnegative increasing low-cost increments')
        require(spec['joint'] >= values[3], 'All 41 predecessor costs admit the one-event floor')
        tag_metadata, zero_metadata = (source.zero5_cost_metadata(cost) for cost in (tag, zero))
        cutoff = max(tag_metadata[3], zero_metadata[3])
        require(tag_metadata[0] == zero_metadata[0] == 1
                and tag_metadata[1] == zero_metadata[1]
                and all(source.zero5_cost(zero, v+1)-source.zero5_cost(zero, v)
                        >= source.zero5_cost(tag, v+1)-source.zero5_cost(tag, v)
                        for v in range(1, cutoff+1)),
                'Complete affine source increments pay the original event weights')
        threshold = values[2]+3*increments[2]
        require(threshold == max(values[i]+3*increments[i] for i in range(3)),
                'Global three-event unclipped threshold')
        new_constant = max(spec['joint'], threshold)
        increase = new_constant-spec['joint']
        increases.append(increase)
        thresholds.append({'name': spec['name'], 'tuple': spec['tuple'],
                           'previous_constant': spec['joint'], 'threshold': threshold,
                           'constant': new_constant, 'increase': increase,
                           'weighted_increase': weights[ci]*increase})
        if increase == 0:
            unchanged_barriers.append(ci)
    require(tuple((specs[i]['name'], tuple(specs[i]['tuple']))
                  for i in unchanged_barriers) == UNCHANGED_BARRIERS,
            'Exactly seven unchanged and 34 raised global barriers')
    H41_increase = sum(weight*increase for weight, increase in zip(weights, increases))
    require(H41_increase > 0, 'Positive complete barrier cost charged to the consumer')

    @lru_cache(None)
    def positive(ci, eta):
        zero = specs[ci]['zero']
        degree, a, z, cutoff = source.zero5_cost_metadata(zero)
        require(degree == 1 and a >= 0 and cutoff >= 2, 'Complete affine source tail')
        psi = lambda v: source.zero5_cost(zero, v)
        x = sum(eta)
        tails = tuple(4*t for t in source.geom(5, cutoff))
        require(tails[0] >= 0 and tails[1]-2*tails[0] >= 0,
                'Nonnegative retained affine-tail coefficients')
        first = tuple(source.affine(F(0), 'id', 1, b, eta, source.ONES) for b in bases)
        raw = {n: tuple(source.zero5_scaled_pure(zero, n, b, eta) for b in bases)
               for n in range(2, cutoff)}
        constant = sum(F(4, 5**n)*psi(n) for n in range(2, cutoff))
        constant += a*tails[1]+z*tails[0]
        values = tuple(sum(F(4, 5**n)*(raw[n][li]-psi(n)*x
                           +(n-2)*(max(raw[n])-psi(n)*x))/n
                           for n in range(2, cutoff))
                       +a*tails[0]*(first[li]-x)
                       +a*(tails[1]-2*tails[0])*(max(first)-x)+constant*x
                       for li in range(10))
        rebuilt = sum(F(4*(n-1), 5**n)*(max(raw[n])-psi(n)*x)/n
                      for n in range(2, cutoff))
        rebuilt += a*(tails[1]-tails[0])*(max(first)-x)+constant*x
        require(rebuilt == source.zero5_positive_with_constant(zero, eta)
                and max(values) <= rebuilt,
                'Whole affine tail reconstructs and is dominated by the old source')
        return values

    parameters = list(source.vertices())
    require(len(rows) == len(parameters) == 1296
            and [row['index'] for row in rows] == list(range(1296)),
            'Complete ordered predecessor vertex margins')
    result = [dict(row) for row in rows]
    for row in result:
        row['M41'] += H41_increase*row['D']
    changes, digest = [], sha256()
    old_checks = new_checks = 0
    for index in SELECTED:
        dat = source.data(parameters[index])
        d, n, eta, s, D = dat
        row = rows[index]
        require((s, D) == (row['s'], row['D']) and s >= F(1, 4)
                and sum(eta) <= F(5, 9) and min(d) >= F(1, 4),
                'Same parameter and complete-domain cap-sign premises')
        cap0 = fixed._cofactor_cap(dat, source.ONES, (F(0),)*5, 5)
        require(cap0 == 5*(s-D) and cap0 >= 0,
                'Unweighted complete cofactor cap is exactly the raw mass loss')
        old_margins, new_margins, directions = [], [], []
        for ci, spec in enumerate(specs):
            tag, zero, old_C = spec['tag'], spec['zero'], spec['joint']
            increase, C = increases[ci], spec['joint']+increases[ci]
            common = source.zero7_raw(tag, dat)-source.zero5_raw(zero, dat)
            old_positive = source.zero5_positive_with_constant(zero, eta)
            old_values, new_values, labels = [], [], []
            for bi, item in enumerate(spec['layouts']):
                b = item['baseline']
                old_k, unit = item['joint']
                k = tuple(value+increase for value in old_k)
                selected = common+sum(n[j]*item['psi'][j]+eta[j]*item['correction'][j]
                                      for j in range(5))
                selected += max(source.zero5_common_deep(zero, b[j], d[j]) for j in range(5))
                old_cap = fixed._cofactor_cap(dat, old_k, unit, 5)
                old_margin = old_C*s-selected-old_positive-old_cap/5
                require(old_margin >= 0, 'Inherited original linear source margin')
                old_values.append(old_margin)
                old_checks += 1
                for li, c in enumerate(bases):
                    correction = tuple(v*t for v, t in zip(unit, c))
                    require(all(0 <= v <= corrected <= kk
                                for v, corrected, kk in zip(unit, correction, k)),
                            'Raised global barrier pays the full three-original-event floor')
                    cap = event_cap(dat, k, correction)
                    require(cap <= old_cap+increase*cap0,
                            'Three-event cap increase is paid by the exact unweighted mass loss')
                    margin = C*s-selected-positive(ci, eta)[li]-cap/5
                    require(margin >= old_margin+increase*D,
                            'Combined source and deletion dominate the fully charged barrier increase')
                    new_values.append(margin)
                    labels.append([bi, li])
                    digest.update(f'{index},{ci},{bi},{li}:{margin}\n'.encode())
                    new_checks += 1
            old_value = min(old_values)
            value = min(new_values)
            require(value > old_value+increase*D,
                    'Every direction improves beyond its fully charged inherited margin')
            old_margins.append(old_value)
            new_margins.append(value)
            directions.append({'name': spec['name'], 'tuple': spec['tuple'],
                               'weight': weights[ci], 'old_margin': old_value,
                               'inherited_margin': old_value+increase*D,
                               'new_margin': value, 'constant': C,
                               'previous_constant': old_C, 'constant_increase': increase,
                               'minimizers': [label for label, margin in zip(labels, new_values)
                                              if margin == value]})
        old_total = sum(w*m for w, m in zip(weights, old_margins))
        new_total = sum(w*m for w, m in zip(weights, new_margins))
        inherited_total = old_total+H41_increase*D
        require(old_total == row['M41'] and new_total > inherited_total,
                'Exact predecessor reconstruction and strict selected-vertex improvement')
        result[index]['M41'] = new_total
        changes.append({'index': index, 'previous_M41': old_total,
                        'inherited_M41': inherited_total,
                        'refined_M41': new_total, 'net_gain': new_total-inherited_total,
                        'directions': directions})
    require(old_checks == 2460 and new_checks == 24600, 'Exact selected-vertex work counts')
    return result, {'refined_directions': 41, 'unclipped_directions': 41,
                    'raised_barriers': 34, 'unchanged_barriers': 7,
                    'unchanged_one_event_directions': 0, 'H41_increase': H41_increase,
                    'updated_vertices': list(SELECTED), 'inherited_vertices': 1290,
                    'predecessor_layout_checks': old_checks,
                    'refined_layout_checks': new_checks,
                    'linear_tail_weight': tail_weight, 'thresholds': thresholds,
                    'changes': changes, 'margin_sha256': digest.hexdigest(),
                    'vertex_table_semantics': 'M41 is a vertex lower bound for one globally defined separately concave 41-direction refinement at globally fixed raised barriers. Inherited rows use old M41 plus H41_increase times D; no concavity claim is made for the patched table itself.',
                    'consumer_obligation': 'Add H41_increase to the complete H41 cost, check the final target at all 1296 returned rows and its nonnegative D coefficient, then apply separate concavity to the global refined margin. Eight missing-class branches remain separate.'}
