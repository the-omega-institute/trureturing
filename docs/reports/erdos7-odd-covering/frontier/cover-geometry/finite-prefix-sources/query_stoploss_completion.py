"""Complete-query stop-loss bounds from the pinned basic anchor certificate.

Only cached geometry values and exact geometric remainders are consumed.
No geometry enumeration or source producer is run. The same fixed threshold
is used at every continuous anchor vertex. Checks remain active under -O.
"""
from argparse import ArgumentParser
from collections import defaultdict
from fractions import Fraction as F
from functools import lru_cache
from hashlib import sha256
from importlib.util import module_from_spec, spec_from_file_location
from math import ceil, prod
from pathlib import Path
import json


THRESHOLDS = (1, 2, 4, 8, 12)
PINS = {
    'six_prime_prefix_certificate.json': 'ecdeb6246626c101b7bb16130366a7d22bf8d71775d5f28997b85e74c796ee61',
    'six_prime_prefix_geometry.json': '0f65a963f617867e87021c695a5ded8ad18cb1217857c0bbc7d49652b0f5fdd1',
    'six_prime_prefix_certificate.py': '3077f18fd91bf8f3a45483690b5f2d1386f1f692dccd9a453c43c99a8746daf4',
}
EIGHT_CORE_CASES = (
    (11, (7, 13, 17, 19, 23, 29), 8, 14, F(10237584019, 168750000000)),
    (13, (7, 11, 17, 19, 23, 29), 8, 18, F(13939935091, 337500000000)),
    (17, (7, 11, 13, 19, 23, 29), 16, 27, F(12314552263, 675000000000)),
    (19, (7, 11, 13, 17, 23, 29), 24, 36, F(290064917, 30000000000)),
)


def require(condition, message):
    if not condition:
        raise ValueError(message)


def pinned(directory, name):
    raw = (directory / name).read_bytes()
    require(sha256(raw).hexdigest() == PINS[name], 'pinned input: ' + name)
    return raw


def anchor_hinge_upper(threshold, mass, whole, hinges):
    """Safe envelope at any ratio, retaining convexity in anchor parameters."""
    if threshold <= 1:
        return whole-threshold*mass
    if threshold in hinges:
        return hinges[threshold]
    grid = sorted(set(hinges) | {F(1)})
    if threshold >= grid[-1]:
        return hinges[grid[-1]]
    lower = max(x for x in grid if x < threshold)
    upper = min(x for x in grid if x > threshold)
    weight = (upper-threshold)/(upper-lower)
    require(0 <= weight <= 1, 'nonnegative hinge secant coefficient')
    left = whole-mass if lower == 1 else hinges[lower]
    return weight*left+(1-weight)*hinges[upper]


def query_hinge(threshold, distribution, mass, whole, hinges):
    table, mean = distribution
    small = {m: probability for m, probability in table.items() if m < threshold}
    below = sum(small.values(), F(0))
    below_mean = sum((m*p for m, p in small.items()), F(0))
    require(0 <= below <= 1 and 0 <= below_mean <= mean, 'exact multiplier remainder')
    hinge = (sum((m*p*anchor_hinge_upper(F(threshold, m), mass, whole, hinges)
                  for m, p in small.items()), F(0)) +
             (mean-below_mean)*whole-threshold*(1-below)*mass)
    require(hinge >= 0, 'nonnegative complete-query stop loss')
    if threshold == 1:
        require(hinge == mean*whole-mass, 'unit query included in the comparison')
    return hinge


def comparison_distributions(primes, caps, cutoff):
    """All six stages and final law, with exact low atoms and full means."""
    def atom(p, cap, n):
        return 1-cap/p if n == 1 else cap*F(p-1, p**n)

    table, mean, distributions = {1: F(1)}, F(1), []
    for p, cap in zip(primes, caps):
        distributions.append((dict(table), mean))
        following = defaultdict(F)
        for m, probability in table.items():
            for n in range(1, (cutoff-1)//m+1):
                factor_probability = atom(p, cap, n)
                require(factor_probability >= 0, 'positive comparison factor probability')
                following[m*n] += probability*factor_probability
        table, mean = dict(following), mean*(1+cap/F(p-1))
    distributions.append((table, mean))

    @lru_cache(None)
    def factorization(stages, m):
        if stages == 0:
            return F(m == 1)
        p, cap = primes[stages-1], caps[stages-1]
        return sum((factorization(stages-1, d)*atom(p, cap, m//d)
                    for d in range(1, m+1) if m % d == 0), F(0))

    checks = 0
    for stages, (table, mean) in enumerate(distributions):
        require(mean == prod(1+caps[i]/F(primes[i]-1) for i in range(stages)),
                'full multiplier first moment')
        for m in range(1, cutoff):
            require(table.get(m, F(0)) == factorization(stages, m),
                    'independent multiplicative factorization')
            checks += 1
        require(0 <= sum(table.values(), F(0)) <= 1 and
                0 <= sum((m*w for m, w in table.items()), F(0)) <= mean,
                'low-product probability and moment')
    return distributions, checks


def eight_core_marginals(helper, envelopes):
    summaries, cases, atom_checks = [], [], 0
    schedule = tuple(helper.THRESHOLDS)
    for omitted, primes, threshold, coarse, expected_mass in EIGHT_CORE_CASES:
        require(all(1 <= t <= p-2 for p, t in zip(primes, schedule)),
                'eight-core source conditional-kernel range')
        caps = tuple(F(p-1, p-1-t) for p, t in zip(primes, schedule))
        distributions, checks = comparison_distributions(primes, caps, max(threshold, *schedule))
        atom_checks += checks
        rows = []
        for node, reserve, mass, whole, hinges in envelopes:
            losses = []
            for p, t, distribution in zip(primes, schedule, distributions):
                require(all(F(t, m) in hinges for m in distribution[0] if m < t),
                        'unchanged cached source-stage formula')
                cost = query_hinge(t, distribution, mass, whole, hinges)/(p-1-t)
                rounded = helper.ceil_decimal(cost)
                require(cost <= rounded < cost+F(1, 10**10), 'upward source loss rounding')
                losses.append(rounded)
            live = reserve-sum(losses, F(0))
            require(live > 0, 'positive same-law eight-core mass')
            numerator = query_hinge(threshold, distributions[-1], mass, whole, hinges)
            bound = threshold-1+numerator/live
            slack = (coarse-threshold+1)*live-numerator
            require(coarse-threshold+1 >= 0 and slack > 0,
                    'strict fixed-threshold concave eight-core vertex inequality')
            rows.append(dict(node=node, anchor_reserve=reserve, comparison_mass=mass,
                             linear_anchor_upper=whole, rounded_loss_upper_bounds=losses,
                             live_mass_lower_cell_units=live, query_hinge_upper=numerator,
                             normalized_query_upper=bound, strict_coarse_slack=slack))
        minimum_mass = min(row['live_mass_lower_cell_units']/135 for row in rows)
        upper = max(row['normalized_query_upper'] for row in rows)
        require(minimum_mass == expected_mass and upper < coarse, 'exact eight-core result')
        parent = 31 if omitted != 19 else 41
        marginal_bound = F(1+coarse, parent-1)
        require(marginal_bound < 1, 'deficient complete marginal via MF3')
        summaries.append(dict(omitted_prime=omitted, reference_primes=(3, 5)+primes,
                              deletion_thresholds=schedule, coordinate_caps=caps,
                              selected_query_threshold=threshold,
                              submeasure_live_mass_lower=minimum_mass,
                              unnormalized_density_cap=prod(caps),
                              nonunit_layout_bound=upper, strict_coarse_bound=coarse,
                              minimum_parent_using_coarse_bound=parent,
                              complete_marginal_strict_upper=marginal_bound,
                              tight_vertices=[row['node'] for row in rows
                                              if row['normalized_query_upper'] == upper]))
        cases.append(dict(omitted_prime=omitted, rows=rows))
    require(len(envelopes) == 32 and atom_checks == 420, 'eight-core verification scope')
    return dict(scope='For each finite original family and fixed query carrier K, one law serves '
                'all layouts. Conditional on the same attributed source construction, convex '
                'comparison, cached anchor geometry and finite prefix transport as the earlier '
                'common-law bounds. No compatibility between independently chosen K-laws.',
                independent_multiplier_atom_checks=atom_checks, exact_vertex_query_rows=128,
                missing19_boundary='This comparison excludes largest parent at least41; '
                'it does not exclude largest parent31 or37.',
                summaries=summaries, rows=cases)


def completion_parameters(count, upper, density):
    primes = (3, 5, 7, 11, 13, 17)[:count]
    if count == 5:
        coarse, parent, density_upper = F(10), 13, F(47)
        threshold, cap, expected_cutoff = F(23, 2), 1000, 14598
    else:
        require(count == 6, 'completion consumer scope')
        coarse, parent, density_upper = F(14), 17, F(150)
        threshold, cap, expected_cutoff = F(31, 2), 4000, 69797
    require(upper < coarse and density < density_upper, 'strict common-law bounds')
    mean = F(parent, parent-1)*coarse
    parent_capacity = F(parent*(parent-2), parent-1)
    probability = 1-mean/threshold
    haar_mass = probability/density_upper
    margin = parent_capacity-threshold
    require(probability > 0 and margin > 0 and haar_mass > F(1, cap), 'positive actual good set')
    moment1 = prod(F(p, p-1) for p in primes)
    moment2 = prod(F(p*(p+1), (p-1)**2) for p in primes)
    cutoff = ceil(cap*moment2)
    require(cutoff == expected_cutoff, 'height-independent tail cutoff')
    numerator = 324*cap*moment1
    require(numerator < 3**6*cutoff**3 and F(1, 3**250) < margin, 'weighted tail fits core margin')
    return dict(reference_primes=primes, transported_core_count_at_most=count,
                minimum_disjoint_parent=parent, rounded_layout_bound=coarse,
                normalized_density_strict_upper=density_upper,
                completion_mean_strict_upper=mean, good_load_threshold=threshold,
                good_probability_strict_lower=probability,
                good_Haar_mass_strict_lower=haar_mass,
                selected_good_set_density_cap=cap, pointwise_completion_margin=margin,
                M1=moment1, M2=moment2, cutoff_integer=cutoff,
                cutoff=f'3^256 * {cutoff}^3', weighted_tail_numerator=numerator)


def certificate(directory, eight_core=False):
    source = json.loads(pinned(directory, 'six_prime_prefix_certificate.json'))
    geometry = json.loads(pinned(directory, 'six_prime_prefix_geometry.json'))
    pinned(directory, 'six_prime_prefix_certificate.py')
    spec = spec_from_file_location('query_stoploss_source', directory / 'six_prime_prefix_certificate.py')
    helper = module_from_spec(spec)
    spec.loader.exec_module(helper)
    require(source['schema'] == 'six-prime-prefix-certificate-v1' and len(geometry['batches']) == 72,
            'existing certificate and geometry schemas')
    expected_nodes = {(a, b, c, -1, j, 0, 0, 0, -1)
                      for a in (1, 2) for b in (2, 4) for c in (a, 3-a) for j in range(1, 5)}
    require(len(source['rows']) == 32 and
            {tuple(row['node']) for row in source['rows']} == expected_nodes, 'complete anchor inventory')
    require(tuple(helper.THRESHOLDS) == (2, 4, 4, 8, 8, 12), 'unchanged deletion schedule')
    distributions = helper.multiplier_prefixes()
    rows, envelopes = [], []
    for original in source['rows']:
        a, b, c, _, j, *_ = original['node']
        reserve = F(original['reserve_lower_bound_cell_units'])
        losses = list(map(F, original['rounded_loss_upper_bounds_cell_units']))
        comparison_mass, whole, hinges = helper.envelope(geometry['batches'], a, b, c, j)
        envelopes.append((original['node'], reserve, comparison_mass, whole, hinges))
        if eight_core:
            continue
        row = dict(node=original['node'], anchor_reserve=reserve,
                   comparison_mass=comparison_mass, linear_anchor_upper=whole, cores={})
        for stages in (3, 4, 5):
            table, mean = distributions[stages]
            live = reserve-sum(losses[:stages])
            require(live > 0, 'positive same-law prefix ledger')
            controls = {}
            for threshold in THRESHOLDS:
                hinge = query_hinge(threshold, (table, mean), comparison_mass, whole, hinges)
                controls[threshold] = dict(hinge_upper=hinge, normalized_upper=threshold-1+hinge/live)
            row['cores'][stages+2] = dict(live_mass_lower_cell_units=live,
                                        multiplier_mean=mean, thresholds=controls)
        rows.append(row)

    if eight_core:
        require(len(helper.BATCHES) == 72 and helper.QUERIES == 51840, 'existing geometry coverage')
        return dict(scope='Eight-core marginal task on a fixed finite original family and query carrier.',
                    inputs=PINS, source=source['source'], source_producer_rerun=False,
                    geometry_enumeration_rerun=False, basic_vertices=32, cached_geometry_batches=72,
                    cached_query_reads=helper.QUERIES,
                    eight_core_marginals=eight_core_marginals(helper, envelopes))

    summaries = []
    for count, chosen in ((5, 4), (6, 8), (7, 12)):
        bounds = {t: max(row['cores'][count]['thresholds'][t]['normalized_upper'] for row in rows)
                  for t in THRESHOLDS}
        require(bounds[chosen] == min(bounds.values()), 'best tested fixed threshold')
        bound = bounds[chosen]
        for row in rows:
            local = row['cores'][count]
            slack = ((bound-chosen+1)*local['live_mass_lower_cell_units'] -
                     local['thresholds'][chosen]['hinge_upper'])
            require(bound-chosen+1 >= 0 and slack >= 0, 'fixed-threshold concave vertex inequality')
            local['selected_interpolation_slack'] = slack
        tight = [row['node'] for row in rows if row['cores'][count]['selected_interpolation_slack'] == 0]
        require(tight == [[2, 4, 1, -1, j, 0, 0, 0, -1] for j in (1, 3, 4)], 'three tight vertices')
        mass = min(row['cores'][count]['live_mass_lower_cell_units']/135 for row in rows)
        density = prod(helper.CAPS[:count-2])/mass
        if count == 5:
            require(bound == F(354268696184847779107405, 37639127656852367739093), 'five-core exact result')
        elif count == 6:
            require(bound == F(8034293665870716452955503975561029997134562974,
                               581858869356700257567944700688463416886232987), 'six-core exact result')
        else:
            require(21 < bound < 29, 'seven-core boundary of this comparison')
        summary = dict(core_count=count, fixed_threshold_bounds=bounds, selected_threshold=chosen,
                       nonunit_layout_bound=bound, tight_vertices=tight,
                       submeasure_live_mass_lower=mass, normalized_Haar_density_cap=density)
        if count <= 6:
            summary['completion'] = completion_parameters(count, bound, density)
        else:
            summary['scope'] = 'The tested threshold comparisons exceed 21; this is not an arithmetic counterexample.'
        summaries.append(summary)
    require(len(helper.BATCHES) == 72 and helper.QUERIES == 51840, 'existing geometry coverage')
    return dict(scope='Ordinary source-comparison consumer for a fixed finite original family and period. '
                'One law serves all its query phases; no projective consistency across independently chosen laws is claimed.',
                inputs=PINS, source=source['source'], source_producer_rerun=False,
                geometry_enumeration_rerun=False, basic_vertices=32, cached_geometry_batches=72,
                cached_query_reads=helper.QUERIES, exact_query_bound_rows=32*3*len(THRESHOLDS),
                query_thresholds=THRESHOLDS, retained_deletion_thresholds=helper.THRESHOLDS,
                summaries=summaries, rows=rows)


def encode(value):
    if isinstance(value, F):
        return str(value)
    if isinstance(value, dict):
        return {str(k): encode(v) for k, v in value.items()}
    if isinstance(value, (list, tuple)):
        return [encode(v) for v in value]
    return value


def main():
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    parser.add_argument('--eight-core-marginals', action='store_true',
                        help='compute the separate eight-core finite-K marginal task')
    args = parser.parse_args()
    result = certificate(Path(__file__).resolve().parent, eight_core=args.eight_core_marginals)
    payload = json.dumps(encode(result), indent=2) + '\n'
    if args.output:
        args.output.write_text(payload)
        print(json.dumps(encode({k: v for k, v in result.items() if k != 'rows'}), indent=2))
    else:
        print(payload, end='')


if __name__ == '__main__':
    main()
