"""Complete-query stop-loss bounds from the pinned basic anchor certificate.

Only cached geometry values and exact geometric remainders are consumed.
No geometry enumeration or source producer is run. The same fixed threshold
is used at every continuous anchor vertex. Checks remain active under -O.
"""
from argparse import ArgumentParser
from fractions import Fraction as F
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


def require(condition, message):
    if not condition:
        raise ValueError(message)


def pinned(directory, name):
    raw = (directory / name).read_bytes()
    require(sha256(raw).hexdigest() == PINS[name], 'pinned input: ' + name)
    return raw


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


def certificate(directory):
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
    rows = []
    for original in source['rows']:
        a, b, c, _, j, *_ = original['node']
        reserve = F(original['reserve_lower_bound_cell_units'])
        losses = list(map(F, original['rounded_loss_upper_bounds_cell_units']))
        comparison_mass, whole, hinges = helper.envelope(geometry['batches'], a, b, c, j)
        row = dict(node=original['node'], anchor_reserve=reserve,
                   comparison_mass=comparison_mass, linear_anchor_upper=whole, cores={})
        for stages in (3, 4, 5):
            table, mean = distributions[stages]
            live = reserve-sum(losses[:stages])
            require(live > 0, 'positive same-law prefix ledger')
            controls = {}
            for threshold in THRESHOLDS:
                small = {m: probability for m, probability in table.items() if m < threshold}
                below = sum(small.values(), F(0))
                below_mean = sum((m*p for m, p in small.items()), F(0))
                require(0 <= below <= 1 and 0 <= below_mean <= mean, 'exact multiplier remainder')
                hinge = (sum((m*p*hinges[F(threshold, m)] for m, p in small.items()), F(0)) +
                         (mean-below_mean)*whole-threshold*(1-below)*comparison_mass)
                require(hinge >= 0, 'nonnegative complete-query stop loss')
                if threshold == 1:
                    require(hinge == mean*whole-comparison_mass, 'unit query included in the comparison')
                controls[threshold] = dict(hinge_upper=hinge, normalized_upper=threshold-1+hinge/live)
            row['cores'][stages+2] = dict(live_mass_lower_cell_units=live,
                                        multiplier_mean=mean, thresholds=controls)
        rows.append(row)

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
    args = parser.parse_args()
    result = certificate(Path(__file__).resolve().parent)
    payload = json.dumps(encode(result), indent=2) + '\n'
    if args.output:
        args.output.write_text(payload)
        print(json.dumps(encode({k: v for k, v in result.items() if k != 'rows'}), indent=2))
    else:
        print(payload, end='')


if __name__ == '__main__':
    main()
