"""Same-vertex first moments give a five-core weighted completion margin.

Consumes the existing six-prime prefix certificate and its pure linear-load
function. No source geometry or earlier producer is rerun. All rational checks
remain active under -O; arbitrary-height source arguments are separate premises.
"""
from argparse import ArgumentParser
from fractions import Fraction as F
from hashlib import sha256
from importlib.util import module_from_spec, spec_from_file_location
from itertools import product
from math import ceil, prod
from pathlib import Path
import json


def require(condition, message):
    if not condition:
        raise ValueError(message)


def linear_anchor(linear_sum, a, b, c, j):
    cells = [x for x in range(135) if x % 3 and x % 9 != 1 and
             x % 27 != b and x % 5 and x % 15 != a]
    total = F(0)
    for positive3, positive5 in product((False, True), repeat=2):
        weights = [(1 if positive3 else 4) *
                   (1 if positive5 else 16 - 4*(x % 5 == c) - (x % 5 == j))
                   for x in cells]
        moment3 = (F(1, 3), F(1, 2)) if positive3 else (F(1), F(0))
        moment5 = (F(1, 5), F(1, 4)) if positive5 else (F(1), F(0))
        scale = F(1, (1 if positive3 else 6)*(1 if positive5 else 20))
        total += scale*linear_sum(weights, cells, moment3, moment5)
    return total


def certificate(directory):
    source_path = directory / 'six_prime_prefix_certificate.json'
    raw = source_path.read_bytes()
    require(sha256(raw).hexdigest() ==
            'ecdeb6246626c101b7bb16130366a7d22bf8d71775d5f28997b85e74c796ee61',
            'existing source certificate identity')
    source = json.loads(raw)
    require(source['schema'] == 'six-prime-prefix-certificate-v1', 'source schema')
    spec = spec_from_file_location('five_core_linear_source',
                                  directory / 'six_prime_prefix_certificate.py')
    helper = module_from_spec(spec)
    spec.loader.exec_module(helper)
    expected = {(a, b, c, -1, j, 0, 0, 0, -1)
                for a in (1, 2) for b in (2, 4) for c in (a, 3-a) for j in range(1, 5)}
    require(len(source['rows']) == len(expected) == 32 and
            {tuple(row['node']) for row in source['rows']} == expected,
            'complete distinct basic vertex inventory')
    caps = (F(3, 2), F(5, 3), F(3, 2))
    multiplier = prod(1 + cap/F(p-1) for p, cap in zip((7, 11, 13), caps))
    density = prod(caps)
    require(multiplier == F(105, 64) and density == F(15, 4), 'whole-coordinate caps')
    rows = []
    for original in source['rows']:
        a, b, c, _, j, *_ = original['node']
        reserve = F(original['reserve_lower_bound_cell_units'])
        gamma = 3*(a == 1) + (b % 3 == a % 3)
        require(reserve == F(135, 4) + gamma +
                (9-gamma)*(F(c == a, 5) + F(j == a, 20)), 'same physical anchor reserve')
        require(original['stage_primes'] == [7, 11, 13, 17, 19, 23], 'stage identity')
        loss = sum(map(F, original['rounded_loss_upper_bounds_cell_units'][:3]))
        whole = linear_anchor(helper.linear_sum, a, b, c, j)
        live = reserve-loss
        numerator = multiplier*whole-reserve
        require(live > 0 and numerator > 0, 'positive five-core ledger')
        next_loss = loss + F(original['rounded_loss_upper_bounds_cell_units'][3])
        require(reserve > next_loss, 'positive six-core ledger for method comparison')
        rows.append(dict(node=original['node'], anchor_reserve=reserve,
                         linear_anchor_upper=whole, five_core_loss_upper=loss,
                         five_core_live_lower=live, nonunit_integral_upper=numerator,
                         normalized_nonunit_upper=numerator/live,
                         next_prefix_upper=(multiplier*F(9, 8)*whole-reserve)/(reserve-next_loss)))
    bound = max(row['normalized_nonunit_upper'] for row in rows)
    mass = min(row['five_core_live_lower']/135 for row in rows)
    require(bound == F(27050781250, 1812390307) < 15, 'parent-17 first-moment threshold')
    require(mass == F(1812390307, 22500000000), 'same-law survivor mass')
    for row in rows:
        row['interpolation_slack'] = bound*row['five_core_live_lower']-row['nonunit_integral_upper']
        require(row['interpolation_slack'] >= 0, 'every vertex supplies the concave interpolation')
    tight = [row['node'] for row in rows if row['interpolation_slack'] == 0]
    require(tight == [[2, 4, 1, -1, j, 0, 0, 0, -1] for j in (1, 3, 4)], 'three tight comparison vertices')
    next_bound = max(row['next_prefix_upper'] for row in rows)
    require(next_bound == F(143701171875, 5231277137) > 17,
            'the unchanged next-prefix upper bound does not pass parent 19')
    tight_row = next(row for row in rows if row['node'] == tight[0])
    zero_next_loss = (multiplier*F(9, 8)*tight_row['linear_anchor_upper'] -
                      tight_row['anchor_reserve'])/tight_row['five_core_live_lower']
    require(zero_next_loss == F(9580078125, 557658556) > 17,
            'even zero next-stage loss does not repair the retained numerator at this vertex')

    mean = F(17, 16)*bound
    whole_threshold = F(255, 16)
    require(whole_threshold-mean > F(3, 40), 'strict mean slack')
    threshold = F(159, 10)
    margin = whole_threshold-threshold
    good_probability = F(3, 80)/threshold
    haar_mass = good_probability*mass/density
    require(margin == F(3, 80) and good_probability == F(1, 424), 'pointwise conversion')
    require(haar_mass == F(1812390307, 35775000000000) > F(1, 20000), 'good-set Haar mass')
    density_cap = 20000
    core_primes = (3, 5, 7, 11, 13)
    moment1 = prod(F(p, p-1) for p in core_primes)
    moment2 = prod(F(p*(p+1), (p-1)**2) for p in core_primes)
    cutoff_integer = ceil(density_cap*moment2)
    require(moment1 == F(1001, 384) and moment2 == F(7007, 480), 'all-height divisor sums')
    require(cutoff_integer == 291959, 'uniform tail cutoff')
    tail_numerator = 324*density_cap*moment1
    require(tail_numerator < 3**6*cutoff_integer**3 and F(1, 3**250) < margin,
            'tail remains below the actual pointwise core margin')
    return dict(scope='New first-moment consumer of existing source bounds; source arbitrary-height '
                'comparison and completion are mathematical premises, not certified by these finite checks.',
                source_certificate_sha256=sha256(raw).hexdigest(), source=source['source'],
                reference_core_primes=core_primes, minimum_distinguished_prime=17,
                transported_scope='Any at most five actual odd core primes, disjoint from the '
                'distinguished prime; finite random prefix injections preserve the bound.',
                basic_vertices=len(rows), same_law_nonunit_layout_mean_upper=bound,
                submeasure_live_mass_lower=mass, submeasure_joint_Haar_density_cap=density,
                normalized_Haar_density_cap=density/mass, multiplier=multiplier,
                core_mean_upper=mean, core_mean_slack=whole_threshold-mean,
                good_load_threshold=threshold, good_probability_strict_lower=good_probability,
                good_Haar_mass_strict_lower=haar_mass, pointwise_margin=margin,
                good_set_Haar_density_cap=density_cap, M1=moment1, M2=moment2,
                cutoff_integer=cutoff_integer, cutoff='3^256 * 291959^3',
                weighted_tail_numerator=tail_numerator, tight_vertices=tight,
                next_prefix_mean_upper=next_bound,
                tight_vertex_upper_with_zero_next_loss=zero_next_loss,
                next_prefix_scope='An upper-bound failure at parent 19, not a realizable phase counterexample.',
                rows=rows)


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
