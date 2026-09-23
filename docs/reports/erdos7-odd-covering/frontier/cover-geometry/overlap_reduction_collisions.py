"""Exact AP checks of two excess-reduction operations and their collisions.

Restriction can create an exact residual cover with repeated moduli.
Ternary insertion reduces excess while repeating output moduli. No fixture
is asserted to be a distinct odd whole cover; the general template
obstruction is an ordinary Fourier proof in the accompanying report.
"""

from collections import Counter
from fractions import Fraction as F
from itertools import product
from math import gcd, lcm


def require(condition, message):
    if not condition:
        raise ValueError(message)


def load(family, x):
    return sum((x-a) % m == 0 for a, m in family)


def mass(family):
    return sum((F(1, m) for _, m in family), F(0))


def restrict(family, a, d):
    result = []
    for b, m in family:
        g = gcd(m, d)
        if (b-a) % g == 0:
            n = m//g
            residue = 0 if n == 1 else ((b-a)//g)*pow(d//g, -1, n) % n
            result.append((residue, n))
    return result


def check_restriction(family, d):
    require(d > 0 and all(m > 0 for _, m in family), 'Positive moduli required')
    require(len({m for _, m in family}) == len(family), 'Original moduli must differ')
    period = lcm(d, *(m for _, m in family))
    residual_period = period//d
    original = [load(family, x) for x in range(period)]
    mean_h = mean_excess = mean_holes = F(0)
    selectors = 0
    for a in range(d):
        residual = restrict(family, a, d)
        loads = [load(residual, k) for k in range(residual_period)]
        require(loads == original[a:period:d], 'Literal affine pullback')
        h = mass(residual)-1
        groups = {}
        for b, n in residual:
            groups.setdefault(n, set()).add(b)
        clean_mass = sum((F(len(bs), n) for n, bs in groups.items()), F(0))
        duplicate = mass(residual)-clean_mass
        collision = sum((F(len(bs)-1, n) for n, bs in groups.items()), F(0))
        mean_h += h/d
        mean_excess += F(sum(max(v-1, 0) for v in loads), period)
        mean_holes += F(loads.count(0), period)
        moduli = sorted(groups)
        for residues in product(*(sorted(groups[n]) for n in moduli)):
            selected = list(zip(residues, moduli))
            selected_loads = [load(selected, k) for k in range(residual_period)]
            uncovered = F(selected_loads.count(0), residual_period)
            excess = F(sum(max(v-1, 0) for v in selected_loads), residual_period)
            require(uncovered-excess == collision-(h-duplicate), 'Selector identity')
            if all(v >= 1 for v in loads):
                require(0 <= duplicate <= h, 'Duplicate bound on covered fibre')
                require(max(F(0), collision-(h-duplicate)) <= uncovered <= collision,
                        'Collision deletion bounds on covered fibre')
                require(excess <= h-duplicate, 'Deletion cannot increase excess')
            selectors += 1
    require(mean_h == mass(family)-1, 'Signed-excess disintegration')
    require(mean_excess == F(sum(max(v-1, 0) for v in original), period),
            'Positive-excess disintegration')
    require(mean_holes == F(original.count(0), period), 'Uncovered-mass disintegration')
    return period, selectors


def check_template(seed, holes):
    seed_period = lcm(*(m for _, m in seed))
    require(all(load(seed, x) >= 1 for x in range(seed_period)), 'Seed must cover')
    output = [(a, 3) for a in range(3) if a not in holes]
    output += [(a+3*b, 3*m) for a in holes for b, m in seed]
    period = 3*seed_period
    output_loads = []
    for x in range(period):
        a = x % 3
        expected = load(seed, (x-a)//3) if a in holes else 1
        observed = load(output, x)
        require(observed == expected and observed >= 1, 'Literal inserted coverage')
        output_loads.append(observed)
    require(mass(output)-1 == F(len(holes), 3)*(mass(seed)-1), 'Excess dilution')
    require(mass(output)-1 == F(sum(v-1 for v in output_loads), period),
            'Actual output Haar excess')
    palette = Counter(m for _, m in output)
    require(any(v > 1 for v in palette.values()), 'Required modulus collision')
    require(len({(a % m, m) for a, m in output}) == len(output),
            'Repeated moduli are different events, not identical copies')
    if len(holes) == 1:
        require(palette[3] == 2, 'Retained classes repeat modulus 3')
    else:
        require(all(palette[3*m] == 2*v for m, v in Counter(m for _, m in seed).items()),
                'Two holes repeat every inserted modulus')
    return period


def main():
    odd = [(0, 3), (10, 15), (50, 75)]
    even_cover = [(0, 2), (0, 3), (1, 4), (5, 6), (7, 12)]
    fixtures = [(odd, 25), ([(0, 15), (0, 35)], 21),
                ([(0, 15), (7, 35)], 21),
                ([(0, 3), (1, 5), (2, 9), (4, 15), (7, 25)], 15),
                (even_cover, 3)]
    results = [check_restriction(family, d) for family, d in fixtures]
    require(all(load(odd, x) <= 1 for x in range(75)), 'Odd family is disjoint')
    require(all(load(odd, x) == 1 for x in (0, 10, 50)), 'Original private points')
    require(restrict(odd, 0, 25) == [(0, 3), (1, 3), (2, 3)], 'Exact conditional cover')
    require(mass(odd) == F(31, 75), 'Original family is not a whole cover')
    require(all(F(sum(load([(r, 3)], k) == 0 for k in range(3)), 3) == F(2, 3)
                for r in range(3)), 'Every distinct-modulus selector loses two thirds')
    repeated_odd_cover = [(0, 3), (1, 3), (2, 3), (0, 5)]
    template_points = sum(check_template(seed, holes)
                          for seed in (even_cover, repeated_odd_cover)
                          for holes in ((0,), (1, 2)))
    print({'restriction_fixtures': len(results),
           'restriction_period_points': sum(p for p, _ in results),
           'selectors': sum(s for _, s in results),
           'template_fixtures': 4, 'template_period_points': template_points})
    print('PASS exact restrictions, disintegration, selector holes, dilution and modulus collisions')
    print('No distinct odd whole-cover fixture or Lean verification is claimed.')


if __name__ == '__main__':
    main()
