#!/usr/bin/env python3
"""Exact actual-family equal-readout fixture; no source search or LP."""
from fractions import Fraction as F
from math import prod


def require(ok, message):
    if not ok:
        raise ValueError(message)


OLD = (3, 5, 7, 11, 13, 17, 19)
PRIMES = OLD + (23, 29)


def crt(coords):
    mod = prod(coords)
    return sum(a * (mod // p) * pow(mod // p, -1, p)
               for p, a in coords.items()) % mod


def family(kind):
    rows = [(p, 1, {p: 1}) for p in OLD]
    for coords in ({3: 0, 23: 0}, {5: 0, 23: 1}):
        rows.append((prod(coords), crt(coords), coords))
    ys = (0, 1) if kind == 'removed' else (2, 2)
    for p, y in zip((7, 11), ys):
        coords = {p: 0, 23: y, 29: 0}
        rows.append((prod(coords), crt(coords), coords))
    require(len(rows) == 11 and len({d for d, _, _ in rows}) == 11,
            'Eleven distinct original odd moduli')
    # Fill unused coordinates by the clean residue 2. Each designated class
    # gets a private point, including the 29-classes whose old-law mass may
    # have been killed earlier. Activity is global actual activity.
    for i, (_, _, coords) in enumerate(rows):
        point = {p: 2 for p in PRIMES}
        point.update(coords)
        n = crt(point)
        require([j for j, (d, a, _) in enumerate(rows) if n % d == a] == [i],
                'Private CRT point for original label ' + str(i))
    survivor = crt({p: 2 for p in PRIMES})
    require(all(survivor % d != a for d, a, _ in rows), 'Complete actual survivor')
    require(all(0 % p != 1 for p in OLD), 'Old Dirac law lies on complete19 survivors')
    return rows


def kernel(alpha, delta, forbidden, size):
    require(alpha == F(sum(forbidden), size) and 0 < delta <= F(1, 2),
            'Actual forbidden fraction and legal clipping parameter')
    if alpha <= delta:
        out = [F(0) if b else F(1, size) / (1 - alpha) for b in forbidden]
    else:
        out = [F(1, size) * (alpha - delta) / (alpha * (1 - delta))
               if b else F(1, size) / (1 - delta) for b in forbidden]
    require(sum(out) == 1 and all(v >= 0 for v in out), 'Actual normalized clipped row')
    return out


def measure(rows):
    old_coordinates = {p: 0 for p in OLD}
    forbidden23 = [any(all(old_coordinates.get(p, y) == a for p, a in coords.items())
                       for d, _, coords in rows if d % 23 == 0 and d % 29 != 0)
                   for y in range(23)]
    require(forbidden23 == [y in (0, 1) for y in range(23)], 'Same actual23 fibre')
    mu = kernel(F(sum(forbidden23), 23), F(1, 23), forbidden23, 23)
    xi = [v if not b else F(0) for v, b in zip(mu, forbidden23)]
    alpha29, beta29, final_rows = [], [], []
    for y in range(23):
        old_y = dict(old_coordinates)
        old_y[23] = y
        forbidden29 = [any(all(old_y.get(p, z) == a for p, a in coords.items())
                          for d, _, coords in rows if d % 29 == 0)
                       for z in range(29)]
        a = F(sum(forbidden29), 29)
        k = kernel(a, F(1, 58), forbidden29, 29)
        alpha29.append(a)
        beta29.append(sum(v for v, b in zip(k, forbidden29) if b))
        final_rows.append(sum(v for v, b in zip(k, forbidden29) if not b))
    b23 = 1 - sum(xi)
    b29 = sum(v * b for v, b in zip(mu, beta29))
    moment = sum(v * a * a for v, a in zip(mu, alpha29))
    overlap = sum((u - v) * b for u, v, b in zip(mu, xi, beta29))
    removed_moment = sum((u - v) * a * a for u, v, a in zip(mu, xi, alpha29))
    survived_moment = sum(v * a * a for v, a in zip(xi, alpha29))
    survival = sum(v * q for v, q in zip(xi, final_rows))
    require(survival == 1 - b23 - b29 + overlap, 'Exact common-law two-step mass')
    require(survived_moment == moment - removed_moment, 'Exact masked moment')
    histogram = {}
    for v, a in zip(mu, alpha29):
        histogram[a] = histogram.get(a, F(0)) + v
    return dict(b23=b23, b29=b29, physical_moment=moment,
                alpha29_law=histogram,
                overlap=overlap, removed_moment=removed_moment,
                survived_moment=survived_moment, survival=survival)


def check_conditional_coefficients():
    # Closed-form full-prime tails; this checks the arithmetic of the
    # conditional criterion, not the unmeasured post19 hinge premise.
    p, q = 23, 29
    prefix_tail = F(3 * p - 1, (p - 1) ** 2)
    transfer = 1 + 2 * prefix_tail
    square_tail = F(1, (q - 1) ** 2)
    m_coef = 1 - square_tail * transfer * 484
    d_coef = square_tail * transfer
    hinge_m, hinge_d = 11 * m_coef, 11 * d_coef
    mass_free = hinge_m / 483 + hinge_d
    require(prefix_tail == F(17, 121) and transfer == F(155, 121),
            'Complete23 prefix transfer tail')
    require((m_coef, d_coef) == (F(41, 196), F(155, 94864)),
            'Direct two-step surviving-mass coefficients')
    require((hinge_m, hinge_d) == (F(451, 196), F(155, 8624)),
            'Complete hinge11 sufficient criterion')
    require(mass_free == F(94709, 4165392),
            'Unit-floor improvement using m >= d/483')
    threshold = mass_free * (403 - F('399.926243355'))
    require(F('0.06988836058') < threshold < F('0.06988836059'),
            'Exact conditional hinge threshold for the stated325 upper bound')
    print('conditional-hinge11-threshold', str(threshold), '(hinge premise unmeasured)')


def main():
    check_conditional_coefficients()
    a, b = family('removed'), family('survived')
    require([r[0] for r in a] == [r[0] for r in b], 'Same original modulus inventory')
    require(a[:9] == b[:9], 'Same complete old family and actual23 labels')
    ra, rb = measure(a), measure(b)
    for key, expected in (('b23', F(1, 22)), ('b29', F(1, 1254)),
                          ('physical_moment', F(1, 18502))):
        require(ra[key] == rb[key] == expected, 'Same exact scalar reading ' + key)
    require(ra['alpha29_law'] == rb['alpha29_law'] == {F(0): F(21, 22), F(1, 29): F(1, 22)},
            'Equal complete physical alpha29 laws, hence every scalar moment')
    require(ra['survived_moment'] == 0 and rb['survived_moment'] == F(1, 18502),
            'Different actual survivor-weighted second moments')
    require(ra['overlap'] == F(1, 1254) and rb['overlap'] == 0,
            'Different actual overlap despite equal scalar readings')
    require(ra['survival'] == F(21, 22) and rb['survival'] == F(598, 627),
            'Both actual positive final masses')
    require(ra['survival'] - rb['survival'] == F(1, 1254), 'Strict survival separation')
    print('29-burden-on-removed23', {k: str(v) for k, v in ra.items()})
    print('29-burden-on-surviving23', {k: str(v) for k, v in rb.items()})
    print('PASS exact kernels, equal scalar readouts, distinct survival; all 22 private points')


if __name__ == '__main__':
    main()
