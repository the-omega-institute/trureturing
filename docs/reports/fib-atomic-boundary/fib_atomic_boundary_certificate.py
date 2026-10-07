#!/usr/bin/env python3
"""Exact data for AURIC_FIB_ATOMIC_BOUNDARY_CALCULUS.md.

All sign decisions use integers and fractions.Fraction. Logarithms use
twenty atanh terms after binary range reduction, with outward dyadic
rounding. This is a reconstructed certificate, not the supplied sandbox
artifact. It is an ordinary mathematical experiment, not a Lean checker.
"""

import argparse
from fractions import Fraction as Q
from functools import lru_cache
from itertools import product
import json
from pathlib import Path


BITS = 80
SCALE = 1 << BITS
LOG_TERMS = 20
HARMONIC_N = 1024
PRIMES = (2, 3, 5, 7)
EXPONENT_LIMITS = (16, 10, 7, 6)


def require(condition, message):
    if not condition:
        raise ArithmeticError(message)


def outward(lo, hi):
    """Enclose [lo, hi] in the dyadic grid of spacing 2**(-BITS)."""
    require(lo <= hi, "reversed interval")
    a, b = lo * SCALE, hi * SCALE
    return Q(a.numerator // a.denominator, SCALE), Q(
        -((-b.numerator) // b.denominator), SCALE
    )


def add(x, y):
    return outward(x[0] + y[0], x[1] + y[1])


def subtract(x, y):
    return outward(x[0] - y[1], x[1] - y[0])


def multiply_integer(k, x):
    return outward(k * x[0], k * x[1]) if k >= 0 else outward(
        k * x[1], k * x[0]
    )


def unit_log(x):
    require(1 <= x <= 2, "unit logarithm outside [1,2]")
    t = (x - 1) / (x + 1)
    partial = 2 * sum(
        (t ** (2 * j + 1) / (2 * j + 1) for j in range(LOG_TERMS)), Q(0)
    )
    remainder = 2 * t ** (2 * LOG_TERMS + 1) / (
        (2 * LOG_TERMS + 1) * (1 - t * t)
    )
    return outward(partial, partial + remainder)


LOG_TWO = unit_log(Q(2))


@lru_cache(maxsize=None)
def log_rational(x):
    require(x > 0, "nonpositive logarithm argument")
    y, e = x, 0
    while y < 1:
        y *= 2
        e -= 1
    while y >= 2:
        y /= 2
        e += 1
    return add(multiply_integer(e, LOG_TWO), unit_log(y))


def log_interval(x):
    require(0 < x[0] <= x[1], "log interval crosses zero")
    return outward(log_rational(x[0])[0], log_rational(x[1])[1])


def nested_logs(n):
    x = (Q(n), Q(n))
    levels = []
    for _ in range(3):
        x = log_interval(x)
        levels.append(x)
    return levels


def gamma_interval():
    h = sum((Q(1, j) for j in range(1, HARMONIC_N + 1)), Q(0))
    lo = h - log_rational(Q(HARMONIC_N + 1))[1]
    hi = h - log_rational(Q(HARMONIC_N))[0]
    return outward(lo, hi)


GAMMA = gamma_interval()


def z_from_exponents(exponents):
    z = Q(1)
    for p, a in zip(PRIMES, exponents):
        z *= sum((Q(1, p ** k) for k in range(a + 1)), Q(0))
    return z


def integer_from_exponents(exponents):
    n = 1
    for p, a in zip(PRIMES, exponents):
        n *= p ** a
    return n


def atom_partial(exponents, k):
    require(k >= 0, "negative atom cutoff")
    return sum(
        (sum((Q(1, p ** j) - Q(1, p ** ((a + 1) * j))
              for p, a in zip(PRIMES, exponents) if a > 0), Q(0)) / j
         for j in range(1, k + 1)), Q(0)
    )


def atom_tail(exponents, k):
    require(k >= 0, "negative atom cutoff")
    return sum(
        (Q(1, (k + 1) * p ** (k + 1)) / (1 - Q(1, p))
         for p, a in zip(PRIMES, exponents) if a > 0), Q(0)
    )


def decimal_outward(x, digits=9):
    scale = 10 ** digits
    def render(q, upper):
        y = q * scale
        v = -((-y.numerator) // y.denominator) if upper else (
            y.numerator // y.denominator
        )
        sign = "-" if v < 0 else ""
        v = abs(v)
        return f"{sign}{v // scale}.{v % scale:0{digits}d}"
    return [render(x[0], False), render(x[1], True)]


def interval_data(x):
    return {"lower": str(x[0]), "upper": str(x[1]),
            "decimal_outward": decimal_outward(x)}


def margin_data(n, z, threshold=None):
    logs = nested_logs(n)
    right = add(GAMMA, logs[-1])
    logz = log_rational(z)
    margin = subtract(right, logz)
    if threshold is not None:
        require(margin[0] > Q(threshold), f"insufficient margin at {n}")
    return {"n": n, "Z_bound": str(z),
            "nested_logs": [interval_data(x) for x in logs],
            "log_Z_bound": interval_data(logz),
            "margin": interval_data(margin),
            "strict_lower_threshold": threshold}


def attach_atom_margin(data, exponents, saturation=False):
    """Transport an actual maximum or the common saturation through K=20."""
    k = LOG_TERMS
    partial = (sum((sum((Q(1, p ** j) for p in PRIMES), Q(0)) / j
                    for j in range(1, k + 1)), Q(0)) if saturation else
               atom_partial(exponents, k))
    epsilon = atom_tail(exponents, k)
    upper = partial + epsilon
    right = add(GAMMA, nested_logs(data['n'])[-1])
    margin = outward(right[0] - upper, right[1] - partial)
    require(Q(data['log_Z_bound']['upper']) <= upper, "atomic upper comparison")
    require(margin[0] > Q(data['strict_lower_threshold']), "atomic sign margin")
    data['atom_certificate'] = {
        "K": k, "saturation": saturation,
        "exponents": None if saturation else list(exponents),
        "L_K": str(partial), "epsilon_K": str(epsilon), "upper": str(upper),
        "margin": interval_data(margin)
    }


def finite_regions():
    ranges = ((5041, 10079), (10080, 25199), (25200, 119999))
    rows = [[] for _ in ranges]
    candidates = 0
    for exponents in product(*(range(a + 1) for a in EXPONENT_LIMITS)):
        candidates += 1
        n = integer_from_exponents(exponents)
        for index, (lo, hi) in enumerate(ranges):
            if lo <= n <= hi:
                rows[index].append((n, exponents, z_from_exponents(exponents)))
    require(candidates == 10472, "candidate cardinality")
    expected = ((72, Q(80, 21), 7560), (121, Q(248, 63), 15120),
                (270, Q(3844, 945), 75600))
    regions = []
    for bounds, bucket, (count, bound, witness) in zip(ranges, rows, expected):
        bucket.sort()
        require(len(bucket) == count, "finite region count")
        require(max(z for _, _, z in bucket) == bound, "finite maximum")
        attainers = [n for n, _, z in bucket if z == bound]
        require(witness in attainers, "maximum witness")
        regions.append({"lower_n": bounds[0], "upper_n": bounds[1],
                        "count": count, "max_Z": str(bound),
                        "attainers": attainers,
                        "rows_n_exponents_Z": [[n, list(e), str(z)]
                                               for n, e, z in bucket]})
    return candidates, regions


def mobius_and_box():
    exponents = (4, 2, 1, 1)
    terms = []
    total = Q(0)
    for mask in product((0, 1), repeat=4):
        d = integer_from_exponents(mask)
        mu = (-1) ** sum(mask)
        z = z_from_exponents(tuple(a - bit for a, bit in zip(exponents, mask)))
        total += mu * z
        terms.append({"d": d, "mu": mu, "n_over_d": 5040 // d, "Z": str(z)})
    require(total == Q(1, 5040), "5040 Mobius atom")
    box = set(product(*(range(a + 1) for a in exponents)))
    require(len(box) == 60, "divisor box cardinality")
    exterior = {}
    for v in box:
        for mask in product((0, 1), repeat=4):
            w = tuple(a + bit for a, bit in zip(v, mask))
            exterior[w] = exterior.get(w, 0) + (-1) ** sum(mask)
    exterior = {v: c for v, c in exterior.items() if c}
    expected = {tuple((a + 1) * bit for a, bit in zip(exponents, mask)):
                (-1) ** sum(mask) for mask in product((0, 1), repeat=4)}
    require(exterior == expected, "exterior support difference")
    for v in product(*(range(a + 3) for a in exponents)):
        recovered = sum(c for w, c in exterior.items()
                        if all(u <= t for u, t in zip(w, v)))
        require(recovered == int(v in box), "causal support reconstruction")
    return {"Z_5040": str(z_from_exponents(exponents)),
            "divisor_count": len(box), "mobius_terms": sorted(terms, key=lambda x: x['d']),
            "mobius_sum": str(total),
            "exterior_endpoint_coefficients": [[list(v), c]
                                               for v, c in sorted(exterior.items())]}


def fib_polynomials():
    f = [0, 1]
    for _ in range(95):
        f.append(f[-1] + f[-2])
    # Columns: previous seam 0,1; rows: next seam 0,1.
    v, a = (1, 0), []
    for n in range(31):
        a.append(sum(v))
        require(a[-1] == f[3 * n + 2], "guarded Fibonacci prefix count")
        v = (3 * v[0] + 2 * v[1], 2 * v[0] + v[1])
    for n in range(30):
        actual = [0] * (n + 3)
        for j in range(n + 1):
            for k, c in enumerate((1, -4, -1)):
                actual[j + k] += c * a[j]
        expected = [0] * (n + 3)
        expected[0] += 1
        expected[1] += 1
        expected[n + 1] -= a[n + 1]
        expected[n + 2] -= a[n]
        require(actual == expected, "finite Fibonacci polynomial including N=0")
    return {"free_end_guard": 0, "N_polynomial_range": [0, 29],
            "prefix_counts_n0_to30": a,
            "counting_matrix": [[3, 2], [2, 1]]}


def phase_alias_data():
    lengths = (5, 3, 2, 2)
    # Root-of-unity averages are exact integer tests on exponents modulo m.
    independent_survivors, shared_survivors = 0, 0
    diagonal_weight = Q(0)
    grid = list(product(*(range(m) for m in lengths)))
    for u in grid:
        diagonal_weight += Q(1, integer_from_exponents(u))
        for v in grid:
            independent_survivors += int(all((a - b) % m == 0
                                            for a, b, m in zip(u, v, lengths)))
            shared_survivors += int(sum(u) == sum(v))
    require(independent_survivors == 60, "independent phase diagonal")
    require(shared_survivors > independent_survivors, "shared phase counterexample")
    require(diagonal_weight == Q(403, 105), "independent phase norm mean")
    return {"axis_grid_lengths": list(lengths), "grid_size": len(grid),
            "independent_surviving_pairs": independent_survivors,
            "shared_continuous_phase_surviving_pairs": shared_survivors,
            "independent_mean_square": str(diagonal_weight)}


def certificate():
    count, regions = finite_regions()
    signs = [margin_data(r['lower_n'], Q(r['max_Z']), threshold)
             for r, threshold in zip(regions, ('0.0014', '0.0044', '0.0134'))]
    for data, exponents in zip(signs, ((3, 3, 1, 1), (4, 3, 1, 1), (4, 3, 2, 1))):
        require(z_from_exponents(exponents) == Q(data['Z_bound']), "maximum response")
        attach_atom_margin(data, exponents)
    tail = margin_data(120000, Q(35, 8), '0.0006')
    attach_atom_margin(tail, (1, 1, 1, 1), saturation=True)
    endpoints = [margin_data(n, z_from_exponents(e))
                 for n, e in ((5040, (4, 2, 1, 1)), (10080, (5, 2, 1, 1)))]
    for data, lo, hi in zip(endpoints, ('-0.006032', '0.013795'),
                            ('-0.005055', '0.014772')):
        m = data['margin']
        require(Q(lo) < Q(m['lower']) <= Q(m['upper']) < Q(hi), "endpoint enclosure")
    atom_rows = []
    exponents = (4, 2, 1, 1)
    logz = log_rational(z_from_exponents(exponents))
    for k in (0, 1, 8, 20):
        partial, tail_budget = atom_partial(exponents, k), atom_tail(exponents, k)
        require(partial < logz[0] and logz[1] <= partial + tail_budget,
                "positive atom strict lower / tail enclosure")
        atom_rows.append({"K": k, "L_K": str(partial),
                          "epsilon_K": str(tail_budget),
                          "upper": str(partial + tail_budget)})
    counterexample_z = z_from_exponents(exponents) * Q(12, 11) * Q(14, 13)
    require(counterexample_z == Q(3224, 715) > Q(35, 8), "fixed-bound counterexample")
    return {"schema": "fib-atomic-boundary-exact-v1",
            "provenance": "reconstructed mathematical certificate; not original sandbox bytes",
            "arithmetic": {"rational": "fractions.Fraction", "rounding_bits": BITS,
                           "log_terms": LOG_TERMS, "harmonic_N": HARMONIC_N},
            "prime_support": list(PRIMES), "exponent_upper_bounds": list(EXPONENT_LIMITS),
            "next_prime_powers": [p ** (a + 1) for p, a in zip(PRIMES, EXPONENT_LIMITS)],
            "candidate_count": count, "finite_regions": regions,
            "gamma": interval_data(GAMMA), "log_two": interval_data(LOG_TWO),
            "finite_region_signs": signs, "saturation_tail": tail,
            "point_margins": endpoints, "atomic_log_5040": atom_rows,
            "divisor_box": mobius_and_box(), "fib": fib_polynomials(),
            "phase": phase_alias_data(),
            "fixed_saturation_bound_counterexample": {
                "n": 720720, "Z": str(counterexample_z), "excluded_bound": "35/8"
            }}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    choice = parser.add_mutually_exclusive_group()
    choice.add_argument('--output', type=Path, help='write exact result JSON')
    choice.add_argument('--check', type=Path, help='recompute and compare result JSON')
    args = parser.parse_args()
    data = certificate()
    if args.check:
        require(data == json.loads(args.check.read_text(encoding='utf-8')),
                'stored result differs from exact recomputation')
        print('EXACT_CERTIFICATE_MATCH')
    else:
        rendered = json.dumps(data, ensure_ascii=False, indent=2) + '\n'
        if args.output:
            args.output.write_text(rendered, encoding='utf-8')
            print('EXACT_CERTIFICATE_WRITTEN')
        else:
            print(rendered, end='')


if __name__ == '__main__':
    main()
