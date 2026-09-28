#!/usr/bin/env python3
"""Exact, standard-library experiments; coefficients are constant first."""
import argparse
import hashlib
import json
import math
from pathlib import Path


def require(condition, message):
    if not condition:
        raise ValueError(message)


def trim(poly):
    poly = list(poly)
    while poly and poly[-1] == 0:
        poly.pop()
    return poly


def add(left, right, scale=1):
    out = list(left) + [0] * max(0, len(right) - len(left))
    for i, value in enumerate(right):
        out[i] += scale * value
    return trim(out)


def multiply(left, right):
    out = [0] * max(0, len(left) + len(right) - 1)
    for i, x in enumerate(left):
        for j, y in enumerate(right):
            out[i + j] += x * y
    return trim(out)


def divide_monic(poly, divisor, modulus=None):
    """Long division over Z or Z/modulus; no coefficient inversion."""
    require(len(divisor) >= 2 and divisor[-1] == 1, "nonconstant monic divisor required")
    require(modulus is None or modulus >= 2, "modulus must be at least 2")
    out = trim(poly if modulus is None else [x % modulus for x in poly])
    degree = len(divisor) - 1
    quotient = [0] * max(0, len(out) - degree)
    for i in range(len(out) - 1, degree - 1, -1):
        lead = out[i]
        quotient[i - degree] = lead
        for j in range(degree + 1):
            out[i - degree + j] -= lead * divisor[j]
            if modulus is not None:
                out[i - degree + j] %= modulus
    return trim(quotient), trim(out[:degree])


def remainder(poly, divisor, modulus):
    out = divide_monic(poly, divisor, modulus)[1]
    return out + [0] * (len(divisor) - 1 - len(out))


def mulmod(left, right, divisor, modulus):
    return remainder(multiply(left, right), divisor, modulus)


def phi(k):
    require(k >= 2, "k must be at least 2")
    return [-1] * k + [1]


def prefix_powers(exponent, shift, divisor, modulus, visit=None):
    """Read bits left to right: (e,U,V) -> (2e+b,U^2 X^b,V^2 (X+a)^b)."""
    require(exponent >= 0, "negative exponent")
    u = remainder([1], divisor, modulus)
    v = u[:]
    e = 0
    for bit in bin(exponent)[2:]:
        u = mulmod(u, u, divisor, modulus)
        v = mulmod(v, v, divisor, modulus)
        if bit == "1":
            u = mulmod(u, [0, 1], divisor, modulus)
            v = mulmod(v, [shift, 1], divisor, modulus)
        e = 2 * e + int(bit)
        if visit is not None:
            visit(e, u, v)
    return u, v


def observation(n, divisor, a=1):
    u, v = prefix_powers(n, a, divisor, n)
    v[0] -= a
    return [(y - x) % n for x, y in zip(u, v)]


def matmul(left, right, modulus):
    columns = list(zip(*right))
    return [[sum(x * y for x, y in zip(row, col)) % modulus
             for col in columns] for row in left]


def matrix_power_vector(exponent, shift, divisor, modulus):
    """Independent right-to-left companion-matrix powering, applied to 1."""
    k = len(divisor) - 1
    base = [[0] * k for _ in range(k)]
    for i in range(k - 1):
        base[i + 1][i] = 1
    for i in range(k):
        base[i][-1] = -divisor[i] % modulus
        base[i][i] = (base[i][i] + shift) % modulus
    vector = [1] + [0] * (k - 1)
    while exponent:
        if exponent & 1:
            vector = [sum(x * y for x, y in zip(row, vector)) % modulus
                      for row in base]
        exponent >>= 1
        if exponent:
            base = matmul(base, base, modulus)
    return vector


def matrix_observation(n, divisor, a=1):
    u = matrix_power_vector(n, 0, divisor, n)
    v = matrix_power_vector(n, a, divisor, n)
    return [(y - x - (a if i == 0 else 0)) % n
            for i, (x, y) in enumerate(zip(u, v))]


def binomial_power(n, a):
    return [math.comb(n, j) * a ** (n - j) for j in range(n + 1)]


def direct_defect(n, a=1):
    out = binomial_power(n, a)
    out[n] -= 1
    out[0] -= a
    return trim(out)


def substitute_mirror(poly):
    """Exact coefficients of poly(-1-X), without modular reduction."""
    out = [0] * len(poly)
    for j, value in enumerate(poly):
        for i in range(j + 1):
            out[i] += value * (-1) ** j * math.comb(j, i)
    return trim(out)


def least_factor(n):
    for d in range(2, math.isqrt(n) + 1):
        if n % d == 0:
            return d
    return n


def prime_trial(n):
    return n >= 2 and least_factor(n) == n


def sieve(limit):
    primes = bytearray(b"\x01") * (limit + 1)
    primes[:2] = b"\x00\x00"
    for p in range(2, math.isqrt(limit) + 1):
        if primes[p]:
            primes[p * p:limit + 1:p] = b"\x00" * ((limit - p * p) // p + 1)
    return primes


def fixtures():
    large = 727993807201
    cases = [(4181, 2, 1), (4181, 2, 2), (4181, 3, 1),
             (large, 2, 1), (large, 3, 1), (large, 4, 1)]
    vectors = []
    for n, k, a in cases:
        vector = observation(n, phi(k), a)
        require(vector == matrix_observation(n, phi(k), a), "fixture matrix mismatch")
        vectors.append({"n": n, "k": k, "a": a, "remainder": vector})
    require(vectors[0]["remainder"] == [0, 0], "4181 k2 a1 mismatch")
    require(vectors[1]["remainder"] == [2453, 3317], "4181 k2 a2 mismatch")
    require(any(vectors[2]["remainder"]), "4181 k3 unexpectedly zero")
    require(vectors[3]["remainder"] == [0, 0], "large k2 mismatch")
    require(vectors[4]["remainder"] == [0, 0, 0], "large k3 mismatch")
    require(vectors[5]["remainder"][0] == 119234756168, "large k4 constant mismatch")
    factors = [4951, 9901, 14851]
    roots = [[[2089, 2863], [132, 820, 4000]],
             [[223, 9679], [5236, 6716, 7851]],
             [[273, 14579], [6774, 9046, 13883]]]
    require(37 * 113 == 4181 and prime_trial(37) and prime_trial(113), "4181 factors")
    require(math.prod(factors) == large and len(set(factors)) == 3, "large factors")
    require(math.gcd(large, 5040) == 1, "gcd mismatch")
    certificates = []
    for q, lists in zip(factors, roots):
        require(prime_trial(q) and (large - 1) % (q - 1) == 0, "prime/exponent failure")
        factorizations = []
        for k, rs in zip((2, 3), lists):
            require(len(set(rs)) == k and all(0 <= r < q for r in rs), "root distinctness")
            product = [1]
            for r in rs:
                require(sum(c * pow(r, i, q) for i, c in enumerate(phi(k))) % q == 0,
                        "not a root")
                product = [c % q for c in multiply(product, [-r, 1])]
            require(product == [c % q for c in phi(k)], "factorization mismatch")
            factorizations.append({"k": k, "roots": rs, "product": product})
        certificates.append({"q": q, "trial_division_through": math.isqrt(q),
                             "N_minus_1_over_q_minus_1": (large - 1) // (q - 1),
                             "factorizations": factorizations})
    return {"vectors": vectors, "4181_factors": [37, 113], "N": large,
            "N_factors": factors, "gcd_N_5040": 1, "certificates": certificates,
            "scope": "finite exact certificates; universal-shift inference is explained in README"}


def arithmetic_checks():
    moduli = [2, 4, 6, 9, 11, 35]
    divisors = [[0, 1], [3, -2, 1], [0, 0, 1], [4, 0, -3, 1]] + [phi(k) for k in range(2, 9)]
    counts = {"prefix_states": 0, "direct_binomial_cases": 0, "mirror_cases": 0,
              "adjacent_crt_cases": 0, "division_reconstructions": 0}
    for modulus in moduli:
        for divisor in divisors:
            for a in [-3, 0, 1, 2]:
                def visit(e, u, v):
                    require(u == matrix_power_vector(e, 0, divisor, modulus), "prefix U")
                    require(v == matrix_power_vector(e, a, divisor, modulus), "prefix V")
                    counts["prefix_states"] += 1
                for exponent in [0, 1, 2, 3, 5, 10, 21]:
                    u, v = prefix_powers(exponent, a, divisor, modulus, visit)
                    require(v == remainder(binomial_power(exponent, a), divisor, modulus), "binomial power")
                    require(u == remainder([0] * exponent + [1], divisor, modulus), "monomial power")
    for n in range(2, 36):
        for divisor in divisors:
            for a in range(-2, 4):
                value = observation(n, divisor, a)
                require(value == remainder(direct_defect(n, a), divisor, n), "direct defect")
                require(value == matrix_observation(n, divisor, a), "matrix defect")
                counts["direct_binomial_cases"] += 1
            if n % 2:
                mirror = [(-1) ** (len(divisor) - 1) * c for c in substitute_mirror(divisor)]
                require(mirror[-1] == 1, "mirror monicity")
                require(substitute_mirror(substitute_mirror(divisor)) == divisor, "mirror involution")
                value = observation(n, mirror)
                expected = remainder(substitute_mirror(observation(n, divisor)), mirror, n)
                require(value == expected, "mirror remainder coefficients")
                require(value == remainder(direct_defect(n), mirror, n), "mirror direct defect")
                counts["mirror_cases"] += 1
    examples = []
    for modulus in moduli:
        for k in range(2, 9):
            p, q = phi(k), phi(k + 1)
            xp = multiply([0, 1], p)
            require(add(xp, q, -1) == [1], "adjacent Bezout")
            product = multiply(p, q)
            sources = [[0], [3, -7, 2], [(-1) ** i * (i * i + 3) for i in range(3 * k + 5)]]
            for source in sources:
                left, right = remainder(source, p, modulus), remainder(source, q, modulus)
                rebuilt = remainder(add(multiply(right, xp), multiply(left, q), -1), product, modulus)
                require(rebuilt == remainder(source, product, modulus), "CRT reconstruction")
                require(remainder(rebuilt, p, modulus) == left, "CRT left")
                require(remainder(rebuilt, q, modulus) == right, "CRT right")
                counts["adjacent_crt_cases"] += 1
                quotient, rest = divide_monic(source, p)
                require(add(multiply(quotient, p), rest) == trim(source), "integer division")
                counts["division_reconstructions"] += 1
                if k == 2 and len(source) > 3:
                    examples.append({"modulus": modulus, "source": source,
                                     "left": left, "right": right, "reconstructed": rebuilt})
    return {"counts": counts, "moduli": moduli, "divisors": divisors,
            "prefix_exponents": [0, 1, 2, 3, 5, 10, 21], "prefix_shifts": [-3, 0, 1, 2],
            "direct_n_inclusive": [2, 35], "direct_a_inclusive": [-2, 3], "crt_examples": examples}


def reduced_checks():
    records = []
    composites = odd = units = 0
    for n in range(4, 302):
        p = least_factor(n)
        if p == n:
            continue
        composites += 1
        delta = trim([c % n for c in direct_defect(n)])
        require(len(delta) - 1 == n - p and all(c == 0 for c in delta[:p]), "degree/X^p failure")
        factor = [0] * p + [1]
        expected_degree = n - 2 * p
        if n % 2:
            odd += 1
            factor = [0] * p + binomial_power(p, 1)
            expected_degree = n - 3 * p
            for k in range(2, 9):
                at_zero, at_minus_one = phi(k)[0], sum(c * (-1) ** i for i, c in enumerate(phi(k)))
                require(at_zero == -1 and at_minus_one in (1, -2), "Phi values")
                require(math.gcd(at_zero, n) == math.gcd(at_minus_one, n) == 1, "Phi units")
                units += 1
        quotient, rest = divide_monic(delta, factor, n)
        require(not rest and len(quotient) - 1 == expected_degree, "reduced division failure")
        rebuilt = trim([c % n for c in multiply(factor, quotient)])
        require(rebuilt == delta, "reduced reconstruction failure")
        if n in [4, 9, 15, 25, 27, 49, 81, 121, 143, 169, 225, 289, 301]:
            records.append({"n": n, "p": p, "delta_degree": len(delta) - 1,
                            "factor_degree": len(factor) - 1, "reduced_degree": len(quotient) - 1})
    return {"n_inclusive": [4, 301], "composites": composites, "odd_composites": odd,
            "unit_checks": units, "examples": records,
            "scope": "bounded checks of parent-supplied claims; no general theorem or bound inferred"}


def boundary_checks():
    """Finite checks of the extra structural deductions and inverse counterexample."""
    distance_two = []
    for k in range(2, 11):
        value = add(multiply([0, 0, 1], phi(k)), phi(k + 2), -1)
        require(value == [1, 1], "distance-two identity")
        distance_two.append({"k": k, "difference": value})
    n, divisor = 561, [0, 0, 1]
    for a in range(n):
        value = observation(n, divisor, a)
        require(value == matrix_observation(n, divisor, a) == [0, 0], "561 affine counterexample")
    require(matrix_power_vector(n, 0, divisor, n) == [0, 0], "nilpotent power")
    require(remainder([0, 1], divisor, n) == [0, 1], "nonzero nilpotent")
    common_root_values = [sum(c * 3 ** i for i, c in enumerate(phi(k))) for k in (2, 6)]
    require(common_root_values == [5, 365], "nonadjacent root certificate")
    return {"distance_two_identities": distance_two,
            "all_shift_counterexample": {"n": n, "P": divisor, "residue_classes_checked": n,
                                         "X": [0, 1], "X_power_n": [0, 0]},
            "nonadjacent": {"modulus": 15, "prime_quotient": 5, "root": 3,
                            "k": [2, 6], "integer_evaluations": common_root_values},
            "scope": "finite arithmetic checks; general structural proofs are in theory sections 305-306"}


def scan(limit):
    primes = sieve(limit)
    require(all(bool(primes[n]) == prime_trial(n) for n in range(2, limit + 1)), "sieve/trial mismatch")
    distribution = {str(k): 0 for k in range(2, 9)}
    survivors, exceptions = [], []
    prime_count = comparisons = even_composites = 0
    digest = hashlib.sha256()
    for n in range(4, limit + 1):
        depth = None
        for k in range(2, 9):
            value = observation(n, phi(k))
            require(value == matrix_observation(n, phi(k)), "scan matrix mismatch")
            comparisons += 1
            digest.update((json.dumps([n, k, value], separators=(",", ":")) + "\n").encode("ascii"))
            if any(value):
                depth = k
                break
        if primes[n]:
            prime_count += 1
            require(depth is None, "prime with nonzero defect")
        else:
            bound = max(2, n // 3 - 1)
            require((depth is not None and depth <= bound) or (depth is None and bound > 8),
                    "composite violates the proposed uniform bound in tested range")
            if n % 2 == 0:
                require(depth == 2, "even composite survives Phi2")
                even_composites += 1
            if depth is None:
                survivors.append(n)
            else:
                distribution[str(depth)] += 1
                if depth > 2:
                    exceptions.append({"n": n, "d": depth, "first_nonzero_remainder": value})
    return {"n_inclusive": [4, limit], "a": 1, "k_inclusive": [2, 8],
            "integers": limit - 3, "primes": prime_count, "composites": limit - 3 - prime_count,
            "composite_first_nonzero_k_distribution": distribution,
            "composites_unresolved_above_8": survivors, "composite_depth_above_2": exceptions,
            "prime_cases_zero_through_8": prime_count, "matrix_comparisons": comparisons,
            "even_composites_at_depth_2": even_composites,
            "uniform_bound_checked": "d(n) <= max(2, floor(n/3)-1); only queried depths are certified",
            "remainder_stream_sha256": digest.hexdigest(),
            "scope": "finite window only; composites stop at first nonzero k; primes tested through 8; no global depth bound"}


def report(limit):
    return {"schema_version": 1, "convention": "constant-first coefficients, residues in [0,n)",
            "fixtures": fixtures(), "arithmetic_checks": arithmetic_checks(),
            "reduced_defect_checks": reduced_checks(), "boundary_checks": boundary_checks(),
            "scan": scan(limit)}


def encode(data):
    # One top-level field per line keeps nested numerical records together.
    return "{\n" + ",\n".join("  " + json.dumps(k) + ": " + json.dumps(v, sort_keys=True)
                              for k, v in sorted(data.items())) + "\n}\n"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--n", type=int, help="compute one observation (n >= 2)")
    parser.add_argument("--k", type=int, help="Phi degree (k >= 2), with --n")
    parser.add_argument("--a", type=int, help="integer shift (default 1), with --n")
    parser.add_argument("--scan-max", type=int, help="inclusive upper endpoint (default 20000)")
    parser.add_argument("--output", type=Path, help="write deterministic results here")
    parser.add_argument("--check", nargs="?", const=Path(__file__).with_name("results.json"),
                        type=Path, help="recompute and compare saved JSON (default sibling results.json)")
    args = parser.parse_args()
    if args.n is not None:
        if (args.n < 2 or args.k is None or args.k < 2 or args.check or args.output
                or args.scan_max is not None):
            parser.error("single-case mode requires --n >= 2 --k >= 2 and no report options")
        a = 1 if args.a is None else args.a
        value = observation(args.n, phi(args.k), a)
        require(value == matrix_observation(args.n, phi(args.k), a), "CLI matrix mismatch")
        print(json.dumps({"n": args.n, "k": args.k, "a": a, "remainder": value, "matrix_agrees": True}))
        return
    if args.k is not None or args.a is not None or (args.check and args.output):
        parser.error("--k/--a require --n; --check and --output are exclusive")
    saved = json.loads(args.check.read_text()) if args.check else None
    limit = args.scan_max if args.scan_max is not None else (saved["scan"]["n_inclusive"][1] if saved else 20000)
    if limit < 4:
        parser.error("--scan-max must be >= 4")
    result = report(limit)
    if saved is not None:
        require(result == saved, "saved results differ from recomputation")
        print(json.dumps({"check": "passed", "n_inclusive": [4, limit],
                          "matrix_comparisons": result["scan"]["matrix_comparisons"]}))
    elif args.output:
        args.output.write_text(encode(result), encoding="utf-8")
        print(json.dumps(result["scan"], sort_keys=True))
    else:
        print(encode(result), end="")


if __name__ == "__main__":
    main()
