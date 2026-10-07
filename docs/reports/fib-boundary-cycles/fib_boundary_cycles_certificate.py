#!/usr/bin/env python3
"""Exact certificates consumed by the FIB seams/cycles continuation.

Run: python3 docs/reports/fib-boundary-cycles/fib_boundary_cycles_certificate.py
An optional --output PATH writes the same canonical JSON to another location.
Only Python's standard library is used; no float enters an assertion.

Arithmetic: integer matrices, explicit bit enumeration, Fraction divisor sums,
20-term atanh logarithms with a proved positive remainder, H_1024 gamma
bracket, and rational outward rounding at every interval operation to 10^-30.
The Robin upper certificate uses only 10080, 20160 and 30240; 60480 is an
additional comparison after that certificate has been constructed.

Provenance: reconstructed mathematical inputs, not retrieved sandbox assets.
Native supplier: trureturing snapshot 78d2f7c423b15d01062f3ffacf4f75b8cee44f30,
FIBONACCI_ATOMIC_RELATION_GENERATION §§3, 104, 141.1, 149.4, 237, equation 367.5;
ZECKENDORF_EULER_5040 equation (22), Theorems 4.1/5.1, absolute anchor §9.1.
Literature scope is documented in the manuscript and consumed Library notes.
"""

import argparse
from dataclasses import dataclass
from fractions import Fraction as F
from itertools import product
from math import comb, isqrt, prod
from pathlib import Path
import json

SNAPSHOT = "78d2f7c423b15d01062f3ffacf4f75b8cee44f30"
GRID = 10**30
LOG_TERMS = 20
GAMMA_M = 1024
SEQUENCES = [[0], [1], [2], [3], [1, 2], [0, 3], [2, 2],
             [1, 1, 1], [1, 2, 3], [3, 0, 2], [1, 2, 0, 3],
             [2, 1, 3, 0, 2]]
I2 = ((1, 0), (0, 1))


def mm(a, b):
    return tuple(tuple(sum(a[i][k] * b[k][j] for k in range(2))
                       for j in range(2)) for i in range(2))


def det(a):
    return a[0][0] * a[1][1] - a[0][1] * a[1][0]


def trace(a):
    return a[0][0] + a[1][1]


def B(t):
    return ((1, t), (1, 0))


def chain(ts):
    a = I2
    for t in ts:
        a = mm(a, B(t))
    return a


def legal(bits, cyclic=False):
    if any(a * b for a, b in zip(bits, bits[1:])):
        return False
    return not cyclic or not bits or not bits[-1] * bits[0]


def weight(bits, ts):
    return prod(t for t, b in zip(ts, bits) if b)


def enumerate_kernel(ts):
    a = [[0, 0], [0, 0]]
    for bits in product((0, 1), repeat=len(ts)):
        if legal(bits):
            for incoming in (0, 1):
                if not incoming * bits[0]:
                    a[incoming][bits[-1]] += weight(bits, ts)
    return tuple(tuple(row) for row in a)


def supported_coefficients(ts, incoming, outgoing):
    return {bits: weight(bits, ts)
            for bits in product((0, 1), repeat=3)
            if legal(bits) and not incoming * bits[0]
            and bits[-1] == outgoing}


def parity(eta, bits):
    return (-1) ** sum(a * b for a, b in zip(eta, bits))


def five_mode_certificate():
    records = []
    signs = list(product((0, 1), repeat=3))
    for ts in product(range(4), repeat=3):
        x, y, z = ts
        explicit = ((1 + x + y, z + x * z), (1 + y, z))
        a = enumerate_kernel(ts)
        assert a == chain(ts) == explicit
        assert det(a) == -x * y * z
        # Chronological native order is (b5,b3,b2), with weights (z,y,x).
        native = enumerate_kernel(ts[::-1])
        assert native == chain(ts[::-1])
        energies = []
        for incoming, outgoing in product((0, 1), repeat=2):
            coeff = supported_coefficients(ts, incoming, outgoing)
            values = {eta: enumerate_kernel(tuple(t * (-1)**e
                      for t, e in zip(ts, eta)))[incoming][outgoing]
                      for eta in signs}
            recovered = {bits: F(sum(values[e] * parity(e, bits)
                         for e in signs), 8) for bits in signs}
            assert all(recovered[b] == coeff.get(b, 0) for b in signs)
            energy = F(sum(v*v for v in values.values()), 8)
            assert energy == sum(c*c for c in coeff.values())
            energies.append(int(energy))
        records.append({"weights": ts, "kernel": a, "native_kernel": native,
                        "determinant": det(a), "phase_squared_means": energies})
    # U and V are different legal singleton masks with equal common phase.
    collision = {"mask_u": [1, 0, 0], "mask_v": [0, 1, 0],
                 "common_phase_equal": True, "independent_sign_eta": [1, 0, 0],
                 "independent_values": [-1, 1],
                 "guarded_weight_cases": [[1, 0, 0], [0, 1, 0]],
                 "guarded_independent_values": [0, 2]}
    assert enumerate_kernel((-1, 0, 0))[0][0] == 0
    assert enumerate_kernel((0, 1, 0))[0][0] == 2
    return {"weight_values": [0, 1, 2, 3], "triples": records,
            "triple_count": len(records), "phase_polynomials": 4*len(records),
            "phase_grid_size": 8, "common_phase_collision": collision}


def weighted_readouts():
    records = []
    for ts in SEQUENCES:
        a = chain(ts)
        words = list(product((0, 1), repeat=len(ts)))
        op = sum(weight(w, ts) for w in words if legal(w))
        cy = sum(weight(w, ts) for w in words if legal(w, True))
        assert op == sum(a[0]) and cy == trace(a)
        # Full-chain reversal preserves weights and legality, not prefixes.
        assert op == sum(chain(ts[::-1])[0])
        assert cy == trace(chain(ts[::-1]))
        records.append({"weights": ts, "kernel": a,
                        "open_weight": op, "cycle_weight": cy})
    assert sum(I2[0]) == 1 and trace(I2) == 2
    return {"cases": records, "case_count": len(records),
            "empty_open_weight": 1, "trace_identity_algebraic": 2,
            "empty_cycle_defined": False}


def divisors(n):
    low, high = [], []
    for d in range(1, isqrt(n) + 1):
        if n % d == 0:
            low.append(d)
            if d*d != n:
                high.append(n//d)
    return low + high[::-1]


def mu(n):
    sign = 1
    p = 2
    while p*p <= n:
        if n % p == 0:
            n //= p
            sign = -sign
            if n % p == 0:
                return 0
        p += 1
    return -sign if n > 1 else sign


def lucas_list(n):
    c = [2, 1]
    for _ in range(2, n+1):
        c.append(c[-1] + c[-2])
    return c


def primitive_word_counts():
    c = lucas_list(16)
    records, ps, ars = [], [0]*17, [0]*17
    total = 0
    for n in range(1, 17):
        ds = divisors(n)
        period_counts = {d: 0 for d in ds}
        orbits = set()
        open_count = 0
        for w in product((0, 1), repeat=n):
            total += 1
            open_count += int(legal(w))
            if not legal(w, True):
                continue
            d = next(d for d in ds if all(w[i] == w[i % d] for i in range(n)))
            period_counts[d] += 1
            if d == n:
                orbits.add(min(w[j:] + w[:j] for j in range(n)))
        ps[n] = period_counts[n]
        ars[n] = len(orbits)
        assert sum(period_counts.values()) == c[n] == trace(chain([1]*n))
        assert ps[n] == sum(mu(d)*c[n//d] for d in ds)
        assert ps[n] == n*ars[n]
        assert all(period_counts[d] == ps[d] for d in ds)
        records.append({"length": n, "all_binary_words": 2**n,
                        "open_count": open_count, "cycle_count": c[n],
                        "primitive_marked_count": ps[n],
                        "primitive_rotation_orbits": ars[n],
                        "minimal_period_counts": {str(d): period_counts[d] for d in ds}})
    assert total == 131070
    euler = [1] + [0]*16
    for d in range(1, 17):
        a = ars[d]
        if not a:
            continue
        factor = [0]*17
        for k in range(16//d+1):
            factor[k*d] = comb(a+k-1, k)
        euler = [sum(euler[j]*factor[i-j] for j in range(i+1))
                 for i in range(17)]
    recurrence = [1, 1]
    for _ in range(2, 17):
        recurrence.append(recurrence[-1] + recurrence[-2])
    assert euler == recurrence
    t, cutoff, r = F(1, 4), 16, F(13, 32)
    assert F(13, 8)**2-F(13, 8)-1 > 0  # phi < 13/8
    head = sum(F(c[n], n)*t**n for n in range(1, cutoff+1))
    tail = 2*r**(cutoff+1)/((cutoff+1)*(1-r))
    return {"lengths": records, "binary_words_examined": total,
            "euler_coefficients_degree_0_to_16": euler,
            "rational_zeta_coefficients_degree_0_to_16": recurrence,
            "log_zeta_tail_example": {"t": frac(t), "cutoff": cutoff,
              "rational_dominating_r": frac(r), "head": frac(head),
              "absolute_tail_upper": frac(tail)}}


def z_by_divisors(n):
    return sum((F(1, d) for d in divisors(n)), F(0))


def z_by_prime_factors(n):
    answer, p = F(1), 2
    while p*p <= n:
        exponent = 0
        while n % p == 0:
            exponent += 1
            n //= p
        if exponent:
            answer *= sum((F(1, p**j) for j in range(exponent+1)), F(0))
        p += 1
    if n > 1:
        answer *= 1 + F(1, n)
    return answer


def mobius_5040():
    c = lucas_list(5040)
    terms = []
    for d in divisors(210):
        m = 5040//d
        z = z_by_divisors(m)
        assert z == z_by_prime_factors(m)
        terms.append({"squarefree_divisor": d, "mu": mu(d),
                      "cycle_length": m, "cycle_count": str(c[m]),
                      "reciprocal_divisor_sum": frac(z),
                      "signed_reciprocal_term": frac(mu(d)*z)})
    p = sum(row["mu"]*int(row["cycle_count"]) for row in terms)
    atom = sum((parse_frac(row["signed_reciprocal_term"]) for row in terms), F(0))
    assert len(terms) == 16 and p > 0 and p % 5040 == 0
    assert atom == F(1, 5040)
    z = z_by_divisors(5040)
    assert z == F(403, 105) and len(divisors(5040)) == 60
    return {"factorization": {"2": 4, "3": 2, "5": 1, "7": 1},
            "radical": 210, "divisor_count": 60,
            "Z_5040": frac(z), "terms": terms, "nonzero_terms": len(terms),
            "P_5040": str(p), "primitive_unmarked_5040": str(p//5040),
            "reciprocal_atom": frac(atom)}


def frac(q):
    q = F(q)
    return {"numerator": str(q.numerator), "denominator": str(q.denominator)}


def parse_frac(q):
    return F(int(q["numerator"]), int(q["denominator"]))


def floor_grid(q):
    return F((q.numerator*GRID)//q.denominator, GRID)


def ceil_grid(q):
    return -floor_grid(-q)


@dataclass(frozen=True)
class Interval:
    lo: F
    hi: F

    @staticmethod
    def enclose(lo, hi=None):
        lo = F(lo)
        hi = lo if hi is None else F(hi)
        assert lo <= hi
        return Interval(floor_grid(lo), ceil_grid(hi))

    def __add__(self, other):
        other = as_interval(other)
        return Interval.enclose(self.lo+other.lo, self.hi+other.hi)

    def __neg__(self):
        return Interval.enclose(-self.hi, -self.lo)

    def __sub__(self, other):
        return self + -as_interval(other)

    def __mul__(self, other):
        other = as_interval(other)
        vals = [a*b for a in (self.lo, self.hi) for b in (other.lo, other.hi)]
        return Interval.enclose(min(vals), max(vals))

    def __truediv__(self, other):
        other = as_interval(other)
        assert not other.lo <= 0 <= other.hi
        inv = Interval.enclose(1/other.hi, 1/other.lo)
        return self * inv

    def data(self):
        return {"lower": frac(self.lo), "upper": frac(self.hi)}


def as_interval(q):
    return q if isinstance(q, Interval) else Interval.enclose(q)


def unit_log_bounds(q):
    """For 1 <= q <= 2: L20 <= log q <= L20 + R20, exactly."""
    assert 1 <= q <= 2
    r = (q-1)/(q+1)
    partial = 2*sum((r**(2*j+1)/F(2*j+1) for j in range(LOG_TERMS)), F(0))
    remainder = 2*r**(2*LOG_TERMS+1)/(F(2*LOG_TERMS+1)*(1-r*r))
    return Interval.enclose(partial, partial+remainder)


LOG2 = unit_log_bounds(F(2))


def log_point(q):
    """Scale rational q=2^k*m with 1<=m<2; k may be negative."""
    q = F(q)
    assert q > 0
    k = 0
    while q >= 2:
        q /= 2
        k += 1
    while q < 1:
        q *= 2
        k -= 1
    return LOG2*k + unit_log_bounds(q)


def log_interval(q):
    q = as_interval(q)
    assert q.lo > 0
    return Interval.enclose(log_point(q.lo).lo, log_point(q.hi).hi)


def triple_logs(n):
    x = log_point(F(n))
    assert x.lo > 1
    y = log_interval(x)
    assert y.lo > 0
    f = log_interval(y)
    return x, y, f


def robin_certificate():
    harmonic = sum((F(1, j) for j in range(1, GAMMA_M+1)), F(0))
    lm = log_point(F(GAMMA_M))
    # 0 < H_m-log(m)-gamma < 1/m, from a telescoping positive series.
    gamma = Interval.enclose(harmonic-lm.hi-F(1, GAMMA_M), harmonic-lm.lo)
    expected = {10080: F(39, 10), 20160: F(1651, 420),
                30240: F(4), 60480: F(254, 63)}
    zs = {n: z_by_divisors(n) for n in expected}
    assert zs == expected
    assert all(zs[n] == z_by_prime_factors(n) for n in zs)
    base_logs = {n: triple_logs(n) for n in [10080, 20160, 30240]}
    x, y, _ = base_logs[10080]
    h = (y+1)/(x*x*y*y)
    a, b = log_point(F(2)), log_point(F(3))
    budget = h*a*b
    ratio = zs[20160]*zs[30240]/zs[10080]
    # Collect shared gamma once, before any signed interval operations.
    edges = (log_point(ratio)-gamma-base_logs[20160][2]
             -base_logs[30240][2]+base_logs[10080][2])
    upper_expression = edges + budget
    threshold = F(-55, 1000)
    assert upper_expression.hi < threshold
    # Only now evaluate the target for a separate upper-relation check.
    target_logs = triple_logs(60480)
    rectangle = (base_logs[20160][2]+base_logs[30240][2]
                 -base_logs[10080][2]-target_logs[2])
    assert rectangle.lo > 0 and rectangle.hi < budget.lo
    assert ratio == zs[60480]  # distinct-axis log Z separability
    records = {}
    for n in [10080, 20160, 30240, 60480]:
        logs = target_logs if n == 60480 else base_logs[n]
        g = log_point(zs[n])-gamma-logs[2]
        records[str(n)] = {"Z": frac(zs[n]), "log_n": logs[0].data(),
                           "loglog_n": logs[1].data(),
                           "logloglog_n": logs[2].data(), "G": g.data()}
    # A short human-readable outward interval, obtained by integer division.
    display_scale = 10**6
    display_lo = F((upper_expression.lo*display_scale).__floor__(), display_scale)
    display_hi = F(-(-upper_expression.hi*display_scale).__floor__(), display_scale)
    assert upper_expression.hi <= display_hi < threshold
    return {"arithmetic": {"grid_denominator": str(GRID), "log_terms": LOG_TERMS,
              "gamma_harmonic_index": GAMMA_M, "gamma_remainder_bounds":
              [frac(0), frac(F(1, GAMMA_M))], "harmonic_number": frac(harmonic)},
            "gamma": gamma.data(), "boundary_integer_values": [10080, 20160, 30240],
            "values": records, "shared_Z_ratio": frac(ratio),
            "h_log10080": h.data(), "log2": a.data(), "log3": b.data(),
            "pair_area_upper_budget": budget.data(), "signed_boundary": edges.data(),
            "upper_expression_U": upper_expression.data(),
            "short_outward_U": {"lower": frac(display_lo), "upper": frac(display_hi)},
            "strict_threshold": frac(threshold),
            "positive_rectangle_correction": rectangle.data(),
            "rectangle_below_pair_budget": True,
            "target_evaluated_after_boundary_certificate": True}


def certificate():
    corner_kernels = [enumerate_kernel(ts) for ts in product((0, 1), repeat=3)]
    integral = tuple(tuple(F(sum(a[i][j] for a in corner_kernels), 8)
                           for j in range(2)) for i in range(2))
    assert integral == ((F(2), F(3, 4)), (F(3, 2), F(1, 2)))
    assert sum(integral[0]) == F(11, 4) and trace(integral) == F(5, 2)
    return {"schema": "fib-boundary-cycles-exact-v1", "supplier_snapshot": SNAPSHOT,
            "provenance": "new reconstructed asset; original sandbox artifact not retrieved",
            "response_task": "formal factorized occupation weights; not native additive quantity",
            "five_modes": five_mode_certificate(), "weighted_readouts": weighted_readouts(),
            "cycles": primitive_word_counts(), "mobius_5040": mobius_5040(),
            "robin": robin_certificate(), "bubble_integral": frac(F(1, 6)**3),
            "corner_integral_bridge": {
              "domain": "independent occupation parameters [0,1]^3",
              "kernel_integral": [[frac(q) for q in row] for row in integral],
              "open_integral": frac(sum(integral[0])),
              "triangle_integral": frac(trace(integral))}}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path,
                        default=Path(__file__).with_suffix(".json"))
    args = parser.parse_args()
    result = certificate()
    data = (json.dumps(result, ensure_ascii=False, sort_keys=True, indent=2)+"\n").encode()
    args.output.write_bytes(data)
    print(json.dumps({"output": str(args.output), "triples": 64, "weighted_cases": 12,
      "binary_words": result["cycles"]["binary_words_examined"],
      "mobius_terms": result["mobius_5040"]["nonzero_terms"],
      "U_upper": result["robin"]["short_outward_U"]["upper"],
      "strict_threshold": result["robin"]["strict_threshold"]}, sort_keys=True))
    print("FIB_BOUNDARY_CYCLES_EXACT_CERTIFICATE_COMPLETE")


if __name__ == "__main__":
    main()
