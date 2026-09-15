"""I35: one fixed 16-node support verification; no search or sign evaluation.

Arb transcendental precision is 256 bits throughout. Interval endpoints and
all algebraic interval operations use exact Fraction arithmetic. The reporting
grid is fixed at 10^-18 before execution and is never used as an input.
"""
import json
import sys
from fractions import Fraction as Q
import flint
from flint import arb, fmpq, ctx

PRECISION = 256
GRID = 10**18
Q_LIST = (1, 2, 3, 5, 6, 7, 10, 14, 15, 21, 30, 35, 42, 70, 105, 210)
NODES = tuple((r, Q(1058400 * Q_LIST[r]), Q(1058400 * Q_LIST[r+1]))
              for r in range(1, 15)) + (
    (23, Q(3175200), Q(17592186044416, 3175200)),
    (37, Q(7408800), Q(95367431640625, 7408800)),
)
TIGHT = (Q(3571708000370, 10**12), Q(5592595433915, 10**12))


def dyadic(x):
    m, e = x.man_exp()
    m, e = int(m), int(e)
    return Q(m * 2**e) if e >= 0 else Q(m, 2**(-e))


def endpoints(x):
    if not x.is_finite():
        raise ArithmeticError("nonfinite Arb enclosure")
    return dyadic(x.lower()), dyadic(x.upper())


def ball(q):
    return arb(fmpq(q.numerator, q.denominator))


def log_interval(q):
    assert q > 0
    return endpoints(ball(q).log())


def add(a, b):
    return a[0] + b[0], a[1] + b[1]


def sub(a, b):
    return a[0] - b[1], a[1] - b[0]


def scale(a, q):
    assert q >= 0
    return a[0] * q, a[1] * q


def maximum(*args):
    return max(a[0] for a in args), max(a[1] for a in args)


def minimum(*args):
    return min(a[0] for a in args), min(a[1] for a in args)


def square_nonnegative(a):
    assert 0 <= a[0] <= a[1]
    return a[0]**2, a[1]**2


def sqrt_nonnegative(a):
    assert 0 <= a[0] <= a[1]
    lo = endpoints(ball(a[0]).sqrt())[0]
    hi = endpoints(ball(a[1]).sqrt())[1]
    return max(Q(0), lo), hi


def grid(a):
    lo, hi = (x * GRID for x in a)
    return [lo.numerator // lo.denominator,
            -((-hi.numerator) // hi.denominator)]


def ge(a, q):
    return "proved" if a[0] >= q else "refuted" if a[1] < q else "inconclusive"


def le(a, q):
    return "proved" if a[1] <= q else "refuted" if a[0] > q else "inconclusive"


def main():
    ctx.prec = PRECISION
    c = [log_interval(Q(n)) for n in (32, 27, 25, 49)]
    d = [log_interval(Q(n)) for n in (64, 81, 125, 343)]
    rows = []
    zero = (Q(0), Q(0))
    for slot, e0, e1 in NODES:
        v, w = scale(log_interval(e0), Q(1, 4)), scale(log_interval(e1), Q(1, 4))
        delta = [minimum(maximum(sub(ci, w), sub(v, ci), zero),
                         maximum(sub(di, w), sub(v, di), zero))
                 for ci, di in zip(c, d)]
        V0 = zero
        for a in delta:
            V0 = add(V0, square_nonnegative(a))
        rho = sqrt_nonnegative(scale(V0, Q(1, 12)))
        L, H = sub(w, rho), add(w, scale(rho, Q(3)))
        comparisons = {"L_ge_tight_lower": ge(L, TIGHT[0]),
                       "L_le_tight_upper": le(L, TIGHT[1]),
                       "H_ge_tight_lower": ge(H, TIGHT[0]),
                       "H_le_tight_upper": le(H, TIGHT[1])}
        rows.append({"slot": slot, "exp_M0": [e0.numerator, e0.denominator],
                     "exp_M1": [e1.numerator, e1.denominator],
                     "delta_grid": [grid(a) for a in delta], "V0_grid": grid(V0),
                     "rho_grid": grid(rho), "L_grid": grid(L), "H_grid": grid(H),
                     "tight_comparisons": comparisons,
                     "coarse_0_lt_L_le_H_lt_14_lt_16":
                         L[0] > 0 and rho[0] >= 0 and H[1] < 14 < 16})
    verdicts = [v for row in rows for v in row["tight_comparisons"].values()]
    status = "contradicted" if "refuted" in verdicts else (
        "inconclusive" if "inconclusive" in verdicts else "certified")
    result = {"schema": "fixed5040-support-256-v1", "precision_bits": ctx.prec,
              "interpreter": sys.executable, "python_version": sys.version,
              "python_flint_version": flint.__version__,
              "flint_version": flint.__FLINT_VERSION__,
              "grid_denominator": GRID, "node_count": len(rows),
              "original_tight_numerators": [3571708000370, 5592595433915],
              "original_tight_denominator": 10**12,
              "original_tight_status": status,
              "inconclusive_comparisons": verdicts.count("inconclusive"),
              "corrected_joint_grid": [min(row["L_grid"][0] for row in rows),
                                       max(row["H_grid"][1] for row in rows)],
              "coarse_all_certified": all(row["coarse_0_lt_L_le_H_lt_14_lt_16"] for row in rows),
              "rows": rows}
    print(json.dumps(result, ensure_ascii=False, indent=2))
    return 0 if result["coarse_all_certified"] and not result["inconclusive_comparisons"] else 2


if __name__ == "__main__":
    sys.exit(main())
