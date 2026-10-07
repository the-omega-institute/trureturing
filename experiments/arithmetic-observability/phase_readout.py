"""Search exact two-norm observation fibers on declared finite source sets.

Rational and prime-field arithmetic are exact. Finite searches are not proofs
of all-state recovery. License: Apache-2.0 under the repository LICENSE.
"""
import argparse
from fractions import Fraction
import json
from math import isqrt
from pathlib import Path
import sys


def _prime(p):
    return type(p) is int and p >= 2 and all(p % d for d in range(2, isqrt(p) + 1))


def analyze(model):
    """Group actual states by squared norm before and after the same update."""
    if not isinstance(model, dict):
        raise ValueError("model must be an object")
    matrix, states = model.get("matrix"), model.get("states")
    if (not isinstance(matrix, list) or len(matrix) != 2
            or any(not isinstance(row, list) or len(row) != 2 for row in matrix)):
        raise ValueError("matrix must be a two-by-two array")
    if (not isinstance(states, list) or not states
            or any(not isinstance(x, list) or len(x) != 2 for x in states)):
        raise ValueError("states must be a nonempty array of pairs")
    modulus = model.get("modulus")
    if modulus is not None and not _prime(modulus):
        raise ValueError("modulus must be prime")

    def parse(x):
        if not isinstance(x, str):
            raise ValueError("coordinates and matrix entries must be rational strings")
        try:
            value = Fraction(x)
        except (ValueError, ZeroDivisionError) as error:
            raise ValueError("invalid rational string") from error
        if modulus is None:
            return value
        if value.denominator % modulus == 0:
            raise ValueError("denominator is zero in the prime field")
        return value.numerator * pow(value.denominator, -1, modulus) % modulus

    def norm(x):
        value = x[0]*x[0] + x[1]*x[1]
        return value if modulus is None else value % modulus

    def neg(x):
        return tuple(-z if modulus is None else -z % modulus for z in x)

    a = [tuple(map(parse, row)) for row in matrix]
    points = [tuple(map(parse, point)) for point in states]
    if len(set(points)) != len(points):
        raise ValueError("source states must be distinct in the declared field")
    r, s, t = (a[0][0]**2+a[1][0]**2,
               a[0][0]*a[0][1]+a[1][0]*a[1][1],
               a[0][1]**2+a[1][1]**2)
    delta = (r-t)**2+4*s*s
    if modulus is not None:
        delta %= modulus
    buckets = {}
    for x in points:
        updated = tuple(row[0]*x[0]+row[1]*x[1] for row in a)
        signature = (norm(x), norm(updated))
        buckets.setdefault(signature, []).append(x)
    extra = 0
    witness = None
    for signature, block in buckets.items():
        first = block[0]
        other = next((x for x in block if x != first and x != neg(first)), None)
        if other is None:
            continue
        extra += 1
        if witness is None:
            witness = {"pair": [list(map(str, first)), list(map(str, other))],
                       "readout": list(map(str, signature))}
    return {"states": len(points), "discriminant": str(delta),
            "readout_buckets": len(buckets),
            "maximum_bucket_size": max(map(len, buckets.values())),
            "extra_collision_buckets": extra, "collision": witness}


def finite_model(modulus):
    if not _prime(modulus):
        raise ValueError("modulus must be prime")
    return {"matrix": [["0", "1"], ["1", "1"]], "modulus": modulus,
            "states": [[str(a), str(b)] for a in range(modulus) for b in range(modulus)]}


def pell_rows(count):
    """Exact rational near-collisions from the unit 9+4√5; no floating roots."""
    if type(count) is not int or count < 1:
        raise ValueError("count must be positive")
    p, q = 1, 0
    rows = []
    for n in range(1, count + 1):
        p, q = 9*p+20*q, 4*p+9*q
        if p*p-5*q*q != 1 or p < 9**n:
            raise ValueError("Pell invariant or growth failed")
        y = (-Fraction(q, p), 2*Fraction(q, p))
        e0 = y[0]**2+y[1]**2
        e1 = y[1]**2+(y[0]+y[1])**2
        error = Fraction(1, p*p)
        gap = 1-y[0]**2
        if e0 != e1 or 1-e0 != error or gap <= Fraction(4, 5):
            raise ValueError("near-collision identity failed")
        rows.append({"index": n, "p": p, "q": q,
                     "state": list(map(str, y)), "readout": [str(e0), str(e1)],
                     "readout_error": str(error), "target_gap": str(gap)})
    return rows


def default_results():
    lattice = [[str(a), str(b)] for a in range(-6, 7) for b in range(-6, 7)]
    models = {"fib_rational_lattice": {"matrix": [["0", "1"], ["1", "1"]],
                                        "states": lattice},
              "diagonal_rational_lattice": {"matrix": [["1", "0"], ["0", "2"]],
                                             "states": lattice}}
    models.update({f"fib_prime_{p}": finite_model(p) for p in (2, 3, 5, 7, 11, 13, 17, 19)})
    return {"models": {name: {"model": model, "result": analyze(model)}
                       for name, model in models.items()}, "pell_near_collisions": pell_rows(8)}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--input", type=Path, help="declared matrix and finite source set as JSON")
    args = parser.parse_args()
    if args.input:
        model = json.loads(args.input.read_text())
        result = {"model": model, "result": analyze(model)}
    else:
        result = default_results()
    json.dump(result, sys.stdout, indent=2, sort_keys=True)
    sys.stdout.write("\n")


if __name__ == "__main__":
    main()
