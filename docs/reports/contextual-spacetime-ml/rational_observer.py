#!/usr/bin/env python3
"""Exact rational observer and generic interval certificates for ML §41.

Standard library only. Rational JSON values are [numerator, denominator], both
decimal strings, with a positive denominator; reduction is not required.
Generation and verification use fixed-depth, unreduced integer-pair arithmetic.
The verifier never calls the constructor or requires a grid-shaped certificate.
The `checks` command additionally uses fractions.Fraction as an arithmetic oracle
and unnormalised two-component Bayesian recursion as a bounded cross-check.
"""

import argparse
import copy
from dataclasses import dataclass
from fractions import Fraction
import json
from pathlib import Path
import re
import sys


class CertificateError(ValueError):
    """Malformed certificate or parameters (separate from scalar inequalities)."""


@dataclass(frozen=True)
class Q:
    n: int
    d: int = 1

    def __post_init__(self):
        if type(self.n) is not int or type(self.d) is not int or self.d <= 0:
            raise CertificateError("integer pair must have positive denominator")

    def __add__(self, other):
        return Q(self.n * other.d + other.n * self.d, self.d * other.d)

    def __sub__(self, other):
        return Q(self.n * other.d - other.n * self.d, self.d * other.d)

    def __mul__(self, other):
        return Q(self.n * other.n, self.d * other.d)

    def __truediv__(self, other):
        if other.n <= 0:
            raise CertificateError("division requires positive divisor")
        return Q(self.n * other.d, self.d * other.n)

    def __le__(self, other):
        return self.n * other.d <= other.n * self.d

    def pair(self):
        return [str(self.n), str(self.d)]

    def fraction(self):
        return Fraction(self.n, self.d)


ZERO, ONE, HALF = Q(0), Q(1), Q(1, 2)
INTEGER = re.compile(r"(?:0|-?[1-9][0-9]*)\Z")
POSITIVE = re.compile(r"[1-9][0-9]*\Z")
SCHEMA = "rational-observer-interval-v1"


def rational(value):
    if (not isinstance(value, list) or len(value) != 2
            or not all(isinstance(x, str) for x in value)
            or not INTEGER.fullmatch(value[0])
            or not POSITIVE.fullmatch(value[1])):
        raise CertificateError("rational must be [integer-string, positive-integer-string]")
    return Q(int(value[0]), int(value[1]))


def cli_rational(value):
    parts = value.split("/")
    return rational(parts if len(parts) == 2 else [value, "1"])


def keys(value, expected, where):
    if not isinstance(value, dict) or set(value) != set(expected):
        raise CertificateError(f"{where}: expected fields {sorted(expected)}")


def parameters(p, r, eps):
    if not (p.n > 0 and r.n > 0 and eps.n > 0
            and 2 * p.n < p.d and 2 * r.n < r.d):
        raise CertificateError("require 0 < p,r < 1/2 and eps > 0")


def bayes(p, q, report):
    # Old hidden bit emits first. Each expression has fixed arithmetic depth.
    a, c, n, e = p.n, p.d, q.n, q.d
    if report == 0:
        return Q((c - a) * n, a * e + (c - 2 * a) * n)
    return Q(a * n, (c - a) * e - (c - 2 * a) * n)


def mix(r, q):
    return Q(r.n * q.d + (r.d - 2 * r.n) * q.n, r.d * q.d)


def update(p, r, q, report):
    return mix(r, bayes(p, q, report))


def output(p, q):
    return Q(p.n * q.d + (p.d - 2 * p.n) * q.n, p.d * q.d)


def nearest(z):
    """Nearest integer; exact halves go to the smaller integer."""
    quotient, remainder = divmod(z.n, z.d)
    return quotient + int(2 * remainder > z.d)


def construct(p, r, eps):
    parameters(p, r, eps)
    d, eta = ONE - Q(2) * p, ONE - Q(2) * r
    raw_k = Q(4) * eps / d
    k = raw_k if raw_k <= ONE else ONE
    cap = ONE + k
    scale = cap * cap * cap * eta / (r * k)
    m = 2 * ((scale.n + scale.d - 1) // scale.d)
    rows = []
    for j in range(m + 1):
        # Common denominator, not an unreduced recurrence across grid rows.
        q = Q(r.n * m + (r.d - 2 * r.n) * j, r.d * m)
        lower = q / (cap - k * q)
        upper = cap * q / (ONE + k * q)
        lo = r if lower <= r else lower
        hi = upper if upper <= ONE - r else ONE - r
        rows.append({"lo": lo.pair(), "hi": hi.pair(),
                     "readout": output(p, q).pair(),
                     "targets": [nearest(Q(m) * bayes(p, q, b)) for b in (0, 1)]})
    return {"schema": SCHEMA,
            "parameters": {"p": p.pair(), "r": r.pair(), "eps": eps.pair()},
            "initial": m // 2, "states": rows}


def verify(certificate):
    """Check supplied intervals, readouts and edges, not generator identity.

    On input passing the range checks, count all 11N+2 scalar comparisons.
    Bad ranges are rejected before evaluating F outside its declared domain.
    Failures are sufficient to reject this certificate, not necessarily the
    actual observer's accuracy on its reachable histories.
    """
    keys(certificate, {"schema", "parameters", "initial", "states"}, "certificate")
    if certificate["schema"] != SCHEMA:
        raise CertificateError("unknown schema")
    pars = certificate["parameters"]
    keys(pars, {"p", "r", "eps"}, "parameters")
    p, r, eps = (rational(pars[name]) for name in ("p", "r", "eps"))
    parameters(p, r, eps)
    rows = certificate["states"]
    if not isinstance(rows, list) or not rows:
        raise CertificateError("states must be a nonempty list")
    n = len(rows)
    initial = certificate["initial"]
    if type(initial) is not int or not 0 <= initial < n:
        raise CertificateError("initial index out of range")
    parsed = []
    for j, row in enumerate(rows):
        keys(row, {"lo", "hi", "readout", "targets"}, f"state {j}")
        targets = row["targets"]
        if (not isinstance(targets, list) or len(targets) != 2
                or any(type(t) is not int or not 0 <= t < n for t in targets)):
            raise CertificateError(f"state {j}: two integer targets in range required")
        parsed.append((rational(row["lo"]), rational(row["hi"]),
                       rational(row["readout"]), targets))

    failures, comparisons = [], 0

    def check(left, right, label):
        nonlocal comparisons
        comparisons += 1
        if not left <= right:
            failures.append(label)

    def result():
        operand_bits = max(max(abs(q.n).bit_length(), q.d.bit_length())
                           for q in [p, r, eps] + [q for row in parsed for q in row[:3]])
        outcome = {"valid": not failures, "states": n,
                   "scalar_comparisons": comparisons,
                   "max_supplied_integer_bits": operand_bits,
                   "index_bits": (n - 1).bit_length()}
        if failures:
            outcome["failures"] = failures
        return outcome

    for j, (lo, hi, y, _) in enumerate(parsed):
        check(r, lo, f"range:{j}:lower")
        check(lo, hi, f"range:{j}:ordered")
        check(hi, ONE - r, f"range:{j}:upper")
        check(ZERO, y, f"readout-range:{j}:lower")
        check(y, ONE, f"readout-range:{j}:upper")
    if failures:
        return result()
    check(parsed[initial][0], HALF, "initial:lower")
    check(HALF, parsed[initial][1], "initial:upper")
    for j, (lo, hi, y, targets) in enumerate(parsed):
        for b, target in enumerate(targets):
            check(parsed[target][0], update(p, r, lo, b), f"transition:{j}:{b}:lower")
            check(update(p, r, hi, b), parsed[target][1], f"transition:{j}:{b}:upper")
        check(y - eps, output(p, lo), f"accuracy:{j}:lower")
        check(output(p, hi), y + eps, f"accuracy:{j}:upper")
    return result()


def unique_object(pairs):
    result = {}
    for key, value in pairs:
        if key in result:
            raise CertificateError(f"duplicate JSON key: {key}")
        result[key] = value
    return result


def load(path):
    return json.loads(Path(path).read_text(), object_pairs_hook=unique_object)


def emit(value, path=None):
    data = json.dumps(value, indent=2, sort_keys=True, ensure_ascii=False) + "\n"
    if path:
        Path(path).write_text(data)
    else:
        sys.stdout.write(data)


def require(condition, message):
    if not condition:
        raise AssertionError(message)


def checks():
    """Bounded regressions; endpoint verification supplies the all-word guarantee."""
    cases = []
    for p_text in ("1/100", "1/4", "49/100"):
        for r_text in ("1/100", "1/4", "499/1000"):
            p, r = cli_rational(p_text), cli_rational(r_text)
            d = ONE - Q(2) * p
            for eps in (d / Q(100), d / Q(4), d / Q(2), Q(2)):
                cert = construct(p, r, eps)
                outcome = verify(cert)
                require(outcome["valid"], f"sweep failed: {p_text}, {r_text}, {eps}")
                require("failures" not in outcome, "successful verification includes failures")
                require(outcome["scalar_comparisons"] == 11 * len(cert["states"]) + 2,
                        "comparison count")
                cases.append({"p": p.pair(), "r": r.pair(), "eps": eps.pair(),
                              "states": outcome["states"],
                              "scalar_comparisons": outcome["scalar_comparisons"]})
    # Exercise either side of k=1, not just the boundary itself.
    for factor in (Q(999, 1000), Q(1001, 1000)):
        cert = construct(Q(1, 3), Q(1, 4), Q(1, 12) * factor)
        require(verify(cert)["valid"], "near k=1 boundary")
        cases.append({**cert["parameters"], "states": len(cert["states"]),
                      "scalar_comparisons": verify(cert)["scalar_comparisons"]})
    require(min(case["states"] for case in cases) == 3, "m=2 case absent")
    base = construct(Q(1, 4), Q(1, 4), Q(1, 16))
    require(len(base["states"]) == 29 and base["initial"] == 14
            and base["states"][14]["targets"][0] == 21, "representative grid")
    representative = verify(base)
    require(representative["valid"] and "failures" not in representative,
            "representative verification output")

    rejections = {}
    for kind, expected in (("transition", "transition:14:0:upper"),
                           ("readout", "accuracy:14:upper"),
                           ("initial", "initial:upper")):
        bad = copy.deepcopy(base)
        if kind == "transition":
            bad["states"][14]["targets"][0] = 0
        elif kind == "readout":
            bad["states"][14]["readout"] = ZERO.pair()
        else:
            bad["initial"] = 0
        outcome = verify(bad)
        require(not outcome["valid"], f"corrupt {kind} accepted")
        require(outcome["failures"] == [expected], f"corrupt {kind} diagnostics")
        rejections[kind] = outcome["failures"]

    altered = copy.deepcopy(base)
    altered["states"][14]["readout"] = Q(501, 1000).pair()
    altered_outcome = verify(altered)
    require(altered_outcome["valid"] and "failures" not in altered_outcome,
            "valid altered readout verification output")
    # A genuinely nongrid certificate checks generic N=1 and interval semantics.
    one = {"schema": SCHEMA,
           "parameters": {"p": Q(1, 4).pair(), "r": Q(1, 4).pair(), "eps": Q(1, 4).pair()},
           "initial": 0,
           "states": [{"lo": Q(1, 4).pair(), "hi": Q(3, 4).pair(),
                       "readout": HALF.pair(), "targets": [0, 0]}]}
    one_outcome = verify(one)
    require(one_outcome["valid"] and "failures" not in one_outcome
            and one_outcome["scalar_comparisons"] == 13,
            "nongrid one-state certificate")
    malformed = 0
    for wrong in ([0.25, "4"], ["1", "0"], ["1", "-4"], [True, "4"]):
        bad = copy.deepcopy(base)
        bad["states"][0]["lo"] = wrong
        try:
            verify(bad)
        except CertificateError:
            malformed += 1
        else:
            raise AssertionError("malformed rational accepted")
    require(nearest(Q(3, 2)) == 1 and nearest(Q(1501, 1000)) == 2,
            "nearest tie rule")

    source_order = update(Q(1, 3), Q(1, 4), HALF, 0).fraction()
    flip_first = bayes(Q(1, 3), mix(Q(1, 4), HALF), 0).fraction()
    require(source_order == Fraction(7, 12) and flip_first == Fraction(2, 3),
            "emit-before-flip check")
    history_count = 0
    for p, r, eps in ((Q(1, 4), Q(1, 4), Q(1, 16)),
                      (Q(1, 3), Q(1, 100), Q(1, 30)),
                      (Q(49, 100), Q(499, 1000), Q(1, 100))):
        cert = construct(p, r, eps)
        pf, rf, ef = p.fraction(), r.fraction(), eps.fraction()
        # (word, unnormalised old-state masses, observer index)
        stack = [("", Fraction(1, 2), Fraction(1, 2), cert["initial"])]
        while stack:
            word, v0, v1, j = stack.pop()
            row = cert["states"][j]
            mass, q = v0 + v1, v1 / (v0 + v1)
            lo, hi, y = (rational(row[k]).fraction() for k in ("lo", "hi", "readout"))
            require(mass >= pf ** len(word) > 0 and lo <= q <= hi,
                    "raw Bayesian recursion outside interval")
            require(abs(y - (pf * v0 + (1 - pf) * v1) / mass) <= ef,
                    "raw next-report error")
            history_count += 1
            if len(word) == 8:
                continue
            for b in (0, 1):
                a0, a1 = ((pf * v0, (1 - pf) * v1) if b == 0
                          else ((1 - pf) * v0, pf * v1))
                u0, u1 = (1 - rf) * a0 + rf * a1, rf * a0 + (1 - rf) * a1
                require(update(p, r, Q(q.numerator, q.denominator), b).fraction()
                        == u1 / (u0 + u1), "scalar versus two-component update")
                stack.append((word + str(b), u0, u1, row["targets"][b]))
    return {"parameter_sweeps": cases, "sweep_count": len(cases),
            "representative": representative, "corrupt_rejections": rejections,
            "valid_altered_readout": "501/1000 at state 14",
            "nongrid_one_state": one_outcome, "malformed_rational_rejections": malformed,
            "source_order": {"emit_then_flip": str(source_order), "flip_then_emit": str(flip_first)},
            "bounded_history_crosscheck": {"parameter_triples": 3, "max_length": 8,
                                           "words_including_empty": history_count}}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="command", required=True)
    gen = sub.add_parser("generate")
    for name in ("p", "r", "eps"):
        gen.add_argument(f"--{name}", required=True)
    gen.add_argument("--out")
    ver = sub.add_parser("verify")
    ver.add_argument("certificate")
    ver.add_argument("--out")
    test = sub.add_parser("checks")
    test.add_argument("--out")
    args = parser.parse_args()
    try:
        if args.command == "generate":
            cert = construct(*(cli_rational(getattr(args, name)) for name in ("p", "r", "eps")))
            require(verify(cert)["valid"], "constructed certificate failed verification")
            emit(cert, args.out)
        elif args.command == "verify":
            result = verify(load(args.certificate))
            emit(result, args.out)
            return 0 if result["valid"] else 1
        else:
            emit(checks(), args.out)
    except (ValueError, OSError) as error:
        emit({"valid": False, "error": str(error)})
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
