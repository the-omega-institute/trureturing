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
import io
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


class IntegerObserver:
    """Table-free integer realization of the grid observer from ML §42.

    The fixed parameters are retained as integer pairs.  Between reports only
    the current grid index is persistent; every successor and readout is
    recomputed from that index.
    """

    def __init__(self, p, r, eps):
        parameters(p, r, eps)
        self.p, self.r, self.eps = p, r, eps
        self.P, self.A = p.n, p.d
        self.R, self.B = r.n, r.d
        self.E, self.C = eps.n, eps.d
        self.D = self.A - 2 * self.P
        self.H = self.B - 2 * self.R
        if 4 * self.E * self.A >= self.C * self.D:
            self.u, self.v = 1, 1
        else:
            self.u, self.v = 4 * self.E * self.A, self.C * self.D
        numerator = self.H * (self.u + self.v) ** 3
        denominator = self.R * self.u * self.v ** 2
        self.m = 2 * ((numerator + denominator - 1) // denominator)
        self.N = self.m + 1
        self.index = self.m // 2

    def grid_numerator(self, index):
        if type(index) is not int or not 0 <= index <= self.m:
            raise CertificateError("grid index out of range")
        return self.R * self.m + self.H * index

    def _transition_parts(self, index, report):
        U = self.grid_numerator(index)
        if report == 0:
            return self.P * self.B * self.m + self.D * U, (self.A - self.P) * U
        if report == 1:
            return (self.A - self.P) * self.B * self.m - self.D * U, self.P * U
        raise CertificateError("report must be 0 or 1")

    def target(self, index, report):
        denominator, numerator = self._transition_parts(index, report)
        quotient, remainder = divmod(self.m * numerator, denominator)
        return quotient + int(2 * remainder > denominator)

    def readout(self, index=None):
        if index is None:
            index = self.index
        denominator, _ = self._transition_parts(index, 0)
        return [str(denominator), str(self.A * self.B * self.m)]

    def step(self, report):
        self.index = self.target(self.index, report)
        return self.readout()


def stream_reports(observer, source, sink):
    """Emit one exact JSON prediction for the empty history and each report.

    ``source`` is consumed incrementally.  Whitespace is ignored, and each
    non-whitespace byte must be an ASCII report bit.  ``sink`` receives one
    JSON line at a time and may discard it.
    """
    def emit(value):
        sink.write(json.dumps(value, separators=(",", ":")) + "\n")
        flush = getattr(sink, "flush", None)
        if flush is not None:
            flush()

    def emit_prediction():
        emit({"index": observer.index, "prediction": observer.readout()})

    emit_prediction()
    while True:
        chunk = source.read(1)
        if chunk in (b"", ""):
            break
        if isinstance(chunk, str):
            byte = chunk
        else:
            byte = chunk.decode("ascii")
        if byte.isspace():
            continue
        if byte not in "01":
            raise CertificateError("stream reports must be ASCII 0 or 1")
        emit_prediction_after = observer.step(int(byte))
        emit({"index": observer.index, "prediction": emit_prediction_after})


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


def _fraction_grid_reference(p, r, eps):
    """Independent Fraction reference for the integer grid evaluator."""
    d, eta = Fraction(1) - 2 * p, Fraction(1) - 2 * r
    k = min(Fraction(1), 4 * eps / d)
    K = 1 + k
    scale = K ** 3 * eta / (r * k)
    m = 2 * ((scale.numerator + scale.denominator - 1) // scale.denominator)

    def nearest_fraction(value):
        quotient = value.numerator // value.denominator
        remainder = value - quotient
        return quotient + int(2 * remainder > 1)

    rows = []
    for j in range(m + 1):
        q = r + eta * j / m
        b0 = (1 - p) * q / (p + d * q)
        b1 = p * q / (1 - p - d * q)
        rows.append({"q": q,
                     "readout": p + d * q,
                     "targets": [nearest_fraction(m * b) for b in (b0, b1)]})
    return m, rows


def integer_checks():
    """Independent bounded checks for the table-free integer observer."""
    cases = [
        (Q(1, 4), Q(1, 4), Q(1, 16), "reduced"),
        (Q(2, 8), Q(2, 8), Q(2, 32), "unreduced"),
        (Q(1, 4), Q(1, 4), Q(1, 8), "k-saturation"),
        (Q(1, 3), Q(1, 5), Q(1, 64), "general"),
    ]
    summaries = []
    for p, r, eps, label in cases:
        observer = IntegerObserver(p, r, eps)
        m, reference = _fraction_grid_reference(p.fraction(), r.fraction(), eps.fraction())
        require(observer.m == m and observer.index == m // 2, f"{label}: initialization")
        require(Fraction(observer.grid_numerator(0), observer.B * m) == r.fraction(),
                f"{label}: lower endpoint")
        require(Fraction(observer.grid_numerator(m), observer.B * m) == (1 - r.fraction()),
                f"{label}: upper endpoint")
        for j, row in enumerate(reference):
            actual_readout = Fraction(*map(int, observer.readout(j)))
            require(actual_readout == row["readout"], f"{label}: readout {j}")
            for report in (0, 1):
                require(observer.target(j, report) == row["targets"][report],
                        f"{label}: target {j}:{report}")
        summaries.append({"label": label, "states": observer.N,
                          "checked_targets": 2 * observer.N,
                          "checked_readouts": observer.N})

    base = IntegerObserver(Q(1, 4), Q(1, 4), Q(1, 16))
    retained = load(Path(__file__).with_name("rational_observer_certificate.json"))
    require(len(retained["states"]) == base.N, "retained table state count")
    for j, row in enumerate(retained["states"]):
        require(base.target(j, 0) == row["targets"][0]
                and base.target(j, 1) == row["targets"][1],
                f"retained table target {j}")
        require(Fraction(*map(int, base.readout(j))) == Fraction(*map(int, row["readout"])),
                f"retained table readout {j}")

    # Saturation equality uses k=1 exactly; both exact lower-index ties are
    # pinned by the supplied regressions, one in each report branch.
    saturated = IntegerObserver(Q(1, 4), Q(1, 4), Q(1, 8))
    require(saturated.u == saturated.v == 1, "saturation equality")
    tie_cases = [(Q(1, 4), Q(1, 4), Q(1, 16), 6, 0),
                 (Q(1, 3), Q(1, 4), Q(1, 16), 9, 1)]
    ties = []
    for p, r, eps, j, report in tie_cases:
        observer = IntegerObserver(p, r, eps)
        denominator, numerator = observer._transition_parts(j, report)
        quotient, remainder = divmod(observer.m * numerator, denominator)
        require(2 * remainder == denominator and observer.target(j, report) == quotient,
                "exact lower-index tie")
        ties.append({"p": p.pair(), "r": r.pair(), "eps": eps.pair(),
                     "state": j, "report": report, "target": quotient})

    for bad in (Q(0), Q(1, 2), Q(-1, 3)):
        try:
            IntegerObserver(bad, Q(1, 4), Q(1, 16))
        except CertificateError:
            pass
        else:
            raise AssertionError("invalid p accepted")
    try:
        IntegerObserver(Q(1, 4), Q(1, 4), Q(0))
    except CertificateError:
        pass
    else:
        raise AssertionError("nonpositive epsilon accepted")

    class CountingSink:
        def __init__(self):
            self.lines = 0

        def write(self, value):
            self.lines += value.count("\n")

    sink = CountingSink()
    stream_observer = IntegerObserver(Q(1, 4), Q(1, 4), Q(1, 16))
    initial_prediction = stream_observer.readout()
    updated_prediction = stream_observer.step(0)
    require(updated_prediction == stream_observer.readout()
            and updated_prediction != initial_prediction, "fresh post-update output")
    stream_reports(IntegerObserver(Q(1, 4), Q(1, 4), Q(1, 16)),
                   io.BytesIO(b"01" * 5000), sink)
    require(sink.lines == 10001, "long stream output count")

    # Full-interval quotient failure: both inputs share rho=1, but their
    # exact F_0 images round to distinct indices.  They are outside the
    # fixed-prior reachable invariant and therefore are not a reachable
    # witness against the grid trajectory theorem.
    p = r = Fraction(1, 4)
    m = 32
    grid = lambda j: r + (1 - 2 * r) * j / m
    rho = lambda x: min(range(m + 1), key=lambda j: (abs(x - grid(j)), j))
    bayes_zero = lambda x: r + (1 - 2 * r) * ((1 - p) * x / (p + (1 - 2 * p) * x))
    x, y = Fraction(13, 50), Fraction(27, 100)
    require(rho(x) == rho(y) == 1, "ambient quotient input fiber")
    require(rho(bayes_zero(x)) == 16 and rho(bayes_zero(y)) == 17,
            "ambient quotient output split")
    require(bayes_zero(x) == Fraction(77, 152) and bayes_zero(y) == Fraction(79, 154),
            "ambient quotient exact values")

    return {"cases": summaries, "retained_table": {"states": base.N,
            "targets_and_readouts": 2 * base.N + base.N},
            "exact_ties": ties, "invalid_boundary_rejections": 4,
            "long_stream": {"reports": 10000, "emitted_lines": sink.lines},
            "stale_output_regression": {"initial": initial_prediction,
                "after_report_0": updated_prediction},
            "ambient_counterexample": {"p": "1/4", "r": "1/4", "m": 32,
                "inputs": [["13", "50"], ["27", "100"]], "shared_index": 1,
                "F0": [["77", "152"], ["79", "154"]],
                "output_indices": [16, 17],
                "reachable_fixed_prior": False}}


def unknown_checks():
    """Bounded paired fixed-model checks for observation companion §48."""
    require(sys.flags.optimize == 0, "unknown-checks requires assertions enabled")
    ps, r = (Q(1, 4), Q(1, 3)), Q(1, 4)
    rf = r.fraction()
    initial = tuple((p, HALF, Fraction(1, 2), Fraction(1, 2)) for p in ps)
    stack = [("", initial)]
    words, zero_rows = 0, {}
    while stack:
        word, models = stack.pop()
        require(tuple(p for p, _, _, _ in models) == ps, "fixed parameter identities")
        readouts, rows = [], []
        for p, q, v0, v1 in models:
            pf, qf, mass = p.fraction(), q.fraction(), v0 + v1
            label = f"p={pf}, word={word!r}"
            require(pf ** len(word) <= mass <= (1 - pf) ** len(word)
                    and v0 > 0 and v1 > 0, f"{label}: finite support")
            require(qf == v1 / mass, f"{label}: scalar posterior versus masses")
            y = output(p, q).fraction()
            require(y == (pf * v0 + (1 - pf) * v1) / mass,
                    f"{label}: current next-zero readout versus masses")
            readouts.append(y)
            rows.append({"p": p.pair(), "posterior": Q(qf.numerator, qf.denominator).pair(),
                         "next_zero": Q(y.numerator, y.denominator).pair(),
                         "word_probability": Q(mass.numerator, mass.denominator).pair()})
        if len(word) <= 8:
            words += 1
        if word == "0" * len(word):
            n = len(word)
            qa, qb = (q.fraction() for _, q, _, _ in models)
            a, b = readouts
            gap = (a - b) / 2
            require(qb < Fraction(9, 14) and b < Fraction(23, 42),
                    f"zero prefix {n}: invariant bounds")
            if n >= 3:
                require(qa >= Fraction(19, 28) and a >= Fraction(33, 56)
                        and gap > Fraction(1, 48), f"zero prefix {n}: rational barrier")
            zero_rows[n] = {"n": n, "models": rows,
                            "half_gap": Q(gap.numerator, gap.denominator).pair()}
        # All words through 8, followed only by the zero branch through 64.
        reports = (0, 1) if len(word) < 8 else (
            (0,) if word == "0" * len(word) and len(word) < 64 else ())
        for report in reports:
            successors = []
            for p, q, v0, v1 in models:
                pf = p.fraction()
                a0, a1 = ((pf * v0, (1 - pf) * v1) if report == 0
                          else ((1 - pf) * v0, pf * v1))
                u0, u1 = (1 - rf) * a0 + rf * a1, rf * a0 + (1 - rf) * a1
                successors.append((p, update(p, r, q, report), u0, u1))
            stack.append((word + str(report), tuple(successors)))

    require(words == 511 and set(zero_rows) == set(range(65)), "bounded coverage")
    for n in range(64):
        before, after = (rational(zero_rows[j]["models"][0]["posterior"]).fraction()
                         for j in (n, n + 1))
        require(before < after, f"zero prefix {n}: p=1/4 increasing posterior")
    require(all(rational(row["next_zero"]).fraction() == Fraction(1, 2)
                for row in zero_rows[0]["models"]), "empty history exact prediction")
    expected = {2: Fraction(5, 228), 3: Fraction(935, 41328), 4: Fraction(145, 6424)}
    for n, value in expected.items():
        require(rational(zero_rows[n]["half_gap"]).fraction() == value,
                f"zero prefix {n}: exact half-gap")
    require(expected[2] < expected[3] > expected[4], "finite nonmonotonicity")
    require(rational(zero_rows[3]["models"][0]["posterior"]).fraction() == Fraction(19, 28)
            and rational(zero_rows[3]["models"][0]["next_zero"]).fraction() == Fraction(33, 56),
            "p=1/4 third iterate and readout")
    require([rational(row["word_probability"]).fraction() for row in zero_rows[2]["models"]]
            == [Fraction(9, 32), Fraction(19, 72)], "unequal two-report laws")
    barrier = update(ps[1], r, Q(9, 14), 0).fraction()
    require(barrier == Fraction(59, 92) < Fraction(9, 14), "invariant endpoint image")
    require(output(ps[1], Q(9, 14)).fraction() == Fraction(23, 42)
            and (Fraction(33, 56) - Fraction(23, 42)) / 2 == Fraction(1, 48),
            "rational readout barrier")
    # Exact square comparisons enclose the radicals; no floating-point premise.
    scale = 10 ** 15
    l3, u3 = Fraction(1732050807568877, scale), Fraction(1732050807568878, scale)
    l17, u17 = Fraction(4123105625617660, scale), Fraction(4123105625617661, scale)
    require(0 < l3 < u3 and l3 * l3 < 3 < u3 * u3, "sqrt(3) bracket")
    require(0 < l17 < u17 and l17 * l17 < 17 < u17 * u17, "sqrt(17) bracket")
    lower, upper = (3 * l3 - u17) / 48, (3 * u3 - l17) / 48
    require(Fraction(1, 48) < lower < upper < expected[3], "limiting gap bracket")
    return {"parameters": {"fixed_p_candidates": [p.pair() for p in ps],
                "r": r.pair(), "hidden_bit_prior": HALF.pair()},
            "bounded_history_crosscheck": {"max_length": 8, "paired_words": words,
                "fixed_models_per_word": 2, "zero_prefix_max_length": 64,
                "zero_prefixes_including_empty": len(zero_rows),
                "distinct_paired_histories": words + len(zero_rows) - 9},
            "zero_word_samples": [zero_rows[n] for n in (0, 1, 2, 3, 4, 8, 64)],
            "invariant": {"p": ps[1].pair(), "posterior_upper": Q(9, 14).pair(),
                "endpoint_image": Q(barrier.numerator, barrier.denominator).pair(),
                "readout_upper": Q(23, 42).pair(), "half_gap_lower": Q(1, 48).pair(),
                "checked_lengths": [3, 64]},
            "finite_nonmonotonicity": "half_gap(2) < half_gap(3) > half_gap(4)",
            "limit": {"expression": "(3*sqrt(3)-sqrt(17))/48",
                "sqrt3_bracket": [Q(v.numerator, v.denominator).pair() for v in (l3, u3)],
                "sqrt17_bracket": [Q(v.numerator, v.denominator).pair() for v in (l17, u17)],
                "half_gap_bracket": [Q(v.numerator, v.denominator).pair()
                                     for v in (lower, upper)]}}


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
    integer_test = sub.add_parser("integer-checks")
    integer_test.add_argument("--out")
    unknown_test = sub.add_parser("unknown-checks")
    unknown_test.add_argument("--out")
    stream = sub.add_parser("stream")
    for name in ("p", "r", "eps"):
        stream.add_argument(f"--{name}", required=True)
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
        elif args.command == "integer-checks":
            emit(integer_checks(), args.out)
        elif args.command == "unknown-checks":
            emit(unknown_checks(), args.out)
        elif args.command == "stream":
            observer = IntegerObserver(*(cli_rational(getattr(args, name))
                                          for name in ("p", "r", "eps")))
            stream_reports(observer, sys.stdin.buffer, sys.stdout)
        else:
            emit(checks(), args.out)
    except (ValueError, OSError) as error:
        emit({"valid": False, "error": str(error)})
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
