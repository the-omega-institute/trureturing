#!/usr/bin/env python3
"""Two fixed emission models, one finite training decision (ML observation §50).

Production parameters are Q values or canonical two-string rational lists.
The true model is never an input. Certificates remain factored; only labels,
pair counters and one pending report evolve. `checks` contains bounded exact
experiments, not a proof of independence or an infinite-time probability bound.
"""

import argparse
import copy
from fractions import Fraction as F
import io
from itertools import product
import json
from math import comb
import sys

from rational_observer import (
    Q, CertificateError, cli_rational, construct, emit, rational, require, verify,
)


def _parameter(value, name):
    """Accept exactly Q or the owner's canonical JSON rational pair."""
    if type(value) is Q:
        parsed = value
    elif type(value) is list and all(type(part) is str for part in value):
        parsed = rational(value)
    else:
        raise CertificateError(f"{name} must be Q or a two-string rational list")
    if parsed.n <= 0 or (name == "delta" and parsed.n >= parsed.d):
        raise CertificateError("require epsilon > 0 and 0 < delta < 1")
    return parsed


def training_budget(delta):
    """Return L=min{k:2^k*delta>=1}, M=ceil(41472*L/25), using integers."""
    delta = _parameter(delta, "delta")
    doubled, L = delta.n, 0
    while doubled < delta.d:
        doubled *= 2
        L += 1
    return L, (41472 * L + 24) // 25


def select_model(M, c):
    """Classify M disjoint pairs with c matches; equality chooses A."""
    if type(M) is not int or M <= 0 or type(c) is not int or not 0 <= c <= M:
        raise CertificateError("require positive integer M and integer 0 <= c <= M")
    return "A" if 288 * c >= 157 * M else "B"


class ModelSelector:
    """A parameter-blind predictor for {p=1/4,p=1/3}, r=1/4, fair hidden prior.

    Public construction derives M from delta and verifies both ordinary §41
    certificates. Static fields: epsilon, delta, L, M, certificates. Dynamic
    training state: (completed pairs, matches, pending bit/None, label A, label B).
    After selection `_training` is the fixed sentinel None and the only
    history-dependent fields are `model` and `index`. There is no report clock.
    """

    __slots__ = ("epsilon", "delta", "L", "M", "certificates",
                 "_training", "model", "index")

    def __init__(self, epsilon, delta):
        epsilon = _parameter(epsilon, "epsilon")
        delta = _parameter(delta, "delta")
        L, M = training_budget(delta)
        certificates = tuple(construct(p, Q(1, 4), epsilon) for p in (Q(1, 4), Q(1, 3)))
        for certificate in certificates:
            if not verify(certificate)["valid"]:
                raise CertificateError("constructed known-model certificate did not verify")
        self._initialize(epsilon, delta, L, M, certificates)

    def _initialize(self, epsilon, delta, L, M, certificates):
        self.epsilon, self.delta, self.L, self.M = epsilon, delta, L, M
        self.certificates = certificates
        self._training = (0, 0, None, certificates[0]["initial"], certificates[1]["initial"])
        self.model = self.index = None

    @classmethod
    def _diagnostic(cls, epsilon, M, verified_certificates):
        """Private checks only: supplied verified tables and small M; no delta guarantee."""
        epsilon = _parameter(epsilon, "epsilon")
        if type(M) is not int or M <= 0:
            raise CertificateError("diagnostic M must be a positive integer")
        observer = cls.__new__(cls)
        observer._initialize(epsilon, None, None, M, verified_certificates)
        return observer

    def readout(self):
        if self.model is None:
            return ["1", "2"]
        table = self.certificates[0 if self.model == "A" else 1]
        return list(table["states"][self.index]["readout"])

    def step(self, report):
        if type(report) is not int or report not in (0, 1):
            raise CertificateError("report must be an integer bit (bool is not a report)")
        if self.model is not None:
            table = self.certificates[0 if self.model == "A" else 1]
            self.index = table["states"][self.index]["targets"][report]
        else:
            k, c, pending, a, b = self._training
            a = self.certificates[0]["states"][a]["targets"][report]
            b = self.certificates[1]["states"][b]["targets"][report]
            if pending is None:
                self._training = (k, c, report, a, b)
            else:
                c += int(pending == report)
                if k + 1 == self.M:
                    self.model = select_model(self.M, c)
                    self.index = a if self.model == "A" else b
                    # Clear all history-bearing training fields BEFORE the
                    # first selected readout; keep the selected updated label.
                    self._training = None
                else:
                    self._training = (k + 1, c, None, a, b)
        return self.readout()


def stream_predictions(observer, source, sink):
    """Binary input, ASCII bits/whitespace; initial output then one JSON line per bit."""
    def send(value):
        record = {"model": observer.model, "label": observer.index, "prediction": value}
        sink.write(json.dumps(record, separators=(",", ":")) + "\n")
        sink.flush()

    send(observer.readout())
    while True:
        report = source.read(1)
        if report == b"":
            return
        if report in (b" ", b"\t", b"\n", b"\r", b"\v", b"\f"):
            continue
        if report not in (b"0", b"1"):
            raise CertificateError("stream reports must be ASCII 0 or 1")
        send(observer.step(int(report)))


def checks():
    """Exact small scopes plus a linear production run; no earlier suites."""
    budgets = []
    for delta, expected in [
        (Q(3, 4), (1, 1659)), (Q(1, 2), (1, 1659)),
        (Q(501, 1000), (1, 1659)), (Q(499, 1000), (2, 3318)),
        (Q(251, 1000), (2, 3318)), (Q(1, 4), (2, 3318)),
        (Q(249, 1000), (3, 4977)), (Q(1, 1000), (10, 16589)),
        (Q(1, 2**100), (100, 165888)),
    ]:
        L, M = training_budget(delta)
        require((L, M) == expected, f"dyadic budget: {delta.pair()}")
        require(2**(L - 1) * delta.n < delta.d <= 2**L * delta.n,
                "minimal dyadic exponent")
        require(25 * (M - 1) < 41472 * L <= 25 * M,
                "minimal sufficient integer M for this L")
        budgets.append({"delta": delta.pair(), "L": L, "M": M, "reports": 2 * M})
    require(training_budget(["2", "4"]) == (1, 1659), "unreduced delta")
    require([select_model(288, c) for c in (156, 157, 158)] == ["B", "A", "A"],
            "threshold equality and neighbors")

    def rejects(call, name):
        try:
            call()
        except CertificateError:
            return
        raise AssertionError("accepted invalid " + name)

    bad_types = [True, False, None, 1, 0.5, F(1, 2), "1/2", ("1", "2"),
                 [1, 2], ["1"], ["1", "0"], ["1", "-2"],
                 ["01", "2"], ["1", True], {"n": 1, "d": 2}, object()]
    rejected_parameters = 0
    for value in bad_types + [Q(0), Q(-1)]:
        rejects(lambda: ModelSelector(value, Q(1, 2)), "epsilon")
        rejected_parameters += 1
    for value in bad_types + [Q(0), Q(-1), Q(1), Q(3, 2)]:
        rejects(lambda: ModelSelector(Q(1, 64), value), "delta")
        rejects(lambda: training_budget(value), "budget delta")
        rejected_parameters += 2
    for M, c in [(True, 0), (0, 0), (-1, 0), (1, True), (1, -1), (1, 2),
                 (1.0, 0), (1, 0.0)]:
        rejects(lambda: select_model(M, c), "classifier count")

    eps = Q(1, 64)
    tables = tuple(construct(p, Q(1, 4), eps) for p in (Q(1, 4), Q(1, 3)))
    verifications = [verify(table) for table in tables]
    for outcome, N, comparisons in zip(verifications, (47, 37), (519, 409)):
        require(outcome["valid"] and "failures" not in outcome, "both certificates valid")
        require((outcome["states"], outcome["scalar_comparisons"]) == (N, comparisons),
                "certificate size and complete comparison count")

    # Independent hidden-mass recursion owned by observer_capture. Unlike its
    # fair-prior `history`, explicitly seed priors 0, 1/2 and 1 here.
    from observer_capture import mass_step

    def masses_for(p, prior, word):
        masses = (1 - prior, prior)
        for report in word:
            masses = mass_step(masses, report, p, F(1, 4))
        return masses

    def next_zero(p, masses):
        return sum(mass_step(masses, 0, p, F(1, 4))) / sum(masses)

    def pair(value):
        return [str(value.numerator), str(value.denominator)]

    pair_laws = []
    for model, p, theta in [("A", F(1, 4), F(9, 16)), ("B", F(1, 3), F(19, 36))]:
        for prior in (F(0), F(1, 2), F(1)):
            for M in (1, 2, 3):
                vectors = {v: F(0) for v in product((0, 1), repeat=M)}
                word_error = F(0)
                for word in product((0, 1), repeat=2 * M):
                    mass = sum(masses_for(p, prior, word))
                    matches = tuple(int(word[2*k] == word[2*k+1]) for k in range(M))
                    vectors[matches] += mass
                    if select_model(M, sum(matches)) != model:
                        word_error += mass
                require(sum(vectors.values()) == 1, "enumerated word law normalizes")
                for vector, mass in vectors.items():
                    expected = theta**sum(vector) * (1 - theta)**(M - sum(vector))
                    require(mass == expected, "full indicator vector product law")
                # This reference uses a rational midpoint, independently of
                # the selector's integer threshold implementation.
                binomial_error = sum(
                    (comb(M, c) * theta**c * (1-theta)**(M-c)
                     for c in range(M+1)
                     if ("A" if F(c, M) >= F(157, 288) else "B") != model), F(0))
                require(word_error == binomial_error, "small-M classification tail")
                pair_laws.append({"model": model, "hidden_prior": pair(prior), "M": M,
                                  "words": 2**(2*M), "vectors": len(vectors),
                                  "error_probability": pair(word_error)})

    class CheckedReadoutSelector(ModelSelector):
        __slots__ = ()

        def readout(self):
            if self.model is not None:
                require(self._training is None, "training erased before selected readout")
            return super().readout()

    trajectories = []
    for model, p, table in zip(("A", "B"), (F(1, 4), F(1, 3)), tables):
        for M in (1, 2, 3):
            prefixes, comparisons, max_error = 0, 0, F(0)
            for word in product((0, 1), repeat=2*M):
                observer = CheckedReadoutSelector._diagnostic(eps, M, tables)
                expected_labels = [t["initial"] for t in tables]
                for t, report in enumerate(word, 1):
                    expected_labels = [tab["states"][j]["targets"][report]
                                       for tab, j in zip(tables, expected_labels)]
                    value = observer.step(report)
                    if t < 2*M:
                        require(value == ["1", "2"] and observer.model is None,
                                "preselection output")
                        require(observer._training[3:] == tuple(expected_labels),
                                "both labels consume every training report")
                require(observer._training is None, "all training state erased at selection")
                require(not hasattr(observer, "__dict__"), "no unbounded dynamic attributes")
                require(observer.index == expected_labels[0 if observer.model == "A" else 1],
                        "selected label is post-update, with no reset")
                if observer.model != model:
                    continue
                prefixes += 1
                for length in range(4):
                    for suffix in product((0, 1), repeat=length):
                        continued = copy.copy(observer)
                        masses = masses_for(p, F(1, 2), word)
                        j = expected_labels[0 if model == "A" else 1]
                        for report in suffix:
                            continued.step(report)
                            j = table["states"][j]["targets"][report]
                            masses = mass_step(masses, report, p, F(1, 4))
                        require(continued.model == model and continued.index == j,
                                "selected trajectory equals known-model trajectory")
                        require(continued._training is None, "training state stays erased")
                        readout = rational(continued.readout()).fraction()
                        error = abs(readout - next_zero(p, masses))
                        require(error <= F(1, 64), "fresh readout predicts the next report")
                        max_error = max(max_error, error)
                        comparisons += 1
            trajectories.append({"model": model, "diagnostic_M": M,
                                 "correct_training_prefixes": prefixes,
                                 "suffix_lengths": [0, 1, 2, 3],
                                 "readouts_checked": comparisons, "max_error": pair(max_error)})

    # Negative timing controls on the same correctly classified prefix 11.
    diag = ModelSelector._diagnostic(eps, 1, tables)
    diag.step(1)
    stale = rational(tables[0]["states"][diag._training[3]]["readout"]).fraction()
    fresh = rational(diag.step(1)).fraction()
    target = next_zero(F(1, 4), masses_for(F(1, 4), F(1, 2), (1, 1)))
    reset = rational(tables[0]["states"][tables[0]["initial"]]["readout"]).fraction()
    require(diag.model == "A" and abs(fresh - target) <= F(1, 64), "boundary next-report target")
    require(abs(stale - target) == F(5, 276) > F(1, 64), "stale-label negative control")
    require(abs(reset - target) == F(1, 12) > F(1, 64), "reset-label negative control")

    invalid_reports = [True, False, -1, 2, 0.0, 1.0, "0", b"1", None, Q(0), [1], {}]
    for observer in (ModelSelector._diagnostic(eps, 1, tables), diag):
        before = (observer._training, observer.model, observer.index)
        for value in invalid_reports:
            rejects(lambda: observer.step(value), "report")
            require((observer._training, observer.model, observer.index) == before,
                    "invalid report must leave state unchanged")

    # One full production training run, linear in the computed budget, never
    # enumeration of its 2^(2M) possible words.
    production = ModelSelector(["1", "64"], ["1", "2"])
    require((production.L, production.M) == (1, 1659), "production derives M")
    for n in range(1, 2*production.M + 1):
        production.step(1)
        require((production.model is not None) == (n == 2*production.M),
                "production selection boundary")
    require(production.model == "A" and production._training is None,
            "production selection and cleanup")
    for report in (0, 1)*6:
        production.step(report)
        require(production.model == "A" and production._training is None,
                "production retains tag without new clock or reselection")

    # A source that only permits incremental reads and a sink that immediately
    # discards output. This also exercises the selection-boundary ordering.
    class IncrementalSource:
        def __init__(self):
            self.parts = iter([b"1", b" ", b"1", b"0", b"\n", b""])

        def read(self, count):
            require(count == 1, "incremental source read")
            return next(self.parts)

    class CheckingSink:
        def __init__(self):
            self.expected = ModelSelector._diagnostic(eps, 1, tables)
            self.lines = 0

        def write(self, line):
            reports = (1, 1, 0)
            if self.lines:
                self.expected.step(reports[self.lines-1])
            record = json.loads(line)
            require(record == {"model": self.expected.model, "label": self.expected.index,
                               "prediction": self.expected.readout()}, "stream emits after update")
            self.lines += 1

        def flush(self):
            pass

    sink = CheckingSink()
    stream_predictions(ModelSelector._diagnostic(eps, 1, tables), IncrementalSource(), sink)
    require(sink.lines == 4, "one initial and one output per report")
    rejects(lambda: stream_predictions(ModelSelector._diagnostic(eps, 1, tables),
                                       io.BytesIO(b"2"), io.StringIO()), "stream bit")
    return {"scope": "bounded exact regressions; no Lean validation or infinite enumeration",
            "epsilon": eps.pair(), "budget_fenceposts": budgets,
            "threshold_288_counts_156_157_158": ["B", "A", "A"],
            "certificate_verification": verifications,
            "pair_indicator_laws": pair_laws, "correct_selection_trajectories": trajectories,
            "timing_controls": {"prefix": "11", "diagnostic_M": 1, "model": "A",
                                "target": pair(target), "fresh_error": pair(abs(fresh-target)),
                                "stale_error": pair(abs(stale-target)), "reset_error": pair(abs(reset-target))},
            "rejected_parameter_calls": rejected_parameters, "rejected_count_calls": 8,
            "rejected_report_calls": 2*len(invalid_reports),
            "production_reports": 2*production.M, "production_continuation_reports": 12,
            "postselection_training_state": "None before first selected readout and thereafter",
            "incremental_stream_predictions": sink.lines}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest="command", required=True)
    check_parser = commands.add_parser("checks", help="run scoped exact regressions")
    check_parser.add_argument("--output")
    stream_parser = commands.add_parser("stream", help="predict incrementally from stdin bits")
    stream_parser.add_argument("--epsilon", type=cli_rational, required=True)
    stream_parser.add_argument("--delta", type=cli_rational, required=True)
    args = parser.parse_args()
    if args.command == "checks":
        emit(checks(), args.output)
    else:
        stream_predictions(ModelSelector(args.epsilon, args.delta), sys.stdin.buffer, sys.stdout)


if __name__ == "__main__":
    try:
        main()
    except (CertificateError, AssertionError) as error:
        print(f"[FAIL] {error}", file=sys.stderr)
        sys.exit(1)
