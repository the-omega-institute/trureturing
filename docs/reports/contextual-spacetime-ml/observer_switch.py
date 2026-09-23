#!/usr/bin/env python3
"""Exact experiments and the fixed eight-report precision switch in ML §43.

Python standard library only. The switch accepts a label from the §41 observer
with p=r=1/4, eps=1/16; its fixed target is 1/1024. No pre-switch history or
clock is available. The independent reference uses two unnormalised masses.
"""

import argparse
from fractions import Fraction as F
from itertools import product
import io
import json
import sys

from rational_observer import (CertificateError, Q, construct, emit, nearest,
                               rational, require, verify)


TARGET = F(1, 1024)
OLD_M, NEW_M, WARMUP = 28, 526, 8


class EightReportSwitch:
    """Fixed §43 switch; dynamic memory is exactly (index, counter).

    reset(j) requires that j is the current label of a valid old §41 run.
    An in-range integer alone cannot establish that historical precondition.
    Certification asserts next-report accuracy, not fine-interval membership.
    """

    def __init__(self, old_label):
        self.table = construct(Q(1, 4), Q(1, 4), Q(1, 1024))
        outcome = verify(self.table)
        if not outcome["valid"] or len(self.table["states"]) != NEW_M + 1:
            raise CertificateError(f"fixed switch table rejected: {outcome}")
        self.reset(old_label)

    def reset(self, old_label):
        if type(old_label) is not int or not 0 <= old_label <= OLD_M:
            raise CertificateError("old label must be an integer from 0 through 28")
        self.index = nearest(Q(NEW_M * old_label, OLD_M))
        self.counter = 0
        return self.readout()

    def readout(self):
        return {"index": self.index, "counter": self.counter,
                "certified": self.counter == WARMUP,
                "prediction": self.table["states"][self.index]["readout"]}

    def step(self, report):
        if type(report) is not int or report not in (0, 1):
            raise CertificateError("report must be the integer 0 or 1")
        self.index = self.table["states"][self.index]["targets"][report]
        self.counter = min(self.counter + 1, WARMUP)
        return self.readout()


def stream_switch(observer, source, sink):
    """Read ASCII bytes incrementally; emit reset and post-update predictions."""
    def send(state):
        sink.write(json.dumps(state, separators=(",", ":")) + "\n")
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


def pair(value):
    return [str(value.numerator), str(value.denominator)]


def mass_step(masses, report):
    """Independent emit-then-flip calculation, without scalar Bayes helpers."""
    weighted = [mass * (F(1, 4) if report == i else F(3, 4))
                for i, mass in enumerate(masses)]
    return ((3 * weighted[0] + weighted[1]) / 4,
            (weighted[0] + 3 * weighted[1]) / 4)


def posterior(masses):
    return masses[1] / sum(masses)


def prediction(q):
    return F(1, 4) + q / 2


def center(m, index):
    return F(1, 4) + F(index, 2 * m)


def reference_nearest(m, q):
    """A full Fraction grid scan, independent of the delivered integer rounding."""
    return min(range(m + 1), key=lambda i: (abs(q - center(m, i)), i))


def envelope(n):
    return (8 + 785 * F(1, 2) ** n) / 12624


def checks():
    coarse = construct(Q(1, 4), Q(1, 4), Q(1, 16))
    modest = construct(Q(1, 4), Q(1, 4), Q(1, 32))
    switch = EightReportSwitch(23)
    certificates = {}
    for name, cert, m in (("old", coarse, 28), ("modest", modest, 32),
                          ("target", switch.table, 526)):
        outcome = verify(cert)
        require(outcome["valid"], f"{name} certificate: {outcome}")
        require(len(cert["states"]) == m + 1, f"{name} grid size")
        certificates[name] = outcome

    expected = {
        "100": ([14, 7, 18, 22], [16, 8, 21, 26], F(15, 128), F(13, 20)),
        "0100": ([14, 21, 10, 19, 23], [16, 24, 11, 22, 26],
                 F(57, 1024), F(25, 38)),
        "00": ([14, 21, 23], [16, 24, 27], F(9, 32), F(2, 3)),
    }
    histories = {}
    for word, (old_trace, fine_trace, probability, q) in expected.items():
        traces = [[coarse["initial"]], [modest["initial"]]]
        masses = (F(1, 2), F(1, 2))
        for bit in map(int, word):
            masses = mass_step(masses, bit)
            for cert, trace in zip((coarse, modest), traces):
                prior = center(len(cert["states"]) - 1, trace[-1])
                independent = posterior(mass_step((1 - prior, prior), bit))
                target = cert["states"][trace[-1]]["targets"][bit]
                require(target == reference_nearest(len(cert["states"]) - 1,
                                                    independent), "history target")
                trace.append(target)
        require(traces == [old_trace, fine_trace], f"history labels: {word}")
        require(sum(masses) == probability > 0 and posterior(masses) == q,
                f"history probability/posterior: {word}")
        histories[word] = {"old_labels": traces[0], "modest_labels": traces[1],
                           "probability": pair(probability), "posterior": pair(q),
                           "next_zero": pair(prediction(q))}

    gap = prediction(F(2, 3)) - prediction(F(25, 38))
    require(gap == F(1, 228) and gap / 2 == F(1, 456) > TARGET,
            "old-label-only obstruction")
    delta = F(1, 2 * NEW_M) / (2 * F(1, 4) * F(3, 4))
    beta = F(1, 2) * delta / (4 * (1 - F(1, 2)))
    initial_bound = F(1, 2) + delta  # log(3/2) <= 1/2, proved in §43.
    require(delta == F(2, 789) and beta == F(1, 1578) < TARGET,
            "strict residual margin")
    require(initial_bound == F(793, 1578), "initial log-error upper bound")
    require(envelope(0) == initial_bound / 8
            and envelope(8) == F(2833, 3231744) < TARGET,
            "rational eight-report sufficient bound")
    require(F(2, 3) * F(3, 112) + F(1, 112) == F(3, 112)
            and F(3, 224) < F(1, 32), "unchanged-old-observer bound")

    reset_map = []
    for j in range(OLD_M + 1):
        switch.reset(j)
        require(switch.index == reference_nearest(NEW_M, center(OLD_M, j)),
                f"nearest reset: {j}")
        require(switch.counter == 0 and not switch.readout()["certified"],
                "reset clears certification")
        reset_map.append(switch.index)
    require(reset_map[7] == 131 and reset_map[21] == 394,
            "both exact reset ties choose lower index")
    switch.reset(23)
    readout = rational(switch.readout()["prediction"]).fraction()
    errors = [abs(readout - prediction(q)) for q in (F(2, 3), F(25, 38))]
    require(switch.index == 432 and readout == F(1221, 2104), "reset label/readout")
    require(errors == [F(19, 6312), F(55, 39976)]
            and all(error > TARGET for error in errors), "immediate reset errors")

    # Every old interval (including labels not asserted reachable), both
    # endpoints, and every eight-report word. These are bounded experiments.
    maximum, maximizer, prefix_checks, leaf_checks = F(0), None, 0, 0
    for j, row in enumerate(coarse["states"]):
        for endpoint in ("lo", "hi"):
            q = rational(row[endpoint]).fraction()
            for bits in product((0, 1), repeat=WARMUP):
                switch.reset(j)
                masses = (1 - q, q)
                for n in range(WARMUP + 1):
                    if n:
                        masses = mass_step(masses, bits[n - 1])
                        switch.step(bits[n - 1])
                    state = switch.readout()
                    require(state["counter"] == min(n, WARMUP)
                            and state["certified"] == (n >= WARMUP),
                            "counter/certification at each prefix")
                    error = abs(rational(state["prediction"]).fraction()
                                - prediction(posterior(masses)))
                    require(error <= envelope(n), f"prefix envelope: {j}, {bits}, {n}")
                    prefix_checks += 1
                require(error < TARGET, "eight-report endpoint accuracy")
                leaf_checks += 1
                if error > maximum:
                    maximum = error
                    maximizer = {"old_label": j, "endpoint": endpoint,
                                 "word": "".join(map(str, bits)),
                                 "new_label": switch.index,
                                 "posterior": pair(posterior(masses))}
    require(maximum == F(14515, 36216152), "eight-report envelope maximum")
    require(leaf_checks == 29 * 2 * 256, "complete endpoint/word coverage")

    switch.reset(23)
    saturation_trace = []
    for bit in map(int, "0101010101010101"):
        before = switch.index
        state = switch.step(bit)
        require(state["index"] == switch.table["states"][before]["targets"][bit]
                and state["prediction"] == switch.table["states"][state["index"]]["readout"],
                "next-report readout uses updated label")
        saturation_trace.append(state["counter"])
    require(saturation_trace == list(range(1, 8)) + [8] * 9, "counter saturation")
    switch.reset(23)
    require(switch.counter == 0 and not switch.readout()["certified"],
            "reset after saturation")
    rejected = 0
    for operation, values in ((switch.reset, (-1, 29, True, "23")),
                              (switch.step, (-1, 2, True, "0"))):
        for value in values:
            before = (switch.index, switch.counter)
            try:
                operation(value)
            except CertificateError:
                rejected += 1
            else:
                raise AssertionError(f"accepted invalid switch input: {value!r}")
            require((switch.index, switch.counter) == before, "invalid input changed state")
    sink = io.StringIO()
    stream_switch(EightReportSwitch(23), io.BytesIO(b"0 1\n000000"), sink)
    lines = [json.loads(line) for line in sink.getvalue().splitlines()]
    require(len(lines) == 9 and not any(row["certified"] for row in lines[:-1])
            and lines[-1]["certified"], "stream certification boundary")

    return {"valid": True, "scope": "fixed p=r=1/4, old m=28, new m=526, target=1/1024",
            "certificates": certificates, "histories": histories,
            "immediate_obstruction": {"output_gap": pair(gap), "lower_bound": pair(gap / 2)},
            "constants": {"delta": pair(delta), "beta": pair(beta),
                          "E0_upper": pair(initial_bound), "bound_at_8": pair(envelope(8)),
                          "target": pair(TARGET), "unchanged_old_bound": pair(F(3, 224))},
            "reset": {"map": reset_map, "label_23": 432, "prediction": pair(readout),
                      "errors_00_0100": list(map(pair, errors)), "lower_tie_old_labels": [7, 21]},
            "endpoint_experiment": {"old_intervals": 29, "endpoints_per_interval": 2,
                                    "words_per_endpoint": 256, "word_length": 8,
                                    "leaf_checks": leaf_checks, "prefix_checks_with_repetition": prefix_checks,
                                    "maximum": pair(maximum), "first_maximizer": maximizer,
                                    "actual_history_optimum": "not determined"},
            "interface": {"counter_trace": saturation_trace, "invalid_input_rejections": rejected,
                          "stream_lines": len(lines), "counter_values": 9, "counter_bits": 4,
                          "label_bits": 10, "separate_bits": 14,
                          "nominal_pairs": 4743, "packed_bits": 13}}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="command", required=True)
    test = sub.add_parser("checks")
    test.add_argument("--out")
    stream = sub.add_parser("stream")
    stream.add_argument("--old-label", type=int, required=True)
    args = parser.parse_args()
    try:
        if args.command == "checks":
            emit(checks(), args.out)
        else:
            stream_switch(EightReportSwitch(args.old_label), sys.stdin.buffer, sys.stdout)
    except (ValueError, OSError, AssertionError) as error:
        emit({"valid": False, "error": str(error)})
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
