#!/usr/bin/env python3
"""Strict interval capture and two-track switching for observation companion §44.

Python 3.10+, standard library only. Reuses the ML41 constructor, verifier and
rounding. The Fraction mass reference belongs only to the finite experiments.
"""

import argparse
import copy
from fractions import Fraction as F
import json
import sys

from rational_observer import (CertificateError, Q, ONE, ZERO, cli_rational,
                               construct, emit, nearest, parameters, rational,
                               require, update, verify)


def grid_k(p, eps):
    raw = Q(4) * eps / (ONE - Q(2) * p)
    return raw if raw <= ONE else ONE


def strict_margins(p, r, eps):
    parameters(p, r, eps)
    d, eta = ONE - Q(2) * p, ONE - Q(2) * r
    k = grid_k(p, eps)
    cap = ONE + k
    env = r * k * eta / (Q(4) * cap * cap)
    edge = eta * p * r / (ONE - p - d * r)
    return env, edge, env if env <= edge else edge


def verify_margin(certificate, margin):
    """Ordinary verification plus 4N supplied-margin endpoint comparisons.

    No constructor equality is required. A smaller positive margin, a different
    valid interval layout, or a non-grid certificate can pass this checker.
    """
    if not isinstance(margin, Q) or margin.n <= 0:
        raise CertificateError("strict margin must be a positive rational")
    ordinary = verify(certificate)
    if not ordinary["valid"]:
        raise CertificateError(f"ordinary certificate rejected: {ordinary}")
    p, r = (rational(certificate["parameters"][key]) for key in ("p", "r"))
    rows = certificate["states"]
    failures = []
    for j, row in enumerate(rows):
        for bit, target in enumerate(row["targets"]):
            successor = rows[target]
            if not rational(successor["lo"]) + margin <= update(p, r, rational(row["lo"]), bit):
                failures.append(f"strict:{j}:{bit}:lower")
            if not update(p, r, rational(row["hi"]), bit) <= rational(successor["hi"]) - margin:
                failures.append(f"strict:{j}:{bit}:upper")
    result = {"valid": not failures, "states": len(rows),
              "ordinary_scalar_comparisons": ordinary["scalar_comparisons"],
              "strict_scalar_comparisons": 4 * len(rows)}
    if failures:
        result["failures"] = failures
    return result


def threshold_holds(eta, error, margin, reports):
    if (not all(isinstance(q, Q) for q in (eta, error, margin))
            or not 0 < eta.n < eta.d or error.n <= 0 or margin.n <= 0):
        raise CertificateError("threshold requires 0 < eta < 1 and E, margin > 0")
    if type(reports) is not int or reports < 1:
        raise CertificateError("capture threshold must be an integer >= 1")
    return (error.n * margin.d * pow(eta.n, reports)
            <= 4 * error.d * margin.n * pow(eta.d, reports))


def sufficient_reports(eta, error, margin):
    reports = 1
    while not threshold_holds(eta, error, margin, reports):
        reports += 1
    return reports


def bernoulli_reports(eta, error, margin):
    threshold_holds(eta, error, margin, 1)  # Validate, even if this test is false.
    bound = eta / (ONE - eta) * (error / (Q(4) * margin) - ONE)
    return max(1, (max(0, bound.n) + bound.d - 1) // bound.d)


def _pair_data(old, new):
    """Private reset data for tables made by the delivered grid constructor."""
    p, r, eps = (rational(old["parameters"][key]) for key in ("p", "r", "eps"))
    for key, value in (("p", p), ("r", r)):
        other = rational(new["parameters"][key])
        if not (value <= other and other <= value):
            raise CertificateError("switch requires matching p and r")
    eta = ONE - Q(2) * r
    old_m, new_m = len(old["states"]) - 1, len(new["states"]) - 1
    error = grid_k(p, eps) + eta / (Q(2 * new_m) * r * (ONE - r))
    return old_m, new_m, eta, error


def _prepare(p, r, eps):
    table = construct(p, r, eps)
    margin = strict_margins(p, r, eps)[2]
    result = verify_margin(table, margin)
    if not result["valid"]:
        raise CertificateError(f"strict certificate rejected: {result}")
    return table, margin


class TwoTrackCapture:
    """Ready/Warm consumer of constructed tables; no history or exact filter.

    If old_label is supplied, actual membership in its old interval is a caller
    precondition. Its range alone cannot establish this mathematical relation.
    Preparation is sequential: the report source waits during a request.
    """

    def __init__(self, p, r, eps, old_label=None):
        self.table, _ = _prepare(p, r, eps)
        if old_label is None:
            old_label = self.table["initial"]
        if type(old_label) is not int or not 0 <= old_label < len(self.table["states"]):
            raise CertificateError("old label out of range")
        self.index = old_label
        self.pending = None
        self.pending_index = None
        self.counter = self.threshold = 0

    def request(self, eps, reports=None):
        if self.pending is not None:
            raise CertificateError("precision requests activate only in Ready")
        p, r = (rational(self.table["parameters"][key]) for key in ("p", "r"))
        table, margin = _prepare(p, r, eps)
        old_m, new_m, eta, error = _pair_data(self.table, table)
        if reports is None:
            reports = sufficient_reports(eta, error, margin)
        if not threshold_holds(eta, error, margin, reports):
            raise CertificateError("supplied report threshold fails capture inequality")
        index = nearest(Q(new_m * self.index, old_m))
        # Commit the request only after all preparation/validation succeeds.
        self.pending, self.pending_index = table, index
        self.counter, self.threshold = 0, reports
        return self.readout()

    def readout(self):
        result = {"mode": "Ready" if self.pending is None else "Warm",
                  "index": self.index, "eps": self.table["parameters"]["eps"],
                  "prediction": self.table["states"][self.index]["readout"]}
        if self.pending is not None:
            result.update({"target_index": self.pending_index, "counter": self.counter,
                           "threshold": self.threshold,
                           "target_eps": self.pending["parameters"]["eps"]})
        return result

    def step(self, report):
        if type(report) is not int or report not in (0, 1):
            raise CertificateError("report must be the integer 0 or 1")
        self.index = self.table["states"][self.index]["targets"][report]
        if self.pending is not None:
            self.pending_index = self.pending["states"][self.pending_index]["targets"][report]
            self.counter += 1
            if self.counter == self.threshold:
                self.table, self.index = self.pending, self.pending_index
                self.pending, self.pending_index = None, None
                self.counter = self.threshold = 0
        return self.readout()


def stream_capture(observer, source, sink):
    """Print the current output and one updated output per ASCII report."""
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


def mass_step(masses, report, p, r):
    """Independent Fraction reference: weight hidden masses, then mix them."""
    weighted = [mass * (p if report == hidden else 1 - p)
                for hidden, mass in enumerate(masses)]
    return ((1 - r) * weighted[0] + r * weighted[1],
            r * weighted[0] + (1 - r) * weighted[1])


def posterior(masses):
    return masses[1] / sum(masses)


def center(m, j, r):
    return r + (1 - 2 * r) * F(j, m)


def interval(table, j):
    return tuple(rational(table["states"][j][key]).fraction() for key in ("lo", "hi"))


def history(table, word, p, r):
    masses, labels = (F(1, 2), F(1, 2)), [table["initial"]]
    for bit in map(int, word):
        masses = mass_step(masses, bit, p, r)
        labels.append(table["states"][labels[-1]]["targets"][bit])
    return masses, labels


def checks():
    p = r = Q(1, 4)
    old = construct(p, r, Q(1, 16))
    new = construct(p, r, Q(1, 1024))
    old_m, new_m, eta, error = _pair_data(old, new)
    env, edge, margin = strict_margins(p, r, Q(1, 1024))
    require((old_m, new_m) == (28, 526), "concrete grid sizes")
    require([q.fraction() for q in (error, env, edge, margin)]
            == [F(793, 1578), F(4, 16641), F(1, 20), F(4, 16641)],
            "concrete capture constants")
    require(eta.fraction() ** 10 * error.fraction() / 4 == F(793, 6463488),
            "ten-report bound")
    require(threshold_holds(eta, error, margin, 10), "ten-report sufficient inequality")
    require(bernoulli_reports(eta, error, margin) == 522, "Bernoulli sufficient bound")

    # Small rational cases exercise clipping, m=2 and the saturated k=1 branch.
    margin_cases = []
    cases = [(p, r, Q(1, 16)), (p, r, Q(1, 1024)),
             (Q(1, 4), Q(49, 100), Q(1, 4)),
             (Q(1, 3), Q(1, 3), Q(1, 12)),
             (Q(1, 5), Q(2, 5), Q(1, 40))]
    for cp, cr, eps in cases:
        table = construct(cp, cr, eps)
        mu = strict_margins(cp, cr, eps)[2]
        result = verify_margin(table, mu)
        require(result["valid"], "representative strict margin")
        require(verify_margin(table, mu / Q(2))["valid"], "smaller supplied margin")
        fp, fr, fm = cp.fraction(), cr.fraction(), mu.fraction()
        minimum = None
        clipped = [0, 0]
        for j, row in enumerate(table["states"]):
            lo, hi = interval(table, j)
            clipped[0] += int(lo == fr)
            clipped[1] += int(hi == 1 - fr)
            for bit, target in enumerate(row["targets"]):
                tl, th = interval(table, target)
                lower = posterior(mass_step((1 - lo, lo), bit, fp, fr)) - tl
                upper = th - posterior(mass_step((1 - hi, hi), bit, fp, fr))
                require(lower >= fm and upper >= fm, "independent strict endpoints")
                value = min(lower, upper)
                minimum = value if minimum is None else min(minimum, value)
        require(all(clipped), "both clipped endpoint sides exercised")
        margin_cases.append({"p": pair(fp), "r": pair(fr), "eps": pair(eps.fraction()),
                             "m": len(table["states"]) - 1, "k": pair(grid_k(cp, eps).fraction()),
                             "margin": pair(fm), "minimum_endpoint_margin": pair(minimum),
                             "clipped_lower_upper": clipped, **result})
    require(margin_cases[2]["m"] == 2 and margin_cases[2]["k"] == ["1", "1"],
            "m=2 with k saturation")
    # A non-grid one-state certificate shows the checker does not demand the
    # constructor's interval/transition layout or its margin formula.
    nongrid = {"schema": old["schema"], "parameters": {"p": p.pair(), "r": r.pair(), "eps": Q(1, 4).pair()},
               "initial": 0, "states": [{"lo": Q(1, 4).pair(), "hi": Q(3, 4).pair(),
                                         "readout": Q(1, 2).pair(), "targets": [0, 0]}]}
    nongrid_result = verify_margin(nongrid, Q(1, 20))
    require(nongrid_result["valid"], "non-grid supplied margin at equality")
    require(not verify_margin(nongrid, Q(1, 19))["valid"], "oversized margin rejected")

    resets = []
    for j in range(old_m + 1):
        actual = nearest(Q(new_m * j, old_m))
        reference = min(range(new_m + 1),
                        key=lambda i: (abs(center(new_m, i, F(1, 4))
                                           - center(old_m, j, F(1, 4))), i))
        require(actual == reference, "independent reset scan")
        resets.append(actual)
    require((resets[7], resets[21], resets[23]) == (131, 394, 432), "reset ties and seed")
    require(new["states"][263]["targets"] == [394, 131], "both rounded report ties")

    # Share prefixes of the complete binary tree; every terminal endpoint/word
    # case is still compared separately using the independent mass reference.
    leaves, minimum_slack, witness = 0, None, None
    fine_intervals = [interval(new, i) for i in range(new_m + 1)]
    for j in range(old_m + 1):
        for endpoint, q in zip(("lo", "hi"), interval(old, j)):
            frontier = [(0, "", resets[j], (1 - q, q))]
            while frontier:
                n, word, index, masses = frontier.pop()
                if n == 10:
                    actual = posterior(masses)
                    lo, hi = fine_intervals[index]
                    require(sum(masses) > 0 and lo <= actual <= hi,
                            f"ten-report membership: {j}/{endpoint}/{word}")
                    slack = min(actual - lo, hi - actual)
                    leaves += 1
                    if minimum_slack is None or slack < minimum_slack:
                        minimum_slack = slack
                        witness = {"old_label": j, "endpoint": endpoint, "word": word,
                                   "new_label": index, "posterior": pair(actual)}
                else:
                    for bit in (1, 0):
                        frontier.append((n + 1, word + str(bit),
                                         new["states"][index]["targets"][bit],
                                         mass_step(masses, bit, F(1, 4), F(1, 4))))
    require(leaves == 59392, "29 intervals x 1024 words x 2 endpoints")

    # Logical distinctions are separate from the following protocol traces.
    masses, _ = history(new, "000", F(1, 4), F(1, 4))
    q = posterior(masses)
    output_error = abs(F(1, 4) + q / 2 - rational(new["states"][449]["readout"]).fraction())
    excess = q - interval(new, 449)[1]
    require(q == F(19, 28) and output_error == F(13, 14728) < F(1, 1024)
            and excess == F(31, 473788) > 0, "output without membership")
    histories = {}
    for word, expected, fq in (("00", [263, 394, 438], F(2, 3)),
                               ("0100", [263, 394, 188, 364, 429], F(25, 38))):
        masses, labels = history(new, word, F(1, 4), F(1, 4))
        _, old_labels = history(old, word, F(1, 4), F(1, 4))
        require(labels == expected and old_labels[-1] == 23 and posterior(masses) == fq,
                "canonical labels and shared old label")
        histories[word] = {"old_label": 23, "fine_labels": labels, "posterior": pair(fq),
                           "next_zero": pair(F(1, 4) + fq / 2)}
    require((F(7, 12) - F(11, 19)) / 2 == F(1, 456), "label-only lower bound")

    rejected = []
    def rejects(label, operation):
        try:
            operation()
        except CertificateError:
            rejected.append(label)
        else:
            raise AssertionError(f"expected rejection: {label}")

    require(threshold_holds(Q(1, 2), Q(1), Q(1, 8), 1), "threshold equality")
    require(not threshold_holds(Q(1, 2), Q(1), Q(1, 9), 1), "threshold failure")
    require(bernoulli_reports(Q(1, 2), Q(1), Q(1)) == 1, "Bernoulli below-one boundary")
    require(bernoulli_reports(Q(1, 2), Q(1), Q(1, 4)) == 1, "Bernoulli zero boundary")
    for label, args in (("T=0", (eta, error, margin, 0)), ("T-negative", (eta, error, margin, -1)),
                        ("T-bool", (eta, error, margin, True)), ("T-string", (eta, error, margin, "10")),
                        ("eta=0", (ZERO, error, margin, 1)), ("eta=1", (ONE, error, margin, 1)),
                        ("E=0", (eta, ZERO, margin, 1)), ("mu=0", (eta, error, ZERO, 1))):
        rejects(label, lambda args=args: threshold_holds(*args))
    for label, value in (("margin-zero", ZERO), ("margin-negative", Q(-1)), ("margin-type", 1)):
        rejects(label, lambda value=value: verify_margin(new, value))
    bad = copy.deepcopy(nongrid)
    bad["states"][0]["targets"] = [0, 1]
    rejects("invalid-certificate-target", lambda: verify_margin(bad, Q(1, 20)))
    bad_accuracy = copy.deepcopy(nongrid)
    bad_accuracy["states"][0]["readout"] = ZERO.pair()
    rejects("invalid-ordinary-certificate", lambda: verify_margin(bad_accuracy, Q(1, 20)))
    for key in ("p", "r"):
        mismatch = copy.deepcopy(new)
        mismatch["parameters"][key] = Q(1, 3).pair()
        rejects(f"mismatched-{key}", lambda mismatch=mismatch: _pair_data(old, mismatch))
    for label, pars in (("p=0", (ZERO, r, Q(1, 16))), ("r=1/2", (p, Q(1, 2), Q(1, 16))),
                        ("eps=0", (p, r, ZERO))):
        rejects(label, lambda pars=pars: TwoTrackCapture(*pars))
    for value in (-1, 29, True, "23"):
        rejects(f"old-label:{value!r}", lambda value=value: TwoTrackCapture(p, r, Q(1, 16), value))

    controller = TwoTrackCapture(p, r, Q(1, 16))
    masses = (F(1, 2), F(1, 2))
    for bit in (0, 0):
        controller.step(bit)
        masses = mass_step(masses, bit, F(1, 4), F(1, 4))
    require(controller.index == 23, "valid history before first request")
    ready = controller.readout()
    rejects("failed-threshold-request", lambda: controller.request(Q(1, 1024), 1))
    require(controller.readout() == ready, "failed preparation preserves Ready")
    stages = []
    for target, reports in ((Q(1, 1024), 10), (Q(1, 16), None),
                             (Q(1, 128), None), (Q(1, 32), None)):
        old_table, old_index = controller.table, controller.index
        old_eps = rational(old_table["parameters"]["eps"]).fraction()
        state = controller.request(target, reports)
        require(state["mode"] == "Warm" and state["counter"] == 0, "start in Warm at zero")
        snapshot = copy.deepcopy(state)
        require(controller.readout() == snapshot and controller.readout() == snapshot,
                "no-report stasis")
        rejects(f"request-in-Warm:{len(stages)}", lambda: controller.request(Q(1, 64)))
        for bad_report in (2, -1, True, "0"):
            rejects(f"invalid-report:{len(stages)}:{bad_report!r}", lambda bad_report=bad_report: controller.step(bad_report))
            require(controller.readout() == snapshot, "rejected report preserves state")
        threshold = state["threshold"]
        pending_table, pending_index = controller.pending, controller.pending_index
        ref_q = center(len(pending_table["states"]) - 1, pending_index, F(1, 4))
        reference = (1 - ref_q, ref_q)
        mu = strict_margins(p, r, target)[2].fraction()
        word = ("00101101" * ((threshold + 7) // 8))[:threshold]
        max_old_error = abs(rational(snapshot["prediction"]).fraction()
                            - (F(1, 4) + posterior(masses) / 2))
        require(max_old_error <= old_eps, "old output during no-report wait")
        for n, bit in enumerate(map(int, word), 1):
            old_index = old_table["states"][old_index]["targets"][bit]
            pending_index = pending_table["states"][pending_index]["targets"][bit]
            masses = mass_step(masses, bit, F(1, 4), F(1, 4))
            reference = mass_step(reference, bit, F(1, 4), F(1, 4))
            state = controller.step(bit)
            actual = posterior(masses)
            lo, hi = interval(old_table, old_index)
            require(lo <= actual <= hi, "old membership throughout warmup")
            tl, th = interval(pending_table, pending_index)
            require(tl + mu <= posterior(reference) <= th - mu, "proof-reference strict membership")
            true_output = F(1, 4) + actual / 2
            observed = rational(state["prediction"]).fraction()
            if n < threshold:
                require(state["mode"] == "Warm" and state["counter"] == n
                        and state["index"] == old_index and state["target_index"] == pending_index,
                        "both updates and warm counter")
                require(state["prediction"] == old_table["states"][old_index]["readout"]
                        and abs(observed - true_output) <= old_eps, "updated old output")
                max_old_error = max(max_old_error, abs(observed - true_output))
            else:
                require(state["mode"] == "Ready" and state["index"] == pending_index
                        and state["prediction"] == pending_table["states"][pending_index]["readout"],
                        "exact handoff to updated new label")
                require(tl <= actual <= th and abs(observed - true_output) <= target.fraction(),
                        "actual new membership and accuracy at handoff")
        stages.append({"from_eps": pair(old_eps), "to_eps": pair(target.fraction()), "reports": threshold,
                       "word": word, "handoff_index": state["index"],
                       "maximum_warm_output_error": pair(max_old_error),
                       "handoff_output_error": pair(abs(observed - true_output))})
    # Normal Ready updates after the final capture keep the restored invariant.
    for bit in map(int, "11001"):
        state = controller.step(bit)
        masses = mass_step(masses, bit, F(1, 4), F(1, 4))
        lo, hi = interval(controller.table, controller.index)
        require(state["mode"] == "Ready" and lo <= posterior(masses) <= hi,
                "membership after completed switches")

    return {"valid": True, "margin_cases": margin_cases, "nongrid_margin_check": nongrid_result,
            "capture_bound": {"E": pair(error.fraction()), "mu": pair(margin.fraction()),
                              "reports": 10, "posterior_bound": pair(F(793, 6463488)),
                              "bernoulli_reports": 522},
            "resets": resets, "midpoint_targets": new["states"][263]["targets"],
            "ten_report_endpoints": {"terminal_comparisons": leaves,
                                     "minimum_membership_slack": pair(minimum_slack), "witness": witness},
            "logical_examples": {"output_without_membership": {"history": "000", "alternative_label": 449,
                                                                 "output_error": pair(output_error),
                                                                 "upper_endpoint_excess": pair(excess)},
                                 "canonical_histories": histories, "common_reset": resets[23],
                                 "label_only_lower_bound": ["1", "456"]},
            "repeated_switches": stages, "rejected_inputs": rejected}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest="command", required=True)
    test = commands.add_parser("checks")
    test.add_argument("--out")
    stream = commands.add_parser("stream")
    stream.add_argument("--p", type=cli_rational, default=Q(1, 4))
    stream.add_argument("--r", type=cli_rational, default=Q(1, 4))
    stream.add_argument("--eps", type=cli_rational, default=Q(1, 16))
    stream.add_argument("--target", type=cli_rational, default=Q(1, 1024))
    stream.add_argument("--old-label", type=int)
    stream.add_argument("--reports", type=int)
    args = parser.parse_args()
    try:
        if args.command == "checks":
            emit(checks(), args.out)
        else:
            observer = TwoTrackCapture(args.p, args.r, args.eps, args.old_label)
            observer.request(args.target, args.reports)
            stream_capture(observer, sys.stdin.buffer, sys.stdout)
    except (CertificateError, AssertionError, ValueError, OSError) as exc:
        print(json.dumps({"valid": False, "error": str(exc)}), file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
