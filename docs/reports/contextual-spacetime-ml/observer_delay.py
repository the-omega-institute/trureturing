#!/usr/bin/env python3
"""Exact finite comparisons for observation companion §45.

Python 3.10+, standard library only. All-word bounds are paper arguments;
the retained suffix and endpoint enumerations check only their stated domains.
"""

import argparse
import copy
from fractions import Fraction as F
import json
import sys

from rational_observer import (CertificateError, Q, construct, emit, nearest,
                               require, update, verify)
from observer_capture import (center, history, interval, mass_step, pair,
                              posterior, strict_margins, sufficient_reports,
                              threshold_holds, verify_margin)


def report_bounds(eps):
    """Integer thresholds L, U, V for a rational 0 < eps <= 1/16."""
    if not isinstance(eps, Q) or not 0 < 16 * eps.n <= eps.d:
        raise CertificateError("delay target requires a rational 0 < eps <= 1/16")
    lower = tracker = 0
    upper = 1
    while 506 * eps.n * 6**lower < eps.d:
        lower += 1
    while eps.n * 2**(upper + 1) < 3 * eps.d:
        upper += 1
    while 16 * eps.n * 2**tracker < eps.d:
        tracker += 1
    return {"necessary_lower": lower, "conservative_capture_upper": upper,
            "exact_center_tracker_upper": tracker}


def checks():
    p = r = Q(1, 4)
    fp = fr = F(1, 4)
    eps = Q(1, 1024)
    old = construct(p, r, Q(1, 16))
    new = construct(p, r, eps)
    old_check = verify(old)
    env, edge, margin = strict_margins(p, r, eps)
    new_check = verify_margin(new, margin)  # Includes the ordinary verifier.
    for name, result in (("old", old_check), ("target", new_check)):
        require(result["valid"], f"{name} certificate rejected: {result}")
        require("failures" not in result, f"{name} success schema")
    old_m, new_m = len(old["states"]) - 1, len(new["states"]) - 1
    require((old_m, new_m) == (28, 526), "old and target grid sizes")

    collision, initial_masses = {}, []
    cases = [
        ("0000", [14, 21, 23, 24, 24], (F(63, 2048), F(135, 2048)),
         F(15, 22), F(13, 22), F(99, 1024)),
        ("1000", [14, 7, 18, 22, 24], (F(45, 2048), F(93, 2048)),
         F(31, 46), F(27, 46), F(69, 1024)),
    ]
    for word, expected_labels, expected_masses, q, prediction, probability in cases:
        masses, labels = history(old, word, fp, fr)
        require(labels == expected_labels and masses == expected_masses,
                f"same-length collision path and masses: {word}")
        require(posterior(masses) == q and fp + q / 2 == prediction
                and sum(masses) == probability, f"collision normalization: {word}")
        collision[word] = {"labels": labels, "descriptor": [labels[-1], len(word)],
                           "masses": [pair(x) for x in masses],
                           "posterior": pair(q), "next_zero": pair(prediction),
                           "word_probability": pair(probability)}
        initial_masses.append(masses)
    require((posterior(initial_masses[0]) - posterior(initial_masses[1])) / 2
            == F(1, 253), "collision prediction gap")

    # Independent hidden-mass continuation, including the empty suffix.
    by_length = [{"reports": n, "prefixes": 0} for n in range(9)]
    minima = [None] * 9
    stack = [("", *initial_masses)]
    while stack:
        word, left, right = stack.pop()
        n = len(word)
        gap = (posterior(left) - posterior(right)) / 2
        require(gap >= F(1, 253 * 6**n), f"persistent gap: {word!r}")
        for masses, initial in zip((left, right), initial_masses):
            require(sum(masses) / sum(initial) >= fp**n,
                    f"positive conditional continuation: {word!r}")
        row = by_length[n]
        row["prefixes"] += 1
        if minima[n] is None or gap < minima[n]:
            minima[n] = gap
            row.update({"minimum_prediction_gap": pair(gap), "witness": word})
        if n < 8:
            for bit in (1, 0):
                stack.append((word + str(bit), mass_step(left, bit, fp, fr),
                              mass_step(right, bit, fp, fr)))
    require([x["prefixes"] for x in by_length] == [2**n for n in range(9)],
            "complete suffix tree through length eight")

    boundaries = []
    for target, expected_lower in ((Q(1, 506), 0), (Q(1, 507), 1),
                                    (Q(1, 3036), 1), (Q(1, 3037), 2)):
        bounds = report_bounds(target)
        n = bounds["necessary_lower"]
        require(n == expected_lower, "lower threshold equality or adjacent case")
        require(506 * target.n * 6**n >= target.d
                and (n == 0 or 506 * target.n * 6**(n - 1) < target.d),
                "lower threshold and predecessor")
        boundaries.append({"eps": target.pair(), **bounds,
                           "lower_threshold_product": pair(506 * target.fraction() * 6**n)})
    for target, upper, tracker in ((Q(1, 16), 5, 0), (Q(1, 32), 6, 1),
                                    (Q(3, 64), 5, 1), (Q(3, 65), 6, 1)):
        bounds = report_bounds(target)
        require((bounds["conservative_capture_upper"], bounds["exact_center_tracker_upper"])
                == (upper, tracker), "upper and tracker threshold boundaries")
        boundaries.append({"eps": target.pair(), **bounds})
    require(report_bounds(Q(2, 2048)) == report_bounds(eps), "unreduced target")

    bounds = report_bounds(eps)
    error = Q(1, 2) + Q(4, 3 * new_m)
    capture = sufficient_reports(Q(1, 2), error, margin)
    require(bounds == {"necessary_lower": 1, "conservative_capture_upper": 11,
                       "exact_center_tracker_upper": 6} and capture == 10,
            "four distinct report quantities")
    require([x.fraction() for x in (error, env, edge, margin)]
            == [F(793, 1578), F(4, 16641), F(1, 20), F(4, 16641)],
            "delivered capture constants")
    require(not threshold_holds(Q(1, 2), error, margin, 9)
            and threshold_holds(Q(1, 2), error, margin, 10),
            "capture sufficient inequality boundary")
    conservative_error = error.fraction() / (4 * 2**bounds["conservative_capture_upper"])
    require(error.fraction() < F(2, 3)
            and conservative_error < eps.fraction() / 9 <= margin.fraction(),
            "strict conservative capture")
    resets = [nearest(Q(new_m * j, old_m)) for j in (7, 21, 24)]
    require(resets == [131, 394, 451], "actual ties-down reset")

    # Compare the exact center tracker with every old interval endpoint and
    # every six-report word. Monotonicity extends endpoints in the paper proof.
    tracker_reports = bounds["exact_center_tracker_upper"]
    terminal_cases, max_error, witness = 0, F(0), None
    for j in range(old_m + 1):
        for side, endpoint in zip(("lo", "hi"), interval(old, j)):
            stack = [("", (1 - endpoint, endpoint), center(old_m, j, fr))]
            while stack:
                word, masses, tracker = stack.pop()
                if len(word) == tracker_reports:
                    error_now = abs(posterior(masses) - tracker) / 2
                    require(error_now < F(1, 16 * 2**tracker_reports),
                            f"tracker endpoint error: {j}/{side}/{word}")
                    terminal_cases += 1
                    if error_now > max_error:
                        max_error = error_now
                        witness = {"old_label": j, "endpoint": side, "word": word}
                else:
                    for bit in (1, 0):
                        next_tracker = update(p, r, Q(tracker.numerator, tracker.denominator),
                                              bit).fraction()
                        stack.append((word + str(bit), mass_step(masses, bit, fp, fr),
                                      next_tracker))
    require(terminal_cases == 3712, "29 old intervals x 2 endpoints x 64 words")

    rejected = []
    for name, target in (("zero", Q(0)), ("negative", Q(-1, 1024)),
                         ("above_domain", Q(1, 15)), ("wrong_carrier", F(1, 1024))):
        try:
            report_bounds(target)
        except CertificateError:
            rejected.append(name)
        else:
            raise AssertionError(f"invalid delay target accepted: {name}")
    corrupted = copy.deepcopy(old)
    corrupted["states"][old["initial"]]["readout"] = ["0", "1"]
    rejected_certificate = verify(corrupted)
    require(not rejected_certificate["valid"] and rejected_certificate.get("failures"),
            "ordinary verifier must name rejected readout")

    return {
        "valid": True,
        "scope": "Finite exact comparisons; no all-history or optimal-constant certification.",
        "certificates": {"old": old_check, "target_strict": new_check},
        "collision": collision,
        "initial_prediction_gap": ["1", "253"],
        "suffix_checks": {"maximum_reports": 8, "prefixes": sum(x["prefixes"] for x in by_length),
                          "by_length": by_length},
        "threshold_boundaries": boundaries,
        "target_example": {"eps": eps.pair(), "m": new_m, **bounds,
                           "sufficient_capture_reports": capture,
                           "E": pair(error.fraction()), "mu": pair(margin.fraction()),
                           "conservative_posterior_bound": pair(conservative_error),
                           "reset_labels_for_7_21_24": resets,
                           "scope": "L is necessary; capture, U and V are sufficient for their distinct tasks."},
        "tracker_endpoint_checks": {"reports": tracker_reports, "terminal_comparisons": terminal_cases,
                                    "maximum_prediction_error": pair(max_error), "witness": witness,
                                    "scope": "All 29 old intervals, both endpoints, all 64 six-report words."},
        "rejected_inputs": rejected,
        "expected_readout_rejection": rejected_certificate,
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest="command", required=True)
    check = commands.add_parser("checks")
    check.add_argument("--out")
    args = parser.parse_args()
    try:
        emit(checks(), args.out)
    except (CertificateError, AssertionError, ValueError, OSError) as exc:
        print(json.dumps({"valid": False, "error": str(exc)}), file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
