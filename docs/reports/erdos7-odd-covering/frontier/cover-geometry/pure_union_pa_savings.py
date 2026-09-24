#!/usr/bin/env python3
"""Exact constants for joint pure-union savings in the four actual PA rows.

Only the Python standard library is used. All auxiliary tails enter through
their exact first moments. This computes the constants of an ordinary
inequality; it does not enumerate original families or verify Lean.
"""
import argparse
from fractions import Fraction as F
import hashlib
import json
from math import prod
from pathlib import Path

ROWS = ((11, 2, F(5, 3), F(1, 3)),
        (13, 2, F(3, 2), F(1, 4)),
        (17, 4, F(2), F(1, 4)),
        (19, 4, F(9, 5), F(1, 5)))


def coordinate(prime, mass, multiplier):
    # Positive count n>=2 has weight multiplier*(p-1)/p^n.
    return {"prime": prime, "mass": mass,
            "mean": mass + multiplier / (prime - 1),
            "low": {1: mass - multiplier / prime,
                    2: multiplier * F(prime - 1, prime**2),
                    3: multiplier * F(prime - 1, prime**3)}}


def hinge(coordinates, threshold):
    law = {1: F(1)}
    for c in coordinates:
        updated = {}
        for n, weight in law.items():
            for m, probability in c["low"].items():
                if n * m < threshold:
                    index = n * m
                    updated[index] = updated.get(index, F(0)) + weight * probability
        law = updated
    mass = prod(c["mass"] for c in coordinates)
    mean = prod(c["mean"] for c in coordinates)
    return mean - threshold * mass + sum((threshold - n) * w for n, w in law.items())


def anchor_data(w5, w7):
    coordinates = [coordinate(5, w5, F(1)), coordinate(7, w7, F(1))]
    charges = {}
    alpha = w5 * w7 - F(1, 12)
    for q, t, cap, coefficient in ROWS:
        charges[q] = hinge(coordinates, t)
        alpha -= coefficient * charges[q]
        coordinates.append(coordinate(q, F(1), cap))
    return {"charges": charges, "alpha": alpha, "Phi": hinge(coordinates, 3)}


def calculate():
    checks = {}

    def require(name, condition):
        if name in checks:
            raise ValueError("duplicate check: " + name)
        checks[name] = bool(condition)
        if not condition:
            raise ValueError(name)

    target = F(257, 51)
    corners = {(x, y): anchor_data(x, y)
               for x in (F(1, 2), F(1)) for y in (F(2, 3), F(1))}
    baseline = corners[F(1, 2), F(2, 3)]
    c0 = baseline["Phi"] - (target - 2) * baseline["alpha"]
    kreq = c0 / (target - 2)
    fmin = baseline["charges"]
    expected = {11: F(97, 840), 13: F(47, 240),
                17: F(202266823897, 1875745872000),
                19: F(807126826607839, 4914954383539200)}
    require("four_minimal_complete_prefix_hinges", fmin == expected)
    require("baseline_alpha", baseline["alpha"] == F(7575003978548161, 73724315753088000))
    require("baseline_Phi", baseline["Phi"] == F(22496082952171, 69510823782400))
    require("NC4_c0", c0 == F(6168733163201163811, 542935350932041267200))
    require("NC4_mass_requirement", kreq == F(6168733163201163811, 1650097635185615616000))
    require("positive_alpha_all_corners", all(z["alpha"] >= baseline["alpha"] > 0 for z in corners.values()))
    require("minimal_hinges_all_corners", all(all(z["charges"][q] >= fmin[q] for q in fmin)
                                            for z in corners.values()))

    # Independent low-product expression at threshold2: just the product1
    # atom is below threshold. This also confirms the explicit F11 formula.
    for (x, y), z in corners.items():
        require("F11_formula_" + str(x) + "_" + str(y),
                z["charges"][11] == x / 42 + y / 20 + F(59, 840))

    def margin(data):
        return (target - 2) * data["alpha"] - data["Phi"]

    base_margin = margin(baseline)
    A5 = 2 * (margin(corners[F(1), F(2, 3)]) - base_margin)
    A7 = 3 * (margin(corners[F(1, 2), F(1)]) - base_margin)
    A57 = 6 * (margin(corners[F(1), F(1)]) - base_margin - A5 / 2 - A7 / 3)
    require("positive_anchor_coefficients", min(A5, A7, A57) > 0)
    require("NC4_anchor_coefficients", (A5, A7, A57) == (
        F(44887686823492905683, 27146767546602063360),
        F(20281636668601030051, 20313907687933516800),
        F(585035299774741193, 203139076879335168)))

    # At most one pure root-q original, at most two at every deeper height.
    # Exact geometric tail: sum_(e>=2) q^-e=1/[q(q-1)].
    row_bounds = {}
    for q, t, cap, a in ROWS:
        p_upper = F(q - 1, 2) * (F(1, q) + F(2, q * (q - 1)))
        require("root_inventory_" + str(q), p_upper == F(q + 1, 2 * q))
        require("PA_parameter_identity_" + str(q), a == 2 * cap / (q - 1) and cap - 1 == a * t)
        gain = a * a * fmin[q] * (1 - p_upper) / (1 + a * (1 - p_upper))
        row_bounds[q] = {"threshold": t, "cap": cap, "coefficient": a,
                         "pure_union_parameter_upper": p_upper,
                         "minimal_prefix_hinge": fmin[q], "saving_lower": gain}
    expected_gains = {11: F(97, 19152), 13: F(47, 9280),
                      17: F(202266823897, 71278343136000),
                      19: F(2421380479823517, 851925426480128000)}
    require("four_root_inventory_savings", {q: z["saving_lower"] for q, z in row_bounds.items()} == expected_gains)
    require("17_alone_not_certified", expected_gains[17] < kreq)
    require("19_alone_not_certified", expected_gains[19] < kreq)

    cases = {}
    for name, selected in (("root11_at_most_one", (11,)),
                           ("root13_at_most_one", (13,)),
                           ("roots17_and19_each_at_most_one", (17, 19))):
        gain = sum((expected_gains[q] for q in selected), F(0))
        delta = (target - 2) * (gain - kreq)
        require("positive_same_law_margin_" + name, delta > 0)
        # lambda(1)<=1 gives R<=T-delta/lambda(1)<=T-delta.
        cases[name] = {"restricted_root_labels": selected,
                       "saving_lower": gain, "saving_margin": gain - kreq,
                       "NC4_margin_lower": delta, "query_upper": target - delta}
    require("root11_uniform_query_bound", cases["root11_at_most_one"]["query_upper"] ==
            F(2733779746141627138211, 542935350932041267200))

    # A single11-row sufficient parameter, with all other savings unused.
    pure11_critical = (fmin[11] - 12 * kreq) / (fmin[11] - 3 * kreq)
    require("pure11_critical_parameter", pure11_critical == F(38840730288863882356, 57346929778467373789))
    require("pure11_critical_identity", F(1, 9) * fmin[11] * (1 - pure11_critical) /
            (1 + F(1, 3) * (1 - pure11_critical)) == kreq)
    return {"scope": "arbitrary finite two-copy families on Q={5,7,11,13,17,19}; stated pure-union conditions",
            "target": target, "minimal_prefix_hinges": fmin,
            "baseline_alpha": baseline["alpha"], "baseline_Phi": baseline["Phi"],
            "NC4_c0": c0, "required_mass_saving": kreq,
            "anchor_coefficients": {"A5": A5, "A7": A7, "A57": A57},
            "corners": [{"w5": x, "w7": y, **z} for (x, y), z in corners.items()],
            "root_inventory_bounds": row_bounds, "sufficient_root_cases": cases,
            "pure11_critical_parameter": pure11_critical,
            "checks": checks, "passed_count": len(checks), "Lean": "not run"}


def encode(value):
    if isinstance(value, F):
        return str(value)
    raise TypeError(type(value).__name__)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=Path(__file__).with_suffix(".json"))
    args = parser.parse_args()
    result = calculate()
    args.output.write_text(json.dumps(result, indent=2, default=encode) + "\n", encoding="utf-8")
    print(json.dumps({"passed_count": result["passed_count"],
                      "sufficient_root_cases": result["sufficient_root_cases"],
                      "json_sha256": hashlib.sha256(args.output.read_bytes()).hexdigest()},
                     indent=2, default=encode))


if __name__ == "__main__":
    main()
