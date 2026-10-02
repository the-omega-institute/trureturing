"""Exact coherent-prefix improvement on one retained five-leaf source.

Uses all divisors of 45 and enumerates every complete phase layout. No solver,
third-party imports, input-source search, or approximate arithmetic is used.
Normal execution checks the saved result; --write-result regenerates it.
"""

import argparse
from collections import Counter
from fractions import Fraction
from itertools import product
import json
from math import lcm, prod
from pathlib import Path


LEAVES = (4, 7, 2, 5, 8)
LABELS = (1, 3, 5, 9, 15, 45)
WEIGHTS = {2: 8, 4: 6, 7: 3, 13: 3}
DENOMINATOR = 200


def compute():
    checks = 0

    def require(condition, description):
        nonlocal checks
        checks += 1
        if not condition:
            raise ValueError(description)

    source = [x for x in range(45) if x % 9 in LEAVES]
    require(len(source) == 25, "full source has 25 live cells")
    require(LABELS == tuple(d for d in range(1, 46) if 45 % d == 0),
            "prefix contains every numerical divisor including the unit")
    nu = {x: Fraction(WEIGHTS.get(x, 0), DENOMINATOR) for x in range(45)}
    for x in range(45):
        full_mass = Fraction(1, 25) if x in source else Fraction(0)
        require(0 <= nu[x] <= full_mass, "same-source dominated retention")

    retained_table = [[Fraction(0)] * 5 for _ in LEAVES]
    for x, numerator in WEIGHTS.items():
        retained_table[LEAVES.index(x % 9)][x % 5] = Fraction(
            5 * numerator, DENOMINATOR)
    require(all(0 <= u <= Fraction(1, 5)
                for row in retained_table for u in row),
            "one retained table lies below the five leaf weights")
    for x in source:
        require(nu[x] == retained_table[LEAVES.index(x % 9)][x % 5] / 5,
                "one table realizes the literal retained measure")
    mass = sum(nu.values(), Fraction(0))
    require(mass == Fraction(1, 10), "unnormalized retained mass")

    profiles = {
        d: [sum((nu[x] for x in range(45) if x % d == a), Fraction(0))
            for a in range(d)]
        for d in LABELS
    }
    maxima = {d: max(values) for d, values in profiles.items()}
    tuple_counts = Counter(lcm(*labels) for labels in product(LABELS, repeat=4))
    require(sum(tuple_counts.values()) == len(LABELS) ** 4,
            "all ordered prefix tuples are included")
    require(dict(tuple_counts) == {1: 1, 3: 15, 5: 15, 9: 65,
                                   15: 225, 45: 975},
            "coordinatewise maximum-depth tuple multiplicities")
    tuple_upper = sum((count * maxima[d] for d, count in tuple_counts.items()),
                      Fraction(0))

    maximum_numerator = -1
    maximizing_phases = None
    number_of_maximizers = 0
    layout_count = 0
    for phases in product(*(range(d) for d in LABELS[1:])):
        numerator = sum(
            weight * (1 + sum(x % d == phase
                              for d, phase in zip(LABELS[1:], phases))) ** 4
            for x, weight in WEIGHTS.items()
        )
        layout_count += 1
        if numerator > maximum_numerator:
            maximum_numerator = numerator
            maximizing_phases = phases
            number_of_maximizers = 1
        elif numerator == maximum_numerator:
            number_of_maximizers += 1
        require(Fraction(numerator, DENOMINATOR) <= tuple_upper,
                "one coherent phase table satisfies the tuple upper bound")
    prefix_bound = Fraction(maximum_numerator, DENOMINATOR)
    require(layout_count == prod(LABELS) == 91125,
            "every complete independent phase table was considered")
    require(prefix_bound == Fraction(417, 8) and tuple_upper == Fraction(211, 4),
            "exact global-layout and separately maximized tuple moments")
    require(tuple_upper - prefix_bound == Fraction(5, 8)
            and maximizing_phases == (2, 2, 2, 2, 2)
            and number_of_maximizers == 1,
            "strict gap and a unique realized complete maximizing layout")

    empty = (
        mass,
        max(sum(profiles[9][leaf] for leaf in (4, 7)),
            sum(profiles[9][leaf] for leaf in (2, 5, 8))),
        max(profiles[9]),
    )
    queried = (
        max(sum(row[colour] for row in retained_table) for colour in range(5)),
        max(max(sum(retained_table[leaf][colour] for leaf in (0, 1)),
                sum(retained_table[leaf][colour] for leaf in (2, 3, 4)))
            for colour in range(5)),
        max(max(row) for row in retained_table),
    )
    require(empty == (Fraction(1, 10), Fraction(3, 50), Fraction(9, 200)),
            "empty-support common-colour envelopes")
    require(queried == (Fraction(11, 40), Fraction(1, 5), Fraction(1, 5)),
            "queried-5 common-colour envelopes")

    def a4(q):
        t = Fraction(1, q - 1)
        return 15 * t + 50 * t**2 + 60 * t**3 + 24 * t**4

    ternary_full = 9 * (a4(3) - Fraction(15, 3))
    require(ternary_full == 216, "complete ternary depth-at-least-two series")
    finite_box = (empty[0] + 15 * empty[1] + 65 * empty[2]
                  + Fraction(15, 5) * (queried[0] + 15 * queried[1]
                                      + 65 * queried[2]))
    full_height = (empty[0] + 15 * empty[1] + ternary_full * empty[2]
                   + a4(5) * (queried[0] + 15 * queried[1]
                              + ternary_full * queried[2]))
    require(finite_box == tuple_upper, "finite-box coefficients equal exact tuple maxima")
    remainder = full_height - finite_box
    require(remainder == Fraction(2082643, 6400) and remainder > 0,
            "complete all-height complement including mixed tuples")
    improved = prefix_bound + remainder
    require(full_height == Fraction(2420243, 6400)
            and improved == Fraction(2416243, 6400),
            "full-height old and coherent-prefix bounds")
    require(full_height - improved == Fraction(5, 8),
            "strict finite gain survives the entire all-height remainder")

    return {
        "scope": "One genuine retained five-leaf/Haar-5 source. Complete phase "
                 "layouts on all divisors of 45, plus the full all-height "
                 "maximum-depth remainder. No seven-prime positivity claim "
                 "and no Lean verification.",
        "checks": checks,
        "labels": list(LABELS),
        "full_source_mass": "1",
        "retained_mass": str(mass),
        "retained_weights": {str(x): str(value) for x, value in nu.items() if value},
        "retained_table": [[str(value) for value in row] for row in retained_table],
        "ordered_prefix_tuple_counts": {str(d): tuple_counts[d] for d in LABELS},
        "phase_layouts_checked": layout_count,
        "maximizing_phases": list(maximizing_phases),
        "number_of_maximizers": number_of_maximizers,
        "max_global_layout_fourth": str(prefix_bound),
        "sum_of_tuple_maxima": str(tuple_upper),
        "strict_gap": str(tuple_upper - prefix_bound),
        "cylinder_maxima": {str(d): str(value) for d, value in maxima.items()},
        "empty_envelopes": list(map(str, empty)),
        "queried5_envelopes": list(map(str, queried)),
        "full_ternary_depth_coefficient": str(ternary_full),
        "full_height_generic_moment": str(full_height),
        "finite_box_generic_moment": str(finite_box),
        "unbounded_height_remainder": str(remainder),
        "prefix_phase_coherent_plus_full_remainder": str(improved),
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--result", type=Path,
                        default=Path(__file__).with_suffix(".json"))
    parser.add_argument("--write-result", action="store_true")
    args = parser.parse_args()
    result = compute()
    if args.write_result:
        args.result.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    else:
        saved = json.loads(args.result.read_text(encoding="utf-8"))
        if saved != result:
            raise ValueError("saved result differs from exact reconstruction")
    print(json.dumps({key: result[key] for key in (
        "checks", "phase_layouts_checked", "max_global_layout_fourth",
        "sum_of_tuple_maxima", "strict_gap", "full_height_generic_moment",
        "prefix_phase_coherent_plus_full_remainder")}))


if __name__ == "__main__":
    main()
