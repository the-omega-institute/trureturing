#!/usr/bin/env python3
"""A literal fixed-threshold source with uniform current marginal.

The adjacent balanced_prefix_budget.py supplies only CRT, exact prefix
partitions and the clipped-kernel formula. This producer rebuilds its own
31-label physical source and never imports a balanced source's law.
All arithmetic is rational; checks remain active under Python -O.
"""

import argparse
from collections import defaultdict
from fractions import Fraction as F
import importlib.util
import json
from pathlib import Path


def require(condition, message):
    if not condition:
        raise ValueError(message)


helper_path = Path(__file__).resolve().with_name("balanced_prefix_budget.py")
spec = importlib.util.spec_from_file_location("balanced_prefix_helpers", helper_path)
require(spec is not None and spec.loader is not None, "missing prefix helpers")
helpers = importlib.util.module_from_spec(spec)
spec.loader.exec_module(helpers)

GROUPS = (
    (1, 5, 375, 405, 625, 2025, 3125),
    (3, 15, 225, 243, 6075),
    (9, 25, 27, 125, 1125, 1875, 3375),
    (45, 81, 135, 675, 5625),
    (729, 2187, 3645),
    (6561,),
)


def monomial(value):
    remainder, exponents = value, []
    for prime in (3, 5):
        exponent = 0
        while remainder % prime == 0:
            remainder //= prime
            exponent += 1
        exponents.append(exponent)
    require(remainder == 1, "weight outside the 3,5 monomials")
    return exponents


def make_source():
    weights = [value for group in GROUPS for value in group]
    require(len(weights) == len(set(weights)) == 28, "distinct monomial weights")
    require(all(sum(group) == 6561 for group in GROUPS), "equal-sum groups")
    labels = []
    for color, group in enumerate(GROUPS, 1):
        for value in group:
            i, j = monomial(value)
            a, b = 12-i, 6-j
            index = len(labels)
            residue = 1+index+index//2
            modulus, joined = helpers.crt(((3**a, residue), (5**b, 1), (7, color)))
            labels.append({
                "modulus": modulus, "residue": joined,
                "r_depth": a, "s_depth": b,
                "r_residue": residue, "s_residue": 1, "color": color,
            })
    require(all(label["r_depth"] >= 4 and label["s_depth"] >= 1
                for label in labels), "old-depth range")
    require(len({label["r_residue"] % 81 for label in labels}) == 28,
            "disjoint old rectangles")
    family = [{"modulus": q, "residue": 0} for q in (3, 5, 7)]+labels
    require(len({label["modulus"] for label in family}) == 31,
            "repeated original numerical modulus")
    require(all(label["modulus"] > 1 and label["modulus"] % 2 for label in family),
            "non-odd or unit original modulus")
    require(all(2 % label["modulus"] != label["residue"] for label in family),
            "avoiding integer fails")
    return labels, family


def run(deltas):
    labels, family = make_source()
    xs = helpers.prefix_cells(3, 12, [(a["r_residue"], a["r_depth"]) for a in labels])
    ys = helpers.prefix_cells(5, 6, [(a["s_residue"], a["s_depth"]) for a in labels])
    require((len(xs), len(ys)) == (352, 24), "exact partition sizes")
    policies = []
    for delta in deltas:
        require(0 < delta < 1, "threshold outside (0,1)")
        current = defaultdict(F)
        pairs, bases = [defaultdict(F), defaultdict(F)], [defaultdict(F), defaultdict(F)]
        active = surplus = F(0)
        color_bad_mass = defaultdict(F)
        for x, ex, wx in xs:
            for y, ey, wy in ys:
                bad = {a["color"] for a in labels
                       if x % 3**a["r_depth"] == a["r_residue"]
                       and y % 5**a["s_depth"] == a["s_residue"]}
                require(len(bad) <= 1, "source rectangles overlap")
                alpha, base_mass, row_mass = F(len(bad), 6), wx*wy, F(0)
                if bad:
                    active += base_mass
                    color_bad_mass[next(iter(bad))] += base_mass
                for color in range(1, 7):
                    density = helpers.clipped(alpha, delta, color in bad)
                    mass = base_mass*density/6
                    current[color] += mass
                    row_mass += density/6
                    for axis, key in enumerate(((x, ex, color), (y, ey, color))):
                        pairs[axis][key] += mass
                        bases[axis][key] += base_mass/6
                    if color not in bad:
                        surplus += base_mass*(density-1)/6
                require(row_mass == 1, "physical row normalization")
        require(all(current[c] == F(1, 6) for c in range(1, 7)),
                "exact current stationarity")
        require(active == F(1, 112500)
                and all(color_bad_mass[c] == F(1, 675000) for c in range(1, 7)),
                "exact color trigger masses")
        u = min(F(1, 6), delta)/(1-min(F(1, 6), delta))
        require(surplus == F(5, 6)*u*active > 0, "positive head surplus")
        distances = [sum((abs(v-bases[i][key]) for key, v in pair.items()), F(0))/2
                     for i, pair in enumerate(pairs)]
        require(distances == [surplus, F(12958, 19683)*surplus],
                "full pair total-variation defects")
        policies.append({
            "delta7": delta, "current_marginal": [current[c] for c in range(1, 7)],
            "active_old_mass": active,
            "color_trigger_masses": [color_bad_mass[c] for c in range(1, 7)],
            "head_surplus": surplus, "pair_total_variation_rp_sp": distances,
        })
    return {
        "scope": "31-label current-stationarity witness; both full pair products fail; not an odd covering",
        "old_heights": [12, 6], "old_surviving_word_count": 2*3**11*4*5**5,
        "exact_prefix_partition_sizes": [len(xs), len(ys)],
        "equal_sum_monomial_groups": GROUPS, "group_sum": 6561,
        "original_labels": family, "avoiding_integer": 2, "policies": policies,
    }


def encode(value):
    if isinstance(value, F):
        return str(value)
    raise TypeError(type(value).__name__)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    parser.add_argument("--delta", type=F, action="append",
                        help="rational threshold; repeat to select several policies")
    args = parser.parse_args()
    result = json.dumps(run(args.delta or [F(1, 96), F(1, 6), F(1, 5)]),
                        default=encode, indent=2, sort_keys=True)+"\n"
    if args.output:
        args.output.write_text(result, encoding="utf-8")
    else:
        print(result, end="")
