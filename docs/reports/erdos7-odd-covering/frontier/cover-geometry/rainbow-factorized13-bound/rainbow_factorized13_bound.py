#!/usr/bin/env python3
"""Exact finite rainbow / factorized13 continuation certificate.

Independent standalone arithmetic; no project producer or input is loaded.
Infinite comparison chains are summed by exact geometric mass and first
moments.  General containment and delayed-split domination are ordinary
proofs supplied separately, not inferences from these finite checks.
"""
from fractions import Fraction as F
from itertools import product
from pathlib import Path
import hashlib
import json

N = E = 4
C11 = F(5, 3)
r11 = F(1, 11 ** E)
w5 = (1 + F(1, 5 ** N)) / 2
w7 = (2 + F(1, 7 ** N)) / 3
m5 = (1 - F(1, 5 ** N)) / 4
m7 = (1 - F(1, 7 ** N)) / 3
eta_mass = m5 * m7
checks = {}


def require(name, condition):
    if name in checks:
        raise ValueError("duplicate check name: " + name)
    checks[name] = bool(condition)
    if not condition:
        raise ValueError(name)


# Fixed color table. The ten colors index terminal 11-adic digits.
RAINBOW = {
    (0, 0): (0, 4), (0, 1): (2, 6), (0, 2): (8, 8),
    (0, 3): (1, 1), (0, 4): (3, 3), (0, 5): (5, 5),
    (0, 6): (7, 7), (0, 7): (9, 9),
    (1, 0): (1, 5), (1, 1): (3, 7), (1, 2): (9, 9),
    (2, 0): (8, 8), (2, 1): (9, 9), (3, 0): (2, 2),
    (4, 0): (3, 3), (5, 0): (6, 6), (6, 0): (7, 7),
    (7, 0): (9, 9),
}
O, C = (1, 1), (2, 2)


def A(n):
    return (n, 2)


def B(n):
    return (2, n)


def active(x, y):
    return [(a, b, slot, colors[slot])
            for (a, b), colors in RAINBOW.items() for slot in (0, 1)
            if a < x[slot] and b < y[slot]]


boundaries = ((A(8), O), (B(8), O), (O, A(8)), (O, B(8)),
              (A(3), C), (B(3), C), (C, A(3)), (C, B(3)))
private_boundaries = {}
require("18_numerical_cofactors", len(RAINBOW) == 18)
require("36_slot_occurrences", sum(len(v) for v in RAINBOW.values()) == 36)
require("four_color9_cofactors", {ab for ab, colors in RAINBOW.items() if 9 in colors}
        == {(0, 7), (1, 2), (2, 1), (7, 0)})
for i, (x, y) in enumerate(boundaries):
    entries = active(x, y)
    require("rainbow_boundary_" + str(i), len(entries) == 10 and sorted(e[3] for e in entries) == list(range(10)))
    for a, b, slot, color in entries:
        private_boundaries.setdefault((a, b, slot), i)
require("private_boundary_for_all36_occurrences", len(private_boundaries) == 36)
states = [O, C] + [s for n in range(3, 11) for s in (A(n), B(n))]
small_count = 0
for x, y in product(states, repeat=2):
    colors = {e[3] for e in active(x, y)}
    load = x[0] * y[0] + x[1] * y[1]
    if len(colors) != min(10, load) or ((9 in colors) != (len(colors) == 10)):
        raise ValueError("rainbow/safe9 small-state check")
    small_count += 1
require("324_small_pairs_and_safe9", small_count == 324)
require("finite_original_inventory", 4 * N + 2 * N * N + 36 * E == 192)


def geom_tail(p, start):
    mass = F(1, p ** (start - 1))
    moment = mass * (start + F(1, p - 1))
    return mass, moment


# Atoms store (old joint state, smallest13 count, mass, first13 moment).
# Old branch counts>=8 may be clipped to8: K is then already saturated.
def coordinate_atoms(p, w, kind):
    atoms = []

    def atom(state, n, mass, moment=None):
        atoms.append((state, n, mass, n * mass if moment is None else moment))

    if kind == "T":
        atom(O, 1, w - F(1, p))
        atom(C, 2, F(p - 3, p * p))
        mass, moment = geom_tail(p, 3)
        atom(C, 3, mass, moment)
    elif kind == "D":
        atom(O, 1, w - F(2, p))
        atom(O, 2, F(p - 1, p * p))
        mass, moment = geom_tail(p, 3)
        atom(O, 3, mass, moment)
        atom(C, 1, F(p - 2, p * p))
    else:
        raise ValueError(kind)
    fixed_count = 2 if kind == "T" else 1
    for orientation in (A, B):
        for n in range(3, 8):
            atom(orientation(n), fixed_count, F(p - 1, p ** n))
        mass, _ = geom_tail(p, 8)
        atom(orientation(8), fixed_count, mass)
    require("coordinate_mass_" + str(p) + kind, sum(t[2] for t in atoms) == w)
    require("coordinate_first_moment_" + str(p) + kind,
            sum(t[3] for t in atoms) == w + F(1, p - 1))
    return atoms


def pure_fibre(k):
    g = 1 - F(k, 10) * (1 - r11)
    h = min(C11, 1 / g)
    return g, h, h * g


def integrated_psi(k, values):
    a, b, c, moment = values
    g, h, s = pure_fibre(k)
    if k == 10:
        return C11 * r11 * ((E + F(11, 10)) * (a + 2 * b + moment) - 2 * (a + b + c))
    return h * a / 110 + h * b / 5 + (s + h / 10) * moment - 2 * s * c


def slope(k):
    _, h, s = pure_fibre(k)
    return C11 * r11 * (E + F(11, 10)) if k == 10 else s + h / 10


slopes = {k: slope(k) for k in range(4, 11)}
require("all_delayed_split_slopes_nonincreasing", all(slopes[k] >= slopes[k + 1] for k in range(4, 10)))
require("all_delayed_split_slopes_positive", min(slopes.values()) > 0)

atoms = {(p, kind): coordinate_atoms(p, w, kind)
         for p, w in ((5, w5), (7, w7)) for kind in ("T", "D")}
type_results = {}
for kind5, kind7 in product(("T", "D"), repeat=2):
    groups = {k: [F(0)] * 4 for k in (2, 4, 5, 6, 7, 8, 9, 10)}
    for x, y in product(atoms[(5, kind5)], atoms[(7, kind7)]):
        state5, n5, mass5, moment5 = x
        state7, n7, mass7, moment7 = y
        k = min(10, state5[0] * state7[0] + state5[1] * state7[1])
        mass, moment = mass5 * mass7, moment5 * moment7
        category = n5 * n7
        if category == 1:
            groups[k][0] += mass
        elif category == 2:
            groups[k][1] += mass
        else:
            groups[k][2] += mass
            groups[k][3] += moment
    if kind5 == "T":
        eta_groups = [eta_mass, F(0), F(0), F(0)]
    else:
        eta_groups = [(m5 - F(1, 5)) * m7, F(4, 25) * m7,
                      F(1, 25) * m7, F(13, 100) * m7]
    groups[2] = [u - v for u, v in zip(groups[2], eta_groups)]
    name = kind5 + kind7
    require("actual_old_mass_" + name, sum(sum(v[:3]) for v in groups.values()) == w5 * w7 - eta_mass)
    require("all_actual_bins_nonnegative_" + name, all(v >= 0 for values in groups.values() for v in values))
    H = sum(integrated_psi(k, values) for k, values in groups.items())
    type_results[name] = {"groups_A_B_C_R": groups, "transported_hinge_upper": H,
                          "eta_groups_A_B_C_R": eta_groups}

expected_td = {
    2: [F(9444, 300125), F(1128, 30625), F(188, 30625), F(1786, 91875)],
    4: [F(188, 6125), F(366, 12005), F(1944, 60025), F(200681, 1440600)],
    5: [F(2256, 214375), F(1464, 60025), F(8, 875), F(104, 2625)],
    6: [F(2256, 1500625), F(1464, 300125), F(8, 4375), F(104, 13125)],
    7: [F(2256, 10504375), F(1464, 1500625), F(8, 21875), F(104, 65625)],
    8: [F(2256, 73530625), F(62714, 7503125), F(3181, 765625), F(124787, 9187500)],
    9: [F(2256, 514714375), F(1464, 37515625), F(8, 546875), F(104, 1640625)],
    10: [F(376, 514714375), F(551616, 37515625), F(6264, 3828125), F(122239, 22968750)],
}
for k, expected in expected_td.items():
    require("TD_exact_bin_" + str(k), type_results["TD"]["groups_A_B_C_R"][k] == expected)
expected_types = {
    "TT": F(9087451444165575901661, 79759312825447505250000),
    "TD": F(13869387400909870454063, 79759312825447505250000),
    "DT": F(110198996442912490409, 805649624499469750000),
    "DD": F(11556805628235524546587, 79759312825447505250000),
}
for name, expected in expected_types.items():
    require("exact_type_" + name, type_results[name]["transported_hinge_upper"] == expected)
Hmax = type_results["TD"]["transported_hinge_upper"]
require("TD_is_largest_of_complete_four_type_reduction", Hmax == max(t["transported_hinge_upper"] for t in type_results.values()))

F13 = (w5 + F(1, 4)) * (w7 + F(1, 6)) * F(7, 6) - 2 * w5 * w7 + (w5 - F(1, 5)) * (w7 - F(1, 7)) * F(28, 33)
raw_gap = F13 - Hmax
credit13 = raw_gap / 4
c0 = F(6168733163201163811, 542935350932041267200)
T = F(257, 51)
needed_saving = c0 / (T - 2)
require("N4_source_masses", (w5, w7, eta_mass) == (F(313, 625), F(1601, 2401), F(4992, 60025)))
require("N4_actual_old_mass", w5 * w7 - eta_mass == F(53759, 214375))
require("exact_F13", F13 == F(93139019, 475398000))
require("exact_raw_gap", raw_gap == F(878448290756953416781, 39879656412723752625000))
require("exact_actual13_credit", credit13 == F(878448290756953416781, 159518625650895010500000))
require("exact_NC4_mass_target", needed_saving == F(6168733163201163811, 1650097635185615616000))
require("strict_mass_saving_margin", credit13 - needed_saving == F(9868274731167038268676761238529, 5580136418937173098165192032000000) > 0)
require("strict_NC4_margin", (T - 2) * credit13 - c0 == F(9868274731167038268676761238529, 1836044886230940825847901894400000) > 0)

out = {"complete": True,
       "scope": "Finite N=E=4 actual rainbow prefix; arbitrary finite13 inventories admitting full-root factorized nested5/7 comparison completions reused at every old11 exponent; arbitrary fixed old11 phases. No arbitrary-support-dependent closure is claimed.",
       "N": N, "E": E, "w5": w5, "w7": w7, "eta_mass": eta_mass,
       "rainbow_table": [{"a": a, "b": b, "colors": colors} for (a, b), colors in sorted(RAINBOW.items())],
       "rainbow_boundaries": [{"old5": x, "old7": y} for x, y in boundaries],
       "private_boundary_indices": [{"a": a, "b": b, "slot": j, "boundary": i}
                                     for (a, b, j), i in sorted(private_boundaries.items())],
       "finite_original_count": 192, "small_joint_state_pairs_checked": small_count,
       "delayed_split_slopes_K4_to10": slopes,
       "coordinate_atoms": {str(p) + k: [{"old_state": a[0], "minimum_count13": a[1], "mass": a[2], "first_moment13": a[3]} for a in v]
                            for (p, k), v in atoms.items()},
       "four_type_results": type_results,
       "Hmax": Hmax, "F13": F13, "raw_gap": raw_gap,
       "absolute_row13_saving_lower": credit13,
       "NC4_required_absolute_saving": needed_saving,
       "strict_mass_saving_margin": credit13 - needed_saving,
       "strict_NC4_margin": (T - 2) * credit13 - c0,
       "checks": checks, "passed_count": len(checks),
       "verification_boundary": "Exact finite arithmetic and geometric tails. Arbitrary-depth rainbow containment, full-root classification and delayed-split domination require the accompanying general proofs. No Lean or old producer run."}


def encode(value):
    if isinstance(value, F):
        return str(value)
    raise TypeError(type(value).__name__)


dest = Path(__file__).with_suffix(".json")
dest.write_text(json.dumps(out, indent=2, default=encode) + "\n", encoding="utf-8")
print(json.dumps({"passed_count": len(checks), "four_type_bounds": {k: str(v["transported_hinge_upper"]) for k, v in type_results.items()},
                  "Hmax": str(Hmax), "credit13": str(credit13),
                  "NC4_margin": str((T - 2) * credit13 - c0), "output": str(dest),
                  "sha256": hashlib.sha256(dest.read_bytes()).hexdigest()}, indent=2))
