#!/usr/bin/env python3
"""Exact support-dependent queries under the fixed rainbow actual11 law.

Only stdlib is used.  Query old11 phases are the one fixed nested9 chain.
All p-height tails are summed exactly; this is a finite family of complete
query layouts, not all possible support-dependent phases or actual13 losses.
"""
from fractions import Fraction as F
from itertools import product
from pathlib import Path
import hashlib
import json

N = E = 4
W = {5: (1 + F(1, 5 ** N)) / 2, 7: (2 + F(1, 7 ** N)) / 3}
DMASS = {5: (1 - F(1, 5 ** N)) / 4, 7: (1 - F(1, 7 ** N)) / 3}
r11 = F(1, 11 ** E)
checks = {}


def require(name, b):
    if name in checks:
        raise ValueError("duplicate check name")
    checks[name] = bool(b)
    if not b:
        raise ValueError(name)


# Atom: old two-slot count state, mass, conditional mean increments of
# N_T and N_D, and their identically-zero flags.  A positive-tail atom
# keeps its entire exact first moment, never a representative tail count.
def atoms(p):
    out = []

    def add(old, mass, incT, incD, name):
        out.append({"old": old, "mass": mass, "increments": (F(incT), F(incD)),
                    "zero": (incT == 0, incD == 0), "name": name})

    add((1, 1), W[p] - F(2, p), 0, 0, "outside_both_roots")
    add((1, 1), F(1, p), 0, F(p, p - 1), "D_root_complete_tail")
    add((2, 2), F(p - 3, p * p), 1, 0, "C_outside_T_child")
    add((2, 2), F(1, p * p), 2 + F(1, p - 1), 0, "T_child_complete_tail")
    for slot in (0, 1):
        for n in range(3, 8):
            old = (n, 2) if slot == 0 else (2, n)
            add(old, F(p - 1, p ** n), 1, 0, "old_branch_" + str(slot) + "_" + str(n))
        old = (8, 2) if slot == 0 else (2, 8)
        add(old, F(1, p ** 7), 1, 0, "old_branch_" + str(slot) + "_8plus")
    require("p" + str(p) + "_total_mass", sum(a["mass"] for a in out) == W[p])
    for typ in (0, 1):
        require("p" + str(p) + "_increment_moment_" + str(typ),
                sum(a["mass"] * a["increments"][typ] for a in out) == F(1, p - 1))
        require("p" + str(p) + "_zero_increment_mass_" + str(typ),
                sum(a["mass"] for a in out if a["zero"][typ]) == W[p] - F(1, p))
    require("p" + str(p) + "_disjoint_positive_roots", all(a["zero"][0] or a["zero"][1] for a in out))
    return out


coordinate = {p: atoms(p) for p in (5, 7)}
patterns = tuple(product((0, 1), repeat=4))


def label(pattern):
    c = "TD"
    return c[pattern[0]] + "/" + c[pattern[1]] + "/" + c[pattern[2]] + c[pattern[3]]


def mean_and_unit(pattern, x, y):
    a, b, c, d = pattern
    mean = 1 + x["increments"][a] + y["increments"][b] + x["increments"][c] * y["increments"][d]
    unit = x["zero"][a] and y["zero"][b] and (x["zero"][c] or y["zero"][d])
    return mean, int(unit)


def fibre(k):
    g = 1 - F(k, 10) * (1 - r11)
    h = min(F(5, 3), 1 / g)
    return h, h * g


raw_atoms = []
for x, y in product(coordinate[5], coordinate[7]):
    k = min(10, x["old"][0] * y["old"][0] + x["old"][1] * y["old"][1])
    raw_atoms.append((x, y, k, x["mass"] * y["mass"]))
# On eta, both7 increments vanish.  The5 D chain occupies all of root3,
# whereas the5 T chain avoids eta.  This accounts for the actual deletion,
# including the whole D-chain count tail within its mixed root.
eta_y = {"increments": (F(0), F(0)), "zero": (True, True)}
eta_atoms = [
    ({"increments": (F(0), F(0)), "zero": (True, True)}, eta_y, 2,
     (DMASS[5] - F(1, 5)) * DMASS[7]),
    ({"increments": (F(0), F(5, 4)), "zero": (True, False)}, eta_y, 2,
     F(1, 5) * DMASS[7]),
]
require("raw_atom_count", len(raw_atoms) == 256)
require("eta_mass", sum(t[3] for t in eta_atoms) == F(4992, 60025))
require("actual_old_mass", sum(t[3] for t in raw_atoms) - sum(t[3] for t in eta_atoms) == F(53759, 214375))


def signed_integral(fn):
    return sum(fn(x, y, k) * mass for x, y, k, mass in raw_atoms) - sum(fn(x, y, k) * mass for x, y, k, mass in eta_atoms)


def direct_integrand(a, b, x, y, k):
    mean0, unit0 = mean_and_unit(a, x, y)
    mean1, _ = mean_and_unit(b, x, y)
    h, s = fibre(k)
    value = s * (mean0 - 2 + unit0)
    if k < 10:
        value += h * mean1 / 10 - h * unit0 / 11
    return value


# Independent separation: the A- and B-pattern dependence is additive.
# The exact hinge identity (M0-2)+=M0-2+1_{M0=1} handles every tail atom.
apart, bpart = {}, {}
for pattern in patterns:
    def component_a(x, y, k):
        mean0, unit0 = mean_and_unit(pattern, x, y)
        h, s = fibre(k)
        return s * (mean0 - 2 + unit0) - (h * unit0 / 11 if k < 10 else 0)

    def component_b(x, y, k):
        mean1, _ = mean_and_unit(pattern, x, y)
        h, _ = fibre(k)
        return h * mean1 / 10 if k < 10 else F(0)

    apart[pattern] = signed_integral(component_a)
    bpart[pattern] = signed_integral(component_b)

values = {}
for a, b in product(patterns, repeat=2):
    direct = signed_integral(lambda x, y, k: direct_integrand(a, b, x, y, k))
    if direct != apart[a] + bpart[b]:
        raise ValueError("direct and separated evaluation differ")
    values[(a, b)] = direct
require("all256_queries_computed", len(values) == 256)
best = max(values.values())
winners = [(a, b) for (a, b), value in values.items() if value == best]
require("separable_optimum", best == max(apart.values()) + max(bpart.values()))
require("all_query_integrals_nonnegative", min(values.values()) >= 0)

H548 = F(13869387400909870454063, 79759312825447505250000)
F13 = F(93139019, 475398000)
c0 = F(6168733163201163811, 542935350932041267200)
T = F(257, 51)
target = F13 - 4 * c0 / (T - 2)
factorized = ((0, 0, 0, 0), (0, 1, 0, 1), (1, 0, 1, 0), (1, 1, 1, 1))
factor_values = {label(a) + "|" + label(b): values[(a, b)] for a, b in product(factorized, repeat=2)}
factor_best = max(factor_values.values())


def finite_query_value(a, b, height5, height7, height11):
    def truncate(atom, p, height):
        v = dict(atom)
        if atom.get("name") == "D_root_complete_tail":
            v["increments"] = (F(0), F(p, p - 1) * (1 - F(1, p ** height)))
        elif atom.get("name") == "T_child_complete_tail":
            v["increments"] = (1 + F(p, p - 1) * (1 - F(1, p ** (height - 1))), F(0))
        return v

    positive11_mean = (1 - F(1, 11 ** height11)) / 10

    def f(x, y, k):
        mean0, unit0 = mean_and_unit(a, x, y)
        mean1, _ = mean_and_unit(b, x, y)
        h, s = fibre(k)
        ans = s * (mean0 - 2 + unit0)
        if k < 10:
            ans += h * positive11_mean * mean1 - h * unit0 / 11
        return ans

    raw = sum(f(truncate(x, 5, height5), truncate(y, 7, height7), k) * mass
              for x, y, k, mass in raw_atoms)
    eta = F(0)
    for x, y, k, mass in eta_atoms:
        xx = dict(x)
        if not x["zero"][1]:
            xx["increments"] = (F(0), F(5, 4) * (1 - F(1, 5 ** height5)))
        eta += f(xx, y, k) * mass
    return raw - eta


winner_a, winner_b = winners[0]
finite_grid = []
for height, height11 in product(range(1, 7), range(1, 5)):
    value = finite_query_value(winner_a, winner_b, height, height, height11)
    finite_grid.append({"height5": height, "height7": height, "height11": height11, "hinge": value,
                        "minus_report548": value - H548})
eligible = [t for t in finite_grid if t["hinge"] > H548]
finite_witness = min(eligible, key=lambda t: (t["height5"], t["height11"])) if eligible else None
require("finite_query_exceeds548", finite_witness is not None)
require("finite_grid_below_complete_query", all(t["hinge"] <= best for t in finite_grid))
height = finite_witness["height5"]
height11 = finite_witness["height11"]
finite_terms = []
for a, b, c in product(range(height + 1), range(height + 1), range(height11 + 1)):
    mods, residues = [], []
    if a:
        mods.append(5 ** a)
        residues.append((4 if a == 1 else 14) if b == 0 else 3)
    if b:
        mods.append(7 ** b)
        residues.append((5 if b == 1 else 19) if a > 0 and c > 0 else 6)
    if c:
        mods.append(11 ** c)
        residues.append(9)
    modulus = 5 ** a * 7 ** b * 11 ** c
    residue = sum(v * (modulus // m) * pow(modulus // m, -1, m)
                  for m, v in zip(mods, residues)) % modulus if modulus > 1 else 0
    if any(residue % m != v % m for m, v in zip(mods, residues)):
        raise ValueError("finite query CRT phase")
    finite_terms.append({"exponents": [a, b, c], "modulus": modulus, "residue": residue})
require("finite_query_distinct_numerical_labels", len({t["modulus"] for t in finite_terms}) == len(finite_terms) == (height + 1) ** 2 * (height11 + 1))
require("finite_query_has_unit_once", sum(t["modulus"] == 1 for t in finite_terms) == 1)


# Independent finite witness evaluation from literal prefix partitions.
# This neither uses tail moments nor scans a full CRT period.
def literal_prefix_partition(p, query_height):
    events = []

    def event(tag, residue, depth):
        digits = []
        for _ in range(depth):
            digits.append(residue % p)
            residue //= p
        events.append((tag, tuple(digits)))

    for depth in range(1, N + 1):
        for color in (1, 2):
            event("pure", color * p ** (depth - 1), depth)
        for color in ((3,) if p == 5 else (3, 4)):
            event("eta", color * p ** (depth - 1), depth)
    for depth in range(1, 8):
        event("oldA", p - 1 if p == 5 else 5, depth)
        event("oldB", (4 if depth == 1 else 9) if p == 5 else (5 if depth == 1 else 12), depth)
    for depth in range(1, query_height + 1):
        event("queryT", (4 if depth == 1 else 14) if p == 5 else (5 if depth == 1 else 19), depth)
        event("queryD", 3 if p == 5 else 6, depth)
    proper = {digits[:k] for _, digits in events for k in range(len(digits))}
    groups = {}
    leaf_count = 0

    def visit(prefix):
        nonlocal leaf_count
        if prefix in proper:
            for digit in range(p):
                visit(prefix + (digit,))
            return
        leaf_count += 1
        tags = [tag for tag, digits in events if prefix[:len(digits)] == digits]
        if "pure" in tags:
            return
        key = (1 + tags.count("oldA"), 1 + tags.count("oldB"),
               1 + tags.count("queryT"), 1 + tags.count("queryD"), "eta" in tags)
        groups[key] = groups.get(key, F(0)) + F(1, p ** len(prefix))

    visit(())
    require("literal_pure_mass_" + str(p), sum(groups.values()) == W[p])
    require("literal_eta_mass_" + str(p), sum(m for key, m in groups.items() if key[4]) == DMASS[p])
    return groups, leaf_count


literal5, leaves5 = literal_prefix_partition(5, height)
literal7, leaves7 = literal_prefix_partition(7, height)
literal_value = F(0)
positive11_mean = (1 - F(1, 11 ** height11)) / 10
for (state5, mass5), (state7, mass7) in product(literal5.items(), literal7.items()):
    if state5[4] and state7[4]:
        continue
    k = min(10, state5[0] * state7[0] + state5[1] * state7[1])
    x = {"increments": (state5[2] - 1, state5[3] - 1), "zero": (state5[2] == 1, state5[3] == 1)}
    y = {"increments": (state7[2] - 1, state7[3] - 1), "zero": (state7[2] == 1, state7[3] == 1)}
    M0, unit = mean_and_unit(winner_a, x, y)
    M1, _ = mean_and_unit(winner_b, x, y)
    h, s = fibre(k)
    value = s * max(M0 - 2, 0)
    if k < 10:
        value += h * positive11_mean * M1 - h * unit / 11
    literal_value += mass5 * mass7 * value
require("finite_literal_prefix_matches_moment_evaluation", literal_value == finite_witness["hinge"])

out = {"complete": True,
       "scope": "Exactly256 fixed complete support-dependent queries under the one192-original N=E=4 rainbow actual11 law. Each positive old11 exponent uses the fixed nested9 chain. This is not an arbitrary-support-dependent maximum and not an actual13 row-loss construction.",
       "coordinate_atoms": coordinate,
       "old_state_clip": "Each old branch count>=8 is represented by8 because K is already10; query-tail moments are not clipped.",
       "eta_mass": F(4992, 60025), "old_actual_mass": F(53759, 214375),
       "pattern_order": "single5 / single7 / joint57, T or D; first pattern for old11 exponent0, second for every positive old11 exponent",
       "A_components": [{"pattern": label(p), "value": apart[p]} for p in patterns],
       "B_components": [{"pattern": label(p), "value": bpart[p]} for p in patterns],
       "queries": [{"A": label(a), "B": label(b), "hinge": value} for (a, b), value in values.items()],
       "maximum": best, "winners": [{"A": label(a), "B": label(b)} for a, b in winners],
       "report548_envelope": H548, "maximum_minus_report548": best - H548,
       "row13_closure_target": target, "maximum_minus_target": best - target,
       "four_whole_patterns_16_pairs": factor_values, "whole_pattern_best": factor_best,
       "same_whole_TD_query": values[((0, 1, 0, 1), (0, 1, 0, 1))],
       "finite_height_grid": finite_grid,
       "finite_counterexample_to548_extension": finite_witness,
       "finite_query_phases": "T5=[4]mod5,[14]mod5^a for a>=2; T7=[5]mod7,[19]mod7^b for b>=2; D5=[3]mod5^a; D7=[6]mod7^b. A=T/D/DD; B=T/D/DT; positive11 phases=[9]mod11^c.",
       "finite_query_terms": finite_terms,
       "finite_literal_prefix_verification": {"p5_leaves": leaves5, "p7_leaves": leaves7,
           "p5_retained_groups": len(literal5), "p7_retained_groups": len(literal7),
           "hinge": literal_value},
       "checks": checks, "passed_count": len(checks), "direct_vs_separated_queries_checked": len(values),
       "Lean": "not run"}


def encode(v):
    if isinstance(v, F):
        return str(v)
    raise TypeError(type(v).__name__)


dest = Path(__file__).with_suffix(".json")
dest.write_text(json.dumps(out, indent=2, default=encode) + "\n", encoding="utf-8")
print(json.dumps({"passed_count": len(checks), "maximum": str(best), "maximum_decimal": float(best),
                  "winners": out["winners"], "vs548": str(best - H548), "vs548_decimal": float(best - H548),
                  "target": str(target), "vs_target": str(best - target), "vs_target_decimal": float(best - target),
                  "whole_TD_TD": str(out["same_whole_TD_query"]),
                  "finite_witness": {k: str(v) if isinstance(v, F) else v for k, v in finite_witness.items()},
                  "finite_terms": len(finite_terms),
                  "output": str(dest), "sha256": hashlib.sha256(dest.read_bytes()).hexdigest()}, indent=2))
