"""One row-mass certificate for every outside colour and multioutside phase.

The literal premises are eleven core phases, fifty-five singleton old phases,
and nonnegative integer row masses. The checker uses no optimization results
or final survivor tensor. The general source transport is proved in report758;
this program checks its exact finite hypotheses, not unrestricted Erdos #7.
"""
from fractions import Fraction
from hashlib import sha256
from math import prod
from pathlib import Path
import json


INPUT_SHA256 = "9330e227ea013314ded1074662600ec76e41af5a1cd42c9b75898d4725222912"


def need(condition, message):
    if not condition:
        raise ValueError(message)


def calculate():
    source = Path(__file__).with_name(
        "fibre_credit_depth_two_allcolors_row_envelope_input.json")
    raw = source.read_bytes()
    need(sha256(raw).hexdigest() == INPUT_SHA256, "pinned literal input")
    data = json.loads(raw)
    primes = data["minimal_outside_primes"]
    need(primes == [11, 13, 17, 19, 23], "five minimum ordered outside primes")
    divisors = [d for d in range(1, 316) if 315 % d == 0]
    core = data["core_originals"]
    need(sorted(d for d, _ in core) == divisors[1:], "eleven distinct core slots")
    need(all(type(d) is int and type(a) is int and 0 <= a < d
             for d, a in core), "literal core phases")
    rows = [x for x in range(315) if all(x % d != a for d, a in core)]
    pairs = data["row_mass_pairs"]
    need([x for x, _ in pairs] == rows, "complete actual core rows")
    need(all(type(x) is int and type(u) is int and u >= 0 for x, u in pairs),
         "nonnegative integer row masses")
    masses = dict(pairs)
    phases = data["old_singleton_phases"]
    need(sorted((j, d) for j, d, _ in phases) ==
         [(j, d) for j in range(5) for d in divisors[1:]],
         "fifty-five distinct old singleton slots")
    need(all(type(j) is int and type(d) is int and type(a) is int and 0 <= a < d
             for j, d, a in phases), "literal old singleton phases")
    lower = {
        x: [p - 1 - sum(x % d == a for axis, d, a in phases if axis == j)
            for j, p in enumerate(primes)] for x in rows}
    need(all(masses[x] == 0 or min(lower[x]) > 0 for x in rows),
         "positive mass only on guaranteed nonempty fibres")

    def evaluate(weights):
        need(sum(weights.values()) > 0, "positive total row mass")
        need(all(weights[x] == 0 or min(lower[x]) > 0 for x in rows),
             "all denominators on the positive support are positive")
        fractions = {}
        for x in rows:
            if weights[x] == 0:
                continue
            values = [Fraction(weights[x])] + [Fraction(0)] * 31
            for mask in range(1, 32):
                bit = mask & -mask
                axis = bit.bit_length() - 1
                values[mask] = values[mask ^ bit] / lower[x][axis]
            fractions[x] = values
        caps = []
        debit = Fraction(0)
        for d in divisors:
            kappa = prod(
                (Fraction(p, p - 1) for p, saturation in ((3, 9), (5, 5), (7, 7))
                 if d % saturation == 0), start=Fraction(1)) - 1
            for mask in range(32):
                coefficient = kappa + (mask.bit_count() >= 2)
                if coefficient == 0:
                    continue
                histogram = {}
                for x, values in fractions.items():
                    phase = x % d
                    histogram[phase] = histogram.get(phase, Fraction(0)) + values[mask]
                cap = max(histogram.values())
                debit += coefficient * cap
                caps.append([d, mask, str(coefficient), str(cap)])
        need(len(caps) == 372, "complete robust query inventory")
        mass = sum(weights.values())
        cell_cap = max(values[31] for values in fractions.values())
        margin = mass - debit
        haar = margin / (315 * prod(primes) * cell_cap)
        return caps, mass, debit, cell_cap, margin, haar

    caps, mass, debit, cell_cap, margin, haar = evaluate(masses)
    need(margin > 0 and haar > Fraction(1, 2320), "strict robust survivor bound")
    old_rows = sorted({x % 45 for x in rows})
    old_values = (6, 2, 6, 6, 5, 6, 6, 6, 6, 6, 6, 6, 6, 6, 2, 6)
    need(len(old_rows) == len(old_values), "explicit old45 comparison rule")
    old_rule = dict(zip(old_rows, old_values))
    _, rule_mass, rule_debit, _, _, _ = evaluate({x: old_rule[x % 45] for x in rows})
    rule_cost = rule_debit / rule_mass
    need(rule_cost > 1, "fixed old45 rule fails this sufficient envelope")
    return {
        "scope": "Fixed eleven core phases and fifty-five old singleton phases; "
                 "all singleton outside roots, all shallow multioutside phases, "
                 "all larger ordered outside primes, arbitrary finite higher core "
                 "powers; outside powers remain at most one",
        "input_sha256": INPUT_SHA256,
        "core_rows": rows,
        "minimum_fibre_lower_bounds": [min(lower[x][j] for x in rows) for j in range(5)],
        "row_mass_total": mass,
        "maximum_row_mass": max(masses.values()),
        "positive_rows": sum(u > 0 for u in masses.values()),
        "query_slots": len(caps),
        "envelope_debit": str(debit),
        "envelope_cost": str(debit / mass),
        "margin": str(margin),
        "point_mass_cap": str(cell_cap),
        "Haar_survivor_lower": str(haar),
        "strict_simple_Haar_lower": "1/2320",
        "fixed_old45_rule": {
            "rows": old_rows, "values": list(old_values), "envelope_cost": str(rule_cost),
            "meaning": "Failure of this fixed rule and upper envelope, not exclusion "
                       "of other row masses or of every actual supported source"},
        "query_caps": caps,
        "lean_verification": False}


if __name__ == "__main__":
    result = calculate()
    expected = json.loads(Path(__file__).with_suffix(".json").read_text())
    need(result == expected, "retained result agrees with exact recomputation")
    print(json.dumps(result, indent=2))
