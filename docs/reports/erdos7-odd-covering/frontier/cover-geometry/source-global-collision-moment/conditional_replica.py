#!/usr/bin/env python3
"""Exact finite conditional-replica checks, using only the standard library.

Columns are literal residues modulo m*p**b.  Both replicas use one old
X~nu on Z/M; their new words Y,Y' are independent uniform words.  The
enumeration, union inclusion-exclusion and labelled CRT pair calculation
are separate checks.  These finite data are neither Lean evidence nor an
odd whole cover.  The cofactor family checks local structural conditions,
not EB1, a prime-ordered BBMST stage, or a whole-cover completion.

Run with python -B -I -S -O conditional_replica.py --check.  Relative input
and output paths are resolved beside this file.  Optional --input JSON has
"fixtures": [{"name": ..., "p": 5, "old_weights": ["1/3", ...],
"columns": [["label", m, b, residue], ...]}] and optional
"counterexample_cofactors": [11, 13, 17].  Core routines accept arbitrary
finite rational old laws and coprime old cofactors, including depth zero.
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass
from fractions import Fraction as F
from itertools import combinations, product
import json
from math import gcd, isqrt
from pathlib import Path


def require(condition, detail):
    """Checks remain active under Python -O."""
    if not condition:
        raise AssertionError(detail)


def prime(n):
    return isinstance(n, int) and n >= 2 and all(n % d for d in range(2, isqrt(n) + 1))


def crt(constraints):
    """Return (residue, modulus), or None for incompatible congruences."""
    a, modulus = 0, 1
    for b, n in constraints:
        require(n >= 1, ("nonpositive modulus", n))
        divisor = gcd(modulus, n)
        if (b - a) % divisor:
            return None
        q = n // divisor
        step = 0 if q == 1 else ((b - a) // divisor) * pow(modulus // divisor, -1, q) % q
        a += modulus * step
        modulus *= q
        a %= modulus
    return a, modulus


@dataclass(frozen=True)
class Column:
    label: str
    cofactor: int
    depth: int
    residue: int

    def old_hit(self, x):
        return x % self.cofactor == self.residue % self.cofactor

    def new_hit(self, y, p):
        return y % (p**self.depth) == self.residue % (p**self.depth)

    def data(self):
        return [self.label, self.cofactor, self.depth, self.residue]


def old_mass(columns, weights):
    solution = crt((c.residue, c.cofactor) for c in columns)
    if solution is None:
        return F(0)
    a, modulus = solution
    return sum((weights[x] for x in range(a, len(weights), modulus)), F(0))


def new_mass(columns, p):
    solution = crt((c.residue, p**c.depth) for c in columns)
    return F(0) if solution is None else F(1, solution[1])


def moments(p, columns, weights):
    """Exhaust all finite replicas and compare exact union and load formulas."""
    weights = tuple(F(w) for w in weights)
    require(prime(p), ("p must be prime", p))
    require(weights and min(weights) >= 0 and sum(weights) == 1, "invalid old law")
    require(len({c.label for c in columns}) == len(columns), "duplicate label name")
    for c in columns:
        require(all(isinstance(n, int) for n in (c.cofactor, c.depth, c.residue))
                and c.cofactor >= 1 and c.depth >= 0 and gcd(c.cofactor, p) == 1,
                ("invalid column", c))
        require(len(weights) % c.cofactor == 0, ("old period does not contain cofactor", c))
    width = p**max((c.depth for c in columns), default=0)
    mean = second = load_second = F(0)
    alpha = []
    for x, weight in enumerate(weights):
        loads = [sum(c.old_hit(x) and c.new_hit(y, p) for c in columns)
                 for y in range(width)]
        union = [int(n > 0) for n in loads]
        ax = F(sum(union), width)
        alpha.append(ax)
        # Explicit Y,Y' enumeration, with the same literal x in each factor.
        union_hits = sum(union[y] * union[z] for y, z in product(range(width), repeat=2))
        load_hits = sum(loads[y] * loads[z] for y, z in product(range(width), repeat=2))
        require(F(union_hits, width**2) == ax**2, ("replica square", x))
        mean += weight * ax
        second += weight * F(union_hits, width**2)
        load_second += weight * F(load_hits, width**2)

    pair_terms = []
    pair_bound = F(0)
    for left, right in product(columns, repeat=2):
        mass = old_mass((left, right), weights)
        direct_mass = sum((w for x, w in enumerate(weights)
                           if left.old_hit(x) and right.old_hit(x)), F(0))
        require(mass == direct_mass, ("old CRT", left, right))
        term = mass / p**(left.depth + right.depth)
        pair_terms.append({"labels": [left.label, right.label],
                           "old_joint_mass": str(mass), "term": str(term)})
        pair_bound += term

    subsets = []
    for size in range(1, len(columns) + 1):
        for group in combinations(columns, size):
            subsets.append((group, (-1)**(size + 1), new_mass(group, p)))
    ie_mean = sum((sign * old_mass(group, weights) * mass
                   for group, sign, mass in subsets), F(0))
    ie_second = sum((s * t * old_mass(a + b, weights) * ha * hb
                     for (a, s, ha), (b, t, hb) in product(subsets, repeat=2)), F(0))
    require((mean, second) == (ie_mean, ie_second), "union CRT inclusion-exclusion mismatch")
    require(load_second == pair_bound, "labelled CRT pair formula mismatch")
    require(mean**2 <= second <= pair_bound, "conditional moment bounds fail")
    return {"p": p, "old_period": len(weights), "new_word_count": width,
            "columns": [c.data() for c in columns], "old_weights": list(map(str, weights)),
            "alpha": list(map(str, alpha)), "mean": str(mean),
            "mean_squared": str(mean**2), "conditional_second_moment": str(second),
            "labelled_pair_bound": str(pair_bound), "union_slack": str(pair_bound - second),
            "replica_states": len(weights) * width**2, "ordered_label_pairs": len(pair_terms),
            "inclusion_exclusion_pairs": len(subsets)**2, "pair_terms": pair_terms}


def uniform(period):
    return (F(1, period),) * period


def fixtures():
    return [
        ("shared_old_phase", 5, [Column("a", 3, 1, 0), Column("b", 3, 1, 6)], uniform(3)),
        ("incompatible_old_phases", 5, [Column("a", 3, 1, 0), Column("b", 3, 1, 1)], uniform(3)),
        ("duplicate_output_labels", 5, [Column("a", 3, 1, 0), Column("b", 3, 1, 0)], uniform(3)),
        ("nonuniform_nested_and_disjoint", 5,
         [Column("a", 3, 1, 0), Column("b", 3, 2, 0),
          Column("c", 9, 1, 6), Column("d", 9, 2, 31)], tuple(F(i, 45) for i in range(1, 10))),
        ("different_coprime_cofactors", 5,
         [Column("a", 3, 1, 0), Column("b", 7, 2, 1), Column("c", 1, 1, 2)], uniform(21)),
        ("depth_zero_and_zero_old_mass", 3,
         [Column("a", 2, 0, 1), Column("b", 4, 1, 4)], (F(0), F(1, 2), F(1, 3), F(1, 6))),
        ("empty_columns", 5, [], uniform(3)),
    ]


def factor_out(n, p):
    exponent = 0
    while n % p == 0:
        exponent += 1
        n //= p
    return n, exponent


def pullback(originals, r, s, u, children):
    """One common depth-one injection; all labels use the same u and children."""
    require(prime(r) and prime(s) and r < s, "invalid embedding primes")
    require(len(children) == r and len(set(children)) == r
            and all(0 <= a < s for a in children), "invalid common injection")
    output = []
    for label, modulus, phase in originals:
        require(isinstance(modulus, int) and modulus >= 1 and isinstance(phase, int),
                ("invalid original congruence", label, modulus, phase))
        rest, a = factor_out(modulus, r)
        m, b = factor_out(rest, s)
        require(a <= 1 and b <= 1, "source checker supports depths at most one")
        if (a and u % r != phase % r) or (b and phase % s not in children):
            continue
        constraints = [(phase, m)]
        if b:
            constraints.append((children.index(phase % s), r))
        output.append(Column(label, m, b, crt(constraints)[0]))
    return output


def verify_pullback(originals, r, s, u, children, old_period):
    output = pullback(originals, r, s, u, children)
    by_label = {c.label: c for c in output}
    checks = 0
    for t in range(old_period * r):
        source = crt(((t, old_period), (u, r), (children[t % r], s)))[0]
        for label, modulus, phase in originals:
            actual = source % modulus == phase % modulus
            c = by_label.get(label)
            projected = c is not None and t % (c.cofactor * r**c.depth) == c.residue
            require(actual == projected, ("literal source pullback", label, u, children, t))
            checks += 1
    return output, checks


def structure(originals):
    moduli = [n for _, n, _ in originals]
    require(len(set(moduli)) == len(moduli), "repeated original modulus")
    require(all(n > 1 and n % 2 for n in moduli), "original modulus not odd nonunit")
    require(all(d in moduli for n in moduli for d in range(2, n + 1) if n % d == 0),
            "original labels not divisor closed")
    count = 0
    for (_, n, a), (_, q, b) in combinations(originals, 2):
        if n % q == 0 or q % n == 0:
            require((a - b) % gcd(n, q) != 0, ("comparable classes meet", n, q))
            count += 1
    return count


def source_case(name, originals, pair, old_period, check_structure=False):
    """Exhaust the 4*21 maps and all literal source/replica residues.

    The safe law is uniform on {1,2,3,4}, avoiding 0 mod 5.  The two-label
    controls stipulate this law; the cofactor family includes that 5-class.
    """
    r, s = 5, 7
    comparable = structure(originals) if check_structure else None
    shared = independent = F(0)
    live = checks = replicas = pair_checks = designated_states = independent_states = 0
    rows = []
    for u, children in product(range(1, r), combinations(range(s), r)):
        output, current = verify_pullback(originals, r, s, u, children, old_period)
        checks += current
        stage = [c for c in output if c.depth == 1]
        result = moments(r, stage, uniform(old_period))
        replicas += result["replica_states"]
        pair_checks += result["ordered_label_pairs"]
        by_label = {c.label: c for c in stage}
        joint = independent_joint = F(0)
        if all(label in by_label for label in pair):
            left, right = [by_label[label] for label in pair]
            require(left.cofactor == right.cofactor, "designated output moduli differ")
            require(left.residue != right.residue, "designated projected phases coincide")
            mass = old_mass((left, right), uniform(old_period))
            joint = 2 * mass / r**2
            independent_joint = 2 * old_mass((left,), uniform(old_period)) * old_mass((right,), uniform(old_period)) / r**2
            # Count designated shared-old ordered replica hits separately.
            hits = sum(left.old_hit(x) and right.old_hit(x)
                       and left.new_hit(y, r) and right.new_hit(z, r)
                       for x, y, z in product(range(old_period), range(r), range(r)))
            require(joint == F(2 * hits, old_period * r**2), "designated replica count")
            designated_states += old_period * r**2
            # Independent full endpoints use different old coordinates as well.
            endpoints = list(product(range(old_period), range(r)))
            independent_hits = sum(left.old_hit(x) and left.new_hit(y, r)
                                   and right.old_hit(z) and right.new_hit(w, r)
                                   for (x, y), (z, w) in product(endpoints, repeat=2))
            require(independent_joint == F(2 * independent_hits, len(endpoints)**2),
                    "independent full endpoint count")
            independent_states += len(endpoints)**2
            live += 1
        shared += joint
        independent += independent_joint
        rows.append({"u": u, "children": list(children),
                     "stage_columns": [c.data() for c in stage],
                     "mean_squared": result["mean_squared"],
                     "conditional_second_moment": result["conditional_second_moment"],
                     "labelled_pair_bound": result["labelled_pair_bound"],
                     "designated_ordered_shared_old": str(joint)})
    require(len(rows) == 84 and live == 10, ("common-map survival", len(rows), live))
    return {"name": name, "originals": [list(t) for t in originals],
            "old_period": old_period, "common_subsets": 21, "safe_coordinates": [1, 2, 3, 4],
            "source_maps": len(rows), "literal_pullback_checks": checks,
            "replica_states": replicas, "ordered_label_pairs": pair_checks,
            "designated_replica_states": designated_states,
            "independent_full_endpoint_states": independent_states,
            "comparable_disjoint_pairs": comparable, "divisor_closed": check_structure,
            "designated_pair": list(pair), "pair_live_maps": live,
            "survival_probability": str(F(live, len(rows))),
            "expected_ordered_shared_old": str(shared / len(rows)),
            "expected_ordered_independent_full_endpoints": str(independent / len(rows)),
            "maps": rows}


def counterexample(m):
    require(prime(m) and m > 7, ("cofactor must be prime above seven", m))
    phase = lambda constraints: crt(constraints)[0]
    return [("3", 3, 0), ("5", 5, 0), ("7", 7, 0), ("m", m, 0),
            ("35", 35, phase(((2, 5), (3, 7)))),
            ("5m", 5*m, phase(((1, 5), (2, m)))),
            ("7m", 7*m, phase(((1, 7), (1, m)))),
            ("35m", 35*m, phase(((1, 5), (2, 7), (1, m))))]


def run(extra_fixtures=(), cofactors=(11, 13, 17)):
    cases = []
    for name, p, columns, law in [*fixtures(), *extra_fixtures]:
        cases.append({"name": name, **moments(p, columns, law)})
    require(cases[0]["conditional_second_moment"] == "4/75", "shared-phase control")
    require(cases[1]["conditional_second_moment"] == "2/75", "incompatible-phase control")
    require(cases[0]["mean_squared"] == cases[1]["mean_squared"] == "4/225", "mean controls")
    require(cases[2]["union_slack"] == "1/25", "duplicate-label union control")
    control_sources = [
        ("shared_old_phase", [("a", 21, 0), ("b", 105, 6)], (0, 6, 1, 2, 3), [0, 6]),
        ("incompatible_old_phases", [("a", 21, 0), ("b", 105, 16)], (0, 2, 1, 3, 4), [0, 1]),
    ]
    literal_controls, sources = [], []
    for name, originals, children, expected in control_sources:
        columns, count = verify_pullback(originals, 5, 7, 1, children, 3)
        require([c.residue for c in columns] == expected, "literal control residues")
        literal_controls.append({"name": name, "u": 1, "children": list(children),
                                 "originals": [list(t) for t in originals],
                                 "output_columns": [c.data() for c in columns],
                                 "literal_pullback_checks": count})
        sources.append(source_case(name, originals, ("a", "b"), 3))
    require(sources[0]["expected_ordered_shared_old"] == "1/315", "shared source control")
    require(sources[1]["expected_ordered_shared_old"] == "0", "incompatible source control")
    counter_cases = []
    for m in cofactors:
        originals = counterexample(m)
        if m == 11:
            require([a for _, _, a in originals] == [0, 0, 0, 0, 17, 46, 1, 331], "literal m=11 phases")
        case = source_case(f"cofactor_{m}", originals, ("7m", "35m"), 3*m, True)
        shared = F(case["expected_ordered_shared_old"])
        independent = F(case["expected_ordered_independent_full_endpoints"])
        require(F(case["survival_probability"]) == F(5, 42), "cofactor survival formula")
        require(shared == F(1, 105*m) and independent == F(1, 105*m*m), "cofactor coefficients")
        require(shared / independent == m, "cofactor ratio")
        counter_cases.append({"cofactor": m, "coefficient_ratio": str(shared / independent), **case})
    coefficient = F(2*5, (5-2)*(7-1)*(5*7-1))
    upper = coefficient * F(3, 2)
    require(upper == F(5, 204), "three-power geometric coefficient")
    finite = F(sources[0]["expected_ordered_shared_old"])
    require(finite < coefficient / 3 < upper, "finite admissible-cofactor comparison")
    all_sources = sources + counter_cases
    return {"schema_version": 1, "status": "PASS",
            "scope": "exact finite conditional replicas and literal common-source maps; no Lean or whole-cover claim",
            "generic_fixtures": cases, "literal_controls": literal_controls,
            "source_controls": sources, "cofactor_counterexamples": counter_cases,
            "coefficient_comparison": {
                "candidate_formula": "2*r/((r-2)*(s-1)*(r*s-1)) * sum_m(1/m)",
                "r": 5, "s": 7, "coefficient": str(coefficient),
                "three_power_reciprocal_sum": "3/2", "three_power_upper": str(upper),
                "finite_shared_phase_contribution": str(finite),
                "finite_single_cofactor_bound": str(coefficient / 3),
                "scope": "finite comparison only; no global bound established by enumeration"},
            "cofactor_family_formulas": {
                "survival_probability": "5/42", "ordered_shared_old": "1/(105*m)",
                "ordered_independent_full_endpoints": "1/(105*m^2)", "ratio": "m",
                "scope": "formulas checked for listed prime cofactors; no EB1 or whole cover asserted"},
            "counts": {"generic_fixtures": len(cases), "source_fixtures": len(all_sources),
                       "common_source_maps": sum(c["source_maps"] for c in all_sources),
                       "literal_pullback_checks": sum(c["literal_pullback_checks"] for c in all_sources + literal_controls),
                       "replica_states": sum(c["replica_states"] for c in cases + all_sources),
                       "designated_replica_states": sum(c["designated_replica_states"] for c in all_sources),
                       "independent_full_endpoint_states": sum(c["independent_full_endpoint_states"] for c in all_sources),
                       "ordered_label_pairs": sum(c["ordered_label_pairs"] for c in cases + all_sources)}}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--input", type=Path, help="optional additional fixture JSON")
    parser.add_argument("--output", type=Path, default=Path(__file__).resolve().with_suffix(".json"))
    parser.add_argument("--check", action="store_true", help="compare stored JSON without writing")
    args = parser.parse_args()
    beside = lambda path: path if path.is_absolute() else Path(__file__).parent / path
    inputs = {} if args.input is None else json.loads(beside(args.input).read_text(encoding="utf-8"))
    extra = [(c["name"], c["p"], [Column(*t) for t in c["columns"]], c["old_weights"])
             for c in inputs.get("fixtures", [])]
    result = run(extra, inputs.get("counterexample_cofactors", [11, 13, 17]))
    rendered = json.dumps(result, indent=2, sort_keys=True) + "\n"
    output = beside(args.output)
    if args.check:
        require(json.loads(output.read_text(encoding="utf-8")) == result, "stored result mismatch")
    else:
        output.write_text(rendered, encoding="utf-8")
    print(json.dumps({"status": result["status"], "counts": result["counts"],
                      "mode": "check" if args.check else "write"}, sort_keys=True))


if __name__ == "__main__":
    main()
