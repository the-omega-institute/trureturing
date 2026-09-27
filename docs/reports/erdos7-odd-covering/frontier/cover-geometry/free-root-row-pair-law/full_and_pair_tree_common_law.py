#!/usr/bin/env python3
"""Construct and verify one law from six pair-3 trees and one full-5 tree.

make_common_law(height, source) returns exact Fraction probabilities and
actual tree witnesses. verify_common_law checks the complete certificate.
The preliminary shell bound tends to 1698/245. Retaining mixed-row phase
incompatibility improves the bound for the same law to a limit of 168/25.
Neither bound proves 2*t_K or optimizes the actual-layout expectation.

With f_j=5**(-j), q_j=3**(-j), the resulting law has plain-prefix cap
(2/5)*f_j+(3/5)*q_j and row-prefix cap (2/5)*(f_j+(1-f_j)*q_j).
Every ordered original-label pair intersects in either an empty set,
a plain prefix or a row-prefix at its literal LCM. Thus all arbitrary
phases obey (8/5)*S_K(1/5)+(9/5)*S_K(1/3)-(6/5)*S_K(1/15), where
S_K(z)=sum((2*j+1)*z**j for j in 0..K). These are ordinary proof
obligations checked on exact finite inputs, not Lean-certified claims.
The stronger row-phase bound is (8/5)*S_K(1/5)+(39/25)*S_K(1/3)-24/25.

No arguments runs exact controls. --stdin accepts one JSON object:
{"height": 1, "source": [[1,0], ...]}. It emits the full exact certificate
and verification as JSON on stdout, with rational values as strings.
Only the standard library and sibling repository research modules are used.
"""
from collections import defaultdict
from fractions import Fraction as F
from itertools import combinations, product
from pathlib import Path
import importlib.util
import json
import sys

ROWS = (1, 2, 3, 4)
PAIRS = tuple(combinations(ROWS, 2))
LIMIT = F(1698, 245)
ROW_PHASE_LIMIT = F(168, 25)


def require(condition, message):
    if not condition:
        raise ValueError(message)


def _sibling(filename, name):
    spec = importlib.util.spec_from_file_location(name, Path(__file__).with_name(filename))
    if spec is None or spec.loader is None:
        raise ImportError("cannot load sibling " + filename)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


_trees = _sibling("prime_layout_mixture_certificate.py", "_common_law_tree_certificate")


def _height(height):
    require(type(height) is int and height >= 0, "height must be a nonnegative integer")


def validate_source(height, source):
    """Validate literal points; no coercion of bools, floats or residues."""
    _height(height)
    require(type(source) in (set, frozenset, list, tuple), "source must be a finite point collection")
    require(bool(source), "source must be nonempty")
    normalized = []
    for point in source:
        require(type(point) in (tuple, list) and len(point) == 2, "point must be a row-residue pair")
        row, residue = point
        require(type(row) is int and row in ROWS and type(residue) is int
                and 0 <= residue < 7 ** height, "point outside the literal four-row carrier")
        normalized.append((row, residue))
    require(len(set(normalized)) == len(normalized), "duplicate source points")
    return frozenset(normalized)


def finite_bound(height):
    """Exact all-original-label shell bound; ordinary theorem, not Lean certification."""
    _height(height)
    def series(z):
        return sum((F(2 * j + 1) * z ** j for j in range(height + 1)), F(0))
    return F(8, 5) * series(F(1, 5)) + F(9, 5) * series(F(1, 3)) - F(6, 5) * series(F(1, 15))


def aligned_bound(height):
    """All-word row-phase bound, proved by first-change charging in the report.

    It is the exact maximum of the retained cap functional over beta and
    row words. It is not an asserted optimum of an actual layout problem.
    """
    _height(height)
    return ROW_PHASE_LIMIT - F(4 * height + 7, 5 ** (height + 1)) - F(39 * (height + 2), 25 * 3 ** height)


def _row_cap(depth, beta):
    f, q = F(1, 5 ** depth), F(1, 3 ** depth)
    return F(2, 5) * (min(beta, f) + (1 - beta) * q)


def row_phase_profile_bound(beta, rows):
    """Exact cap expression for a specified actual-row word, retaining QQ zeros.

    beta is a probability dictionary on rows 1..4; rows[j] is the mixed
    phase's row at depth j. An absent row-zero phase vanishes and can be
    dominated by any actual-row label, as explained in the analytic proof.
    """
    require(type(beta) is dict and set(beta) == set(ROWS)
            and all(type(r) is int and type(x) in (int, F) and x >= 0 for r, x in beta.items())
            and sum(beta.values(), F(0)) == 1, "beta must be an exact probability on four rows")
    require(type(rows) in (tuple, list) and rows
            and all(type(r) is int and r in ROWS for r in rows), "nonempty literal actual-row word required")
    result = F(0)
    for j, row in enumerate(rows):
        previous = rows[:j]
        matches = sum(r == row for r in previous)
        m = F(2, 5 ** (j + 1)) + F(3, 5 * 3 ** j)
        result += (2 * j + 1) * m + (2 * j + 3 + 2 * matches) * _row_cap(j, beta[row])
        result += 2 * sum((_row_cap(j, beta[r]) for r in previous), F(0))
    return result


def first_change_limit(depth):
    """Infinite first-change excess, strictly negative at every integer depth >=1."""
    _height(depth)
    require(depth >= 1, "a first change needs positive depth")
    return (F(8 - 2 * depth, 25 * 3 ** depth) - F(4 * depth + 1, 5 ** (depth + 1))
            - F(434 * depth + 346, 245 * 15 ** depth))


def _mixture(components):
    result = defaultdict(F)
    for weight, law in components:
        for point, mass in law.items():
            result[point] += weight * mass
    return {point: mass for point, mass in sorted(result.items()) if mass}


def _uniform_witness(witness, branching, height):
    return {point: F(1, branching ** height) for point in witness["points"]}


def make_common_law(height, source):
    """Select actual witnesses and return their beta-dependent common law.

    The sibling tree API maximizes 0/1 source membership. Value one
    certifies that every selected row-labelled leaf belongs to the source.
    Equal-cost choices use that API's deterministic tie-breaking.
    """
    source = validate_source(height, source)
    membership = {(r, y): F((r, y) in source) for r, y in product(ROWS, range(7 ** height))}
    full = _trees.row_tree_witness(membership, height, ROWS, 5)
    require(full["value"] == 1, "source lacks a complete full-projection five-ary tree")
    pair_witnesses = {}
    for pair in PAIRS:
        witness = _trees.row_tree_witness(membership, height, pair, 3)
        require(witness["value"] == 1, "source lacks a complete pair-ternary tree for " + str(pair))
        pair_witnesses[pair] = witness
    mu = _uniform_witness(full, 5, height)
    beta = {r: sum((mass for (s, _), mass in mu.items() if s == r), F(0)) for r in ROWS}
    pair_laws = {pair: _uniform_witness(witness, 3, height) for pair, witness in pair_witnesses.items()}
    pair_weights = {pair: (1 - beta[pair[0]] - beta[pair[1]]) / 3 for pair in PAIRS}
    omega = _mixture((pair_weights[pair], pair_laws[pair]) for pair in PAIRS)
    nu = _mixture(((F(2, 5), mu), (F(3, 5), omega)))
    return {"height": height, "full_witness": full, "pair_witnesses": pair_witnesses,
            "mu": mu, "beta": beta, "pair_laws": pair_laws, "pair_weights": pair_weights,
            "omega": omega, "nu": nu}


def _probability(law, source, name):
    require(type(law) is dict and law, name + " must be a nonempty probability dictionary")
    for point, mass in law.items():
        require(type(point) is tuple and len(point) == 2
                and all(type(x) is int for x in point) and point in source,
                name + " has a nonliteral or unsupported point")
        require(type(mass) in (int, F) and mass > 0, name + " needs positive exact masses")
    require(sum(law.values(), F(0)) == 1, name + " mass must sum to one")


def _witness(height, source, witness, rows, branching):
    require(type(witness) is dict, "tree witness must be a dictionary")
    require(type(witness.get("branching")) is int and witness["branching"] == branching,
            "incorrect witness branching")
    require(type(witness.get("rows")) in (tuple, list)
            and all(type(r) is int for r in witness["rows"]) and tuple(witness["rows"]) == rows,
            "incorrect witness rows")
    require(type(witness.get("value")) in (int, F) and witness["value"] == 1,
            "witness does not certify source membership")
    points = validate_source(height, witness.get("points"))
    require(points <= source and all(r in rows for r, _ in points), "tree witness leaves source or allowed rows")
    leaves = witness.get("leaves")
    require(type(leaves) in (tuple, list) and all(type(y) is int for y in leaves), "literal tree leaves required")
    require(len(points) == branching ** height and len(leaves) == len(set(leaves)) == len(points)
            and set(leaves) == {y for _, y in points}, "tree witness cardinality or row assignment mismatch")
    require(_trees.contains_bary_tree(leaves, height, branching), "witness leaves do not form the required tree")
    return {point: F(1, branching ** height) for point in points}


def _prefixes(law, depth):
    plain, joint = defaultdict(F), defaultdict(F)
    modulus = 7 ** depth
    for (row, y), mass in law.items():
        plain[y % modulus] += mass
        joint[row, y % modulus] += mass
    return plain, joint


def verify_common_law(height, source, certificate):
    """Independently check witnesses, exact mixture identities, and every prefix cap."""
    source = validate_source(height, source)
    require(type(certificate) is dict and type(certificate.get("height")) is int
            and certificate["height"] == height, "certificate height mismatch")
    require(set(certificate) == {"height", "full_witness", "pair_witnesses", "mu", "beta",
                                 "pair_laws", "pair_weights", "omega", "nu"}, "certificate schema mismatch")
    mu, omega, nu = (certificate[name] for name in ("mu", "omega", "nu"))
    for name in ("mu", "omega", "nu"):
        _probability(certificate[name], source, name)
    require(mu == _witness(height, source, certificate["full_witness"], ROWS, 5), "mu is not its uniform witness law")
    beta, pair_laws, pair_weights = (certificate[name] for name in ("beta", "pair_laws", "pair_weights"))
    require(type(beta) is dict and set(beta) == set(ROWS)
            and all(type(r) is int and type(v) in (int, F) and v >= 0 for r, v in beta.items()),
            "exact beta row masses required")
    require(beta == {r: sum((mass for (s, _), mass in mu.items() if s == r), F(0)) for r in ROWS},
            "beta is not the actual row marginal of mu")
    for name in ("pair_laws", "pair_weights", "pair_witnesses"):
        data = certificate[name]
        require(type(data) is dict and set(data) == set(PAIRS)
                and all(type(pair) is tuple and all(type(r) is int for r in pair) for pair in data),
                name + " must contain exactly the six literal pairs")
    for pair in PAIRS:
        _probability(pair_laws[pair], source, "pair law " + str(pair))
        expected = _witness(height, source, certificate["pair_witnesses"][pair], pair, 3)
        require(pair_laws[pair] == expected, "pair law does not match its uniform actual witness")
        weight = pair_weights[pair]
        require(type(weight) in (int, F) and weight >= 0
                and weight == (F(1) - beta[pair[0]] - beta[pair[1]]) / 3, "incorrect omitted-row pair weight")
    require(sum(pair_weights.values(), F(0)) == 1, "pair weights must form one probability")
    expected_omega = _mixture((pair_weights[pair], pair_laws[pair]) for pair in PAIRS)
    require(omega == expected_omega, "omega is not the common omitted-row mixture")
    require(nu == _mixture(((F(2, 5), mu), (F(3, 5), omega))), "nu is not the claimed common law")

    prefix_checks = []
    actual_envelope, envelope = F(0), F(0)
    for depth in range(height + 1):
        f, q = F(1, 5 ** depth), F(1, 3 ** depth)
        mu_plain, mu_joint = _prefixes(mu, depth)
        omega_plain, omega_joint = _prefixes(omega, depth)
        nu_plain, nu_joint = _prefixes(nu, depth)
        require(max(mu_plain.values()) <= f
                and all(mass <= min(beta[r], f) for (r, _), mass in mu_joint.items()), "mu prefix caps")
        for pair in PAIRS:
            pair_plain, pair_joint = _prefixes(pair_laws[pair], depth)
            require(max(pair_plain.values()) <= q
                    and all(r in pair and mass <= q for (r, _), mass in pair_joint.items()), "pair prefix caps")
        require(max(omega_plain.values()) <= q
                and all(mass <= F(2, 3) * (1 - beta[r]) * q for (r, _), mass in omega_joint.items()),
                "omitted-row mixture prefix caps")
        plain_bound = F(2, 5) * f + F(3, 5) * q
        joint_bound = F(2, 5) * (f + (1 - f) * q)
        row_bounds = {r: F(2, 5) * (min(beta[r], f) + (1 - beta[r]) * q) for r in ROWS}
        plain_max, joint_max = max(nu_plain.values()), max(nu_joint.values())
        require(plain_max <= plain_bound and joint_max <= joint_bound
                and all(mass <= row_bounds[r] <= joint_bound for (r, _), mass in nu_joint.items()),
                "single-law plain and joint prefix bounds")
        require(plain_bound + 3 * joint_bound == F(8, 5) * f + F(9, 5) * q - F(6, 5) * f * q,
                "original-label shell coefficient identity")
        actual_envelope += (2 * depth + 1) * (plain_max + 3 * joint_max)
        envelope += (2 * depth + 1) * (plain_bound + 3 * joint_bound)
        prefix_checks.append({"depth": depth, "f": f, "q": q, "plain_max": plain_max,
                              "joint_max": joint_max, "plain_bound": plain_bound,
                              "joint_bound": joint_bound, "row_bounds": row_bounds})
    require(actual_envelope <= envelope == finite_bound(height) < LIMIT, "finite shell bound and uniform limit")
    sharper_bound = aligned_bound(height)
    require(sharper_bound <= envelope and sharper_bound < ROW_PHASE_LIMIT, "row-phase bound and limit")
    return {"height": height, "source_points": len(source), "law_support_points": len(nu),
            "row_masses": {r: sum((mass for (s, _), mass in nu.items() if s == r), F(0)) for r in ROWS},
            "prefix_checks": prefix_checks, "actual_prefix_shell_bound": actual_envelope,
            "shell_bound": envelope, "limit_bound": LIMIT,
            "row_phase_bound": sharper_bound, "row_phase_limit": ROW_PHASE_LIMIT,
            "best_certified_bound": min(actual_envelope, sharper_bound),
            "scope": "one common-law upper bound; neither the 2*t_K target nor actual-layout optimality is claimed"}


def row_phase_controls():
    """Direct label-pair/profile identities and first-change algebra controls.

    No exhaustive row-word search is used as an all-height certificate.
    """
    examples = (
        ({1: F(1, 5), 2: F(4, 5), 3: F(0), 4: F(0)}, (1,)),
        ({1: F(1, 5), 2: F(4, 5), 3: F(0), 4: F(0)}, (1, 1, 1, 1)),
        ({1: F(1, 2), 2: F(1, 2), 3: F(0), 4: F(0)}, (1, 2)),
        ({1: F(1, 5), 2: F(2, 5), 3: F(1, 5), 4: F(1, 5)}, (1, 1, 2, 3, 4, 2)),
        ({1: F(0), 2: F(0), 3: F(0), 4: F(1)}, (1, 1, 1, 1, 1, 1, 2)),
    )
    profiles = []
    for beta, rows in examples:
        labels = [(False, j, None) for j in range(len(rows))] + [(True, j, r) for j, r in enumerate(rows)]
        direct = F(0)
        for mixed_a, a, r in labels:
            for mixed_b, b, s in labels:
                j = max(a, b)
                if not mixed_a and not mixed_b:
                    direct += F(2, 5 ** (j + 1)) + F(3, 5 * 3 ** j)
                elif mixed_a and mixed_b:
                    if r == s:
                        direct += _row_cap(j, beta[r])
                else:
                    direct += _row_cap(j, beta[r if mixed_a else s])
        profile = row_phase_profile_bound(beta, rows)
        require(profile == direct and profile <= aligned_bound(len(rows) - 1), "ordered-label row-profile identity")
        if len(set(rows)) > 1:
            require(profile < aligned_bound(len(rows) - 1), "changed word is strictly below aligned maximum")
        profiles.append({"rows": rows, "bound": profile, "aligned_bound": aligned_bound(len(rows) - 1)})
    for height in range(9):
        beta = {1: F(1, 5), 2: F(4, 5), 3: F(0), 4: F(0)}
        require(row_phase_profile_bound(beta, (1,) * (height + 1)) == aligned_bound(height), "aligned exact maximum formula")
        series_form = sum((F(2 * j + 1) * (F(8, 5 ** (j + 1)) + F(39, 25 * 3 ** j))
                           for j in range(height + 1)), F(0)) - F(24, 25)
        require(series_form == aligned_bound(height), "row-phase closed series formula")
    require([first_change_limit(h) for h in (1, 2, 3)]
            == [F(-407, 1225), F(-467, 6125), F(-16397, 826875)], "initial first-change excesses")
    for h in range(1, 13):
        f, q, s = F(1, 5 ** h), F(1, 3 ** h), F(1, 15 ** h)
        u = F(2, 5) * (f + q - s)
        weighted_gain = F(18, 25) * (h + 1) * q - F(6, 5) * F(105 * h + 60, 49) * s
        later_penalty = f / 5 + 2 * q / 5 - 2 * s / 35
        require(weighted_gain - 2 * h * u - later_penalty == first_change_limit(h) < 0,
                "summed first-change geometric-series identity")
    def tail(j):
        f, q = F(1, 5 ** j), F(1, 3 ** j)
        u = F(2, 5) * (f + (1 - f) * q)
        v = F(2, 5) * (f + F(4, 5) * q)
        return (6 * j + 3) * (u - v) - 2 * u
    require(tail(2) == F(-4, 375), "exceptional negative depth-two tail")
    for j in range(3, 13):
        scaled = (6 * j - 7) * 5 ** (j - 1) - 2 * 3 ** j - (6 * j + 1)
        require(tail(j) == F(2, 5) * F(scaled, 15 ** j)
                and scaled >= 48 * j - 118 > 0, "positive-tail coefficient estimate")
    return {"profiles": profiles, "initial_first_change_excesses": [first_change_limit(h) for h in (1, 2, 3)],
            "exceptional_depth_two_tail": F(-4, 375), "limit": ROW_PHASE_LIMIT,
            "scope": "exact formula controls; all-height alignment is proved by first-change charging"}


def _jsonable(value):
    if type(value) is F:
        return str(value)
    if type(value) is dict:
        if all(type(k) is str for k in value):
            return {key: _jsonable(item) for key, item in value.items()}
        return [{"key": _jsonable(key), "value": _jsonable(item)} for key, item in value.items()]
    if type(value) in (tuple, list):
        return [_jsonable(item) for item in value]
    return value


def from_json(payload):
    require(type(payload) is dict and set(payload) == {"height", "source"}, "input needs exactly height and source")
    height, source = payload["height"], payload["source"]
    certificate = make_common_law(height, source)
    return {"certificate": certificate, "verification": verify_common_law(height, source, certificate)}


def self_check():
    recursive = _sibling("recursive_minimum_source_common_law.py", "_recursive_common_law")
    obstruction = _sibling("fixed_source_subclass_decomposition_obstruction.py", "_fixed_source_obstruction")
    roots = _sibling("cell_tail_root_type_bound.py", "_cell_tail_root_types")
    fixtures = [("three_rows_height_zero", 0, {(r, 0) for r in (1, 2, 3)}),
                ("four_rows_height_zero", 0, {(r, 0) for r in ROWS}),
                ("type_E_eight_points", 1, set(roots.fixtures()["E"][0])),
                ("399_obstruction", 2, obstruction.fixture(2)),
                ("three_rows_five_tree", 2, {(r, y) for r in (1, 2, 3) for y in recursive.five_leaves(2)}),
                ("full_carrier", 2, set(product(ROWS, range(49))))]
    for height in (1, 2, 3):
        fixtures.append(("401_pure_" + str(height), height, set(recursive.law(height))))
        fixtures.append(("401_coloured_" + str(height), height,
                         set(recursive.coloured_law(height, recursive.last_digit_colour))))
    controls = []
    for name, height, source in fixtures:
        certificate = make_common_law(height, source)
        audit = verify_common_law(height, source, certificate)
        controls.append({"name": name, "height": height, "source_points": len(source),
                         "law_support_points": len(certificate["nu"]),
                         "shell_bound": audit["shell_bound"], "row_phase_bound": audit["row_phase_bound"],
                         "actual_prefix_shell_bound": audit["actual_prefix_shell_bound"]})
    require(len(fixtures[2][2]) == 8, "retained type-E fixture has eight points")
    require(F(8, 5) * F(15, 8) + F(9, 5) * 3 - F(6, 5) * F(60, 49) == LIMIT, "infinite series limit")
    import copy
    source = set(roots.fixtures()["E"][0])
    certificate = make_common_law(1, source)
    bad_weight = copy.deepcopy(certificate)
    bad_weight["pair_weights"][PAIRS[0]] += F(1, 7)
    bad_law = copy.deepcopy(certificate)
    bad_law["nu"][next(iter(bad_law["nu"]))] = 1.0
    bad_tree = copy.deepcopy(certificate)
    bad_tree["full_witness"]["leaves"] = (0, 0, 1, 2, 3)
    invalid = [lambda h=h: make_common_law(h, source) for h in (True, False, -1, 1.0, "1")]
    invalid += [lambda s=s: make_common_law(1, s) for s in (
        [], "source", {(0, 0)}, {(5, 0)}, {(True, 0)}, {(1.0, 0)}, {(1, True)},
        {(1, 0.0)}, {(1, -1)}, {(1, 7)}, [(1, 0), (1, 0)], [(1,)],
        {(r, y) for r in ROWS for y in range(3)},
        {(1, y) for y in range(5)},
    )]
    invalid += [lambda c=c: verify_common_law(1, source, c) for c in (bad_weight, bad_law, bad_tree)]
    invalid += [lambda: from_json({"height": 1, "source": list(source), "extra": 0})]
    invalid += [lambda: row_phase_profile_bound({1: F(1), 2: F(0), 3: F(0), 4: F(0)}, (True,)),
                lambda: row_phase_profile_bound({1: 1.0, 2: F(0), 3: F(0), 4: F(0)}, (1,)),
                lambda: first_change_limit(0)]
    rejected = 0
    for operation in invalid:
        try:
            operation()
        except ValueError:
            rejected += 1
    require(rejected == len(invalid), "malformed source, premises or certificate was accepted")
    cli = from_json({"height": 0, "source": [[1, 0], [2, 0], [3, 0]]})
    require(cli["verification"]["shell_bound"] == F(11, 5), "JSON constructor boundary")
    integer_beta = copy.deepcopy(cli["certificate"])
    integer_beta["beta"] = {r: int(v) for r, v in integer_beta["beta"].items()}
    require(verify_common_law(0, {(r, 0) for r in (1, 2, 3)}, integer_beta)
            == cli["verification"], "equal-valued integer beta must preserve exact verification")
    return {"controls": controls, "rejected_inputs": rejected, "uniform_limit": LIMIT,
            "limit_excess_above_six": LIMIT - 6,
            "row_phase_controls": row_phase_controls(), "row_phase_limit": ROW_PHASE_LIMIT,
            "row_phase_limit_excess_above_six": ROW_PHASE_LIMIT - 6,
            "scope": "exact common-law controls and prefix envelopes; no target comparison or optimality claim"}


def main():
    if len(sys.argv) == 1:
        result = self_check()
    else:
        require(sys.argv[1:] == ["--stdin"], "usage: full_and_pair_tree_common_law.py [--stdin]")
        result = from_json(json.load(sys.stdin))
    print(json.dumps(_jsonable(result), indent=2))


if __name__ == "__main__":
    main()
