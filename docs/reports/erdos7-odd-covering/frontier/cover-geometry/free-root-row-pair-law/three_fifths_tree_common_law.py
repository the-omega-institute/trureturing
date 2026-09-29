#!/usr/bin/env python3
"""One actual tree-mixture law with a universal 309/50 original-layout bound.

The law is (3/5)*mu+(2/5)*omega, using the actual full/pair witnesses
of full_and_pair_tree_common_law.py. Exact prefix checks retain beta,
and 13 concave supergradient certificates cover early row changes.
The all-height conclusion also uses the analytic first-change and
geometric-tail argument in the report, not a row-word search cutoff.

The limiting constant is sharp for arbitrary permitted witness choices;
it is not the minimax constant over all laws on a source and exceeds 6.
No arguments prints checks. --stdin accepts {"height":K,"source":[[r,y],...]}.
Only stdout is written. All arithmetic is exact and standard-library only.
"""
from collections import defaultdict
from fractions import Fraction as F
from itertools import product
from pathlib import Path
import importlib.util
import json
import sys


def require(ok, message):
    if not ok:
        raise ValueError(message)


def _sibling(filename, name):
    spec = importlib.util.spec_from_file_location(name, Path(__file__).with_name(filename))
    if spec is None or spec.loader is None:
        raise ImportError(filename)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


_common = _sibling("full_and_pair_tree_common_law.py", "_three_fifths_components")
ROWS, PAIRS = _common.ROWS, _common.PAIRS
MIX, PAIR = F(3, 5), F(4, 15)
LIMIT = F(309, 50)


def row_cap(depth, beta):
    return MIX * min(beta, F(1, 5 ** depth)) + PAIR * (1 - beta) / 3 ** depth


def aligned_profile(height):
    """Value attained by an aligned beta=1/5 profile; not every finite cap maximum."""
    _common._height(height)
    s5 = sum((F(2 * j + 1, 5 ** j) for j in range(height + 1)), F(0))
    s3 = sum((F(2 * j + 1, 3 ** j) for j in range(height + 1)), F(0))
    return F(12, 5) * s5 + F(26, 25) * s3 - F(36, 25)


def _weights(rows):
    require(type(rows) in (tuple, list) and rows
            and all(type(r) is int and r in ROWS for r in rows), "nonempty literal actual-row word")
    weights = {r: [0] * len(rows) for r in ROWS}
    for j, r in enumerate(rows):
        weights[r][j] += 2 * j + 3 + 2 * sum(s == r for s in rows[:j])
        for s in rows[:j]:
            weights[s][j] += 2
    return weights


def _beta(beta):
    require(type(beta) is dict and set(beta) == set(ROWS)
            and all(type(r) is int and type(b) in (int, F) and b >= 0 for r, b in beta.items())
            and sum(beta.values(), F(0)) == 1, "exact four-row probability beta required")


def profile_bound(rows, beta):
    """Exact independent-row cap functional for this specified word and beta."""
    weights = _weights(rows)
    _beta(beta)
    pure = sum((F(2 * j + 1) * (MIX / 5 ** j + (1 - MIX) / 3 ** j)
                for j in range(len(rows))), F(0))
    return pure + sum((weights[r][j] * row_cap(j, beta[r])
                       for r in ROWS for j in range(len(rows))), F(0))


def certify_profile_maximum(rows, beta, expected):
    """Verify an exact common supergradient, proving the global simplex maximum.

    Each coordinate function is concave piecewise linear. A common slope
    supports every coordinate at the supplied beta, so summing the four
    support inequalities proves the claimed upper bound for all beta.
    This is a certificate check, not a numerical or exhaustive optimizer.
    """
    weights = _weights(rows)
    _beta(beta)
    require(type(expected) in (int, F), "exact profile value required")
    require(profile_bound(rows, beta) == expected, "incorrect claimed profile value")
    slopes = {}
    for r in ROWS:
        b = F(beta[r])
        penalty = PAIR * sum((F(weights[r][j], 3 ** j) for j in range(len(rows))), F(0))
        left = MIX * sum(weights[r][j] for j in range(len(rows)) if b <= F(1, 5 ** j)) - penalty
        right = MIX * sum(weights[r][j] for j in range(len(rows)) if b < F(1, 5 ** j)) - penalty
        require(left >= right, "coordinate slopes must be nonincreasing")
        slopes[r] = {"left": left, "right": right}
    lower = max(slopes[r]["right"] for r in ROWS if beta[r] < 1)
    upper = min(slopes[r]["left"] for r in ROWS if beta[r] > 0)
    require(lower <= upper, "no common supporting slope: proposed profile is not certified optimal")
    supporting = lower
    require(all((beta[r] == 1 or supporting >= slopes[r]["right"])
                and (beta[r] == 0 or supporting <= slopes[r]["left"]) for r in ROWS),
            "simplex-boundary supergradient conditions")
    return {"rows": tuple(rows), "beta": beta, "maximum": F(expected),
            "supporting_slope": supporting, "coordinate_slopes": slopes}


# These are exact finite certificates for the 13 early-change branches,
# not samples asserted to cover unrestricted word lengths.
EARLY_CERTIFICATES = (
    ("0010", F(291698, 50625), (F(1, 5), F(1, 25), F(0), F(19, 25))),
    ("0011", F(292907, 50625), (F(24, 25), F(1, 25), F(0), F(0))),
    ("0012", F(97196, 16875), (F(119, 125), F(1, 25), F(1, 125), F(0))),
    ("0100", F(285313, 50625), (F(4, 5), F(1, 5), F(0), F(0))),
    ("0101", F(287927, 50625), (F(4, 5), F(1, 5), F(0), F(0))),
    ("0102", F(57464, 10125), (F(99, 125), F(1, 5), F(1, 125), F(0))),
    ("0110", F(293327, 50625), (F(4, 5), F(1, 5), F(0), F(0))),
    ("0111", F(297913, 50625), (F(4, 5), F(1, 5), F(0), F(0))),
    ("0112", F(295904, 50625), (F(99, 125), F(1, 5), F(1, 125), F(0))),
    ("0120", F(289052, 50625), (F(19, 25), F(1, 5), F(1, 25), F(0))),
    ("0121", F(292132, 50625), (F(19, 25), F(1, 5), F(1, 25), F(0))),
    ("0122", F(293012, 50625), (F(19, 25), F(1, 5), F(1, 25), F(0))),
    ("0123", F(291409, 50625), (F(94, 125), F(1, 5), F(1, 25), F(1, 125))),
)


def analytic_controls():
    certificates = [certify_profile_maximum(tuple(int(d) + 1 for d in word),
                                           dict(zip(ROWS, beta)), value)
                    for word, value, beta in EARLY_CERTIFICATES]
    # Normalize a four-letter prefix by first appearance. Excluding 0000
    # and 0001 leaves exactly the first-change-depth 1 or 2 cases.
    expected_words = {"".join(map(str, word)) for word in product(range(4), repeat=4)
                      if word[0] == 0 and all(word[j] <= max(word[:j]) + 1 for j in range(1, 4))
                      and (word[1] != 0 or word[2] != 0)}
    require({word for word, _, _ in EARLY_CERTIFICATES} == expected_words and len(expected_words) == 13,
            "complete disjoint early-prefix case split")
    prefix_maximum = max(c["maximum"] for c in certificates)
    require(prefix_maximum == F(297913, 50625), "early-prefix maximum")

    def geometric(z, first):
        return z ** first / (1 - z)

    def arithmetic(z, first):
        return z ** first * (F(first, 1) / (1 - z) + z / (1 - z) ** 2)

    tail = MIX * (8 * arithmetic(F(1, 5), 4) + 2 * geometric(F(1, 5), 4))
    tail += ((1 - MIX) * (2 * arithmetic(F(1, 3), 4) + geometric(F(1, 3), 4))
             + PAIR * (6 * arithmetic(F(1, 3), 4) + geometric(F(1, 3), 4))
             - PAIR * (6 * arithmetic(F(1, 15), 4) + geometric(F(1, 15), 4)))
    require(tail == F(633557, 2480625) and prefix_maximum + tail == F(564122, 91875)
            and LIMIT - prefix_maximum - tail == F(7331, 183750) > 0, "analytic nonconstant-tail ceiling")
    aligned_beta = {1: F(1, 5), 2: F(4, 5), 3: F(0), 4: F(0)}
    constant_controls = []
    for height in range(2, 9):
        exact = profile_bound((1,) * (height + 1), aligned_beta)
        require(exact == aligned_profile(height) < LIMIT, "constant-row aligned formula")
        constant_controls.append(certify_profile_maximum((1,) * (height + 1), aligned_beta, exact))
    low_beta = {1: F(1), 2: F(0), 3: F(0), 4: F(0)}
    low = [certify_profile_maximum((1,) * (height + 1), low_beta, value)
           for height, value in ((0, F(14, 5)), (1, F(116, 25)))]
    require(F(12, 5) * F(15, 8) + F(26, 25) * 3 - F(36, 25) == LIMIT, "aligned limiting value")
    # Constant-prefix derivative inequalities used at every N>=2.
    right_at_two = 1 - F(4, 5) * (F(23, 9) - 1)
    left_infinite = 1 + F(27, 5) - F(4, 5) * 2
    require(right_at_two == F(-11, 45) < 0 and left_infinite == F(24, 5) > 0,
            "all-long-prefix derivative signs")
    # Formula controls for the all-height reduction to the already proved
    # two-fifths first-change estimate. No finite cutoff proves its sign.
    change_controls = []
    for h, last in ((3, 3), (3, 9), (4, 7), (8, 12)):
        def caps(j):
            f, q = F(1, 5 ** j), F(1, 3 ** j)
            old_u = F(2, 5) * (f + (1 - f) * q)
            old_v = F(2, 5) * (f + F(4, 5) * q)
            new_u = MIX * f + PAIR * (1 - f) * q
            new_v = row_cap(j, F(1, 5))
            require(new_u == F(2, 3) * old_u + f / 3
                    and new_v == F(2, 3) * old_v + f / 3, "first-change affine cap relation")
            return old_u, old_v, new_u, new_v
        ou, ov, nu, nv = caps(h)
        old_d = (6 * h + 3) * (ou - ov) - 2 * h * ou
        new_d = (6 * h + 3) * (nu - nv) - 2 * h * nu
        for j in range(h + 1, last + 1):
            ou, ov, nu, nv = caps(j)
            old_d += (6 * j + 3) * (ou - ov) - 2 * ou
            new_d += (6 * j + 3) * (nu - nv) - 2 * nu
        correction = F(2 * h, 3 * 5 ** h) + F(2, 3) * sum((F(1, 5 ** j) for j in range(h + 1, last + 1)), F(0))
        require(new_d == F(2, 3) * old_d - correction < 0
                and old_d <= _common.first_change_limit(h) < 0, "late-first-change domination")
        change_controls.append({"first_change": h, "last_depth": last, "old_excess": old_d, "new_excess": new_d})
    return {"early_prefix_certificates": certificates, "prefix_maximum": prefix_maximum,
            "infinite_nonconstant_tail": tail, "early_ceiling": prefix_maximum + tail,
            "early_margin_to_limit": LIMIT - prefix_maximum - tail,
            "constant_profile_controls": constant_controls, "short_constant_profiles": low,
            "late_change_controls": change_controls, "limit": LIMIT,
            "scope": "exact finite supergradients and analytic identities, with all-height case proof in the report"}


def make_law(height, source, components=None):
    """Construct one supported probability, allowing supplied valid witness choices."""
    if components is None:
        components = _common.make_common_law(height, source)
    _common.verify_common_law(height, source, components)
    law = _common._mixture(((MIX, components["mu"]), (1 - MIX, components["omega"])))
    return {"height": height, "components": components, "nu": law}


def verify_law(height, source, certificate):
    source = _common.validate_source(height, source)
    require(type(certificate) is dict and set(certificate) == {"height", "components", "nu"}
            and type(certificate["height"]) is int and certificate["height"] == height, "three-fifths certificate schema")
    components = certificate["components"]
    _common.verify_common_law(height, source, components)
    law = certificate["nu"]
    _common._probability(law, source, "three-fifths nu")
    require(law == _common._mixture(((MIX, components["mu"]), (1 - MIX, components["omega"]))),
            "three-fifths probability identity")
    checks = []
    for depth in range(height + 1):
        pure, joint = _common._prefixes(law, depth)
        pure_bound = MIX / 5 ** depth + (1 - MIX) / 3 ** depth
        by_row = {r: row_cap(depth, components["beta"][r]) for r in ROWS}
        require(max(pure.values()) <= pure_bound
                and all(mass <= by_row[r] for (r, _), mass in joint.items()), "actual three-fifths prefix caps")
        checks.append({"depth": depth, "plain_max": max(pure.values()), "plain_bound": pure_bound,
                       "joint_max": max(joint.values()), "row_bounds": by_row})
    return {"height": height, "source_points": len(source), "law_support_points": len(law),
            "prefix_checks": checks, "strict_uniform_bound": LIMIT,
            "scope": "one actual law obeys the analytic 309/50 bound; finite Gamma optimality and the 2*t_K target are not claimed"}


def sharpness_source(height, four_active=False):
    """Actual permitted witnesses attaining the aligned profile at every K>=1."""
    _common._height(height)
    require(height >= 1 and type(four_active) is bool, "positive height and boolean four-active option")
    def leaves(base):
        result = {0}
        for _ in range(height):
            result = {d + 7 * y for d in range(base) for y in result}
        return result
    full, ternary = leaves(5), leaves(3)
    mu = {(1 if y % 7 == 0 else 2, y): F(1, 5 ** height) for y in full}
    eta = {}
    for pair in PAIRS:
        row = 1 if 1 in pair else (2 if 2 in pair else 3)
        eta[pair] = {(row, y): F(1, 3 ** height) for y in ternary}
    source = set(mu).union(*(set(law) for law in eta.values()))
    if four_active:
        source.add((4, 7 ** height - 1))
    beta = {1: F(1, 5), 2: F(4, 5), 3: F(0), 4: F(0)}
    pair_weights = {pair: (1 - beta[pair[0]] - beta[pair[1]]) / 3 for pair in PAIRS}
    omega = _common._mixture((pair_weights[pair], eta[pair]) for pair in PAIRS)
    def witness(rows, branching, law):
        return {"rows": rows, "branching": branching, "value": F(1),
                "leaves": tuple(sorted(y for _, y in law)), "points": tuple(sorted(law))}
    components = {"height": height, "full_witness": witness(ROWS, 5, mu),
                  "pair_witnesses": {pair: witness(pair, 3, eta[pair]) for pair in PAIRS},
                  "mu": mu, "beta": beta, "pair_laws": eta, "pair_weights": pair_weights,
                  "omega": omega, "nu": _common._mixture(((F(2, 5), mu), (F(3, 5), omega)))}
    certificate = make_law(height, source, components)
    verify_law(height, source, certificate)
    phases = tuple(a for j in range(height + 1) for a in (0, 7 ** j * pow(7 ** j, -1, 5)))
    _common._trees.validate_layout(height, phases)
    expectation = sum((mass * _common._trees.literal_layout_cost(height, phases, point)
                       for point, mass in certificate["nu"].items()), F(0))
    require(expectation == aligned_profile(height), "actual aligned layout attains the sharpness profile")
    return {"source": source, "certificate": certificate,
            "audit": {"height": height, "source_points": len(source), "active_rows": len({r for r, _ in source}),
                      "original_divisors": _common._trees.original_divisors(height), "literal_phases": phases,
                      "actual_layout_expectation": expectation, "aligned_profile": aligned_profile(height),
                      "limiting_ceiling": LIMIT,
                      "scope": "one attained layout profile; sharp limiting ceiling for arbitrary witness choices, not source minimax"}}


def self_check():
    analytic = analytic_controls()
    recursive = _sibling("recursive_minimum_source_common_law.py", "_three_fifths_recursive")
    obstruction = _sibling("fixed_source_subclass_decomposition_obstruction.py", "_three_fifths_obstruction")
    source_controls = []
    fixtures = [("three_rows_zero", 0, {(r, 0) for r in (1, 2, 3)}),
                ("399", 2, obstruction.fixture(2)),
                ("full_carrier", 2, set(product(ROWS, range(49))))]
    for h in (1, 2, 3):
        fixtures.append(("401_pure", h, set(recursive.law(h))))
        fixtures.append(("401_coloured", h, set(recursive.coloured_law(h, recursive.last_digit_colour))))
    for name, height, source in fixtures:
        certificate = make_law(height, source)
        audit = verify_law(height, source, certificate)
        source_controls.append({"name": name, "height": height, "points": len(source),
                                "law_support_points": audit["law_support_points"]})
    sharpness = [sharpness_source(h, h == 3)["audit"] for h in range(1, 6)]
    source = {(r, 0) for r in (1, 2, 3)}
    import copy
    bad = copy.deepcopy(make_law(0, source))
    bad["nu"][next(iter(bad["nu"]))] = 1.0
    invalid = [lambda h=h: make_law(h, source) for h in (True, False, -1, 0.0, "0")]
    invalid += [lambda: verify_law(0, source, bad), lambda: sharpness_source(0),
                lambda: sharpness_source(1, 1),
                lambda: profile_bound((True,), {1: F(1), 2: F(0), 3: F(0), 4: F(0)}),
                lambda: certify_profile_maximum((1, 2, 2, 2), {r: F(1, 4) for r in ROWS}, F(1)),
                lambda: certify_profile_maximum((1, 2, 2, 2), {r: F(1, 4) for r in ROWS},
                                                  profile_bound((1, 2, 2, 2), {r: F(1, 4) for r in ROWS}))]
    rejected = 0
    for operation in invalid:
        try:
            operation()
        except ValueError:
            rejected += 1
    require(rejected == len(invalid), "invalid data or nonoptimal supergradient candidate accepted")
    return {"analytic_certificates": analytic, "source_controls": source_controls,
            "sharpness_controls": sharpness, "rejected_inputs": rejected,
            "uniform_bound": LIMIT, "excess_above_six": LIMIT - 6,
            "scope": "ordinary all-height cap proof with exact witnesses and supergradients; no covering conclusion"}


def main():
    if len(sys.argv) == 1:
        result = self_check()
    else:
        require(sys.argv[1:] == ["--stdin"], "usage: three_fifths_tree_common_law.py [--stdin]")
        payload = json.load(sys.stdin)
        require(type(payload) is dict and set(payload) == {"height", "source"}, "input requires height and source")
        certificate = make_law(payload["height"], payload["source"])
        result = {"certificate": certificate, "verification": verify_law(payload["height"], payload["source"], certificate)}
    print(json.dumps(_common._jsonable(result), indent=2))


if __name__ == "__main__":
    main()
