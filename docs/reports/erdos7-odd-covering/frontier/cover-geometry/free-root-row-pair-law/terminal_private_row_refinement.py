#!/usr/bin/env python3
"""One exact common law for private rows at the last seven-adic digit.

make_common_law(height, source, tree, private_digits) accepts any finite
actual source containing the four specified private points above every
leaf of a complete five-ary tree of height-1. It returns an exact law and
an attaining layout at all original divisors. verify_common_law validates
the complete certificate against the actual source.

make_refinement(base_height, source, terminal_digits=None) constructs
this support by adding four private terminal rows and retaining old row
labels in a fifth child. It requires the old projection to be exactly a
complete five-ary tree and preserves its point surplus and pair trees.
Per-leaf child digits may differ; all are literal digits in 0..6.

The exact maximum for this law is 105/32+(180*K+55)/(32*5**K), K>=2.
This is an ordinary proved identity checked on finite inputs, not a
Lean certificate or an all-source minimax theorem. Size grows with the
supplied finite source; no point or height cutoff is implicit.

No arguments runs exact controls. --stdin accepts either:
  {"operation":"refine", "height":H, "source":[[r,y], ...],
   "terminal_digits":[[y,[d0,d1,d2,d3,d4]], ...]}
or
  {"operation":"law", "height":K, "source":[[r,y], ...],
   "tree":[y,...], "private_digits":[[y,[d1,d2,d3,d4]], ...]}.
terminal_digits is optional in refine mode. Output is JSON on stdout;
non-string-key dictionaries are encoded as key/value entry lists.
Only standard-library and sibling research modules are used.
"""
from collections import defaultdict
from fractions import Fraction as F
from itertools import combinations, product
from pathlib import Path
import copy
import importlib.util
import json
import sys

ROWS = (1, 2, 3, 4)


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


_trees = _sibling("prime_layout_mixture_certificate.py", "_terminal_private_tree_api")


def _height(height, minimum=0):
    require(type(height) is int and height >= minimum,
            "height must be an integer at least " + str(minimum))


def validate_source(height, source):
    """Validate a nonempty finite literal source without coercing its data."""
    _height(height)
    require(type(source) in (set, frozenset, list, tuple) and source,
            "source must be a nonempty finite point collection")
    points = []
    for point in source:
        require(type(point) in (tuple, list) and len(point) == 2,
                "source point must be a row-residue pair")
        row, residue = point
        require(type(row) is int and row in ROWS and type(residue) is int
                and 0 <= residue < 7**height, "point outside the literal carrier")
        points.append((row, residue))
    require(len(set(points)) == len(points), "duplicate source points")
    return frozenset(points)


def validate_five_tree(height, leaves):
    """Require exactly one full five-ary tree, not a superset of a tree."""
    _height(height)
    require(type(leaves) in (set, frozenset, list, tuple), "finite tree leaves required")
    require(all(type(y) is int and 0 <= y < 7**height for y in leaves),
            "tree leaf outside the literal residue space")
    require(len(set(leaves)) == len(leaves), "duplicate tree leaves")
    require(len(leaves) == 5**height
            and _trees.contains_bary_tree(leaves, height, 5),
            "leaves must form a complete five-ary tree")
    return frozenset(leaves)


def _digits(leaves, mapping, width):
    require(type(mapping) is dict and all(type(y) is int for y in mapping)
            and set(mapping) == set(leaves), "one digit tuple per tree leaf required")
    result = {}
    for y, digits in mapping.items():
        require(type(digits) in (list, tuple) and len(digits) == width,
                "incorrect terminal digit tuple")
        require(all(type(d) is int and 0 <= d < 7 for d in digits)
                and len(set(digits)) == width, "terminal digits must be distinct literals")
        result[y] = tuple(digits)
    return result


def exact_moment(height):
    """The proved exact maximum for the specified terminal private-row law."""
    _height(height, 2)
    return F(105, 32) + F(180*height + 55, 32*5**height)


def _phases(height, point):
    row, residue = point
    modulus = 7**height
    x = residue + modulus*((row-residue)*pow(modulus, -1, 5) % 5)
    return tuple(x % d for d in _trees.original_divisors(height))


def make_common_law(height, source, tree, private_digits):
    """Construct a certificate on arbitrary actual supported private rows.

    tree lies at height-1; private_digits[y][r-1] selects row r's
    private last digit. The four digits at each leaf must be distinct.
    The source may contain additional points. No pair-tree premise or
    full-five projection of the target source is required for this law.
    """
    _height(height, 2)
    source = validate_source(height, source)
    tree = validate_five_tree(height-1, tree)
    digits = _digits(tree, private_digits, 4)
    nu = {(r, y + 7**(height-1)*digits[y][r-1]): F(1, 4*5**(height-1))
          for y in sorted(tree) for r in ROWS}
    require(set(nu) <= source, "source lacks a required private row point")
    point = min(nu)
    return {"height": height, "tree": tuple(sorted(tree)), "private_digits": digits,
            "nu": nu, "attainer_point": point, "original_phases": _phases(height, point)}


def make_refinement(base_height, source, terminal_digits=None):
    """Refine any source whose projection is exactly a complete five-tree.

    terminal_digits[y] has five distinct entries: old labels use entry
    zero and row r's new private point uses entry r. No source is silently
    discarded or projected onto a selected subsource.
    """
    _height(base_height, 1)
    source = validate_source(base_height, source)
    tree = validate_five_tree(base_height, {y for _, y in source})
    if terminal_digits is None:
        terminal_digits = {y: (0, 1, 2, 3, 4) for y in tree}
    digits = _digits(tree, terminal_digits, 5)
    modulus = 7**base_height
    refined = {(r, y + modulus*digits[y][0]) for r, y in source}
    refined.update((r, y + modulus*digits[y][r]) for y in tree for r in ROWS)
    certificate = make_common_law(base_height+1, refined, tree,
                                  {y: ds[1:] for y, ds in digits.items()})
    return {"height": base_height+1, "source": frozenset(refined),
            "terminal_digits": digits, "certificate": certificate}


def verify_common_law(height, source, certificate):
    """Validate support, the exact law, every prefix mass and a literal attainer.

    The shell sum is an upper bound for all independently chosen phases
    by the report's LCM-intersection proof. Its equality with the directly
    evaluated original-divisor layout certifies the exact maximum for
    this one law. It does not certify optimality among all source laws.
    """
    _height(height, 2)
    source = validate_source(height, source)
    keys = {"height", "tree", "private_digits", "nu", "attainer_point", "original_phases"}
    require(type(certificate) is dict and set(certificate) == keys,
            "certificate fields must match the complete certificate schema")
    require(type(certificate["height"]) is int and certificate["height"] == height,
            "certificate height mismatch")
    tree = validate_five_tree(height-1, certificate["tree"])
    digits = _digits(tree, certificate["private_digits"], 4)
    private_points = {(r, y + 7**(height-1)*digits[y][r-1]) for y in tree for r in ROWS}
    require(private_points <= source, "unsupported private row point")
    nu = certificate["nu"]
    require(type(nu) is dict and nu, "nu must be a nonempty probability dictionary")
    mass = F(1, 4*5**(height-1))
    for point, weight in nu.items():
        require(type(point) is tuple and len(point) == 2
                and all(type(x) is int for x in point) and point in source,
                "nonliteral or unsupported probability point")
        require(type(weight) in (int, F) and weight > 0 and weight == mass,
                "each private point needs its positive exact uniform mass")
    require(set(nu) == private_points and sum(nu.values(), F(0)) == 1,
            "the probability must include exactly the private points")
    prefix_maxima = []
    for b in range(height+1):
        plain, joint = defaultdict(F), defaultdict(F)
        for (r, y), weight in nu.items():
            plain[y % 7**b] += weight
            joint[r, y % 7**b] += weight
        if b < height:
            prefixes = {y % 7**b for y in tree}
            require(set(plain) == prefixes and set(joint) == set(product(ROWS, prefixes)),
                    "incorrect selected prefixes")
            require(all(x == F(1, 5**b) for x in plain.values())
                    and all(x == F(1, 4*5**b) for x in joint.values()),
                    "actual prefix masses violate the uniform row identity")
        else:
            require(all(x == mass for x in plain.values())
                    and all(x == mass for x in joint.values()),
                    "last private digit must determine its row")
        prefix_maxima.append((max(plain.values()), max(joint.values())))
    shell = sum(((2*b+1)*(m+3*c) for b, (m, c) in enumerate(prefix_maxima)), F(0))
    require(shell == exact_moment(height), "measured shell sum disagrees with its formula")
    point = certificate["attainer_point"]
    require(type(point) in (tuple, list) and len(point) == 2
            and all(type(x) is int for x in point) and tuple(point) in nu,
            "attainer must be an actual private point")
    phases = _trees.validate_layout(height, certificate["original_phases"])
    require(phases == _phases(height, point), "phases must follow the declared private point")
    actual = sum((weight*_trees.literal_layout_cost(height, phases, point)
                  for point, weight in nu.items()), F(0))
    require(actual == shell, "literal original-divisor layout does not attain the shell bound")
    target = 6-F(2*(height+2), 3**height)
    require(actual < target, "target comparison failed")
    return {"height": height, "source_points": len(source), "law_points": len(nu),
            "prefix_maxima": tuple(prefix_maxima), "exact_moment": actual,
            "target": target, "gap": target-actual,
            "original_divisors": _trees.original_divisors(height),
            "attaining_original_phases": phases,
            "scope": "exact maximum for one supported law, not a source minimax value"}


def _json_digit_map(data):
    require(type(data) is list, "digit map must be a list of leaf/digit-tuples")
    result = {}
    for item in data:
        require(type(item) is list and len(item) == 2 and type(item[0]) is int,
                "each digit-map entry needs a literal leaf and tuple")
        require(item[0] not in result, "duplicate digit-map leaf")
        result[item[0]] = item[1]
    return result


def from_json(data):
    require(type(data) is dict, "JSON input must be an object")
    mode = data.get("operation")
    if mode == "refine":
        require(set(data) in ({"operation", "height", "source"},
                             {"operation", "height", "source", "terminal_digits"}),
                "unexpected or missing refine input fields")
        digits = _json_digit_map(data["terminal_digits"]) if "terminal_digits" in data else None
        result = make_refinement(data["height"], data["source"], digits)
    else:
        require(mode == "law" and set(data) ==
                {"operation", "height", "source", "tree", "private_digits"},
                "unexpected operation or law input fields")
        certificate = make_common_law(data["height"], data["source"], data["tree"],
                                       _json_digit_map(data["private_digits"]))
        result = {"height": data["height"], "source": validate_source(data["height"], data["source"]),
                  "certificate": certificate}
    result["verification"] = verify_common_law(result["height"], result["source"], result["certificate"])
    return result


def _jsonable(value):
    if type(value) is F:
        return str(value)
    if type(value) is dict:
        if all(type(k) is str for k in value):
            return {k: _jsonable(v) for k, v in value.items()}
        return [{"key": _jsonable(k), "value": _jsonable(v)} for k, v in value.items()]
    if type(value) in (set, frozenset):
        return [_jsonable(v) for v in sorted(value)]
    if type(value) in (tuple, list):
        return [_jsonable(v) for v in value]
    return value


def _source_control(old_height, old, result, audit_api):
    source, cert = result["source"], result["certificate"]
    height = old_height+1
    require(len(source)-5**height == len(old)-5**old_height, "point surplus changed")
    for pair in combinations(ROWS, 2):
        old_good = _trees.contains_bary_tree({y for r, y in old if r in pair}, old_height, 3)
        new_good = _trees.contains_bary_tree({y for r, y in source if r in pair}, height, 3)
        require(old_good == new_good, "pair-tree capability changed")
    measured = verify_common_law(height, source, cert)
    audit = audit_api.audit_fixed_source(source, height)
    require(audit["full_fiveary"] and not any(audit["individual_fiveary"].values())
            and not any(audit["omitted_row_fiveary"].values()), "full/proper-row tree conditions")
    columns = sorted({y % 7 for _, y in source})
    child_sizes = tuple(sum(y % 7 == c for _, y in source) for c in columns)
    if height >= 3:
        second = defaultdict(set)
        for r, y in source:
            second[r, y % 7].add(y//7 % 7)
        require(len(second) == 20 and all(len(ds) == 5 for ds in second.values()),
                "claimed sparse-root exclusion fails")
    return {"height": height, "source_points": len(source), "law_points": len(cert["nu"]),
            "root_columns": columns, "child_sizes": child_sizes,
            "all_six_pair_trees": all(audit["pair_ternary"].values()),
            "exact_moment": measured["exact_moment"], "gap": measured["gap"],
            "attaining_original_phases": measured["attaining_original_phases"]}


def malformed_controls(root, refined):
    source, certificate = refined["source"], refined["certificate"]
    tests = []
    for h in (True, False, -1, 0, 1.0, "1"):
        tests.append(lambda h=h: make_refinement(h, root))
    for s in ([], "source", [(1, 0), (1, 0)], [(1,)], [(0, 0)], [(True, 0)],
              [(1, True)], [(1, 0.0)], [(1, -1)], [(1, 7)], [(1, [0])],
              [(1, y) for y in range(4)]):
        tests.append(lambda s=s: make_refinement(1, s))
    for tree in ((0, 0, 1, 2, 3), (True, 1, 2, 3, 4), (0, 1, 2, 3, 7)):
        tests.append(lambda tree=tree: validate_five_tree(1, tree))
    tests.append(lambda: validate_five_tree(2, list(range(25))))
    base_digits = {y: (0, 1, 2, 3, 4) for y in range(5)}
    for digits in ({}, {**base_digits, 6: (0, 1, 2, 3, 4)},
                   {**base_digits, 0: (0, 1, 2, 3, 3)},
                   {**base_digits, 0: (0, 1, 2, 3, 7)},
                   {**base_digits, 0: (0, 1, 2, 3, True)},
                   {**base_digits, 0: (0, 1, 2, 3, [4])},
                   {**base_digits, 0: (0, 1, 2)}, "map"):
        tests.append(lambda digits=digits: make_refinement(1, root, digits))
    point = next(iter(certificate["nu"]))
    for value in (True, 0.05, F(-1), F(0), F(1, 19)):
        bad = copy.deepcopy(certificate)
        bad["nu"][point] = value
        tests.append(lambda bad=bad: verify_common_law(2, source, bad))
    changes = (("height", True), ("height", 3), ("tree", (0, 0, 1, 2, 3)),
               ("attainer_point", (True, point[1])), ("attainer_point", (0, point[1])),
               ("original_phases", (0,)),
               ("original_phases", (0, 0, 0, 0, 0, 0)))
    for key, value in changes:
        bad = copy.deepcopy(certificate)
        bad[key] = value
        tests.append(lambda bad=bad: verify_common_law(2, source, bad))
    missing = source-{point}
    tests.append(lambda: verify_common_law(2, missing, certificate))
    tests.append(lambda: make_common_law(2, missing, certificate["tree"], certificate["private_digits"]))
    bad = copy.deepcopy(certificate)
    del bad["nu"][point]
    tests.append(lambda bad=bad: verify_common_law(2, source, bad))
    bad = copy.deepcopy(certificate)
    bad["nu"][(0, 0)] = bad["nu"].pop(point)
    tests.append(lambda bad=bad: verify_common_law(2, source, bad))
    bad = copy.deepcopy(certificate)
    bad["extra"] = 1
    tests.append(lambda bad=bad: verify_common_law(2, source, bad))
    tests.append(lambda: from_json({"operation": "refine", "height": 1, "source": list(root), "extra": 1}))
    tests.append(lambda: _json_digit_map([[0, [1, 2, 3, 4]], [0, [1, 2, 3, 4]]]))
    rejected = 0
    for test in tests:
        try:
            test()
        except ValueError:
            rejected += 1
    require(rejected == len(tests), "malformed source or certificate accepted")
    return rejected


def self_check():
    fixed = _sibling("fixed_source_subclass_decomposition_obstruction.py", "_terminal_fixture_api")
    source = fixed.fixture(2)-{(3, 30)}
    family = []
    for height in range(2, 6):
        result = make_refinement(height, source)
        control = _source_control(height, source, result, fixed)
        require(control["all_six_pair_trees"], "sharp family lost admissibility")
        family.append(control)
        source = result["source"]
    root = {(1, 0), (2, 1), (3, 1), (2, 2), (4, 2), (3, 3), (4, 4)}
    refined = make_refinement(1, root)
    height_two = _source_control(1, root, refined, fixed)
    seed = fixed.fixture(2)-{(3, 30)}
    digits = {y: tuple((2*d+y) % 7 for d in range(5)) for _, y in seed}
    nonstationary = _source_control(2, seed, make_refinement(2, seed, digits), fixed)
    # Irregular five-tree: the selected second digits depend on its first digit.
    irregular_tree = {a+7*((a+2*b) % 7) for a in (0, 2, 3, 5, 6) for b in range(5)}
    irregular = {(1+y % 4, y) for y in irregular_tree}
    irregular_result = make_refinement(2, irregular,
                       {y: tuple((y+3*d) % 7 for d in range(5)) for y in irregular_tree})
    irregular_control = _source_control(2, irregular, irregular_result, fixed)
    # Certifying arbitrary target sources does not assume source tree premises.
    private_only = frozenset(refined["certificate"]["nu"])
    cert = refined["certificate"]
    private_audit = verify_common_law(2, private_only, cert)
    superset_audit = verify_common_law(2, private_only | {(4, 48)}, cert)
    require(private_audit["exact_moment"] == superset_audit["exact_moment"],
            "unused actual source points changed the common law")
    json_refine = from_json({"operation": "refine", "height": 1, "source": sorted(root)})
    json_law = from_json({"operation": "law", "height": 2, "source": sorted(private_only),
                         "tree": list(cert["tree"]),
                         "private_digits": [[y, list(ds)] for y, ds in cert["private_digits"].items()]})
    require(json_refine["verification"]["exact_moment"] == json_law["verification"]["exact_moment"],
            "JSON public interfaces disagree on the same law")
    return {"sharp_double_surplus_family": family, "height_two_type_c_refinement": height_two,
            "varying_terminal_digits": nonstationary, "irregular_five_tree": irregular_control,
            "arbitrary_source_private_only_points": len(private_only),
            "malformed_inputs_rejected": malformed_controls(root, refined),
            "limit": F(105, 32),
            "scope": "finite certificate controls; all-height identity is proved in the report"}


def main():
    if len(sys.argv) == 1:
        result = self_check()
    else:
        require(sys.argv[1:] == ["--stdin"], "usage: terminal_private_row_refinement.py [--stdin]")
        result = from_json(json.load(sys.stdin))
    print(json.dumps(_jsonable(result), indent=2))


if __name__ == "__main__":
    main()
