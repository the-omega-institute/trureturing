#!/usr/bin/env python3
"""Reconstruct all actual315 carriers modulo common CRT root symmetries.

Uses only Python's standard library. Its source geometry is the adjacent
canonical actual_deletion_profile_certificate.json (or --source-certificate).
The default action checks the adjacent seven_digit_classification_certificate.json.
--write PATH creates the deterministic result certificate after reconstruction.
No optimizer, scratch module, policy cache, or floating arithmetic is used.
"""

# Pinned local IO preserves complete certificate hashes after semantic splitting.
import sys as _certificate_sys
from pathlib import Path as _CertificatePath
from hashlib import sha256 as _certificate_sha256
_certificate_root = _CertificatePath(__file__).resolve().parent
_certificate_io_path = _certificate_root / 'certificate_io.py'
if _certificate_sha256(_certificate_io_path.read_bytes()).hexdigest() != '3bab29ebc23defcae75e775fb182d2aa0d83d71ba1ae3b168ed8e9bc7a8c1fe2':
    raise ValueError('certificate IO source SHA-256 mismatch')
_certificate_sys.path.insert(0, str(_certificate_root))
from certificate_io import read_artifact_bytes, read_artifact_text, write_certificate_text
from collections import Counter
from hashlib import sha256
from itertools import permutations, product
from math import factorial, prod
from pathlib import Path
import argparse
import json

MODULI = (3, 5, 9, 15, 45)
CATEGORIES = ("same_other_column", "other_same_column", "other_other_column")
SCHEMA = "erdos7-seven-digit-carrier-classification-v1"
SOURCE_SCHEMA = "erdos7-common-fibre-head-experiment-v1"
SCOPE = ("Complete actual low315 carriers on the six canonical old45 geometries; "
         "common nonzero7-root permutations and old3/5 carrier stabilizers; "
         "no universal moment target or covering-system resolution")


def require(condition, message):
    if not condition:
        raise ArithmeticError(message)


def digest(value):
    data = json.dumps(value, sort_keys=True, separators=(",", ":")).encode()
    return sha256(data).hexdigest()


def integer_list(value, name):
    require(type(value) is list and all(type(v) is int for v in value),
            "integer list: " + name)


def canonical_classes(root, category):
    other = 3 - root
    row, column = {"same_other_column": (root, 2),
                   "other_same_column": (other, 1),
                   "other_other_column": (other, 2)}[category]
    a15 = next(a for a in range(15) if a % 3 == root and a % 5 == 1)
    a45 = next(a for a in range(45) if a % 9 == row and a % 5 == column)
    return [[3, 0], [9, 4], [5, 0], [15, a15], [45, a45]]


def read_geometries(path):
    source = json.loads(read_artifact_text(path))
    require(type(source) is dict and source.get("schema") == SOURCE_SCHEMA,
            "canonical source schema")
    cases = source.get("cases")
    require(type(cases) is list and len(cases) == 6, "six source geometries")
    expected_names = [f"root{r}_{c}" for r, c in product((1, 2), CATEGORIES)]
    require(all(type(row) is dict for row in cases), "source geometry objects")
    require([row.get("shape") for row in cases] == expected_names,
            "pinned six-shape domain and order")
    result = []
    for (root, category), row in zip(product((1, 2), CATEGORIES), cases):
        family = row.get("old_classes")
        require(type(family) is list and len(family) == 5,
                "five source old classes")
        for pair in family:
            integer_list(pair, "old class")
            require(len(pair) == 2, "modulus/residue pair")
        require(family == canonical_classes(root, category), "canonical old family")
        points = row.get("old_points")
        integer_list(points, "old points")
        actual = [x for x in range(45)
                  if all(x % d != a for d, a in family)]
        require(points == actual, "actual old survivor complement")
        geometry = row.get("geometry")
        require(type(geometry) is dict, "source geometry counts")
        for name in ("vectors", "digit_union_states"):
            require(type(geometry.get(name)) is int and geometry[name] > 0,
                    "integer source count: " + name)
        widths = geometry.get("independent_state_widths")
        integer_list(widths, "source successive-label counts")
        require(len(widths) == 6, "source successive-label indexing")
        stamp = geometry.get("ordered_vectors_sha256")
        require(type(stamp) is str and len(stamp) == 64
                and all(c in "0123456789abcdef" for c in stamp), "source b digest")
        result.append({"shape": row["shape"], "old_classes": family,
                       "old_points": points, "vectors": geometry["vectors"],
                       "digit_union_states": geometry["digit_union_states"],
                       "independent_state_widths": widths,
                       "ordered_vectors_sha256": stamp})
    return result


def equality_patterns(length):
    def walk(prefix):
        if len(prefix) == length:
            yield tuple(prefix)
            return
        for value in range(max(prefix) + 2):
            yield from walk(prefix + [value])
    yield from walk([0])


def check_digit_partitions():
    patterns = list(equality_patterns(6))
    require(len(patterns) == len(set(patterns)) == 203, "Bell6 patterns")
    normalized = Counter()
    for tail in product(range(7), repeat=5):
        labels = {}
        pattern = []
        for value in (0,) + tail:
            if value not in labels:
                labels[value] = len(labels)
            pattern.append(labels[value])
        normalized[tuple(pattern)] += 1
    require(set(normalized) == set(patterns), "all concrete digit assignments")
    for pattern in patterns:
        blocks = max(pattern) + 1
        require(normalized[pattern] == factorial(6) // factorial(7 - blocks),
                "exact labelled-digit orbit size")
    counts = Counter(max(p) + 1 for p in patterns)
    require([counts[k] for k in range(1, 7)] == [1, 31, 90, 65, 15, 1],
            "six-label Stirling counts")
    require(sum(normalized.values()) == 7**5, "16807 concrete digit tuples")
    require(len(set(equality_patterns(5))) == 52, "Bell5 optional construction")
    return {"patterns": 203, "patterns_by_blocks": {str(k): counts[k] for k in counts},
            "concrete_digit_tuples": 7**5, "optional_nonzero_patterns": 52,
            "patterns_sha256": digest(sorted(patterns))}


def digit_union_states(points):
    cylinders = [sorted({sum(1 << i for i, x in enumerate(points) if x % d == a)
                         for a in range(d)}) for d in MODULI]
    require(all(0 in choices for choices in cylinders), "empty old-cylinder option")
    states = {()}
    widths = [1]
    for choices in cylinders:
        following = set()
        for unions in states:
            for cylinder in choices:
                if cylinder == 0:
                    following.add(unions)
                    continue
                following.add(tuple(sorted(unions + (cylinder,))))
                for j, old in enumerate(unions):
                    following.add(tuple(sorted(unions[:j] + (old | cylinder,)
                                               + unions[j + 1:])))
        states = following
        widths.append(len(states))
    require(all(len(s) <= 5 and all(0 < u < 1 << len(points) for u in s)
                for s in states), "at most five nonempty digit masks")
    return states, cylinders, widths


def old_maps(points):
    lookup = {(x % 9, x % 5): i for i, x in enumerate(points)}
    families = [{tuple(i for i, x in enumerate(points) if x % d == a)
                 for a in range(d)} for d in MODULI]
    result = []
    for short, long, columns in product(permutations((1, 7)),
                                        permutations((2, 5, 8)),
                                        permutations((1, 2, 3, 4))):
        rows = dict(zip((1, 7, 2, 5, 8), short + long))
        cols = dict(zip((1, 2, 3, 4), columns))
        image = tuple(lookup.get((rows[x % 9], cols[x % 5])) for x in points)
        if any(j is None for j in image):
            continue
        require(len(set(image)) == len(points), "old coordinate permutation")
        for family in families:
            require({tuple(sorted(image[i] for i in block)) for block in family}
                    == family, "every cofactor cylinder family is preserved")
        result.append(image)
    group = set(result)
    require(len(group) == len(result), "distinct old coordinate maps")
    require(tuple(range(len(points))) in group, "old group identity")
    require(all(tuple(p[q[i]] for i in range(len(points))) in group
                for p in result for q in result), "old stabilizer group closure")
    return result


def image_mask(mask, permutation):
    result = 0
    while mask:
        bit = mask & -mask
        result |= 1 << permutation[bit.bit_length() - 1]
        mask ^= bit
    return result


def deletion_vector(unions, size):
    return tuple(sum((mask >> i) & 1 for mask in unions) for i in range(size))


def classify(geometry):
    points = geometry["old_points"]
    size = len(points)
    states, cylinders, widths = digit_union_states(points)
    require(len(states) == geometry["digit_union_states"], "existing carrier count")
    require(widths == geometry["independent_state_widths"], "existing recursive widths")
    multiplicity = Counter(deletion_vector(state, size) for state in states)
    vectors = sorted(multiplicity, key=lambda b: (sum(b), b))
    require(len(vectors) == geometry["vectors"], "existing b count")
    require(digest(vectors) == geometry["ordered_vectors_sha256"], "existing exact b set")
    maps = old_maps(points)
    used_masks = {mask for state in states for mask in state}
    transformed = [{u: image_mask(u, p) for u in used_masks} for p in maps]
    remaining = states.copy()
    representatives = set()
    orbit_sizes = Counter()
    while remaining:
        state = remaining.pop()
        images = {tuple(sorted(action[u] for u in state)) for action in transformed}
        require(images <= states, "carrier family stable under old maps")
        remaining.difference_update(images)
        representative = min(images)
        require(representative not in representatives, "disjoint carrier orbits")
        representatives.add(representative)
        orbit_sizes[len(images)] += 1
    require(sum(k * v for k, v in orbit_sizes.items()) == len(states),
            "complete carrier orbit accounting")
    remaining_b = set(vectors)
    b_orbits = 0
    while remaining_b:
        vector = remaining_b.pop()
        images = {tuple(vector[p[i]] for i in range(size)) for p in maps}
        require(images <= multiplicity.keys(), "b family stable under old maps")
        remaining_b.difference_update(images)
        b_orbits += 1
    result = {
        "shape": geometry["shape"], "old_points": size,
        "effective_cylinder_counts_including_empty": [len(c) for c in cylinders],
        "labelled_Bell6_patterns": 203 * prod(map(len, cylinders)),
        "optional_Bell5_patterns": 52 * prod(map(len, cylinders)),
        "successive_label_widths": widths, "deletion_vectors": len(vectors),
        "digit_union_states": len(states), "old_carrier_automorphisms": len(maps),
        "digit_union_orbits": len(representatives), "deletion_vector_orbits": b_orbits,
        "union_orbit_sizes": {str(k): v for k, v in sorted(orbit_sizes.items())},
        "union_states_sha256": digest(sorted(states)),
        "union_orbits_sha256": digest(sorted(representatives)),
        "deletion_vectors_sha256": digest(vectors),
        "old_maps_sha256": digest(sorted(maps)),
        "maximum_union_states_per_vector": max(multiplicity.values()),
    }
    collision = None
    if geometry["shape"] == "root1_same_other_column":
        first = (66576, 103278)
        second = (8, 65828, 104018)
        require(first in states and second in states, "attainable collision carriers")
        require(deletion_vector(first, size) == deletion_vector(second, size),
                "same b for two distinct carrier orbits")
        require(len(first) != len(second), "root-map invariant distinguishes collision")
        collision = {"shape": geometry["shape"], "union_masks_a": list(first),
                     "union_masks_b": list(second),
                     "b": list(deletion_vector(first, size))}
    return result, collision


def reconstruct(source_path):
    geometries = read_geometries(source_path)
    digit_data = check_digit_partitions()
    rows = []
    collision = None
    for geometry in geometries:
        row, witness = classify(geometry)
        rows.append(row)
        if witness is not None:
            collision = witness
    keys = ("deletion_vectors", "digit_union_states", "digit_union_orbits",
            "deletion_vector_orbits", "labelled_Bell6_patterns", "optional_Bell5_patterns")
    totals = {key: sum(row[key] for row in rows) for key in keys}
    require(totals["deletion_vectors"] == 161375
            and totals["digit_union_states"] == 965595
            and totals["digit_union_orbits"] == 170569
            and totals["deletion_vector_orbits"] == 29241, "pinned classification totals")
    require(collision is not None, "loss-of-information witness")
    return {"schema": SCHEMA, "scope": SCOPE,
            "canonical_source_schema": SOURCE_SCHEMA,
            "source_geometry_sha256": digest(geometries), "digit_classification": digit_data,
            "full_old_residue_choices_per_shape": prod(MODULI),
            "full_labelled_digit_orbits_per_shape": 203 * prod(MODULI),
            "cases": rows, "totals": totals, "deletion_vector_collision": collision}


def check_json_types(value):
    require(type(value) in (dict, list, str, int), "result JSON must contain no floats/bools")
    if type(value) is dict:
        require(all(type(k) is str for k in value), "string result keys")
        for item in value.values():
            check_json_types(item)
    elif type(value) is list:
        for item in value:
            check_json_types(item)


def main():
    base = Path(__file__).resolve().parent
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source-certificate", type=Path,
                        default=base / 'certificates/actual_deletion_profile_certificate.json')
    parser.add_argument("--check", type=Path,
                        default=base / 'certificates/seven_digit_classification_certificate.json')
    parser.add_argument("--write", type=Path)
    args = parser.parse_args()
    expected = None
    if args.write is None:
        expected = json.loads(read_artifact_text(args.check))
        check_json_types(expected)
        require(type(expected) is dict and expected.get("schema") == SCHEMA,
                "classification result schema")
    result = reconstruct(args.source_certificate)
    if args.write is not None:
        write_certificate_text(args.write, json.dumps(result, indent=2) + "\n")
    else:
        require(expected == result, "exact deterministic classification certificate")
    print(json.dumps({"verified": True, "digit_patterns": 203, **result["totals"]}, indent=2))


if __name__ == "__main__":
    main()
