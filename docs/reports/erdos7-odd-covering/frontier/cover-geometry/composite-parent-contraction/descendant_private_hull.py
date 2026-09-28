"""Exact control separating private-hull and descendant-assisted hull tests."""

import argparse
from functools import reduce
import json
from math import gcd, lcm
from pathlib import Path


def need(condition, message):
    if not condition:
        raise ValueError(message)


def owners(point, family):
    return [modulus for modulus, phase in family.items() if point % modulus == phase]


def divisors(number):
    return [divisor for divisor in range(1, number + 1) if number % divisor == 0]


def validate():
    old_pairs = (
        (3, 0), (5, 0), (7, 0), (11, 0), (15, 1),
        (21, 16), (35, 1), (55, 12), (77, 67), (385, 3),
    )
    old = dict(old_pairs)
    need(len(old) == len(old_pairs), "original numerical labels repeat")
    partial = {modulus: phase for modulus, phase in old.items() if modulus not in (35, 385)}
    partial[35] = 3
    new = dict(partial)
    new[105] = 71
    period = lcm(*old, *new)
    need(period == 1155, "wrong full period")
    need(all(modulus > 1 and modulus % 2 for modulus in old), "not odd nonunit")
    need(all(0 <= phase < modulus for modulus, phase in old.items()), "phase not reduced")
    need(all(old[prime] == 0 for prime in (3, 5, 7, 11)), "prime classes not normalized")
    need(
        all(divisor in old for modulus in old for divisor in divisors(modulus) if divisor > 1),
        "not divisor closed",
    )
    old_owners = [owners(point, old) for point in range(period)]
    partial_owners = [owners(point, partial) for point in range(period)]
    new_owners = [owners(point, new) for point in range(period)]
    private = {
        modulus: [point for point, labels in enumerate(old_owners) if labels == [modulus]]
        for modulus in old
    }
    need(all(private.values()), "not irredundant")
    need(
        all(
            not (set(range(a, period, m)) & set(range(b, period, n)))
            for m, a in old.items()
            for n, b in old.items()
            if m < n and n % m == 0
        ),
        "comparable classes meet",
    )
    hulls = {
        modulus: reduce(gcd, [period] + [point - points[0] for point in points])
        for modulus, points in private.items()
    }
    expected_hulls = {modulus: (105 if modulus == 35 else modulus) for modulus in old}
    need(hulls == expected_hulls, "unexpected complete private hull")
    old_test_violations = [
        (modulus, divisor)
        for modulus, hull in hulls.items()
        for divisor in divisors(hull)
        if 1 < divisor < modulus and divisor not in old
    ]
    need(not old_test_violations, "old PH5 already detects this control")
    need(105 not in old and 35 < 105 < 385 and 385 % 35 == 0, "wrong strict consumer")
    phase_group = [
        modulus for modulus, phase in old.items()
        if modulus > 35 and modulus % 35 == 0 and phase % 35 == 3
    ]
    need(phase_group == [385], "unexpected descendant phase group")
    partial_loss = [point for point in range(period) if old_owners[point] and not partial_owners[point]]
    need(partial_loss == private[35], "phase-group old-union loss is not exactly parent private region")
    loss = [point for point in range(period) if old_owners[point] and not new_owners[point]]
    need(not loss, "exchange loses old covered integer")
    need(len(old) == len(new) and sum(new) == sum(old) - 280, "wrong lexicographic improvement")
    need(not old_owners[2] and not new_owners[2], "missing noncover witness")
    need(all(point % 105 == 71 for point in private[35]), "wrong hull phase")
    need(
        not (set(range(old[35], period, 35)) & set(range(old[385], period, 385))),
        "removed classes overlap",
    )
    joint = [
        point for point in range(period)
        if old_owners[point] and set(old_owners[point]) <= {35, 385}
    ]
    need(set(joint) == set(private[35]) | set(private[385]), "wrong joint liability reduction")
    old_covered = sum(bool(labels) for labels in old_owners)
    new_covered = sum(bool(labels) for labels in new_owners)
    need((old_covered, new_covered, len(joint)) == (793, 811, 12), "unexpected exact counts")
    return {
        "result": "PASS",
        "period": period,
        "old_classes": sorted(old.items()),
        "new_classes": sorted(new.items()),
        "private_counts": {str(modulus): len(points) for modulus, points in private.items()},
        "private_witnesses": {str(modulus): points[0] for modulus, points in private.items()},
        "complete_private_hulls": hulls,
        "old_PH5_violations": old_test_violations,
        "strict_new_obligation": {
            "parent": 35, "descendant": 385, "unused_hull_divisor": 105, "hull_phase": 71,
        },
        "old_modulus_sum": sum(old),
        "new_modulus_sum": sum(new),
        "old_covered": old_covered,
        "new_covered": new_covered,
        "lost_points": loss,
        "joint_liability_count": len(joint),
        "hole": 2,
        "scope": (
            "Actual distinct odd irredundant divisor-closed noncover passes every old PH5 test, "
            "but a descendant-assisted two-label replacement preserves its entire old union "
            "and lowers modulus sum. Not an extremal whole cover."
        ),
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", required=True, type=Path)
    arguments = parser.parse_args()
    result = validate()
    arguments.output.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    summary_keys = (
        "result", "period", "old_modulus_sum", "new_modulus_sum",
        "old_covered", "new_covered", "old_PH5_violations",
    )
    print(json.dumps({key: result[key] for key in summary_keys}, sort_keys=True))


if __name__ == "__main__":
    main()
