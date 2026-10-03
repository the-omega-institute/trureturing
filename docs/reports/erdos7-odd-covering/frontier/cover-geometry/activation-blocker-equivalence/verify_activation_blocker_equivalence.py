#!/usr/bin/env python3
"""Finite audit of the activation/blocker reformulation in Report 385 §243.

For a finite atom universe V and each label i, an option family O_i is a
nonempty finite family of activation sets T(i, b).  The direct formulation
accepts U when one option for every label is contained in U.  The dual
formulation first enumerates inclusion-minimal blockers R (sets meeting every
option of one label), then accepts U when it meets every such blocker.

This program exhausts bounded option-family catalogues for universes of size
0 through 5, compares the two feasible-U sets, and checks several positive
integer weight vectors.  It is a finite consistency audit only.  It does not
prove the unrestricted activation lower bound, the EB1 replacement statement,
or Erdős #7.
"""

from __future__ import annotations

import argparse
import itertools
import json
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable, Sequence


DEFAULT_OUTPUT = Path(__file__).with_suffix(".json")


@dataclass(frozen=True)
class FamilyRecord:
    options: tuple[int, ...]
    direct_bits: int
    blockers: tuple[int, ...]
    blocker_bits: int


def bit_count_mask(mask: int) -> int:
    return mask.bit_count()


def all_subsets(universe_size: int) -> range:
    return range(1 << universe_size)


def mask_to_elements(mask: int, universe_size: int) -> list[int]:
    return [i for i in range(universe_size) if mask & (1 << i)]


def mask_bits(masks: Iterable[int]) -> int:
    result = 0
    for mask in masks:
        result |= 1 << mask
    return result


def minimal_blockers(options: Sequence[int], universe_size: int) -> tuple[int, ...]:
    """Return inclusion-minimal subsets meeting every option."""

    candidates = tuple(
        r
        for r in all_subsets(universe_size)
        if all((r & option) != 0 for option in options)
    )
    candidate_set = set(candidates)
    minimal = tuple(
        r
        for r in candidates
        if all(
            not (s != r and (s & r) == s)
            for s in candidate_set
        )
    )
    return minimal


def family_record(options: Sequence[int], universe_size: int) -> FamilyRecord:
    options_tuple = tuple(options)
    direct = tuple(
        u
        for u in all_subsets(universe_size)
        if any((option & ~u) == 0 for option in options_tuple)
    )
    blockers = minimal_blockers(options_tuple, universe_size)
    hit = tuple(
        u
        for u in all_subsets(universe_size)
        if all((u & blocker) != 0 for blocker in blockers)
    )
    return FamilyRecord(
        options=options_tuple,
        direct_bits=mask_bits(direct),
        blockers=blockers,
        blocker_bits=mask_bits(hit),
    )


def family_catalogue(universe_size: int) -> tuple[FamilyRecord, ...]:
    """Generate a finite catalogue of nonempty option families.

    For n<=3 all nonempty families of subsets are included.  For n=4,5 we
    include every family with one or two options; this keeps the audit fully
    exhaustive for the stated bounded catalogue while avoiding an enormous
    2^(2^n) catalogue.  The output records this scope explicitly.
    """

    options = tuple(all_subsets(universe_size))
    if universe_size <= 3:
        max_options = len(options)
    else:
        max_options = 2
    records: list[FamilyRecord] = []
    for option_count in range(1, max_options + 1):
        for choice in itertools.combinations(options, option_count):
            records.append(family_record(choice, universe_size))
    return tuple(records)


def weight_vectors(universe_size: int) -> tuple[tuple[int, ...], ...]:
    if universe_size == 0:
        return ((),)
    ascending = tuple(range(1, universe_size + 1))
    descending = tuple(reversed(ascending))
    periodic = tuple(2 + (i % 3) for i in range(universe_size))
    prime_prefix = (2, 3, 5, 7, 11)[:universe_size]
    return (tuple(1 for _ in ascending), ascending, descending, periodic, prime_prefix)


def weighted_min(bits: int, weights: Sequence[int], universe_size: int) -> int:
    best: int | None = None
    remaining = bits
    while remaining:
        low = remaining & -remaining
        subset = low.bit_length() - 1
        value = sum(
            weights[i]
            for i in range(universe_size)
            if subset & (1 << i)
        )
        if best is None or value < best:
            best = value
        remaining ^= low
    if best is None:
        raise AssertionError("every finite option family has a feasible U")
    return best


def combined_bits(records: Sequence[FamilyRecord], attr: str) -> int:
    value = (1 << (1 << len(records[0].options).bit_length() - 1)) - 1
    # The line above is intentionally not used: option masks do not encode n.
    # Callers replace the universe-wide all-mask below.
    del value
    raise AssertionError("combined_bits requires universe_size")


def combined_feasible_bits(
    records: Sequence[FamilyRecord], universe_size: int, attribute: str
) -> int:
    all_u = (1 << (1 << universe_size)) - 1
    value = all_u
    for record in records:
        value &= getattr(record, attribute)
    return value


def family_to_json(record: FamilyRecord, universe_size: int) -> dict[str, object]:
    return {
        "options": [mask_to_elements(option, universe_size) for option in record.options],
        "blockers": [mask_to_elements(blocker, universe_size) for blocker in record.blockers],
        "direct_feasible_U": [
            mask_to_elements(u, universe_size)
            for u in all_subsets(universe_size)
            if record.direct_bits & (1 << u)
        ],
    }


def sample_cases() -> list[dict[str, object]]:
    cases = [
        (3, ((1,), (2,))),
        (3, ((1, 2),)),
        (3, ((1, 2), (2, 4))),
        (5, ((1, 3, 16), (2, 4, 8))),
    ]
    output = []
    for n, raw_options in cases:
        records = [family_record(tuple(raw_options_i), n) for raw_options_i in raw_options]
        direct = combined_feasible_bits(records, n, "direct_bits")
        blocked = combined_feasible_bits(records, n, "blocker_bits")
        output.append(
            {
                "universe_size": n,
                "labels": [family_to_json(record, n) for record in records],
                "direct_feasible_U": [
                    mask_to_elements(u, n) for u in all_subsets(n) if direct & (1 << u)
                ],
                "blocker_hitting_U": [
                    mask_to_elements(u, n) for u in all_subsets(n) if blocked & (1 << u)
                ],
                "minimum_weight_by_vector": {
                    ",".join(map(str, weights)): weighted_min(direct, weights, n)
                    for weights in weight_vectors(n)
                },
            }
        )
    return output


def audit() -> dict[str, object]:
    failures: list[dict[str, object]] = []
    summary: list[dict[str, object]] = []
    total_instances = 0
    total_weight_checks = 0
    total_family_records = 0
    total_blocker_records = 0

    for n in range(6):
        catalogue = family_catalogue(n)
        total_family_records += len(catalogue)
        max_labels = 3 if n <= 2 else 2
        instances = 0
        weight_checks = 0
        for label_count in range(1, max_labels + 1):
            for indices in itertools.combinations_with_replacement(
                range(len(catalogue)), label_count
            ):
                records = tuple(catalogue[index] for index in indices)
                instances += 1
                total_instances += 1
                total_blocker_records += sum(len(record.blockers) for record in records)
                direct = combined_feasible_bits(records, n, "direct_bits")
                blocked = combined_feasible_bits(records, n, "blocker_bits")
                if direct != blocked:
                    failures.append(
                        {
                            "universe_size": n,
                            "label_indices": list(indices),
                            "direct_U": [
                                mask_to_elements(u, n)
                                for u in all_subsets(n)
                                if direct & (1 << u)
                            ],
                            "blocker_U": [
                                mask_to_elements(u, n)
                                for u in all_subsets(n)
                                if blocked & (1 << u)
                            ],
                        }
                    )
                    if len(failures) >= 10:
                        break
                for weights in weight_vectors(n):
                    direct_min = weighted_min(direct, weights, n)
                    blocker_min = weighted_min(blocked, weights, n)
                    weight_checks += 1
                    total_weight_checks += 1
                    if direct_min != blocker_min:
                        failures.append(
                            {
                                "universe_size": n,
                                "label_indices": list(indices),
                                "weights": list(weights),
                                "direct_min": direct_min,
                                "blocker_min": blocker_min,
                            }
                        )
                        if len(failures) >= 10:
                            break
                if len(failures) >= 10:
                    break
            if len(failures) >= 10:
                break
        summary.append(
            {
                "universe_size": n,
                "family_catalogue_size": len(catalogue),
                "max_labels": max_labels,
                "instances": instances,
                "weight_vectors": [list(weights) for weights in weight_vectors(n)],
                "weight_checks": weight_checks,
            }
        )
        if len(failures) >= 10:
            break

    return {
        "schema": "activation_blocker_equivalence_v1",
        "status": "PASS" if not failures else "FAIL",
        "scope": {
            "universe_sizes": list(range(6)),
            "catalogue": {
                "n_le_3": "all nonempty families of subsets of V",
                "n_4_or_5": "all nonempty families with at most two options",
            },
            "label_multisets": "one through three labels for n<=2; one through two for n>=3",
            "weights": "five positive integer vectors per universe",
            "meaning": "finite exhaustive audit of the declared bounded catalogue; not a global proof",
        },
        "summary": summary,
        "totals": {
            "instances": total_instances,
            "weight_checks": total_weight_checks,
            "family_records": total_family_records,
            "minimal_blocker_records": total_blocker_records,
            "failures": failures,
        },
        "sample_cases": sample_cases(),
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    args = parser.parse_args()
    result = audit()
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, ensure_ascii=False, indent=2, sort_keys=True) + "\n")
    print(json.dumps({
        "status": result["status"],
        "output": str(args.output),
        "instances": result["totals"]["instances"],
        "weight_checks": result["totals"]["weight_checks"],
        "failures": len(result["totals"]["failures"]),
    }, ensure_ascii=False, sort_keys=True))
    if result["status"] != "PASS":
        raise SystemExit(1)


if __name__ == "__main__":
    main()
