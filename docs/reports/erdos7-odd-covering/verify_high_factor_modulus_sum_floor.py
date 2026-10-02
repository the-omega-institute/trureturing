"""Exact arithmetic check for the Section 187 modulus-sum floor.

The script checks only the finite integer minimizations used after the
HF1/HF2/EB1/EB2/HF9 and Simpson hypotheses have been established.  It does
not check those covering-system inputs.
"""

from __future__ import annotations


def main() -> None:
    full_29_floor = 29 * sum(range(1, 58, 2))
    non_29_floor = sum(range(3, 192, 2)) - (29 + 87 + 145)
    assert full_29_floor == 24389
    assert non_29_floor == 8954
    assert full_29_floor + non_29_floor == 33343

    smallest_four_repair = (
        non_29_floor
        - (187 + 189 + 191)
        + (231 + 385 + 1155)
    )
    assert smallest_four_repair == 10158
    assert full_29_floor + smallest_four_repair == 34547

    other_four_repair = (
        non_29_floor
        - (187 + 189 + 191)
        + (273 + 455 + 1365)
    )
    assert other_four_repair == 10480
    assert full_29_floor + other_four_repair == 34869

    containing_29_repair = full_29_floor - 1653 + 3045
    assert containing_29_repair == 25781
    assert containing_29_repair + non_29_floor == 34735

    assert 29**4 > 34547
    print("Section 187 exact arithmetic checks passed: floor=34547")


if __name__ == "__main__":
    main()
