#!/usr/bin/env python3
"""Verify the finite summatory-totient base used in the accompanying proof."""

from math import gcd


FIRST_M = 2
LAST_M = 34
EXPECTED_FINAL_SUM = 360
EXPECTED_ZERO_SLACKS = [2, 4, 6]


def totient(n: int) -> int:
    if n < 1:
        raise ValueError(f"totient input must be positive, got {n}")
    return sum(1 for k in range(1, n + 1) if gcd(k, n) == 1)


def require(condition: bool, message: str) -> None:
    if not condition:
        raise RuntimeError(message)


def main() -> int:
    # This convention is used in S(m) = sum_{j=1}^m phi(j).
    require(totient(1) == 1, "phi(1) must equal 1")

    summatory_totient = totient(1)
    zero_slacks = []
    for m in range(FIRST_M, LAST_M + 1):
        summatory_totient += totient(m)
        slack = 4 * summatory_totient - m * (m + 2)
        print(f"m={m:2d} S(m)={summatory_totient:3d} slack={slack:3d}")
        require(slack >= 0, f"totient inequality failed at m={m}: slack={slack}")
        if slack == 0:
            zero_slacks.append(m)

    require(
        summatory_totient == EXPECTED_FINAL_SUM,
        f"unexpected S({LAST_M}): {summatory_totient} != {EXPECTED_FINAL_SUM}",
    )
    require(
        zero_slacks == EXPECTED_ZERO_SLACKS,
        f"unexpected zero-slack indices: {zero_slacks} != {EXPECTED_ZERO_SLACKS}",
    )
    print(
        f"verified m={FIRST_M}..{LAST_M}; "
        f"S({LAST_M})={summatory_totient}; zero slacks={zero_slacks}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
