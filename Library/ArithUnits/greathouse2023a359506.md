---
bibkey: greathouse2023a359506
authors: Peter Kagey; Charles R. Greathouse IV
year: 2023
title: "OEIS A359506: least enders of increasing zero-XOR sequences"
doi: null
url: https://oeis.org/A359506/internal
claim: "Conjecture: a(n) <= 5(n+1)/3."
strata_touched:
  - D5/S3/Arith/Additive/GreathouseA359506XorBound
license: citation-only
triage: anchor
---

## Verified locator

Source: https://oeis.org/A359506/internal (revision 41; unpaginated).

Linked note: https://oeis.org/A359506/a359506.pdf, Peter Kagey,
January 12, 2023. The OEIS entry has no arXiv identifier or DOI.

## Source statements

OEIS A359506, revision 41, NAME:

> a(n) is the least integer m such that there exists a strictly increasing integer sequence n = b_1 < b_2 < ... < b_t = m with the property that b_1 XOR b_2 XOR ... XOR b_t = 0.

COMMENTS:

> XOR is the bitwise XOR function, A003987.

FORMULA:

> For n > 1, a(n) >= n + 3. a(4n) = 4n + 3 for n > 0. Conjecture: a(n) <= 5(n+1)/3. - Charles R Greathouse IV, Jan 12 2023

Kagey's linked note defines a finite sequence of nonnegative integers with
zero XOR and proves a bijection and inverse statement. The quantitative
five-thirds bound is the conjecture in the OEIS entry.

## Mathematical scope

Natural numbers include zero. A finite list records the strictly increasing
sequence. It is nonempty, with `bs.headD 0 = n` and `bs.getLastD 0 = m`.
Its XOR is `List.foldr (fun a b => a ^^^ b) 0 bs`.
The minimum condition quantifies over every natural ender. The integer inequality
`3 * m ≤ 5 * (n + 1)` expresses the rational bound without floor division.

The exact minimum families are `2^s * (2*k+1) - 1` with `k ≥ 1`, whose ender is
`2^s * (2*k+3)`, and `2^(s+1) - 1`, whose ender is `3 * 2^s`.
The first family with `k = 1` attains the coefficient five-thirds.
Separate statements for A359507 and A359508 remain outside this result.

## Experimental reference

The preregistration cites the independent integer checker in
[trureturing-experiments](https://github.com/the-omega-institute/trureturing-experiments/tree/d94908eea9683284b6755fa762e2d2b3a2a9e450/docs/reports/greathouse-a359506-xor-bound).
Its `check.py` SHA-256 is
`cb0fbf202b9124fa9dbd6d35fa82b84a30d60466eeebbed2baff96e6689cb56c`.
The recorded command `python3 check.py` exits 0 and ends with `ALL_CHECKS_OK`.
It checks the published prefix through 10, exact minima and the bound through
512, and the sharp family for exponents through 12. These are finite checks.

## Literature boundary

[Preregistration #23097](https://github.com/the-omega-institute/trureturing/issues/23097)
records the source revisions and literature screen. No settlement was located
in that screen. Literature completeness is ASSUMED-UNVERIFIED.
