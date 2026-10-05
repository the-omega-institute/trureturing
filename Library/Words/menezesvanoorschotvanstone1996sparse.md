---
bibkey: menezesvanoorschotvanstone1996sparse
authors: Alfred J. Menezes, Paul C. van Oorschot, Scott A. Vanstone
year: 1996
title: "Handbook of Applied Cryptography"
doi: null
url: https://cacr.uwaterloo.ca/hac/about/chap14.pdf
claim: "Fact 14.124 gives uniqueness and minimum nonzero-digit count for sparse signed binary representations."
strata_touched:
  - D5/S1/Words/Palindromes/PeriodDoubling/CanonicalSignedDigits
  - D5/S1/Words/Palindromes/PeriodDoubling/NonadjacentSignedDigits
license: citation-only
triage: anchor
---

# Sparse signed binary representations

Definition 14.123, page 628: "A signed-digit representation of an integer e is said to be sparse if no two non-zero entries are adjacent in the representation."

Fact 14.124(i), page 628: "Every integer e has a unique sparse signed-digit representation."

Fact 14.124(ii), page 628: "A sparse signed-digit representation for e has the smallest number of non-zero entries among all signed-digit representations for e."

The Lean digits are integers in {−1, 0, 1}, ordered from the least significant position upward and evaluated by a fold with radix two. The uniqueness statement compares lists of the same length; this retains zero padding explicitly. The minimum-weight statement counts the nonzero digits. These are literature results, used to identify the arithmetic streams and their signed weights.
