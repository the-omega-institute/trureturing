---
bibkey: gawronulas2022partitions
authors: Filip Gawron and Maciej Ulas
year: 2022
title: Signs behaviour of sums of weighted numbers of partitions
doi: 10.1007/s11139-022-00602-3
url: https://arxiv.org/abs/2202.05221v1
claim: "Conjecture 4.4 asserts eventual period-four signs for k ≤ m − 2 and eventual alternating signs for k ≥ m − 1 for the factorial part sets U_m."
strata_touched:
  - D5/S1/Recurrence/Partitions/GawronUlasFactorialSignConjecture
license: citation-only
triage: anchor
---

## Verified locator

DOI: 10.1007/s11139-022-00602-3

Source: https://arxiv.org/abs/2202.05221v1

The DOI identifies the publication in Ramanujan Journal 60 (2023), 571–584.
The statements quoted below are from the arXiv v1 text. The journal text has
not been verified; equality of its conjecture with v1 is ASSUMED-UNVERIFIED.

## Source definitions

Pages 1–2: “Let A ⊂ N+ be given and take n ∈ N. By an A-partition
λ = (λ_1, . . . , λ_k) with parts in A, of a non-negative integer n, we mean a
representation of n in the form n = λ_1 + . . . + λ_k, where λ_i ∈ A.
The representations of n differing only in order of the terms are counted as one.”
“c_A(i, n) is the number of A-partitions of n with exactly i parts.”

Page 2: “S_{A,k}(n) = Σ_{i=0}^{n} (−1)^i i^k c_A(i, n)”.
The empty partition of zero is included, and exponent-zero powers are one.

## Conjecture 4.4

Page 11: “Let m ∈ N≥2 and take U_m = {i! : i = 1, . . . , m}. Then, for each
k ∈ {0, . . . , m − 2}, (−1)^⌊(n+1)/2⌋ S_{U_m,k}(n) ≥ 0 for n ≫ 0, i.e., the
sequence of signs of the sequence (S_{U_m,k}(n))_{n∈N} is eventually periodic of
period 4. Moreover, if k ≥ m − 1 then (−1)^n S_{U_m,k}(n) ≥ 0 for n ≫ 0.”

The formal proposition records both displayed inequalities with separate
thresholds for each m and k. It does not strengthen nonnegative signs to
strict positivity or require the least eventual period to equal four.

## Scope of the refutation

The repository proof refutes the second assertion at m=3 and k=2 by an
unbounded family of even arguments. It does not refute the first assertion.
The broader literature search and priority of this refutation remain
ASSUMED-UNVERIFIED. No claim about a first published refutation is made.
