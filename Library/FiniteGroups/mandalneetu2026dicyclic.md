---
bibkey: mandalneetu2026dicyclic
authors: Sagar Mandal and Neetu
year: 2026
title: Exact and Asymptotic Counts of MSTD, MDTS, and Balanced Sets in Dicyclic Groups
doi: 10.48550/arXiv.2602.09073
url: https://arxiv.org/abs/2602.09073v1
claim: "Question 6.3 asks whether S, D and B are all even for n >= 3 and 2 <= m <= 2n."
strata_touched:
  - D5/S3/FiniteGroups/SubsetProducts/DicyclicSubsetParityRefutation
license: citation-only
triage: anchor
---

# Dicyclic subset parity

Sagar Mandal and Neetu, *Exact and Asymptotic Counts of MSTD, MDTS, and
Balanced Sets in Dicyclic Groups*, arXiv:2602.09073v1. The versioned
[abstract](https://arxiv.org/abs/2602.09073v1) identifies the authors and title;
the DOI is [10.48550/arXiv.2602.09073](https://doi.org/10.48550/arXiv.2602.09073).

## Source and interpretation

The [v1 source](https://arxiv.org/src/2602.09073v1), `Main.tex` line 792,
prints Question 6.3. With mathematical macros expanded, it asks:

> Is it true that S_Dic(4n)(m), D_Dic(4n)(m) and B_Dic(4n)(m) are even
> integers for any positive integers n,m with n >= 3 and 2 <= m <= 2n?

`Main.tex` has SHA-256
`7ed61ecf73935d71b750c85a2f03f635b3669ae370d87e41f16c653c0e48f959`.
Line 120 defines the sumset by products `xy` and the difference set by
right quotients `xy^(-1)`. Line 121 presents the order-`4n` dicyclic group
by `a^(2n)=1`, `a^n=b^2` and `b^(-1)ab=a^(-1)`.
Mathlib's `QuaternionGroup n` uses `x` for `b` and the same presentation.
Its `QuaternionGroup.card` theorem supplies the order.

Lines 183–187 define S, D and B as the numbers of all subsets of the stated
cardinality with product cardinality respectively larger, smaller and equal
to right quotient cardinality. Lines 189–193 separately introduce
type-restricted counts; those are not the counts in Question 6.3. The
question ranges over both parities of n.

## Refutation and boundaries

The corresponding Lean claim uses the actual `QuaternionGroup n`, every
distinct m-element subset, duplicate-free product and right quotient sets,
and a conjunction of the three natural-number parity assertions.
The result is its literal negation. Trichotomy partitions all m-subsets into
the three classes. At n = 3 and m = 4 their total is `choose(12,4)=495`.
Three even counts cannot have this odd sum.

The argument refutes the joint universal assertion without identifying which
class has odd cardinality. It does not change the preceding observations
for m = 2,3 or resolve other questions in the paper. The conclusion concerns
the cited v1 wording. Journal-version equivalence, later corrections and
worldwide first-resolution priority are not established here. The question
is literature-attested; this formal refutation is a repository derivation,
not a result attributed to the source authors.

## Verified locator

DOI: [10.48550/arXiv.2602.09073](https://doi.org/10.48550/arXiv.2602.09073).
Versioned URL: https://arxiv.org/abs/2602.09073v1.
