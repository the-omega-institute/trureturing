---
bibkey: gallardo2025collatzlength
authors: Luis H. Gallardo and Olivier Rahavandrainy
year: 2025
title: A variant of Collatz's Conjecture over Binary Polynomials
doi: 10.48550/arXiv.2510.07530
url: https://arxiv.org/abs/2510.07530v1
claim: "However, several computations suggest that here also r_A is bounded by a polynomial in deg(A) (see Section 3)."
strata_touched:
  - D5/S1/Recurrence/GallardoRahavandrainyCollatzLengthBound
license: citation-only
triage: anchor
---

# Polynomial bounds for binary-polynomial Collatz length

## Verified locator

DOI: 10.48550/arXiv.2510.07530

Source: https://arxiv.org/abs/2510.07530v1

The journal version is Revista de la Unión Matemática Argentina 69(1),
295–302, DOI 10.33044/revuma.5555.

## Source statements

The transformations in §1 (p. 4) include “A₀ = A” and
“A₂ₖ = 1 + M₁A₂ₖ₋₁”, where M₁ = x² + x + 1.
The odd polynomial A₁ satisfies “A₀ = x^{a₀}(x + 1)^{b₀}A₁”.
Subsequent odd terms satisfy “A₂ₖ₊₁ = A₂ₖ/(x^{a₂ₖ}(x + 1)^{b₂ₖ})”.

Theorem 1.2 (p. 4): “Let A be a nonzero binary polynomial. Then the sequences
of polynomials obtained from Collatz transformations are of finite length r_A.”
It gives “where m ∈ ℕ* and r_A = m + 1 ≤ 2^{deg(A)−1}.”
The terminal pair is x(x+1), 1 from index m onward.

The prediction in §1 (p. 5) reads: “However, several computations suggest
that here also r_A is bounded by a polynomial in deg(A) (see Section 3).”

## Encoding and result

The coefficient ring is ZMod 2. The existing declarations M, oddPart and
oddSeq give the multiplier, removal of linear factors and odd-indexed
sequence, with oddSeq A k = A₂ₖ₊₁. The even terms retain A at k=0 and
1+M*oddSeq A (k-1) at positive k. The length is one plus the least positive
index from which the terminal pair persists.

For nonzero A the repository theorem proves r_A ≤ 2 + ⌊natDegree(A)²/4⌋.
On each constant-degree plateau, the smaller root multiplicity at 0 and 1
of F+1 decreases by one; the sum of the degree budgets gives the quadratic
bound. Exact plateau duration, sharpness examples and a formal equality
for the source's g(n) are not asserted by this module.

Prior-art completeness remains ASSUMED-UNVERIFIED; the literature screen is
in https://github.com/the-omega-institute/trureturing/issues/20129.

The corroborating experiment is in
https://github.com/the-omega-institute/trureturing-experiments at commit
8db3cff2b9136b3086be66583c454f3ca93fb369, path
docs/reports/gallardo-rahavandrainy-2025-binary-collatz-length-bound/check.py,
SHA-256 4f0db8a8d3cf2081c030bc3b8df0bb194c991b58c8831c2ef48f015531422238.
The preregistration records exit 0. This finite computation corroborates
the definitions and bound; the universal estimate is proved in Lean.
