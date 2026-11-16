---
bibkey: abednikolaevanovikov2026trace
authors: Sami Abdullah Abed; Irina Nikolaeva; Andrej Novikov
year: 2026
title: "How characterisations of traces and central elements fail: sharp violation constants via Michelson contrast and noncentrality"
doi: 10.48550/arXiv.2610.34388
arxiv: 2610.34388v1
url: https://arxiv.org/abs/2610.34388v1
claim: "Conjecture 11.1, item 6: V₂ = G − 1 for the spectral geometric mean on complex qubit densities."
strata_touched:
  - D5/S3/Quantum/Matrix/AbedNikolaevaNovikovItemSix
license: citation-only
triage: anchor
---

## Verified locator

DOI: 10.48550/arXiv.2610.34388

Source: https://arxiv.org/abs/2610.34388v1

## Conjecture 11.1

Page 57, verbatim (mathematical subscripts rendered as Unicode):

> Vₙ = G² − 1 for item 7 and Vₙ = g₂₅(δ) for item 25 in every dimension; V₂ = G − 1 for item 6; the value of Proposition 5.17 holds for item 9 in every dimension; and the lower bound of Proposition 5.22 is the two-contrast envelope of item 8 for even n.

Only the item-6 clause is addressed here. On its faithful range 0 ≤ δ < 1, G = 1/√(1−δ²).

Section 3.4 defines the envelope:

> For a fixed density V(ρ) denotes its supremum, and the envelope Vₙ(δ) is the supremum of V(ρ) over all ρ in Mₙ with OMC(ρ) = δ.

For item 6, the relative violation is (L−R)/R with L = φρ(A♮B) and R = √(φρ(A)φρ(B)). The positive definite matrices A and B are unrestricted complex matrices. Section 5.11 defines A♮B = (A⁻¹#B)¹ᐟ² A (A⁻¹#B)¹ᐟ², where X#Y = X¹ᐟ²(X⁻¹ᐟ²YX⁻¹ᐟ²)¹ᐟ²X¹ᐟ². Section 3.2 defines OMC(ρ) = (M−m)/(M+m), where M and m are the largest and smallest spectral values. Density scaling cancels from the quotient.

## Evidence and scope

The item-6 Lean theorem proves the outer envelope equality for every δ ∈ [0,1). It establishes the upper bound for all faithful complex qubit densities and constructs a positive definite family attaining the limiting value for a density of each contrast. A separate fixed-density sharpness theorem for every density is not asserted.

The independent experiment is `the-omega-institute/trureturing-experiments`, commit `899d34d8041742cedebc176045cf870d202805a2`, file `docs/reports/michelson-trace-violation-two-dim/check.py`, SHA256 `c38a22de5c2abd02f88fce0dac6b6444e2f856c112698a8887cb50157c4e6ae0`. Its recorded exit is 0 with `ALL_CHECKS_OK`: 2800 scalar cases, 756 complex-vector cases, non-diagonal unitary transport and symbolic identities. These are experimental readings from issue #22896, separate from the Lean proof.

Literature-screen completeness is ASSUMED-UNVERIFIED. The source's higher-dimensional numerical observations, the singular endpoint and the other Conjecture 11.1 clauses are outside the item-6 theorem.
