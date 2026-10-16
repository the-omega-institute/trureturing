---
bibkey: girardplagne2026boxes
authors: Benjamin Girard and Alain Plagne
year: 2026
title: The Davenport constant of low-dimensional boxes
doi: 10.48550/arXiv.2610.16562
url: https://arxiv.org/abs/2610.16562v1
claim: "Section 2 asks whether the fixed-support box Davenport ratio has a limit in every positive dimension; Theorem 5 gives the three-dimensional asymptotic constant 16."
strata_touched:
  - D5/S3/Arith/Lattices/CofactorKernel
  - D5/S3/Arith/Lattices/CubeSimplexDeterminant
  - D5/S3/Arith/Lattices/PrimitivePencil
  - D5/S3/Arith/Lattices/MinimalKernelPacking
  - D5/S3/Arith/Lattices/GirardPlagneBoxLimit
license: citation-only
triage: anchor
---

# Fixed-support Davenport constants of integer boxes

## Verified locator

DOI: https://doi.org/10.48550/arXiv.2610.16562

Source: https://arxiv.org/abs/2610.16562v1

The version is arXiv:2610.16562v1. Section 2 is titled “New results”.
Theorem 5 and the question below appear on printed page 4.

## Source statements

Section 2, printed page 2, defines the quantity:

> we study the quantity D^(d+1)(⟦−m, m⟧^d) which is defined as the maximal length of a minimal zero-sum sequence over ⟦−m, m⟧^d having a support of size d + 1.

Section 2, printed page 4, asks:

> It appears tempting to conjecture that for every integer d ≥ 1, the ratio D^(d+1)(⟦−m, m⟧^d)/m^d has a limit when m tends to infinity. This is clear when d = 1, and it follows from Theorems 1 and 5 when d ∈ {2, 3}. However, this problem remains open when d ≥ 4.

Section 1, printed page 1, defines minimality:

> Moreover, if S is a zero-sum sequence such that ∑ᵢ∈ᴵ xᵢ ≠ 0 for every ∅ ≠ I ⊊ ⟦1, ℓ⟧, it will be called a minimal zero-sum sequence.

The sum of every nonempty proper subsequence is required to be nonzero. Multiplicity functions with values
in the natural numbers represent sequences; their pointwise order represents
subsequence inclusion. A support has one element per distinct vector.

## Mathematical correspondence

For dimension `d` and radius `m`, the box consists of integer vectors `v`
satisfying `∀ i, |v i| ≤ m`. The length set records all nonzero minimal
zero-sum multiplicity functions with support cardinality exactly `d + 1`.
Its natural-number supremum is the source's fixed-support Davenport constant.
The formal claim includes nonemptiness and boundedness for every `m ≥ 1`.

The repository-derived strengthening identifies the limit with `delta d`,
the finite maximum of the absolute determinant after adjoining a top row of
ones to a `d` by `d + 1` sign matrix. Full rank gives a primitive cofactor
kernel and its exact length formula. A cube vertex estimate bounds the
determinant, and a packing estimate makes deficient rank lower order.
Smith form supplies primitive integer pencils approaching an extremal simplex.

Theorem 1's two-dimensional formula and Theorem 5's three-dimensional
asymptotic agree with this limit. The source's unrestricted box Davenport
constant questions and exact higher-dimensional values are separate questions.
No general evaluation of the augmented maximal determinant is asserted.

## Numerical evidence and literature boundary

The independent experiment is
`docs/reports/girard-plagne-2026-box-davenport-limit/check.py` in
`the-omega-institute/trureturing-experiments`, commit
`73c308cec1a907b063b6e7a614083b5f71b0b0d8`, SHA-256
`94291f19d14913886f357a5e8d364f36d1ac02fd602cb34bbae46d37030c2fea`.
The supplied reading is `python3 check.py`, exit 0, `ALL_OK`.
These computations do not replace the general proof.

The supplied literature screen covers arXiv:2510.20412 (v1 and v2),
arXiv:2601.07950, Girard–Zotova arXiv:2510.23543, Plagne–Tringali
arXiv:1405.4363, and arXiv:2610.14546. No settlement was found in that screen.
Sturmfels's monograph, Chapters 6–7, was not obtained. Literature completeness
is `ASSUMED-UNVERIFIED`; no exhaustive priority claim is made.
