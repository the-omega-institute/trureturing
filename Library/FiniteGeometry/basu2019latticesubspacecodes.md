---
bibkey: basu2019latticesubspacecodes
authors: Pranab Basu, Navin Kashyap
year: 2019
title: The Lattice Structure of Linear Subspace Codes
doi: null
url: https://arxiv.org/abs/1911.00721v1
claim: "A linear code 𝒰 in ℙ_q(n) has a unique indecomposable basis if and only if 𝒰 is closed under intersection."
strata_touched:
  - D5/S3/Combinatorics/SubspaceCodes/BasuKashyapUniqueIndecomposableBasisRefutation
license: citation-only
triage: anchor
---

# Basu and Kashyap, linear subspace codes

## Verified locator

DOI: null

Source: https://arxiv.org/abs/1911.00721v1

The arXiv v1 PDF has 24 pages. It uses consecutive numbering
for definitions and propositions; the TeX labels below identify the statements
independently of numbering.

- Page 2: the subspace distance is
  `d_S(X,Y) = dim X + dim Y − 2 dim(X ∩ Y)`.
- Pages 4–5, Definition 1, TeX label `L`: “A subset 𝒰 ⊆ ℙ_q(n), with {0} ∈ 𝒰, is a
  linear subspace code if there exists a function ⊞ : 𝒰 × 𝒰 → 𝒰 such that:
  (i) (𝒰, ⊞) is an abelian group;
  (ii) the identity element of (𝒰, ⊞) is {0};
  (iii) X ⊞ X = {0} for every group element X ∈ 𝒰;
  (iv) the addition operation ⊞ is isometric, i.e., d_S(X ⊞ Y₁, X ⊞ Y₂) = d_S(Y₁, Y₂)
  for all X, Y₁, Y₂ ∈ 𝒰.”
- Page 15, Definition 9, TeX label `8`: “A linear code 𝒰 ⊆ ℙ_q(n) with the property
  that X ∩ Y ∈ 𝒰 whenever X, Y ∈ 𝒰 is said to be a linear code closed under intersection.”
- Page 19, Definition 11, TeX label `9`: “A codeword Y ≠ {0} of a linear subspace
  code 𝒰 is said to be indecomposable if Y cannot be expressed as Y = Y₁ ⊞ Y₂ for
  any Y₁,Y₂ ∈ 𝒰 with dim Y₁, dim Y₂ < dim Y.”
- Page 21, Remark 5, TeX label `R`: “The set of indecomposable codewords in a linear
  subspace code closed under intersection is linearly independent with respect to
  the linear addition over 𝔽₂. This together with Proposition 17 imply that the
  indecomposable codewords are a basis for the vector space over 𝔽₂ formed by the
  linear code.”
- Page 22, Section 6: “We observed earlier that the indecomposable codewords in a
  linear subspace code constitute a basis for the vector space over 𝔽₂ formed by
  the code (Remark 5). We refer to such a basis as an indecomposable basis. A linear
  code closed under intersection has a unique indecomposable basis.”
- Page 23, Section 6, Conjecture 6.1, TeX label `UIB`: “A linear code 𝒰 in ℙ_q(n)
  has a unique indecomposable basis if and only if 𝒰 is closed under intersection.”

## Encoding and scope

The field is any finite `F : Type`; the ambient space is `Fin n → F`. Codewords
are `Submodule F (Fin n → F)`. Intersection is `⊓`, the zero subspace is `⊥`, and
dimension is `Module.finrank F`. The distance uses the displayed integer
expression literally. A code records its subset and operation on that subset,
together with all four axioms. The basis is an unordered finite subset of
codewords: each codeword has exactly one representation as a finite subset sum
under the code operation. This is a basis of the code's 𝔽₂-space, rather than a
basis of the ambient F-space.

The converse fails for every finite field. Split the coordinates into blocks
`I,P,Q` of dimensions `i,a,b`, with `0 < i < a` and `i < b`. Put `A = I ⊕ P`,
`B = I ⊕ Q`, `C = P ⊕ Q` and use Klein addition on `{⊥,A,B,C}`. Exactly `A,B` are
indecomposable, and they form its unique indecomposable basis; nevertheless
`A ⊓ B = I` is outside the code. The settling module proves this family and
negates the universal conjecture with `F = ZMod 2` and `(i,a,b) = (1,2,2)`.

The source's intersection-closed direction and the qualified Remark 5 remain
intact. Section 6's recap omits Remark 5's intersection-closed qualifier. The
Braun–Etzion–Vardy cardinality conjecture and the source's results proved under
intersection closure are not refuted by this construction.
