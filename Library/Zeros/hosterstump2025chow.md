---
bibkey: hosterstump2025chow
authors: Elena Hoster and Christian Stump
year: 2025
title: Chow polynomials of simplicial posets with positive h-vector are real-rooted
doi: null
url: https://arxiv.org/abs/2508.15538v1
claim: Conjecture 1.5 asserts real-rootedness of the Chow, dual Chow and augmented Chow polynomials of every simplicial poset, together with their interlacing.
strata_touched:
  - D5/S3/Zeros/SimplicialPosetChowRefutation
license: citation-only
triage: anchor
---

# Chow polynomials of simplicial posets

## Verified locator

DOI: null. Crossref's title-and-author query returns no matching work.

Source: https://arxiv.org/abs/2508.15538v1

Section 1, p. 1: simplicial posets, the adjoined top, isolated sets, flag
f- and h-vectors, formulas (1.1)–(1.2), and Theorem 1.1. Section 1, p. 2:
Theorem 1.2. Section 1, p. 3: Conjecture 1.5. The associated FPSAC 2026
abstract gives the conjecture on p. 4.

## Source statements

Section 1, p. 1:

> Let P be a finite graded simplicial poset. This is, P is a finite poset with 0̂ for which all maximal intervals are boolean of the same rank n.

> Let P̂ be obtained from P by adding a top element 1̂.

> Here, a set S ⊂ ℤ is isolated if i ∈ S implies i+1 ∉ S.

The flag f-vector counts maximal chains in the subposet with only the selected
ranks, with α(∅) = 1 as in Example 1.3. The flag h-vector is
β(S) = Σ_{T⊆S} (−1)^{|S∖T|} α(T). Formula (1.1) is
H(x) = Σ_{S⊆{2,…,n}, S isolated} β(S) x^{|S|} (1+x)^{n−2|S|}.

Conjecture 1.5, p. 3:

> Let P be a simplicial poset. Then H_P̂(x), H_P̂*(x) and H^aug_P̂(x) are real-rooted. Moreover, the roots of both H_P̂(x) and H_P̂*(x) interlace the roots of H^aug_P̂(x) = H^aug_P̂*(x).

## Scope

The refutation uses the face poset of two tetrahedra sharing one vertex.
Its Chow polynomial is x⁴ + 23x³ + 43x² + 23x + 1 and has a non-real
complex zero. This refutes the first assertion of Conjecture 1.5 and hence
the conjecture. Theorems 1.1–1.2 retain their positive-h-vector hypothesis;
the counterexample has h-vector (1, 3, −3, 1, 0). The family, h-vector and
neighbouring assertions are separate from the kernel-checked single-instance
refutation.
