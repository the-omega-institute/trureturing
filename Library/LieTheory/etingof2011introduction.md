---
bibkey: etingof2011introduction
authors: P. Etingof; O. Golberg; S. Hensel; T. Liu; A. Schwendner; D. Vaintrob; E. Yudovina
year: 2011
title: "Introduction to representation theory"
doi: 10.48550/arXiv.0901.0827
url: https://arxiv.org/abs/0901.0827v5
claim: "Problem 1.55 develops the finite-dimensional representation theory of sl(2) from the relations HE − EH = 2E, HF − FH = −2F, EF − FE = H: part (b) gives, for a vector w with Ew = 0, a degree-k polynomial P_k with E^k F^k w = P_k(H) w, and part (f) shows that a finite-dimensional irreducible representation with highest weight λ has basis v, Fv, …, F^λ v."
strata_touched:
  - D5/S3/Quantum/SpinChains/HypereclecticNonShortening
license: citation-only
triage: anchor
---

# Etingof et al., Introduction to representation theory

P. Etingof, O. Golberg, S. Hensel, T. Liu, A. Schwendner, D. Vaintrob and E. Yudovina,
*Introduction to representation theory*, arXiv:0901.0827v5 [math.RT] (1 February 2011);
published as Student Mathematical Library 59, American Mathematical Society, 2011.
Page numbers below are those printed in the v5 PDF.

## Verified locator

DOI: 10.48550/arXiv.0901.0827.
Primary version: https://arxiv.org/abs/0901.0827v5.
Source: https://arxiv.org/pdf/0901.0827v5 (text read from the PDF), §1.14 "Representations of sl(2)", Problem 1.55, printed pp. 20–21.

## Source statements

Problem 1.55 (p. 20): "According to the above, a representation of sl(2) is just a vector space V with a triple of operators E,F,H such that HE − EH = 2E, HF − FH = −2F, EF − FE = H … Let V be a finite dimensional representation of sl(2) (the ground field in this problem is C)."

Part (b) (p. 20): "Let W be any representation of sl(2) and w ∈ W be a nonzero vector such that Ew = 0. For any k > 0 find a polynomial P_k(x) of degree k such that E^k F^k w = P_k(H) w. (First compute EF^k w, then use induction in k)."

Part (f) (p. 21): "Show that for each N > 0, there exists a unique up to isomorphism irreducible representation of sl(2) of dimension N. … (For V finite dimensional irreducible take λ as in (a) and v ∈ V(λ) an eigenvector of H. Show that v, Fv, …, F^λ v is a basis of V …)"

## Use in this repository

`D5/S3/Quantum/SpinChains/HypereclecticNonShortening.lowering_kernel_zero` states, over any field of characteristic zero, that a vector of natural weight q annihilated by a power of the raising operator and by F^k with k ≤ q is zero. This is the nonvanishing of the lowering string of a primitive vector in parts (b) and (f), stated for a vector that is not assumed primitive. The repository proof inducts on the raising length and uses Mathlib's `IsSl2Triple.HasPrimitiveVectorWith.pow_toEnd_f_ne_zero_of_eq_nat`.
