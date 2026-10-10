---
bibkey: krishna2022cstarsmale
authors: K. Mahesh Krishna
year: 2022
title: "C*-algebraic Smale Mean Value Conjecture and Dubinin-Sugawa Dual Mean Value Conjecture"
doi: 10.48550/arXiv.2206.08154
url: https://arxiv.org/abs/2206.08154v1
claim: "Section 2 defines the ordered derivative P′; Section 3 states Conjecture DUALSMALE (Conjecture 3.1) and proves its degree-two case (Theorem 3.3)."
strata_touched:
  - D5/S3/Quantum/Algebra/CStarDualMeanValue
license: citation-only
triage: anchor
---

## Verified locator

DOI: https://doi.org/10.48550/arXiv.2206.08154

Source: https://arxiv.org/abs/2206.08154v1

Journal: https://doi.org/10.26117/2079-6641-2026-54-2-38-47

# C*-algebraic dual mean value conjecture

K. Mahesh Krishna, “C*-algebraic Smale Mean Value Conjecture and Dubinin-Sugawa
Dual Mean Value Conjecture”, arXiv:2206.08154v1 (16 June 2022). The journal
version is Vestnik KRAUNC Fiz.-Mat. Nauki 54(2) (2026), 38–47,
DOI 10.26117/2079-6641-2026-54-2-38-47.

Section 2, p. 4, defines the polynomial and its derivative:

> Let 𝒜 be a C*-algebra. For P(z) ≔ (z−a₁)(z−a₂)⋯(z−aₙ) for all z∈𝒜 with a₁, a₂, …, aₙ ∈ 𝒜, we define P′(z)=∑ⱼ₌₁ⁿ (z−a₁)⋯(z−aⱼ)̂⋯(z−aₙ), ∀z∈𝒜 where the term with cap is missing.

The derivative is the sum of ordered products with one factor omitted. The
gloss in Conjecture CSMALE (Conjecture 2.1, p. 4) is “If z∈𝒜 is not a critical
point of P (i.e., P′(z)≠0)”.

Section 3, p. 7, states Conjecture DUALSMALE (Conjecture 3.1):

> **C*-algebraic Dubinin-Sugawa Dual Mean Value Conjecture.** Let 𝒜 be a commutative C*-algebra. Let P(z) ≔ (z−a₁)⋯(z−aₙ) be a polynomial of degree n ≥ 2 over 𝒜, a₁, …, aₙ ∈ 𝒜. If z∈𝒜 is not a critical point of P, then there exists a critical point w∈𝒜 of P such that ‖P′(z)‖/deg(P) = ‖P′(z)‖/n ≤ ‖P(z)−P(w)‖/‖z−w‖.

The same norm-form assertion is Conjecture 3.1 in the journal version.
Theorem 3.3 of the arXiv version (p. 7), numbered Theorem 3.1 in the journal,
states:

> Conjecture 3.1 holds for degree 2 C*-algebraic polynomials.

For degree two the sole critical point is (a₁+a₂)/2 and the norm inequality
is an equality. This result is distinct from the degree-three refutation.

The Lean encoding uses zero-based Fin n indices and the ordered product
`(List.ofFn fun i => z - a i).prod`. It reuses the ordered derivative of
`CStarSchoenberg`. Noncritical means that derivative is nonzero; critical
means that it is zero. The degree parameter n is cast to ℝ in the norm
inequality. The carrier is restricted to unital commutative C*-algebras in
Type, weakening the source's universal assertion; a counterexample in that
subclass refutes the source statement.
