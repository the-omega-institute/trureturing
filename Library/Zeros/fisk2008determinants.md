---
bibkey: fisk2008determinants
authors: Steve Fisk
year: 2008
title: Questions about determinants and polynomials
doi: null
url: https://arxiv.org/abs/0808.1850v1
claim: Question 10 asserts that every minor of the coefficient-Toeplitz matrix of a positive upper bivariate polynomial is Hurwitz stable.
strata_touched:
  - D5/S3/Zeros/FiskToeplitzRefutation
license: citation-only
triage: anchor
---

# Questions about determinants and polynomials

## Verified locator

Source: https://arxiv.org/abs/0808.1850v1

Question 10 and matrix (5), PDF p. 4; definitions, PDF p. 1;
Remark 9, PDF p. 5. The related source is Steve Fisk, *Polynomials,
roots, and interlacing*, https://arxiv.org/abs/math/0612833v2,
Section 21.10, printed p. 648, Conjecture 21.84 and matrix (21.10.2).
No journal version was identified in the literature screen of issue #21768.

## Source statements

PDF p. 1 defines U₂ by:

> All polynomials f(x₁,…,x_d) with real coefficients such that f(σ₁,…,σ_d)≠0 for all σ₁,…,σ_d in the open upper half plane.

> P⁺_d = all polynomials in U_d with all positive coefficients.

> H₁ = all polynomials with all roots in the closed left half plane.

Question 10, PDF p. 4:

> Suppose f∈P⁺₂, and write f = ∑ f_i(x)y^i. Form the infinite matrix

The matrix (5) has entry f_(c−r) when r≤c and zero otherwise,
with rows and columns numbered from zero.

> Show that the resulting matrix is totally stable. That is, every minor is a stable polynomial.

Conjecture 21.84, printed p. 648 of the related book:

> If f(x,y)∈P₂ᵖᵒˢ then all minors of the matrix (21.10.2) are stable.

The book defines its input class using substitution, homogeneous positivity,
and positivity of all coefficients. That presentation is distinct from the
note's U₂-based presentation; no equality of these classes is assumed.

## Encoding and scope

Real bivariate polynomials are Polynomial (Polynomial ℝ), with x in the
coefficient ring and y outermost. Positivity is required on the coefficient
support. A minor uses strictly increasing row and column maps Fin n → ℕ,
so its sign is the source sign. Coefficients beyond the degree are zero;
the empty minor is 1. Hurwitz stability uses roots after mapping the real
coefficients to ℂ, and includes structural zero minors because their root
multiset is empty.

The counterexample is f=(4x+y+1)(x+y+4). Rows 0,…,4 and columns 1,…,5
give the nonzero determinant
5(x+1)(21x²+33x+21)(13x²−x+13). Its root
(1+15i√3)/26 has real part 1/26. The formal result negates Question 10.
For the book's input condition, either real specialization is a product of
two real affine factors with fixed degree two; the homogeneous part is
4x²+5xy+y². These observations explain the same counterexample for the
book without claiming a separate Lean theorem about its input class.

Remark 9's implication from Question 10 to Question 9 supplies no
refutation of Question 9. The repeated-factor examples and the book's
conditional statements about already totally stable matrices are unaffected.
The classification of surviving subclasses and minimal obstruction size
remain open here. Literature completeness is ASSUMED-UNVERIFIED.
