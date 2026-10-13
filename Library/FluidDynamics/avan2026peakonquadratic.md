---
bibkey: avan2026peakonquadratic
authors: Jean Avan, Luc Frappat, Eric Ragoucy
year: 2026
title: "Quadratic Poisson brackets for the Camassa–Holm peakons"
doi: 10.1088/1751-8121/ae7683
url: https://arxiv.org/abs/2512.11066v3
claim: "For the deformed Camassa–Holm peakon Lax matrix L(z) = S + Λ(z)T + ξ(z)A, the transfer matrices τ_m(z) = tr L(z)^m are polynomials in Λ(z) of degree m without constant term, with degree-one term h^(m) = m tr((T + γA/2)(S + A)^(m−1)) (Proposition 5.1). Conjecture 5.2 asserts that τ_m(z) expands in products h^(k_1)⋯h^(k_j) over partitions of m with coefficients a_j(k), a_1(m) = 1, and the values (5.21); the other coefficients are left undetermined."
strata_touched:
  - D5/S3/FluidDynamics/Solitons/CamassaHolmPeakonTransferExpansion
license: citation-only
triage: anchor
---

# Avan–Frappat–Ragoucy, quadratic Poisson brackets for the Camassa–Holm peakons

J. Avan, L. Frappat and E. Ragoucy, *Quadratic Poisson brackets for the Camassa–Holm peakons*, arXiv:2512.11066 [nlin.SI] (v1 11 December 2025; v3 29 June 2026); J. Phys. A: Math. Theor. **59**, 245202 (2026), DOI 10.1088/1751-8121/ae7683.

## Verified locator

DOI: 10.1088/1751-8121/ae7683 (J. Phys. A 59, 245202; the journal full text was not read).
Primary version read: https://arxiv.org/abs/2512.11066v3 (the latest arXiv version).
Source: https://arxiv.org/pdf/2512.11066v3 (text read from the PDF):
- §2.1, Eqs. (2.1)–(2.3), the matrices A, T and S;
- §5.3, Proposition 5.1 with (5.17)–(5.19), and Conjecture 5.2 with (5.20) and (5.21);
- §6, the conclusion.

## Source statements

§2.1: "A = Σ_{i,j=1}^N √(p_i p_j) sinh(ν(q_i − q_j)/2) E_ij, (2.1) T = Σ_{i,j=1}^N √(p_i p_j) cosh(ν(q_i − q_j)/2) E_ij, (2.2) S = Σ_{i,j=1}^N √(p_i p_j) s_ij sinh(ν(q_i − q_j)/2) E_ij, (2.3) where s_ij = sgn(q_i − q_j) with the convention s_ii = 0."

§5.3, Proposition 5.1: "The transfer matrix τ_m(z) is a polynomial in Λ(z) of degree m with no constant term, and a degree 1 term of the form h^(m) = m tr((T + ½γA)(S + A)^{m−1}). (5.17)" Its proof: "the Lax matrix (4.8) can be decomposed as L(z) = S + Λ(z)T + ξ(z)A … ξ(z)² = Λ(z)² + γΛ(z) + 1. (5.18)"

§5.3: "From the expressions of τ_m(z), m = 2,3,...,7, we are led to postulate the following conjecture: Conjecture 5.2 The transfer matrices τ_m(z) can be expanded as τ_m(z) = Σ_{j=1}^m Λ(z)^j Σ_{0<k_j≤k_{j−1}≤...≤k_1, k_1+k_2+...+k_j=m} a_j(k_1,k_2,..,k_j) h^(k_1) h^(k_2) ⋯ h^(k_j), (5.20) with a_1(m) = 1. We conjecture the following values for the coefficients a_m(1,1,...,1) = 1, a_{j+1}(m−j,1,...,1) = m/(m−j), 0 ≤ j < m−1, (5.21) the other coefficients a_j(k_1,k_2,..,k_j) remain to be determined."

§6: "it would be desirable to prove the conjecture we have postulated on the expansion of the transfer matrices."
