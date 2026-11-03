---
bibkey: han2025hankel
authors: Guo-Niu Han, Emmanuel Pedon
year: 2025
title: "Hankel continued fractions and Hankel determinants for q-deformed metallic numbers"
doi: 10.48550/arXiv.2502.05993
url: https://arxiv.org/abs/2502.05993v2
claim: "H-fraction expansions of the q-metallic numbers and their shifts up to n+1, periodicity, values, Gale-Robinson recurrences and contiguity relations of their shifted Hankel determinants; Conjecture E on the shifts n+2 and beyond."
strata_touched:
  - D5/S3/Combinatorics/MetallicHankel/MetallicHankel
  - D5/S3/Combinatorics/MetallicHankel/MetallicHankelUnbounded
  - D5/S3/Combinatorics/MetallicHankel/MetallicHankelQuasipolynomialDefs
license: citation-only
triage: anchor
---

# Han and Pedon, Hankel determinants of q-deformed metallic numbers

The q-metallic number Φ_n(q) is the power series with constant term 1 satisfying
q Φ² + ((1 + qⁿ)(1 − q) − q[n]_q) Φ = 1, a q-deformation of the metallic ratio in the sense of Morier-Genoud and
Ovsienko. The paper computes the Hankel continued fraction of Φ_n and of its shifts Φ_n^{(ℓ)} for ℓ ≤ n + 1
(Theorems A and 7.3), and proves that the shifted Hankel determinants Δ^{(ℓ)}, 0 ≤ ℓ ≤ n + 1, take values in
{−1, 0, 1}, are 2n(n+1)-periodic for even n and antiperiodic for odd n (Theorem B), satisfy a Gale–Robinson
recurrence (Theorem C) and contiguity relations (Theorem D). Conjecture E states that Δ^{(n+2)} has the same
(anti)periodicity with values in {−2, …, 2} (part 1) and that Δ^{(ℓ)} is unbounded for ℓ ≥ n + 3 (part 2).

The module `D5/S3/Combinatorics/MetallicHankel/MetallicHankel` proves part 1 of Conjecture E for every n ≥ 2.

## Verified locator

DOI: 10.48550/arXiv.2502.05993

URL: https://arxiv.org/abs/2502.05993v2

- Locator: Section 1, equations (1.1), (1.2), Theorems A–D and Conjecture E.
- Locator: Section 2, equation (2.5); Section 7, Theorem 7.3.

## Higher-shift quasipolynomials

The separate follow-up by Guo-Niu Han and Emmanuel Pedon, *Hankel determinants for the (n+2)-shifted q-metallic numbers*, arXiv:2610.36132v1 (2026), states Conjecture C in its introduction. Its DOI is https://doi.org/10.48550/arXiv.2610.36132 and its specified version is https://arxiv.org/abs/2610.36132v1. The quadratic defining equation is equation (2.13); equations (1.4) and (1.5) define the shifted determinant and its empty value one.

For every metallic parameter n>=1 and every shift ell>=n+3, Conjecture C prescribes period rho=2n(n+1) for even n and rho=4n(n+1) for odd n. For every residue 0<=r<rho and every m>=0, the determinant of size r+m rho is the value at m of a rational polynomial Q_r. Each polynomial takes integer values at all integers, including negative ones. The conjecture imposes neither a degree bound nor minimality of the stated period. The exact statement is defined in MetallicHankelQuasipolynomialDefs and remains distinct from the earlier bounded-shift periodicity and higher-shift unboundedness results.

The normal inverse is given by `MetallicHankelBoundaryPolynomials.hankel_inverse_bezout`. The transfer statement `MetallicHankelEndpointSpectral.transfer_spectral_remainder` isolates one unit characteristic branch for a two-by-two rational power-series matrix with trace constant coefficient one and determinant q^D: its powers have the same coefficients as that branch at every actual depth h<D*K. Applying it to metallic continuants still requires the trace and determinant identities for the identical ordinary block.

The arithmetic theorem `D5/S3/Arith/PolynomialValues/BackwardPropagation.eval_int_mem_of_eval_nat_mem` extends additive subgroup membership of rational polynomial values from all natural inputs to all integer inputs. Taking the subgroup to be the integer image gives the all-integer-valuedness condition once residue polynomials agreeing with integral determinants on every nonnegative input have been constructed. These arithmetic and spectral results do not construct the residue polynomials or fixed complementary-minor formulas required by the full conjecture.

The source-specific theorem `MetallicHankelUnbounded.normal_family` exposes the metallic-series construction and its identical continuants. It supplies existence and uniqueness for every n>=1, the actual golden or metallic cycle data, the denominator recurrence and support, and determinant-one boundaries N=K rho for every K>=1 using the prescribed parity blocks. The reversed coefficients c and d are explicitly zero outside their polynomial supports. Every c moment below N vanishes, and every length-N predecessor moment is zero except the final value -1. The original unboundedness theorem consumes this construction. The normal data therefore match the hypotheses of the supported inverse theorem after setting its moment sequence to mu_i=[q^(n+1+i)]Phi and its dimension parameter to N-1. A separate exact inverse specialization is not asserted here. Polynomial dependence of arbitrary endpoint jets for these same continuants, the fixed complementary-index and sign identities, and construction of all residue polynomials remain necessary for Conjecture C.
