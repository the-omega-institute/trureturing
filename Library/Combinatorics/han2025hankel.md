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

The theorem `MetallicHankelResiduePolynomials.result` has the exact claim defined in `MetallicHankelQuasipolynomialDefs`: existence of an integral metallic series for every n>=1, and residue polynomials for every satisfying series, every shift ell>=n+3, every residue and every natural input including zero. The all-integer-valuedness clause includes negative inputs. The matching dossier is `Problems/han-pedon-metallic-hankel-quasipolynomial.md`, under the original preregistration issue #23253. The conclusion does not assert a minimal period or a sharp degree bound.

The source-specific theorem `MetallicHankelUnbounded.normal_family` supplies one metallic series and its unique normal continuants. It gives the same cycle data and denominator recurrence for every n>=1, with support degree N=K rho and enclosing Hankel determinant one at every K>=1. `MetallicHankelBlocks.ordinary_blocks` identifies the ordinary block acting on those continuants, with trace constant coefficient one and determinant X^(2rho); `reversed_blocks` identifies their supported reversals and gives constant monodromy equal to the identity. The actual trace series is not asserted to be one.

`MetallicHankelEndpointSpectral.transfer_spectral_remainder` supplies the unit characteristic branch for the ordinary block, with coefficient equality at every actual depth h<2K rho. `MetallicHankelEndpointJets.continuant_endpoint_jets` combines that branch with the reversed block to construct four rational coefficient polynomials at every depth. The common-degree high reversal of the predecessor retains its factor X^(n+1).

`MetallicHankelBoundaryPolynomials.hankel_inverse_bezout` determines all inverse entries from the same supported normal moment relations. `MetallicHankelComplementaryMinor.shifted_hankel_boundary` applies the original matrix duality identity with the ordered complementary indices, the exact sign (-1)^(a j), and guarded natural subtractions. Only the enclosing normal determinant is a unit; there is no target or neighboring-minor invertibility premise, and the target size can be zero.

For a=ell-(n+1) and residue r, choose K0=a+1, t=K0 rho-r and u=t-a. At every m>=0, the enclosing size (K0+m)rho equals r+m rho+t. All boundary depths are strictly below 2t and hence below twice the enclosing size, including the first term and the empty target. Replacing the four coefficient jets gives a fixed matrix over Q[X]. Evaluation commutes with its determinant; composition with K0+X and the constant sign (-1)^(a r) gives the residue polynomial.

`D5/S3/Arith/PolynomialValues/BackwardPropagation.eval_int_mem_of_eval_nat_mem` extends additive subgroup membership of rational polynomial values from all natural inputs to all integer inputs. Applied to the image of Z in Q, it supplies the negative-input integer-valuedness from the exact determinant values at every natural input. These results give polynomial laws for all residues; they do not supply minimal quasiperiods or sharp degrees.
