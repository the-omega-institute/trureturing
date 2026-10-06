# Catalan Root and Lagrange Coefficient Transform

## Abstract

The Catalan root supplies a formal substitution inverse used to recover the actual P13 series and transforms arbitrary rational-series coefficients through the original owner’s public Lagrange supplier.

Let C be the rational image of Mathlib’s Catalan series and q = C − 1. These statements concern formal power series. The public coefficient supplier is `D5/S3/Combinatorics/Nonnesting/NonnestingOneThreeTwoTwo.lagrange_coefficient`; its proof remains in the original nonnesting enumeration owner, where result also uses it.

The classical lineage is Gessel’s Lagrange inversion survey, Theorem 2.1.1 and Section 2.3. The proofs here combine that supplier with Mathlib’s Catalan equation, substitution, inverse, order and polynomial coefficient APIs. The coefficient transform retains n ≥ 1 and the positive-power bridge retains 1 ≤ k ≤ n.

**Definition 1.1 (Rational formal power series).**

Lean statement: `D5/S3/Combinatorics/Nonnesting/CatalanLagrangeBridge.PS`

*Formalization.* `D5/S3/Combinatorics/Nonnesting/CatalanLagrangeBridge.PS` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Ira M. Gessel (2016). *Lagrange Inversion*. DOI: [10.48550/arXiv.1609.05988](https://doi.org/10.48550/arXiv.1609.05988). URL: <https://arxiv.org/abs/1609.05988v1>.

*Commentary.*

PS abbreviates PowerSeries ℚ. All series, coefficients and cancellations in this module are formal and rational; no analytic convergence hypothesis is used.

**Definition 1.2 (The rational Catalan series).**

Lean statement: `D5/S3/Combinatorics/Nonnesting/CatalanLagrangeBridge.catalanUnit`

*Formalization.* `D5/S3/Combinatorics/Nonnesting/CatalanLagrangeBridge.catalanUnit` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Ira M. Gessel (2016). *Lagrange Inversion*. DOI: [10.48550/arXiv.1609.05988](https://doi.org/10.48550/arXiv.1609.05988). URL: <https://arxiv.org/abs/1609.05988v1>.

*Commentary.*

C is the image of Mathlib’s natural-coefficient Catalan series under Nat.castRingHom ℚ. Its coefficient at index n is the rational cast of the nth Catalan number.

**Definition 1.3 (The zero-constant Catalan root).**

Lean statement: `D5/S3/Combinatorics/Nonnesting/CatalanLagrangeBridge.q`

*Formalization.* `D5/S3/Combinatorics/Nonnesting/CatalanLagrangeBridge.q` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Ira M. Gessel (2016). *Lagrange Inversion*. DOI: [10.48550/arXiv.1609.05988](https://doi.org/10.48550/arXiv.1609.05988). URL: <https://arxiv.org/abs/1609.05988v1>.

*Commentary.*

The series q is C − 1. This is the root substitution used in Gessel’s Section 2.3, with its constant coefficient removed.

**Theorem 1.4 (The Catalan equation over ℚ).**

Lean statement: `D5/S3/Combinatorics/Nonnesting/CatalanLagrangeBridge.catalanUnit_equation`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Nonnesting/CatalanLagrangeBridge.catalanUnit_equation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ira M. Gessel (2016). *Lagrange Inversion*. DOI: [10.48550/arXiv.1609.05988](https://doi.org/10.48550/arXiv.1609.05988). URL: <https://arxiv.org/abs/1609.05988v1>.

*Commentary.*

C²X + 1 = C follows by mapping Mathlib’s catalanSeries_sq_mul_X_add_one to rational coefficients.

**Theorem 1.5 (Constant coefficient of C).**

Lean statement: `D5/S3/Combinatorics/Nonnesting/CatalanLagrangeBridge.catalanUnit_constantCoeff`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Nonnesting/CatalanLagrangeBridge.catalanUnit_constantCoeff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ira M. Gessel (2016). *Lagrange Inversion*. DOI: [10.48550/arXiv.1609.05988](https://doi.org/10.48550/arXiv.1609.05988). URL: <https://arxiv.org/abs/1609.05988v1>.

*Commentary.*

The constant coefficient of the rational Catalan series C is one.

**Theorem 1.6 (Admissibility of the root substitution).**

Lean statement: `D5/S3/Combinatorics/Nonnesting/CatalanLagrangeBridge.q_constantCoeff`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Nonnesting/CatalanLagrangeBridge.q_constantCoeff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ira M. Gessel (2016). *Lagrange Inversion*. DOI: [10.48550/arXiv.1609.05988](https://doi.org/10.48550/arXiv.1609.05988). URL: <https://arxiv.org/abs/1609.05988v1>.

*Commentary.*

The constant coefficient of q is zero. The substitution proofs use this equality to construct HasSubst q; admissibility is not assumed for an arbitrary nonzero-constant series.

**Theorem 1.7 (The Catalan root equation).**

Lean statement: `D5/S3/Combinatorics/Nonnesting/CatalanLagrangeBridge.q_equation`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Nonnesting/CatalanLagrangeBridge.q_equation` (`✓ std3`). ∎

*Citation.* Ira M. Gessel (2016). *Lagrange Inversion*. DOI: [10.48550/arXiv.1609.05988](https://doi.org/10.48550/arXiv.1609.05988). URL: <https://arxiv.org/abs/1609.05988v1>.

*Commentary.*

The series q satisfies q = X(1 + q)², the Catalan instance of the Lagrange fixed-point equation.

**Definition 1.8 (The square unit).**

Lean statement: `D5/S3/Combinatorics/Nonnesting/CatalanLagrangeBridge.sourceUnitSq`

*Formalization.* `D5/S3/Combinatorics/Nonnesting/CatalanLagrangeBridge.sourceUnitSq` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Ira M. Gessel (2016). *Lagrange Inversion*. DOI: [10.48550/arXiv.1609.05988](https://doi.org/10.48550/arXiv.1609.05988). URL: <https://arxiv.org/abs/1609.05988v1>.

*Commentary.*

sourceUnitSq is (1 + X)² in ℚ⟦X⟧.

**Definition 1.9 (The formal multiplicative inverse).**

Lean statement: `D5/S3/Combinatorics/Nonnesting/CatalanLagrangeBridge.sourceUnitSqInv`

*Formalization.* `D5/S3/Combinatorics/Nonnesting/CatalanLagrangeBridge.sourceUnitSqInv` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Ira M. Gessel (2016). *Lagrange Inversion*. DOI: [10.48550/arXiv.1609.05988](https://doi.org/10.48550/arXiv.1609.05988). URL: <https://arxiv.org/abs/1609.05988v1>.

*Commentary.*

sourceUnitSqInv is PowerSeries.invOfUnit applied to (1 + X)² with the unit Units.mk0 (1 : ℚ) one_ne_zero. This is a formal unit inverse, not a numerical division or an analytic reciprocal.

**Definition 1.10 (The inverse substitution).**

Lean statement: `D5/S3/Combinatorics/Nonnesting/CatalanLagrangeBridge.zeta`

*Formalization.* `D5/S3/Combinatorics/Nonnesting/CatalanLagrangeBridge.zeta` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Ira M. Gessel (2016). *Lagrange Inversion*. DOI: [10.48550/arXiv.1609.05988](https://doi.org/10.48550/arXiv.1609.05988). URL: <https://arxiv.org/abs/1609.05988v1>.

*Commentary.*

The series ζ is X times sourceUnitSqInv, so it represents X/(1 + X)² as a formal power series.

**Theorem 1.11 (Right multiplicative inverse).**

Lean statement: `D5/S3/Combinatorics/Nonnesting/CatalanLagrangeBridge.sourceUnitSq_inv_right`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Nonnesting/CatalanLagrangeBridge.sourceUnitSq_inv_right` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ira M. Gessel (2016). *Lagrange Inversion*. DOI: [10.48550/arXiv.1609.05988](https://doi.org/10.48550/arXiv.1609.05988). URL: <https://arxiv.org/abs/1609.05988v1>.

*Commentary.*

sourceUnitSq times sourceUnitSqInv equals one.

**Theorem 1.12 (Left multiplicative inverse).**

Lean statement: `D5/S3/Combinatorics/Nonnesting/CatalanLagrangeBridge.sourceUnitSq_inv_left`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Nonnesting/CatalanLagrangeBridge.sourceUnitSq_inv_left` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ira M. Gessel (2016). *Lagrange Inversion*. DOI: [10.48550/arXiv.1609.05988](https://doi.org/10.48550/arXiv.1609.05988). URL: <https://arxiv.org/abs/1609.05988v1>.

*Commentary.*

sourceUnitSqInv times sourceUnitSq equals one.

**Theorem 1.13 (Admissibility of the inverse substitution).**

Lean statement: `D5/S3/Combinatorics/Nonnesting/CatalanLagrangeBridge.zeta_constantCoeff`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Nonnesting/CatalanLagrangeBridge.zeta_constantCoeff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ira M. Gessel (2016). *Lagrange Inversion*. DOI: [10.48550/arXiv.1609.05988](https://doi.org/10.48550/arXiv.1609.05988). URL: <https://arxiv.org/abs/1609.05988v1>.

*Commentary.*

The constant coefficient of ζ is zero, supplying HasSubst ζ for lawful composition in the actual carrier recovery.

**Theorem 1.14 (Substituting q into ζ).**

Lean statement: `D5/S3/Combinatorics/Nonnesting/CatalanLagrangeBridge.zeta_subst_q`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Nonnesting/CatalanLagrangeBridge.zeta_subst_q` (`✓ std3`). ∎

*Citation.* Ira M. Gessel (2016). *Lagrange Inversion*. DOI: [10.48550/arXiv.1609.05988](https://doi.org/10.48550/arXiv.1609.05988). URL: <https://arxiv.org/abs/1609.05988v1>.

*Commentary.*

PowerSeries.subst q ζ = X. In dot notation this is ζ.subst q = X: q is the inner substitution argument. The proof substitutes into the square-unit identity and uses q = X(1 + q)².

**Definition 1.15 (The Lagrange factor).**

Lean statement: `D5/S3/Combinatorics/Nonnesting/CatalanLagrangeBridge.catalanFactor`

*Formalization.* `D5/S3/Combinatorics/Nonnesting/CatalanLagrangeBridge.catalanFactor` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Ira M. Gessel (2016). *Lagrange Inversion*. DOI: [10.48550/arXiv.1609.05988](https://doi.org/10.48550/arXiv.1609.05988). URL: <https://arxiv.org/abs/1609.05988v1>.

*Commentary.*

catalanFactor is the formal series (1 + X)² used as the factor in the public generic Lagrange theorem.

**Theorem 1.16 (The supplier’s fixed-point hypothesis).**

Lean statement: `D5/S3/Combinatorics/Nonnesting/CatalanLagrangeBridge.q_factor_equation`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Nonnesting/CatalanLagrangeBridge.q_factor_equation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ira M. Gessel (2016). *Lagrange Inversion*. DOI: [10.48550/arXiv.1609.05988](https://doi.org/10.48550/arXiv.1609.05988). URL: <https://arxiv.org/abs/1609.05988v1>.

*Commentary.*

q = X times PowerSeries.subst q catalanFactor. Together with q_constantCoeff this discharges the two series hypotheses of the original owner’s lagrange_coefficient.

**Theorem 1.17 (Coefficients of the square-factor powers).**

Lean statement: `D5/S3/Combinatorics/Nonnesting/CatalanLagrangeBridge.binomialCoefficient`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Nonnesting/CatalanLagrangeBridge.binomialCoefficient` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ira M. Gessel (2016). *Lagrange Inversion*. DOI: [10.48550/arXiv.1609.05988](https://doi.org/10.48550/arXiv.1609.05988). URL: <https://arxiv.org/abs/1609.05988v1>.

*Commentary.*

For natural exponent e and index j, the coefficient of Xʲ in (1 + X)ᵉ is the rational cast of e.choose j. The proof reuses the polynomial coefficient formula.

**Theorem 1.18 (A binomial difference).**

Lean statement: `D5/S3/Combinatorics/Nonnesting/CatalanLagrangeBridge.one_sub_X_power_coefficient`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Nonnesting/CatalanLagrangeBridge.one_sub_X_power_coefficient` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ira M. Gessel (2016). *Lagrange Inversion*. DOI: [10.48550/arXiv.1609.05988](https://doi.org/10.48550/arXiv.1609.05988). URL: <https://arxiv.org/abs/1609.05988v1>.

*Commentary.*

For natural e and j, the coefficient of Xʲ in (1 − X)(1 + X)ᵉ is one if j = 0, and otherwise equals the rational cast of e.choose j minus the rational cast of e.choose (j − 1). The zero-index case is explicit; natural subtraction is not silently replaced by integer subtraction.

**Theorem 1.19 (Positive powers of the Catalan root).**

Lean statement: `D5/S3/Combinatorics/Nonnesting/CatalanLagrangeBridge.q_power_coefficient_bridge`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Nonnesting/CatalanLagrangeBridge.q_power_coefficient_bridge` (`✓ std3`). ∎

*Citation.* Ira M. Gessel (2016). *Lagrange Inversion*. DOI: [10.48550/arXiv.1609.05988](https://doi.org/10.48550/arXiv.1609.05988). URL: <https://arxiv.org/abs/1609.05988v1>.

*Commentary.*

For natural n and k with 1 ≤ k ≤ n, the coefficient of Xⁿ in qᵏ equals the coefficient of Xⁿ⁻ᵏ in (1 − X)(1 + X)^(2n − 1). The proof directly invokes the original owner’s public lagrange_coefficient, then uses Pascal’s identity and a binomial ratio. It treats k = n separately and cancels the rational cast of n only after proving it nonzero.

**Theorem 1.20 (The zero-power case).**

Lean statement: `D5/S3/Combinatorics/Nonnesting/CatalanLagrangeBridge.q_zero_power_coefficient_bridge`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Nonnesting/CatalanLagrangeBridge.q_zero_power_coefficient_bridge` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ira M. Gessel (2016). *Lagrange Inversion*. DOI: [10.48550/arXiv.1609.05988](https://doi.org/10.48550/arXiv.1609.05988). URL: <https://arxiv.org/abs/1609.05988v1>.

*Commentary.*

For n ≥ 1, the coefficient of Xⁿ in q⁰ equals the coefficient of Xⁿ in (1 − X)(1 + X)^(2n − 1). Both vanish; the binomial symmetry argument supplies this case separately from the positive-power supplier.

**Theorem 1.21 (An arbitrary-series coefficient transform).**

Lean statement: `D5/S3/Combinatorics/Nonnesting/CatalanLagrangeBridge.q_subst_coefficient_transform`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Nonnesting/CatalanLagrangeBridge.q_subst_coefficient_transform` (`✓ std3`). ∎

*Citation.* Ira M. Gessel (2016). *Lagrange Inversion*. DOI: [10.48550/arXiv.1609.05988](https://doi.org/10.48550/arXiv.1609.05988). URL: <https://arxiv.org/abs/1609.05988v1>.

*Commentary.*

For every G : ℚ⟦X⟧ and natural n ≥ 1, coeff n (G.subst q) = coeff n ((1 − X)(1 + X)^(2n − 1)G). This is Gessel’s equation (2.1.2) specialized to R(t) = (1 + t)². The proof uses HasSubst q, the order bound that kills powers beyond n, a finite coefficient sum, and the separate k = 0 and 1 ≤ k ≤ n bridges. No restriction to polynomial G is imposed.

The actual P13Enumeration consumer uses ζ.subst q = X on the recovery path and applies the arbitrary-series coefficient transform to the explicit scalar G. The matching identification and actual boundary elimination belong to that consumer. This bridge retains the inverse direction used there; the unused reverse companion is omitted.

## References

- Truth anchor: `D5/S3/Combinatorics/Nonnesting/CatalanLagrangeBridge.PS`
- Truth anchor: `D5/S3/Combinatorics/Nonnesting/CatalanLagrangeBridge.binomialCoefficient`
- Truth anchor: `D5/S3/Combinatorics/Nonnesting/CatalanLagrangeBridge.catalanFactor`
- Truth anchor: `D5/S3/Combinatorics/Nonnesting/CatalanLagrangeBridge.catalanUnit`
- Truth anchor: `D5/S3/Combinatorics/Nonnesting/CatalanLagrangeBridge.catalanUnit_constantCoeff`
- Truth anchor: `D5/S3/Combinatorics/Nonnesting/CatalanLagrangeBridge.catalanUnit_equation`
- Truth anchor: `D5/S3/Combinatorics/Nonnesting/CatalanLagrangeBridge.one_sub_X_power_coefficient`
- Truth anchor: `D5/S3/Combinatorics/Nonnesting/CatalanLagrangeBridge.q`
- Truth anchor: `D5/S3/Combinatorics/Nonnesting/CatalanLagrangeBridge.q_constantCoeff`
- Truth anchor: `D5/S3/Combinatorics/Nonnesting/CatalanLagrangeBridge.q_equation`
- Truth anchor: `D5/S3/Combinatorics/Nonnesting/CatalanLagrangeBridge.q_factor_equation`
- Truth anchor: `D5/S3/Combinatorics/Nonnesting/CatalanLagrangeBridge.q_power_coefficient_bridge`
- Truth anchor: `D5/S3/Combinatorics/Nonnesting/CatalanLagrangeBridge.q_subst_coefficient_transform`
- Truth anchor: `D5/S3/Combinatorics/Nonnesting/CatalanLagrangeBridge.q_zero_power_coefficient_bridge`
- Truth anchor: `D5/S3/Combinatorics/Nonnesting/CatalanLagrangeBridge.sourceUnitSq`
- Truth anchor: `D5/S3/Combinatorics/Nonnesting/CatalanLagrangeBridge.sourceUnitSqInv`
- Truth anchor: `D5/S3/Combinatorics/Nonnesting/CatalanLagrangeBridge.sourceUnitSq_inv_left`
- Truth anchor: `D5/S3/Combinatorics/Nonnesting/CatalanLagrangeBridge.sourceUnitSq_inv_right`
- Truth anchor: `D5/S3/Combinatorics/Nonnesting/CatalanLagrangeBridge.zeta`
- Truth anchor: `D5/S3/Combinatorics/Nonnesting/CatalanLagrangeBridge.zeta_constantCoeff`
- Truth anchor: `D5/S3/Combinatorics/Nonnesting/CatalanLagrangeBridge.zeta_subst_q`
- Truth anchor: `D5/S3/Combinatorics/Nonnesting/NonnestingOneThreeTwoTwo.lagrange_coefficient`
- Dependency: [D5/S3/Combinatorics/Nonnesting/NonnestingOneThreeTwoTwo](NonnestingOneThreeTwoTwo.md)
- Narrative reference: [D5/S3/Combinatorics/Nonnesting/NonnestingOneThreeTwoTwo](NonnestingOneThreeTwoTwo.md)
