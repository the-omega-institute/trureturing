# RenyiSufficiencyRefutation

## Abstract

Positive matrix maps and the two-triangle obstruction to Rényi sufficiency.

**Theorem 1.1 (weighted charpoly eq).**

$$\forall (e : \mathbb{C}) , \forall (d : \operatorname{Fin} 5 \to \mathbb{C}) , (\operatorname{weightedRho} \operatorname{false} e d) .\operatorname{charpoly} = (\operatorname{weightedRho} \operatorname{true} e d) .\operatorname{charpoly}$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumChannels/RenyiSufficiency/RenyiSufficiencyRefutation.weighted_charpoly_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The two orientations of each triangle cancel in the principal minors. Multiplication on both sides by an arbitrary diagonal matrix retains equality of the characteristic polynomials.

**Theorem 1.2 (rho isDensity).**

$$\forall (minus : \operatorname{Bool}) , \operatorname{IsDensity} (\operatorname{rho} minus (1 / 1000))$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumChannels/RenyiSufficiency/RenyiSufficiencyRefutation.rho_isDensity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The complete parameter telescope and conclusion are displayed. Matrix products, transpose and conjTranspose have their Mathlib meanings; arrows indexed by Complex denote LinearMap.

**Theorem 1.3 (sigma isDensity).**

$$\operatorname{IsDensity} \operatorname{sigma}$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumChannels/RenyiSufficiency/RenyiSufficiencyRefutation.sigma_isDensity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The complete parameter telescope and conclusion are displayed. Matrix products, transpose and conjTranspose have their Mathlib meanings; arrows indexed by Complex denote LinearMap.

**Theorem 1.4 (DminFinite bouquet).**

$$\forall (minus : \operatorname{Bool}) , \forall (alpha : \mathbb{R}) , \operatorname{DminFinite} (\operatorname{rho} minus (1 / 1000)) \operatorname{sigma} alpha$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumChannels/RenyiSufficiency/RenyiSufficiencyRefutation.DminFinite_bouquet` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The complete parameter telescope and conclusion are displayed. Matrix products, transpose and conjTranspose have their Mathlib meanings; arrows indexed by Complex denote LinearMap.

**Theorem 1.5 (checkpoint profiles).**

$$\forall (alpha : \mathbb{R}) , (alpha \in \operatorname{Set}.\operatorname{Ioo} (2 : \mathbb{R}) 3) \to (\operatorname{Dmin} (\operatorname{rho} \operatorname{false} (1 / 1000)) \operatorname{sigma} alpha = \operatorname{Dmin} (\operatorname{rho} \operatorname{true} (1 / 1000)) \operatorname{sigma} alpha) \land (\operatorname{DminFinite} (\operatorname{rho} \operatorname{false} (1 / 1000)) \operatorname{sigma} alpha) \land (\operatorname{DminFinite} (\operatorname{rho} \operatorname{true} (1 / 1000)) \operatorname{sigma} alpha)$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumChannels/RenyiSufficiency/RenyiSufficiencyRefutation.checkpoint_profiles` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The complete parameter telescope and conclusion are displayed. Matrix products, transpose and conjTranspose have their Mathlib meanings; arrows indexed by Complex denote LinearMap.

**Definition 1.6 (claim).**

$$\operatorname{claim} = (\forall (n m : \mathbb{N}) (rho1 sigma1 : \operatorname{Matrix} (\operatorname{Fin} n) (\operatorname{Fin} n) \mathbb{C}) (rho2 sigma2 : \operatorname{Matrix} (\operatorname{Fin} m) (\operatorname{Fin} m) \mathbb{C}) , \operatorname{IsDensity} rho1 \to \operatorname{IsDensity} sigma1 \to \operatorname{IsDensity} rho2 \to \operatorname{IsDensity} sigma2 \to \forall a b : \mathbb{R} , 1 / 2 \leq a \to a < b \to (\forall alpha \in \operatorname{Set}.\operatorname{Ioo} a b , (\operatorname{DminFinite} rho1 sigma1 alpha) \land (\operatorname{DminFinite} rho2 sigma2 alpha)) \to (\operatorname{Interconvertible} rho1 sigma1 rho2 sigma2 \iff \forall alpha \in \operatorname{Set}.\operatorname{Ioo} a b , \operatorname{Dmin} rho1 sigma1 alpha = \operatorname{Dmin} rho2 sigma2 alpha))$$

*Formalization.* `D5/S3/QuantumChannels/RenyiSufficiency/RenyiSufficiencyRefutation.claim` (`✓ std3`).

*Citation.* N. Galke, L. van Luijk, H. Wilming (2023). *Sufficiency of Rényi divergences*. DOI: [10.48550/arXiv.2304.12989](https://doi.org/10.48550/arXiv.2304.12989). URL: <https://arxiv.org/abs/2304.12989v6>.

*Commentary.*

Galke, van Luijk and Wilming, Conjecture 22, Section 3.3, arXiv:2304.12989v6, p. 17: “Let (ρ₁, σ₁) and (ρ₂, σ₂) be pairs of density operators on quantum system S₁ and S₂. Let (a, b), ½ ≤ a < b, be any interval on which the minimal quantum Rényi divergences of both dichotomies are finite. Then the dichotomies are interconvertible via positive, trace-preserving maps if and only if they have the same minimal quantum Rényi divergences on this interval, i.e., (ρ₁, σ₁) ↔ (ρ₂, σ₂) ⇐⇒ Dᵐⁱⁿ_α(ρ₁, σ₁) = Dᵐⁱⁿ_α(ρ₂, σ₂) < ∞ ∀α ∈ (a, b).” The dimensions n and m range over Nat; the states are complex Fin-indexed matrices. IsDensity is the existing predicate asserting positive semidefiniteness and trace one. Dmin and DminFinite implement Appendix E with support inclusion also at alpha=1.

**Theorem 1.7 (result).**

$$\neg \operatorname{claim}$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumChannels/RenyiSufficiency/RenyiSufficiencyRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/galke-van-luijk-wilming-2023-renyi-sufficiency` (refuted) by `D5/S3/QuantumChannels/RenyiSufficiency/RenyiSufficiencyRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"galke-van-luijk-wilming-2023-renyi-sufficiency","declaration_gid":"D5/S3/QuantumChannels/RenyiSufficiency/RenyiSufficiencyRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* N. Galke, L. van Luijk, H. Wilming (2023). *Sufficiency of Rényi divergences*. DOI: [10.48550/arXiv.2304.12989](https://doi.org/10.48550/arXiv.2304.12989). URL: <https://arxiv.org/abs/2304.12989v6>.

*Commentary.*

At dimension five, epsilon=1/1000 and interval (2,3), the two bouquet dichotomies have equal finite minimal Rényi profiles. Their two-triangle gain changes sign, which precludes both sigma-preserving conjugation orientations and therefore positive trace-preserving interconversion.

## References

- Truth anchor: `D5/S3/QuantumChannels/RenyiSufficiency/RenyiSufficiencyRefutation.DminFinite_bouquet`
- Truth anchor: `D5/S3/QuantumChannels/RenyiSufficiency/RenyiSufficiencyRefutation.checkpoint_profiles`
- Truth anchor: `D5/S3/QuantumChannels/RenyiSufficiency/RenyiSufficiencyRefutation.claim`
- Truth anchor: `D5/S3/QuantumChannels/RenyiSufficiency/RenyiSufficiencyRefutation.result`
- Truth anchor: `D5/S3/QuantumChannels/RenyiSufficiency/RenyiSufficiencyRefutation.rho_isDensity`
- Truth anchor: `D5/S3/QuantumChannels/RenyiSufficiency/RenyiSufficiencyRefutation.sigma_isDensity`
- Truth anchor: `D5/S3/QuantumChannels/RenyiSufficiency/RenyiSufficiencyRefutation.weighted_charpoly_eq`
- Dependency: [D5/S3/Quantum/Entanglement/ChoiKiemKye/ConstructionReduction](../../Quantum/Entanglement/ChoiKiemKye/ConstructionReduction.md)
- Dependency: [D5/S3/QuantumChannels/RenyiSufficiency/BouquetHolonomy](BouquetHolonomy.md)
