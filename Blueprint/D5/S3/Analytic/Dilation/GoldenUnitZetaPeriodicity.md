# Golden Unit Zeta Periodicity

## Abstract

The golden-unit lattice zeta is periodic along the regulator flow.

**Theorem 1.1 (The golden unit gives the regulator period).**

$$\begin{aligned}sigmaPlus: \mathbb{Z} \times \mathbb{Z} \to \mathbb{R}, \operatorname{sigmaPlus}((a, b)) := a + b \times \varphi,\\sigmaMinus: \mathbb{Z} \times \mathbb{Z} \to \mathbb{R}, \operatorname{sigmaMinus}((a, b)) := a + b \times \psi,\\anisotropicForm: \mathbb{R} \to \mathbb{Z} \times \mathbb{Z} \to \mathbb{R}, \operatorname{anisotropicForm}(eta, (a, b)) := \operatorname{exp}(eta) \times \operatorname{sigmaPlus}((a, b))^{2} + \operatorname{exp}(-eta) \times \operatorname{sigmaMinus}((a, b))^{2},\\goldenUnitZeta: \mathbb{C} \to \mathbb{R} \to \mathbb{C}, \operatorname{goldenUnitZeta}(s, eta) := \sum_{alpha \in {\mathbb{Z} \times \mathbb{Z}} \setminus \{(0, 0)\}} \operatorname{anisotropicForm}(eta, alpha)^{-s},\\\forall s \in \mathbb{C}, \forall eta \in \mathbb{R}, \operatorname{goldenUnitZeta}(s, eta + 2 \cdot \operatorname{log}(\varphi)) = \operatorname{goldenUnitZeta}(s, eta).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Dilation/GoldenUnitZetaPeriodicity.golden_unit_zeta_periodicity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A coefficient pair (a,b) represents the quadratic integer a+b phi. The statement exposes both real embeddings, the anisotropic form, and the zeta sum over the nonzero coefficient lattice.

Multiplication by phi is the integral bijection (a,b) maps to (b,a+b). Its two embeddings scale by phi and its conjugate, so reindexing the totalized sum shifts the flow parameter by twice log(phi) without changing the value.

## References

- Truth anchor: `D5/S3/Analytic/Dilation/GoldenUnitZetaPeriodicity.golden_unit_zeta_periodicity`
