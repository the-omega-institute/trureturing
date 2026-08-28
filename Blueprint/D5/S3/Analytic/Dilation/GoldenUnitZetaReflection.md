# Golden Unit Zeta Reflection

## Abstract

Conjugation reflects the golden-unit flow, while unit multiplication supplies its period.

**Theorem 1.1 (Conjugation and unit translation generate the flow symmetries).**

$$\begin{aligned}sigmaPlus: \mathbb{Z} \times \mathbb{Z} \to \mathbb{R}, \operatorname{sigmaPlus}((a, b)) := a + b \times \varphi,\\sigmaMinus: \mathbb{Z} \times \mathbb{Z} \to \mathbb{R}, \operatorname{sigmaMinus}((a, b)) := a + b \times \psi,\\anisotropicForm: \mathbb{R} \to \mathbb{Z} \times \mathbb{Z} \to \mathbb{R}, \operatorname{anisotropicForm}(eta, (a, b)) := \operatorname{exp}(eta) \times \operatorname{sigmaPlus}((a, b))^{2} + \operatorname{exp}(-eta) \times \operatorname{sigmaMinus}((a, b))^{2},\\goldenUnitZeta: \mathbb{C} \to \mathbb{R} \to \mathbb{C}, \operatorname{goldenUnitZeta}(s, eta) := \sum_{alpha \in {\mathbb{Z} \times \mathbb{Z}} \setminus \{(0, 0)\}} \operatorname{anisotropicForm}(eta, alpha)^{-s},\\(\forall s \in \mathbb{C}, \forall eta \in \mathbb{R}, \operatorname{goldenUnitZeta}(s, eta) = \operatorname{goldenUnitZeta}(s, -eta)) \land (\forall s \in \mathbb{C}, \forall eta \in \mathbb{R}, \operatorname{goldenUnitZeta}(s, eta + 2 \cdot \operatorname{log}(\varphi)) = \operatorname{goldenUnitZeta}(s, eta)).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Dilation/GoldenUnitZetaReflection.golden_unit_zeta_reflection` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A coefficient pair (a,b) represents the quadratic integer a+b phi. Both real embeddings, the anisotropic form, and the zeta sum over the nonzero coefficient lattice are exposed in the statement.

Quadratic conjugation is the integral involution (a,b) maps to (a+b,-b). It exchanges the two real embeddings and therefore reindexes the zeta at eta as the zeta at minus eta. The second public conjunct imports the regulator-period theorem on exactly the same carrier, exposing both symmetry generators.

Current D5 and pinned-Mathlib searches found no exact reflection theorem. The proof applies the canonical subtype equivalence and total-sum reindexing machinery; it does not define the zeta by its target symmetry or replace the coefficient lattice with a surrogate.

## References

- Truth anchor: `D5/S3/Analytic/Dilation/GoldenUnitZetaReflection.golden_unit_zeta_reflection`
- Dependency: [D5/S3/Analytic/Dilation/GoldenUnitZetaPeriodicity](GoldenUnitZetaPeriodicity.md)
