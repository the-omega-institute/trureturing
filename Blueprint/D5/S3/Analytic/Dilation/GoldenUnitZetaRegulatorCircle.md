# Golden Unit Zeta on the Regulator Circle

## Abstract

The golden-unit lattice zeta is periodic and descends to its regulator circle.

**Theorem 1.1 (The golden-unit zeta descends through the regulator period).**

$$\begin{aligned}(\forall s \in \mathbb{C}, \forall eta \in \mathbb{R}, \operatorname{goldenUnitZeta}(s, eta + 2 \cdot \operatorname{log}(\varphi)) = \operatorname{goldenUnitZeta}(s, eta)) \land\\(\forall s \in \mathbb{C}, \forall eta \in \mathbb{R}, \operatorname{goldenUnitZetaOnRegulatorCircle}(s, [eta]_{\operatorname{AddCircle}(2 \cdot \operatorname{log}(\varphi))}) = \operatorname{goldenUnitZeta}(s, eta)).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Dilation/GoldenUnitZetaRegulatorCircle.golden_unit_zeta_regulator_circle` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Here goldenUnitZeta is the named sum over the nonzero coefficient lattice Z x Z for Z[phi]. Its named anisotropic form uses the two concrete embeddings a+b phi and a+b psi.

The first conjunct is the literal shift equality by twice log(phi). Its proof directly reuses the already-frozen lattice reindexing theorem.

The second conjunct evaluates the named quotient lift on the class of eta in AddCircle(2 log(phi)). Mathlib's Periodic.lift_coe identifies that pullback with the original zeta, so the quotient carrier appears in Lean rather than only in prose.

## References

- Truth anchor: `D5/S3/Analytic/Dilation/GoldenUnitZetaRegulatorCircle.golden_unit_zeta_regulator_circle`
- Dependency: [D5/S3/Analytic/Dilation/GoldenUnitZetaPeriodicity](GoldenUnitZetaPeriodicity.md)
