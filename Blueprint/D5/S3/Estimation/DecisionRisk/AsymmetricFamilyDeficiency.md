# Asymmetric Family Deficiency

## Abstract

Deficiency is directed along each fixed-mass fibre of the asymmetric experiment.

**Theorem 1.1 (Exact directed deficiencies on a fixed-mass fibre).**

$$\forall a, M, dOne, dTwo: \mathbb{R},\\{}(0 < 2 \cdot a)\\{} \Rightarrow (2 \cdot a < M)\\{} \Rightarrow (M < 1)\\{} \Rightarrow (a \leq dOne)\\{} \Rightarrow (dOne < dTwo)\\{} \Rightarrow (dTwo < (M - a))\\{} \Rightarrow (\text{let } D = 1 - M, L = M - a, QOne = \operatorname{asymmetricExperiment}(a, dOne, (L - dOne)), QTwo = \operatorname{asymmetricExperiment}(a, dTwo, (L - dTwo)), gamma = \frac{D \cdot (dTwo - dOne)}{(2 \cdot dTwo + D)} \text{ in } ((\operatorname{finiteDeficiency}(QTwo, QOne) = 0) \land\\{}(\operatorname{finiteDeficiency}(QOne, QTwo) = \operatorname{ofReal}(gamma)) \land\\{}(0 < gamma))).$$

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/DecisionRisk/AsymmetricFamilyDeficiency.asymmetric_family_deficiency` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Increasing the second label mass is an exact garbling: the common output is split between itself and the second label while both labels remain fixed.

In the reverse direction, the optimal error is the positive quantity gamma. A zero-one Bayes risk comparison gives the lower bound, and a kernel that moves mass from the third output to the common output attains it in both states.

## References

- Truth anchor: `D5/S3/Estimation/DecisionRisk/AsymmetricFamilyDeficiency.asymmetric_family_deficiency`
- Dependency: [D5/S3/Estimation/DecisionRisk/AsymmetricFamilyRiskInjectivity](AsymmetricFamilyRiskInjectivity.md)
