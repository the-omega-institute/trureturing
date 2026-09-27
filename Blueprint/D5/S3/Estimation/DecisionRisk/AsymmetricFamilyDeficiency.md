# Asymmetric Family Deficiency

## Abstract

Deficiency is directed along each fixed-mass fibre of the asymmetric experiment.

**Theorem 1.1 (Exact directed deficiencies on a fixed-mass fibre).**

$$\forall a, M, dOne, dTwo: \mathbb{R},\\{}(0 < 2 \cdot a)\\{} \Rightarrow (M < 1)\\{} \Rightarrow (a \leq dOne)\\{} \Rightarrow (dOne < dTwo)\\{} \Rightarrow (dTwo < (M - a))\\{} \Rightarrow (\text{let } D = 1 - M, L = M - a, QOne = \operatorname{asymmetricExperiment}(a, dOne, (L - dOne)), QTwo = \operatorname{asymmetricExperiment}(a, dTwo, (L - dTwo)), gamma = \frac{D \cdot (dTwo - dOne)}{(2 \cdot dTwo + D)}, h = \frac{2 \cdot (dTwo - dOne)}{(2 \cdot dTwo + D)} \text{ in } ((\operatorname{finiteDeficiency}(QTwo, QOne) = 0) \land\\{}(\operatorname{finiteDeficiency}(QOne, QTwo) = \operatorname{ofReal}(gamma)) \land\\{}(0 < gamma) \land\\{}(0 < (\frac{(dTwo - dOne)}{(L - dOne)})) \land\\{}((\frac{(dTwo - dOne)}{(L - dOne)}) < 1) \land\\{}(0 < h) \land\\{}(h < 1) \land\\{}(\exists K: \operatorname{FiniteMarkovKernel}(\operatorname{Fin}(3), \operatorname{Fin}(3)),\\{}((K.1 = \begin{pmatrix}1 - (\frac{(dTwo - dOne)}{(L - dOne)})&0&\frac{(dTwo - dOne)}{(L - dOne)}\\0&1&0\\0&0&1\end{pmatrix}) \land\\{}(\forall i: \operatorname{Fin}(2), \operatorname{channelOutput}(K.1, QOne\left(i\right)) = QTwo\left(i\right)))) \land\\{}(\exists reverseKernel: \operatorname{FiniteMarkovKernel}(\operatorname{Fin}(3), \operatorname{Fin}(3)),\\{}((reverseKernel.1 = \begin{pmatrix}1&0&0\\0&1&0\\h&0&1 - h\end{pmatrix}) \land\\{}(\forall i: \operatorname{Fin}(2), \operatorname{totalVariation}(QOne\left(i\right), \operatorname{channelOutput}(reverseKernel.1, QTwo\left(i\right))) = gamma) \land\\{}(\operatorname{uniformSimulationError}(QOne, QTwo, reverseKernel) = gamma))))).$$

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/DecisionRisk/AsymmetricFamilyDeficiency.asymmetric_family_deficiency` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Increasing the second label mass is an exact garbling through the displayed state-independent kernel: the common output is split between itself and the second label while both labels remain fixed.

In the reverse direction, the optimal error is the positive quantity gamma. A zero-one Bayes risk comparison gives the lower bound, and the displayed kernel moves mass from the third output to the common output and has total-variation error exactly gamma in each state.

## References

- Truth anchor: `D5/S3/Estimation/DecisionRisk/AsymmetricFamilyDeficiency.asymmetric_family_deficiency`
- Dependency: [D5/S3/Estimation/DecisionRisk/AsymmetricFamilyRiskInjectivity](AsymmetricFamilyRiskInjectivity.md)
