# Asymmetric Family Risk and Injective Queries

## Abstract

The asymmetric three-output experiment has an explicit Bayes risk, and the fixed-mass risk queries are injective exactly below the saturation prior.

**Definition 1.1 (The asymmetric experiment).**

$$\forall a, d, b: \mathbb{R},\\{}\text{let } D = 1 - (b + a + d) \text{ in } \operatorname{asymmetricExperiment}(a, d, b) = ((b, a + D, d), (b, a, d + D)).$$

*Formalization.* `D5/S3/Estimation/DecisionRisk/AsymmetricFamilyRiskInjectivity.asymmetricExperiment` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The two states share mass b in the first output. The residual mass D is placed in the second output for state zero and in the third output for state one.

**Definition 1.2 (Optimal zero-one Bayes risk).**

$$\forall a, d, b, pi: \mathbb{R},\\{}\operatorname{asymmetricBayesRisk}(a, d, b, pi) = \operatorname{sInf}(\operatorname{range}((delta: \operatorname{FiniteMarkovKernel}(\operatorname{Fin}(3), \operatorname{Fin}(2)) \mapsto \operatorname{finiteBayesCost}(\operatorname{vec}(pi, 1 - pi), (i, j)\mapsto \text{if }i = j \text{then }0 \text{else }1, \operatorname{asymmetricExperiment}(a, d, b), delta)))).$$

*Formalization.* `D5/S3/Estimation/DecisionRisk/AsymmetricFamilyRiskInjectivity.asymmetricBayesRisk` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The risk is the infimum over all row-stochastic decisions from the three outputs to the two actions, for the prior (pi, 1 - pi) and zero-one loss.

**Definition 1.3 (Risk along a fixed-mass fiber).**

$$\forall M, a, pi, d: \mathbb{R},\\{}\operatorname{asymmetricFiberRisk}(M, a, pi, d) = \operatorname{asymmetricBayesRisk}(a, d, M - a - d, pi).$$

*Formalization.* `D5/S3/Estimation/DecisionRisk/AsymmetricFamilyRiskInjectivity.asymmetricFiberRisk` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Fixing M and a leaves d as the fiber coordinate and sets b equal to M - a - d.

**Theorem 1.4 (Piecewise risk and injectivity threshold).**

$$\begin{gathered}\forall aOne, dOne, bOne, piOne, aTwo, mTwo, piTwo: \mathbb{R},\\{}((0 < aOne \land\\{}aOne \leq dOne \land\\{}0 < bOne \land\\{}bOne + aOne + dOne < 1 \land\\{}piOne \in \operatorname{Icc}(0, 1)) \Rightarrow \text{let } M = bOne + aOne + dOne, D = 1 - M, tMinus = \frac{aOne}{2 \cdot aOne + D}, tPlus = \frac{dOne + D}{2 \cdot dOne + D} \text{ in } ((0 < tMinus \land\\{}tMinus < \frac{1}{2} \land\\{}\frac{1}{2} < tPlus \land\\{}tPlus < 1) \land\\{}((piOne \in \operatorname{Icc}(0, tMinus)) \Rightarrow (\operatorname{asymmetricBayesRisk}(aOne, dOne, bOne, piOne) = piOne)) \land\\{}((piOne \in \operatorname{Icc}(tMinus, \frac{1}{2})) \Rightarrow (\operatorname{asymmetricBayesRisk}(aOne, dOne, bOne, piOne) = aOne + piOne \cdot (M - 2 \cdot aOne))) \land\\{}((piOne \in \operatorname{Icc}(\frac{1}{2}, tPlus)) \Rightarrow (\operatorname{asymmetricBayesRisk}(aOne, dOne, bOne, piOne) = M \cdot (1 - piOne) + (2 \cdot piOne - 1) \cdot dOne)) \land\\{}((piOne \in \operatorname{Icc}(tPlus, 1)) \Rightarrow (\operatorname{asymmetricBayesRisk}(aOne, dOne, bOne, piOne) = 1 - piOne)))) \land\\{}((0 < 2 \cdot aTwo \land\\{}2 \cdot aTwo < mTwo \land\\{}mTwo < 1 \land\\{}\frac{1}{2} < piTwo \land\\{}piTwo \leq 1) \Rightarrow \text{let } D = 1 - mTwo, L = mTwo - aTwo, U = 2 \cdot L + D, s = 2 \cdot piTwo - 1, c = mTwo \cdot (1 - piTwo), t = \frac{D \cdot (1 - s)}{2 \cdot s} \text{ in } ((\forall d \in \operatorname{Ico}(aTwo, L), \operatorname{asymmetricFiberRisk}(mTwo, aTwo, piTwo, d) = c + s \cdot \min (d, t)) \land\\{}((\operatorname{InjOn}(\operatorname{asymmetricFiberRisk}(mTwo, aTwo, piTwo), \operatorname{Ico}(aTwo, L))) \iff (piTwo \leq \frac{L + D}{2 \cdot L + D})) \land\\{}\frac{L + D}{2 \cdot L + D} = \frac{1 + \frac{D}{U}}{2} \land\\{}((\operatorname{InjOn}(\operatorname{asymmetricFiberRisk}(mTwo, aTwo, piTwo), \operatorname{Ico}(aTwo, L))) \Rightarrow (s \leq \frac{D}{U})) \land\\{}\operatorname{InjOn}(\operatorname{asymmetricFiberRisk}(mTwo, aTwo, \frac{L + D}{2 \cdot L + D}), \operatorname{Ico}(aTwo, L)) \land\\{}2 \cdot \frac{L + D}{2 \cdot L + D} - 1 = \frac{D}{U})).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/DecisionRisk/AsymmetricFamilyRiskInjectivity.asymmetric_family_risk_and_injective_queries` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive asymmetric masses with a at most d, the two likelihood crossings lie strictly on opposite sides of one half. Minimizing the error contribution separately at each output gives the four displayed affine pieces.

On a fixed-mass fiber and above prior one half, the risk is a positive affine multiple of min(d,t). It is strictly increasing when t is at least the fiber endpoint L, and otherwise it is constant on a nontrivial terminal interval. This yields the exact injectivity threshold and the maximal admissible slope.

## References

- Truth anchor: `D5/S3/Estimation/DecisionRisk/AsymmetricFamilyRiskInjectivity.asymmetricBayesRisk`
- Truth anchor: `D5/S3/Estimation/DecisionRisk/AsymmetricFamilyRiskInjectivity.asymmetricExperiment`
- Truth anchor: `D5/S3/Estimation/DecisionRisk/AsymmetricFamilyRiskInjectivity.asymmetricFiberRisk`
- Truth anchor: `D5/S3/Estimation/DecisionRisk/AsymmetricFamilyRiskInjectivity.asymmetric_family_risk_and_injective_queries`
- Dependency: [D5/S3/Estimation/SequentialDecisionRisk/FiniteDeficiencyRiskTransfer](../SequentialDecisionRisk/FiniteDeficiencyRiskTransfer.md)
