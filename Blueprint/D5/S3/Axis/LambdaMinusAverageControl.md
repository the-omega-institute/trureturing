# Diagonal Control of the Contraction-Face Average

## Abstract

The diagonal prime-axis sum controls the contraction-face average with the exact golden scale.

**Theorem 1.1 (The diagonal prime-axis average transfers to the contraction face).**

$$\begin{aligned}\forall x: \mathbb{N}, lambdaMinusPrimeAxisSummatory\left(x\right) := \sum_{p < x+1, p \text{prime}} \sum_{0 \leq n \leq x} \operatorname{if}(p \in \operatorname{support}(\operatorname{factorization}(n)), betaContraction\left(\operatorname{factorization}(n)\left(p\right)\right) \cdot \operatorname{log}(p), 0);\\\forall s: \mathbb{C}, 1 < \Re(s),\\{}\operatorname{LSeries}(lambdaMinus, s) = \zeta(s) \cdot lambdaMinusAxisSeries\left(s\right) \land\\{}(\forall x: \mathbb{N}, \sum_{0 \leq n \leq x} lambdaMinus\left(n\right) = lambdaMinusPrimeAxisSummatory\left(x\right)) \land\\{}(\operatorname{Tendsto}((x: \mathbb{N}) \mapsto \frac{lambdaMinusPrimeAxisSummatory\left(x\right)}{(x:\mathbb{R}) \cdot \operatorname{log}(x)}, atTop, \operatorname{nhds}(\psi^{2})) \Rightarrow \operatorname{Tendsto}((x: \mathbb{N}) \mapsto \frac{\sum_{0 \leq n \leq x} lambdaMinus\left(n\right)}{(x:\mathbb{R}) \cdot \operatorname{log}(x)}, atTop, \operatorname{nhds}(\psi^{2}))) \land\\{}betaContraction\left(1\right) = \psi^{2}.\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Axis/LambdaMinusAverageControl.lambda_minus_average_diagonal_control` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The diagonal summatory function is assembled prime-first. For each prime below the cutoff, it sums the contraction reading of that prime's factorization exponent over the integers below the cutoff.

Finite-sum interchange proves that this independently assembled diagonal quantity is exactly the summatory lambdaMinus function. Consequently, the displayed diagonal asymptotic premise transfers without loss to the contraction-face average.

The existing Dirichlet-series theorem supplies the zeta factor. The first contraction exponent is evaluated exactly as the square of the golden conjugate; the decimal approximation and finite-window measurement are empirical remarks and are not theorem conjuncts.

The reverse analytic-information direction remains an open semantic status remark in the source and is not encoded as a claim of formal unprovability.

## References

- Truth anchor: `D5/S3/Axis/LambdaMinusAverageControl.lambda_minus_average_diagonal_control`
- Dependency: [D5/S1/Deficit/Beatty/BetaBeattyClosedForms](../../S1/Deficit/Beatty/BetaBeattyClosedForms.md)
- Dependency: [D5/S3/Axis/LambdaMinusDirichletSeries](LambdaMinusDirichletSeries.md)
