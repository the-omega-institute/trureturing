# Approximate Simulation Without Exact Attainment

## Abstract

Zero nonnegative simulation infimum is approximate domination, while a nonclosed family of stochastic postprocessors need not contain an exact member.

**Theorem 1.1 (Zero simulation defect need not be attained).**

$$\begin{aligned}(\forall S: \operatorname{Type}, e: S \to \mathbb{R},\\\operatorname{Nonempty}\left(S\right) \land (\forall m: S, 0 \le \operatorname{e}\left(m\right)) \Rightarrow\\(\operatorname{sInf}\left(\{\operatorname{e}\left(m\right) \mid m \in S\}\right) = 0 \iff \forall epsilon: \mathbb{R}, 0 < epsilon \Rightarrow \exists m: S, \operatorname{e}\left(m\right) < epsilon)) \land\\\operatorname{let} K: \operatorname{FiniteMarkovKernel}\left(Unit, Unit\right), \operatorname{value}\left(K, star, star\right) = 1,\\L: \operatorname{FiniteMarkovKernel}\left(Unit, Bool\right), \operatorname{value}\left(L, star, b\right) = \operatorname{if}\left(b, 0, 1\right),\\M: \mathbb{N} \to \operatorname{FiniteMarkovKernel}\left(Unit, Bool\right), \operatorname{value}\left(M_{n}, star, b\right) = \operatorname{if}\left(b, \frac{1}{n+2}, 1-\frac{1}{n+2}\right),\\err_{n} = \operatorname{TV}\left(\operatorname{row}\left(L, star\right), \operatorname{channelOutput}\left(M_{n}, \operatorname{row}\left(K, star\right)\right)\right),\\\operatorname{sInf}\left(\{err_{n} \mid n \in \mathbb{N}\}\right) = 0 \land\\\neg \exists n: \mathbb{N}, \operatorname{row}\left(L, star\right) = \operatorname{channelOutput}\left(M_{n}, \operatorname{row}\left(K, star\right)\right).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/DataProcessing/ApproximateSimulationWithoutExactAttainment.approximate_simulation_without_exact_attainment` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any nonempty simulator class with a nonnegative error cost, infimum zero is equivalent to the existence of a simulator below every positive tolerance.

K is the deterministic experiment on the singleton observation space, and L is the deterministic Boolean target law concentrated at false. Both are constructed as finite Markov kernels.

The nth admissible simulator assigns mass 1/(n+2) to true and the remaining mass to false. Its total-variation simulation error is therefore exactly 1/(n+2).

These errors have infimum zero and become smaller than every positive tolerance, while positivity of 1/(n+2) rules out an exact simulator inside the same family.

## References

- Truth anchor: `D5/S3/Estimation/DataProcessing/ApproximateSimulationWithoutExactAttainment.approximate_simulation_without_exact_attainment`
- Dependency: [D5/S3/Estimation/DecisionRisk/DescentDefectBounds](../DecisionRisk/DescentDefectBounds.md)
