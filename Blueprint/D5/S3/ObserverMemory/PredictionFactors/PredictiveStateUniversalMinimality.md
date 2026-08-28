# Predictive State Universal Minimality

## Abstract

Every sufficient past statistic uniquely determines the canonical predictive state on its realized image.

**Theorem 1.1 (The predictive state is the coarsest sufficient past quotient).**

$$\begin{gathered}\forall P, R, L: \operatorname{Type},\\{}K: P \to L, r: P \to R, Kbar: R \to L,\\{}K = Kbar \circ r \Rightarrow\\{}\exists! f: \operatorname{range}(r) \to \operatorname{range}(K), \operatorname{rangeFactorization}(K) = f \circ \operatorname{rangeFactorization}(r).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/PredictionFactors/PredictiveStateUniversalMinimality.predictive_state_universal_minimality` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The future-law map supplies the canonical predictive state through its range factorization. If a statistic supports a predictor reproducing that law, there is exactly one map from the statistic's realized image to the future-law image that makes the canonical state factorization commute.

## References

- Truth anchor: `D5/S3/ObserverMemory/PredictionFactors/PredictiveStateUniversalMinimality.predictive_state_universal_minimality`
- Dependency: [D5/S3/ObserverMemory/PredictionFactors/CausalStateFactorization](CausalStateFactorization.md)
