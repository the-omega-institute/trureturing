# Canonical Predictive-State Sufficiency

## Abstract

The canonical conditional-future-law state makes the complete past and future conditionally independent.

**Theorem 1.1 (The predictive state retains every past influence on the future).**

$$\begin{gathered}\forall Past, Future: \operatorname{Type}, [\operatorname{Fintype}(Past)], [\operatorname{Fintype}(Future)],\\{}\pi: \operatorname{PMF}(Past), K: Past \to \operatorname{PMF}(Future),\\{}S := \operatorname{range}(K), \varepsilon: Past \to S := \operatorname{rangeFactorization}(K),\\{}J: \operatorname{Product}(Past, \operatorname{Product}(S, Future)) \to \mathbb{R} := \lambda \operatorname{Triple}(h, s, f), \operatorname{ite}(\varepsilon(h)=s, \operatorname{toReal}(\pi(h)) \cdot \operatorname{toReal}(K(h)(f)), 0),\\{}\forall h: Past, s: S, f: Future,\\{}J(\operatorname{Triple}(h, s, f)) \cdot \operatorname{marginal}(\operatorname{yFirstLaw}(J), s) = \operatorname{xyProjection}(J, \operatorname{Pair}(h, s)) \cdot \operatorname{xzProjection}(\operatorname{yFirstLaw}(J), \operatorname{Pair}(s, f)).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/PredictionFactors/CanonicalPredictiveStateSufficiency.canonical_predictive_state_is_sufficient` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Past and Future are finite alphabets. The process is constructed from a past prior and its conditional future PMF channel.

The map epsilon is the canonical range factorization of the complete conditional future law, matching the repository's causal-state carrier. The displayed cross-product equality is the finite joint-law criterion for conditional independence of past and future given S.

The proof identifies the induced law with a channel-generated Markov law and applies the frozen Markov channel theorem. No positive-support condition on the past prior is required.

## References

- Truth anchor: `D5/S3/ObserverMemory/PredictionFactors/CanonicalPredictiveStateSufficiency.canonical_predictive_state_is_sufficient`
- Dependency: [D5/S3/Entropy/Submodularity/MarkovDataProcessing](../../Entropy/Submodularity/MarkovDataProcessing.md)
