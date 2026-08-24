# Conditional Probability Profile Minimality

## Abstract

The complete conditional probability profile is the minimal predictive concept.

**Theorem 1.1 (Conditional probability profiles form the minimal sufficient concept).**

$$\begin{gathered}\forall X, Y, B: \operatorname{Type},\\{}[\operatorname{Fintype}(X)],\\{}K: X \to \operatorname{PMF}\left(Y\right), r: X \to B,\\{}Kbar: B \to \operatorname{PMF}\left(Y\right), K = Kbar \circ r \Rightarrow\\{}(\exists! phi: \operatorname{range}\left(r\right) \to \operatorname{range}\left(K\right),\\{}\operatorname{rangeFactorization}\left(K\right) = phi \circ \operatorname{rangeFactorization}\left(r\right) \land\\{}(\forall s: \operatorname{range}\left(r\right), \operatorname{val}\left(phi(s)\right) = Kbar(\operatorname{val}\left(s\right))) \land\\{}K = \operatorname{val} \circ phi \circ \operatorname{rangeFactorization}\left(r\right)) \land\\{}\forall x, x': X, K(x) \neq K(x') \Rightarrow r(x) \neq r(x').\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/PredictionFactors/ConditionalProbabilityProfileMinimality.conditional_probability_profile_is_minimal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A probability kernel K assigns every finite source state its complete conditional law in PMF(Y). An interface r is predictively sufficient when K factors as Kbar after r.

The realized conditional-law concept is the canonical range factorization of K. Every sufficient interface induces a unique map from its realized image onto this concept, and that map agrees with Kbar on every realized interface value.

Composing the induced map with inclusion into PMF(Y) recovers K itself. Thus the canonical object retains the whole conditional probability profile, rather than selecting one future outcome.

The final public clause states the corresponding separation law: two states with different conditional distributions cannot share an interface value in any sufficient concept.

## References

- Truth anchor: `D5/S3/ObserverMemory/PredictionFactors/ConditionalProbabilityProfileMinimality.conditional_probability_profile_is_minimal`
- Dependency: [D5/S3/ObserverMemory/PredictionFactors/CausalStateFactorization](CausalStateFactorization.md)
