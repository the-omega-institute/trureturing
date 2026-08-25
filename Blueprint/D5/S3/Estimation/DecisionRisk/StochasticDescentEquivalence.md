# Stochastic Descent Equivalence

## Abstract

A discrete transition law descends to the effective readout image exactly when its observed rows are constant on readout fibers.

**Theorem 1.1 (Stochastic descent is equivalent to strong lumpability).**

$$\begin{gathered}\forall X, B: \operatorname{Type},\\{}q: X \to B, K: X \to \operatorname{PMF}(X),\\{}\operatorname{ListTFAE}({[\exists Kbar: \operatorname{range}(q) \to \operatorname{PMF}(\operatorname{range}(q)),\\{}\forall x: X, \operatorname{map}(K(x), q) = \operatorname{map}(Kbar(\operatorname{rangeFactorization}(q, x)), val),\\{}\forall x: X, y: X, q(x) = q(y) \Rightarrow \operatorname{map}(K(x), q) = \operatorname{map}(K(y), q),\\{}\exists L: \operatorname{range}(q) \to \operatorname{PMF}(B),\\{}\forall x: X, \operatorname{map}(K(x), q) = L(\operatorname{rangeFactorization}(q, x))]}).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/DecisionRisk/StochasticDescentEquivalence.stochastic_descent_equivalence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The source transition assigns a probability mass function on the state space to every current state. Mapping that law through q gives the one-step observed law.

The first clause constructs a transition law on the literal effective image of q. Its pushforward along the subtype inclusion recovers every one-step observed law.

The second clause is strong lumpability: states in one q-fiber have equal observed rows. The third clause factors those rows through the current effective readout without yet requiring an image-valued next state.

Canonical range factorization and range splitting construct the descended transition. No finiteness or nonemptiness assumption is needed.

## References

- Truth anchor: `D5/S3/Estimation/DecisionRisk/StochasticDescentEquivalence.stochastic_descent_equivalence`
