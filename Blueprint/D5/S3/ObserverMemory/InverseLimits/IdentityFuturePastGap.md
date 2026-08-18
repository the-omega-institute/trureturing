# Identity Future and Past Gap

## Abstract

Identity readout retains every finite state, while infinite backward orbits retain only periodic states.

**Theorem 1.1 (Identity future completion exceeds the past core).**

$$\begin{gathered}\forall Y, [\operatorname{Fintype} Y],\\\tau: Y \to Y, \neg \operatorname{Bijective}(\tau) \Rightarrow\\(\forall y, z\in Y, R_{\operatorname{id}}(y, z) \Leftrightarrow y = z) \land\\Z_{\operatorname{id}} \equiv Y \land\\X_{\tau}^{-} \equiv P_{\tau} \land\\\operatorname{card}(P_{\tau}) < \operatorname{card}(Y) \land\\\operatorname{card}(X_{\tau}^{-}) < \operatorname{card}(Z_{\operatorname{id}}).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/InverseLimits/IdentityFuturePastGap.identity_future_completion_exceeds_past_core` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let Y be a finite state type and tau a self-map that is not a permutation. Define R for a readout by equality of every future readout along the iterates of tau, and define Z as the quotient of Y by R.

For the identity readout, coordinate zero already separates states. Thus R is equality and the quotient completion Z is equivalent to Y.

An infinite backward orbit is a sequence whose next coordinate maps to the current coordinate. Coordinate-zero evaluation identifies these orbits with the positive-period points P. Since tau is not a permutation, P has strictly fewer elements than Y, yielding the strict cardinality gap between the past and future completions.

The proof directly applies the repository's canonical backward-orbit bijection and Mathlib's kernel-range equivalence, finite periodic-point characterization, and cardinality transport. Repository and pinned-Mathlib searches found no theorem combining all five clauses. Neither Loogle nor LeanSearch was installed in the worker environment.

## References

- Truth anchor: `D5/S3/ObserverMemory/InverseLimits/IdentityFuturePastGap.identity_future_completion_exceeds_past_core`
- Dependency: [D5/S3/ObserverMemory/InverseLimits/BackwardOrbitCore](BackwardOrbitCore.md)
- Dependency: [D5/S3/ObserverMemory/Prediction/ItineraryCompletion](../Prediction/ItineraryCompletion.md)
