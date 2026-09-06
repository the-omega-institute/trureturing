# The Observer Read-Update Commutator

## Abstract

The represented read-update commutator is the predecessor read-value difference times the predecessor amplitude.

For an arbitrary index type I, a register is a function from I to the complex numbers. A permutation tau acts by pullback: observerUpdate(tau,psi)(i) = psi(tau inverse(i)). The read operator multiplies pointwise: readObservable(f,psi)(i) = f(i) times psi(i). These are the represented operators of `D5/S3/Quantum/ObserverAlgebra`.

**Theorem 1.1 (The commutator as a translated observable difference).**

$$\forall I,\ \forall \tau \in \operatorname{Perm}\left(I\right),\ \forall f, \psi:I\to\mathbb{C},\ \operatorname{observerUpdate}\left(\tau, \operatorname{readObservable}\left(f, \psi\right)\right) - \operatorname{readObservable}\left(f, \operatorname{observerUpdate}\left(\tau, \psi\right)\right) = (i \mapsto (f(\tau^{-1}(i)) - f(i)) \cdot \psi(\tau^{-1}(i)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/ObserverCommutator.observer_read_update_commutator_formula` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Julian Schwinger (1960). *Unitary Operator Bases*. DOI: [10.1073/pnas.46.4.570](https://doi.org/10.1073/pnas.46.4.570).

*Commentary.*

For every permutation tau of I and every pair of complex-valued functions f and psi on I, the difference between updating after reading and reading after updating is the function sending i to (f(tau inverse(i)) - f(i)) times psi(tau inverse(i)). No finiteness or inhabitability hypothesis on I and no nonvanishing hypothesis on psi are required.

Function extensionality reduces the equality to an entrywise identity. Unfolding the two operators produces two products with the same predecessor amplitude, and distributivity gives the formula. It determines the commutator even when it vanishes. Schwinger's finite unitary-operator construction is background for the represented read-update setting; the identity here is a repository derivation for an arbitrary index type.

## References

- Truth anchor: `D5/S3/Quantum/ObserverCommutator.observer_read_update_commutator_formula`
- Dependency: [D5/S3/Quantum/ObserverAlgebra](ObserverAlgebra.md)
- Narrative reference: [D5/S3/Quantum/ObserverAlgebra](ObserverAlgebra.md)
