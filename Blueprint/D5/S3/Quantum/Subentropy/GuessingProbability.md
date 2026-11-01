# Guessing probability

## Abstract

Finite positive operator-valued measurements define an honest supremum guessing probability.

**Theorem 1.1 (Identity-summing measurements preserve total trace pairing).**

$$\forall X \in FiniteType, B \in FiniteType, R \in Matrix\left(B, B, \mathbb{C}\right), M \in X \to Matrix\left(B, B, \mathbb{C}\right),\; trace\left(R\right) = 1 \land sum\left(M\right) = 1 \Rightarrow \sum_{x \in X} Re\left(trace\left(M\left(x\right) R\right)\right) = 1$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Subentropy/GuessingProbability.measurement_trace_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For finite label and matrix index types, a trace-one complex matrix has total real trace pairing one with any matrix family whose sum is the identity.

**Theorem 1.2 (Every POVM success probability lies between zero and one).**

$$\forall X \in FiniteType, B \in FiniteType, p \in X \to \mathbb{R}, rho \in X \to DensityState\left(B\right), M \in X \to Matrix\left(B, B, \mathbb{C}\right),\; \forall x \in X,\; 0 \le p\left(x\right) \land sum\left(p\right) = 1 \land \forall x \in X,\; PosSemidef\left(M\left(x\right)\right) \land sum\left(M\right) = 1 \Rightarrow 0 \le successProbability\left(p, rho, M\right) \land successProbability\left(p, rho, M\right) \le 1$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Subentropy/GuessingProbability.success_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For finite label and matrix index types, nonnegative weights summing to one, density states, and positive semidefinite measurement effects summing to the identity, the success probability lies in the closed unit interval.

**Definition 1.3 (The success probability of a labelled measurement).**

Lean statement: `D5/S3/Quantum/Subentropy/GuessingProbability.successProbability`

*Formalization.* `D5/S3/Quantum/Subentropy/GuessingProbability.successProbability` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Nilanjana Datta, Tony Dorlas, Richard Jozsa, Fabio Benatti (2014). *Properties of subentropy*. DOI: [10.1063/1.4882935](https://doi.org/10.1063/1.4882935). URL: <https://arxiv.org/abs/1310.1312>.

*Commentary.*

For a finite ensemble of density states rho_x with label weights p_x, successProbability is sum_x p_x Re Tr(M_x rho_x). The finite measurement has exactly one output for each guessed label.

**Definition 1.4 (The genuine POVM success set).**

Lean statement: `D5/S3/Quantum/Subentropy/GuessingProbability.successProbabilitySet`

*Formalization.* `D5/S3/Quantum/Subentropy/GuessingProbability.successProbabilitySet` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Nilanjana Datta, Tony Dorlas, Richard Jozsa, Fabio Benatti (2014). *Properties of subentropy*. DOI: [10.1063/1.4882935](https://doi.org/10.1063/1.4882935). URL: <https://arxiv.org/abs/1310.1312>.

*Commentary.*

successProbabilitySet consists of exactly the success probabilities of matrices M_x that are positive semidefinite and sum to the identity. No restriction to projective measurements is imposed.

**Definition 1.5 (The optimal guessing probability).**

Lean statement: `D5/S3/Quantum/Subentropy/GuessingProbability.pGuess`

*Formalization.* `D5/S3/Quantum/Subentropy/GuessingProbability.pGuess` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Nilanjana Datta, Tony Dorlas, Richard Jozsa, Fabio Benatti (2014). *Properties of subentropy*. DOI: [10.1063/1.4882935](https://doi.org/10.1063/1.4882935). URL: <https://arxiv.org/abs/1310.1312>.

*Commentary.*

pGuess is the supremum of successProbabilitySet. For nonnegative normalized ensemble weights, pGuess_bounds establishes that the set is nonempty and bounded above, and that 0<pGuess<=1 and 1-pGuess<=-log pGuess. Positivity follows from the deterministic measurement guessing a positive-weight label; normalization itself excludes an empty label type. The same proof establishes that any bound q<=1-successProbability valid for every labelled POVM implies q<=1-pGuess. It requires no attainment theorem for an optimal POVM.

These probability and supremum statements do not assert a bound on conditional subentropy. That further conclusion requires the separate matrix pinching-gap inequality for every POVM.

**Theorem 1.6 (Bounded positive guessing probability and supremum transfer).**

Lean statement: `D5/S3/Quantum/Subentropy/GuessingProbability.pGuess_bounds`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Subentropy/GuessingProbability.pGuess_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Nilanjana Datta, Tony Dorlas, Richard Jozsa, Fabio Benatti (2014). *Properties of subentropy*. DOI: [10.1063/1.4882935](https://doi.org/10.1063/1.4882935). URL: <https://arxiv.org/abs/1310.1312>.

*Commentary.*

For every finite nonnegative normalized ensemble, the genuine POVM success set is nonempty and bounded above, and its supremum lies in (0,1]. The logarithmic comparison 1-pGuess<=-log pGuess follows from log p<=p-1. Every bound q<=1-successProbability valid for all finite POVMs transfers to q<=1-pGuess by the defining least-upper-bound property. No optimal measurement or supremum attainment is assumed.

## References

- Truth anchor: `D5/S3/Quantum/Subentropy/GuessingProbability.measurement_trace_sum`
- Truth anchor: `D5/S3/Quantum/Subentropy/GuessingProbability.pGuess`
- Truth anchor: `D5/S3/Quantum/Subentropy/GuessingProbability.pGuess_bounds`
- Truth anchor: `D5/S3/Quantum/Subentropy/GuessingProbability.successProbability`
- Truth anchor: `D5/S3/Quantum/Subentropy/GuessingProbability.successProbabilitySet`
- Truth anchor: `D5/S3/Quantum/Subentropy/GuessingProbability.success_bounds`
- Dependency: [D5/S3/Quantum/Foundation/FiniteStateChannel](../Foundation/FiniteStateChannel.md)
- Dependency: [D5/S3/Quantum/Information/OrthogonalRecordEntropy](../Information/OrthogonalRecordEntropy.md)
