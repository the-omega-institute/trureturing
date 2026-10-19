# Guessing probability

## Abstract

Finite positive operator-valued measurements define an honest supremum guessing probability.

**Definition 1.1 (The success probability of a labelled measurement).**

Lean statement: `D5/S3/Quantum/Subentropy/GuessingProbability.successProbability`

*Formalization.* `D5/S3/Quantum/Subentropy/GuessingProbability.successProbability` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Nilanjana Datta, Tony Dorlas, Richard Jozsa, Fabio Benatti (2014). *Properties of subentropy*. DOI: [10.1063/1.4882935](https://doi.org/10.1063/1.4882935). URL: <https://arxiv.org/abs/1310.1312>.

*Commentary.*

For a finite ensemble of density states rho_x with label weights p_x, successProbability is sum_x p_x Re Tr(M_x rho_x). The finite measurement has exactly one output for each guessed label.

**Definition 1.2 (The genuine POVM success set).**

Lean statement: `D5/S3/Quantum/Subentropy/GuessingProbability.successProbabilitySet`

*Formalization.* `D5/S3/Quantum/Subentropy/GuessingProbability.successProbabilitySet` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Nilanjana Datta, Tony Dorlas, Richard Jozsa, Fabio Benatti (2014). *Properties of subentropy*. DOI: [10.1063/1.4882935](https://doi.org/10.1063/1.4882935). URL: <https://arxiv.org/abs/1310.1312>.

*Commentary.*

successProbabilitySet consists of exactly the success probabilities of matrices M_x that are positive semidefinite and sum to the identity. No restriction to projective measurements is imposed.

**Definition 1.3 (The optimal guessing probability).**

Lean statement: `D5/S3/Quantum/Subentropy/GuessingProbability.pGuess`

*Formalization.* `D5/S3/Quantum/Subentropy/GuessingProbability.pGuess` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Nilanjana Datta, Tony Dorlas, Richard Jozsa, Fabio Benatti (2014). *Properties of subentropy*. DOI: [10.1063/1.4882935](https://doi.org/10.1063/1.4882935). URL: <https://arxiv.org/abs/1310.1312>.

*Commentary.*

pGuess is the supremum of successProbabilitySet. For nonnegative normalized ensemble weights, pGuess_bounds establishes that the set is nonempty and bounded above, and that 0<pGuess<=1 and 1-pGuess<=-log pGuess. Positivity follows from the deterministic measurement guessing a positive-weight label; normalization itself excludes an empty label type. The same proof establishes that any bound q<=1-successProbability valid for every labelled POVM implies q<=1-pGuess. It requires no attainment theorem for an optimal POVM.

These probability and supremum statements do not assert a bound on conditional subentropy. That further conclusion requires the separate matrix pinching-gap inequality for every POVM.

**Theorem 1.4 (Bounded positive guessing probability and supremum transfer).**

Lean statement: `D5/S3/Quantum/Subentropy/GuessingProbability.pGuess_bounds`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Subentropy/GuessingProbability.pGuess_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Nilanjana Datta, Tony Dorlas, Richard Jozsa, Fabio Benatti (2014). *Properties of subentropy*. DOI: [10.1063/1.4882935](https://doi.org/10.1063/1.4882935). URL: <https://arxiv.org/abs/1310.1312>.

*Commentary.*

For every finite nonnegative normalized ensemble, the genuine POVM success set is nonempty and bounded above, and its supremum lies in (0,1]. The logarithmic comparison 1-pGuess<=-log pGuess follows from log p<=p-1. Every bound q<=1-successProbability valid for all finite POVMs transfers to q<=1-pGuess by the defining least-upper-bound property. No optimal measurement or supremum attainment is assumed.

## References

- Truth anchor: `D5/S3/Quantum/Subentropy/GuessingProbability.pGuess`
- Truth anchor: `D5/S3/Quantum/Subentropy/GuessingProbability.pGuess_bounds`
- Truth anchor: `D5/S3/Quantum/Subentropy/GuessingProbability.successProbability`
- Truth anchor: `D5/S3/Quantum/Subentropy/GuessingProbability.successProbabilitySet`
- Dependency: [D5/S3/Quantum/Foundation/FiniteStateChannel](../Foundation/FiniteStateChannel.md)
- Dependency: [D5/S3/Quantum/Information/OrthogonalRecordEntropy](../Information/OrthogonalRecordEntropy.md)
