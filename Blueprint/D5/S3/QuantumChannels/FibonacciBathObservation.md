# A minimal record of the qutrit ground-state observation

## Abstract

The six-level Fibonacci Gibbs bath has a minimum lossless ground-state record of three outcomes.

Wheeler's discussion of apparatus-elicited yes-or-no answers in Chapter 19, §19.2 supplies the historical context. Here the binary target X is whether the outgoing qutrit is in its ground state. B is the outgoing bath basis readout and T is produced from B by a finite row-stochastic readout. Shannon's finite entropy and conditional entropy supply the information measure. The formal argument uses the repository's Markov equality and conditional probability profile theorems.

A second record problem compares the outgoing bath itself with the input Gibbs state. Summing the terminal joint table over qutrit levels gives the outgoing bath masses (0, 88, 25, 28)/141 on groups consisting of level 0, levels 1–3, level 4 and level 5. The same groups have Gibbs masses (48, 66, 15, 12)/141. The ratio is constant within each group and equals 0, 4/3, 5/3 or 7/3. The exact diagonal memory theorem, DiagonalExperiment.sharp_entropy_dimension, therefore requires four memory dimensions to preserve Umegaki relative entropy to the input Gibbs state under a CPTP encoder. Recording the ratio as an orthogonal state attains dimension four.

**Theorem 1.1 (Gibbs preparation and an energy-conserving unitary).**

Lean statement: `D5/S3/QuantumChannels/FibonacciBathObservation.terminalJoint_gibbs_implementation`

*Proof.* Machine-checked in Lean as `D5/S3/QuantumChannels/FibonacciBathObservation.terminalJoint_gibbs_implementation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Frederik vom Ende (2022). *Which bath Hamiltonians matter for thermal operations?*. DOI: [10.1063/5.0117534](https://doi.org/10.1063/5.0117534). URL: <https://arxiv.org/abs/2207.11189v4>.

*Acknowledgement.* John Archibald Wheeler (1999). *Information, Physics, Quantum: The Search for Links*. DOI: [10.1201/9780429500459-19](https://doi.org/10.1201/9780429500459-19). URL: <https://cqi.inf.usi.ch/qic/wheeler.pdf>.

*Commentary.*

The qutrit has energies 0, 1 and 2 and starts with populations (0, 2/3, 1/3). The independently supplied bath has energies 0 through 5 with multiplicities (1, 1, 2, 3, 5, 8), at inverse temperature log 2. The theorem identifies the appended state with the matrix-exponential Gibbs state of the diagonal bath Hamiltonian. The existing permutation is unitary and conserves total energy.

**Theorem 1.2 (Exact terminal joint state).**

Lean statement: `D5/S3/QuantumChannels/FibonacciBathObservation.terminalJoint_eq_diagonal`

*Proof.* Machine-checked in Lean as `D5/S3/QuantumChannels/FibonacciBathObservation.terminalJoint_eq_diagonal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Frederik vom Ende (2022). *Which bath Hamiltonians matter for thermal operations?*. DOI: [10.1063/5.0117534](https://doi.org/10.1063/5.0117534). URL: <https://arxiv.org/abs/2207.11189v4>.

*Commentary.*

The entire joint matrix is diagonal. In increasing bath-energy order, its three qutrit rows have per-basis-coordinate numerators (0, 64, 32, 16, 8, 4), (0, 0, 0, 0, 0, 2) and (0, 0, 0, 0, 2, 1), all divided by 282. Lean's kernel checks the rational table against the actual permutation.

**Theorem 1.3 (Equality of mutual information and posterior preservation).**

Lean statement: `D5/S3/QuantumChannels/FibonacciBathObservation.mutualInformation_eq_iff_preservesGroundPosterior`

*Proof.* Machine-checked in Lean as `D5/S3/QuantumChannels/FibonacciBathObservation.mutualInformation_eq_iff_preservesGroundPosterior` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Claude E. Shannon (1948). *A Mathematical Theory of Communication*. URL: <https://people.math.harvard.edu/~ctm/home/text/others/shannon/entropy/entropy.pdf>.

*Commentary.*

For any finite joint law of X and B with X binary, the row-stochastic readout gives a Markov chain X → B → T. The equality I(X; T) = I(X; B) holds exactly when P(X = true | B = b) equals P(X = true | T = t) on every positive joint event (b, t). The proof applies the equality case of Markov data processing and reduces equality of Bernoulli laws to their true probabilities.

**Theorem 1.4 (Unique decoder on the positive record support).**

Lean statement: `D5/S3/QuantumChannels/FibonacciBathObservation.existsUnique_surjective_recordDecoder`

*Proof.* Machine-checked in Lean as `D5/S3/QuantumChannels/FibonacciBathObservation.existsUnique_surjective_recordDecoder` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Suppose distinct posterior values label the classes and every class occurs with positive probability. A posterior-preserving randomized record has a unique surjective decoder from its positive-probability symbols onto the classes. For every positive event (b, t), that decoder sends t to the class of b. The proof uses the conditional probability profile theorem on the positive joint support.

**Theorem 1.5 (Posterior determined by the bath-energy class).**

Lean statement: `D5/S3/QuantumChannels/FibonacciBathObservation.groundPosterior_eq_classRate`

*Proof.* Machine-checked in Lean as `D5/S3/QuantumChannels/FibonacciBathObservation.groundPosterior_eq_classRate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Positive outcomes at levels 1 through 3 have one class, level 4 has a second class and level 5 has a third class. The bottom level has zero outgoing mass and is assigned to the first class.

**Theorem 1.6 (The three ground-state posteriors).**

Lean statement: `D5/S3/QuantumChannels/FibonacciBathObservation.posteriorRate_values`

*Proof.* Machine-checked in Lean as `D5/S3/QuantumChannels/FibonacciBathObservation.posteriorRate_values` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In class order the ground-state probabilities are 1, 4/5 and 4/7.

**Theorem 1.7 (Three outcomes are necessary for exact posterior preservation).**

Lean statement: `D5/S3/QuantumChannels/FibonacciBathObservation.sixLevel_record_minimal`

*Proof.* Machine-checked in Lean as `D5/S3/QuantumChannels/FibonacciBathObservation.sixLevel_record_minimal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every finite randomized readout preserving the terminal ground-state posterior has at least three positive-probability symbols, since its positive support surjects onto the three realized posterior classes.

**Theorem 1.8 (Three outcomes are necessary for equality of mutual information).**

Lean statement: `D5/S3/QuantumChannels/FibonacciBathObservation.sixLevel_record_minimal_of_mutualInformation_eq`

*Proof.* Machine-checked in Lean as `D5/S3/QuantumChannels/FibonacciBathObservation.sixLevel_record_minimal_of_mutualInformation_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Claude E. Shannon (1948). *A Mathematical Theory of Communication*. URL: <https://people.math.harvard.edu/~ctm/home/text/others/shannon/entropy/entropy.pdf>.

*Commentary.*

For the physical terminal law, equality of the record and full bath mutual information with the ground indicator implies the same three-outcome lower bound.

**Theorem 1.9 (A three-outcome measurement attains the minimum).**

Lean statement: `D5/S3/QuantumChannels/FibonacciBathObservation.sixLevel_classReadout_attains`

*Proof.* Machine-checked in Lean as `D5/S3/QuantumChannels/FibonacciBathObservation.sixLevel_classReadout_attains` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Measure in the bath energy basis and report the deterministic class of the measured coordinate. The classes have outgoing probabilities 88/141, 25/141 and 28/141. The readout has three positive outcomes, preserves every positive-event posterior and attains equality of mutual information.

## References

- Truth anchor: `D5/S3/QuantumChannels/FibonacciBathObservation.existsUnique_surjective_recordDecoder`
- Truth anchor: `D5/S3/QuantumChannels/FibonacciBathObservation.groundPosterior_eq_classRate`
- Truth anchor: `D5/S3/QuantumChannels/FibonacciBathObservation.mutualInformation_eq_iff_preservesGroundPosterior`
- Truth anchor: `D5/S3/QuantumChannels/FibonacciBathObservation.posteriorRate_values`
- Truth anchor: `D5/S3/QuantumChannels/FibonacciBathObservation.sixLevel_classReadout_attains`
- Truth anchor: `D5/S3/QuantumChannels/FibonacciBathObservation.sixLevel_record_minimal`
- Truth anchor: `D5/S3/QuantumChannels/FibonacciBathObservation.sixLevel_record_minimal_of_mutualInformation_eq`
- Truth anchor: `D5/S3/QuantumChannels/FibonacciBathObservation.terminalJoint_eq_diagonal`
- Truth anchor: `D5/S3/QuantumChannels/FibonacciBathObservation.terminalJoint_gibbs_implementation`
- Dependency: [D5/S3/Entropy/Submodularity/MutualInformationChainRule](../Entropy/Submodularity/MutualInformationChainRule.md)
- Dependency: [D5/S3/ObserverMemory/PredictionFactors/ConditionalProbabilityProfileMinimality](../ObserverMemory/PredictionFactors/ConditionalProbabilityProfileMinimality.md)
- Dependency: [D5/S3/Quantum/Decoherence/GibbsBathBandwidth](../Quantum/Decoherence/GibbsBathBandwidth.md)
- Dependency: [D5/S3/Quantum/ProcessReconstruction/GibbsHiddenProcess](../Quantum/ProcessReconstruction/GibbsHiddenProcess.md)
- Dependency: [D5/S3/QuantumChannels/ThermalOperationDegeneracyRefutation](ThermalOperationDegeneracyRefutation.md)
