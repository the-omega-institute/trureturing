# Typed Prime-Language Hierarchy

## Abstract

Prime-observation languages have strict comparisons only on shared state types.

**Theorem 1.1 (Equal radical and support do not determine multiplicity).**

$$rad\left(2\right) = rad\left(4\right) \land \left(supp\left(\nu\left(2\right)\right) = supp\left(\nu\left(4\right)\right) \land \nu\left(2\right) \neq \nu\left(4\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/ObservationOrder/TypedPrimeLanguageHierarchy.support_multiplicity_witness` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The positive naturals two and four have the same radical and the same prime support, while their exponent tables differ at two.

This is the named witness used to refute recovery of valuations from support alone.

**Theorem 1.2 (Support is strictly coarser than valuation).**

$$Refines\left(primeSupportLanguage, primeExponentLanguage\right) \land \neg{Refines\left(primeExponentLanguage, primeSupportLanguage\right)}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/ObservationOrder/TypedPrimeLanguageHierarchy.support_strictly_coarser_than_valuation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Finite support factors through the canonical prime-exponent language. The reverse factor would identify the exponent tables of two and four, contradicting the named witness.

Both readouts have the common state type of positive naturals; no cross-type comparison is asserted.

**Theorem 1.3 (Equal prime diagonals do not determine relative phase).**

$$rhoPlus \neq rhoMinus \land \left(qubitPrimeDiagonalLanguage\left(rhoPlus\right) = qubitPrimeDiagonalLanguage\left(rhoMinus\right) \land qubitOperatorLanguage\left(rhoPlus\right) \neq qubitOperatorLanguage\left(rhoMinus\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/ObservationOrder/TypedPrimeLanguageHierarchy.relative_phase_density_witness` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The equal-superposition density operator and its Pauli-Z phase flip are positive trace-one matrices with equal diagonal entries.

Canonical prime dephasing therefore gives the same matrix, while the full operator readout distinguishes their off-diagonal entries.

**Theorem 1.4 (Prime-diagonal readout is strictly coarser than operators).**

$$Refines\left(qubitPrimeDiagonalLanguage, qubitOperatorLanguage\right) \land \neg{Refines\left(qubitOperatorLanguage, qubitPrimeDiagonalLanguage\right)}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/ObservationOrder/TypedPrimeLanguageHierarchy.prime_diagonal_strictly_coarser_than_operator` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Prime dephasing factors through the full density-operator readout. The reverse factor is impossible because the named phase pair has one dephased output and two distinct operator outputs.

This theorem compares readouts only on qubit density states. The source's warning against a transport-free global order remains a metalevel typing statement and is intentionally not encoded.

## References

- Truth anchor: `D5/S3/ConceptDynamics/ObservationOrder/TypedPrimeLanguageHierarchy.prime_diagonal_strictly_coarser_than_operator`
- Truth anchor: `D5/S3/ConceptDynamics/ObservationOrder/TypedPrimeLanguageHierarchy.relative_phase_density_witness`
- Truth anchor: `D5/S3/ConceptDynamics/ObservationOrder/TypedPrimeLanguageHierarchy.support_multiplicity_witness`
- Truth anchor: `D5/S3/ConceptDynamics/ObservationOrder/TypedPrimeLanguageHierarchy.support_strictly_coarser_than_valuation`
- Dependency: [D5/S3/ConceptDynamics/ConceptJoinUniversal](../ConceptJoinUniversal.md)
- Dependency: [D5/S3/Factorization/ExponentCoordinates/PrimeExponentBijection](../../Factorization/ExponentCoordinates/PrimeExponentBijection.md)
- Dependency: [D5/S3/Quantum/Divergence/QuantumRelativeEntropyDefectComposition](../../Quantum/Divergence/QuantumRelativeEntropyDefectComposition.md)
- Dependency: [D5/S3/Quantum/FixedAlgebra/PrimeDephasingRefinementAbsorption](../../Quantum/FixedAlgebra/PrimeDephasingRefinementAbsorption.md)
- Dependency: [D5/S3/Quantum/QubitWitnesses](../../Quantum/QubitWitnesses.md)
