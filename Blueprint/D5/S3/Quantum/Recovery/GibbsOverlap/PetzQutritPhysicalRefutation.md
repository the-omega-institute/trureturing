# A faithful counterexample to the conditional Gibbs root-fidelity inequality

## Abstract

A faithful two-flag qutrit refutes the conditional Gibbs root-fidelity bound.

**Theorem 1.1 (The faithful partial-trace counterexample).**

Lean statement: `D5/S3/Quantum/Recovery/GibbsOverlap/PetzQutritPhysicalRefutation.exists_faithful_qutrit_two_flag_petz_fidelity_failure`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/GibbsOverlap/PetzQutritPhysicalRefutation.exists_faithful_qutrit_two_flag_petz_fidelity_failure` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On a qutrit with a two-valued classical flag, take ρ with blocks Q/2 and σ with blocks D₁/3 and D₂/3 from the strict two-flag deficit. Both joint states are positive definite with trace one. Their right partial traces are Q and I/3, respectively, and both are positive definite. Let G be the unnormalized conditional Gibbs operator and let P be ordinary Petz recovery against σ of the actual input marginal Q. Both G/(Re Tr G) and P are positive definite with trace one. The block deficit proves that their root fidelity is strictly less than √(Re Tr G).

**Theorem 1.2 (The universal lower bound is false).**

Lean statement: `D5/S3/Quantum/Recovery/GibbsOverlap/PetzQutritPhysicalRefutation.result`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/GibbsOverlap/PetzQutritPhysicalRefutation.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The claim asserts root fidelity at least √(Re Tr G) for all faithful trace-one joint inputs and references with faithful marginals on this qutrit–flag system. The faithful example gives its negation. The sharp constant for the trace-distance recovery inequality remains open.

## References

- Truth anchor: `D5/S3/Quantum/Recovery/GibbsOverlap/PetzQutritPhysicalRefutation.exists_faithful_qutrit_two_flag_petz_fidelity_failure`
- Truth anchor: `D5/S3/Quantum/Recovery/GibbsOverlap/PetzQutritPhysicalRefutation.result`
- Dependency: [D5/S3/Quantum/CommutingMidpoint/Fidelity](../../CommutingMidpoint/Fidelity.md)
- Dependency: [D5/S3/Quantum/Divergence/GibbsVariationalIdentity](../../Divergence/GibbsVariationalIdentity.md)
- Dependency: [D5/S3/Quantum/Entanglement/ConicalDesignConcurrenceComparability](../../Entanglement/ConicalDesignConcurrenceComparability.md)
- Dependency: [D5/S3/Quantum/FixedAlgebra/RecordFixedAlgebraDecomposition](../../FixedAlgebra/RecordFixedAlgebraDecomposition.md)
- Dependency: [D5/S3/Quantum/Foundation/FiniteTraceDistance](../../Foundation/FiniteTraceDistance.md)
- Dependency: [D5/S3/Quantum/Information/PartialTraceMutualInformation](../../Information/PartialTraceMutualInformation.md)
- Dependency: [D5/S3/Quantum/Recovery/BKMRelativeDensity](../BKMRelativeDensity.md)
- Dependency: [D5/S3/Quantum/Recovery/GibbsOverlap/PetzQutritFirstFlag](PetzQutritFirstFlag.md)
