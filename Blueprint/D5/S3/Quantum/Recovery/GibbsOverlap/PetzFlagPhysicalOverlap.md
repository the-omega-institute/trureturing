# Conditional Gibbs and Petz overlap under the right partial trace

## Abstract

The two-flag Gibbs root fidelity is a normalized sum of block trace norms.

For a qutrit matrix Q and two effects Dᵢ summing to I, the joint input ρ has blocks Q/2 and the joint reference σ has blocks Dᵢ/3. Write ρ_A and σ_A for their right partial traces. For faithful joint states and marginals, the conditional Gibbs operator is G = exp(log σ + lift(log ρ_A − log σ_A)), where lift tensors with the flag identity. The normalized Gibbs state is G/(Re Tr G).

**Lemma 1.1 (The input marginal is Q).**

Lean statement: `D5/S3/Quantum/Recovery/GibbsOverlap/PetzFlagPhysicalOverlap.input_marginal`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/GibbsOverlap/PetzFlagPhysicalOverlap.input_marginal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The right partial trace sums the two copies of Q/2.

**Lemma 1.2 (The reference marginal is I/3).**

Lean statement: `D5/S3/Quantum/Recovery/GibbsOverlap/PetzFlagPhysicalOverlap.reference_marginal`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/GibbsOverlap/PetzFlagPhysicalOverlap.reference_marginal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The right partial trace sums Dᵢ/3 and the effects sum to I.

**Lemma 1.3 (Faithfulness of the joint input).**

Lean statement: `D5/S3/Quantum/Recovery/GibbsOverlap/PetzFlagPhysicalOverlap.input_faithful_density`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/GibbsOverlap/PetzFlagPhysicalOverlap.input_faithful_density` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

When Q is positive definite with trace one, the joint input has both properties.

**Lemma 1.4 (Faithfulness of the joint reference).**

Lean statement: `D5/S3/Quantum/Recovery/GibbsOverlap/PetzFlagPhysicalOverlap.reference_faithful_density`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/GibbsOverlap/PetzFlagPhysicalOverlap.reference_faithful_density` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Positive definite effects summing to I give a positive definite, trace-one joint reference.

**Lemma 1.5 (The Gibbs trace is the sum of the block traces).**

Lean statement: `D5/S3/Quantum/Recovery/GibbsOverlap/PetzFlagPhysicalOverlap.gibbsOperator_trace`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/GibbsOverlap/PetzFlagPhysicalOverlap.gibbsOperator_trace` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive definite effects summing to I and any qutrit matrix Q, Re Tr G = Z, where Z = Σᵢ Re Tr Ωᵢ and Ωᵢ = exp(log Dᵢ + log Q). On the faithful input domain, the scalar logarithm shifts from σ and σ_A cancel.

**Lemma 1.6 (The normalized Gibbs state is faithful).**

Lean statement: `D5/S3/Quantum/Recovery/GibbsOverlap/PetzFlagPhysicalOverlap.normalizedGibbs_faithful_density`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/GibbsOverlap/PetzFlagPhysicalOverlap.normalizedGibbs_faithful_density` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive definite effects summing to I and any qutrit matrix Q, the normalized Gibbs operator is positive definite and has trace one. Each block is the exponential of a self-adjoint matrix, and Z is positive.

**Lemma 1.7 (The ordinary Petz output is faithful).**

Lean statement: `D5/S3/Quantum/Recovery/GibbsOverlap/PetzFlagPhysicalOverlap.recovered_faithful_density`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/GibbsOverlap/PetzFlagPhysicalOverlap.recovered_faithful_density` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive definite effects summing to I and positive definite Q of trace one, ordinary Petz recovery of ρ_A against σ has blocks √Dᵢ Q √Dᵢ. The output is positive definite, and cycling the trace in each block gives total trace one.

**Theorem 1.8 (The block deficit is equivalent to failure of the root-fidelity bound).**

Lean statement: `D5/S3/Quantum/Recovery/GibbsOverlap/PetzFlagPhysicalOverlap.rootFidelity_lt_sqrt_partition_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/GibbsOverlap/PetzFlagPhysicalOverlap.rootFidelity_lt_sqrt_partition_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive definite effects summing to I and positive definite Q, root fidelity between G/Z and the ordinary Petz output on ρ_A equals Σᵢ ‖Kᵢ‖₁/√Z, where Kᵢ = √Ωᵢ √Dᵢ √Q. Thus it is strictly smaller than √Z exactly when Σᵢ (‖Kᵢ‖₁ − Re Tr Ωᵢ) < 0.

## References

- Truth anchor: `D5/S3/Quantum/Recovery/GibbsOverlap/PetzFlagPhysicalOverlap.gibbsOperator_trace`
- Truth anchor: `D5/S3/Quantum/Recovery/GibbsOverlap/PetzFlagPhysicalOverlap.input_faithful_density`
- Truth anchor: `D5/S3/Quantum/Recovery/GibbsOverlap/PetzFlagPhysicalOverlap.input_marginal`
- Truth anchor: `D5/S3/Quantum/Recovery/GibbsOverlap/PetzFlagPhysicalOverlap.normalizedGibbs_faithful_density`
- Truth anchor: `D5/S3/Quantum/Recovery/GibbsOverlap/PetzFlagPhysicalOverlap.recovered_faithful_density`
- Truth anchor: `D5/S3/Quantum/Recovery/GibbsOverlap/PetzFlagPhysicalOverlap.reference_faithful_density`
- Truth anchor: `D5/S3/Quantum/Recovery/GibbsOverlap/PetzFlagPhysicalOverlap.reference_marginal`
- Truth anchor: `D5/S3/Quantum/Recovery/GibbsOverlap/PetzFlagPhysicalOverlap.rootFidelity_lt_sqrt_partition_iff`
- Dependency: [D5/S3/Quantum/CommutingMidpoint/Fidelity](../../CommutingMidpoint/Fidelity.md)
- Dependency: [D5/S3/Quantum/Entanglement/PermutationCriteria/BellBlocks](../../Entanglement/PermutationCriteria/BellBlocks.md)
- Dependency: [D5/S3/Quantum/Recovery/BKMFlagRefinementPetz](../BKMFlagRefinementPetz.md)
