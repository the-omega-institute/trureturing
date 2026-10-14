# The exact EJM inflation score

## Abstract

Exact centered expectations for the 2×2×4 EJM inflation certificate.

The 16 ten-node and 16 nine-node marginal maps use the pinned upstream party and event order. The source supports of each head and its own tail are disjoint. Maps starting with B,A,C use the actual party-labelled probability and the EJM target's A,B symmetry; no symmetry is assumed of the hidden-variable responses or the full lift.

**Theorem 1.1 (Distinct triangle-block nodes).**

Lean statement: `D5/S3/Quantum/Entanglement/EJMInflationScore.triangle_injective`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/EJMInflationScore.triangle_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each original ten-node marginal map is injective, supplying the exact tuple adapter used by both the zero-expectation and noisy-distribution consumers.

**Theorem 1.2 (Distinct singleton-block nodes).**

Lean statement: `D5/S3/Quantum/Entanglement/EJMInflationScore.singleton_injective`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/EJMInflationScore.singleton_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each original nine-node marginal map is injective.

**Theorem 1.3 (Independent triangle head and tail).**

Lean statement: `D5/S3/Quantum/Entanglement/EJMInflationScore.triangle_support_disjoint`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/EJMInflationScore.triangle_support_disjoint` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The actual source-copy supports of every three-node triangle head and its seven-node tail are disjoint.

**Theorem 1.4 (Independent singleton head and tail).**

Lean statement: `D5/S3/Quantum/Entanglement/EJMInflationScore.singleton_support_disjoint`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/EJMInflationScore.singleton_support_disjoint` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The actual source-copy supports of every singleton head and its eight-node tail are disjoint.

**Theorem 1.5 (Party-labelled head mass for any represented distribution).**

Lean statement: `D5/S3/Quantum/Entanglement/EJMInflationScore.triangle_head_mass_of_represents`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/EJMInflationScore.triangle_head_mass_of_represents` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any represented triangle probability, each head marginal equals that probability read in actual A,B,C party order. A map beginning B,A,C is reordered by its recorded party labels; no A,B symmetry of the probability is needed.

**Theorem 1.6 (Uniform head mass from the actual one-party marginals).**

Lean statement: `D5/S3/Quantum/Entanglement/EJMInflationScore.singleton_head_mass_of_uniform`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/EJMInflationScore.singleton_head_mass_of_uniform` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Uniform A and B one-party marginals suffice for every singleton head to have mass 1/4. The full represented triangle probability can be noisy and asymmetric.

**Theorem 1.7 (Singleton cancellation for a noisy represented distribution).**

Lean statement: `D5/S3/Quantum/Entanglement/EJMInflationScore.singleton_block_expectation_zero_of_uniform`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/EJMInflationScore.singleton_block_expectation_zero_of_uniform` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every original singleton block has zero lifted expectation under any represented probability with the specified uniform one-party marginals. This separates the exact singleton cancellation from the triangle-block error bound in the physical source-noise consumer.

**Theorem 1.8 (Three-node centered expectation).**

Lean statement: `D5/S3/Quantum/Entanglement/EJMInflationScore.triangle_block_expectation_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/EJMInflationScore.triangle_block_expectation_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary integer coefficients, 256 times the ten-node score cancels its exact contraction against the target numerators 25, 1 and 5. The probability denominator is 256.

**Theorem 1.9 (One-node centered expectation).**

Lean statement: `D5/S3/Quantum/Entanglement/EJMInflationScore.singleton_block_expectation_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/EJMInflationScore.singleton_block_expectation_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The uniform singleton probability is 1/4, giving the exact contraction factor 64 against the remaining eight coordinates.

**Theorem 1.10 (All 32 blocks cancel).**

Lean statement: `D5/S3/Quantum/Entanglement/EJMInflationScore.score_expectation_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/EJMInflationScore.score_expectation_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The original coefficient functions remain arbitrary in this theorem. Their actual finite positivity proof is supplied by the certificate consumer, independently of the continuous-model expectation proof.

**Theorem 1.11 (Positive score excludes a local model).**

Lean statement: `D5/S3/Quantum/Entanglement/EJMInflationScore.positive_score_excludes_triangle_local`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/EJMInflationScore.positive_score_excludes_triangle_local` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An earned global integer bound of at least 1 contradicts the normalized nonnegative lifted law's zero score expectation. The strict positivity premise must be discharged for the exact coefficient functions.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/EJMInflationScore.positive_score_excludes_triangle_local`
- Truth anchor: `D5/S3/Quantum/Entanglement/EJMInflationScore.score_expectation_zero`
- Truth anchor: `D5/S3/Quantum/Entanglement/EJMInflationScore.singleton_block_expectation_zero`
- Truth anchor: `D5/S3/Quantum/Entanglement/EJMInflationScore.singleton_block_expectation_zero_of_uniform`
- Truth anchor: `D5/S3/Quantum/Entanglement/EJMInflationScore.singleton_head_mass_of_uniform`
- Truth anchor: `D5/S3/Quantum/Entanglement/EJMInflationScore.singleton_injective`
- Truth anchor: `D5/S3/Quantum/Entanglement/EJMInflationScore.singleton_support_disjoint`
- Truth anchor: `D5/S3/Quantum/Entanglement/EJMInflationScore.triangle_block_expectation_zero`
- Truth anchor: `D5/S3/Quantum/Entanglement/EJMInflationScore.triangle_head_mass_of_represents`
- Truth anchor: `D5/S3/Quantum/Entanglement/EJMInflationScore.triangle_injective`
- Truth anchor: `D5/S3/Quantum/Entanglement/EJMInflationScore.triangle_support_disjoint`
- Dependency: [D5/S3/Quantum/Entanglement/EJMWightedCancellation](EJMWightedCancellation.md)
- Dependency: [D5/S3/Quantum/Entanglement/ElegantJointMeasurementInflation](ElegantJointMeasurementInflation.md)
