# Uniform complementary compression lifts

## Abstract

Full Kraus-product span gives an operator-norm bound on lifts that is independent of the reference dimension.

**Theorem 1.1 (Norm under simultaneous reindexing).**

Lean statement: `D5/S3/Quantum/Divergence/CompleteHockeyStick/UniformLift.norm_reindex`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/CompleteHockeyStick/UniformLift.norm_reindex` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Christoph Hirche; Ian George; Theshani Nuradha; Mark M. Wilde (2026). *Conditional contraction coefficients and their applications to quantum networks*. URL: <https://arxiv.org/abs/2608.27171v1>.

*Commentary.*

The Euclidean coordinate permutation is unitary, so conjugation by it preserves the operator norm.

**Definition 1.2 (Reference-first tensor order).**

Lean statement: `D5/S3/Quantum/Divergence/CompleteHockeyStick/UniformLift.referenceOutputOrder`

*Formalization.* `D5/S3/Quantum/Divergence/CompleteHockeyStick/UniformLift.referenceOutputOrder` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Christoph Hirche; Ian George; Theshani Nuradha; Mark M. Wilde (2026). *Conditional contraction coefficients and their applications to quantum networks*. URL: <https://arxiv.org/abs/2608.27171v1>.

*Commentary.*

The permutation moves the reference before the output and keeps the environment index last.

**Definition 1.3 (Amplified complementary compression).**

Lean statement: `D5/S3/Quantum/Divergence/CompleteHockeyStick/UniformLift.amplifiedComplementCompression`

*Formalization.* `D5/S3/Quantum/Divergence/CompleteHockeyStick/UniformLift.amplifiedComplementCompression` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Christoph Hirche; Ian George; Theshani Nuradha; Mark M. Wilde (2026). *Conditional contraction coefficients and their applications to quantum networks*. URL: <https://arxiv.org/abs/2608.27171v1>.

*Commentary.*

The amplified dilation compresses a joint reference and environment observable with identity on the output.

**Theorem 1.4 (Dimension-independent lift).**

Lean statement: `D5/S3/Quantum/Divergence/CompleteHockeyStick/UniformLift.exists_uniform_complement_lift_of_full_span`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/CompleteHockeyStick/UniformLift.exists_uniform_complement_lift_of_full_span` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Christoph Hirche; Ian George; Theshani Nuradha; Mark M. Wilde (2026). *Conditional contraction coefficients and their applications to quantum networks*. URL: <https://arxiv.org/abs/2608.27171v1>.

*Commentary.*

The compression sends environment matrix units to the Kraus products. When those products span the input matrix algebra, choose a lift of each input matrix unit. At every reference dimension each coefficient block of an input contraction has norm at most one. The sum of the norms of the fixed lifts, enlarged to at least one, bounds the norm of the amplified lift.

## References

- Truth anchor: `D5/S3/Quantum/Divergence/CompleteHockeyStick/UniformLift.amplifiedComplementCompression`
- Truth anchor: `D5/S3/Quantum/Divergence/CompleteHockeyStick/UniformLift.exists_uniform_complement_lift_of_full_span`
- Truth anchor: `D5/S3/Quantum/Divergence/CompleteHockeyStick/UniformLift.norm_reindex`
- Truth anchor: `D5/S3/Quantum/Divergence/CompleteHockeyStick/UniformLift.referenceOutputOrder`
- Dependency: [D5/S3/Quantum/Divergence/CanonicalRelativeModularModel](../CanonicalRelativeModularModel.md)
