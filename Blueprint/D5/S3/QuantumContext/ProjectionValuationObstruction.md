# An Eighteen-Ray Projection-Valuation Obstruction

## Abstract

An exact eighteen-ray parity configuration obstructs binary projection valuations.

**Theorem 1.1 (Nine complete contexts have no binary projection valuation).**

$$\neg \exists v: P\to \{0,1\},\ \forall c\in C,\ \sum_{p \in C_{c}} v( p)=1.$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumContext/ProjectionValuationObstruction.projection_valuation_obstruction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The configuration consists of eighteen explicit integer ray representatives in complex dimension four and nine tetrads. The declarations ks_vectors_injective, ks_vectors_nonzero, and ray_norm_sq_exact audit the ray table. The exact integer code projectionCode is four times each normalized outer product. Kernel-checked integer identities then give trace one, nonzero, self-adjoint, and idempotent complex projections.

Every context map is injective. Its four rays are pairwise orthogonal, the corresponding projection products vanish, and the four projections sum exactly to the identity. The finite incidence certificate proves that every ray occurs in exactly two of the thirty-six context slots. The theorem projection_injective proves that the eighteen rank-one projections are pairwise distinct; ConfigurationProjection is their range, and labeledProjection embeds the ray table into it.

A binary valuation selecting exactly one projection in each context would make the sum of the nine context totals equal to nine. Regrouping the same terms by ray makes every contribution occur twice, so the total is even. The Lean proof exposes the nine exact equations and closes this parity contradiction arithmetically; it does not enumerate all binary functions or use an unchecked evaluator.

The general contextual obstruction is classical background; `D5/L/kochen1968problem` records that scope. The deposited theorem is the exact finite dimension-four projective certificate above: an instance-level obstruction on valuations of these actual projections. It does not assert the full classification in every dimension at least three, a Gleason representation theorem, or a qubit projection obstruction.

**Theorem 1.2 (The first eight contexts have an explicit valuation).**

$$eightContextValuation=(0,1,0,0,1,0,0,0,0,1,0,1,0,0,0,0,0,0),\ \forall c<8,\ \sum_{r \in C_{c}} eightContextValuation( r)=1.$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumContext/ProjectionValuationObstruction.eight_contexts_satisfiable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The explicit valuation selecting zero-based ray labels 1, 4, 9, and 11 gives total one in each of the first eight contexts. Its total in the ninth context is zero. Thus the local constraints are nonempty and remain jointly satisfiable until the final tetrad closes the odd parity cycle; the obstruction is not a consequence of an empty index family or malformed context data.

## References

- Truth anchor: `D5/S3/QuantumContext/ProjectionValuationObstruction.eight_contexts_satisfiable`
- Truth anchor: `D5/S3/QuantumContext/ProjectionValuationObstruction.projection_valuation_obstruction`
