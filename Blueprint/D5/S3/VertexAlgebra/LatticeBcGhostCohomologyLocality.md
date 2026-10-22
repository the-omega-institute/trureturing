# Scope

## Abstract

Uniform signed locality on the full original BRST quotient.

The carrier is the existing full OriginalCycles quotient by OriginalBoundaries for arbitrary original lattice data D and matrix H. The two states are fixed by their actual descended parity projections. One locality order annihilates the Koszul-signed commutator as a distribution of quotient linear maps: it is uniform over all integer mode pairs and all quotient inputs. No inverse, rank, eigenstate or global cutoff assumption is introduced.

**Theorem 1.1 (Cycle delta and the actual tensor commutator).**

Lean statement: `D5/S3/VertexAlgebra/LatticeBcGhostCohomologyLocality.iterated_cycle_val`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeBcGhostCohomologyLocality.iterated_cycle_val` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural iterate and every pair of integer indices, the cycle commutator evaluates to the corresponding tensor supercommutator. The induction retains both shifted integer indices.

**Theorem 1.2 (Evaluation on quotient representatives).**

Lean statement: `D5/S3/VertexAlgebra/LatticeBcGhostCohomologyLocality.iterated_quotient_mk`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeBcGhostCohomologyLocality.iterated_quotient_mk` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every delta iterate of the quotient commutator on an actual cycle class is the quotient image of the cycle iterate. Bilinear product_mk and the quotient linear map transport each shifted term.

**Theorem 1.3 (Uniform locality of actual parity projections).**

Lean statement: `D5/S3/VertexAlgebra/LatticeBcGhostCohomologyLocality.projected_superLocal`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeBcGhostCohomologyLocality.projected_superLocal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The existing tensor homogeneous_superFieldLocal theorem supplies a single order. Quotient surjectivity and the two delta identities transport its linear-map equality to every quotient input.

**Theorem 1.4 (Uniform signed locality of homogeneous quotient states).**

Lean statement: `D5/S3/VertexAlgebra/LatticeBcGhostCohomologyLocality.superLocal`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeBcGhostCohomologyLocality.superLocal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The parity-fixed hypotheses identify the original two quotient states with actual parity-projected representatives. The result is equality of the entire killed distribution, not an input-dependent locality bound. Tensor locality is reused; no independent locality discovery or complete physical theory is claimed.

## References

- Truth anchor: `D5/S3/VertexAlgebra/LatticeBcGhostCohomologyLocality.iterated_cycle_val`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeBcGhostCohomologyLocality.iterated_quotient_mk`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeBcGhostCohomologyLocality.projected_superLocal`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeBcGhostCohomologyLocality.superLocal`
- Dependency: [D5/S3/VertexAlgebra/LatticeBcGhostCohomologyFields](LatticeBcGhostCohomologyFields.md)
