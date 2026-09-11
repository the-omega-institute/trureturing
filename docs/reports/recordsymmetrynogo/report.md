# Equivariant record symmetry no-go — implementation report

## Provenance and scope

This implementation uses the existing repository theorem
`D5/S3/Quantum/Matrix/CrossSpeciesConsensus.equivariant_selfAdjoint_eq_smul_id_of_irreducible`.
No new axiom, `sorry`, `native_decide`, or external numerical oracle is used. The target is a
conditional algebraic obstruction for finite complex matrix representations. It does not reject
the quantum research line: it identifies the choice required for an observer-to-objective
construction, between a reducible shared symmetry and records that break equivariance.

The preregistered escape witness is the binary scalar equation. Mathlib's pinned representation
API provides `Representation.IsIrreducible`; no separate `IsReducible` definition exists in the
searched pinned tree, so the reverse statements use `¬ Representation.IsIrreducible`.

## Formal declarations

The new module is `D5/S3/Quantum/Matrix/RecordSymmetryNoGo.lean`.

1. `equivariant_selfAdjoint_idempotent_eq_zero_or_one`: Schur scalarity gives `P = r I`;
   a diagonal entry of `P² = P` gives `r² = r`; real factorization gives `r = 0 ∨ r = 1`.
2. `nontrivial_equivariant_selfAdjoint_idempotent_implies_reducible`: contraposition of (1)
   for a nonzero proper projection.
3. `two_nonzero_orthogonal_equivariant_records_imply_reducible`: under irreducibility the first
   nonzero projection is identity, and its orthogonality with the second forces the second to be
   zero, contradicting its nonzero hypothesis.

The third theorem takes two Hermitian idempotents, equivariance for each, nonzeroness for each,
and `P * Q = 0`. This is sufficient for the stated pairwise orthogonality consequence.

All public declarations are general symbolic theorems with `utility: none`; none is a bounded
enumeration, checker, numeric reduction, or certified finite instance. The module's direct frozen
dependency is the imported CrossSpeciesConsensus theorem above.

## Verification

The source was checked with Lean 4.33.0 and the pinned Mathlib environment. The direct warm
elaboration passed after the CrossSpeciesConsensus object was built. The required serial build,
`make lean-report`, `make emit`, `make deposit-uncovered`, and the pre-PR scribe content check
are the final gate sequence for this branch; their exact receipts are appended when run on the
complete tree.

## Boundary and constructive reading

The no-go says that a nontrivial family of orthogonal records cannot remain equivariant under a
shared irreducible symmetry. It therefore exposes a design choice: use a reducible shared
representation or allow the record projections to break that symmetry. It does not say that
quantum models fail, nor does it derive either physical premise.
