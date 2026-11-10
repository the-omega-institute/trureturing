# The full arbitrary Heawood double-cover parameter theorem

## Abstract

The full arbitrary Heawood double-cover parameter theorem

An arbitrary finite neighborhood cover of the actual fourteen-vertex binary Fano graph with every actual fiber of size two is represented by a binary signing. Actual graph-isomorphism transport and the complete signing theorem give SF sixteen, beta fourteen exactly when not preconnected, and connected beta fifteen or sixteen with gap at most one. The four unresolved type-specific exact beta values and higher deck-group questions remain separate.

**Theorem 1.1 (parameters).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/HeawoodAllDoubleCovers.parameters`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/HeawoodAllDoubleCovers.parameters` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem parameters {U : Type} [Fintype U] [DecidableEq U] (H : SimpleGraph U) [DecidableRel H.Adj] (p : U → Fin 14) (cover : CoverPullback.NeighborhoodCover HeawoodLift.base.Adj H.Adj p) (fibers : ∀ v, Nat.card {u // p u=v}=2) : SF H 2=16 ∧ (beta H 2=14 ↔ ¬ H.Preconnected) ∧ (H.Preconnected → (beta H 2=15 ∨ beta H 2=16) ∧ SF H 2-beta H 2≤1).

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/HeawoodAllDoubleCovers.parameters`
- Dependency: [D5/S3/Combinatorics/Graph/StarForming/BinaryCoverRepresentation](BinaryCoverRepresentation.md)
- Dependency: [D5/S3/Combinatorics/Graph/StarForming/HeawoodCoverParameters](HeawoodCoverParameters.md)
