# Cover density above the S and J two-lifts

## Abstract

Cover density above the S and J two-lifts

The actual sixteen-vertex S and J dissociation selections are used by the generic certificate-density and cubic-gap theorems. Every uniform cover above either fixed two-lift has beta density at least four sevenths and SF-minus-beta density at most one forty-ninth. The cover, fiber cardinality and uniformity hypotheses remain explicit. No classification conclusion is added.

**Theorem 1.1 (scalar cover bound).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/Families/HeawoodCoverDensity.scalar_cover_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/Families/HeawoodCoverDensity.scalar_cover_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact declaration: theorem scalar_cover_bound {U : Type} [Fintype U] [DecidableEq U] (H : SimpleGraph U) [DecidableRel H.Adj] (p : U → Fin 28) (cover : CoverPullback.NeighborhoodCover HeawoodCertificates.scalarGraph.Adj H.Adj p) (k : ℕ) (hk : ∀ v, (Finset.univ.filter (fun w => p w = v)).card = k) : 4 * Fintype.card U ≤ 7 * beta H 2 ∧ 49 * (SF H 2 - beta H 2) ≤ Fintype.card U.

**Theorem 1.2 (jordan cover bound).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/Families/HeawoodCoverDensity.jordan_cover_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/Families/HeawoodCoverDensity.jordan_cover_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact declaration: theorem jordan_cover_bound {U : Type} [Fintype U] [DecidableEq U] (H : SimpleGraph U) [DecidableRel H.Adj] (p : U → Fin 28) (cover : CoverPullback.NeighborhoodCover HeawoodCertificates.jordanGraph.Adj H.Adj p) (k : ℕ) (hk : ∀ v, (Finset.univ.filter (fun w => p w = v)).card = k) : 4 * Fintype.card U ≤ 7 * beta H 2 ∧ 49 * (SF H 2 - beta H 2) ≤ Fintype.card U.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/Families/HeawoodCoverDensity.jordan_cover_bound`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/Families/HeawoodCoverDensity.scalar_cover_bound`
- Dependency: [D5/S3/Combinatorics/Graph/StarForming/CoverDensity](../CoverDensity.md)
- Dependency: [D5/S3/Combinatorics/Graph/StarForming/Families/HeawoodCertificates](HeawoodCertificates.md)
