# Actual certificate density in uniform finite covers

## Abstract

Actual certificate density in uniform finite covers

Neighborhood bijections preserve finite vertex degrees and pull back a two-coloring. Uniform fibers give the complete whole-order identity, including zero fibers and empty bases. Every actual base dissociation set yields its stated density in the lift. For cubic bipartite bases this combines with sharp compensation to bound the actual canonical gap. Above either supplied S/J two-lift the density is at least four sevenths and gap at most one forty-ninth of the order. No arbitrary even nonregular cover factorization or higher-cover SF exactness is assumed.

**Theorem 1.1 (degree cover).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/CoverDensity.degree_cover`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/CoverDensity.degree_cover` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact declaration: theorem degree_cover (p : W → V) (cover : CoverPullback.NeighborhoodCover G.Adj H.Adj p) (v : W) : DegreeCapacity.degree H v = DegreeCapacity.degree G (p v).

**Theorem 1.2 (colorable cover).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/CoverDensity.colorable_cover`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/CoverDensity.colorable_cover` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact declaration: theorem colorable_cover (p : W → V) (cover : CoverPullback.NeighborhoodCover G.Adj H.Adj p) (hG : G.Colorable 2) : H.Colorable 2.

**Theorem 1.3 (card cover).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/CoverDensity.card_cover`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/CoverDensity.card_cover` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact declaration: theorem card_cover (p : W → V) (k : ℕ) (hk : ∀ v, (Finset.univ.filter (fun w => p w = v)).card = k) : Fintype.card W = k * Fintype.card V.

**Theorem 1.4 (certificate density).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/CoverDensity.certificate_density`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/CoverDensity.certificate_density` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact declaration: theorem certificate_density (p : W → V) (cover : CoverPullback.NeighborhoodCover G.Adj H.Adj p) (k : ℕ) (hk : ∀ v, (Finset.univ.filter (fun w => p w = v)).card = k) (A : Finset V) (hA : IsKIndependent G 2 A) : A.card * Fintype.card W ≤ Fintype.card V * beta H 2.

**Theorem 1.5 (cubic certificate gap).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/CoverDensity.cubic_certificate_gap`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/CoverDensity.cubic_certificate_gap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact declaration: theorem cubic_certificate_gap (p : W → V) (cover : CoverPullback.NeighborhoodCover G.Adj H.Adj p) (k : ℕ) (hk : ∀ v, (Finset.univ.filter (fun w => p w = v)).card = k) (hG : G.Colorable 2) (hr : ∀ v, DegreeCapacity.degree G v = 3) (A : Finset V) (hA : IsKIndependent G 2 A) : (7 * Fintype.card V) * (SF H 2 - beta H 2) ≤ (3 * Fintype.card V - 5 * A.card) * Fintype.card W.

**Theorem 1.6 (scalar cover bound).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/CoverDensity.scalar_cover_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/CoverDensity.scalar_cover_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact declaration: theorem scalar_cover_bound {U : Type} [Fintype U] [DecidableEq U] (H : SimpleGraph U) [DecidableRel H.Adj] (p : U → Fin 28) (cover : CoverPullback.NeighborhoodCover HeawoodCertificates.scalarGraph.Adj H.Adj p) (k : ℕ) (hk : ∀ v, (Finset.univ.filter (fun w => p w = v)).card = k) : 4 * Fintype.card U ≤ 7 * beta H 2 ∧ 49 * (SF H 2 - beta H 2) ≤ Fintype.card U.

**Theorem 1.7 (jordan cover bound).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/CoverDensity.jordan_cover_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/CoverDensity.jordan_cover_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact declaration: theorem jordan_cover_bound {U : Type} [Fintype U] [DecidableEq U] (H : SimpleGraph U) [DecidableRel H.Adj] (p : U → Fin 28) (cover : CoverPullback.NeighborhoodCover HeawoodCertificates.jordanGraph.Adj H.Adj p) (k : ℕ) (hk : ∀ v, (Finset.univ.filter (fun w => p w = v)).card = k) : 4 * Fintype.card U ≤ 7 * beta H 2 ∧ 49 * (SF H 2 - beta H 2) ≤ Fintype.card U.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/CoverDensity.card_cover`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/CoverDensity.certificate_density`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/CoverDensity.colorable_cover`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/CoverDensity.cubic_certificate_gap`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/CoverDensity.degree_cover`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/CoverDensity.jordan_cover_bound`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/CoverDensity.scalar_cover_bound`
- Dependency: [D5/S3/Combinatorics/Graph/StarForming/HeawoodCertificates](HeawoodCertificates.md)
