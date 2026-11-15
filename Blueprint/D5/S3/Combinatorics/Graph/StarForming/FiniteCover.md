# Finite fibers and canonical graph invariants

## Abstract

Finite fibers and canonical graph invariants

The relational selection predicates are transported to canonical finite stars. Constant finite fibers are counted exactly, including fiber size zero. Safely certified minimal selections pull back under neighborhood covers and yield the multiplicative SF lower bound when every minimal base selection has safe certificates. Local injectivity yields the multiplicative beta lower bound. These directions do not preserve a positive SF-minus-beta gap, and global surjectivity is not silently added.

**Theorem 1.1 (regular forms iff).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/FiniteCover.regular_forms_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/FiniteCover.regular_forms_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact declaration: theorem regular_forms_iff (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) : Regular.Forms G.Adj (· ∈ S) ↔ IsStarForming G 2 S.

**Theorem 1.2 (regular minimal iff).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/FiniteCover.regular_minimal_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/FiniteCover.regular_minimal_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact declaration: theorem regular_minimal_iff (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) : Regular.Minimal G.Adj (· ∈ S) ↔ IsMinimalStarForming G 2 S.

**Theorem 1.3 (card preimage uniform).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/FiniteCover.card_preimage_uniform`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/FiniteCover.card_preimage_uniform` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact declaration: theorem card_preimage_uniform (p : W → V) (k : ℕ) (hk : ∀ v, (Finset.univ.filter (fun w => p w = v)).card = k) (S : Finset V) : (Finset.univ.filter (fun w => p w ∈ S)).card = k * S.card.

**Theorem 1.4 (minimal preimage of safe).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/FiniteCover.minimal_preimage_of_safe`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/FiniteCover.minimal_preimage_of_safe` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact declaration: theorem minimal_preimage_of_safe (G : SimpleGraph V) (H : SimpleGraph W) [DecidableRel G.Adj] [DecidableRel H.Adj] (p : W → V) (cover : CoverPullback.NeighborhoodCover G.Adj H.Adj p) (S : Finset V) (hS : IsMinimalStarForming G 2 S) (hsafe : CoverPullback.HasSafeCertificates G.Adj (· ∈ S)) : IsMinimalStarForming H 2 (Finset.univ.filter (fun w => p w ∈ S)).

**Theorem 1.5 (sf mul le of safe).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/FiniteCover.sf_mul_le_of_safe`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/FiniteCover.sf_mul_le_of_safe` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact declaration: theorem sf_mul_le_of_safe (G : SimpleGraph V) (H : SimpleGraph W) [DecidableRel G.Adj] [DecidableRel H.Adj] (p : W → V) (cover : CoverPullback.NeighborhoodCover G.Adj H.Adj p) (k : ℕ) (hk : ∀ v, (Finset.univ.filter (fun w => p w = v)).card = k) (hsafe : ∀ S : Finset V, IsMinimalStarForming G 2 S → CoverPullback.HasSafeCertificates G.Adj (· ∈ S)) : k * SF G 2 ≤ SF H 2.

**Theorem 1.6 (beta mul le).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/FiniteCover.beta_mul_le`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/FiniteCover.beta_mul_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact declaration: theorem beta_mul_le (G : SimpleGraph V) (H : SimpleGraph W) [DecidableRel G.Adj] [DecidableRel H.Adj] (p : W → V) (cover : CoverPullback.NeighborhoodCover G.Adj H.Adj p) (k : ℕ) (hk : ∀ v, (Finset.univ.filter (fun w => p w = v)).card = k) : k * beta G 2 ≤ beta H 2.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/FiniteCover.beta_mul_le`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/FiniteCover.card_preimage_uniform`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/FiniteCover.minimal_preimage_of_safe`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/FiniteCover.regular_forms_iff`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/FiniteCover.regular_minimal_iff`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/FiniteCover.sf_mul_le_of_safe`
- Dependency: [D5/S3/Combinatorics/Graph/StarForming/CoverStability](CoverStability.md)
- Dependency: [D5/S3/Combinatorics/Graph/StarForming/DissociationCover](DissociationCover.md)
- Dependency: [D5/S3/Combinatorics/Graph/StarForming/Semantics](Semantics.md)
