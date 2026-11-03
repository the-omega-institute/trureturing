/- GID: D5/S3/Combinatorics/Graph/Laman/PlanarLaman
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Laman/PlanarLaman
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Finite]
   utility: none
   digest: A finite graph admits a real planar rigid placement exactly when it contains a spanning Laman graph. -/
/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in docs/reports/licenses/laman-henneberg/LICENSE.txt.
Authors: Bryan Gin-ge Chen
Modified file: selected source declarations reorganized for trureturing;
receiver imports and API adaptations; unconsumed declarations omitted.
Source: CombinatorialRigidity@021c2284bc387efee3c3b20a18eb5f769638b578.
-/
import D5.S3.Combinatorics.Graph.Laman.PlanarForward
import D5.S3.Combinatorics.Graph.Laman.PlanarRows

/-!
# PlanarLaman

A finite simple graph on at least two vertices admits an arbitrary real planar placement with rigidity kernel dimension at most three if and only if it contains a spanning Laman subgraph. The placement need not be injective. The graph need not be planar and may contain additional edges.
-/

@[expose] public section

namespace SimpleGraph

variable {V : Type*}

theorem IsGenericallyRigid.exists_isLaman_le [Fintype V] {G : SimpleGraph V}
    (h : G.IsGenericallyRigid 2) (hV : 2 ≤ Fintype.card V) :
    ∃ H : SimpleGraph V, H ≤ G ∧ H.IsLaman := by
  -- Step 1: pick an IR + affinely-spanning placement.
  obtain ⟨p₀, hp₀⟩ := h
  obtain ⟨p, hp_IR, hp_aff⟩ := exists_affinelySpanning_of_eventually hp₀.eventually
  -- Step 2: rank lower bound at `p` (from IR + rank-nullity).
  have h_rank_ge : 2 * Fintype.card V ≤
      Module.finrank ℝ (LinearMap.range (G.RigidityMap p)) + 3 := by
    have h_ker : Module.finrank ℝ (LinearMap.ker (G.RigidityMap p)) ≤ 3 := hp_IR
    have h_total : Module.finrank ℝ (Framework V 2) = 2 * Fintype.card V := by
      rw [Framework.finrank, mul_comm]
    have h_rn := LinearMap.finrank_range_add_finrank_ker (G.RigidityMap p)
    omega
  -- Step 3: basis-pick at `p`.
  obtain ⟨I, hI_card, hI⟩ :=
    exists_edgeSetRowIndependent_of_finrank_range_ge_dim_two h_rank_ge
  -- Step 4: assemble the spanning subgraph and verify Laman.
  set H : SimpleGraph V := fromEdgeSet (Subtype.val '' I) with hH_def
  have hHG : H ≤ G := by
    rw [hH_def, fromEdgeSet_le]
    rintro e ⟨⟨e', _, rfl⟩, _⟩
    exact e'.property
  have hH_edgeSet : H.edgeSet = Subtype.val '' I := by
    rw [hH_def, edgeSet_fromEdgeSet]
    refine sdiff_eq_left.mpr ?_
    rw [Set.disjoint_left]
    rintro e ⟨e', _, rfl⟩ he_diag
    exact not_isDiag_of_mem_edgeSet G e'.property he_diag
  have hH_ncard : H.edgeSet.ncard = 2 * Fintype.card V - 3 := by
    rw [hH_edgeSet, Set.ncard_image_of_injective _ Subtype.val_injective, hI_card]
  refine ⟨H, hHG, isSparse_of_edgeSetRowIndependent_dim_two hp_aff hI, ?_⟩
  rw [hH_ncard, Nat.card_eq_fintype_card]
  omega

/-- **Laman's theorem** (Pollaczek-Geiringer 1927, Laman 1970). A simple graph on `n ≥ 2`
vertices is generically rigid in the plane iff it contains a Laman spanning subgraph.

The iff is composed from the two named directional theorems
`IsLaman.isGenericallyRigid_two` and `IsGenericallyRigid.exists_isLaman_le`. -/
theorem isGenericallyRigid_two_iff_exists_isLaman_le [Finite V] {G : SimpleGraph V}
    (hV : 2 ≤ Nat.card V) :
    G.IsGenericallyRigid 2 ↔ ∃ H : SimpleGraph V, H ≤ G ∧ H.IsLaman := by
  have : Fintype V := Fintype.ofFinite V
  rw [Nat.card_eq_fintype_card] at hV
  exact ⟨fun h => h.exists_isLaman_le hV,
   fun ⟨_, hHG, hLam⟩ => hLam.isGenericallyRigid_two.mono hHG⟩

end SimpleGraph
