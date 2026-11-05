/- GID: D5/S3/Combinatorics/Graph/Laman/PlanarForward
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Laman/PlanarForward
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Finite]
   utility: none
   digest: Every finite Laman graph has a real planar rigid placement by Henneberg induction. -/
/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in docs/reports/licenses/laman-henneberg/LICENSE.txt.
Authors: Bryan Gin-ge Chen
Modified file: selected source declarations reorganized for trureturing;
receiver imports and namespace adaptations.
Source: CombinatorialRigidity@021c2284bc387efee3c3b20a18eb5f769638b578.
-/
import D5.S3.Combinatorics.Graph.Laman.HennebergRigidity

/-!
# PlanarForward

Every finite Laman graph has a rigid planar placement. Strong induction uses exact reverse reconstruction, both geometric Henneberg moves, and the two-vertex complete graph.
-/

@[expose] public section

namespace SimpleGraph

variable {V : Type*}

/-- **Strong-form (⇐) Laman, internal helper.** Strong induction on
`Fintype.card V`: every Laman graph admits an *injective* rigid placement in
dim 2 (`IsGenericallyRigidInj 2`).

Both inductive moves (Type I and Type II) are handled by the unconditional
per-move preservation theorems in `HennebergRigidity.lean`; the Type II step's
non-collinearity gap is discharged inside
`typeII_isGenericallyRigidInj_two` via openness of infinitesimal rigidity
(`IsInfinitesimallyRigid.eventually`) and a perturbation of one neighbor of the
new vertex off the line through the other two. Base case `n = 2` reduces to `K₂` via
`eq_top_of_card_eq_two` plus iso transport. -/
private theorem IsLaman.isGenericallyRigidInj_two_of_card :
    ∀ (n : ℕ) {V : Type*} [Fintype V], Fintype.card V = n →
      ∀ {G : SimpleGraph V}, G.IsLaman → G.IsGenericallyRigidInj 2 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro V _ hV G h
    classical
    by_cases hV3 : 3 ≤ Fintype.card V
    · -- Inductive step: apply the flat-form `exists_typeI_or_typeII_reverse`, reconstruct the
      -- iso to `typeI G' a b` / `typeII G' x y c` at this callsite (the flat form describes the
      -- smaller graph directly via `comap` and `fromEdgeSet`), then IH + operation-form forward
      -- preservation + iso transport.
      obtain ⟨v, hbranch⟩ := Henneberg.IsLaman.exists_typeI_or_typeII_reverse h hV3
      have hcard_lt : Fintype.card {w : V // w ≠ v} < n := by
        rw [← hV]
        exact Fintype.card_subtype_lt (p := fun w => w ≠ v) (x := v) (by simp)
      rcases hbranch with
        ⟨_hdeg, a, b, hab, hN_iff, hG'_lam⟩ |
        ⟨_hdeg, x, y, c, hxy, hcx, hcy, hN_iff, hnxy, hG'_lam⟩
      · -- Type I: build `G ≃g typeI (G.comap _) a b` and transport.
        have ih_G' : (G.comap (Subtype.val : {w : V // w ≠ v} → V)).IsGenericallyRigidInj 2 :=
          ih _ hcard_lt rfl hG'_lam
        have φ : G ≃g Henneberg.typeI (G.comap (Subtype.val : {w : V // w ≠ v} → V)) a b :=
          Henneberg.isoTypeIOfTwoNeighbors a.property.symm b.property.symm hN_iff
        exact (Henneberg.typeI_isGenericallyRigidInj_two ih_G' hab).iso φ.symm
      · -- Type II: build `G ≃g typeII (G.comap _ ⊔ fromEdgeSet {s(x, y)}) x y c` and transport.
        have ih_G' :
            (G.comap (Subtype.val : {w : V // w ≠ v} → V) ⊔
              fromEdgeSet ({s(x, y)} : Set _)).IsGenericallyRigidInj 2 :=
          ih _ hcard_lt rfl hG'_lam
        have φ : G ≃g Henneberg.typeII
            (G.comap (Subtype.val : {w : V // w ≠ v} → V) ⊔
              fromEdgeSet ({s(x, y)} : Set _)) x y c :=
          Henneberg.isoTypeIIOfThreeNeighbors x.property.symm y.property.symm c.property.symm
            hN_iff hnxy
        exact (Henneberg.typeII_isGenericallyRigidInj_two ih_G' hxy hcx.symm hcy.symm).iso φ.symm
    · -- Base case: `Fintype.card V ≤ 2`. The `≤ 1` sub-cases contradict Laman
      -- tightness (a Laman graph has `#E + 3 = 2 * #V`, infeasible for #V ≤ 1
      -- in `ℕ`); `n = 2` reduces to K₂ via `eq_top_of_card_eq_two` + iso transport.
      have hE := h.edgeSet_ncard
      rw [Nat.card_eq_fintype_card] at hE
      have hcard2 : Fintype.card V = 2 := by omega
      have h_top : G = ⊤ := h.eq_top_of_card_eq_two hcard2
      rw [h_top]
      have e : V ≃ Fin 2 := Fintype.equivFinOfCardEq hcard2
      exact (top_fin_two_isGenericallyRigidInj 1).iso (Iso.completeGraph e.symm)

/-- Every Laman graph is generically rigid in dimension 2.

Proved by Henneberg induction on `Fintype.card V`: the K₂ base case is
`top_fin_two_isGenericallyRigidInj 1` (dimension `1 + 1`); the inductive step uses
`IsLaman.exists_typeI_or_typeII_reverse` plus per-move rigidity preservation
plus iso transport (`IsGenericallyRigidInj.iso`). The induction maintains the
strong predicate `IsGenericallyRigidInj` (existence of an *injective* rigid
placement) — see `IsLaman.isGenericallyRigidInj_two_of_card`. -/
theorem IsLaman.isGenericallyRigid_two [Finite V] {G : SimpleGraph V}
    (h : G.IsLaman) : G.IsGenericallyRigid 2 := by
  have : Fintype V := Fintype.ofFinite V
  exact (IsLaman.isGenericallyRigidInj_two_of_card _ rfl h).toIsGenericallyRigid


end SimpleGraph
