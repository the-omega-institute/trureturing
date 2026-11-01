/- GID: D5/S3/Geometry/Polygons/PolygonEarSlideCardinality
   generality: G
   mirror-B: D5/B/S3/Geometry/Polygons/PolygonEarSlideCardinality
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Complete conditioned polygon fibre partition and cyclic ear-slide counts. -/

import D5.S3.Geometry.Polygons.PolygonEarSlide
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Logic.Equiv.Sum

/-! Exact local complete-fibre counts, with the optional third-ear partition. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Geometry.Polygons.PolygonEarSlideCardinality
open Finset PolygonEarSlide PolygonEarSlide.Carrier PolygonEarSlide.Actual

variable {n : ℕ} [NeZero n]

omit [NeZero n] in
/-- Restoring the two erased observations leaves exactly the optional third ear. -/
private theorem restore_trace {E J X : Finset (ZMod n)} {t u : ZMod n}
    (ht : t ∉ E)
    (h : E ∩ (J.erase t).erase u = X) :
    E ∩ J = if u ∈ E ∩ J then insert u X else X := by
  ext i
  have hi := Finset.ext_iff.mp h i
  simp only [mem_inter, mem_erase] at hi
  split_ifs with hu
  · simp only [mem_inter, mem_insert]
    have hum := mem_inter.mp hu
    by_cases hit : i = t <;> by_cases hiu : i = u <;> grind
  · simp only [mem_inter]
    have hun : ¬(u ∈ E ∧ u ∈ J) := by simpa using hu
    by_cases hit : i = t <;> by_cases hiu : i = u <;> grind

/-- Source (37.8), with all complete conditioned fibres and arbitrary cyclic origin. -/
theorem condition_fibre_card_at (hn : 14 ≤ n) (a : ZMod n)
    {P Q J R : Finset (ZMod n)} (hJ : J ⊆ E_K (P ∪ Q))
    (ha0 : a ∉ J) (ha1 : a + 1 ∈ J) (ha2 : a + 2 ∈ J)
    (hR : R ⊆ ((J.erase (a + 1)).erase (a + 2)).erase (a + 3)) :
    Nat.card (ConditionFiber P Q J (insert (a + 2) R)) =
      Nat.card (ConditionFiber P Q J (insert (a + 1) R)) +
        if a + 3 ∈ J then
          Nat.card (ConditionFiber P Q J (insert (a + 3) (insert (a + 1) R)))
        else 0 := by
  classical
  let s := a + 1
  let t := a + 2
  let u := a + 3
  let X := insert s R
  let F := ConditionFiber P Q ((J.erase t).erase u) X
  let A := ConditionFiber P Q J X
  let B := ConditionFiber P Q J (insert u X)
  have hval (k : ℕ) (hk : k < n) : (k : ZMod n).val = k :=
    ZMod.val_natCast_of_lt hk
  have hvalone : (1 : ZMod n).val = 1 := by simpa using hval 1 (by omega)
  have hvaltwo : (2 : ZMod n).val = 2 := by simpa using hval 2 (by omega)
  have hvalthree : (3 : ZMod n).val = 3 := by simpa using hval 3 (by omega)
  have hst : s ≠ t := by
    intro h
    have he : (1 : ZMod n) = 2 := add_left_cancel h
    have hv := congrArg ZMod.val he
    rw [hvalone, hvaltwo] at hv
    omega
  have hus : u ≠ s := by
    intro h
    have he : (3 : ZMod n) = 1 := add_left_cancel h
    have hv := congrArg ZMod.val he
    rw [hvalthree, hvalone] at hv
    omega
  have htR : t ∉ R := fun h => (mem_erase.mp (mem_erase.mp (hR h)).2).1 rfl
  have huR : u ∉ R := fun h => (mem_erase.mp (hR h)).1 rfl
  have htX : t ∉ X := by simp [X, hst.symm, htR]
  have huX : u ∉ X := by simp [X, hus, huR]
  have hcross : Cross (ear s) (ear t) := by
    simpa only [s, t, add_comm] using
      (cross_ear_shift_iff (i := 1) (j := 2) (a := a)).mpr
        (cross_symm (local_crossings (show 6 ≤ n by omega)).1)
  have no_t (T : Finset (Sym2 (ZMod n))) (hT : IsTriangulation T)
      (hs : s ∈ EarCenters T) : t ∉ EarCenters T := by
    intro ht
    exact hT.noncrossing (ear s) (mem_earCenters.mp hs)
      (ear t) (mem_earCenters.mp ht) hcross
  have full (x : F) : EarCenters x.1 ∩ J =
      if u ∈ EarCenters x.1 ∩ J then insert u X else X := by
    have hs : s ∈ EarCenters x.1 := (mem_inter.mp
      ((Finset.ext_iff.mp x.2.2.2.2 s).mpr (by simp [X]))).1
    exact restore_trace (no_t x.1 x.2.1 hs) x.2.2.2.2
  have reduce (T : Finset (Sym2 (ZMod n)))
      (h : EarCenters T ∩ J = X ∨ EarCenters T ∩ J = insert u X) :
      EarCenters T ∩ (J.erase t).erase u = X := by
    ext i
    rcases h with h | h
    all_goals
      have hi := Finset.ext_iff.mp h i
      simp only [mem_inter, mem_insert] at hi
      simp only [mem_inter, mem_erase]
      by_cases hit : i = t <;> by_cases hiu : i = u <;> subst_vars <;>
        simp_all
  have eA : {x : F // u ∉ EarCenters x.1 ∩ J} ≃ A :=
    { toFun := fun x => ⟨x.1.1, x.1.2.1, x.1.2.2.1, x.1.2.2.2.1,
          by simpa [x.2] using full x.1⟩
      invFun := fun x => ⟨⟨x.1, x.2.1, x.2.2.1, x.2.2.2.1,
          reduce x.1 (Or.inl x.2.2.2.2)⟩, by simpa [x.2.2.2.2] using huX⟩
      left_inv := fun _ => by apply Subtype.ext; apply Subtype.ext; rfl
      right_inv := fun _ => Subtype.ext rfl }
  have : Finite A := by dsimp [A, ConditionFiber]; infer_instance
  have : Finite B := by dsimp [B, ConditionFiber]; infer_instance
  rw [Nat.card_congr (condition_fibre_equiv_at hn a hJ ha0 ha1 ha2 hR)]
  change Nat.card F = Nat.card A + if u ∈ J then Nat.card B else 0
  by_cases huJ : u ∈ J
  · have eB : {x : F // ¬u ∉ EarCenters x.1 ∩ J} ≃ B :=
      { toFun := fun x => ⟨x.1.1, x.1.2.1, x.1.2.2.1, x.1.2.2.2.1,
            by simpa [not_not.mp x.2] using full x.1⟩
        invFun := fun x => ⟨⟨x.1, x.2.1, x.2.2.1, x.2.2.2.1,
            reduce x.1 (Or.inr x.2.2.2.2)⟩, by simp [x.2.2.2.2]⟩
        left_inv := fun _ => by apply Subtype.ext; apply Subtype.ext; rfl
        right_inv := fun _ => Subtype.ext rfl }
    rw [ite_eq_left huJ, ← Nat.card_sum, ← Nat.card_congr (Equiv.sumCongr eA eB)]
    exact (Nat.card_congr (Equiv.sumCompl (fun x : F => u ∉ EarCenters x.1 ∩ J))).symm
  · have eF : F ≃ {x : F // u ∉ EarCenters x.1 ∩ J} :=
      { toFun := fun x => ⟨x, fun h => huJ (mem_inter.mp h).2⟩
        invFun := Subtype.val
        left_inv := fun _ => rfl
        right_inv := fun _ => Subtype.ext rfl }
    simpa [huJ] using Nat.card_congr (eF.trans eA)

end D5.S3.Geometry.Polygons.PolygonEarSlideCardinality
