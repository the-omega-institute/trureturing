/- GID: D5/S3/Geometry/Polygons/PolygonEarContraction
   generality: G
   mirror-B: D5/B/S3/Geometry/Polygons/PolygonEarContraction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual ear deletion and insertion on complete maximal noncrossing polygon triangulations. -/

import D5.S3.Geometry.Polygons.PolygonEarSlide

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Finset
namespace D5.S3.Geometry.Polygons.PolygonEarContraction
open PolygonEarSlide PolygonEarSlide.Carrier PolygonEarSlide.Actual

variable {m : ℕ} [NeZero m]

/-- Insert the missing vertex 1; the other vertices retain their cyclic order. -/
def vertexLift (x : ZMod m) : ZMod (m + 1) :=
  ((if x.val = 0 then 0 else x.val + 1 : ℕ) : ZMod (m + 1))

/-- Delete vertex 1. Its value at that vertex is unused on retained diagonals. -/
def vertexDrop (x : ZMod (m + 1)) : ZMod m := ((x.val - 1 : ℕ) : ZMod m)

def chordLift (e : Sym2 (ZMod m)) : Sym2 (ZMod (m + 1)) := e.map vertexLift

def chordDrop (e : Sym2 (ZMod (m + 1))) : Sym2 (ZMod m) := e.map vertexDrop

private lemma lift_val (x : ZMod m) :
    (vertexLift x).val = if x.val = 0 then 0 else x.val + 1 := by
  apply ZMod.val_natCast_of_lt
  have := ZMod.val_lt x
  split_ifs <;> omega

private lemma drop_lift (x : ZMod m) : vertexDrop (vertexLift x) = x := by
  unfold vertexDrop
  rw [lift_val]
  split_ifs with h
  · apply ZMod.val_injective m
    simpa [h] using (ZMod.val_zero : (0 : ZMod m).val = 0)
  · simpa using ZMod.natCast_zmod_val x

private lemma lift_injective : Function.Injective (vertexLift (m := m)) :=
  Function.LeftInverse.injective drop_lift

private lemma lift_ne_one (hm : 5 ≤ m) (x : ZMod m) : vertexLift x ≠ 1 := by
  intro h
  have := congrArg ZMod.val h
  rw [lift_val, ZMod.val_one'' (by omega)] at this
  split_ifs at this <;> omega

private lemma lift_drop (hm : 5 ≤ m) {x : ZMod (m + 1)} (hx : x ≠ 1) :
    vertexLift (vertexDrop x) = x := by
  have hlt := ZMod.val_lt x
  have hv1 : x.val ≠ 1 := by
    intro h
    apply hx
    apply ZMod.val_injective (m + 1)
    simpa [ZMod.val_one'' (show m + 1 ≠ 1 by omega)] using h
  have hdrop : (vertexDrop x).val = x.val - 1 := by
    apply ZMod.val_natCast_of_lt
    omega
  apply ZMod.val_injective (m + 1)
  rw [lift_val, hdrop]
  split_ifs <;> omega

private lemma chord_drop_lift (e : Sym2 (ZMod m)) : chordDrop (chordLift e) = e := by
  induction e using Sym2.ind with
  | _ a b => simp [chordDrop, chordLift, drop_lift]

private lemma chord_lift_injective : Function.Injective (chordLift (m := m)) :=
  Function.LeftInverse.injective chord_drop_lift

private lemma chord_lift_drop (hm : 5 ≤ m) {e : Sym2 (ZMod (m + 1))}
    (he : ∀ x, e ≠ s(1, x)) : chordLift (chordDrop e) = e := by
  induction e using Sym2.ind with
  | _ a b =>
    have ha : a ≠ 1 := fun h => he b (by simp [h])
    have hb : b ≠ 1 := fun h => he a (by simp [h, Sym2.eq_swap])
    simp [chordDrop, chordLift, lift_drop hm ha, lift_drop hm hb]

private lemma lift_order (a b : ZMod m) :
    (vertexLift a).val < (vertexLift b).val ↔ a.val < b.val := by
  rw [lift_val, lift_val]
  split_ifs <;> omega

private lemma lift_sbtw (a b c : ZMod m) :
    sbtw (vertexLift a) (vertexLift b) (vertexLift c) ↔ sbtw a b c := by
  rw [rotation_sbtw_iff_val, rotation_sbtw_iff_val]
  simp only [lift_order]

private lemma lift_cross (e f : Sym2 (ZMod m)) :
    Cross (chordLift e) (chordLift f) ↔ Cross e f := by
  constructor
  · rintro ⟨a, b, c, d, he, hf, hab, hcd⟩
    induction e using Sym2.ind with | _ u v =>
      induction f using Sym2.ind with | _ x y =>
        change s(vertexLift u, vertexLift v) = s(a, b) at he
        change s(vertexLift x, vertexLift y) = s(c, d) at hf
        rcases Sym2.eq_iff.mp he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
          rcases Sym2.eq_iff.mp hf with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact ⟨u, v, x, y, rfl, rfl, (lift_sbtw _ _ _).mp hab, (lift_sbtw _ _ _).mp hcd⟩
        · exact ⟨u, v, y, x, rfl, Sym2.eq_swap, (lift_sbtw _ _ _).mp hab, (lift_sbtw _ _ _).mp hcd⟩
        · exact ⟨v, u, x, y, Sym2.eq_swap, rfl, (lift_sbtw _ _ _).mp hab, (lift_sbtw _ _ _).mp hcd⟩
        · exact ⟨v, u, y, x, Sym2.eq_swap, Sym2.eq_swap, (lift_sbtw _ _ _).mp hab, (lift_sbtw _ _ _).mp hcd⟩
  · rintro ⟨a, b, c, d, rfl, rfl, hab, hcd⟩
    exact ⟨vertexLift a, vertexLift b, vertexLift c, vertexLift d, rfl, rfl,
      (lift_sbtw _ _ _).mpr hab, (lift_sbtw _ _ _).mpr hcd⟩

private lemma side_val {k : ℕ} [NeZero k] (hk : 2 ≤ k) (a b : ZMod k) :
    IsSide s(a, b) ↔ b.val = a.val + 1 ∨ a.val = b.val + 1 ∨
      (a.val = 0 ∧ b.val = k - 1) ∨ (b.val = 0 ∧ a.val = k - 1) := by
  have hs (x : ZMod k) : (x + 1).val = if x.val + 1 < k then x.val + 1 else 0 := by
    rw [ZMod.val_add, ZMod.val_one'' (by omega)]
    have := ZMod.val_lt x
    split_ifs with h
    · exact Nat.mod_eq_of_lt h
    · have hx : x.val + 1 = k := by omega
      simp [hx]
  have heq (x y : ZMod k) : x = y + 1 ↔ x.val = (y + 1).val :=
    ⟨congrArg ZMod.val, ZMod.val_injective k⟩
  have hadj : IsSide s(a, b) ↔ b = a + 1 ∨ a = b + 1 := by
    constructor
    · rintro ⟨i, hi⟩
      rcases Sym2.eq_iff.1 hi with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      exacts [Or.inl rfl, Or.inr rfl]
    · rintro (rfl | rfl)
      exacts [⟨a, rfl⟩, ⟨b, Sym2.eq_swap⟩]
  rw [hadj, heq b a, heq a b, hs, hs]
  have := ZMod.val_lt a
  have := ZMod.val_lt b
  split_ifs <;> omega

/-- The new reduced boundary lifts to surviving original sides together with the forced ear. -/
theorem boundary_lift_iff (hm : 5 ≤ m) (e : Sym2 (ZMod m)) :
    IsSide e ↔ IsSide (chordLift e) ∨ chordLift e = ear (1 : ZMod (m + 1)) := by
  induction e using Sym2.ind with
  | _ a b =>
    change IsSide s(a, b) ↔ IsSide s(vertexLift a, vertexLift b) ∨
      s(vertexLift a, vertexLift b) = ear (1 : ZMod (m + 1))
    rw [side_val (by omega), side_val (by omega), ear_one, Sym2.eq_iff]
    have eq0 (x : ZMod m) : vertexLift x = 0 ↔ (vertexLift x).val = 0 :=
      ⟨fun h => by rw [h, ZMod.val_zero], fun h => (ZMod.val_eq_zero _).mp h⟩
    have eq2 (x : ZMod m) : vertexLift x = 2 ↔ (vertexLift x).val = 2 := by
      constructor
      · intro h; rw [h]; exact ZMod.val_natCast_of_lt (by omega)
      · intro h; apply ZMod.val_injective (m + 1)
        simpa [ZMod.val_natCast_of_lt (show 2 < m + 1 by omega)] using h
    rw [eq0, eq0, eq2, eq2]
    simp only [lift_val]
    have := ZMod.val_lt a
    have := ZMod.val_lt b
    split_ifs <;> omega

private lemma lift_diagonal (hm : 5 ≤ m) (e : Sym2 (ZMod m)) :
    IsDiagonal e ↔ IsDiagonal (chordLift e) ∧ chordLift e ≠ ear (1 : ZMod (m + 1)) := by
  have hseg : IsSegment (chordLift e) ↔ IsSegment e := by
    induction e using Sym2.ind with
    | _ a b => simp [chordLift, IsSegment, Sym2.mk_isDiag_iff, lift_injective.eq_iff]
  have he := isDiagonal_sEar (n := m + 1) (by omega)
  change IsDiagonal (ear (1 : ZMod (m + 1))) at he
  rw [IsDiagonal, IsDiagonal, hseg, boundary_lift_iff hm]
  tauto

end D5.S3.Geometry.Polygons.PolygonEarContraction
