/- GID: D5/S3/Geometry/Polygons/PolygonEarContraction
   generality: G
   mirror-B: D5/B/S3/Geometry/Polygons/PolygonEarContraction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual ear deletion and insertion on complete maximal noncrossing polygon triangulations. -/

import D5.S3.Geometry.Polygons.PolygonEarSlide

/-! Deleting one ear centre preserves the complete triangulation carrier. -/

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
    ⟨congrArg ZMod.val, fun h => ZMod.val_injective k h⟩
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
    have htwo : (2 : ZMod (m + 1)).val = 2 := by
      simpa using (ZMod.val_natCast_of_lt (n := m + 1) (a := 2) (by omega))
    have eq2 (x : ZMod m) : vertexLift x = 2 ↔ (vertexLift x).val = 2 := by
      constructor
      · intro h; rw [h, htwo]
      · intro h; apply ZMod.val_injective (m + 1); rwa [htwo]
    rw [eq0, eq0, eq2, eq2]
    simp only [lift_val]
    have := ZMod.val_lt a
    have := ZMod.val_lt b
    split_ifs <;> simp_all <;> omega

private lemma lift_diagonal (hm : 5 ≤ m) (e : Sym2 (ZMod m)) :
    IsDiagonal e ↔ IsDiagonal (chordLift e) ∧ chordLift e ≠ ear (1 : ZMod (m + 1)) := by
  have hseg : IsSegment (chordLift e) ↔ IsSegment e := by
    induction e using Sym2.ind with
    | _ a b => simp [chordLift, IsSegment, Sym2.mk_isDiag_iff, lift_injective.eq_iff]
  have he := isDiagonal_sEar (n := m + 1) (by omega)
  change IsDiagonal (ear (1 : ZMod (m + 1))) at he
  rw [IsDiagonal, IsDiagonal, hseg, boundary_lift_iff hm]
  tauto


private lemma lift_avoids (hm : 5 ≤ m) (e : Sym2 (ZMod m)) :
    ∀ x, chordLift e ≠ s(1, x) := by
  induction e using Sym2.ind with
  | _ a b =>
    intro x h
    change s(vertexLift a, vertexLift b) = s(1, x) at h
    rcases Sym2.eq_iff.mp h with ⟨h, _⟩ | ⟨_, h⟩
    · exact lift_ne_one hm a h
    · exact lift_ne_one hm b h

private lemma lift_not_cross_ear (hm : 5 ≤ m) (e : Sym2 (ZMod m)) :
    ¬Cross (chordLift e) (ear (1 : ZMod (m + 1))) :=
  not_cross_s_of_avoidOne (by omega) (lift_avoids hm e)

/-- Delete the forced ear and relabel exactly the remaining original chords. -/
def reduce (T : Finset (Sym2 (ZMod (m + 1)))) : Finset (Sym2 (ZMod m)) :=
  (T.erase (ear 1)).image chordDrop

/-- Add the forced ear to the lifted full reduced triangulation. -/
def expand (U : Finset (Sym2 (ZMod m))) : Finset (Sym2 (ZMod (m + 1))) :=
  insert (ear 1) (U.image chordLift)

private lemma member_lift_drop (hm : 5 ≤ m) {T : Finset (Sym2 (ZMod (m + 1)))}
    (hT : IsTriangulation T) (hs : ear 1 ∈ T) {e : Sym2 (ZMod (m + 1))}
    (he : e ∈ T) : chordLift (chordDrop e) = e :=
  chord_lift_drop hm (avoidOne_of_diagonal_not_cross_s (by omega)
    (hT.isDiagonal e he) (hT.noncrossing e he _ hs))

theorem reduce_isTriangulation (hm : 5 ≤ m) {T : Finset (Sym2 (ZMod (m + 1)))}
    (hT : IsTriangulation T) (hs : ear 1 ∈ T) : IsTriangulation (reduce T) := by
  constructor
  · intro e he
    obtain ⟨f, hf, rfl⟩ := mem_image.mp he
    have hl := member_lift_drop hm hT hs (mem_of_mem_erase hf)
    apply (lift_diagonal hm _).mpr
    rw [hl]
    exact ⟨hT.isDiagonal _ (mem_of_mem_erase hf), (mem_erase.mp hf).1⟩
  · intro e he f hf
    obtain ⟨a, ha, rfl⟩ := mem_image.mp he
    obtain ⟨b, hb, rfl⟩ := mem_image.mp hf
    intro hc
    apply hT.noncrossing a (mem_of_mem_erase ha) b (mem_of_mem_erase hb)
    have h := (lift_cross _ _).mpr hc
    rwa [member_lift_drop hm hT hs (mem_of_mem_erase ha),
      member_lift_drop hm hT hs (mem_of_mem_erase hb)] at h
  · intro e he hnot
    have hdiag := (lift_diagonal hm e).mp he
    have hout : chordLift e ∉ T := by
      intro h
      apply hnot
      exact mem_image.mpr ⟨chordLift e, mem_erase.mpr ⟨hdiag.2, h⟩, chord_drop_lift e⟩
    obtain ⟨f, hf, hc⟩ := hT.maximal _ hdiag.1 hout
    have hfe : f ≠ ear 1 := by
      intro h
      subst f
      exact lift_not_cross_ear hm e hc
    refine ⟨chordDrop f, mem_image.mpr ⟨f, mem_erase.mpr ⟨hfe, hf⟩, rfl⟩, ?_⟩
    apply (lift_cross _ _).mp
    rwa [member_lift_drop hm hT hs hf]

theorem expand_isTriangulation (hm : 5 ≤ m) {U : Finset (Sym2 (ZMod m))}
    (hU : IsTriangulation U) : IsTriangulation (expand U) := by
  constructor
  · intro e he
    rcases mem_insert.mp he with rfl | he
    · exact isDiagonal_sEar (by omega)
    · obtain ⟨f, hf, rfl⟩ := mem_image.mp he
      exact ((lift_diagonal hm f).mp (hU.isDiagonal f hf)).1
  · intro e he f hf
    rcases mem_insert.mp he with rfl | he <;> rcases mem_insert.mp hf with rfl | hf
    · exact not_cross_self _
    · obtain ⟨f, hf, rfl⟩ := mem_image.mp hf
      exact fun h => lift_not_cross_ear hm f (cross_symm h)
    · obtain ⟨e, he, rfl⟩ := mem_image.mp he
      exact lift_not_cross_ear hm e
    · obtain ⟨a, ha, hea⟩ := mem_image.mp he
      obtain ⟨b, hb, hfb⟩ := mem_image.mp hf
      rw [← hea, ← hfb]
      exact fun h => hU.noncrossing a ha b hb ((lift_cross _ _).mp h)
  · intro e he hnot
    by_cases hc : Cross e (ear (1 : ZMod (m + 1)))
    · exact ⟨ear 1, mem_insert_self .., hc⟩
    have hl := chord_lift_drop hm (avoidOne_of_diagonal_not_cross_s (by omega) he hc)
    have hne : e ≠ ear 1 := by
      intro h
      exact hnot (by simp [expand, h])
    have hd : IsDiagonal (chordDrop e) := (lift_diagonal hm _).mpr (by simpa [hl] using And.intro he hne)
    have hn : chordDrop e ∉ U := by
      intro h
      exact hnot (mem_insert_of_mem (mem_image.mpr ⟨chordDrop e, h, hl⟩))
    obtain ⟨f, hf, hcross⟩ := hU.maximal _ hd hn
    refine ⟨chordLift f, mem_insert_of_mem (mem_image.mpr ⟨f, hf, rfl⟩), ?_⟩
    have h := (lift_cross _ _).mpr hcross
    rwa [hl] at h

theorem expand_reduce (hm : 5 ≤ m) {T : Finset (Sym2 (ZMod (m + 1)))}
    (hT : IsTriangulation T) (hs : ear 1 ∈ T) : expand (reduce T) = T := by
  ext e
  constructor
  · intro he
    rcases mem_insert.mp he with rfl | he
    · exact hs
    · obtain ⟨f, hf, rfl⟩ := mem_image.mp he
      obtain ⟨g, hg, rfl⟩ := mem_image.mp hf
      rw [member_lift_drop hm hT hs (mem_of_mem_erase hg)]
      exact mem_of_mem_erase hg
  · intro he
    by_cases hs' : e = ear 1
    · simp [expand, hs']
    · exact mem_insert_of_mem (mem_image.mpr ⟨chordDrop e,
        mem_image.mpr ⟨e, mem_erase.mpr ⟨hs', he⟩, rfl⟩, member_lift_drop hm hT hs he⟩)

theorem reduce_expand (hm : 5 ≤ m) {U : Finset (Sym2 (ZMod m))}
    (hU : IsTriangulation U) : reduce (expand U) = U := by
  ext e
  constructor
  · intro he
    obtain ⟨f, hf, rfl⟩ := mem_image.mp he
    have hfn := (mem_erase.mp hf).1
    rcases mem_insert.mp (mem_of_mem_erase hf) with h | hf
    · exact False.elim (hfn h)
    · obtain ⟨g, hg, rfl⟩ := mem_image.mp hf
      simpa only [chord_drop_lift] using hg
  · intro he
    have hne := ((lift_diagonal hm e).mp (hU.isDiagonal e he)).2
    exact mem_image.mpr ⟨chordLift e, mem_erase.mpr ⟨hne,
      mem_insert_of_mem (mem_image.mpr ⟨e, he, rfl⟩)⟩, chord_drop_lift e⟩

/-- Every full original triangulation containing ear 1 corresponds to exactly one full reduced triangulation. -/
def earOneEquiv (hm : 5 ≤ m) :
    {T : Finset (Sym2 (ZMod (m + 1))) // IsTriangulation T ∧ ear 1 ∈ T} ≃
      {U : Finset (Sym2 (ZMod m)) // IsTriangulation U} where
  toFun T := ⟨reduce T.val, reduce_isTriangulation hm T.property.1 T.property.2⟩
  invFun U := ⟨expand U.val, expand_isTriangulation hm U.property, mem_insert_self ..⟩
  left_inv T := Subtype.ext (expand_reduce hm T.property.1 T.property.2)
  right_inv U := Subtype.ext (reduce_expand hm U.property)


/-- Rotate the chosen original ear to centre 1, then delete exactly that centre. -/
def earEquiv (hm : 5 ≤ m) (i : ZMod (m + 1)) :
    {T : Finset (Sym2 (ZMod (m + 1))) // IsTriangulation T ∧ ear i ∈ T} ≃
      {U : Finset (Sym2 (ZMod m)) // IsTriangulation U} := by
  let a := 1 - i
  have hi : i + a = 1 := by dsimp [a]; ring
  have hj : (1 : ZMod (m + 1)) + -a = i := by dsimp [a]; ring
  let rotate :
      {T : Finset (Sym2 (ZMod (m + 1))) // IsTriangulation T ∧ ear i ∈ T} ≃
      {T : Finset (Sym2 (ZMod (m + 1))) // IsTriangulation T ∧ ear 1 ∈ T} :=
    { toFun := fun T => ⟨shiftChords T.val a, isTriangulation_map_add T.property.1 a,
        by rw [← hi]; exact mem_image.mpr ⟨ear i, T.property.2, (ear_add i a).symm⟩⟩
      invFun := fun T => ⟨shiftChords T.val (-a), isTriangulation_map_add T.property.1 (-a),
        by rw [← hj]; exact mem_image.mpr ⟨ear 1, T.property.2, (ear_add 1 (-a)).symm⟩⟩
      left_inv := fun T => Subtype.ext (shiftChords_add_neg T.val a)
      right_inv := fun T => Subtype.ext (by
        simpa only [neg_neg] using shiftChords_add_neg T.val (-a)) }
  exact rotate.trans (earOneEquiv hm)

end D5.S3.Geometry.Polygons.PolygonEarContraction
