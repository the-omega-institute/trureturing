/- GID: D5/S3/TotalVariation/FairBiasLink
   generality: G
   mirror-B: D5/B/S3/TotalVariation/FairBiasLink
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The fair-bias link is the realization of the signed complement-spanning complex. -/

import D5.S3.TotalVariation.MinimumParityInputs
import D5.S3.Geometry.FiniteConeCollapse

/-! Geometric realization of the directions that retain a spanning set of fair columns. -/

set_option autoImplicit false

open scoped BigOperators

namespace D5.S3.TotalVariation.FairBiasLink

open D5.S3.Geometry.FiniteConeCollapse
open D5.S3.TotalVariation.MinimumParityInputs

universe u v

variable {A : Type u} {L : Type v} [AddCommGroup A] [Fintype L]

/-- The normalized directions whose zero columns generate the span of all columns. -/
def link (c : L → A) : Set (L → ℝ) :=
  {x | (∑ i, |x i|) = 1 ∧ fairSpan c x = AddSubgroup.closure (Set.range c)}

private def unusedSpan (c : L → A) (S : Finset (L × Bool)) : AddSubgroup A :=
  AddSubgroup.closure (c '' {i | ∀ b : Bool, (i, b) ∉ S})

private theorem unusedSpan_le (c : L → A) (S : Finset (L × Bool)) :
    unusedSpan c S ≤ AddSubgroup.closure (Set.range c) :=
  AddSubgroup.closure_mono (fun a ⟨i, _, he⟩ => ⟨i, he⟩)

/-- A face selects at most one sign per label and leaves a spanning complement. -/
def signedComplex (c : L → A) : PreAbstractSimplicialComplex (L × Bool) where
  faces := {S | S.Nonempty ∧ (∀ i, (i, true) ∈ S → (i, false) ∉ S) ∧
    unusedSpan c S = AddSubgroup.closure (Set.range c)}
  isRelLowerSet_faces := by
    rintro S ⟨hS, hsign, hspan⟩
    refine ⟨hS, ?_⟩
    intro T hTS hT
    refine ⟨hT, (fun i hi hn => hsign i (hTS hi) (hTS hn)), ?_⟩
    apply le_antisymm (unusedSpan_le c T)
    rw [← hspan]
    exact AddSubgroup.closure_mono
      (fun a ⟨i, hi, he⟩ => ⟨i, fun b hb => hi b (hTS hb), he⟩)

private noncomputable def splitWeight (x : L → ℝ) (z : L × Bool) : ℝ :=
  if z.2 then max (x z.1) 0 else max (-x z.1) 0

private def signedDifference (w : L × Bool → ℝ) (i : L) : ℝ :=
  w (i, true) - w (i, false)

variable [DecidableEq L]

private theorem splitWeight_nonneg (x : L → ℝ) (z : L × Bool) :
    0 ≤ splitWeight x z := by
  unfold splitWeight
  split <;> exact le_max_right _ _

private theorem splitWeight_sum_pair (x : L → ℝ) (i : L) :
    splitWeight x (i, true) + splitWeight x (i, false) = |x i| := by
  rcases le_total 0 (x i) with h | h
  · simp [splitWeight, max_eq_left h, max_eq_right (neg_nonpos.mpr h), abs_of_nonneg h]
  · simp [splitWeight, max_eq_right h, max_eq_left (neg_nonneg.mpr h), abs_of_nonpos h]

private theorem splitWeight_signs (x : L → ℝ) (i : L) :
    (splitWeight x (i, true) ≠ 0 ↔ 0 < x i) ∧
    (splitWeight x (i, false) ≠ 0 ↔ x i < 0) := by
  rcases lt_trichotomy (x i) 0 with h | h | h
  · simp [splitWeight, max_eq_right h.le, max_eq_left (neg_nonneg.mpr h.le),
      h, h.ne, not_lt_of_ge h.le]
  · simp [splitWeight, h]
  · simp [splitWeight, max_eq_left h.le, max_eq_right (neg_nonpos.mpr h.le),
      h, h.ne', not_lt_of_ge h.le]

private theorem splitWeight_in_realization (c : L → A) (x : link c) :
    splitWeight x.val ∈ realization (signedComplex c) := by
  classical
  let w := splitWeight x.val
  let S := Finset.univ.filter (fun z : L × Bool => w z ≠ 0)
  have hw : ∑ z, w z = 1 := by
    rw [Fintype.sum_prod_type]
    simpa only [Fintype.sum_bool, splitWeight_sum_pair] using x.property.1
  have hnonempty : S.Nonempty := by
    by_contra hn
    have hz : ∀ z, w z = 0 := by
      intro z
      by_contra hnz
      exact hn ⟨z, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hnz⟩⟩
    simp [hz] at hw
  have hComplement : {i : L | ∀ b : Bool, (i, b) ∉ S} = {i | x.val i = 0} := by
    ext i
    change (∀ b, (i, b) ∉ S) ↔ x.val i = 0
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, not_not]
    constructor
    · intro h
      exact le_antisymm (le_of_not_gt (fun hp => (splitWeight_signs x.val i).1.mpr hp (h true)))
        (le_of_not_gt (fun hn => (splitWeight_signs x.val i).2.mpr hn (h false)))
    · intro hi b
      cases b <;> simp [w, splitWeight, hi]
  have hspan : unusedSpan c S = fairSpan c x.val := by
    unfold unusedSpan fairSpan
    rw [hComplement]
    rfl
  have hface : S ∈ signedComplex c := by
    refine ⟨hnonempty, ?_, hspan.trans x.property.2⟩
    intro i hp hn
    have hp' := (splitWeight_signs x.val i).1.mp (Finset.mem_filter.mp hp).2
    have hn' := (splitWeight_signs x.val i).2.mp (Finset.mem_filter.mp hn).2
    exact (not_lt_of_ge hp'.le) hn'
  refine ⟨S, hface, ?_⟩
  rw [← faceSimplex_eq_convexHull]
  exact ⟨splitWeight_nonneg x.val, hw,
    fun z hz => not_ne_iff.mp (fun hn => hz (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hn⟩))⟩

private theorem realization_pair_data (c : L → A) (w : realization (signedComplex c)) :
    (∀ z, 0 ≤ w.val z) ∧ (∑ z, w.val z) = 1 ∧
      ∃ S ∈ signedComplex c, (∀ z ∉ S, w.val z = 0) := by
  obtain ⟨S, hS, hw⟩ := w.property
  rw [← faceSimplex_eq_convexHull] at hw
  exact ⟨hw.1, hw.2.1, S, hS, hw.2.2⟩

private theorem signedDifference_in_link (c : L → A) (w : realization (signedComplex c)) :
    signedDifference w.val ∈ link c := by
  obtain ⟨hn, hsum, S, hS, hz⟩ := realization_pair_data c w
  have hinj : ∀ i, w.val (i, true) = 0 ∨ w.val (i, false) = 0 := by
    intro i
    by_cases h : (i, true) ∈ S
    · exact Or.inr (hz _ (hS.2.1 i h))
    · exact Or.inl (hz _ h)
  have habs (i : L) : |signedDifference w.val i| = w.val (i, true) + w.val (i, false) := by
    rcases hinj i with hp | hm
    · simp [signedDifference, hp, abs_of_nonneg (hn (i, false))]
    · simp [signedDifference, hm, abs_of_nonneg (hn (i, true))]
  refine ⟨?_, ?_⟩
  · simpa only [Fintype.sum_prod_type, Fintype.sum_bool, habs] using hsum
  · apply le_antisymm
    · apply AddSubgroup.closure_mono
      rintro a ⟨i, _, rfl⟩
      exact ⟨i, rfl⟩
    · change unusedSpan c S = AddSubgroup.closure (Set.range c) at hS.2.2
      rw [← hS.2.2]
      apply AddSubgroup.closure_mono
      rintro a ⟨i, hi, rfl⟩
      exact ⟨i, by simp [signedDifference, hz _ (hi true), hz _ (hi false)], rfl⟩

private theorem signedDifference_splitWeight (x : L → ℝ) :
    signedDifference (splitWeight x) = x := by
  funext i
  rcases le_total 0 (x i) with h | h
  · simp [signedDifference, splitWeight, max_eq_left h, max_eq_right (neg_nonpos.mpr h)]
  · simp [signedDifference, splitWeight, max_eq_right h, max_eq_left (neg_nonneg.mpr h)]

private theorem splitWeight_signedDifference (c : L → A) (w : realization (signedComplex c)) :
    splitWeight (signedDifference w.val) = w.val := by
  obtain ⟨hn, _, S, hS, hz⟩ := realization_pair_data c w
  funext z
  obtain ⟨i, b⟩ := z
  by_cases h : (i, true) ∈ S
  · have hm : w.val (i, false) = 0 := hz _ (hS.2.1 i h)
    have hp := hn (i, true)
    cases b <;> simp [splitWeight, signedDifference, hm, max_eq_left hp,
      max_eq_right (neg_nonpos.mpr hp)]
  · have hp : w.val (i, true) = 0 := hz _ h
    have hm := hn (i, false)
    cases b <;> simp [splitWeight, signedDifference, hp, max_eq_left hm,
      max_eq_right (neg_nonpos.mpr hm)]

private theorem continuous_splitWeight : Continuous (splitWeight : (L → ℝ) → L × Bool → ℝ) := by
  apply continuous_pi
  rintro ⟨i, b⟩
  cases b
  · simpa only [splitWeight, Bool.false_eq_true, ite_false] using
      (continuous_apply i).neg.max continuous_const
  · simpa only [splitWeight, ite_true] using (continuous_apply i).max continuous_const

private theorem continuous_signedDifference :
    Continuous (signedDifference : (L × Bool → ℝ) → L → ℝ) :=
  continuous_pi (fun i => (continuous_apply (i, true)).sub (continuous_apply (i, false)))

/-- Positive and negative parts identify the fair-bias link with the barycentric realization.
The nonzero weights record the signed support of the original direction. -/
theorem fair_bias_link_realization (c : L → A) :
    ∃ e : link c ≃ₜ realization (signedComplex c),
      ∀ x i,
        (e x).val (i, true) = max (x.val i) 0 ∧
        (e x).val (i, false) = max (-x.val i) 0 := by
  let e : link c ≃ₜ realization (signedComplex c) :=
    { toFun := fun x => ⟨splitWeight x.val, splitWeight_in_realization c x⟩
      invFun := fun w => ⟨signedDifference w.val, signedDifference_in_link c w⟩
      left_inv := fun x => Subtype.ext (signedDifference_splitWeight x.val)
      right_inv := fun w => Subtype.ext (splitWeight_signedDifference c w)
      continuous_toFun := (continuous_splitWeight.comp continuous_subtype_val).subtype_mk _
      continuous_invFun := (continuous_signedDifference.comp continuous_subtype_val).subtype_mk _ }
  exact ⟨e, fun _ _ => ⟨rfl, rfl⟩⟩

end D5.S3.TotalVariation.FairBiasLink
