/- GID: D5/S1/Words/Powers/GoldenDesubstitutionZeckendorf
   generality: I
   mirror-B: D5/B/S1/Words/Powers/GoldenDesubstitutionZeckendorf
   mirror-E: none(waiver:block-boundary-bookkeeping)
   anchors: []
   digest: Golden desubstitution terminals are identified by shifted Zeckendorf digits. -/

import D5.S1.Words.Powers.GoldenDesubstitutionNormalForm
import D5.S1.Deficit.ZeckendorfDisplacementReading

namespace GoldenDesubstitutionZeckendorf

open D5.S0.Conventions
open D5.S1.Words
open D5.S1.Words.Powers
open D5.S1.Deficit.ZeckendorfDisplacementReading
open GoldenDesubstitutionNormalForm

local instance : IsTrans ℕ (fun a b ↦ b + 2 ≤ a) where
  trans _ _ _ hab hbc := by omega

/-- Golden substitution block starts are the Zeckendorf up-shift displacement reading. -/
theorem golden_subst_start_eq_displacement_decode (n : Nat) :
    goldenSubstStart n = displacementDecode n := by
  have hinvFloor : ⌊Real.goldenRatio⁻¹⌋ = (0 : Int) := by
    rw [Int.floor_eq_zero_iff]
    exact ⟨(inv_pos.mpr Real.goldenRatio_pos).le,
      inv_lt_one_of_one_lt₀ Real.one_lt_goldenRatio⟩
  have hcount := goldenWindowTrueCount_eq_floor 0 n
  simp only [Nat.zero_add, Nat.cast_add, Nat.cast_one] at hcount
  simp only [one_mul] at hcount
  rw [hinvFloor, sub_zero] at hcount
  have hphi : Real.goldenRatio = 1 + Real.goldenRatio⁻¹ := by
    rw [Real.inv_goldenRatio]
    linarith [Real.goldenRatio_add_goldenConj]
  have hfloor :
      ⌊(((n : Real) + 1) * Real.goldenRatio)⌋ =
        (n : Int) + 1 + ⌊(((n : Real) + 1) * Real.goldenRatio⁻¹)⌋ := by
    have hexpand : ((n : Real) + 1) * (1 + Real.goldenRatio⁻¹) =
        ((n + 1 : Nat) : Real) + (((n : Real) + 1) * Real.goldenRatio⁻¹) := by
      push_cast
      ring
    conv_lhs => rw [hphi]
    rw [hexpand, Int.floor_natCast_add]
    push_cast
    ring
  have hstart : (goldenSubstStart n : Int) =
      ⌊(((n : Real) + 1) * Real.goldenRatio)⌋ - 1 := by
    rw [goldenSubstStart]
    push_cast
    rw [hcount, hfloor]
    ring
  have hdecode := displacement_decode_eq_beatty_floor n
  exact_mod_cast hstart.trans hdecode.symm

private theorem shifted_wdigits_isCanonical (n r : Nat) :
    ((wdigits n).map fun k => k + r).IsZeckendorfRep := by
  have hcanonical := wdigits_isCanonical n
  rw [List.IsZeckendorfRep, List.isChain_iff_pairwise] at hcanonical ⊢
  rw [List.pairwise_append] at hcanonical ⊢
  refine ⟨?_, by simp, ?_⟩
  · rw [List.pairwise_map]
    exact hcanonical.1.imp fun h => by omega
  · intro a ha b hb
    simp only [List.mem_map] at ha
    rcases ha with ⟨k, hk, rfl⟩
    simp only [List.mem_singleton] at hb
    subst b
    have := hcanonical.2.2 k hk 0 (by simp)
    omega

/-- A golden substitution block start shifts every occupied Zeckendorf index by one. -/
theorem golden_subst_start_wdigits (n : Nat) :
    wdigits (goldenSubstStart n) = (wdigits n).map (fun k => k + 1) := by
  rw [golden_subst_start_eq_displacement_decode]
  symm
  apply wdigits_unique (shifted_wdigits_isCanonical n 1)
  rw [List.map_map]
  simp [Function.comp_def, displacementDecode]

private theorem eq_of_wdigits_eq {n m : Nat} (h : wdigits n = wdigits m) : n = m := by
  rw [← decode_wdigits n, ← decode_wdigits m, h]

private theorem desubStep_wdigits {x y : Nat} (h : desubStep x y) :
    wdigits x = (wdigits y).map (fun k => k + 1) := by
  rw [← h.2]
  exact golden_subst_start_wdigits y

private def desubIter : Nat → Nat → Nat
  | 0, m => m
  | r + 1, m => goldenSubstStart (desubIter r m)

private theorem desubIter_wdigits (r m : Nat) :
    wdigits (desubIter r m) = (wdigits m).map (fun k => k + r) := by
  induction r with
  | zero => simp [desubIter]
  | succ r ih =>
      rw [desubIter, golden_subst_start_wdigits, ih, List.map_map]
      simp [Function.comp_def, Nat.add_assoc]

private theorem desubIter_ne_zero {m : Nat} (hm : m ≠ 0) (r : Nat) :
    desubIter r m ≠ 0 := by
  induction r with
  | zero => simpa [desubIter]
  | succ r ih =>
      rw [desubIter, goldenSubstStart]
      omega

private theorem desubIter_zero (r : Nat) : desubIter r 0 = 0 := by
  induction r with
  | zero => rfl
  | succ r ih => simp [desubIter, ih, goldenSubstStart_zero]

private theorem desubIter_path {m : Nat} (hm : m ≠ 0) (r : Nat) :
    Relation.ReflTransGen desubStep (desubIter r m) m := by
  induction r with
  | zero => exact .refl
  | succ r ih =>
      exact .head ⟨desubIter_ne_zero hm (r + 1), rfl⟩ ih

/-- Iterated golden desubstitution is exactly a uniform downward shift of Zeckendorf indices. -/
theorem golden_desubstitution_path_iff (n m : Nat) :
    Relation.ReflTransGen desubStep n m ↔
      ∃ r, wdigits n = (wdigits m).map (fun k => k + r) := by
  constructor
  · intro hpath
    induction hpath using Relation.ReflTransGen.head_induction_on with
    | refl => exact ⟨0, by simp⟩
    | head hstep _ ih =>
        obtain ⟨r, hr⟩ := ih
        refine ⟨r + 1, ?_⟩
        rw [desubStep_wdigits hstep, hr, List.map_map]
        simp [Function.comp_def, Nat.add_assoc]
  · rintro ⟨r, hr⟩
    by_cases hm : m = 0
    · subst m
      have hn : n = 0 := by
        apply eq_of_wdigits_eq
        simpa [wdigits] using hr
      subst n
      exact .refl
    · have hn : n = desubIter r m := by
        apply eq_of_wdigits_eq
        exact hr.trans (desubIter_wdigits r m).symm
      subst n
      exact desubIter_path hm r

/-- A terminal golden desubstitution path is zero, or ends at a number whose least
Zeckendorf digit is occupied; all earlier indices are uniform upward digit shifts. -/
theorem golden_desubstitution_terminal_iff (n m : Nat) :
    (Relation.ReflTransGen desubStep n m ∧ (m = 0 ∨ goldenWord m = false)) ↔
      (n = 0 ∧ m = 0) ∨
        ∃ r, 2 ∈ wdigits m ∧ wdigits n = (wdigits m).map (fun k => k + r) := by
  constructor
  · rintro ⟨hpath, hm | hfalse⟩
    · subst m
      obtain ⟨r, hr⟩ := (golden_desubstitution_path_iff n 0).mp hpath
      left
      refine ⟨?_, rfl⟩
      apply eq_of_wdigits_eq
      simpa [wdigits] using hr
    · right
      obtain ⟨r, hr⟩ := (golden_desubstitution_path_iff n m).mp hpath
      refine ⟨r, ?_, hr⟩
      rw [goldenWord_eq_zeckendorf_criterion] at hfalse
      by_contra htwo
      simp [htwo] at hfalse
  · rintro (⟨rfl, rfl⟩ | ⟨r, htwo, hr⟩)
    · exact ⟨.refl, Or.inl rfl⟩
    · refine ⟨(golden_desubstitution_path_iff n m).mpr ⟨r, hr⟩, Or.inr ?_⟩
      rw [goldenWord_eq_zeckendorf_criterion]
      simp [htwo]

example :
    Relation.ReflTransGen desubStep 2 1 ∧ (1 = 0 ∨ goldenWord 1 = false) := by
  rw [golden_desubstitution_terminal_iff]
  right
  have hone : wdigits 1 = [2] := by
    symm
    apply wdigits_unique
    · norm_num [List.IsZeckendorfRep]
    · norm_num [Nat.fib]
  have hstart : goldenSubstStart 1 = 2 := by
    simpa [goldenSubstStart_zero] using goldenSubstStart_step_true goldenWord_zero
  refine ⟨1, by simp [hone], ?_⟩
  rw [← hstart]
  exact golden_subst_start_wdigits 1

end GoldenDesubstitutionZeckendorf
