module

public import Mathlib.Analysis.Complex.Order
public import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic

/-! # Entrywise fourth-root phase averaging on the Choi carrier -/

@[expose] public section

namespace D5.S3.Quantum.Measurement.AuricFourthPhase

open Complex Matrix Finset
open scoped BigOperators

variable {a : Type*} [Fintype a] [DecidableEq a]

/-- The Choi character for phasing a single input and output coordinate. -/
def character (u : a) (entry : a × a) : ℂ :=
  if entry.1 = entry.2 then 1 else
    if u = entry.1 then I else if u = entry.2 then -I else 1

private theorem character_cases (u : a) (p : a × a) :
    character u p = 1 ∨ character u p = I ∨ character u p = -I := by
  unfold character
  split_ifs <;> simp

/-- The actual average over the phases 1, i, -1 and -i in one coordinate. -/
noncomputable def coordinateAverage (u : a) (p q : a × a) : ℂ :=
  let z := character u p * star (character u q)
  (1 + z + z ^ 2 + z ^ 3) / 4

private theorem rootAverage (p q : ℂ)
    (hp : p = 1 ∨ p = I ∨ p = -I) (hq : q = 1 ∨ q = I ∨ q = -I) :
    (1 + p * star q + (p * star q) ^ 2 + (p * star q) ^ 3) / 4 =
      if p = q then 1 else 0 := by
  have hI1 : I ≠ (1 : ℂ) := by
    intro h
    have ht := congrArg Complex.im h
    norm_num at ht
  have hnI1 : -I ≠ (1 : ℂ) := by
    intro h
    have ht := congrArg Complex.im h
    norm_num at ht
  have hInI : I ≠ -I := by
    intro h
    have ht := congrArg Complex.im h
    norm_num at ht
  rcases hp with rfl | rfl | rfl <;> rcases hq with rfl | rfl | rfl
  all_goals simp [hI1, hI1.symm, hnI1, hnI1.symm, hInI, hInI.symm,
    Complex.star_def, Complex.I_mul_I, pow_succ, mul_assoc]
  all_goals ring

theorem coordinateAverage_eq (u : a) (p q : a × a) :
    coordinateAverage u p q = if character u p = character u q then 1 else 0 :=
  rootAverage _ _ (character_cases u p) (character_cases u q)

private theorem same_characters_iff (p q : a × a) :
    (∀ u, character u p = character u q) ↔
      (p.1 = p.2 ∧ q.1 = q.2) ∨ p = q := by
  have hI1 : I ≠ (1 : ℂ) := by
    intro h
    have ht := congrArg Complex.im h
    norm_num at ht
  have hnI1 : -I ≠ (1 : ℂ) := by
    intro h
    have ht := congrArg Complex.im h
    norm_num at ht
  have hInI : I ≠ -I := by
    intro h
    have ht := congrArg Complex.im h
    norm_num at ht
  constructor
  · intro h
    by_cases hp : p.1 = p.2
    · by_cases hq : q.1 = q.2
      · exact Or.inl ⟨hp, hq⟩
      · have hh := h q.1
        simp [character, hp, hq, hI1.symm] at hh
    · by_cases hq : q.1 = q.2
      · have hh := h p.1
        simp [character, hp, hq, hI1] at hh
      · right
        apply Prod.ext
        · by_contra! hneq
          have hh := h p.1
          simp only [character, if_neg hp, if_neg hq, if_pos rfl, if_neg hneq] at hh
          split_ifs at hh <;> contradiction
        · by_contra! hneq
          have hh := h p.2
          have hpval : character p.2 p = -I := by simp [character, hp, Ne.symm hp]
          rw [hpval] at hh
          by_cases hfirst : p.2 = q.1
          · exact hInI ((by simpa only [character, ite_eq_right hq, ite_eq_left hfirst]
              using hh : -I = I).symm)
          · exact hnI1 (by
              simpa only [character, ite_eq_right hq, ite_eq_right hfirst, ite_eq_right hneq]
                using hh)
  · rintro (⟨hp, hq⟩ | rfl) u
    · simp [character, hp, hq]
    · rfl

/-- Independent fourth-root phase averaging preserves the coherences between
diagonal Choi entries and deletes every other off-diagonal coefficient. -/
theorem independent_phase_average (p q : a × a) :
    (∏ u, coordinateAverage u p q) =
      if (p.1 = p.2 ∧ q.1 = q.2) ∨ p = q then 1 else 0 := by
  classical
  by_cases h : (p.1 = p.2 ∧ q.1 = q.2) ∨ p = q
  · have hh := (same_characters_iff p q).2 h
    simp [coordinateAverage_eq, hh, h]
  · have hbad := mt (same_characters_iff p q).1 h
    push Not at hbad
    obtain ⟨u, hu⟩ := hbad
    rw [if_neg h]
    apply Finset.prod_eq_zero (Finset.mem_univ u)
    simp [coordinateAverage_eq, hu]

end D5.S3.Quantum.Measurement.AuricFourthPhase
