/- GID: D5/S3/Observer/GoldenPrimeCircle/GoldenClockWindowCriterion
   generality: G
   mirror-B: none(waiver:new-cross-library-adapter)
   mirror-E: none(waiver:exact-all-resolution-window-classification)
   anchors: []
   digest: Classifies every closed unit-width internal window preserved by all golden clock contractions; the sharp cut-offset range is [(1-alpha)/2,(1+alpha)/2]. -/

import D5.S3.Observer.GoldenPrimeCircle.GoldenClockLattice

set_option autoImplicit false

namespace D5.S3.Observer.GoldenPrimeCircle.GoldenClockWindowCriterion

open GoldenClockLattice

noncomputable section

def ClosedWindow (ρ x : ℝ) : Prop := -ρ ≤ x ∧ x ≤ 1 - ρ

def Preserves (ρ d : ℝ) : Prop :=
  ∀ x : ℝ, ClosedWindow ρ x → ClosedWindow ρ (d * x)

lemma preserves_mul (ρ a b : ℝ) (ha : Preserves ρ a) (hb : Preserves ρ b) :
    Preserves ρ (a * b) := by
  intro x hx
  simpa only [mul_assoc] using ha (b * x) (hb x hx)

lemma nonnegative_preserves (ρ d : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (hd0 : 0 ≤ d) (hd1 : d ≤ 1) : Preserves ρ d := by
  rintro x ⟨hx0, hx1⟩
  have hl := mul_le_mul_of_nonneg_left hx0 hd0
  have hu := mul_le_mul_of_nonneg_left hx1 hd0
  have hp := mul_nonneg (sub_nonneg.mpr hd1) hρ0
  have hq := mul_nonneg (sub_nonneg.mpr hd1) (sub_nonneg.mpr hρ1)
  constructor <;> nlinarith

/-- A reflected contraction is tested exactly at the two endpoints. -/
theorem negative_preserves_iff (ρ q : ℝ) (hq : 0 ≤ q) :
    Preserves ρ (-q) ↔ q * (1 - ρ) ≤ ρ ∧ q * ρ ≤ 1 - ρ := by
  constructor
  · intro h
    have hl := h (-ρ) (by constructor <;> linarith)
    have hr := h (1 - ρ) (by constructor <;> linarith)
    rcases hl with ⟨hl0, hl1⟩
    rcases hr with ⟨hr0, hr1⟩
    constructor <;> nlinarith
  · rintro ⟨h0, h1⟩ x ⟨hx0, hx1⟩
    have hl := mul_le_mul_of_nonneg_left hx0 hq
    have hr := mul_le_mul_of_nonneg_left hx1 hq
    constructor <;> nlinarith

lemma alpha_cube_eq : alpha ^ 3 = 2 * alpha - 1 := by
  linear_combination alpha * alpha_sq_add - alpha_sq_add

/-- Every scale is controlled by the first positive and the first negative contraction. -/
theorem all_resolutions_iff (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) :
    (∀ L : ℕ, Preserves ρ (signedWidth L)) ↔
      alpha ^ 3 * (1 - ρ) ≤ ρ ∧ alpha ^ 3 * ρ ≤ 1 - ρ := by
  have hd0 : signedWidth 0 = alpha ^ 2 := by
    dsimp [signedWidth, alpha]
    ring
  have hd1 : signedWidth 1 = -(alpha ^ 3) := by
    dsimp [signedWidth, alpha]
    ring
  have hp : Preserves ρ (alpha ^ 2) := nonnegative_preserves ρ (alpha ^ 2)
    hρ0 hρ1 (sq_nonneg _) (by nlinarith [alpha_sq_add, alpha_pos])
  constructor
  · intro h
    have h1 := h 1
    rw [hd1] at h1
    exact (negative_preserves_iff ρ (alpha ^ 3) (le_of_lt (pow_pos alpha_pos _))).mp h1
  · intro h L
    have hn : Preserves ρ (-(alpha ^ 3)) :=
      (negative_preserves_iff ρ (alpha ^ 3) (le_of_lt (pow_pos alpha_pos _))).mpr h
    induction L using Nat.twoStepInduction with
    | zero => simpa only [hd0] using hp
    | one => simpa only [hd1] using hn
    | more L ih0 ih1 =>
        rw [signedWidth_two]
        exact preserves_mul ρ (alpha ^ 2) (signedWidth L) hp ih0

/-- Sharp offset interval for CLOSED real windows. This is not a statement about only
sampled integer orbit points; half-open endpoint conventions are retained by the section modules. -/
theorem sharp_offset_interval (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) :
    (∀ L : ℕ, Preserves ρ (signedWidth L)) ↔
      (1 - alpha) / 2 ≤ ρ ∧ ρ ≤ (1 + alpha) / 2 := by
  rw [all_resolutions_iff ρ hρ0 hρ1]
  have hp : 0 < 1 + alpha ^ 3 := by positivity
  have hlo : (1 + alpha ^ 3) * ((1 - alpha) / 2) = alpha ^ 3 := by
    rw [alpha_cube_eq]
    nlinarith [alpha_sq_add]
  have hhi : (1 + alpha ^ 3) * ((1 + alpha) / 2) = 1 := by
    rw [alpha_cube_eq]
    nlinarith [alpha_sq_add]
  constructor
  · rintro ⟨h0, h1⟩
    constructor
    · by_contra h
      have hlt : ρ < (1 - alpha) / 2 := lt_of_not_ge h
      have hh := mul_pos hp (sub_pos.mpr hlt)
      nlinarith [hlo]
    · by_contra h
      have hlt : (1 + alpha) / 2 < ρ := lt_of_not_ge h
      have hh := mul_pos hp (sub_pos.mpr hlt)
      nlinarith [hhi]
  · rintro ⟨h0, h1⟩
    have hl := mul_le_mul_of_nonneg_left h0 (le_of_lt hp)
    have hh := mul_le_mul_of_nonneg_left h1 (le_of_lt hp)
    constructor <;> nlinarith [hlo, hhi]

/-- Outside the sharp range the failure already occurs at resolution one. -/
theorem outside_range_fails_at_one (ρ : ℝ)
    (h : ρ < (1 - alpha) / 2 ∨ (1 + alpha) / 2 < ρ)
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) : ¬ Preserves ρ (signedWidth 1) := by
  intro hp
  have hd1 : signedWidth 1 = -(alpha ^ 3) := by
    dsimp [signedWidth, alpha]
    ring
  rw [hd1] at hp
  have hc := (negative_preserves_iff ρ (alpha ^ 3) (le_of_lt (pow_pos alpha_pos _))).mp hp
  have hall := (all_resolutions_iff ρ hρ0 hρ1).mpr hc
  have hr := (sharp_offset_interval ρ hρ0 hρ1).mp hall
  rcases h with h | h <;> linarith [hr.1, hr.2]

end
end D5.S3.Observer.GoldenPrimeCircle.GoldenClockWindowCriterion
