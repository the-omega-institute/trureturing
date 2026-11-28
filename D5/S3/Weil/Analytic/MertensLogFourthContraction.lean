/- GID: D5/S3/Weil/Analytic/MertensLogFourthContraction
   generality: I
   mirror-B: none(waiver:mobius-log-fourth-support)
   mirror-E: none(waiver:mobius-log-fourth)
   anchors: []
   utility: none
   digest: An eighth-root cutoff contracts the fourth-logarithmic prefix envelope. -/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option autoImplicit false

noncomputable section

namespace MertensLogFourthContraction

open Set

/-- The cutoff used in the finite hyperbola split. -/
def cutoff (x : ℝ) : ℝ := x ^ (1 / 8 : ℝ)

theorem cutoff_pos {x : ℝ} (hx : 0 < x) : 0 < cutoff x :=
  Real.rpow_pos_of_pos hx _

theorem cutoff_ge_one {x : ℝ} (hx : 1 ≤ x) : 1 ≤ cutoff x :=
  Real.one_le_rpow hx (by norm_num)

theorem cutoff_le {x : ℝ} (hx : 1 ≤ x) : cutoff x ≤ x :=
  Real.rpow_le_self_of_one_le hx (by norm_num)

theorem log_cutoff {x : ℝ} (hx : 0 < x) : Real.log (cutoff x) = (1 / 8) * Real.log x :=
  Real.log_rpow hx _

theorem log_div_cutoff {x : ℝ} (hx : 0 < x) :
    Real.log (x / cutoff x) = (7 / 8) * Real.log x := by
  rw [Real.log_div hx.ne' (cutoff_pos hx).ne', log_cutoff hx]
  ring

/-- The fourth logarithmic power varies by less than a factor of two on the
range contributing to the head of the hyperbola sum. -/
theorem log_fourth_le_twice {x t : ℝ} (hx : 1 ≤ x) (ht : x / cutoff x ≤ t) :
    Real.log x ^ 4 ≤ 2 * Real.log t ^ 4 := by
  have hx₀ : 0 < x := zero_lt_one.trans_le hx
  have hxY : 0 < x / cutoff x := div_pos hx₀ (cutoff_pos hx₀)
  have hlog : (7 / 8 : ℝ) * Real.log x ≤ Real.log t := by
    rw [← log_div_cutoff hx₀]
    exact Real.log_le_log hxY ht
  calc
    Real.log x ^ 4 = 1 * Real.log x ^ 4 := (one_mul _).symm
    _ ≤ (2 * (7 / 8 : ℝ) ^ 4) * Real.log x ^ 4 :=
      mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
    _ = 2 * ((7 / 8 : ℝ) * Real.log x) ^ 4 := by ring
    _ ≤ 2 * Real.log t ^ 4 := by
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (mul_nonneg (by norm_num) (Real.log_nonneg hx)) hlog 4)
        (by norm_num)

/-- On the part of the hyperbola above the cutoff quotient, the normalized
bound provides one common denominator for the head and the upper integral. -/
theorem bound_on_cutoff_interval {f : ℝ → ℝ} {x t R : ℝ} (hx : 1 < x)
    (ht : x / cutoff x ≤ t) (hR : |f t| * Real.log t ^ 4 / t ≤ R) :
    |f t| ≤ R * t / Real.log (x / cutoff x) ^ 4 := by
  have hx₀ : 0 < x := zero_lt_one.trans hx
  have hcut₀ : 0 < x / cutoff x := div_pos hx₀ (cutoff_pos hx₀)
  have ht₀ : 0 < t := hcut₀.trans_le ht
  have hlog : 0 < Real.log (x / cutoff x) := by
    rw [log_div_cutoff hx₀]
    exact mul_pos (by norm_num) (Real.log_pos hx)
  apply (le_div_iff₀ (pow_pos hlog _)).2
  calc
    _ ≤ |f t| * Real.log t ^ 4 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hlog.le (Real.log_le_log hcut₀ ht) 4)
        (abs_nonneg _)
    _ ≤ R * t := (div_le_iff₀ ht₀).1 hR

/-- The finite recurrence estimates give a uniform fourth-logarithmic-power
bound. The recurrence takes an envelope only on the range from the cutoff
quotient to the current scale. -/
theorem fourth_log_bound_of_recurrence (f : ℝ → ℝ) {C D X₀ : ℝ}
    (hC : 0 ≤ C) (hD : 0 ≤ D) (hX₀ : 1 ≤ X₀)
    (htrivial : ∀ x ≥ (1 : ℝ), |f x| ≤ x)
    (hrec : ∀ x ≥ X₀, ∀ R ≥ (0 : ℝ),
      (∀ t ∈ Icc (x / cutoff x) x, |f t| * Real.log t ^ 4 / t ≤ R) →
      Real.log x * |f x| ≤
        (x / Real.log (x / cutoff x) ^ 4) *
          (R * (2 * Real.log (cutoff x) + C + 1)) +
        D * x / Real.log x ^ 3) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x > (1 : ℝ), |f x| ≤ K * x / Real.log x ^ 4 := by
  let X : ℝ := max X₀ (Real.exp (8 * (C + 1) + 1))
  let K : ℝ := max (Real.log X ^ 4) (4 * D)
  have hXOne : 1 ≤ X := hX₀.trans (le_max_left _ _)
  refine ⟨K, (pow_nonneg (Real.log_nonneg hXOne) 4).trans (le_max_left _ _), ?_⟩
  intro T hT
  let r (x : ℝ) : ℝ := |f x| * Real.log x ^ 4 / x
  let values := r '' Icc (1 : ℝ) T
  have hT₀ : 0 < T := zero_lt_one.trans hT
  have initial_bound {x z : ℝ} (hx : 1 ≤ x) (hxz : x ≤ z) : r x ≤ Real.log z ^ 4 := by
    have hx₀ : 0 < x := zero_lt_one.trans_le hx
    change |f x| * Real.log x ^ 4 / x ≤ _
    calc
      _ ≤ x * Real.log x ^ 4 / x := by
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right (htrivial x hx) (by positivity)) hx₀.le
      _ = Real.log x ^ 4 := by rw [mul_comm x, mul_div_cancel_right₀ _ hx₀.ne']
      _ ≤ Real.log z ^ 4 :=
        pow_le_pow_left₀ (Real.log_nonneg hx) (Real.log_le_log hx₀ hxz) 4
  have hvalues : values.Nonempty := ⟨r T, T, ⟨hT.le, le_rfl⟩, rfl⟩
  have hbounded : BddAbove values := ⟨Real.log T ^ 4, by
    rintro _ ⟨x, hx, rfl⟩
    exact initial_bound hx.1 hx.2⟩
  let R := sSup values
  have hr {x : ℝ} (hx : x ∈ Icc (1 : ℝ) T) : r x ≤ R :=
    le_csSup hbounded ⟨x, hx, rfl⟩
  have hrT₀ : 0 ≤ r T := by
    dsimp [r]
    positivity
  have hR : 0 ≤ R := hrT₀.trans (hr ⟨hT.le, le_rfl⟩)
  have hsup : R ≤ max (Real.log X ^ 4) (D + (3 / 4 : ℝ) * R) := by
    apply csSup_le hvalues
    rintro _ ⟨x, hx, rfl⟩
    by_cases hxX : x ≤ X
    · exact (initial_bound hx.1 hxX).trans (le_max_left _ _)
    have hXx : X ≤ x := le_of_not_ge hxX
    have hxrec : X₀ ≤ x := (le_max_left _ _).trans hXx
    have hx₀ : 0 < x := zero_lt_one.trans_le hx.1
    have hlog : 8 * (C + 1) + 1 ≤ Real.log x := by
      rw [← Real.log_exp (8 * (C + 1) + 1)]
      exact Real.log_le_log (Real.exp_pos _) ((le_max_right _ _).trans hXx)
    have hlogpos : 0 < Real.log x := by linarith
    have hquotient : 1 ≤ x / cutoff x := by
      apply (le_div_iff₀ (cutoff_pos hx₀)).mpr
      simpa only [one_mul] using cutoff_le hx.1
    have hlocal (t : ℝ) (ht : t ∈ Icc (x / cutoff x) x) :
        |f t| * Real.log t ^ 4 / t ≤ R :=
      hr ⟨hquotient.trans ht.1, ht.2.trans hx.2⟩
    have hrecx := hrec x hxrec R hR hlocal
    have hden : 0 < Real.log (x / cutoff x) ^ 4 := by
      rw [log_div_cutoff hx₀]
      positivity
    have hdistortion : Real.log x ^ 4 / Real.log (x / cutoff x) ^ 4 ≤ 2 :=
      (div_le_iff₀ hden).mpr (log_fourth_le_twice hx.1 le_rfl)
    have hhead : 0 ≤ R * (2 * Real.log (cutoff x) + C + 1) := by
      have hylog := Real.log_nonneg (cutoff_ge_one hx.1)
      positivity
    have hcost : 2 * (2 * Real.log (cutoff x) + C + 1) ≤ (3 / 4 : ℝ) * Real.log x := by
      rw [log_cutoff hx₀]
      linarith only [hlog]
    have hnorm : Real.log x * r x ≤ (D + (3 / 4 : ℝ) * R) * Real.log x := by
      calc
        Real.log x * r x = (Real.log x ^ 4 / x) * (Real.log x * |f x|) := by
          dsimp [r]
          ring
        _ ≤ (Real.log x ^ 4 / x) *
            ((x / Real.log (x / cutoff x) ^ 4) *
              (R * (2 * Real.log (cutoff x) + C + 1)) +
              D * x / Real.log x ^ 3) :=
          mul_le_mul_of_nonneg_left hrecx (by positivity)
        _ = (Real.log x ^ 4 / Real.log (x / cutoff x) ^ 4) *
              (R * (2 * Real.log (cutoff x) + C + 1)) + D * Real.log x := by
          field_simp [hx₀.ne', hlogpos.ne', hden.ne']
          <;> ring
        _ ≤ 2 * (R * (2 * Real.log (cutoff x) + C + 1)) + D * Real.log x :=
          add_le_add (mul_le_mul_of_nonneg_right hdistortion hhead) le_rfl
        _ = R * (2 * (2 * Real.log (cutoff x) + C + 1)) + D * Real.log x := by ring
        _ ≤ R * ((3 / 4 : ℝ) * Real.log x) + D * Real.log x :=
          add_le_add (mul_le_mul_of_nonneg_left hcost hR) le_rfl
        _ = (D + (3 / 4 : ℝ) * R) * Real.log x := by ring
    have hpoint : r x ≤ D + (3 / 4 : ℝ) * R := by
      apply le_of_mul_le_mul_right _ hlogpos
      simpa only [mul_comm (Real.log x) (r x)] using hnorm
    exact hpoint.trans (le_max_right _ _)
  have hRK : R ≤ K := by
    by_cases hRX : R ≤ Real.log X ^ 4
    · exact hRX.trans (le_max_left _ _)
    · have hcontract : R ≤ D + (3 / 4 : ℝ) * R := by
        rcases le_max_iff.mp hsup with h | h
        · exact False.elim (hRX h)
        · exact h
      exact (show R ≤ 4 * D by linarith only [hcontract]).trans (le_max_right _ _)
  have hnormalized : r T ≤ K := (hr ⟨hT.le, le_rfl⟩).trans hRK
  exact (le_div_iff₀ (pow_pos (Real.log_pos hT) _)).2 ((div_le_iff₀ hT₀).1 hnormalized)

end MertensLogFourthContraction
