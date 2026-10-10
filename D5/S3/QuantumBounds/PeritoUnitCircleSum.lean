/- GID: D5/S3/QuantumBounds/PeritoUnitCircleSum
   generality: G
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Bound the regular unit-circle distance sum by twice the half-angle cosecant. -/

import D5.S3.Observer.WindowRegister
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex

/-!
# A regular unit-circle sum bound

A cyclic shift of the samples preserves their absolute cosine sum. Reducing
its phase to a half-open interval puts every sampled cosine in the nonnegative
half-circle. The finite cosine sum formula then gives a uniform bound.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open scoped BigOperators
open D5.S3.Observer.WindowRegister

namespace D5.S3.QuantumBounds.PeritoUnitCircleSum

private lemma abs_cos_sum_periodic (d : ℕ) (hd : 0 < d) :
    Function.Periodic (fun s : ℝ => ∑ y ∈ Finset.range d,
      |Real.cos (s + Real.pi / d * y)|) (Real.pi / d) := by
  intro s
  change (∑ y ∈ Finset.range d, |Real.cos (s + Real.pi / d + Real.pi / d * y)|) = _
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  have hend : |Real.cos (s + Real.pi / d * d)| = |Real.cos s| := by
    rw [div_mul_cancel₀ _ hdR, Real.cos_add_pi, abs_neg]
  have hshift : (∑ y ∈ Finset.range d, |Real.cos (s + Real.pi / d + Real.pi / d * y)|) =
      ∑ y ∈ Finset.range d, |Real.cos (s + Real.pi / d * (y + 1))| := by
    apply Finset.sum_congr rfl
    intro y hy
    congr 2
    ring
  rw [hshift]
  have h := Finset.sum_range_succ' (fun y : ℕ => |Real.cos (s + Real.pi / d * y)|) d
  rw [Finset.sum_range_succ, hend] at h
  simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, mul_zero, add_zero] at h
  exact (add_right_cancel h).symm

private lemma abs_cos_sum_le (d : ℕ) (hd : 2 ≤ d) (s : ℝ) :
    ∑ y ∈ Finset.range d, |Real.cos (s + Real.pi / d * y)| ≤
      1 / Real.sin (Real.pi / (2 * (d : ℝ))) := by
  have hd0 : 0 < d := by omega
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd0
  have ha : 0 < Real.pi / (d : ℝ) := div_pos Real.pi_pos hdR
  obtain ⟨k, hk, _⟩ := existsUnique_sub_zsmul_mem_Ico ha s (-(Real.pi / 2))
  let t := s - k • (Real.pi / (d : ℝ))
  have ht : t ∈ Set.Ico (-(Real.pi / 2)) (-(Real.pi / 2) + Real.pi / d) := hk
  rw [← (abs_cos_sum_periodic d hd0).sub_zsmul_eq k]
  change (∑ y ∈ Finset.range d, |Real.cos (t + Real.pi / d * y)|) ≤ _
  have hcos : ∀ y ∈ Finset.range d, 0 ≤ Real.cos (t + Real.pi / d * y) := by
    intro y hy
    have hyR : (y : ℝ) + 1 ≤ (d : ℝ) := by exact_mod_cast Finset.mem_range.mp hy
    apply Real.cos_nonneg_of_mem_Icc
    constructor
    · have : 0 ≤ Real.pi / d * (y : ℝ) := mul_nonneg ha.le (Nat.cast_nonneg y)
      linarith [ht.1]
    · have hprod := mul_le_mul_of_nonneg_left hyR ha.le
      have hcancel : Real.pi / d * d = Real.pi := div_mul_cancel₀ _ hdR.ne'
      nlinarith [ht.2]
  rw [Finset.sum_congr rfl (fun y hy => abs_of_nonneg (hcos y hy))]
  have hsum := Real.sin_mul_sum_cos d (Real.pi / d) t
  have horder : (∑ y ∈ Finset.range d, Real.cos (Real.pi / d * y + t)) =
      ∑ y ∈ Finset.range d, Real.cos (t + Real.pi / d * y) := by
    apply Finset.sum_congr rfl
    intro y hy
    rw [add_comm]
  rw [horder] at hsum
  have harg : (d : ℝ) * (Real.pi / d) / 2 = Real.pi / 2 := by
    field_simp
  have hhalf : Real.pi / (d : ℝ) / 2 = Real.pi / (2 * d) := by ring
  rw [harg, Real.sin_pi_div_two, one_mul, hhalf] at hsum
  have hspos : 0 < Real.sin (Real.pi / (2 * (d : ℝ))) := by
    apply Real.sin_pos_of_pos_of_lt_pi
    · positivity
    · have htwo : 1 < 2 * (d : ℝ) := by exact_mod_cast (show 1 < 2 * d by omega)
      exact (div_lt_self Real.pi_pos htwo)
  apply (le_div_iff₀ hspos).mpr
  rw [mul_comm]
  rw [hsum]
  exact Real.cos_le_one _

private lemma norm_one_add_exp_two_mul_i (t : ℝ) :
    ‖1 + Complex.exp ((2 * t : ℝ) * Complex.I)‖ = 2 * |Real.cos t| := by
  have hfactor : 1 + Complex.exp ((2 * t : ℝ) * Complex.I) =
      ((2 * Real.cos t : ℝ) : ℂ) * Complex.exp ((t : ℂ) * Complex.I) := by
    simp only [Complex.ofReal_mul, Complex.ofReal_ofNat, Complex.ofReal_cos]
    rw [Complex.two_cos, add_mul,
      ← Complex.exp_add, ← Complex.exp_add]
    have hneg : -(t : ℂ) * Complex.I + (t : ℂ) * Complex.I = 0 := by ring
    rw [hneg, Complex.exp_zero, add_comm]
    congr 2
    ring
  rw [hfactor, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul]
  simp [Complex.norm_exp]

/-- The regular unit-circle distance sum is bounded uniformly in its phase. -/
theorem unit_circle_sum_le (d : ℕ) (hd : 2 ≤ d) (z : ℂ) (hz : ‖z‖ = 1) :
    ∑ y : Fin d, ‖1 + windowRoot d ^ (y : ℕ) * z‖ ≤
      2 / Real.sin (Real.pi / (2 * (d : ℝ))) := by
  let s : ℝ := z.arg / 2
  have hzexp : z = Complex.exp ((2 * s : ℝ) * Complex.I) := by
    have h := Complex.norm_mul_exp_arg_mul_I z
    rw [hz, Complex.ofReal_one, one_mul] at h
    convert h.symm using 2
    dsimp [s]
    push_cast
    ring
  have hterm (y : ℕ) : ‖1 + windowRoot d ^ y * z‖ =
      2 * |Real.cos (s + Real.pi / d * y)| := by
    rw [hzexp, windowRoot, ← Complex.exp_nat_mul, ← Complex.exp_add]
    convert norm_one_add_exp_two_mul_i (s + Real.pi / d * y) using 3
    push_cast
    ring_nf
  simp_rw [hterm]
  rw [← Finset.mul_sum]
  rw [Fin.sum_univ_eq_sum_range (fun y : ℕ => |Real.cos (s + Real.pi / d * y)|) d]
  calc
    _ ≤ 2 * (1 / Real.sin (Real.pi / (2 * (d : ℝ)))) :=
      mul_le_mul_of_nonneg_left (abs_cos_sum_le d hd s) (by norm_num)
    _ = _ := by ring

end D5.S3.QuantumBounds.PeritoUnitCircleSum
