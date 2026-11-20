/- GID: D5/S3/Analytic/Asymptotics/ExactLacunaryCoefficients
   generality: I
   mirror-B: D5/B/S3/Analytic/Asymptotics/ExactLacunaryCoefficients
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact lacunary coefficients have summable weights and a divergent real second moment. -/

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Algebra.InfiniteSum.Ring

set_option autoImplicit false

namespace ExactLacunaryCoefficients

noncomputable section

def frequency (n : ℕ) : ℝ := (3 : ℝ) ^ (n + 1)

def rho (β γ : ℝ) : ℂ := (β : ℂ) + (γ : ℂ) * Complex.I

def coefficient (β γ : ℝ) : ℂ := 1 / (rho β γ * (1 - rho β γ))

private theorem one_le_frequency (n : ℕ) : 1 ≤ frequency n := by
  unfold frequency
  exact one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 3)

private theorem frequency_pos (n : ℕ) : 0 < frequency n :=
  zero_lt_one.trans_le (one_le_frequency n)

/-- Bounds for the exact coefficient at height `γ`. The lacunary frequencies are at least one. -/
theorem coefficient_bounds {β γ : ℝ} (hβlo : 1 / 2 ≤ β) (hβhi : β ≤ 1)
    (hγ : 1 ≤ γ) :
    1 / (5 * γ ^ 2) ≤ (coefficient β γ).re ∧
    (coefficient β γ).re ≤ 1 / γ ^ 2 ∧
    |(coefficient β γ).im| ≤ 1 / γ ^ 3 := by
  let z : ℂ := rho β γ * (1 - rho β γ)
  let x : ℝ := γ ^ 2 + β * (1 - β)
  let y : ℝ := γ * (1 - 2 * β)
  let d : ℝ := x ^ 2 + y ^ 2
  have hrhore : (rho β γ).re = β := by simp [rho]
  have hrhoim : (rho β γ).im = γ := by simp [rho]
  have hzre : z.re = x := by
    change (rho β γ * (1 - rho β γ)).re = γ ^ 2 + β * (1 - β)
    simp only [Complex.mul_re, Complex.sub_re, Complex.sub_im, Complex.one_re,
      Complex.one_im, hrhore, hrhoim]
    ring
  have hzim : z.im = y := by
    change (rho β γ * (1 - rho β γ)).im = γ * (1 - 2 * β)
    simp only [Complex.mul_im, Complex.sub_re, Complex.sub_im, Complex.one_re,
      Complex.one_im, hrhore, hrhoim]
    ring
  have hnorm : Complex.normSq z = d := by
    simp only [Complex.normSq_apply, hzre, hzim, d, pow_two]
  have hre : (coefficient β γ).re = x / d := by
    change (1 / z).re = x / d
    rw [one_div, Complex.inv_re, hzre, hnorm]
  have him : (coefficient β γ).im = -y / d := by
    change (1 / z).im = -y / d
    rw [one_div, Complex.inv_im, hzim, hnorm]
  have hγpos : 0 < γ := zero_lt_one.trans_le hγ
  have hγsq : 0 < γ ^ 2 := pow_pos hγpos 2
  have hγle_sq : γ ≤ γ ^ 2 := le_self_pow₀ hγ (by decide)
  have hone_le_sq : 1 ≤ γ ^ 2 := hγ.trans hγle_sq
  have hβnonneg : 0 ≤ β := by linarith only [hβlo]
  have hxlo : γ ^ 2 ≤ x :=
    le_add_of_nonneg_right (mul_nonneg hβnonneg (sub_nonneg.mpr hβhi))
  have hxhi : x ≤ 2 * γ ^ 2 := calc
    x ≤ γ ^ 2 + 1 := by
      change γ ^ 2 + β * (1 - β) ≤ γ ^ 2 + 1
      apply add_le_add le_rfl
      calc
        β * (1 - β) ≤ 1 * (1 - β) := mul_le_mul_of_nonneg_right hβhi (sub_nonneg.mpr hβhi)
        _ = 1 - β := one_mul _
        _ ≤ 1 := sub_le_self _ hβnonneg
    _ ≤ 2 * γ ^ 2 := by linarith only [hone_le_sq]
  have hxpos : 0 < x := hγsq.trans_le hxlo
  have hyabs : |y| ≤ γ := by
    have hβabs : |1 - 2 * β| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
    dsimp only [y]
    rw [abs_mul, abs_of_pos hγpos]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hβabs hγpos.le
  have hxsq_le_d : x ^ 2 ≤ d := le_add_of_nonneg_right (sq_nonneg y)
  have hdlo : γ ^ 4 ≤ d := calc
    γ ^ 4 = (γ ^ 2) ^ 2 := by ring
    _ ≤ x ^ 2 := pow_le_pow_left₀ hγsq.le hxlo 2
    _ ≤ d := hxsq_le_d
  have hdhi : d ≤ 5 * γ ^ 4 := calc
    d ≤ (2 * γ ^ 2) ^ 2 + (γ ^ 2) ^ 2 := by
      change x ^ 2 + y ^ 2 ≤ (2 * γ ^ 2) ^ 2 + (γ ^ 2) ^ 2
      refine add_le_add (pow_le_pow_left₀ hxpos.le hxhi 2) ?_
      rw [← sq_abs y]
      exact pow_le_pow_left₀ (abs_nonneg y) (hyabs.trans hγle_sq) 2
    _ = 5 * γ ^ 4 := by ring
  have hdpos : 0 < d := (pow_pos hγpos 4).trans_le hdlo
  have hfive : 0 < 5 * γ ^ 2 := mul_pos (by norm_num) hγsq
  rw [hre, him]
  refine ⟨?_, ?_, ?_⟩
  · apply (div_le_div_iff₀ hfive hdpos).2
    rw [one_mul]
    calc
      d ≤ 5 * γ ^ 4 := hdhi
      _ = γ ^ 2 * (5 * γ ^ 2) := by ring
      _ ≤ x * (5 * γ ^ 2) := mul_le_mul_of_nonneg_right hxlo hfive.le
  · apply (div_le_div_iff₀ hdpos hγsq).2
    rw [one_mul]
    calc
      x * γ ^ 2 ≤ x * x := mul_le_mul_of_nonneg_left hxlo hxpos.le
      _ = x ^ 2 := (pow_two x).symm
      _ ≤ d := hxsq_le_d
  · rw [abs_div, abs_neg, abs_of_pos hdpos]
    apply (div_le_div_iff₀ hdpos (pow_pos hγpos 3)).2
    rw [one_mul]
    calc
      |y| * γ ^ 3 ≤ γ * γ ^ 3 := mul_le_mul_of_nonneg_right hyabs (pow_pos hγpos 3).le
      _ = γ ^ 4 := by ring
      _ ≤ d := hdlo

def realWeight (β : ℕ → ℝ) (t : ℝ) (n : ℕ) : ℝ :=
  Real.exp ((β n - 1) * t) * (coefficient (β n) (frequency n)).re

def imagWeight (β : ℕ → ℝ) (t : ℝ) (n : ℕ) : ℝ :=
  Real.exp ((β n - 1) * t) * (coefficient (β n) (frequency n)).im

private theorem abs_exponent_le_half {β : ℝ} (hlo : 1 / 2 ≤ β) (hhi : β ≤ 1) :
    |β - 1| ≤ 1 / 2 := by
  rw [abs_of_nonpos (sub_nonpos.mpr hhi)]
  linarith only [hlo]

private theorem weighted_bounds {β : ℕ → ℝ} {t : ℝ} (ht : 0 ≤ t) (n : ℕ)
    (hlo : 1 / 2 ≤ β n) (hhi : β n ≤ 1) :
    Real.exp (-t / 2) / (5 * frequency n ^ 2) ≤ realWeight β t n ∧
    realWeight β t n ≤ 1 / frequency n ^ 2 ∧
    |imagWeight β t n| ≤ 1 / frequency n ^ 3 := by
  obtain ⟨hReLo, hReHi, hIm⟩ := coefficient_bounds hlo hhi (one_le_frequency n)
  have hReNonneg : 0 ≤ (coefficient (β n) (frequency n)).re :=
    (div_nonneg zero_le_one
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 5) (sq_nonneg (frequency n)))).trans hReLo
  have heLo : Real.exp (-t / 2) ≤ Real.exp ((β n - 1) * t) := by
    apply Real.exp_le_exp.mpr
    calc
      -t / 2 = -(1 / 2 : ℝ) * t := by ring
      _ ≤ (β n - 1) * t :=
        mul_le_mul_of_nonneg_right (abs_le.mp (abs_exponent_le_half hlo hhi)).1 ht
  have heHi : Real.exp ((β n - 1) * t) ≤ 1 :=
    Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hhi) ht)
  have hePos : 0 < Real.exp ((β n - 1) * t) := Real.exp_pos _
  refine ⟨?_, ?_, ?_⟩
  · unfold realWeight
    calc
      _ = Real.exp (-t / 2) * (1 / (5 * frequency n ^ 2)) := (mul_one_div _ _).symm
      _ ≤ Real.exp (-t / 2) * (coefficient (β n) (frequency n)).re :=
        mul_le_mul_of_nonneg_left hReLo (Real.exp_pos _).le
      _ ≤ _ := mul_le_mul_of_nonneg_right heLo hReNonneg
  · unfold realWeight
    calc
      _ ≤ (coefficient (β n) (frequency n)).re := by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right heHi hReNonneg
      _ ≤ _ := hReHi
  · rw [imagWeight, abs_mul, abs_of_pos hePos]
    calc
      _ ≤ |(coefficient (β n) (frequency n)).im| := by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right heHi (abs_nonneg _)
      _ ≤ _ := hIm

private theorem real_second_moment_lower {β : ℕ → ℝ} {t : ℝ} (ht : 0 ≤ t) (n : ℕ)
    (hlo : 1 / 2 ≤ β n) (hhi : β n ≤ 1) :
    Real.exp (-t / 2) / 5 ≤ realWeight β t n * frequency n ^ 2 := by
  calc
    Real.exp (-t / 2) / 5 =
        (Real.exp (-t / 2) / (5 * frequency n ^ 2)) * frequency n ^ 2 := by
      rw [← div_div]
      exact (div_mul_cancel₀ _ (pow_ne_zero 2 (frequency_pos n).ne')).symm
    _ ≤ _ := mul_le_mul_of_nonneg_right (weighted_bounds ht n hlo hhi).1 (sq_nonneg _)

private theorem summable_inv_frequency_sq : Summable (fun n => 1 / frequency n ^ 2) := by
  have hthree : (3 : ℝ) ^ 2 = 9 := by norm_num
  have hterm (n : ℕ) : 1 / frequency n ^ 2 = (1 / 9 : ℝ) ^ n * (1 / 9) := calc
    1 / frequency n ^ 2 = 1 / (9 : ℝ) ^ (n + 1) := by
      rw [frequency, pow_right_comm (3 : ℝ) (n + 1) 2, hthree]
    _ = (1 / 9 : ℝ) ^ (n + 1) := by simp only [div_pow, one_pow]
    _ = _ := pow_succ _ _
  have hgeo : Summable (fun n : ℕ => (1 / 9 : ℝ) ^ n) :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  simpa only [hterm] using hgeo.mul_right (1 / 9)

/-- The weighted real coefficients have a divergent second moment. The weighted imaginary
coefficients and their first moment are absolutely summable. -/
theorem weighted_summability {β : ℕ → ℝ} {t : ℝ} (ht : 0 ≤ t)
    (hlo : ∀ n, 1 / 2 ≤ β n) (hhi : ∀ n, β n ≤ 1) :
    (∀ n, 0 ≤ realWeight β t n) ∧ Summable (realWeight β t) ∧
    Summable (fun n => |imagWeight β t n|) ∧
    Summable (fun n => |imagWeight β t n * frequency n|) ∧
    ¬ Summable (fun n => realWeight β t n * frequency n ^ 2) := by
  have hb (n : ℕ) := weighted_bounds ht n (hlo n) (hhi n)
  have hA (n : ℕ) : 0 ≤ realWeight β t n :=
    (div_nonneg (Real.exp_pos (-t / 2)).le
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 5) (sq_nonneg (frequency n)))).trans (hb n).1
  have hB (n : ℕ) : |imagWeight β t n| ≤ 1 / frequency n ^ 2 :=
    (hb n).2.2.trans (one_div_pow_le_one_div_pow_of_le (one_le_frequency n) (by decide : 2 ≤ 3))
  have hBγ (n : ℕ) : |imagWeight β t n * frequency n| ≤ 1 / frequency n ^ 2 := by
    rw [abs_mul, abs_of_pos (frequency_pos n)]
    calc
      _ ≤ (1 / frequency n ^ 3) * frequency n :=
        mul_le_mul_of_nonneg_right (hb n).2.2 (frequency_pos n).le
      _ = ((1 / frequency n ^ 2) / frequency n) * frequency n := by
        rw [div_div, pow_succ (frequency n) 2]
      _ = _ := div_mul_cancel₀ _ (frequency_pos n).ne'
  refine ⟨hA, Summable.of_nonneg_of_le hA (fun n => (hb n).2.1) summable_inv_frequency_sq,
    Summable.of_nonneg_of_le (fun _ => abs_nonneg _) hB summable_inv_frequency_sq,
    Summable.of_nonneg_of_le (fun _ => abs_nonneg _) hBγ summable_inv_frequency_sq, ?_⟩
  intro hm
  have hc : 0 < Real.exp (-t / 2) / 5 := div_pos (Real.exp_pos _) (by norm_num)
  have hconst : Summable (fun _ : ℕ => Real.exp (-t / 2) / 5) :=
    Summable.of_nonneg_of_le (fun _ => hc.le)
      (fun n => real_second_moment_lower ht n (hlo n) (hhi n)) hm
  exact (Finite.of_summable_const hc hconst).false

theorem phase_eq_int_turn (n : ℕ) (m : ℤ) :
    ∃ k : ℤ, frequency n * (2 * Real.pi * (m : ℝ)) = (k : ℝ) * (2 * Real.pi) := by
  refine ⟨(3 : ℤ) ^ (n + 1) * m, ?_⟩
  rw [mul_comm (2 * Real.pi) (m : ℝ)]
  simp only [frequency, Int.cast_mul, Int.cast_pow, Int.cast_ofNat, mul_assoc]

end

end ExactLacunaryCoefficients
