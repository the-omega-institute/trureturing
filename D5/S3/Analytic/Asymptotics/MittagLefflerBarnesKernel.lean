/- GID: D5/S3/Analytic/Asymptotics/MittagLefflerBarnesKernel
   generality: G
   mirror-B: D5/B/S3/Analytic/Asymptotics/MittagLefflerBarnesKernel
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The literal Mittag-Leffler Barnes kernel is integrable on exterior contour lines. -/

/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the repository root LICENSE.
Authors: Bastiaan J Braams
SPDX-License-Identifier: Apache-2.0

Adapted source port, 2026-10-31: the five private Gamma-factorization and
residue declarations below are selected from bjbraams/lean-DLMF revision
560b9475f35bbc6e4f5296631298859825091f7f, BarnesResidue.lean and
MellinBarnesSeries.lean. Namespace, imports and visibility are adapted;
the literal-kernel consumers and strip construction are local additions.
The complete license, source-chain assessment and per-declaration consumers
are recorded in Library/Asymptotics/braams2026barnesmittagport.md.
Retire each selected port when this repository's pinned Mathlib supplies an
equivalent declaration, replacing the actual consumers with direct calls.
-/

import D5.S3.Analytic.Asymptotics.GammaVerticalReciprocalBounds
import D5.S3.Analytic.Asymptotics.BarnesSineBounds
import D5.S3.Analytic.Asymptotics.BarnesResidue
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

open Complex Filter Set MeasureTheory
open scoped Topology Real Interval

noncomputable section
namespace D5.S3.Analytic.Asymptotics.MittagLefflerBarnesKernel

/-- The literal Barnes integrand, with the principal logarithm of `-z`. -/
def kernel (α β : ℝ) (z s : ℂ) : ℂ :=
  Complex.Gamma s * Complex.Gamma (1 - s) *
    (Complex.Gamma ((β : ℂ) - α * s))⁻¹ * Complex.exp (-s * Complex.log (-z))

/-- The positive angular margin in the exterior sector. -/
def margin (α : ℝ) (z : ℂ) : ℝ :=
  Real.pi * (1 - α / 2) - |Complex.arg (-z)|

private theorem reflected (α β : ℝ) (z s : ℂ) :
    kernel α β z s = (Real.pi : ℂ) / Complex.sin (Real.pi * s) *
      (Complex.Gamma ((β : ℂ) - α * s))⁻¹ * Complex.exp (-s * Complex.log (-z)) := by
  rw [kernel, Complex.Gamma_mul_Gamma_one_sub]

private theorem exponential_norm (c y : ℝ) (z : ℂ) :
    ‖Complex.exp (-((c : ℂ) + y * I) * Complex.log (-z))‖ =
      Real.exp (-c * Real.log ‖z‖ + y * Complex.arg (-z)) := by
  rw [Complex.norm_exp]
  congr 1
  simp [Complex.mul_re, Complex.log_re, Complex.log_im]

private theorem sine_pos {c : ℝ} (hc : Real.sin (Real.pi * c) ≠ 0) (y : ℝ) :
    0 < ‖Complex.sin (Real.pi * ((c : ℂ) + y * I))‖ := by
  exact lt_of_lt_of_le
    (mul_pos (div_pos (abs_pos.mpr hc) (by norm_num)) (Real.exp_pos _))
    (BarnesSineBounds.barnesRes_sin_lower_line c y)

/-- A polynomial times the actual sector margin dominates the literal kernel on a vertical line.
The reciprocal Gamma bound applies even where its argument is a Gamma pole. -/
theorem exists_line_majorant {α : ℝ} (hα : 0 < α) (β c : ℝ) (z : ℂ)
    (hc : Real.sin (Real.pi * c) ≠ 0) :
    ∃ C : ℝ, ∃ K : ℕ, ∀ y : ℝ,
      ‖kernel α β z (c + y * I)‖ ≤
        C * (1 + |y|) ^ K * Real.exp (-(margin α z * |y|)) := by
  obtain ⟨A, K, hA⟩ :=
    GammaVerticalReciprocalBounds.exists_norm_recip_Gamma_le |β - α * c|
  have hx : β - α * c ∈ Icc (-|β - α * c|) |β - α * c| :=
    ⟨neg_abs_le _, le_abs_self _⟩
  have hA0 : 0 ≤ A := by
    have h := hA (β - α * c) hx 0
    simp only [abs_zero, add_zero, one_pow, mul_one, mul_zero, zero_div,
      Real.exp_zero] at h
    exact (norm_nonneg _).trans h
  refine ⟨(2 * Real.pi / |Real.sin (Real.pi * c)|) *
    Real.exp (-c * Real.log ‖z‖) * A * (1 + α) ^ K, K, fun y => ?_⟩
  have hsin := BarnesSineBounds.barnesRes_sin_lower_line c y
  have hspos := sine_pos hc y
  have hG := hA (β - α * c) hx (-α * y)
  have harg : (β : ℂ) - α * ((c : ℂ) + y * I) =
      ((β - α * c : ℝ) : ℂ) + I * ((-α * y : ℝ) : ℂ) := by push_cast; ring
  have habs : |(-α * y)| = α * |y| := by rw [abs_mul, abs_neg, abs_of_pos hα]
  rw [habs] at hG
  have hpoly : (1 + α * |y|) ^ K ≤ (1 + α) ^ K * (1 + |y|) ^ K := by
    rw [← mul_pow]
    gcongr
    nlinarith [abs_nonneg y]
  have hangle : y * Complex.arg (-z) ≤ |Complex.arg (-z)| * |y| := by
    calc
      _ ≤ |y * Complex.arg (-z)| := le_abs_self _
      _ = _ := by rw [abs_mul]; ring
  have he : Real.exp (Real.pi * (α * |y|) / 2) *
      Real.exp (-c * Real.log ‖z‖ + y * Complex.arg (-z)) ≤
        Real.exp (-c * Real.log ‖z‖) *
          Real.exp (Real.pi * |y|) * Real.exp (-(margin α z * |y|)) := by
    rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    dsimp [margin]
    nlinarith
  rw [reflected, norm_mul, norm_mul, norm_div, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos Real.pi_pos, harg, exponential_norm]
  rw [show Real.pi / ‖Complex.sin (Real.pi * ((c : ℂ) + y * I))‖ *
      ‖(Complex.Gamma (((β - α * c : ℝ) : ℂ) + I * ((-α * y : ℝ) : ℂ)))⁻¹‖ *
      Real.exp (-c * Real.log ‖z‖ + y * Complex.arg (-z)) =
      (Real.pi * ‖(Complex.Gamma
        (((β - α * c : ℝ) : ℂ) + I * ((-α * y : ℝ) : ℂ)))⁻¹‖ *
        Real.exp (-c * Real.log ‖z‖ + y * Complex.arg (-z))) /
        ‖Complex.sin (Real.pi * ((c : ℂ) + y * I))‖ by ring]
  apply (div_le_iff₀ hspos).2
  have hden : 0 < |Real.sin (Real.pi * c)| := abs_pos.mpr hc
  have hbase :
      Real.pi * ‖(Complex.Gamma
        (((β - α * c : ℝ) : ℂ) + I * ((-α * y : ℝ) : ℂ)))⁻¹‖ *
        Real.exp (-c * Real.log ‖z‖ + y * Complex.arg (-z)) ≤
      Real.pi * (A * ((1 + α) ^ K * (1 + |y|) ^ K)) *
        (Real.exp (-c * Real.log ‖z‖) * Real.exp (Real.pi * |y|) *
          Real.exp (-(margin α z * |y|))) := by
    calc
      _ ≤ Real.pi * (A * (1 + α * |y|) ^ K *
          Real.exp (Real.pi * (α * |y|) / 2)) *
          Real.exp (-c * Real.log ‖z‖ + y * Complex.arg (-z)) := by gcongr
      _ = Real.pi * (A * (1 + α * |y|) ^ K) *
          (Real.exp (Real.pi * (α * |y|) / 2) *
            Real.exp (-c * Real.log ‖z‖ + y * Complex.arg (-z))) := by ring
      _ ≤ _ := by gcongr
  calc
    _ ≤ _ := hbase
    _ ≤ ((2 * Real.pi / |Real.sin (Real.pi * c)|) *
        Real.exp (-c * Real.log ‖z‖) * A * (1 + α) ^ K * (1 + |y|) ^ K *
        Real.exp (-(margin α z * |y|))) *
        ‖Complex.sin (Real.pi * ((c : ℂ) + y * I))‖ := by
      have hscaled := mul_le_mul_of_nonneg_left hsin
        (by positivity : 0 ≤ (2 * Real.pi / |Real.sin (Real.pi * c)|) *
          Real.exp (-c * Real.log ‖z‖) * A * (1 + α) ^ K * (1 + |y|) ^ K *
          Real.exp (-(margin α z * |y|)))
      convert hscaled using 1 <;> field_simp [hden.ne'] <;> ring

/-- All vertical lines avoiding the sine zeros are integrable in the strict exterior sector. -/
theorem integrable_line {α : ℝ} (hα : 0 < α) (β c : ℝ) (z : ℂ)
    (hc : Real.sin (Real.pi * c) ≠ 0) (hz : 0 < margin α z) :
    Integrable (fun y : ℝ => kernel α β z (c + y * I)) := by
  obtain ⟨C, K, h⟩ := exists_line_majorant hα β c z hc
  have hm : AEStronglyMeasurable (fun y : ℝ => kernel α β z (c + y * I)) := by
    simp_rw [reflected]
    have hrecip : Continuous (fun w : ℂ => (Complex.Gamma w)⁻¹) := by
      simpa only [one_div] using Complex.differentiable_one_div_Gamma.continuous
    have hsin : Continuous (fun y : ℝ =>
        Complex.sin (Real.pi * ((c : ℂ) + y * I))) := by fun_prop
    have hdiv : Continuous (fun y : ℝ =>
        (Real.pi : ℂ) / Complex.sin (Real.pi * ((c : ℂ) + y * I))) :=
      continuous_const.div hsin (fun y => norm_pos_iff.mp (sine_pos hc y))
    exact ((hdiv.mul (hrecip.comp (by fun_prop))).mul (by fun_prop)).aestronglyMeasurable
  exact ((GammaVerticalReciprocalBounds.integrable_one_add_abs_pow_mul_exp_neg hz K).const_mul
    C).mono' hm (Filter.Eventually.of_forall fun y => by
      simpa only [mul_assoc] using h y)


private theorem barnesRes_Gamma_add_nat_succ (w : ℂ) (n : ℕ) (h : ∀ j : ℕ, j ≤ n → w + j ≠ 0) :
    Complex.Gamma (w + n + 1) = Complex.Gamma w * ∏ j ∈ Finset.range (n + 1), (w + j) := by
  induction n with
  | zero =>
    have := h 0 le_rfl
    simp only [Nat.cast_zero, add_zero] at this ⊢
    rw [Complex.Gamma_add_one w this]; simp; ring
  | succ n ih =>
    rw [Finset.prod_range_succ, ← mul_assoc, ← ih (fun j hj => h j (by omega))]
    have := h (n + 1) le_rfl
    push_cast at this ⊢
    rw [show w + (n + 1) + 1 = (w + n + 1) + 1 by ring, Complex.Gamma_add_one _ (by
      rw [show w + n + 1 = w + (n + 1) by ring]; exact this)]
    ring

private theorem barnesRes_prod_nat_sub (n : ℕ) : ∏ j ∈ Finset.range n, ((n:ℂ) - j) = n.factorial := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.prod_range_succ', Nat.factorial_succ]
    have : ∏ j ∈ Finset.range n, (((n+1 : ℕ) : ℂ) - ((j+1 : ℕ) : ℂ)) =
        ∏ j ∈ Finset.range n, ((n:ℂ) - j) :=
      Finset.prod_congr rfl fun j _ => by push_cast; ring
    rw [this, ih]; push_cast; ring

private theorem barnesRes_prod_sub_nat (n : ℕ) :
    ∏ j ∈ Finset.range n, ((j:ℂ) - n) = (-1)^n * n.factorial := by
  calc ∏ j ∈ Finset.range n, ((j:ℂ) - n) = ∏ j ∈ Finset.range n, ((-1) * ((n:ℂ) - j)) :=
        Finset.prod_congr rfl fun j _ => by ring
    _ = (-1)^n * ∏ j ∈ Finset.range n, ((n:ℂ) - j) := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]
    _ = _ := by rw [barnesRes_prod_nat_sub]

private theorem mbSeries_Gamma_mul_eq_div (G : ℂ → ℂ) (a : ℂ) (n : ℕ) {s : ℂ}
    (hs : ∀ j : ℕ, j ≤ n → s + a + j ≠ 0) :
    G s * Complex.Gamma (s + a) =
      G s * Complex.Gamma (s + a + n + 1) / (∏ j ∈ Finset.range n, (s + a + j)) / (s - (-n - a)) := by
  have hG := barnesRes_Gamma_add_nat_succ (s + a) n hs
  have hP : ∏ j ∈ Finset.range n, (s + a + j) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun j hj => hs j (Finset.mem_range.mp hj).le
  rw [hG, Finset.prod_range_succ, show s - (-n - a) = s + a + n by ring]
  have hn' : s + a + (n : ℂ) ≠ 0 := hs n le_rfl
  field_simp

private theorem mbSeries_Gamma_residue (G : ℂ → ℂ) (a : ℂ) (n : ℕ) :
    G (-n - a) * Complex.Gamma ((-n - a) + a + n + 1) / ∏ j ∈ Finset.range n, ((-n - a) + a + j) =
      (-1) ^ n * G (-n - a) / n.factorial := by
  have h1 : (-n - a) + a + n + 1 = (1 : ℂ) := by ring
  have h2 : ∏ j ∈ Finset.range n, ((-n - a) + a + (j : ℂ)) = (-1) ^ n * n.factorial := by
    rw [← barnesRes_prod_sub_nat]
    exact Finset.prod_congr rfl fun j _ => by ring
  rw [h1, Complex.Gamma_one, h2]
  have : ((n.factorial : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  have h3 : ((-1 : ℂ)) ^ n ≠ 0 := pow_ne_zero _ (by norm_num)
  field_simp
  rw [← pow_mul, show n * 2 = 2 * n by ring, pow_mul]
  simp

/-- The decreasing half-integer contour sequence. -/
def leftLine (n : ℕ) : ℝ := 1 / 2 - n

/-- The numerator at the only possible pole in the `n`-th left strip.
The factors divided out here have their zeros strictly to the right of the strip. -/
def leftNumerator (α β : ℝ) (z : ℂ) (n : ℕ) (s : ℂ) : ℂ :=
  (Complex.Gamma (1 - s) * (Complex.Gamma ((β : ℂ) - α * s))⁻¹ *
    Complex.exp (-s * Complex.log (-z))) * Complex.Gamma (s + n + 1) /
      ∏ j ∈ Finset.range n, (s + j)

private theorem left_factor_ne_zero (n j : ℕ) (hj : j < n) {s : ℂ}
    (hs : s.re ∈ Icc (leftLine (n + 1)) (leftLine n)) : s + (j : ℂ) ≠ 0 := by
  intro he
  have hre := congrArg Complex.re he
  simp only [Complex.add_re, Complex.natCast_re, Complex.zero_re] at hre
  have hj' : (j : ℝ) + 1 ≤ n := by exact_mod_cast Nat.succ_le_of_lt hj
  dsimp [leftLine] at hs
  nlinarith [hs.2]

/-- Holomorphy of the actual numerator, including reciprocal-Gamma zeros. -/
theorem differentiableOn_leftNumerator (α β : ℝ) (z : ℂ) (n : ℕ) :
    DifferentiableOn ℂ (leftNumerator α β z n)
      (Complex.re ⁻¹' Icc (leftLine (n + 1)) (leftLine n)) := by
  intro s hs
  have hs' : s.re ∈ Icc (leftLine (n + 1)) (leftLine n) := hs
  have hshift : 0 < (s + (n : ℂ) + 1).re := by
    simp only [Complex.add_re, Complex.natCast_re, Complex.one_re]
    dsimp [leftLine] at hs'
    push_cast at hs'
    linarith [hs'.1]
  have hone : 0 < (1 - s).re := by
    simp only [Complex.sub_re, Complex.one_re]
    dsimp [leftLine] at hs'
    nlinarith [hs'.2, Nat.cast_nonneg (α := ℝ) n]
  have hGamma {w : ℂ} (hw : 0 < w.re) : DifferentiableAt ℂ Complex.Gamma w := by
    apply Complex.differentiableAt_Gamma
    intro m he
    have := congrArg Complex.re he
    simp only [Complex.neg_re, Complex.natCast_re] at this
    nlinarith [Nat.cast_nonneg (α := ℝ) m]
  have h1 : DifferentiableAt ℂ (fun s : ℂ => Complex.Gamma (1 - s)) s :=
    (hGamma hone).comp s (by fun_prop)
  have h2 : DifferentiableAt ℂ
      (fun s : ℂ => (Complex.Gamma ((β : ℂ) - α * s))⁻¹) s :=
    (Complex.differentiable_one_div_Gamma _).comp s (by fun_prop)
  have h3 : DifferentiableAt ℂ
      (fun s : ℂ => Complex.exp (-s * Complex.log (-z))) s := by fun_prop
  have h4 : DifferentiableAt ℂ (fun s : ℂ => Complex.Gamma (s + n + 1)) s :=
    (hGamma hshift).comp s (by fun_prop)
  have h5 : DifferentiableAt ℂ (fun s : ℂ => ∏ j ∈ Finset.range n, (s + j)) s := by
    fun_prop
  exact (((h1.mul h2).mul h3).mul h4).div h5
    (Finset.prod_ne_zero_iff.mpr fun j hj =>
      left_factor_ne_zero n j (Finset.mem_range.mp hj) hs') |>.differentiableWithinAt

/-- Actual factorization of the literal kernel on the closed left strip away from its pole. -/
theorem kernel_eq_leftNumerator (α β : ℝ) (z : ℂ) (n : ℕ) {s : ℂ}
    (hs : s.re ∈ Icc (leftLine (n + 1)) (leftLine n)) (hne : s ≠ -(n : ℂ)) :
    kernel α β z s = leftNumerator α β z n s / (s - (-(n : ℂ))) := by
  let G : ℂ → ℂ := fun s => Complex.Gamma (1 - s) *
    (Complex.Gamma ((β : ℂ) - α * s))⁻¹ * Complex.exp (-s * Complex.log (-z))
  have hf : ∀ j : ℕ, j ≤ n → s + (0 : ℂ) + j ≠ 0 := by
    intro j hj
    rcases lt_or_eq_of_le hj with hj | rfl
    · simpa only [add_zero] using left_factor_ne_zero n j hj hs
    · simpa only [add_zero, sub_neg_eq_add] using sub_ne_zero.mpr hne
  calc
    kernel α β z s = G s * Complex.Gamma (s + 0) := by dsimp [kernel, G]; ring
    _ = G s * Complex.Gamma (s + 0 + n + 1) /
        (∏ j ∈ Finset.range n, (s + 0 + j)) / (s - (-n - 0)) :=
      mbSeries_Gamma_mul_eq_div G 0 n hf
    _ = leftNumerator α β z n s / (s - (-(n : ℂ))) := by
      simp only [add_zero, sub_zero, leftNumerator, G]

/-- The actual residue numerator is the literal source coefficient.
No nonvanishing assumption on Gamma(alpha*n+beta) is used. -/
theorem leftNumerator_residue (α β : ℝ) {z : ℂ} (hz : z ≠ 0) (n : ℕ) :
    leftNumerator α β z n (-(n : ℂ)) =
      z ^ n / (Real.Gamma (α * (n : ℝ) + β) : ℂ) := by
  let G : ℂ → ℂ := fun s => Complex.Gamma (1 - s) *
    (Complex.Gamma ((β : ℂ) - α * s))⁻¹ * Complex.exp (-s * Complex.log (-z))
  have hr := mbSeries_Gamma_residue G 0 n
  simp only [sub_zero, add_zero] at hr
  change G (-(n : ℂ)) * Complex.Gamma (-(n : ℂ) + n + 1) /
    (∏ j ∈ Finset.range n, (-(n : ℂ) + j)) = _
  rw [hr]
  have hfac : Complex.Gamma (1 - (-(n : ℂ))) = (n.factorial : ℂ) := by
    convert Complex.Gamma_nat_eq_factorial n using 1 <;> congr 1 <;> ring
  have hexp : Complex.exp (-(-(n : ℂ)) * Complex.log (-z)) = (-z) ^ n := by
    rw [neg_neg, Complex.exp_nat_mul, Complex.exp_log (neg_ne_zero.mpr hz)]
  have harg : (β : ℂ) - α * (-(n : ℂ)) = ((α * (n : ℝ) + β : ℝ) : ℂ) := by
    push_cast
    ring
  dsimp [G]
  rw [hfac, hexp, harg, Complex.Gamma_ofReal]
  have hfac0 : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  have hsign : (-1 : ℂ) ^ n * (-z) ^ n = z ^ n := by
    rw [← mul_pow]
    congr 1
    ring
  calc
    (-1 : ℂ) ^ n * ((n.factorial : ℂ) *
        (Real.Gamma (α * (n : ℝ) + β) : ℂ)⁻¹ * (-z) ^ n) / n.factorial =
        ((-1 : ℂ) ^ n * (-z) ^ n) * (Real.Gamma (α * (n : ℝ) + β) : ℂ)⁻¹ := by
      rw [div_eq_mul_inv]
      calc
        (-1 : ℂ) ^ n * ((n.factorial : ℂ) *
            (Real.Gamma (α * (n : ℝ) + β) : ℂ)⁻¹ * (-z) ^ n) *
              (n.factorial : ℂ)⁻¹ =
            (((-1 : ℂ) ^ n * (-z) ^ n) *
              (Real.Gamma (α * (n : ℝ) + β) : ℂ)⁻¹) *
                ((n.factorial : ℂ) * (n.factorial : ℂ)⁻¹) := by ring
        _ = _ := by rw [mul_inv_cancel₀ hfac0, mul_one]
    _ = _ := by rw [hsign, div_eq_mul_inv]

/-- On a line whose reciprocal-Gamma real argument is at least one half,
retain the growing real Gamma denominator instead of a bounded-strip constant. -/
theorem norm_line_le_recip_gamma {α : ℝ} (hα : 0 < α) (β c : ℝ) (z : ℂ)
    (hc : Real.sin (Real.pi * c) ≠ 0) (hx : 1 / 2 ≤ β - α * c) (y : ℝ) :
    ‖kernel α β z (c + y * I)‖ ≤
      (2 * Real.pi / |Real.sin (Real.pi * c)|) *
        Real.exp (-c * Real.log ‖z‖) / Real.Gamma (β - α * c) *
          Real.exp (-(margin α z * |y|)) := by
  have hGpos : 0 < Real.Gamma (β - α * c) :=
    Real.Gamma_pos_of_pos (by linarith)
  have hGsq := GammaVerticalReciprocalBounds.norm_recip_Gamma_sq_le hx (-α * y)
  have habs : |(-α * y)| = α * |y| := by rw [abs_mul, abs_neg, abs_of_pos hα]
  rw [habs] at hGsq
  have hG : ‖(Complex.Gamma (((β - α * c : ℝ) : ℂ) + I * ((-α * y : ℝ) : ℂ)))⁻¹‖ ≤
      Real.exp (Real.pi * (α * |y|) / 2) / Real.Gamma (β - α * c) := by
    apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
    rw [div_pow, ← Real.exp_nat_mul]
    norm_num only [Nat.cast_ofNat]
    rw [show (2 : ℝ) * (Real.pi * (α * |y|) / 2) =
      Real.pi * (α * |y|) by ring]
    exact hGsq
  have harg : (β : ℂ) - α * ((c : ℂ) + y * I) =
      ((β - α * c : ℝ) : ℂ) + I * ((-α * y : ℝ) : ℂ) := by push_cast; ring
  have hangle : y * Complex.arg (-z) ≤ |Complex.arg (-z)| * |y| := by
    calc
      _ ≤ |y * Complex.arg (-z)| := le_abs_self _
      _ = _ := by rw [abs_mul]; ring
  have he : Real.exp (Real.pi * (α * |y|) / 2) *
      Real.exp (-c * Real.log ‖z‖ + y * Complex.arg (-z)) ≤
        Real.exp (-c * Real.log ‖z‖) * Real.exp (Real.pi * |y|) *
          Real.exp (-(margin α z * |y|)) := by
    rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    dsimp [margin]
    nlinarith
  have hsin := BarnesSineBounds.barnesRes_sin_lower_line c y
  have hspos := sine_pos hc y
  have hcpos := abs_pos.mpr hc
  rw [reflected, norm_mul, norm_mul, norm_div, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos Real.pi_pos, harg, exponential_norm]
  have hnum : Real.pi *
      ‖(Complex.Gamma (((β - α * c : ℝ) : ℂ) + I * ((-α * y : ℝ) : ℂ)))⁻¹‖ *
        Real.exp (-c * Real.log ‖z‖ + y * Complex.arg (-z)) ≤
      Real.pi * (Real.exp (-c * Real.log ‖z‖) * Real.exp (Real.pi * |y|) *
        Real.exp (-(margin α z * |y|))) / Real.Gamma (β - α * c) := by
    calc
      _ ≤ Real.pi * (Real.exp (Real.pi * (α * |y|) / 2) /
          Real.Gamma (β - α * c)) *
            Real.exp (-c * Real.log ‖z‖ + y * Complex.arg (-z)) := by gcongr
      _ = Real.pi * (Real.exp (Real.pi * (α * |y|) / 2) *
          Real.exp (-c * Real.log ‖z‖ + y * Complex.arg (-z))) /
            Real.Gamma (β - α * c) := by ring
      _ ≤ _ := by gcongr
  have hscaled := mul_le_mul_of_nonneg_left hsin
    (by positivity : 0 ≤ (2 * Real.pi / |Real.sin (Real.pi * c)|) *
      Real.exp (-c * Real.log ‖z‖) / Real.Gamma (β - α * c) *
        Real.exp (-(margin α z * |y|)))
  have htotal : Real.pi *
      ‖(Complex.Gamma (((β - α * c : ℝ) : ℂ) + I * ((-α * y : ℝ) : ℂ)))⁻¹‖ *
        Real.exp (-c * Real.log ‖z‖ + y * Complex.arg (-z)) ≤
      ((2 * Real.pi / |Real.sin (Real.pi * c)|) *
        Real.exp (-c * Real.log ‖z‖) / Real.Gamma (β - α * c) *
          Real.exp (-(margin α z * |y|))) *
            ‖Complex.sin (Real.pi * ((c : ℂ) + y * I))‖ := by
    apply hnum.trans
    convert hscaled using 1 <;> field_simp [hcpos.ne', hGpos.ne'] <;> ring
  have hdiv := (div_le_iff₀ hspos).mpr htotal
  convert hdiv using 1 <;> ring

/-- The half-integer lines have a sine factor of absolute value one. -/
theorem abs_sin_leftLine (n : ℕ) : |Real.sin (Real.pi * leftLine n)| = 1 := by
  induction n with
  | zero =>
    have hzero : Real.pi * leftLine 0 = Real.pi / 2 := by
      norm_num [leftLine] <;> ring
    rw [hzero, Real.sin_pi_div_two]
    norm_num
  | succ n ih =>
    have hstep : Real.pi * leftLine (n + 1) = Real.pi * leftLine n - Real.pi := by
      dsimp [leftLine]
      push_cast
      ring
    rw [hstep, Real.sin_sub, Real.sin_pi, Real.cos_pi]
    simpa using ih

/-- An integral bound with the real Gamma denominator retained.
All constants apart from that denominator and the radial factor are line-independent
on the half-integer contour sequence. The integral is with respect to `dy`. -/
theorem norm_integral_leftLine_le {α : ℝ} (hα : 0 < α) (β : ℝ) (z : ℂ)
    (hz : 0 < margin α z) (n : ℕ) (hx : 1 / 2 ≤ β - α * leftLine n) :
    ‖∫ y : ℝ, kernel α β z (leftLine n + y * I)‖ ≤
      (2 * Real.pi * Real.exp (-leftLine n * Real.log ‖z‖) /
        Real.Gamma (β - α * leftLine n)) *
          ∫ y : ℝ, Real.exp (-(margin α z * |y|)) := by
  have hc : Real.sin (Real.pi * leftLine n) ≠ 0 := by
    intro he
    simpa [he] using abs_sin_leftLine n
  have hi : Integrable (fun y : ℝ => Real.exp (-(margin α z * |y|))) := by
    simpa only [neg_mul] using ExponentialAbsIntegrability.integrable_exp_neg_mul_abs hz
  have hmajor := hi.const_mul
    (2 * Real.pi * Real.exp (-leftLine n * Real.log ‖z‖) /
      Real.Gamma (β - α * leftLine n))
  have hle := norm_integral_le_of_norm_le hmajor (Filter.Eventually.of_forall fun y => by
    simpa only [abs_sin_leftLine n, div_one] using
      norm_line_le_recip_gamma hα β (leftLine n) z hc hx y)
  simpa only [integral_const_mul] using hle

private theorem barnesRes_tendsto_poly_exp {b : ℝ} (hb : 0 < b) (K : ℕ) :
    Tendsto (fun u : ℝ => (1 + u) ^ K * Real.exp (-(b * u))) atTop (𝓝 0) := by
  have h := ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero K).comp
    ((tendsto_id.const_mul_atTop hb).comp (tendsto_atTop_add_const_left _ 1 tendsto_id))).const_mul
    ((b ^ K)⁻¹ * Real.exp b)
  rw [mul_zero] at h
  refine h.congr fun u => ?_
  simp only [Function.comp_def, id]
  rw [mul_pow, show -(b * (1 + u)) = -b + -(b*u) by ring, Real.exp_add, Real.exp_neg b]
  have : b ^ K ≠ 0 := by positivity
  field_simp

private theorem exists_horizontal_majorant {α : ℝ} (hα : 0 < α) (β a b : ℝ) (z : ℂ) :
    ∃ C : ℝ, ∃ K : ℕ, ∀ x ∈ Icc a b, ∀ y : ℝ, 1 ≤ |y| →
      ‖kernel α β z (x + y * I)‖ ≤
        C * (1 + |y|) ^ K * Real.exp (-(margin α z * |y|)) := by
  let X : ℝ := |β| + α * (|a| + |b|)
  obtain ⟨A, K, hA⟩ := GammaVerticalReciprocalBounds.exists_norm_recip_Gamma_le X
  have hA0 : 0 ≤ A := by
    have hX : 0 ≤ X := by dsimp [X]; positivity
    have h := hA 0 ⟨neg_nonpos.mpr hX, hX⟩ 0
    simp only [abs_zero, add_zero, one_pow, mul_one, mul_zero, zero_div,
      Real.exp_zero] at h
    exact (norm_nonneg _).trans h
  let R : ℝ := Real.exp ((|a| + |b|) * |Real.log ‖z‖|)
  refine ⟨4 * Real.pi * A * (1 + α) ^ K * R, K, ?_⟩
  intro x hx y hy
  have hxabs : |x| ≤ |a| + |b| := abs_le.mpr ⟨by
    have := neg_abs_le a
    linarith [hx.1, abs_nonneg b], by
    have := le_abs_self b
    linarith [hx.2, abs_nonneg a]⟩
  have hxG : β - α * x ∈ Icc (-X) X := by
    have htri : |β - α * x| ≤ |β| + |α * x| := by
      simpa only [sub_zero, zero_sub, abs_neg] using abs_sub_le β 0 (α * x)
    have hmul : |α * x| ≤ α * (|a| + |b|) := by
      rw [abs_mul, abs_of_pos hα]
      exact mul_le_mul_of_nonneg_left hxabs hα.le
    have h : |β - α * x| ≤ X := by dsimp [X]; linarith
    exact abs_le.mp h
  have hG := hA (β - α * x) hxG (-α * y)
  have habs : |(-α * y)| = α * |y| := by rw [abs_mul, abs_neg, abs_of_pos hα]
  rw [habs] at hG
  have harg : (β : ℂ) - α * ((x : ℂ) + y * I) =
      ((β - α * x : ℝ) : ℂ) + I * ((-α * y : ℝ) : ℂ) := by push_cast; ring
  have hpoly : (1 + α * |y|) ^ K ≤ (1 + α) ^ K * (1 + |y|) ^ K := by
    rw [← mul_pow]
    gcongr
    nlinarith [abs_nonneg y]
  have hangle : y * Complex.arg (-z) ≤ |Complex.arg (-z)| * |y| := by
    calc
      _ ≤ |y * Complex.arg (-z)| := le_abs_self _
      _ = _ := by rw [abs_mul]; ring
  have hrad : -x * Real.log ‖z‖ ≤ (|a| + |b|) * |Real.log ‖z‖| := by
    calc
      _ ≤ |-x * Real.log ‖z‖| := le_abs_self _
      _ = |x| * |Real.log ‖z‖| := by rw [abs_mul, abs_neg]
      _ ≤ _ := mul_le_mul_of_nonneg_right hxabs (abs_nonneg _)
  have he : Real.exp (Real.pi * (α * |y|) / 2) *
      Real.exp (-x * Real.log ‖z‖ + y * Complex.arg (-z)) ≤
        R * Real.exp (Real.pi * |y|) * Real.exp (-(margin α z * |y|)) := by
    dsimp [R]
    rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    dsimp [margin]
    nlinarith
  have hsin := BarnesSineBounds.barnesRes_sin_lower_far x hy
  have hspos : 0 < ‖Complex.sin (Real.pi * ((x : ℂ) + y * I))‖ :=
    lt_of_lt_of_le (by positivity) hsin
  rw [reflected, norm_mul, norm_mul, norm_div, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos Real.pi_pos, harg, exponential_norm]
  have hnum : Real.pi *
      ‖(Complex.Gamma (((β - α * x : ℝ) : ℂ) + I * ((-α * y : ℝ) : ℂ)))⁻¹‖ *
        Real.exp (-x * Real.log ‖z‖ + y * Complex.arg (-z)) ≤
      Real.pi * (A * ((1 + α) ^ K * (1 + |y|) ^ K)) *
        (R * Real.exp (Real.pi * |y|) * Real.exp (-(margin α z * |y|))) := by
    calc
      _ ≤ Real.pi * (A * (1 + α * |y|) ^ K *
          Real.exp (Real.pi * (α * |y|) / 2)) *
            Real.exp (-x * Real.log ‖z‖ + y * Complex.arg (-z)) := by gcongr
      _ = Real.pi * (A * (1 + α * |y|) ^ K) *
          (Real.exp (Real.pi * (α * |y|) / 2) *
            Real.exp (-x * Real.log ‖z‖ + y * Complex.arg (-z))) := by ring
      _ ≤ _ := by gcongr
  have hscaled := mul_le_mul_of_nonneg_left hsin
    (by positivity : 0 ≤ 4 * Real.pi * A * (1 + α) ^ K * R *
      (1 + |y|) ^ K * Real.exp (-(margin α z * |y|)))
  have htotal := hnum.trans (show Real.pi * (A * ((1 + α) ^ K * (1 + |y|) ^ K)) *
      (R * Real.exp (Real.pi * |y|) * Real.exp (-(margin α z * |y|))) ≤
        (4 * Real.pi * A * (1 + α) ^ K * R * (1 + |y|) ^ K *
          Real.exp (-(margin α z * |y|))) *
            ‖Complex.sin (Real.pi * ((x : ℂ) + y * I))‖ by
    convert hscaled using 1 <;> ring)
  have hdiv := (div_le_iff₀ hspos).mpr htotal
  convert hdiv using 1 <;> ring

/-- The actual horizontal cross-sections vanish on every finite strip at both ends. -/
theorem horizontal_tendsto_zero {α : ℝ} (hα : 0 < α) (β a b : ℝ) (z : ℂ)
    (hab : a ≤ b) (hz : 0 < margin α z) :
    Tendsto (fun T : ℝ => ∫ x in a..b, kernel α β z (x + T * I)) atTop (𝓝 0) ∧
    Tendsto (fun T : ℝ => ∫ x in a..b, kernel α β z (x + T * I)) atBot (𝓝 0) := by
  obtain ⟨C, K, h⟩ := exists_horizontal_majorant hα β a b z
  have hbound {T : ℝ} (hT : 1 ≤ |T|) :
      ‖∫ x in a..b, kernel α β z (x + T * I)‖ ≤
        (C * (1 + |T|) ^ K * Real.exp (-(margin α z * |T|))) * (b - a) := by
    have hle := intervalIntegral.norm_integral_le_of_norm_le_const
      (fun x hx => h x (by
        rw [uIoc_of_le hab] at hx
        exact ⟨hx.1.le, hx.2⟩) T hT)
    simpa only [abs_of_nonneg (sub_nonneg.mpr hab)] using hle
  have hlim {l : Filter ℝ} (hl : Tendsto (fun T : ℝ => |T|) l atTop) :
      Tendsto (fun T : ℝ => ∫ x in a..b, kernel α β z (x + T * I)) l (𝓝 0) := by
    have hp := ((barnesRes_tendsto_poly_exp hz K).comp hl).const_mul C
    have hp' := hp.mul_const (b - a)
    simp only [mul_zero, zero_mul] at hp'
    apply squeeze_zero_norm' _ hp'
    filter_upwards [hl.eventually (eventually_ge_atTop 1)] with T hT
    simpa only [Function.comp_def, mul_assoc] using hbound hT
  constructor
  · apply hlim
    exact tendsto_id.congr' (by
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
      exact (abs_of_nonneg hT).symm)
  · apply hlim
    exact tendsto_neg_atBot_atTop.congr' (by
      filter_upwards [eventually_le_atBot (0 : ℝ)] with T hT
      exact (abs_of_nonpos hT).symm)

/-- The rightward half-integer contour sequence. -/
def rightLine (n : ℕ) : ℝ := n + 1 / 2

/-- The actual numerator at the pole `n+1`. The minus sign comes from
`1-s+n = -(s-(n+1))`; it is essential for rightward contour shifts. -/
def rightNumerator (α β : ℝ) (z : ℂ) (n : ℕ) (s : ℂ) : ℂ :=
  -(Complex.Gamma s * (Complex.Gamma ((β : ℂ) - α * s))⁻¹ *
    Complex.exp (-s * Complex.log (-z)) * Complex.Gamma (1 - s + n + 1) /
      ∏ j ∈ Finset.range n, (1 - s + j))

private theorem right_factor_ne_zero (n j : ℕ) (hj : j < n) {s : ℂ}
    (hs : s.re ∈ Icc (rightLine n) (rightLine (n + 1))) :
    1 - s + (j : ℂ) ≠ 0 := by
  intro he
  have hre := congrArg Complex.re he
  simp only [Complex.add_re, Complex.sub_re, Complex.one_re,
    Complex.natCast_re, Complex.zero_re] at hre
  have hj' : (j : ℝ) + 1 ≤ n := by exact_mod_cast Nat.succ_le_of_lt hj
  dsimp [rightLine] at hs
  nlinarith [hs.1]

/-- Holomorphy of the right-strip numerator uses entire reciprocal Gamma. -/
theorem differentiableOn_rightNumerator (α β : ℝ) (z : ℂ) (n : ℕ) :
    DifferentiableOn ℂ (rightNumerator α β z n)
      (Complex.re ⁻¹' Icc (rightLine n) (rightLine (n + 1))) := by
  intro s hs
  have hs' : s.re ∈ Icc (rightLine n) (rightLine (n + 1)) := hs
  have hpos : 0 < s.re := by
    dsimp [rightLine] at hs'
    nlinarith [hs'.1, Nat.cast_nonneg (α := ℝ) n]
  have hshift : 0 < (1 - s + (n : ℂ) + 1).re := by
    simp only [Complex.add_re, Complex.sub_re, Complex.one_re, Complex.natCast_re]
    dsimp [rightLine] at hs'
    push_cast at hs'
    linarith [hs'.2]
  have hGamma {w : ℂ} (hw : 0 < w.re) : DifferentiableAt ℂ Complex.Gamma w := by
    apply Complex.differentiableAt_Gamma
    intro m he
    have := congrArg Complex.re he
    simp only [Complex.neg_re, Complex.natCast_re] at this
    nlinarith [Nat.cast_nonneg (α := ℝ) m]
  have h1 := hGamma hpos
  have h2 : DifferentiableAt ℂ
      (fun s : ℂ => (Complex.Gamma ((β : ℂ) - α * s))⁻¹) s :=
    (Complex.differentiable_one_div_Gamma _).comp s (by fun_prop)
  have h3 : DifferentiableAt ℂ
      (fun s : ℂ => Complex.exp (-s * Complex.log (-z))) s := by fun_prop
  have h4 : DifferentiableAt ℂ (fun s : ℂ => Complex.Gamma (1 - s + n + 1)) s :=
    (hGamma hshift).comp s (by fun_prop)
  have h5 : DifferentiableAt ℂ (fun s : ℂ => ∏ j ∈ Finset.range n, (1 - s + j)) s := by
    fun_prop
  exact (((((h1.mul h2).mul h3).mul h4).div h5
    (Finset.prod_ne_zero_iff.mpr fun j hj =>
      right_factor_ne_zero n j (Finset.mem_range.mp hj) hs')).neg).differentiableWithinAt

/-- Factorization on a right strip, away from its unique possible pole. -/
theorem kernel_eq_rightNumerator (α β : ℝ) (z : ℂ) (n : ℕ) {s : ℂ}
    (hs : s.re ∈ Icc (rightLine n) (rightLine (n + 1)))
    (hne : s ≠ (n : ℂ) + 1) :
    kernel α β z s = rightNumerator α β z n s / (s - ((n : ℂ) + 1)) := by
  have hf : ∀ j : ℕ, j ≤ n → (1 - s) + j ≠ 0 := by
    intro j hj
    rcases lt_or_eq_of_le hj with hj | rfl
    · exact right_factor_ne_zero n j hj hs
    · intro he
      apply hne
      linear_combination -he
  have hG := barnesRes_Gamma_add_nat_succ (1 - s) n hf
  have hprod : (∏ j ∈ Finset.range n, (1 - s + (j : ℂ))) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun j hj => hf j (Finset.mem_range.mp hj).le
  rw [kernel, rightNumerator, hG, Finset.prod_range_succ]
  have hp : s - ((n : ℂ) + 1) ≠ 0 := sub_ne_zero.mpr hne
  simp only [div_eq_mul_inv]
  generalize (Complex.Gamma ((β : ℂ) - α * s))⁻¹ = G
  field_simp [hprod, hp, hf n le_rfl] <;> ring

/-- The residue includes reciprocal-Gamma zeros without cancelling Gamma. -/
theorem rightNumerator_residue (α β : ℝ) {z : ℂ} (hz : z ≠ 0) (n : ℕ) :
    rightNumerator α β z n ((n : ℂ) + 1) =
      (z ^ (n + 1))⁻¹ / (Real.Gamma (β - α * ((n : ℝ) + 1)) : ℂ) := by
  have hfac : Complex.Gamma ((n : ℂ) + 1) = (n.factorial : ℂ) :=
    Complex.Gamma_nat_eq_factorial n
  have hshift : 1 - ((n : ℂ) + 1) + n + 1 = 1 := by ring
  have hprod : (∏ j ∈ Finset.range n, (1 - ((n : ℂ) + 1) + (j : ℂ))) =
      (-1 : ℂ) ^ n * n.factorial := by
    rw [← barnesRes_prod_sub_nat]
    exact Finset.prod_congr rfl fun j _ => by ring
  have he : Complex.exp (-((n : ℂ) + 1) * Complex.log (-z)) =
      ((-z) ^ (n + 1))⁻¹ := by
    rw [neg_mul, Complex.exp_neg]
    congr 1
    convert Complex.exp_nat_mul (Complex.log (-z)) (n + 1) using 1 <;>
      simp [Complex.exp_log (neg_ne_zero.mpr hz)]
  have harg : (β : ℂ) - α * ((n : ℂ) + 1) =
      ((β - α * ((n : ℝ) + 1) : ℝ) : ℂ) := by push_cast; ring
  rw [rightNumerator, hfac, hshift, Complex.Gamma_one, mul_one, hprod,
    he, harg, Complex.Gamma_ofReal, neg_pow]
  have hfac0 : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  have hzpow : z ^ (n + 1) ≠ 0 := pow_ne_zero _ hz
  have hsign : (-1 : ℂ) ^ (n + 1) = -((-1 : ℂ) ^ n) := by rw [pow_succ]; ring
  rw [hsign]
  simp only [div_eq_mul_inv]
  generalize (Real.Gamma (β - α * ((n : ℝ) + 1)) : ℂ)⁻¹ = G
  have hsign0 : (-1 : ℂ) ^ n ≠ 0 := pow_ne_zero _ (by norm_num)
  field_simp [hfac0, hzpow, hsign0] <;> ring
  all_goals rw [show n * 2 = 2 * n by ring, pow_mul]
  all_goals simp

/-- The sine on each right half-integer line has absolute value one. -/
theorem abs_sin_rightLine (n : ℕ) : |Real.sin (Real.pi * rightLine n)| = 1 := by
  induction n with
  | zero =>
    have hzero : Real.pi * rightLine 0 = Real.pi / 2 := by
      norm_num [rightLine] <;> ring
    rw [hzero, Real.sin_pi_div_two]
    norm_num
  | succ n ih =>
    have hstep : Real.pi * rightLine (n + 1) = Real.pi * rightLine n + Real.pi := by
      dsimp [rightLine]
      push_cast
      ring
    rw [hstep, Real.sin_add, Real.sin_pi, Real.cos_pi]
    simpa using ih

/-- The actual rightward shift, with integration in `dy` and its residue sign. -/
theorem integral_right_step {α : ℝ} (hα : 0 < α) (β : ℝ) {z : ℂ} (hz0 : z ≠ 0)
    (hz : 0 < margin α z) (n : ℕ) :
    (∫ y : ℝ, kernel α β z (rightLine (n + 1) + y * I)) -
      (∫ y : ℝ, kernel α β z (rightLine n + y * I)) =
        2 * (Real.pi : ℂ) * ((z ^ (n + 1))⁻¹ /
          (Real.Gamma (β - α * ((n : ℝ) + 1)) : ℂ)) := by
  have hrewrite {s : ℂ} (hs : s.re ∈ Icc (rightLine n) (rightLine (n + 1)))
      (hne : s ≠ (n : ℂ) + 1) := kernel_eq_rightNumerator α β z n hs hne
  have hv (j : ℕ) (hj : j = n ∨ j = n + 1) (y : ℝ) :
      kernel α β z (rightLine j + y * I) =
        rightNumerator α β z n (rightLine j + y * I) /
          (rightLine j + y * I - ((n : ℂ) + 1)) := by
    apply hrewrite
    · rcases hj with rfl | rfl <;> simp [rightLine] <;> push_cast <;> constructor <;> linarith
    · intro he
      have := congrArg Complex.re he
      rcases hj with rfl | rfl <;> simp [rightLine] at this <;> push_cast at this <;> linarith
  have hi (j : ℕ) : Integrable fun y : ℝ => kernel α β z (rightLine j + y * I) := by
    apply integrable_line hα β _ z _ hz
    intro he
    simpa [he] using abs_sin_rightLine j
  have hh := horizontal_tendsto_zero hα β (rightLine n) (rightLine (n + 1)) z
    (by dsimp [rightLine]; push_cast; linarith) hz
  have htopEq : (fun T : ℝ => ∫ x in rightLine n..rightLine (n + 1),
      rightNumerator α β z n (x + T * I) / (x + T * I - ((n : ℂ) + 1))) =ᶠ[atTop]
      (fun T : ℝ => ∫ x in rightLine n..rightLine (n + 1), kernel α β z (x + T * I)) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
    apply intervalIntegral.integral_congr
    intro x hx
    apply (hrewrite _ _).symm
    · rw [uIcc_of_le (by dsimp [rightLine]; push_cast; linarith)] at hx
      simpa using hx
    · intro he
      have := congrArg Complex.im he
      simp at this
      linarith
  have hbotEq : (fun T : ℝ => ∫ x in rightLine n..rightLine (n + 1),
      rightNumerator α β z n (x + T * I) / (x + T * I - ((n : ℂ) + 1))) =ᶠ[atBot]
      (fun T : ℝ => ∫ x in rightLine n..rightLine (n + 1), kernel α β z (x + T * I)) := by
    filter_upwards [eventually_lt_atBot (0 : ℝ)] with T hT
    apply intervalIntegral.integral_congr
    intro x hx
    apply (hrewrite _ _).symm
    · rw [uIcc_of_le (by dsimp [rightLine]; push_cast; linarith)] at hx
      simpa using hx
    · intro he
      have := congrArg Complex.im he
      simp at this
      linarith
  have h := BarnesResidue.barnesRes_vertical_shift
    (φ := rightNumerator α β z n) (p := (n : ℂ) + 1)
    (by simp [rightLine] <;> linarith)
    (by simp [rightLine] <;> push_cast <;> linarith)
    (differentiableOn_rightNumerator α β z n)
    (by simpa only [← hv n (Or.inl rfl)] using hi n)
    (by simpa only [← hv (n + 1) (Or.inr rfl)] using hi (n + 1))
    (hh.1.congr' htopEq.symm) (hh.2.congr' hbotEq.symm)
  simp_rw [← hv n (Or.inl rfl), ← hv (n + 1) (Or.inr rfl),
    rightNumerator_residue α β hz0 n] at h
  exact h

/-- Positive radial scaling preserves the actual principal-logarithm margin. -/
theorem margin_pos_scale (α : ℝ) {r : ℝ} (hr : 0 < r) (w : ℂ) :
    margin α ((r : ℂ) * w) = margin α w := by
  rw [margin, margin, ← mul_neg, Complex.arg_real_mul _ hr]

/-- The principal logarithm gives an exact radial norm factor on each vertical line. -/
theorem norm_kernel_pos_scale (α β c y : ℝ) {r : ℝ} (hr : 0 < r)
    {w : ℂ} (hw : w ≠ 0) :
    ‖kernel α β ((r : ℂ) * w) (c + y * I)‖ =
      Real.rpow r (-c) * ‖kernel α β w (c + y * I)‖ := by
  have hl : Complex.log (-((r : ℂ) * w)) =
      (Real.log r : ℂ) + Complex.log (-w) := by
    rw [← mul_neg, Complex.log_ofReal_mul hr (neg_ne_zero.mpr hw)]
  have he : Complex.exp (-((c : ℂ) + y * I) * Complex.log (-((r : ℂ) * w))) =
      Complex.exp (-((c : ℂ) + y * I) * (Real.log r : ℂ)) *
        Complex.exp (-((c : ℂ) + y * I) * Complex.log (-w)) := by
    rw [hl, mul_add, Complex.exp_add]
  have hn : ‖Complex.exp (-((c : ℂ) + y * I) * (Real.log r : ℂ))‖ =
      Real.rpow r (-c) := by
    rw [Complex.norm_exp]
    change Real.exp _ = r ^ (-c)
    rw [Real.rpow_def_of_pos hr]
    congr 1
    simp <;> ring
  simp only [kernel, he, norm_mul, hn]
  ring

/-- The actual contour integral has a radial power bound with a fixed integrable constant. -/
theorem norm_integral_pos_scale_le {α : ℝ} (hα : 0 < α) (β c : ℝ)
    (hc : Real.sin (Real.pi * c) ≠ 0) {w : ℂ} (hw : w ≠ 0)
    (hmargin : 0 < margin α w) {r : ℝ} (hr : 0 < r) :
    ‖∫ y : ℝ, kernel α β ((r : ℂ) * w) (c + y * I)‖ ≤
      Real.rpow r (-c) * ∫ y : ℝ, ‖kernel α β w (c + y * I)‖ := by
  have hi := (integrable_line hα β c w hc hmargin).norm.const_mul (Real.rpow r (-c))
  have h := norm_integral_le_of_norm_le hi (Filter.Eventually.of_forall fun y =>
    (norm_kernel_pos_scale α β c y hr hw).le)
  simpa only [integral_const_mul] using h

end D5.S3.Analytic.Asymptotics.MittagLefflerBarnesKernel
