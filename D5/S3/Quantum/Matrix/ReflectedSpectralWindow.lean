/- GID: D5/S3/Quantum/Matrix/ReflectedSpectralWindow
   generality: G
   mirror-B: D5/B/S3/Quantum/Matrix/ReflectedSpectralWindow
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A finite time window suppresses off-diagonal terms in a signed spectral amplitude. -/

module

public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Ring

/-! A finite window bound for spectra with real signed weights. -/

public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Matrix.ReflectedSpectralWindow

open scoped BigOperators
open MeasureTheory

private noncomputable def phase (freq t : ℝ) : ℂ := Complex.exp ((freq * t : ℝ) * Complex.I)

/-- The signed spectral amplitude at time t. -/
noncomputable def amplitude {ι : Type*} [Fintype ι] (freq c : ι → ℝ) (t : ℝ) : ℂ :=
  ∑ j, (c j : ℂ) * phase (freq j) t

private theorem pair_re (a b x y t : ℝ) :
    ((a : ℂ) * phase x t * star ((b : ℂ) * phase y t)).re =
      a * b * Real.cos ((x - y) * t) := by
  change ((a : ℂ) * phase x t * (starRingEnd ℂ) ((b : ℂ) * phase y t)).re = _
  have harg : (starRingEnd ℂ) ((y * t : ℝ) * Complex.I) =
      ((-(y * t) : ℝ) : ℂ) * Complex.I := by simp
  have hsum : ((x * t : ℝ) : ℂ) * Complex.I + ((-(y * t) : ℝ) : ℂ) * Complex.I =
      (((x - y) * t : ℝ) : ℂ) * Complex.I := by push_cast; ring
  simp only [phase, map_mul, Complex.conj_ofReal, ← Complex.exp_conj, harg]
  rw [show (a : ℂ) * Complex.exp ((x * t : ℝ) * Complex.I) *
      ((b : ℂ) * Complex.exp ((-(y * t) : ℝ) * Complex.I)) =
      ((a * b : ℝ) : ℂ) * (Complex.exp ((x * t : ℝ) * Complex.I) *
        Complex.exp ((-(y * t) : ℝ) * Complex.I)) by push_cast; ring]
  rw [← Complex.exp_add, hsum, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]

private theorem amplitude_energy {ι : Type*} [Fintype ι] (freq c : ι → ℝ) (t : ℝ) :
    ‖amplitude freq c t‖ ^ 2 = ∑ i, ∑ j, c i * c j * Real.cos ((freq i - freq j) * t) := by
  calc
    ‖amplitude freq c t‖ ^ 2 = (amplitude freq c t * (starRingEnd ℂ) (amplitude freq c t)).re := by
      rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
    _ = ∑ i, ∑ j, c j * c i * Real.cos ((freq j - freq i) * t) := by
      simp only [amplitude, map_sum, Finset.sum_mul, Finset.mul_sum, Complex.re_sum]
      exact Finset.sum_congr rfl (fun i _ =>
        Finset.sum_congr rfl (fun j _ => pair_re (c j) (c i) (freq j) (freq i) t))
    _ = _ := Finset.sum_comm

private theorem cosine_window (τ ω : ℝ) (hω : ω ≠ 0) :
    |∫ t in (0 : ℝ)..τ, Real.cos (ω * t)| ≤ |ω|⁻¹ := by
  rw [intervalIntegral.integral_comp_mul_left Real.cos hω, integral_cos]
  simp only [mul_zero, Real.sin_zero, sub_zero, smul_eq_mul, abs_mul, abs_inv]
  exact mul_le_of_le_one_right (inv_nonneg.mpr (abs_nonneg _)) (Real.abs_sin_le_one _)

/-- Bound the integrated spectral interference by the actual off-diagonal weight. -/
theorem interference_bound {ι : Type*} [Fintype ι] (freq c : ι → ℝ)
    (τ δ : ℝ) (hδ : 0 < δ) (hgap : ∀ i j, i ≠ j → δ ≤ |freq i - freq j|) :
    |(∫ t in (0 : ℝ)..τ, ‖amplitude freq c t‖ ^ 2) - τ * ∑ i, (c i) ^ 2| ≤
      δ⁻¹ * ((∑ i, |c i|) ^ 2 - ∑ i, (c i) ^ 2) := by
  classical
  let kernel (i j : ι) := ∫ t in (0 : ℝ)..τ, Real.cos ((freq i - freq j) * t)
  let cross (i j : ι) := if i = j then 0 else c i * c j * kernel i j
  have kernel_diag (i : ι) : kernel i i = τ := by simp [kernel]
  have integral_energy :
      (∫ t in (0 : ℝ)..τ, ‖amplitude freq c t‖ ^ 2) =
        ∑ i, ∑ j, c i * c j * kernel i j := by
    simp only [amplitude_energy]
    rw [intervalIntegral.integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro i _
      rw [intervalIntegral.integral_finsetSum]
      · simp only [intervalIntegral.integral_const_mul, kernel]
      · intro j _
        exact (by fun_prop : Continuous fun t : ℝ =>
          c i * c j * Real.cos ((freq i - freq j) * t)).intervalIntegrable _ _
    · intro i _
      exact (by fun_prop : Continuous fun t : ℝ =>
        ∑ j, c i * c j * Real.cos ((freq i - freq j) * t)).intervalIntegrable _ _
  have integral_split :
      ∑ i, ∑ j, c i * c j * kernel i j = τ * (∑ i, (c i) ^ 2) + ∑ i, ∑ j, cross i j := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    calc
      ∑ j, c i * c j * kernel i j =
          ∑ j, ((if j = i then τ * (c i) ^ 2 else 0) + cross i j) := by
        apply Finset.sum_congr rfl
        intro j _
        by_cases h : j = i
        · subst j
          simp [cross, kernel_diag]
          ring
        · simp [cross, h, Ne.symm h]
      _ = _ := by simp [Finset.sum_add_distrib]
  have cross_le (i j : ι) : |cross i j| ≤
      δ⁻¹ * (if i = j then 0 else |c i| * |c j|) := by
    by_cases h : i = j
    · simp [cross, h]
    · have hg := hgap i j h
      have hd : freq i - freq j ≠ 0 := by
        intro hzero
        rw [hzero, abs_zero] at hg
        linarith
      have hk : |kernel i j| ≤ δ⁻¹ :=
        (cosine_window τ _ hd).trans (inv_anti₀ hδ hg)
      rw [show cross i j = c i * c j * kernel i j by simp [cross, h],
        abs_mul, abs_mul, ite_eq_right h, mul_comm δ⁻¹]
      exact mul_le_mul_of_nonneg_left hk (mul_nonneg (abs_nonneg _) (abs_nonneg _))
  have cross_weight :
      (∑ i, ∑ j, if i = j then 0 else |c i| * |c j|) =
        (∑ i, |c i|) ^ 2 - ∑ i, (c i) ^ 2 := by
    rw [sq, Finset.sum_mul, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    have diagonal : (∑ j : ι, if j = i then (c i) ^ 2 else 0) = (c i) ^ 2 := by simp
    rw [Finset.mul_sum, ← diagonal, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    by_cases h : i = j
    · subst j
      simp [← sq, sq_abs]
    · simp [h, Ne.symm h]
  rw [integral_energy, integral_split, add_comm, add_sub_cancel_right]
  calc
    |∑ i, ∑ j, cross i j| ≤ ∑ i, |∑ j, cross i j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, ∑ j, |cross i j| :=
      Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, ∑ j, δ⁻¹ * (if i = j then 0 else |c i| * |c j|) :=
      Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => cross_le i j
    _ = _ := by simp only [← Finset.mul_sum, cross_weight]

/-- With unit absolute weight, the averaged transition exceeds the stated threshold. -/
theorem average_lower_bound {ι : Type*} [Fintype ι] [Nonempty ι] (freq c : ι → ℝ)
    (hc : (∑ i, |c i|) = 1) (τ δ ε : ℝ) (hδ : 0 < δ) (hε : 0 < ε)
    (hgap : ∀ i j, i ≠ j → δ ≤ |freq i - freq j|)
    (hτ : (Fintype.card ι : ℝ) / (ε * δ) ≤ τ) :
    (1 - ε) / (Fintype.card ι : ℝ) <
      (∫ t in (0 : ℝ)..τ, ‖amplitude freq c t‖ ^ 2) / τ := by
  let n : ℝ := Fintype.card ι
  let diagonal : ℝ := ∑ i, (c i) ^ 2
  let total : ℝ := ∫ t in (0 : ℝ)..τ, ‖amplitude freq c t‖ ^ 2
  have hn : 0 < n := by
    change (0 : ℝ) < (Fintype.card ι : ℝ)
    exact_mod_cast (Fintype.card_pos (α := ι))
  have hεδ : 0 < ε * δ := mul_pos hε hδ
  have ht : 0 < τ := (div_pos hn hεδ).trans_le hτ
  have hcauchy : 1 ≤ n * diagonal := by
    simpa [hc, sq_abs, n, diagonal] using
      (sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun i => |c i|))
  have hdiag : 1 / n ≤ diagonal := (div_le_iff₀ hn).2 (by simpa [mul_comm] using hcauchy)
  have hdiag_pos : 0 < diagonal := (div_pos one_pos hn).trans_le hdiag
  have herr := interference_bound freq c τ δ hδ hgap
  rw [hc, one_pow] at herr
  have hinterference : - (δ⁻¹ * (1 - diagonal)) ≤ total - τ * diagonal :=
    (abs_le.mp herr).1
  have hstrict : δ⁻¹ * (1 - diagonal) < δ⁻¹ := by
    calc
      _ < δ⁻¹ * 1 := mul_lt_mul_of_pos_left (by linarith) (inv_pos.mpr hδ)
      _ = _ := mul_one _
  have hwindow : δ⁻¹ ≤ τ * ε / n := by
    apply (le_div_iff₀ hn).2
    have h : n ≤ τ * (ε * δ) := (div_le_iff₀ hεδ).1 hτ
    rw [mul_comm δ⁻¹, ← div_eq_mul_inv]
    exact (div_le_iff₀ hδ).2 (by simpa [mul_assoc] using h)
  have main : τ * (1 / n) - τ * ε / n < total := by
    linarith [mul_le_mul_of_nonneg_left hdiag ht.le, hstrict.trans_le hwindow]
  change (1 - ε) / n < total / τ
  apply (lt_div_iff₀ ht).2
  calc
    (1 - ε) / n * τ = τ * (1 / n) - τ * ε / n := by ring
    _ < total := main

end D5.S3.Quantum.Matrix.ReflectedSpectralWindow
