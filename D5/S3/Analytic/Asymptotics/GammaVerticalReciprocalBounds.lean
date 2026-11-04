/- GID: D5/S3/Analytic/Asymptotics/GammaVerticalReciprocalBounds
   generality: G
   mirror-B: D5/B/S3/Analytic/Asymptotics/GammaVerticalReciprocalBounds
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Reciprocal Gamma has a uniform exponential bound on bounded vertical strips. -/

/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the repository root LICENSE.
Authors: Bastiaan J Braams
SPDX-License-Identifier: Apache-2.0

Adapted source port from bjbraams/lean-DLMF at
560b9475f35bbc6e4f5296631298859825091f7f. The selected declarations retain
their mathematical statements; imports, namespace and local integrability
ownership are adapted for this repository. Source slices and consumers are
identified in Library/Asymptotics/braams2026barnesmittagport.md.
Retire each port when this repository's pinned Mathlib supplies an equivalent
declaration, replacing its consumers with direct Mathlib calls.
-/

import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import D5.S3.Analytic.Asymptotics.ExponentialAbsIntegrability

open Complex Filter Set MeasureTheory
open scoped Topology Real ComplexConjugate

noncomputable section
namespace D5.S3.Analytic.Asymptotics.GammaVerticalReciprocalBounds

/-- `∑ₖ y²/(x+k)²` converges. -/
private theorem summable_sq_div_add_sq (x y : ℝ) : Summable fun k : ℕ => y ^ 2 / (x + k) ^ 2 := by
  have hg : Summable fun k : ℕ => 4 * y ^ 2 * (1 / (k : ℝ) ^ 2) :=
    (Real.summable_one_div_nat_pow.mpr one_lt_two).mul_left _
  refine Summable.of_norm_bounded_eventually_nat hg ?_
  filter_upwards [eventually_ge_atTop (⌈2 * |x|⌉₊ + 1)] with k hk
  have hk' : 2 * |x| + 1 ≤ k := by
    have := Nat.le_ceil (2 * |x|)
    have : ((⌈2 * |x|⌉₊ + 1 : ℕ) : ℝ) ≤ k := by exact_mod_cast hk
    push_cast at this
    linarith
  have hk0 : (0 : ℝ) < k := by linarith [abs_nonneg x]
  have hxk2 : k / 2 ≤ x + k := by linarith [neg_abs_le x]
  have hxk0 : (0 : ℝ) < x + k := by linarith
  rw [Real.norm_of_nonneg (by positivity), div_le_iff₀ (by positivity : (0 : ℝ) < (x + k) ^ 2)]
  have : (k : ℝ) ^ 2 / 4 ≤ (x + k) ^ 2 := by nlinarith
  field_simp
  nlinarith [sq_nonneg y, mul_le_mul_of_nonneg_left this (sq_nonneg y)]

/-- `∏ₖ (1 + y²/(x+k)²)` converges. -/
private theorem multipliable_one_add_sq_div_add_sq (x y : ℝ) :
    Multipliable fun k : ℕ => 1 + y ^ 2 / (x + k) ^ 2 :=
  Real.multipliable_one_add_of_summable (summable_sq_div_add_sq x y)

open Finset in
/-- Both products follow from Gauss's limit `Γ(s) = lim nˢ n!/(s(s+1)⋯(s+n))`: the ratios of
the Gauss sequences are exactly the partial products. -/
private theorem Gamma_div_Gamma_add_mul_I_sq {x y : ℝ} (hx : ∀ k : ℕ, (x : ℂ) ≠ -k) :
    ‖(Real.Gamma x : ℂ) / Complex.Gamma (x + I * y)‖ ^ 2 =
      ∏' k : ℕ, (1 + y ^ 2 / (x + k) ^ 2) := by
  have hxk : ∀ k : ℕ, (x : ℂ) + k ≠ 0 := fun k h => hx k (eq_neg_of_add_eq_zero_left h)
  have hxk' : ∀ k : ℕ, (x + k : ℝ) ≠ 0 := fun k h => hxk k (by exact_mod_cast h)
  have hz : ∀ k : ℕ, (x : ℂ) + I * y ≠ -k := by
    intro k h
    have him := congrArg Complex.im h
    have hre := congrArg Complex.re h
    simp at him hre
    exact hx k (by exact_mod_cast hre)
  have hmul := multipliable_one_add_sq_div_add_sq x y
  have hP : Tendsto (fun n : ℕ => ∏ k ∈ range (n + 1), (1 + y ^ 2 / (x + k) ^ 2)) atTop
      (𝓝 (∏' k : ℕ, (1 + y ^ 2 / (x + k) ^ 2))) :=
    hmul.hasProd.tendsto_prod_nat.comp (tendsto_add_atTop_nat 1)
  -- the Gauss sequences
  have hseq : ∀ n : ℕ, 0 < n →
      ‖Complex.GammaSeq x n / Complex.GammaSeq (x + I * y) n‖ ^ 2 =
        ∏ k ∈ range (n + 1), (1 + y ^ 2 / (x + k) ^ 2) := by
    intro n hn
    have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
    have hf : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
    have hP1 : ∏ j ∈ range (n + 1), ((x : ℂ) + j) ≠ 0 :=
      prod_ne_zero_iff.mpr fun j _ => hxk j
    have hP2 : ∏ j ∈ range (n + 1), ((x : ℂ) + I * y + j) ≠ 0 :=
      prod_ne_zero_iff.mpr fun j _ => fun h => hz j (eq_neg_of_add_eq_zero_left h)
    have hc1 : (n : ℂ) ^ (x : ℂ) ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl hn')
    have hc2 : (n : ℂ) ^ ((x : ℂ) + I * y) ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl hn')
    have hsplit : Complex.GammaSeq x n / Complex.GammaSeq (x + I * y) n =
        ((n : ℂ) ^ (x : ℂ) / (n : ℂ) ^ ((x : ℂ) + I * y)) *
          (∏ j ∈ range (n + 1), ((x : ℂ) + I * y + j)) / ∏ j ∈ range (n + 1), ((x : ℂ) + j) := by
      simp only [Complex.GammaSeq]
      field_simp
    rw [hsplit, norm_div, norm_mul, norm_div, norm_natCast_cpow_of_pos hn,
      norm_natCast_cpow_of_pos hn]
    have hre : ((x : ℂ) + I * y).re = x := by simp
    rw [hre, Complex.ofReal_re, div_self (Real.rpow_pos_of_pos (Nat.cast_pos.mpr hn) x).ne',
      one_mul,
      norm_prod, norm_prod, div_pow, ← Finset.prod_pow, ← Finset.prod_pow,
      ← prod_div_distrib]
    refine prod_congr rfl fun j _ => ?_
    have h1 : ‖(x : ℂ) + I * y + j‖ ^ 2 = (x + j) ^ 2 + y ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]; simp; ring
    have h2 : ‖(x : ℂ) + j‖ ^ 2 = (x + j) ^ 2 := by
      rw [show (x : ℂ) + j = ((x + j : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
        Real.norm_eq_abs, sq_abs]
    rw [h1, h2]
    have := hxk' j
    field_simp
  have hlim : Tendsto (fun n : ℕ => ‖Complex.GammaSeq x n / Complex.GammaSeq (x + I * y) n‖ ^ 2)
      atTop (𝓝 (‖Complex.Gamma x / Complex.Gamma (x + I * y)‖ ^ 2)) :=
    (((Complex.GammaSeq_tendsto_Gamma _).div (Complex.GammaSeq_tendsto_Gamma _)
      (Complex.Gamma_ne_zero hz)).norm).pow 2
  rw [← Complex.Gamma_ofReal]
  refine tendsto_nhds_unique hlim (hP.congr' ?_)
  filter_upwards [eventually_gt_atTop 0] with n hn
  exact (hseq n hn).symm

/-- `Γ(z) Γ(z̄) = |Γ(z)|²`. -/
private theorem Gamma_mul_Gamma_conj (z : ℂ) :
    Complex.Gamma z * Complex.Gamma (conj z) = (‖Complex.Gamma z‖ : ℂ) ^ 2 := by
  rw [Complex.Gamma_conj, mul_conj, Complex.normSq_eq_norm_sq, ofReal_pow]

/-- DLMF 5.4.4: `Γ(1/2 + iy) Γ(1/2 - iy) = |Γ(1/2 + iy)|² = π/cosh(πy)`. -/
private theorem Gamma_half_add_mul_I (y : ℝ) :
    Complex.Gamma (1 / 2 + I * y) * Complex.Gamma (1 / 2 - I * y) =
      ‖Complex.Gamma (1 / 2 + I * y)‖ ^ 2 ∧
    ‖Complex.Gamma (1 / 2 + I * y)‖ ^ 2 = π / Real.cosh (π * y) := by
  let z : ℂ := 1 / 2 + I * y
  have hstar : star z = 1 / 2 - I * y := by
    simp [z, star_add, star_mul]
    ring
  have harg : (1 : ℂ) - z = 1 / 2 - I * y := by
    simp [z]
    ring
  have hprod :
      Complex.Gamma z * Complex.Gamma (1 / 2 - I * y) = π / sin (π * z) := by
    simpa [harg] using Complex.Gamma_mul_Gamma_one_sub z
  have hnorm :
      Complex.Gamma z * Complex.Gamma (1 / 2 - I * y) =
        ‖Complex.Gamma z‖ ^ 2 := by
    rw [← hstar]; exact Gamma_mul_Gamma_conj z
  have hsin : sin (π * z) = Real.cosh (π * y) := by
    have hsplit : (π : ℂ) * z = (π / 2 : ℂ) + (↑(π * y) : ℂ) * I := by
      simp [z, mul_add]
      ring
    rw [hsplit, sin_add_mul_I]
    simp [Complex.sin_pi_div_two, Complex.cos_pi_div_two, Complex.ofReal_cosh]
  refine ⟨hnorm, ?_⟩
  have hℂ : (‖Complex.Gamma z‖ ^ 2 : ℂ) = (π / Real.cosh (π * y) : ℂ) := by
    calc
      (‖Complex.Gamma z‖ ^ 2 : ℂ) =
          Complex.Gamma z * Complex.Gamma (1 / 2 - I * y) := hnorm.symm
      _ = π / sin (π * z) := hprod
      _ = π / Real.cosh (π * y) := by rw [hsin]
  exact_mod_cast hℂ

/-- The product `P(x,y) = ∏ₖ (1 + y²/(x+k)²)` of DLMF 5.8.3. -/
private def gammaVertProd (x y : ℝ) : ℝ := ∏' k : ℕ, (1 + y ^ 2 / (x + k) ^ 2)

/-- The partial products `∏_{k<n} (1 + y²/(x + k)²)` tend to `gammaVertProd x y`. -/
private theorem tendsto_prod_gammaVertProd (x y : ℝ) :
    Tendsto (fun n : ℕ => ∏ k ∈ Finset.range n, (1 + y ^ 2 / (x + k) ^ 2)) atTop
      (𝓝 (gammaVertProd x y)) :=
  (multipliable_one_add_sq_div_add_sq x y).hasProd.tendsto_prod_nat

/-- `gammaVertProd x y ≥ 1`. -/
private theorem one_le_gammaVertProd (x y : ℝ) : 1 ≤ gammaVertProd x y :=
  ge_of_tendsto' (tendsto_prod_gammaVertProd x y) fun n =>
    Finset.one_le_prod₀ fun k _ => le_add_of_nonneg_right (by positivity)

/-- The product decreases in `x > 0`. -/
private theorem gammaVertProd_anti {x x' : ℝ} (hx : 0 < x) (hxx : x ≤ x') (y : ℝ) :
    gammaVertProd x' y ≤ gammaVertProd x y := by
  refine le_of_tendsto_of_tendsto' (tendsto_prod_gammaVertProd x' y)
    (tendsto_prod_gammaVertProd x y) fun n => ?_
  refine Finset.prod_le_prod₀ (fun k _ => by positivity) fun k _ => ?_
  have h1 : 0 < x + k := by positivity
  gcongr

/-- For `x > 0`, `|Γ(x + iy)|² = Γ(x)² / ∏ₖ (1 + y²/(x + k)²)`. -/
private theorem norm_Gamma_sq_eq {x : ℝ} (hx : 0 < x) (y : ℝ) :
    ‖Complex.Gamma (x + I * y)‖ ^ 2 = Real.Gamma x ^ 2 / gammaVertProd x y := by
  have hxk : ∀ k : ℕ, (x : ℂ) ≠ -k := fun k h => by
    have := congrArg re h; simp at this; linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  have h := Gamma_div_Gamma_add_mul_I_sq (y := y) hxk
  have hne : Complex.Gamma (x + I * y) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by simp [hx])
  rw [gammaVertProd, ← h, norm_div, div_pow, norm_real, Real.norm_of_nonneg
    (Real.Gamma_pos_of_pos hx).le]
  have : ‖Complex.Gamma (x + I * y)‖ ≠ 0 := norm_ne_zero_iff.mpr hne
  field_simp

/-- `∏ₖ (1 + y²/(1/2 + k)²) = cosh(π y)`. -/
private theorem gammaVertProd_half (y : ℝ) : gammaVertProd (1 / 2) y = Real.cosh (π * y) := by
  have h := norm_Gamma_sq_eq (one_half_pos) y
  rw [show (((1 / 2 : ℝ)) : ℂ) = 1 / 2 by push_cast; ring, (Gamma_half_add_mul_I y).2,
    Real.Gamma_one_half_eq, Real.sq_sqrt Real.pi_pos.le] at h
  · have hP := one_le_gammaVertProd (1 / 2) y
    have hc := Real.cosh_pos (π * y)
    field_simp at h
    nlinarith [h]

/-- `cosh t ≤ e^|t|`. -/
private theorem cosh_le_exp_abs (t : ℝ) : Real.cosh t ≤ Real.exp |t| := by
  rw [Real.cosh_eq]
  have h1 := Real.exp_le_exp.mpr (le_abs_self t)
  have h2 := Real.exp_le_exp.mpr (neg_le_abs t)
  linarith

/-- For `x ≥ 1/2`: `|1/Γ(x+iy)|² = P(x,y)/Γ(x)² ≤ cosh(πy)/Γ(x)²`. -/
theorem norm_recip_Gamma_sq_le {x : ℝ} (hx : 1 / 2 ≤ x) (y : ℝ) :
    ‖(Complex.Gamma (x + I * y))⁻¹‖ ^ 2 ≤ Real.exp (π * |y|) / Real.Gamma x ^ 2 := by
  have hx0 : 0 < x := by linarith
  have hG := Real.Gamma_pos_of_pos hx0
  have hP := gammaVertProd_anti (by norm_num : (0 : ℝ) < 1 / 2) hx y
  rw [gammaVertProd_half] at hP
  have hP1 := one_le_gammaVertProd x y
  rw [norm_inv, inv_pow, norm_Gamma_sq_eq hx0, inv_div]
  have hc : Real.cosh (π * y) ≤ Real.exp (π * |y|) := by
    have := cosh_le_exp_abs (π * y); rwa [abs_mul, abs_of_pos Real.pi_pos] at this
  gcongr
  linarith

/-- **Growth of `1/Γ` on vertical lines**, uniformly for `x` in a bounded interval:
`|1/Γ(x+iy)| ≤ C (1+|y|)^K e^{π|y|/2}`. -/
theorem exists_norm_recip_Gamma_le (X : ℝ) :
    ∃ C : ℝ, ∃ K : ℕ, ∀ x ∈ Icc (-X) X, ∀ y : ℝ,
      ‖(Complex.Gamma (x + I * y))⁻¹‖ ≤ C * (1 + |y|) ^ K * Real.exp (π * |y| / 2) := by
  set B : ℝ := max X 2 with hB
  have hB2 : 2 ≤ B := le_max_right _ _
  -- the minimum of `Γ` on `[1/2, B]`
  obtain ⟨m, hm, hmin⟩ : ∃ m : ℝ, 0 < m ∧ ∀ x ∈ Icc (1 / 2 : ℝ) B, m ≤ Real.Gamma x := by
    have hcont : ContinuousOn Real.Gamma (Icc (1 / 2 : ℝ) B) := fun x hx =>
      (Real.differentiableAt_Gamma fun k h => by
        have := hx.1; rw [h] at this; linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
        ).continuousAt.continuousWithinAt
    obtain ⟨x₀, hx₀, hmin⟩ := isCompact_Icc.exists_isMinOn
      (nonempty_Icc.mpr (by linarith)) hcont
    exact ⟨Real.Gamma x₀, Real.Gamma_pos_of_pos (by linarith [hx₀.1]), fun x hx => hmin hx⟩
  have base : ∀ x ∈ Icc (1 / 2 : ℝ) B, ∀ y : ℝ,
      ‖(Complex.Gamma (x + I * y))⁻¹‖ ≤ m⁻¹ * Real.exp (π * |y| / 2) := by
    intro x hx y
    have h := norm_recip_Gamma_sq_le hx.1 y
    have hGm := hmin x hx
    have hE : Real.exp (π * |y|) = Real.exp (π * |y| / 2) ^ 2 := by
      rw [← Real.exp_nat_mul]; ring_nf
    refine (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp (h.trans ?_)
    rw [hE, mul_pow, div_eq_mul_inv, mul_comm, inv_pow]
    gcongr
  have step : ∀ n : ℕ, ∀ x ∈ Icc (1 / 2 - n : ℝ) B, ∀ y : ℝ,
      ‖(Complex.Gamma (x + I * y))⁻¹‖ ≤
        m⁻¹ * (B + n) ^ n * (1 + |y|) ^ n * Real.exp (π * |y| / 2) := by
    intro n
    induction n with
    | zero => intro x hx y; simpa using base x (by simpa using hx) y
    | succ n ih =>
      intro x hx y
      by_cases hx' : 1 / 2 - (n : ℝ) ≤ x
      · refine (ih x ⟨hx', hx.2⟩ y).trans ?_
        have h1 : (B + n) ^ n ≤ (B + (n + 1 : ℕ)) ^ (n + 1) := by
          push_cast
          calc (B + n) ^ n ≤ (B + (n + 1)) ^ n := by gcongr; linarith
            _ ≤ (B + (n + 1)) ^ (n + 1) := pow_le_pow_right₀ (by linarith) (Nat.le_succ n)
        have h2 : (1 + |y|) ^ n ≤ (1 + |y|) ^ (n + 1) :=
          pow_le_pow_right₀ (by linarith [abs_nonneg y]) (Nat.le_succ n)
        have hm0 : 0 ≤ m⁻¹ := inv_nonneg.mpr hm.le
        calc m⁻¹ * (B + n) ^ n * (1 + |y|) ^ n * Real.exp (π * |y| / 2)
            ≤ m⁻¹ * (B + (n + 1 : ℕ)) ^ (n + 1) * (1 + |y|) ^ (n + 1) *
                Real.exp (π * |y| / 2) := by gcongr
          _ = _ := by push_cast; ring
      push Not at hx'
      have hx1 : x + 1 ∈ Icc (1 / 2 - n : ℝ) B := by
        constructor
        · push_cast at hx; linarith [hx.1]
        · linarith
      have h := ih (x + 1) hx1 y
      by_cases hw : (x : ℂ) + I * y = 0
      · rw [hw, Complex.Gamma_zero, inv_zero, norm_zero]
        have hm0 : 0 ≤ m⁻¹ := inv_nonneg.mpr hm.le
        have : 0 ≤ B + (n + 1 : ℕ) := by positivity
        positivity
      have hG := Complex.Gamma_add_one _ hw
      rw [show (x : ℂ) + I * y + 1 = ((x + 1 : ℝ) : ℂ) + I * y by push_cast; ring] at hG
      have hinv : (Complex.Gamma (x + I * y))⁻¹ =
          ((x : ℂ) + I * y) * (Complex.Gamma (((x + 1 : ℝ) : ℂ) + I * y))⁻¹ := by
        rw [hG, mul_inv, ← mul_assoc, mul_inv_cancel₀ hw, one_mul]
      rw [hinv, norm_mul]
      have hn1 : ‖(x : ℂ) + I * y‖ ≤ (B + (n + 1 : ℕ)) * (1 + |y|) := by
        refine (norm_add_le _ _).trans ?_
        rw [norm_real, norm_mul, norm_I, one_mul, norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
        have hxa : |x| ≤ B + (n + 1 : ℕ) := by
          rw [abs_le]; push_cast at hx ⊢; constructor <;> linarith [hx.1, hx.2]
        have : (1 : ℝ) ≤ B + (n + 1 : ℕ) := by push_cast; linarith
        nlinarith [abs_nonneg y, abs_nonneg x]
      have hB' : (B + n) ^ n ≤ (B + (n + 1 : ℕ)) ^ n := by gcongr; linarith
      have hm0 : 0 ≤ m⁻¹ := inv_nonneg.mpr hm.le
      calc ‖(x : ℂ) + I * y‖ * ‖(Complex.Gamma (((x + 1 : ℝ) : ℂ) + I * y))⁻¹‖
          ≤ ((B + (n + 1 : ℕ)) * (1 + |y|)) *
              (m⁻¹ * (B + n) ^ n * (1 + |y|) ^ n * Real.exp (π * |y| / 2)) :=
            mul_le_mul hn1 h (norm_nonneg _) (by positivity)
        _ ≤ ((B + (n + 1 : ℕ)) * (1 + |y|)) *
              (m⁻¹ * (B + (n + 1 : ℕ)) ^ n * (1 + |y|) ^ n * Real.exp (π * |y| / 2)) := by
            gcongr
        _ = _ := by ring
  obtain ⟨n, hn⟩ := exists_nat_ge (X + 1)
  refine ⟨m⁻¹ * (B + n) ^ n, n, fun x hx y => ?_⟩
  refine (step n x ⟨by linarith [hx.1], hx.2.trans (le_max_left _ _)⟩ y).trans (le_of_eq ?_)
  ring

/-- Polynomial times `e^{-c|y|}` is integrable on `ℝ`. -/
theorem integrable_one_add_abs_pow_mul_exp_neg {c : ℝ} (hc : 0 < c) (K : ℕ) :
    Integrable (fun y : ℝ => (1 + |y|) ^ K * Real.exp (-(c * |y|))) := by
  -- `(1+t)^K e^{-ct/2}` is bounded on `t ≥ 0`
  have hlim : Tendsto (fun t : ℝ => (1 + t) ^ K * Real.exp (-(c / 2 * t))) atTop (𝓝 0) := by
    have hu : Tendsto (fun t : ℝ => c / 2 * (1 + t)) atTop atTop :=
      (tendsto_atTop_add_const_left _ 1 tendsto_id).const_mul_atTop (half_pos hc)
    have h := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero K).comp hu
    have h' := h.const_mul ((2 / c) ^ K * Real.exp (c / 2))
    rw [mul_zero] at h'
    refine h'.congr' (Eventually.of_forall fun t => ?_)
    simp only [Function.comp_apply]
    have hc' : c ≠ 0 := hc.ne'
    rw [show -(c / 2 * (1 + t)) = -(c / 2 * t) + -(c / 2) by ring, Real.exp_add, mul_pow]
    have h1 : Real.exp (c / 2) * Real.exp (-(c / 2)) = 1 := by rw [← Real.exp_add]; simp
    have h2 : (2 / c) ^ K * (c / 2) ^ K = 1 := by rw [← mul_pow]; field_simp; simp
    linear_combination ((1 + t) ^ K * Real.exp (-(c / 2 * t))) *
      ((2 / c) ^ K * (c / 2) ^ K * h1 + h2)
  obtain ⟨M, hM⟩ := (hlim.eventually (gt_mem_nhds one_pos)).exists_forall_of_atTop
  have hbd : ∃ D : ℝ, ∀ t : ℝ, 0 ≤ t → (1 + t) ^ K * Real.exp (-(c / 2 * t)) ≤ D := by
    obtain ⟨D, hD⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := max M 0)).exists_bound_of_continuousOn
      (f := fun t : ℝ => (1 + t) ^ K * Real.exp (-(c / 2 * t))) (by fun_prop)
    refine ⟨max D 1, fun t ht => ?_⟩
    by_cases htM : t ≤ max M 0
    · have := hD t ⟨ht, htM⟩
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)] at this
      exact this.trans (le_max_left _ _)
    · push Not at htM
      exact (hM t (le_of_lt (lt_of_le_of_lt (le_max_left _ _) htM))).le.trans (le_max_right _ _)
  obtain ⟨D, hD⟩ := hbd
  refine ((D5.S3.Analytic.Asymptotics.ExponentialAbsIntegrability.integrable_exp_neg_mul_abs (half_pos hc)).const_mul D).mono'
    (by fun_prop) (Eventually.of_forall fun y => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have h := hD |y| (abs_nonneg y)
  have he : Real.exp (-(c * |y|)) = Real.exp (-(c / 2 * |y|)) * Real.exp (-(c / 2 * |y|)) := by
    rw [← Real.exp_add]; ring_nf
  rw [he, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right h (Real.exp_pos _).le

end D5.S3.Analytic.Asymptotics.GammaVerticalReciprocalBounds
