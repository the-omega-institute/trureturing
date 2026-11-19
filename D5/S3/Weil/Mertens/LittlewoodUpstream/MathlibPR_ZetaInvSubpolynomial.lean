/- GID: D5/S3/Weil/Mertens/LittlewoodUpstream/MathlibPR_ZetaInvSubpolynomial
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Littlewood subpower bounds for the removable reciprocal on zero-free half-planes. -/

/-
Copyright (c) 2026 Qamar Munawer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qamar Munawer
Source: Qamarbajwa/RiemannBlueprint@1cf9572a7cdc5dbae1860dcb7c80729f614549a4
Adapted to a parameterized zero-free half-plane.
The strip estimate uses the repository's fractional-part Mellin identity.
-/
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Complex.BorelCaratheodory
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Hadamard
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.PSeriesComplex
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.LSeries.SumCoeff
import D5.S3.Weil.ZetaPntBounds.NymanFractionalMellin

/-!
# Littlewood's reciprocal zeta growth bound on zero-free half-planes

A zero-free edge `θ ∈ [1/2, 1)` gives subpolynomial growth of the removable
reciprocal on every closed half-plane strictly to its right. After shifting
by one and dividing by the shifted variable, the regularized reciprocal
decays with every exponent `-p` for `0 < p < 1` on closed real strips inside
the shifted zero-free half-plane.
-/

set_option linter.style.openClassical false

section

open scoped LSeries.notation Topology
open Asymptotics Complex Filter MeasureTheory Metric Set Real

/-! ### Fractional-part bound for the strip estimate -/

/-- The reciprocal fractional-part function `x ↦ {1 / x}`. -/
private noncomputable def recipFract (x : ℝ) : ℝ :=
  Int.fract (1 / x)

private lemma norm_recipFract_le_one (x : ℝ) : ‖(recipFract x : ℂ)‖ ≤ 1 := by
  unfold recipFract
  rw [Complex.norm_real, Real.norm_of_nonneg (Int.fract_nonneg _)]
  exact (Int.fract_lt_one _).le

/-! ### Stage 1: Unconditional `riemannZeta` Strip and Right-Half-Plane Bounds -/

/-- Removable-singularity inverse of `riemannZeta`: equals `0` at `s = 1`
and `(ζ s)⁻¹` elsewhere. -/
noncomputable def zetaInv (s : ℂ) : ℂ :=
  if s = 1 then 0 else (riemannZeta s)⁻¹

/-- `zetaInv` has complex derivative `1` at `s = 1` from the residue `(s - 1) * ζ(s) → 1`. -/
private theorem hasDerivAt_zetaInv_one : HasDerivAt zetaInv 1 1 := by
  rw [hasDerivAt_iff_tendsto_slope, slope_fun_def_field]
  simp only [zetaInv, ↓reduceIte, sub_zero]
  have h_res := riemannZeta_residue_one
  have h_inv : Tendsto (fun z : ℂ => ((z - 1) * riemannZeta z)⁻¹) (𝓝[≠] 1) (𝓝 (1⁻¹ : ℂ)) :=
    h_res.inv₀ one_ne_zero
  rw [inv_one] at h_inv
  refine h_inv.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with z hz
  have hne : z ≠ 1 := hz
  simp only [hne, ↓reduceIte]
  have hsub : z - 1 ≠ 0 := sub_ne_zero.mpr hne
  by_cases hζ : riemannZeta z = 0
  · simp [hζ]
  · field_simp [hsub, hζ]

private theorem differentiableAt_zetaInv_one : DifferentiableAt ℂ zetaInv 1 :=
  hasDerivAt_zetaInv_one.differentiableAt

/-- For any `s ≠ 1` with `riemannZeta s ≠ 0`, `zetaInv` is differentiable at `s`. -/
private theorem differentiableAt_zetaInv {s : ℂ} (hs1 : s ≠ 1) (hζ : riemannZeta s ≠ 0) :
    DifferentiableAt ℂ zetaInv s := by
  have h_ev : zetaInv =ᶠ[𝓝 s] (fun z => (riemannZeta z)⁻¹) := by
    filter_upwards [isOpen_ne.mem_nhds hs1] with z hz
    simp [zetaInv, hz]
  exact ((differentiableAt_riemannZeta hs1).inv hζ).congr_of_eventuallyEq h_ev

/-- The removable reciprocal is differentiable throughout a zero-free half-plane. -/
theorem differentiableOn_zetaInv_of_zero_free {θ : ℝ}
    (hzero : ∀ z : ℂ, θ < z.re → z ≠ 1 → riemannZeta z ≠ 0) :
    DifferentiableOn ℂ zetaInv {z : ℂ | θ < z.re} := by
  intro z hz
  by_cases h1 : z = 1
  · subst z
    exact differentiableAt_zetaInv_one.differentiableWithinAt
  · exact (differentiableAt_zetaInv h1 (hzero z hz h1)).differentiableWithinAt

/-- Unconditional upper bound for the fractional-part integral on `0 < s.re`. -/
private lemma norm_integral_Ioc_recipFract_le {s : ℂ} (hs : 0 < s.re) :
    ‖∫ x in Set.Ioc (0 : ℝ) 1,
      (recipFract x : ℂ) * (x : ℂ) ^ (s - 1)‖ ≤ 1 / s.re := by
  have hint_real : IntegrableOn (fun x : ℝ => x ^ (s.re - 1)) (Set.Ioc 0 1) := by
    simpa [sub_eq_add_neg] using
      (intervalIntegral.intervalIntegrable_rpow' (show (-1 : ℝ) < s.re - 1 by linarith)).1
  have hnorm :
      ‖∫ x in Set.Ioc (0 : ℝ) 1,
        (recipFract x : ℂ) * (x : ℂ) ^ (s - 1)‖ ≤
        ∫ x in Set.Ioc (0 : ℝ) 1, x ^ (s.re - 1) := by
    refine norm_integral_le_of_norm_le hint_real ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx.1]
    simp only [Complex.sub_re, Complex.one_re]
    exact mul_le_of_le_one_left (Real.rpow_nonneg hx.1.le _)
      (norm_recipFract_le_one x)
  have hval : (∫ x in Set.Ioc (0 : ℝ) 1, x ^ (s.re - 1)) = 1 / s.re := by
    rw [← intervalIntegral.integral_of_le zero_le_one,
      integral_rpow (Or.inl (show (-1 : ℝ) < s.re - 1 by linarith))]
    have h0 : (0 : ℝ) ^ s.re = 0 := Real.zero_rpow (ne_of_gt hs)
    rw [show s.re - 1 + 1 = s.re by ring, h0, Real.one_rpow, sub_zero, one_div]
  linarith

/-- **Stage 1 Strip Bound (Unconditional):**
For `1/2 ≤ s.re` and `1 ≤ |s.im|`, `‖ζ(s)‖ ≤ 3 * ‖s‖`. -/
private theorem norm_riemannZeta_le_three_mul_norm {s : ℂ}
    (hs_re : 1 / 2 ≤ s.re) (hs_im : 1 ≤ |s.im|) :
    ‖riemannZeta s‖ ≤ 3 * ‖s‖ := by
  have hs_pos : 0 < s.re := by linarith
  have hs_ne_one : s ≠ 1 := by
    intro h
    rw [h] at hs_im
    norm_num at hs_im
  have hid : (∫ x in Set.Ioc (0 : ℝ) 1,
      (recipFract x : ℂ) * (x : ℂ) ^ (s - 1)) =
      1 / (s - 1) - riemannZeta s / s := by
    rw [MeasureTheory.integral_Ioc_eq_integral_Ioo]
    simpa only [recipFract] using
      D5.S3.Weil.ZetaPntBounds.NymanFractionalMellin.bd_mellin_base_case_proved
        s hs_pos hs_ne_one
  have hs_ne0 : s ≠ 0 := by
    intro h
    rw [h] at hs_pos
    simp at hs_pos
  have hζ : riemannZeta s =
      s / (s - 1) - s * ∫ x in Set.Ioc (0 : ℝ) 1,
        (recipFract x : ℂ) * (x : ℂ) ^ (s - 1) := by
    have h1 := congrArg (s * ·) hid
    have h1' : s * ∫ x in Set.Ioc (0 : ℝ) 1,
        (recipFract x : ℂ) * (x : ℂ) ^ (s - 1) =
        s / (s - 1) - riemannZeta s := by
      rw [h1, mul_sub, div_eq_mul_inv, mul_div_cancel₀ _ hs_ne0]
      ring
    rw [h1']
    ring
  rw [hζ]
  have h_sub_ge : 1 ≤ ‖s - 1‖ := by
    calc (1 : ℝ) ≤ |s.im| := hs_im
      _ = |(s - 1).im| := by simp
      _ ≤ ‖s - 1‖ := Complex.abs_im_le_norm (s - 1)
  have h1 : ‖s / (s - 1)‖ ≤ ‖s‖ := by
    rw [norm_div]
    exact div_le_self (norm_nonneg s) h_sub_ge
  have h2 : ‖s * ∫ x in Set.Ioc (0 : ℝ) 1,
      (recipFract x : ℂ) * (x : ℂ) ^ (s - 1)‖ ≤ 2 * ‖s‖ := by
    rw [norm_mul]
    calc ‖s‖ * ‖∫ x in Set.Ioc (0 : ℝ) 1,
          (recipFract x : ℂ) * (x : ℂ) ^ (s - 1)‖
        ≤ ‖s‖ * (1 / s.re) :=
          mul_le_mul_of_nonneg_left (norm_integral_Ioc_recipFract_le hs_pos) (norm_nonneg s)
      _ ≤ ‖s‖ * 2 := by
          gcongr
          rw [div_le_iff₀ hs_pos]
          linarith
      _ = 2 * ‖s‖ := by ring
  calc ‖s / (s - 1) - s * ∫ x in Set.Ioc (0 : ℝ) 1, _‖
      ≤ ‖s / (s - 1)‖ + ‖s * ∫ x in Set.Ioc (0 : ℝ) 1, _‖ := norm_sub_le _ _
    _ ≤ ‖s‖ + 2 * ‖s‖ := add_le_add h1 h2
    _ = 3 * ‖s‖ := by ring

/-- Telescoping tail bound `∑_{n ≥ 2} n^{-2} ≤ 3/4 < 1`, giving uniform lower/upper bounds
on `ζ(2 + it)`. -/
private lemma norm_riemannZeta_sub_one_le_of_two_le_re {s : ℂ} (hs : 2 ≤ s.re) :
    ‖riemannZeta s - 1‖ ≤ 3 / 4 := by
  have hs1 : 1 < s.re := by linarith
  rw [zeta_eq_tsum_one_div_nat_add_one_cpow hs1]
  have hsum : Summable (fun n : ℕ => 1 / ((n : ℂ) + 1) ^ s) := by
    have h_norm : Summable (fun n : ℕ => ‖1 / ((n : ℂ) + 1) ^ s‖) := by
      have h_ev : (fun n : ℕ => ‖1 / ((n : ℂ) + 1) ^ s‖) =
          fun n : ℕ => ((n : ℝ) + 1) ^ (-s.re) := by
        ext n
        rw [norm_div, norm_one, one_div]
        have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
        rw [← Complex.ofReal_natCast, ← Complex.ofReal_one, ← Complex.ofReal_add,
          Complex.norm_cpow_eq_rpow_re_of_pos hn, Real.rpow_neg hn.le]
      rw [h_ev]
      exact (Real.summable_nat_rpow_inv.mpr hs1).comp_injective
        Nat.succ_injective |>.congr fun n => by
        simp [Real.rpow_neg (by positivity : (0 : ℝ) ≤ (n : ℝ) + 1)]
    exact h_norm.of_norm
  rw [Summable.tsum_eq_zero_add hsum]
  simp only [Nat.cast_zero, zero_add, one_cpow, div_one, add_sub_cancel_left]
  have hsum1 : Summable (fun n : ℕ => 1 / (((n + 1 : ℕ) : ℂ) + 1) ^ s) :=
    hsum.comp_injective Nat.succ_injective
  rw [Summable.tsum_eq_zero_add hsum1]
  have h_zero : 1 / (((0 + 1 : ℕ) : ℂ) + 1) ^ s = 1 / (2 : ℂ) ^ s := by
    norm_num
  rw [h_zero]
  have hsum2 : Summable (fun n : ℕ => 1 / ((n : ℂ) + 3) ^ s) :=
    (hsum1.comp_injective Nat.succ_injective).congr fun n => by
      simp only [Function.comp_apply]
      congr 2
      push_cast
      ring
  have h_shift : (∑' b : ℕ, 1 / ((((b + 1) + 1 : ℕ) : ℂ) + 1) ^ s) =
      ∑' n : ℕ, 1 / ((n : ℂ) + 3) ^ s := by
    refine tsum_congr fun n => ?_
    congr 2
    push_cast
    ring
  rw [h_shift]
  have h_tele_hasSum : HasSum (fun n : ℕ => (1 : ℝ) / (((n : ℝ) + 2) * ((n : ℝ) + 3))) (1 / 2) := by
    rw [hasSum_iff_tendsto_nat_of_nonneg (fun _ => by positivity)]
    have h_part : ∀ N : ℕ, ∑ n ∈ Finset.range N, (1 : ℝ) / (((n : ℝ) + 2) * ((n : ℝ) + 3)) =
        1 / 2 - 1 / ((N : ℝ) + 2) := by
      intro N
      have hterm : ∀ n : ℕ, (1 : ℝ) / (((n : ℝ) + 2) * ((n : ℝ) + 3)) =
          1 / ((n : ℝ) + 2) - 1 / (((n + 1 : ℕ) : ℝ) + 2) := by
        intro n; push_cast
        have h2 : (n : ℝ) + 2 ≠ 0 := by positivity
        have h3 : (n : ℝ) + 3 ≠ 0 := by positivity
        field_simp [h2, h3]; ring
      simp_rw [hterm]
      rw [Finset.sum_range_sub' (fun n : ℕ => 1 / ((n : ℝ) + 2))]
      norm_num
    simp_rw [h_part]
    have h_inv_lim : Tendsto (fun N : ℕ => 1 / ((N : ℝ) + 2)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
    simpa using tendsto_const_nhds.sub h_inv_lim
  have h_re_le : ∀ n : ℕ, ‖1 / ((n : ℂ) + 3) ^ s‖ ≤ (1 : ℝ) / (((n : ℝ) + 2) * ((n : ℝ) + 3)) := by
    intro n
    rw [norm_div, norm_one]
    have hn : (1 : ℝ) ≤ (n : ℝ) + 3 := by linarith [Nat.cast_nonneg (α := ℝ) n]
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_ofNat, ← Complex.ofReal_add,
      Complex.norm_cpow_eq_rpow_re_of_pos (by positivity)]
    have hpow2 : ((n : ℝ) + 3) ^ (2 : ℝ) ≤ ((n : ℝ) + 3) ^ s.re :=
      Real.rpow_le_rpow_of_exponent_le hn hs
    have hmul : ((n : ℝ) + 2) * ((n : ℝ) + 3) ≤ ((n : ℝ) + 3) ^ (2 : ℝ) := by
      rw [Real.rpow_two]
      nlinarith
    have h_mul_pos : 0 < ((n : ℝ) + 2) * ((n : ℝ) + 3) := by positivity
    exact one_div_le_one_div_of_le h_mul_pos (hmul.trans hpow2)
  have hnorm_sum : ‖1 / (2 : ℂ) ^ s + ∑' n : ℕ, 1 / ((n : ℂ) + 3) ^ s‖ ≤ 3 / 4 := by
    have h_first : ‖1 / (2 : ℂ) ^ s‖ ≤ 1 / 4 := by
      rw [norm_div, norm_one, ← Complex.ofReal_ofNat,
        Complex.norm_cpow_eq_rpow_re_of_pos (by positivity)]
      have h2 : (2 : ℝ) ^ (2 : ℝ) ≤ (2 : ℝ) ^ s.re :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) hs
      calc 1 / (2 : ℝ) ^ s.re ≤ 1 / ((2 : ℝ) ^ (2 : ℝ)) :=
            one_div_le_one_div_of_le (by positivity) h2
        _ = 1 / 4 := by norm_num
    have h_tail : ‖∑' n : ℕ, 1 / ((n : ℂ) + 3) ^ s‖ ≤ 1 / 2 := by
      have h_tri_neg : ∀ n : ℕ, 0 ≤ ‖1 / ((n : ℂ) + 3) ^ s‖ := fun _ => norm_nonneg _
      have h_le_pos : ∀ n : ℕ, 0 ≤ (1 : ℝ) / (((n : ℝ) + 2) * ((n : ℝ) + 3)) :=
        fun _ => by positivity
      calc ‖∑' n : ℕ, 1 / ((n : ℂ) + 3) ^ s‖
          ≤ ∑' n : ℕ, ‖1 / ((n : ℂ) + 3) ^ s‖ := norm_tsum_le_tsum_norm hsum2.norm
        _ ≤ ∑' n : ℕ, (1 : ℝ) / (((n : ℝ) + 2) * ((n : ℝ) + 3)) :=
            Summable.tsum_le_tsum h_re_le hsum2.norm h_tele_hasSum.summable
        _ = 1 / 2 := h_tele_hasSum.tsum_eq
    calc ‖1 / (2 : ℂ) ^ s + ∑' n : ℕ, 1 / ((n : ℂ) + 3) ^ s‖
        ≤ ‖1 / (2 : ℂ) ^ s‖ + ‖∑' n : ℕ, 1 / ((n : ℂ) + 3) ^ s‖ := norm_add_le _ _
      _ ≤ 1 / 4 + 1 / 2 := add_le_add h_first h_tail
      _ = 3 / 4 := by norm_num
  simpa using hnorm_sum

/-- For `2 ≤ s.re`, `1 / 4 ≤ ‖ζ(s)‖`, `‖ζ(s)‖ ≤ 7 / 4`, and `‖zetaInv s‖ ≤ 4`. -/
private lemma norm_zeta_lower_of_two_le_re {s : ℂ} (hs : 2 ≤ s.re) :
    1 / 4 ≤ ‖riemannZeta s‖ ∧ ‖riemannZeta s‖ ≤ 7 / 4 ∧ ‖zetaInv s‖ ≤ 4 := by
  have hsub := norm_riemannZeta_sub_one_le_of_two_le_re hs
  have h_lo : 1 / 4 ≤ ‖riemannZeta s‖ := by
    have htri := norm_sub_norm_le (1 : ℂ) (riemannZeta s)
    rw [norm_one, norm_sub_rev] at htri
    linarith
  have h_hi : ‖riemannZeta s‖ ≤ 7 / 4 := by
    have htri := norm_add_le (1 : ℂ) (riemannZeta s - 1)
    simp only [add_sub_cancel, norm_one] at htri
    linarith
  have hs_ne1 : s ≠ 1 := by
    intro h
    rw [h] at hs
    norm_num at hs
  have h_inv : ‖zetaInv s‖ ≤ 4 := by
    unfold zetaInv
    split_ifs with hs1
    · exact (hs_ne1 hs1).elim
    · rw [norm_inv]
      exact inv_le_of_inv_le₀ (by norm_num) (by linarith)
  exact ⟨h_lo, h_hi, h_inv⟩

/-- Uniform logarithmic-derivative bound on `{s : ℂ | 1 + η ≤ s.re}` (`0 < η`). -/
private theorem norm_logDeriv_riemannZeta_le {η : ℝ} (hη : 0 < η) :
    ∃ C > 0, ∀ s : ℂ, 1 + η ≤ s.re → ‖deriv riemannZeta s / riemannZeta s‖ ≤ C := by
  have h1 : 1 < (1 + η : ℂ).re := by simp [hη]
  have hsum_ref : LSeriesSummable (↗ArithmeticFunction.vonMangoldt) (1 + η : ℂ) :=
    ArithmeticFunction.LSeriesSummable_vonMangoldt h1
  refine ⟨(∑' n : ℕ, ‖LSeries.term (↗ArithmeticFunction.vonMangoldt) (1 + η : ℂ) n‖) + 1,
    by positivity, fun s hs => ?_⟩
  have hs1 : 1 < s.re := by linarith
  have h_eq := ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs1
  have h_eq' : deriv riemannZeta s / riemannZeta s = -L ↗ArithmeticFunction.vonMangoldt s := by
    rw [h_eq]; ring
  rw [h_eq', norm_neg]
  have hsum_s : LSeriesSummable (↗ArithmeticFunction.vonMangoldt) s :=
    ArithmeticFunction.LSeriesSummable_vonMangoldt hs1
  calc ‖L ↗ArithmeticFunction.vonMangoldt s‖
      ≤ ∑' n : ℕ, ‖LSeries.term (↗ArithmeticFunction.vonMangoldt) s n‖ :=
        norm_tsum_le_tsum_norm hsum_s.norm
    _ ≤ ∑' n : ℕ, ‖LSeries.term (↗ArithmeticFunction.vonMangoldt) (1 + η : ℂ) n‖ := by
        refine Summable.tsum_le_tsum (fun n => ?_) hsum_s.norm hsum_ref.norm
        rcases eq_or_ne n 0 with rfl | hn
        · simp [LSeries.term]
        · simp only [LSeries.term, hn, ↓reduceIte, norm_div]
          have hn_ge1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.pos_of_ne_zero hn
          have hn_pos : (0 : ℝ) < n := by positivity
          rw [← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos hn_pos,
            Complex.norm_cpow_eq_rpow_re_of_pos hn_pos]
          simp only [Complex.add_re, Complex.one_re, Complex.ofReal_re]
          exact div_le_div_of_nonneg_left (norm_nonneg _) (Real.rpow_pos_of_pos hn_pos _)
            (Real.rpow_le_rpow_of_exponent_le hn_ge1 hs)
    _ ≤ (∑' n : ℕ, ‖LSeries.term (↗ArithmeticFunction.vonMangoldt) (1 + η : ℂ) n‖) + 1 := by
        linarith

/-! ### Stage 2: Holomorphic Logarithm on Disks & Borel–Carathéodory Bound -/

/-- Norm bound for `Complex.log w` on `1/4 ≤ ‖w‖ ≤ 7/4`:
`‖Complex.log w‖ ≤ Real.log 4 + Real.pi`. -/
private lemma norm_log_le_of_bounds {w : ℂ} (hlo : 1 / 4 ≤ ‖w‖) (hhi : ‖w‖ ≤ 7 / 4) :
    ‖Complex.log w‖ ≤ Real.log 4 + Real.pi := by
  have hlog : Complex.log w = (Real.log ‖w‖ : ℂ) + (Complex.arg w : ℂ) * I := rfl
  rw [hlog]
  have hre_abs : |Real.log ‖w‖| ≤ Real.log 4 := by
    rw [abs_le]
    constructor
    · have h1 := Real.log_le_log (by norm_num : (0 : ℝ) < 1 / 4) hlo
      rw [one_div, Real.log_inv] at h1
      linarith
    · have h2 := Real.log_le_log (by linarith : 0 < ‖w‖) (by linarith : ‖w‖ ≤ 4)
      linarith
  have him_abs : |Complex.arg w| ≤ Real.pi :=
    abs_le.mpr ⟨(Complex.neg_pi_lt_arg w).le, Complex.arg_le_pi w⟩
  calc ‖(Real.log ‖w‖ : ℂ) + (Complex.arg w : ℂ) * I‖
      ≤ ‖(Real.log ‖w‖ : ℂ)‖ + ‖(Complex.arg w : ℂ) * I‖ := norm_add_le _ _
    _ = |Real.log ‖w‖| + |Complex.arg w| := by
        simp [Complex.norm_real, Complex.norm_I]
    _ ≤ Real.log 4 + Real.pi := add_le_add hre_abs him_abs

/-- Given the zero-free half-plane, for `6 ≤ |t|` and `0 < η < 1/4`, there is a holomorphic branch
`logZ : ℂ → ℂ` on `B = ball (2 + t * I) (2 - θ - η/2)` satisfying:
1. `exp (logZ z) = riemannZeta z` on `B`;
2. `‖logZ z‖ ≤ M₁` uniformly in `t` on `closedBall (2 + t * I) (1 - η)`;
3. `‖logZ z‖ ≤ M₃ * Real.log |t|` uniformly on `closedBall (2 + t * I) (2 - θ - η)`. -/
private theorem exists_logZeta_ball_bounds_of_zero_free {θ : ℝ}
    (hθ_half : 1 / 2 ≤ θ) (hθ_lt_one : θ < 1)
    (hzero : ∀ z : ℂ, θ < z.re → z ≠ 1 → riemannZeta z ≠ 0)
    {η : ℝ} (hη0 : 0 < η) (hη1 : η < 1 / 4) :
    ∃ M₁ M₃ : ℝ, 0 < M₁ ∧ 0 < M₃ ∧
      ∀ (t : ℝ), 6 ≤ |t| →
        ∃ logZ : ℂ → ℂ,
          DifferentiableOn ℂ logZ (ball (2 + (t : ℂ) * I) (2 - θ - η / 2)) ∧
          (∀ z ∈ ball (2 + (t : ℂ) * I) (2 - θ - η / 2), Complex.exp (logZ z) = riemannZeta z) ∧
          (∀ z ∈ closedBall (2 + (t : ℂ) * I) (1 - η), ‖logZ z‖ ≤ M₁) ∧
          (∀ z ∈ closedBall (2 + (t : ℂ) * I) (2 - θ - η), ‖logZ z‖ ≤ M₃ * Real.log |t|) := by
  obtain ⟨CΛ, hCΛ_pos, hCΛ⟩ := norm_logDeriv_riemannZeta_le hη0
  set R₀ : ℝ := 2 - θ - η / 2
  set r₁ : ℝ := 1 - η
  set r₃ : ℝ := 2 - θ - η
  have hR₀_pos : 0 < R₀ := by dsimp [R₀]; linarith
  have hr₃_lt_R₀ : r₃ < R₀ := by dsimp [r₃, R₀]; linarith
  set M₁ : ℝ := Real.log 4 + Real.pi + CΛ * r₁
  -- Choose M₃ large enough so Bore-Caratheodory gives ‖L z‖ ≤ M₃ * log |t| for |t| ≥ 6
  -- (note log 6 > 1.7 > 1)
  set c_bc : ℝ := 2 * r₃ / (η / 2)
  set d_bc : ℝ := (2 * Real.log 6) * r₃ / (η / 2) + (Real.log 4 + Real.pi) * (R₀ + r₃) / (η / 2)
  set M₃ : ℝ := c_bc + d_bc + 1
  have hM₁_pos : 0 < M₁ := by
    have := Real.log_pos (by norm_num : (1 : ℝ) < 4)
    have := Real.pi_pos
    have : 0 < r₁ := by dsimp [r₁]; linarith
    positivity
  have h_eta_half : 0 < η / 2 := by linarith
  have hc_bc_nn : 0 ≤ c_bc := by
    have : 0 < r₃ := by dsimp [r₃]; linarith
    positivity
  have hd_bc_nn : 0 ≤ d_bc := by
    have : 0 < r₃ := by dsimp [r₃]; linarith
    have : 0 < Real.log 6 := Real.log_pos (by norm_num)
    have : 0 < Real.log 4 := Real.log_pos (by norm_num)
    have := Real.pi_pos
    positivity
  have hM₃_pos : 0 < M₃ := by dsimp [M₃]; linarith
  refine ⟨M₁, M₃, hM₁_pos, hM₃_pos, fun t ht => ?_⟩
  set s₀ : ℂ := 2 + (t : ℂ) * I
  set B : Set ℂ := ball s₀ R₀
  have hs₀_re : 2 ≤ s₀.re := by simp [s₀]
  have h_ball_prop : ∀ z ∈ B, θ + η / 2 < z.re ∧ z.re < 7 / 2 ∧
      9 / 2 < |z.im| ∧ ‖z‖ ≤ 2 * |t| := by
    intro z hz
    have hdist : ‖z - s₀‖ < R₀ := mem_ball_iff_norm.mp hz
    have hre_sub : |z.re - 2| < R₀ := by
      have h1 : |z.re - 2| = |(z - s₀).re| := by simp [s₀]
      rw [h1]
      exact (Complex.abs_re_le_norm (z - s₀)).trans_lt hdist
    have him_sub : |z.im - t| < R₀ := by
      have h1 : |z.im - t| = |(z - s₀).im| := by simp [s₀]
      rw [h1]
      exact (Complex.abs_im_le_norm (z - s₀)).trans_lt hdist
    have hre_lo : θ + η / 2 < z.re := by
      have := (abs_lt.mp hre_sub).1
      dsimp [R₀] at this
      linarith
    have hre_hi : z.re < 7 / 2 := by
      have := (abs_lt.mp hre_sub).2
      dsimp [R₀] at this
      linarith
    have him_lo : 9 / 2 < |z.im| := by
      have : |t| - |z.im| ≤ |z.im - t| := by
        simpa [abs_sub_comm] using abs_sub_abs_le_abs_sub t z.im
      dsimp [R₀] at him_sub
      linarith
    have him_hi : |z.im| < |t| + 3 / 2 := by
      have : |z.im| - |t| ≤ |z.im - t| := abs_sub_abs_le_abs_sub z.im t
      dsimp [R₀] at him_sub
      linarith
    have hnorm : ‖z‖ ≤ 2 * |t| := by
      have htri : ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
      have hzre_abs : |z.re| ≤ 7 / 2 := abs_le.mpr ⟨by linarith, by linarith⟩
      linarith
    exact ⟨hre_lo, hre_hi, him_lo, hnorm⟩
  have hB_nz : ∀ z ∈ B, z ≠ 1 ∧ riemannZeta z ≠ 0 := by
    intro z hz
    obtain ⟨hre, _, him, _⟩ := h_ball_prop z hz
    have hz1 : z ≠ 1 := by
      intro h; rw [h] at him; norm_num at him
    have hζ : riemannZeta z ≠ 0 := hzero z (by linarith) hz1
    exact ⟨hz1, hζ⟩
  have hlogDeriv_diff : DifferentiableOn ℂ (fun z => deriv riemannZeta z / riemannZeta z) B := by
    have hζ_diff : DifferentiableOn ℂ riemannZeta B := fun z hz =>
      (differentiableAt_riemannZeta (hB_nz z hz).1).differentiableWithinAt
    have hζ_deriv_diff : DifferentiableOn ℂ (deriv riemannZeta) B := hζ_diff.deriv isOpen_ball
    exact hζ_deriv_diff.div hζ_diff (fun z hz => (hB_nz z hz).2)
  have hs₀_mem : s₀ ∈ B := mem_ball_self hR₀_pos
  obtain ⟨logZ, hLs₀, hL_deriv⟩ :=
    (hlogDeriv_diff.isExactOn_ball).with_val_at s₀ (Complex.log (riemannZeta s₀))
  have hL_diff : DifferentiableOn ℂ logZ B :=
    fun z hz => (hL_deriv z hz).differentiableAt.differentiableWithinAt
  have h_exp_eq : ∀ z ∈ B, Complex.exp (logZ z) = riemannZeta z := by
    let Q : ℂ → ℂ := fun z => riemannZeta z * Complex.exp (-logZ z)
    have hQ_deriv : ∀ z ∈ B, HasDerivAt Q 0 z := by
      intro z hz
      have h1 : HasDerivAt riemannZeta (deriv riemannZeta z) z :=
        (differentiableAt_riemannZeta (hB_nz z hz).1).hasDerivAt
      have h2 : HasDerivAt (fun w => Complex.exp (-logZ w))
          (Complex.exp (-logZ z) * -(deriv riemannZeta z / riemannZeta z)) z :=
        ((hL_deriv z hz).neg).cexp
      have hmul := h1.mul h2
      have hzero : deriv riemannZeta z * Complex.exp (-logZ z) +
          riemannZeta z * (Complex.exp (-logZ z) * -(deriv riemannZeta z / riemannZeta z)) = 0 := by
        have hζnz : riemannZeta z ≠ 0 := (hB_nz z hz).2
        field_simp [hζnz]; ring
      rw [hzero] at hmul
      exact hmul
    have hQ_const : ∀ z ∈ B, Q z = Q s₀ := fun z hz =>
      ((convex_ball s₀ R₀).is_const_of_fderivWithin_eq_zero
        (fun w hw => (hQ_deriv w hw).differentiableAt.differentiableWithinAt)
        (fun w hw => by
          rw [(hQ_deriv w hw).hasDerivWithinAt.hasFDerivWithinAt.fderivWithin
            (isOpen_ball.uniqueDiffOn w hw)]
          ext1; simp)
        hz hs₀_mem)
    intro z hz
    have hQs₀ : Q s₀ = 1 := by
      dsimp [Q]
      rw [hLs₀, Complex.exp_neg, Complex.exp_log (hB_nz s₀ hs₀_mem).2,
        mul_inv_cancel₀ (hB_nz s₀ hs₀_mem).2]
    have hQz : riemannZeta z * Complex.exp (-logZ z) = 1 := (hQ_const z hz).trans hQs₀
    rw [Complex.exp_neg] at hQz
    have h1 : (Complex.exp (logZ z))⁻¹ = (riemannZeta z)⁻¹ :=
      eq_inv_of_mul_eq_one_right hQz
    calc Complex.exp (logZ z) = ((Complex.exp (logZ z))⁻¹)⁻¹ := (inv_inv _).symm
      _ = ((riemannZeta z)⁻¹)⁻¹ := by rw [h1]
      _ = riemannZeta z := inv_inv _
  have h_inner_bound : ∀ z ∈ closedBall s₀ r₁, ‖logZ z‖ ≤ M₁ := by
    set S₁ : Set ℂ := closedBall s₀ r₁
    have hr₁_lt_R₀ : r₁ < R₀ := by dsimp [r₁, R₀]; linarith
    have hS₁_sub : S₁ ⊆ B := closedBall_subset_ball hr₁_lt_R₀
    have hS₁_diff : ∀ z ∈ S₁, DifferentiableAt ℂ logZ z :=
      fun z hz => (hL_deriv z (hS₁_sub hz)).differentiableAt
    have hS₁_deriv_bound : ∀ z ∈ S₁, ‖deriv logZ z‖ ≤ CΛ := by
      intro z hz
      have hre_ge : 1 + η ≤ z.re := by
        have hdist : ‖z - s₀‖ ≤ r₁ := mem_closedBall_iff_norm.mp hz
        have hre_abs : |z.re - 2| ≤ r₁ := by
          have : |z.re - 2| = |(z - s₀).re| := by simp [s₀]
          rw [this]
          exact (Complex.abs_re_le_norm (z - s₀)).trans hdist
        have := (abs_le.mp hre_abs).1
        dsimp [r₁] at this; linarith
      rw [(hL_deriv z (hS₁_sub hz)).deriv]
      exact hCΛ z hre_ge
    have hs₀_S₁ : s₀ ∈ S₁ := mem_closedBall_self (by dsimp [r₁]; linarith)
    obtain ⟨hlo_s₀, hhi_s₀, _⟩ := norm_zeta_lower_of_two_le_re hs₀_re
    have hLs₀_norm : ‖logZ s₀‖ ≤ Real.log 4 + Real.pi := by
      rw [hLs₀]
      exact norm_log_le_of_bounds hlo_s₀ hhi_s₀
    intro z hz
    have hmvt := (convex_closedBall s₀ r₁).norm_image_sub_le_of_norm_deriv_le
      hS₁_diff hS₁_deriv_bound hs₀_S₁ hz
    have hdist_le : ‖z - s₀‖ ≤ r₁ := mem_closedBall_iff_norm.mp hz
    calc ‖logZ z‖ ≤ ‖logZ z - logZ s₀‖ + ‖logZ s₀‖ := norm_le_norm_sub_add _ _
      _ ≤ CΛ * ‖z - s₀‖ + (Real.log 4 + Real.pi) := add_le_add hmvt hLs₀_norm
      _ ≤ CΛ * r₁ + (Real.log 4 + Real.pi) := by gcongr
      _ = M₁ := by dsimp [M₁]; ring
  have h_outer_bound : ∀ z ∈ closedBall s₀ r₃, ‖logZ z‖ ≤ M₃ * Real.log |t| := by
    let g : ℂ → ℂ := fun w => logZ (s₀ + w)
    have hg_diff : DifferentiableOn ℂ g (ball 0 R₀) := by
      refine hL_diff.comp ((differentiable_id.const_add s₀).differentiableOn) ?_
      intro w hw
      rw [mem_ball_iff_norm, add_sub_cancel_left]
      exact mem_ball_zero_iff.mp hw
    set M_re : ℝ := Real.log (6 * |t|)
    have hM_re_pos : 0 < M_re := Real.log_pos (by linarith)
    have hg_re : MapsTo g (ball 0 R₀) {z : ℂ | z.re ≤ M_re} := by
      intro w hw
      have hwB : s₀ + w ∈ B := by
        rw [mem_ball_iff_norm, add_sub_cancel_left]
        exact mem_ball_zero_iff.mp hw
      obtain ⟨hre, _, him, hnorm⟩ := h_ball_prop (s₀ + w) hwB
      have hre_ge_half : 1 / 2 ≤ (s₀ + w).re := by linarith
      have him_ge_one : 1 ≤ |(s₀ + w).im| := by linarith
      have hζ_le := norm_riemannZeta_le_three_mul_norm hre_ge_half him_ge_one
      have hζ_pos : 0 < ‖riemannZeta (s₀ + w)‖ := norm_pos_iff.mpr (hB_nz (s₀ + w) hwB).2
      have hexp_re : Real.exp (g w).re = ‖riemannZeta (s₀ + w)‖ := by
        dsimp [g]
        rw [← Complex.norm_exp, h_exp_eq (s₀ + w) hwB]
      have hre_eq : (g w).re = Real.log ‖riemannZeta (s₀ + w)‖ := by
        rw [← hexp_re, Real.log_exp]
      rw [Set.mem_ofPred_eq, hre_eq]
      exact Real.log_le_log hζ_pos (hζ_le.trans (by linarith))
    obtain ⟨hlo_s₀, hhi_s₀, _⟩ := norm_zeta_lower_of_two_le_re hs₀_re
    have hg0_norm : ‖g 0‖ ≤ Real.log 4 + Real.pi := by
      dsimp [g]; rw [add_zero, hLs₀]
      exact norm_log_le_of_bounds hlo_s₀ hhi_s₀
    have hlog6_le : 1 ≤ Real.log |t| := by
      have h_e : Real.exp 1 ≤ |t| := by
        have := Real.exp_one_lt_d9
        linarith
      calc 1 = Real.log (Real.exp 1) := (Real.log_exp 1).symm
        _ ≤ Real.log |t| := Real.log_le_log (Real.exp_pos 1) h_e
    intro z hz
    set w := z - s₀
    have hw_mem : w ∈ ball 0 R₀ := by
      rw [mem_ball_zero_iff]
      exact (mem_closedBall_iff_norm.mp hz).trans_lt hr₃_lt_R₀
    have hw_norm : ‖w‖ ≤ r₃ := mem_closedBall_iff_norm.mp hz
    have hbc := Complex.borelCaratheodory hM_re_pos hg_diff hg_re hR₀_pos hw_mem
    have hdenom : R₀ - ‖w‖ ≥ η / 2 := by dsimp [R₀, r₃] at *; linarith
    have hM_re_split : M_re = Real.log 6 + Real.log |t| :=
      Real.log_mul (by norm_num) (by linarith)
    have h_r₃_pos : 0 < r₃ := by dsimp [r₃]; linarith
    have h_term1_le : 2 * M_re * ‖w‖ / (R₀ - ‖w‖) ≤ 2 * M_re * r₃ / (η / 2) := by
      have hnum : 2 * M_re * ‖w‖ ≤ 2 * M_re * r₃ := by gcongr
      calc 2 * M_re * ‖w‖ / (R₀ - ‖w‖)
          ≤ 2 * M_re * r₃ / (R₀ - ‖w‖) := div_le_div_of_nonneg_right hnum (by linarith)
        _ ≤ 2 * M_re * r₃ / (η / 2) := by
            rw [div_eq_mul_inv, div_eq_mul_inv]
            exact mul_le_mul_of_nonneg_left (inv_anti₀ (by positivity) hdenom) (by positivity)
    have h_term2_le : ‖g 0‖ * (R₀ + ‖w‖) / (R₀ - ‖w‖) ≤
        (Real.log 4 + Real.pi) * (R₀ + r₃) / (η / 2) := by
      have h_pi_nn : 0 ≤ Real.log 4 + Real.pi := by positivity
      have hnum : ‖g 0‖ * (R₀ + ‖w‖) ≤ (Real.log 4 + Real.pi) * (R₀ + r₃) :=
        mul_le_mul hg0_norm (by linarith) (by positivity) h_pi_nn
      calc ‖g 0‖ * (R₀ + ‖w‖) / (R₀ - ‖w‖)
          ≤ (Real.log 4 + Real.pi) * (R₀ + r₃) / (R₀ - ‖w‖) :=
            div_le_div_of_nonneg_right hnum (by linarith)
        _ ≤ (Real.log 4 + Real.pi) * (R₀ + r₃) / (η / 2) := by
            rw [div_eq_mul_inv, div_eq_mul_inv]
            exact mul_le_mul_of_nonneg_left (inv_anti₀ (by positivity) hdenom) (by positivity)
    calc ‖logZ z‖ = ‖g w‖ := by simp [g, w]
      _ ≤ 2 * M_re * ‖w‖ / (R₀ - ‖w‖) + ‖g 0‖ * (R₀ + ‖w‖) / (R₀ - ‖w‖) := hbc
      _ ≤ 2 * M_re * r₃ / (η / 2) + (Real.log 4 + Real.pi) * (R₀ + r₃) / (η / 2) :=
          add_le_add h_term1_le h_term2_le
      _ = c_bc * Real.log |t| + d_bc := by
          rw [hM_re_split]
          dsimp [c_bc, d_bc]
          ring
      _ ≤ c_bc * Real.log |t| + d_bc * Real.log |t| := by
          gcongr
          exact le_mul_of_one_le_right hd_bc_nn hlog6_le
      _ ≤ M₃ * Real.log |t| := by
          dsimp [M₃]
          nlinarith [hlog6_le]
  exact ⟨logZ, hL_diff, h_exp_eq, h_inner_bound, h_outer_bound⟩

/-! ### Stage 3: Littlewood (1912) Three-Lines Bound & Inverse Zeta Growth -/

/-- Elementary sublinear-vs-linear bound: if `0 < θ < 1`, `0 ≤ A`, and `0 < δ`,
then `∃ B ≥ 0, ∀ x ≥ 0, A * x ^ θ ≤ δ * x + B`. -/
private lemma sublinear_rpow_le_linear {θ A eps : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hA : 0 ≤ A) (heps : 0 < eps) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x : ℝ, 0 ≤ x → A * x ^ θ ≤ eps * x + B := by
  set X₀ : ℝ := (A / eps) ^ (1 / (1 - θ)) + 1
  have hX₀_pos : 0 < X₀ := by positivity
  refine ⟨A * X₀ ^ θ, by positivity, fun x hx => ?_⟩
  rcases le_total x X₀ with hle | hgt
  · have hxθ : x ^ θ ≤ X₀ ^ θ := Real.rpow_le_rpow hx hle hθ0.le
    calc A * x ^ θ ≤ A * X₀ ^ θ := mul_le_mul_of_nonneg_left hxθ hA
      _ ≤ eps * x + A * X₀ ^ θ := le_add_of_nonneg_left (mul_nonneg heps.le hx)
  · have h1mθ : 0 < 1 - θ := sub_pos.mpr hθ1
    have h_base_gt : (A / eps) ^ (1 / (1 - θ)) < x := by linarith
    have h_rpow : A / eps ≤ x ^ (1 - θ) := by
      have h_pow_le := Real.rpow_le_rpow (by positivity) h_base_gt.le h1mθ.le
      rw [← Real.rpow_mul (by positivity), one_div_mul_cancel h1mθ.ne', Real.rpow_one] at h_pow_le
      exact h_pow_le
    have hx_pos : 0 < x := lt_of_lt_of_le hX₀_pos hgt
    have hmul : A * x ^ θ ≤ eps * x := by
      calc A * x ^ θ = eps * ((A / eps) * x ^ θ) := by field_simp [heps.ne']
        _ ≤ eps * (x ^ (1 - θ) * x ^ θ) := by
            gcongr
        _ = eps * x := by
            rw [← Real.rpow_add hx_pos]
            simp
    linarith [show 0 ≤ A * X₀ ^ θ by positivity]

/-- Littlewood's subpower bound for the removable reciprocal on every closed
half-plane strictly to the right of a zero-free edge `θ ∈ [1/2, 1)`. -/
theorem inv_zeta_isBigO_im_of_zero_free {θ : ℝ}
    (hθ_half : 1 / 2 ≤ θ) (hθ_lt_one : θ < 1)
    (hzero : ∀ z : ℂ, θ < z.re → z ≠ 1 → riemannZeta z ≠ 0)
    {σ₀ eps : ℝ} (hσ₀ : θ < σ₀) (heps : 0 < eps) :
    ∃ C > 0, ∀ s : ℂ, σ₀ ≤ s.re → ‖zetaInv s‖ ≤ C * (1 + |s.im|) ^ eps := by
  set σ₁ : ℝ := min σ₀ ((θ + 1) / 2)
  have hσ₁_gt : θ < σ₁ := lt_min hσ₀ (by linarith)
  have hσ₁_le_σ₀ : σ₁ ≤ σ₀ := min_le_left _ _
  have hσ₁_lt_one : σ₁ < 1 := (min_le_right _ _).trans_lt (by linarith)
  set η : ℝ := (σ₁ - θ) / 4
  have hη0 : 0 < η := by dsimp [η]; linarith
  have hη1 : η < 1 / 4 := by dsimp [η]; linarith
  obtain ⟨M₁, M₃, hM₁_pos, hM₃_pos, h_ball⟩ :=
    exists_logZeta_ball_bounds_of_zero_free hθ_half hθ_lt_one hzero hη0 hη1
  set r₁ : ℝ := 1 - η
  set r₂_max : ℝ := 2 - σ₁
  set r₃ : ℝ := 2 - θ - η
  have hr₁_pos : 0 < r₁ := by dsimp [r₁]; linarith
  have hr₁_lt_r₂max : r₁ < r₂_max := by dsimp [r₁, r₂_max, η]; linarith
  have hr₂max_lt_r₃ : r₂_max < r₃ := by dsimp [r₂_max, r₃, η]; linarith
  have hr₁_lt_r₃ : r₁ < r₃ := hr₁_lt_r₂max.trans hr₂max_lt_r₃
  set u_strip : ℝ := Real.log (r₃ / r₁)
  have hu_pos : 0 < u_strip := Real.log_pos ((one_lt_div hr₁_pos).mpr hr₁_lt_r₃)
  set α : ℝ := Real.log (r₂_max / r₁) / u_strip
  have h_r2_gt1 : 1 < r₂_max / r₁ := (one_lt_div hr₁_pos).mpr hr₁_lt_r₂max
  have h_r2_lt_r3 : r₂_max / r₁ < r₃ / r₁ := div_lt_div_of_pos_right hr₂max_lt_r₃ hr₁_pos
  have hα0 : 0 < α := div_pos (Real.log_pos h_r2_gt1) hu_pos
  have hα1 : α < 1 := (div_lt_one hu_pos).mpr (Real.log_lt_log (by positivity) h_r2_lt_r3)
  set A_coef : ℝ := max M₁ 1 * (M₃ ^ α)
  have hA_nn : 0 ≤ A_coef := by positivity
  obtain ⟨B_sub, hB_sub_nn, h_sublin⟩ := sublinear_rpow_le_linear hα0 hα1 hA_nn heps
  set t₀ : ℝ := max 6 (Real.exp (1 / M₃))
  have ht₀_ge6 : 6 ≤ t₀ := le_max_left _ _
  set K_box : Set ℂ := Icc σ₁ 2 ×ℂ Icc (-t₀) t₀
  have hK_compact : IsCompact K_box := isCompact_Icc.reProdIm isCompact_Icc
  have hK_sub : K_box ⊆ {s : ℂ | θ < s.re} := fun s hs => hσ₁_gt.trans_le hs.1.1
  have hK_cont : ContinuousOn zetaInv K_box :=
    ((differentiableOn_zetaInv_of_zero_free hzero).mono hK_sub).continuousOn
  obtain ⟨B_box, hB_box⟩ := hK_compact.exists_bound_of_continuousOn hK_cont
  set C : ℝ := max 4 (max (max B_box 0) (max (Real.exp B_sub) (Real.exp M₁))) + 1
  have hC_pos : 0 < C := by
    have : 0 ≤ max 4 (max (max B_box 0) (max (Real.exp B_sub) (Real.exp M₁))) :=
      le_max_of_le_left (by norm_num)
    linarith
  refine ⟨C, hC_pos, fun s hs_re => ?_⟩
  have h_one_le_rpow : (1 : ℝ) ≤ (1 + |s.im|) ^ eps :=
    Real.one_le_rpow (by linarith [abs_nonneg s.im]) heps.le
  have h_base_bound : ∀ M_bnd : ℝ, M_bnd ≤ C → M_bnd ≤ C * (1 + |s.im|) ^ eps := fun M_bnd hM => by
    calc M_bnd ≤ C := hM
      _ = C * 1 := (mul_one C).symm
      _ ≤ C * (1 + |s.im|) ^ eps := mul_le_mul_of_nonneg_left h_one_le_rpow hC_pos.le
  rcases le_or_gt 2 s.re with hs_ge2 | hs_lt2
  · obtain ⟨_, _, h_inv⟩ := norm_zeta_lower_of_two_le_re hs_ge2
    exact h_inv.trans (h_base_bound 4 (by
      dsimp [C]
      linarith [le_max_left 4 (max (max B_box 0) (max (Real.exp B_sub) (Real.exp M₁)))]))
  · rcases le_or_gt |s.im| t₀ with him_le | him_gt
    · have hs_box : s ∈ K_box := ⟨⟨hσ₁_le_σ₀.trans hs_re, hs_lt2.le⟩, abs_le.mp him_le⟩
      have h_le_B : ‖zetaInv s‖ ≤ max B_box 0 := (hB_box s hs_box).trans (le_max_left _ _)
      have h_le_C : max B_box 0 ≤ C := by
        dsimp [C]
        have h1 : max B_box 0 ≤ max (max B_box 0) (max (Real.exp B_sub) (Real.exp M₁)) :=
          le_max_left _ _
        have h2 := h1.trans (le_max_right 4 _)
        linarith
      exact h_le_B.trans (h_base_bound (max B_box 0) h_le_C)
    · have ht6 : 6 ≤ |s.im| := ht₀_ge6.trans him_gt.le
      obtain ⟨logZ, hL_diff, h_exp_eq, h_inner, h_outer⟩ := h_ball s.im ht6
      set s₀ : ℂ := 2 + (s.im : ℂ) * I
      have hs_ne1 : s ≠ 1 := by
        intro h; rw [h] at ht6; norm_num at ht6
      rcases le_or_gt (1 + η) s.re with hs_ge1η | hs_lt1η
      · have hs_inner : s ∈ closedBall s₀ r₁ := by
          rw [mem_closedBall_iff_norm]
          have hsub : s - s₀ = ((s.re - 2 : ℝ) : ℂ) := by
            apply Complex.ext <;> simp [s₀]
          rw [hsub, Complex.norm_real, Real.norm_eq_abs, abs_le]
          dsimp [r₁]; constructor <;> linarith
        have hr₁_lt_R₀ : r₁ < 2 - θ - η / 2 := by dsimp [r₁]; linarith
        have hexp_s : Complex.exp (logZ s) = riemannZeta s :=
          h_exp_eq s (closedBall_subset_ball hr₁_lt_R₀ hs_inner)
        have h_inv_norm : ‖zetaInv s‖ ≤ Real.exp M₁ := by
          have hz_eq : zetaInv s = (riemannZeta s)⁻¹ := by simp [zetaInv, hs_ne1]
          rw [hz_eq, norm_inv, ← hexp_s, Complex.norm_exp, ← Real.exp_neg]
          refine Real.exp_le_exp.mpr ?_
          have h_neg_le : -(logZ s).re ≤ ‖logZ s‖ := by
            linarith [neg_le_abs (logZ s).re, Complex.abs_re_le_norm (logZ s)]
          exact h_neg_le.trans (h_inner s hs_inner)
        have h_le_C : Real.exp M₁ ≤ C := by
          dsimp [C]
          have h1 := (le_max_right (Real.exp B_sub) (Real.exp M₁)).trans
            (le_max_right (max B_box 0) _) |>.trans (le_max_right 4 _)
          linarith
        exact h_inv_norm.trans (h_base_bound (Real.exp M₁) h_le_C)
      · have hs_ge_σ₁ : σ₁ ≤ s.re := hσ₁_le_σ₀.trans hs_re
        set r_s : ℝ := 2 - s.re
        have hr_lo : r₁ < r_s := by dsimp [r₁, r_s]; linarith
        have hr_hi : r_s ≤ r₂_max := by dsimp [r_s, r₂_max]; linarith
        let F : ℂ → ℂ := fun w => logZ (s₀ + (r₁ : ℂ) * Complex.exp w)
        have h_map_strip : ∀ w ∈ Complex.HadamardThreeLines.verticalClosedStrip 0 u_strip,
            s₀ + (r₁ : ℂ) * Complex.exp w ∈ closedBall s₀ r₃ := by
          intro w hw
          rw [mem_closedBall_iff_norm, add_sub_cancel_left, norm_mul, Complex.norm_real,
            Real.norm_eq_abs, abs_of_pos hr₁_pos, Complex.norm_exp]
          have hw_le : w.re ≤ u_strip := hw.2
          calc r₁ * Real.exp w.re ≤ r₁ * Real.exp u_strip :=
                mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hw_le) hr₁_pos.le
            _ = r₁ * (r₃ / r₁) := by
                dsimp [u_strip]; rw [Real.exp_log (div_pos (by linarith) hr₁_pos)]
            _ = r₃ := mul_div_cancel₀ r₃ hr₁_pos.ne'
        have hr₃_lt_R₀ : r₃ < 2 - θ - η / 2 := by dsimp [r₃]; linarith
        have hF_diff : DiffContOnCl ℂ F (Complex.HadamardThreeLines.verticalStrip 0 u_strip) := by
          have h_cl : closure (Complex.HadamardThreeLines.verticalStrip 0 u_strip) ⊆
              Complex.HadamardThreeLines.verticalClosedStrip 0 u_strip := by
            intro w hw
            have h_closed : IsClosed (Complex.HadamardThreeLines.verticalClosedStrip 0 u_strip) :=
              isClosed_Icc.preimage Complex.continuous_re
            exact h_closed.closure_subset_iff.mpr (fun z hz => ⟨hz.1.le, hz.2.le⟩) hw
          refine DifferentiableOn.diffContOnCl ?_
          intro w hw
          have hw_ball : s₀ + (r₁ : ℂ) * Complex.exp w ∈ ball s₀ (2 - θ - η / 2) :=
            closedBall_subset_ball hr₃_lt_R₀ (h_map_strip w (h_cl hw))
          have h_inner_diff : DifferentiableAt ℂ (fun z : ℂ => s₀ + (r₁ : ℂ) * Complex.exp z) w :=
            (differentiableAt_id.cexp.const_mul _).const_add _
          exact ((hL_diff.differentiableAt (isOpen_ball.mem_nhds hw_ball)).comp
            w h_inner_diff).differentiableWithinAt
        have hF_bdd :
            BddAbove ((norm ∘ F) '' Complex.HadamardThreeLines.verticalClosedStrip 0 u_strip) := by
          refine ⟨M₃ * Real.log |s.im|, ?_⟩
          rintro y ⟨w, hw, rfl⟩
          exact h_outer _ (h_map_strip w hw)
        have hF_left : ∀ w ∈ Complex.re ⁻¹' {0}, ‖F w‖ ≤ max M₁ 1 := by
          intro w hw
          have hw_cb : s₀ + (r₁ : ℂ) * Complex.exp w ∈ closedBall s₀ r₁ := by
            rw [mem_closedBall_iff_norm, add_sub_cancel_left, norm_mul, Complex.norm_real,
              Real.norm_eq_abs, abs_of_pos hr₁_pos, Complex.norm_exp]
            simp only [Set.mem_preimage, Set.mem_singleton_iff] at hw
            rw [hw, Real.exp_zero, mul_one]
          exact (h_inner _ hw_cb).trans (le_max_left _ _)
        have h_log_tail_ge1 : 1 ≤ M₃ * Real.log |s.im| := by
          have h_ex : Real.exp (1 / M₃) ≤ |s.im| := (le_max_right 6 _).trans him_gt.le
          have h_log : 1 / M₃ ≤ Real.log |s.im| := by
            have := Real.log_le_log (Real.exp_pos _) h_ex
            rwa [Real.log_exp] at this
          calc 1 = M₃ * (1 / M₃) := (mul_div_cancel₀ 1 hM₃_pos.ne').symm
            _ ≤ M₃ * Real.log |s.im| := mul_le_mul_of_nonneg_left h_log hM₃_pos.le
        have hF_right : ∀ w ∈ Complex.re ⁻¹' {u_strip}, ‖F w‖ ≤ M₃ * Real.log |s.im| := by
          intro w hw
          have hw_re : w.re = u_strip := hw
          exact h_outer _ (h_map_strip w ⟨hw_re.symm ▸ hu_pos.le, hw_re.le⟩)
        set w_s : ℂ := (Real.log (r_s / r₁) : ℂ) + (Real.pi : ℂ) * I
        have hw_s_re : w_s.re = Real.log (r_s / r₁) := by simp [w_s]
        have h_rs_gt1 : 1 < r_s / r₁ := (one_lt_div hr₁_pos).mpr hr_lo
        have h_rs_le_r3 : r_s / r₁ ≤ r₃ / r₁ :=
          div_le_div_of_nonneg_right (hr_hi.trans hr₂max_lt_r₃.le) hr₁_pos.le
        have hw_s_mem : w_s ∈ Complex.HadamardThreeLines.verticalClosedStrip 0 u_strip := by
          refine ⟨?_, ?_⟩
          · rw [hw_s_re]; exact (Real.log_pos h_rs_gt1).le
          · rw [hw_s_re]; exact Real.log_le_log (by positivity) h_rs_le_r3
        have hFs : F w_s = logZ s := by
          dsimp [F]
          congr 1
          have hexp_ws : Complex.exp w_s = - ((r_s / r₁ : ℝ) : ℂ) := by
            dsimp [w_s]
            rw [Complex.exp_add, Complex.exp_pi_mul_I, mul_neg_one, ← Complex.ofReal_exp,
              Real.exp_log (div_pos (by linarith) hr₁_pos)]
          rw [hexp_ws, mul_neg, ← Complex.ofReal_mul, mul_div_cancel₀ r_s hr₁_pos.ne']
          apply Complex.ext <;> simp [s₀, r_s]
        have h_htl := Complex.HadamardThreeLines.norm_le_interp_of_mem_verticalClosedStrip'
          hu_pos hw_s_mem hF_diff hF_bdd hF_left hF_right
        rw [hFs] at h_htl
        set β : ℝ := (w_s.re - 0) / (u_strip - 0)
        have hβ0 : 0 ≤ β := by
          dsimp [β]; rw [sub_zero, sub_zero]
          exact div_nonneg hw_s_mem.1 hu_pos.le
        have hβ_le_α : β ≤ α := by
          dsimp [β, α]; rw [sub_zero, sub_zero, hw_s_re]
          exact div_le_div_of_nonneg_right
            (Real.log_le_log (by positivity)
              (div_le_div_of_nonneg_right hr_hi hr₁_pos.le)) hu_pos.le
        have h_one_sub_le : (max M₁ 1) ^ (1 - β) ≤ max M₁ 1 := by
          have hge1 : 1 ≤ max M₁ 1 := le_max_right _ _
          have h1mβ : 1 - β ≤ 1 := by linarith
          calc (max M₁ 1) ^ (1 - β) ≤ (max M₁ 1) ^ (1 : ℝ) :=
                Real.rpow_le_rpow_of_exponent_le hge1 h1mβ
            _ = max M₁ 1 := Real.rpow_one _
        have h_right_rpow : (M₃ * Real.log |s.im|) ^ β ≤ (M₃ * Real.log |s.im|) ^ α :=
          Real.rpow_le_rpow_of_exponent_le h_log_tail_ge1 hβ_le_α
        have h_logZ_le : ‖logZ s‖ ≤ A_coef * (Real.log |s.im|) ^ α := by
          calc ‖logZ s‖
              ≤ (max M₁ 1) ^ (1 - β) * (M₃ * Real.log |s.im|) ^ β := by
                simpa [β] using h_htl
            _ ≤ max M₁ 1 * (M₃ * Real.log |s.im|) ^ α :=
                mul_le_mul h_one_sub_le h_right_rpow
                  (Real.rpow_nonneg (by positivity) _) (by positivity)
            _ = A_coef * (Real.log |s.im|) ^ α := by
                have hlog_nn : 0 ≤ Real.log |s.im| := (Real.log_pos (by linarith)).le
                rw [Real.mul_rpow hM₃_pos.le hlog_nn]
                dsimp [A_coef]; ring
        have h_log_im_nn : 0 ≤ Real.log |s.im| := (Real.log_pos (by linarith)).le
        have h_lin : ‖logZ s‖ ≤ eps * Real.log |s.im| + B_sub :=
          h_logZ_le.trans (h_sublin (Real.log |s.im|) h_log_im_nn)
        have hexp_s : Complex.exp (logZ s) = riemannZeta s := by
          have hs_ball : s ∈ ball s₀ (2 - θ - η / 2) :=
            closedBall_subset_ball hr₃_lt_R₀ (by
              rw [mem_closedBall_iff_norm]
              have hsub : s - s₀ = ((s.re - 2 : ℝ) : ℂ) := by apply Complex.ext <;> simp [s₀]
              rw [hsub, Complex.norm_real, Real.norm_eq_abs, abs_le]
              dsimp [r₃, η] at *; constructor <;> linarith)
          exact h_exp_eq s hs_ball
        have him_pos : 0 < |s.im| := by linarith
        have h_inv_norm : ‖zetaInv s‖ ≤ Real.exp B_sub * |s.im| ^ eps := by
          have hz_eq : zetaInv s = (riemannZeta s)⁻¹ := by simp [zetaInv, hs_ne1]
          rw [hz_eq, norm_inv, ← hexp_s, Complex.norm_exp, ← Real.exp_neg]
          have h_neg_le : -(logZ s).re ≤ ‖logZ s‖ := by
            linarith [neg_le_abs (logZ s).re, Complex.abs_re_le_norm (logZ s)]
          calc Real.exp (-(logZ s).re)
              ≤ Real.exp ‖logZ s‖ := Real.exp_le_exp.mpr h_neg_le
            _ ≤ Real.exp (eps * Real.log |s.im| + B_sub) := Real.exp_le_exp.mpr h_lin
            _ = Real.exp B_sub * Real.exp (eps * Real.log |s.im|) := by rw [Real.exp_add, mul_comm]
            _ = Real.exp B_sub * |s.im| ^ eps := by
                rw [mul_comm eps, Real.rpow_def_of_pos him_pos]
        have h_expB_le_C : Real.exp B_sub ≤ C := by
          dsimp [C]
          have h1 := (le_max_left (Real.exp B_sub) (Real.exp M₁)).trans
            (le_max_right (max B_box 0) _) |>.trans (le_max_right 4 _)
          linarith
        have h_im_le : |s.im| ^ eps ≤ (1 + |s.im|) ^ eps :=
          Real.rpow_le_rpow (abs_nonneg _) (by linarith) heps.le
        exact h_inv_norm.trans (mul_le_mul h_expB_le_C h_im_le (by positivity) hC_pos.le)

#print axioms inv_zeta_isBigO_im_of_zero_free

/-- The regularized reciprocal zeta transform, including its removable value at zero. -/
noncomputable def regularizedZetaReciprocal (s : ℂ) : ℂ :=
  dslope zetaInv 1 (1 + s)

@[simp] theorem regularizedZetaReciprocal_zero : regularizedZetaReciprocal 0 = 1 := by
  rw [regularizedZetaReciprocal, add_zero, dslope_same, hasDerivAt_zetaInv_one.deriv]

private theorem regularizedZetaReciprocal_eq_zetaInv_div {s : ℂ} (hs : s ≠ 0) :
    regularizedZetaReciprocal s = zetaInv (1 + s) / s := by
  have h1 : 1 + s ≠ (1 : ℂ) := by
    intro h
    exact hs (add_left_cancel (h.trans (add_zero (1 : ℂ)).symm))
  rw [regularizedZetaReciprocal, dslope_of_ne _ h1, slope_def_field]
  simp [zetaInv]

theorem regularizedZetaReciprocal_eq {s : ℂ} (hs : s ≠ 0) :
    regularizedZetaReciprocal s = 1 / (s * riemannZeta (1 + s)) := by
  have h1 : 1 + s ≠ (1 : ℂ) := by
    intro h
    exact hs (add_left_cancel (h.trans (add_zero (1 : ℂ)).symm))
  rw [regularizedZetaReciprocal_eq_zetaInv_div hs, zetaInv, ite_eq_right h1,
    one_div, mul_inv_rev, div_eq_mul_inv]

theorem differentiableOn_regularizedZetaReciprocal_of_zero_free {θ : ℝ} (hθ_lt_one : θ < 1)
    (hzero : ∀ z : ℂ, θ < z.re → z ≠ 1 → riemannZeta z ≠ 0) :
    DifferentiableOn ℂ regularizedZetaReciprocal {s : ℂ | θ - 1 < s.re} := by
  have hopen : IsOpen {z : ℂ | θ < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hmem : (1 : ℂ) ∈ {z : ℂ | θ < z.re} := by simpa using hθ_lt_one
  have hds :=
    (Complex.differentiableOn_dslope (hopen.mem_nhds hmem)).2
      (differentiableOn_zetaInv_of_zero_free hzero)
  refine hds.comp ((differentiable_id.const_add (1 : ℂ)).differentiableOn) ?_
  intro s hs
  change θ - 1 < s.re at hs
  change θ < (1 + s).re
  rw [Complex.add_re, Complex.one_re]
  linarith

/-- Uniform decay on every closed real strip inside the shifted zero-free half-plane. -/
theorem norm_regularizedZetaReciprocal_le_rpow_of_zero_free {θ σ σ₀ p : ℝ}
    (hθ_half : 1 / 2 ≤ θ) (hθ_lt_one : θ < 1)
    (hzero : ∀ z : ℂ, θ < z.re → z ≠ 1 → riemannZeta z ≠ 0)
    (hσ : θ - 1 < σ) (hp : 0 < p) (hp₁ : p < 1) :
    ∃ C > 0, ∀ s : ℂ, σ ≤ s.re → s.re ≤ σ₀ →
      ‖regularizedZetaReciprocal s‖ ≤ C * (1 + |s.im|) ^ (-p) := by
  obtain ⟨A, hA, hInv⟩ := inv_zeta_isBigO_im_of_zero_free hθ_half hθ_lt_one hzero
    (σ₀ := 1 + σ) (eps := 1 - p) (by linarith) (sub_pos.mpr hp₁)
  let K : Set ℂ := Icc σ σ₀ ×ℂ Icc (-1) 1
  have hK : IsCompact K := isCompact_Icc.reProdIm isCompact_Icc
  have hKsub : K ⊆ {s : ℂ | θ - 1 < s.re} := fun _ hs => hσ.trans_le hs.1.1
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn
    ((differentiableOn_regularizedZetaReciprocal_of_zero_free hθ_lt_one hzero).continuousOn.mono hKsub)
  let C : ℝ := max (2 * A) (max B 0 * (2 : ℝ) ^ p)
  have hCA : 2 * A ≤ C := le_max_left _ _
  have hCB : max B 0 * (2 : ℝ) ^ p ≤ C := le_max_right _ _
  have hC : 0 < C := (show 0 < 2 * A by positivity).trans_le hCA
  refine ⟨C, hC, ?_⟩
  intro s hs hs₀
  have hb : 0 < 1 + |s.im| := by positivity
  have hbpow : 0 ≤ (1 + |s.im|) ^ (-p) := Real.rpow_nonneg hb.le _
  by_cases ht : 1 ≤ |s.im|
  · have him := Complex.abs_im_le_norm s
    have hnorm : 0 < ‖s‖ := by linarith
    have hs_ne : s ≠ 0 := norm_pos_iff.mp hnorm
    have hRe : 1 + σ ≤ (1 + s).re := by
      rw [Complex.add_re, Complex.one_re]
      exact add_le_add_right hs 1
    have hz : ‖zetaInv (1 + s)‖ ≤ A * (1 + |s.im|) ^ (1 - p) := by
      simpa only [Complex.add_im, Complex.one_im, zero_add] using hInv (1 + s) hRe
    rw [regularizedZetaReciprocal_eq_zetaInv_div hs_ne, norm_div]
    apply (div_le_iff₀ hnorm).2
    calc
      ‖zetaInv (1 + s)‖ ≤ A * (1 + |s.im|) ^ (1 - p) := hz
      _ = A * (1 + |s.im|) * (1 + |s.im|) ^ (-p) := by
        rw [sub_eq_add_neg, Real.rpow_add hb, Real.rpow_one, mul_assoc]
      _ ≤ A * (2 * ‖s‖) * (1 + |s.im|) ^ (-p) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (by linarith) hA.le) hbpow
      _ = (2 * A) * (1 + |s.im|) ^ (-p) * ‖s‖ := by ring
      _ ≤ C * (1 + |s.im|) ^ (-p) * ‖s‖ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCA hbpow) hnorm.le
  · have hsk : s ∈ K := ⟨⟨hs, hs₀⟩, abs_le.mp (le_of_not_ge ht)⟩
    have hpow : (2 : ℝ) ^ (-p) ≤ (1 + |s.im|) ^ (-p) :=
      Real.rpow_le_rpow_of_nonpos hb (by linarith [le_of_not_ge ht]) (neg_nonpos.mpr hp.le)
    calc
      ‖regularizedZetaReciprocal s‖ ≤ B := hB s hsk
      _ ≤ max B 0 := le_max_left _ _
      _ = (max B 0 * (2 : ℝ) ^ p) * (2 : ℝ) ^ (-p) := by
        rw [mul_assoc, ← Real.rpow_add (by norm_num : 0 < (2 : ℝ)), add_neg_cancel,
          Real.rpow_zero, mul_one]
      _ ≤ C * (1 + |s.im|) ^ (-p) :=
        mul_le_mul hCB hpow (Real.rpow_nonneg (by norm_num) _) hC.le

#print axioms regularizedZetaReciprocal_zero
#print axioms regularizedZetaReciprocal_eq
#print axioms differentiableOn_regularizedZetaReciprocal_of_zero_free
#print axioms norm_regularizedZetaReciprocal_le_rpow_of_zero_free

end
