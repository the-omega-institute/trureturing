/- GID: D5/S3/Weil/Analytic/NymanOneSidedInteger
   generality: I
   mirror-B: D5/B/S3/Weil/Analytic/NymanOneSidedInteger
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Integer-scale transfer and a signed rational criterion for RH. -/

import Batteries.Tactic.OpenPrivate
import D5.S3.Weil.Analytic.NymanOneSidedScalar
import D5.S3.Weil.Analytic.NymanFixedScalarUpper

/-! Integer-scale transfer and a signed rational criterion for RH. -/

set_option autoImplicit false
noncomputable section
open Filter Set MeasureTheory Complex
open scoped Topology
open NymanOneSidedScalar NymanShellMellin NymanShellScale
open NymanFixedRationalKernel NymanFixedRationalScalar

open private complex_support complex_lip from D5.S3.Weil.Analytic.NymanOneSidedScalar

namespace NymanOneSidedInteger

/-- The real Möbius shell value at reciprocal integer scale. -/
def integerSample (W : ℝ→ℝ) (N : ℕ) : ℝ :=
  (scaled (Wcomplex W) ((N:ℝ)⁻¹)).re

/-- Adjacent integer scales transfer an upper or lower bound, with only a
uniform additive loss. -/
theorem one_sided_signal_of_integer {W : ℝ→ℝ}
    (hW : ∀ x∉Set.Ioo (1:ℝ) 2,W x=0)
    {K : ℝ} (hK : 0≤K) (hlip : ∀ x y : ℝ,|W x-W y|≤K*|x-y|)
    {β c C : ℝ} (hβ : 0≤β) (hC : 0≤C)
    (hbound : ∀ N : ℕ,0<N → c*integerSample W N≤C*(N:ℝ)^β) :
    ∀ᶠ t in atTop,c*signal W t≤(C+10*|c| * K)*Real.exp (β*t) := by
  refine eventually_atTop.mpr ⟨Real.log 2+1,fun t ht => ?_⟩
  let x := 2*Real.exp (-t)
  have hx0 : 0<x := by dsimp [x]; positivity
  have hlog : 0≤Real.log 2 := Real.log_nonneg (by norm_num)
  have ht0 : 0≤t := by linarith
  have hx1 : x<1 := by
    dsimp [x]
    have hf : 2*Real.exp (-t)=Real.exp (Real.log 2-t) := by
      rw [Real.exp_sub,Real.exp_log (by norm_num : (0:ℝ)<2),Real.exp_neg,div_eq_mul_inv]
    rw [hf,Real.exp_lt_one_iff]
    linarith
  let N := ⌊x⁻¹⌋₊
  have hinv : (1:ℝ)≤x⁻¹ := (one_le_inv₀ hx0).2 hx1.le
  have hN : 0<N := by exact Nat.le_floor (by simpa using hinv)
  have hNlo : (N:ℝ)≤x⁻¹ := Nat.floor_le (by positivity)
  have hNhi : x⁻¹<(N:ℝ)+1 := Nat.lt_floor_add_one _
  have hx₁ : ((N:ℝ)+1)⁻¹≤x := (inv_le_comm₀ (by positivity) hx0).2 hNhi.le
  have hx₂ : x≤(N:ℝ)⁻¹ := (le_inv_comm₀ hx0 (by positivity)).2 hNlo
  have hdiff := scale_difference (complex_support hW) hK (complex_lip hlip) hN hx₁ hx₂
  have hrdiff : |signal W t-integerSample W N|≤10*K := by
    calc
      _ = |(scaled (Wcomplex W) x-scaled (Wcomplex W) ((N:ℝ)⁻¹)).re| := by
        simp only [signal,integerSample,Complex.sub_re,x]
      _ ≤ ‖scaled (Wcomplex W) x-scaled (Wcomplex W) ((N:ℝ)⁻¹)‖ := Complex.abs_re_le_norm _
      _ ≤ _ := hdiff
  have hcdiff : c*(signal W t-integerSample W N)≤10*|c| * K := by
    calc
      _ ≤ |c*(signal W t-integerSample W N)| := le_abs_self _
      _ = |c| * |signal W t-integerSample W N| := abs_mul _ _
      _ ≤ |c| * (10*K) := mul_le_mul_of_nonneg_left hrdiff (abs_nonneg _)
      _ = _ := by ring
  have hNexp : (N:ℝ)≤Real.exp t := by
    apply hNlo.trans
    dsimp [x]
    rw [mul_inv,Real.exp_neg,inv_inv]
    norm_num
    linarith [Real.exp_pos t]
  have hpow : (N:ℝ)^β≤Real.exp (β*t) := by
    have h := Real.rpow_le_rpow (by positivity : (0:ℝ)≤N) hNexp hβ
    rw [Real.rpow_def_of_pos (Real.exp_pos t),Real.log_exp,mul_comm t β] at h
    exact h
  have hexp : 1≤Real.exp (β*t) := Real.one_le_exp (by positivity)
  calc
    _ = c*integerSample W N+c*(signal W t-integerSample W N) := by ring
    _ ≤ C*(N:ℝ)^β+10*|c| * K := add_le_add (hbound N hN) hcdiff
    _ ≤ C*Real.exp (β*t)+(10*|c| * K)*Real.exp (β*t) := add_le_add
      (mul_le_mul_of_nonneg_left hpow hC) (le_mul_of_one_le_right (by positivity) hexp)
    _ = _ := by ring

private theorem zero_re_le_of_integer_bound {W : ℝ→ℝ}
    (hc : Continuous W) (hW : ∀ x∉Set.Ioo (1:ℝ) 2,W x=0)
    {K : ℝ} (hK : 0≤K) (hlip : ∀ x y : ℝ,|W x-W y|≤K*|x-y|)
    {β c C : ℝ} (hβ : 0<β) (hβ1 : β<1) (hc0 : c≠0) (hC : 0≤C)
    (hbound : ∀ N : ℕ,0<N → c*integerSample W N≤C*(N:ℝ)^β)
    {rho : ℂ} (hz : riemannZeta rho=0) (hrho1 : rho.re<1)
    (hker : mellin (Wcomplex W) rho≠0) : rho.re≤β := by
  exact zero_re_le_of_one_sided_signal hc hW hK hlip hβ hβ1 hc0
    (one_sided_signal_of_integer hW hK hlip hβ.le hC hbound) hz hrho1 hker

/-- A bound in either fixed direction, with arbitrarily small exponent slack. -/
def OneSidedSquareRoot (a : ℕ→ℝ) (c : ℝ) : Prop :=
  ∀ ε : ℝ,0<ε → ∃ C : ℝ,0≤C ∧ ∀ N : ℕ,0<N → c*a N≤C*(N:ℝ)^(1/2+ε)

private theorem original_sample {N : ℕ} (hN : 0<N) : integerSample b N=(scalar N:ℝ) := by
  unfold integerSample Wcomplex
  rw [←scalar_eq_scaled hN,←Complex.ofReal_ratCast,Complex.ofReal_re]

/-- Either an upper or a lower square-root bound for the literal original
rational scalar implies RH. -/
private theorem rh_of_one_sided_original {c : ℝ} (hc0 : c≠0)
    (h : OneSidedSquareRoot (fun N => (scalar N:ℝ)) c) : RiemannHypothesis := by
  apply D5.S3.Weil.ZetaBridge.RightHalfStripRiemannReduction.golden_right_half_strip_implies_rh
  intro rho hz hlo hhi
  let β := (1/2+rho.re)/2
  have hβ : 1/2<β := by dsimp [β];linarith
  have hβ1 : β<1 := by dsimp [β];linarith
  obtain ⟨C,hC,hbound⟩ := h (β-1/2) (by linarith)
  obtain ⟨K,hK,hlip⟩ := b_lipschitz
  have hdisc : ∀ N : ℕ,0<N → c*integerSample b N≤C*(N:ℝ)^β := by
    intro N hN
    rw [original_sample hN]
    simpa only [show 1/2+(β-1/2)=β by ring] using hbound N hN
  have hr := zero_re_le_of_integer_bound continuous_b b_zero_off hK hlip
    (by linarith : 0<β) hβ1 hc0 hC hdisc hz hhi
    (NymanFixedRationalKernel.mellin_ne_zero (by linarith : 0<rho.re))
  dsimp [β] at hr
  linarith

/-- For each fixed nonzero multiplier, the one-sided square-root bound with
arbitrary positive slack for the literal rational scalar is equivalent to RH. -/
theorem rh_iff_one_sided_original {c : ℝ} (hc0 : c ≠ 0) :
    RiemannHypothesis ↔ OneSidedSquareRoot (fun N => (scalar N : ℝ)) c := by
  refine ⟨?_, rh_of_one_sided_original hc0⟩
  intro hRH ε hε
  obtain ⟨C, hC, hbound⟩ := NymanFixedScalarUpper.rh_iff_scalar.mp hRH ε hε
  refine ⟨|c| * C, mul_nonneg (abs_nonneg c) hC, ?_⟩
  intro N hN
  calc
    c * (scalar N : ℝ) ≤ |c * (scalar N : ℝ)| := le_abs_self _
    _ = |c| * |(scalar N : ℝ)| := abs_mul _ _
    _ ≤ |c| * (C * (N : ℝ) ^ (1 / 2 + ε)) :=
      mul_le_mul_of_nonneg_left (hbound N hN) (abs_nonneg c)
    _ = (|c| * C) * (N : ℝ) ^ (1 / 2 + ε) := (mul_assoc _ _ _).symm

end NymanOneSidedInteger
