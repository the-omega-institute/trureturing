/- GID: D5/S3/Weil/Analytic/NymanFixedRationalScalar
   generality: I
   mirror-B: D5/B/S3/Weil/Analytic/NymanFixedRationalScalar
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The fixed rational scalar growth bound implies the Riemann hypothesis. -/

import D5.S3.Weil.Analytic.NymanShellScale
import D5.S3.Weil.Analytic.NymanFixedRationalKernelLipschitz
import D5.S3.Weil.Analytic.NymanFixedRationalKernelMellin
import D5.S3.Weil.ZetaBridge.RightHalfStripRiemannReduction

/-! The fixed rational scalar growth bound implies the Riemann hypothesis. -/

set_option autoImplicit false
noncomputable section
open Finset Filter Complex ArithmeticFunction
open scoped Topology ArithmeticFunction.Moebius
open NymanFixedRationalKernel NymanShellMellin NymanShellScale

namespace NymanFixedRationalScalar

/-- Exact finite rational statistic supported on the first omitted reciprocal shell. -/
def scalar (N : ℕ) : ℚ :=
    ∑ n∈Ioc N (2*N),(μ n:ℚ)*bRat ((n:ℚ)/(N:ℚ))

/-- Square-root growth with arbitrary positive exponent slack for this single scalar. -/
def ScalarSquareRoot : Prop :=
  ∀ ε : ℝ, 0<ε → ∃ C : ℝ,0≤C ∧ ∀ N : ℕ, 0<N → |(scalar N:ℝ)|≤C*(N:ℝ)^(1/2+ε)

theorem scalar_eq_scaled {N : ℕ} (hN : 0<N) :
    (scalar N:ℂ)=scaled (fun x => (b x:ℂ)) ((N:ℝ)⁻¹) := by
  unfold scalar scaled
  push_cast
  have hNr : (0:ℝ)<N := by positivity
  rw [tsum_eq_sum (s:=Ioc N (2*N))]
  · apply sum_congr rfl
    intro n hn
    have he := congrArg (fun x:ℝ => (x:ℂ)) (bRat_cast ((n:ℚ)/(N:ℚ)))
    push_cast at he
    rw [←div_eq_mul_inv,←he]
  · intro n hn
    have hnot : ((n:ℝ)*(N:ℝ)⁻¹)∉Set.Ioo (1:ℝ) 2 := by
      intro hx
      rw [←div_eq_mul_inv] at hx
      have hn1 := (lt_div_iff₀ hNr).mp hx.1
      have hn2 := (div_lt_iff₀ hNr).mp hx.2
      rw [one_mul] at hn1
      exact hn (mem_Ioc.mpr ⟨by exact_mod_cast hn1,by exact_mod_cast hn2.le⟩)
    simp [b_zero_off _ hnot]

private theorem scaled_small_of_scalar (hS : ScalarSquareRoot)
    (ε : ℝ) (hε : 0<ε) :
    scaled (fun x => (b x:ℂ)) =O[𝓝[>] (0:ℝ)] (fun t => t^(-(1/2+ε:ℝ))) := by
  obtain ⟨C,hC,hCb⟩ := hS ε hε
  obtain ⟨K,hK,hb⟩ := b_lipschitz
  have hW : ∀ x∉Set.Ioo (1:ℝ) 2,(b x:ℂ)=0 := by intro x hx; simp [b_zero_off x hx]
  have hKW : ∀ x y : ℝ,‖(b x:ℂ)-(b y:ℂ)‖≤K*|x-y| := by
    intro x y
    rw [←Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs]
    exact hb x y
  apply Asymptotics.IsBigO.of_bound (C+10*K)
  filter_upwards [self_mem_nhdsWithin,nhdsWithin_le_nhds (Iio_mem_nhds (by norm_num : (0:ℝ)<1))] with t ht ht1
  have ht0 : 0<t := ht
  have htlt : t<1 := ht1
  let N := ⌊t⁻¹⌋₊
  have hinv : (1:ℝ)≤t⁻¹ := (one_le_inv₀ ht0).2 htlt.le
  have hN : 0<N := by exact Nat.le_floor (by simpa using hinv)
  have hNlo : (N:ℝ)≤t⁻¹ := Nat.floor_le (by positivity)
  have hNhi : t⁻¹<(N:ℝ)+1 := Nat.lt_floor_add_one _
  have ht₁ : ((N:ℝ)+1)⁻¹≤t := (inv_le_comm₀ (by positivity) ht0).2 hNhi.le
  have ht₂ : t≤(N:ℝ)⁻¹ := (le_inv_comm₀ ht0 (by positivity)).2 hNlo
  have hdiff := scale_difference hW hK hKW hN ht₁ ht₂
  rw [←scalar_eq_scaled hN] at hdiff
  have hscalar := hCb N hN
  have hpow : (N:ℝ)^(1/2+ε)≤t^(-(1/2+ε:ℝ)) := by
    rw [Real.rpow_neg_eq_inv_rpow]
    exact Real.rpow_le_rpow (by positivity) hNlo (by positivity)
  have hpow1 : 1≤t^(-(1/2+ε:ℝ)) := by
    rw [Real.rpow_neg_eq_inv_rpow]
    exact Real.one_le_rpow hinv (by positivity)
  rw [Real.norm_eq_abs,abs_of_nonneg (by positivity)]
  calc
    _ ≤ ‖scaled (fun x => (b x:ℂ)) t-(scalar N:ℂ)‖+‖(scalar N:ℂ)‖ := by
      have h := norm_add_le (scaled (fun x => (b x:ℂ)) t-(scalar N:ℂ)) (scalar N:ℂ)
      simpa only [sub_add_cancel] using h
    _ ≤ 10*K+C*(N:ℝ)^(1/2+ε) := by
      rw [←Complex.ofReal_ratCast,Complex.norm_real,Real.norm_eq_abs]
      exact add_le_add hdiff hscalar
    _ ≤ (10*K)*t^(-(1/2+ε:ℝ))+C*t^(-(1/2+ε:ℝ)) :=
      add_le_add (by simpa using mul_le_mul_of_nonneg_left hpow1 (by positivity : 0≤10*K))
        (mul_le_mul_of_nonneg_left hpow hC)
    _ = _ := by ring

/-- RH follows from square-root growth, with any positive slack, of one fixed
finite rational statistic. -/
theorem rh_of_scalar (hS : ScalarSquareRoot) : RiemannHypothesis := by
  apply D5.S3.Weil.ZetaBridge.RightHalfStripRiemannReduction.golden_right_half_strip_implies_rh
  intro rho hz hrho hrho1
  have hW : ∀ x∉Set.Ioo (1:ℝ) 2,(b x:ℂ)=0 := by intro x hx; simp [b_zero_off x hx]
  have hh := zero_forces_kernel_zero (continuous_ofReal.comp continuous_b) hW (scaled_small_of_scalar hS)
    hrho hrho1 hz
  exact NymanFixedRationalKernel.mellin_ne_zero (by linarith) hh

end NymanFixedRationalScalar
