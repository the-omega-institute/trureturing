/- GID: D5/S3/Analytic/PolynomialReciprocalBounds
   generality: G
   mirror-B: D5/B/S3/Analytic/PolynomialReciprocalBounds
   mirror-E: none(waiver:analytic-estimate)
   anchors: []
   utility: none
   digest: Reciprocal polynomial quadrature in integral function norms using the complex polynomial L2 derivative bound. -/

import D5.S3.Analytic.SignedReciprocalQuadrature
import D5.S3.Analytic.PolynomialL2Derivative
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.Tactic

noncomputable section
open MeasureTheory Polynomial Set Filter
open scoped Topology Interval BigOperators ComplexConjugate
namespace D5.S3.Analytic.PolynomialReciprocalBounds
open D5.S3.Analytic.SignedReciprocalQuadrature

def value (F : ℂ[X]) (t : ℝ) : ℂ := F.eval (t : ℂ)
def energy (F : ℂ[X]) : ℝ := ∫ t in (0:ℝ)..1, ‖value F t‖^2
def ltwo (F : ℂ[X]) : ℝ := Real.sqrt (energy F)
def mixed (F G : ℂ[X]) (t : ℝ) : ℝ := (value F t * conj (value G t)).re
def mixedDeriv (F G : ℂ[X]) (t : ℝ) : ℝ :=
  (value F.derivative t * conj (value G t) + value F t * conj (value G.derivative t)).re

@[fun_prop] lemma value_continuous (F : ℂ[X]) : Continuous (value F) :=
  F.continuous.comp Complex.continuous_ofReal
lemma energy_nonneg (F : ℂ[X]) : 0 ≤ energy F :=
  intervalIntegral.integral_nonneg_of_forall (by norm_num) (fun _ => sq_nonneg _)
lemma ltwo_nonneg (F : ℂ[X]) : 0 ≤ ltwo F := Real.sqrt_nonneg _
lemma ltwo_sq (F : ℂ[X]) : ltwo F ^ 2 = energy F := Real.sq_sqrt (energy_nonneg F)

lemma mixed_self (F : ℂ[X]) (t : ℝ) : mixed F F t = ‖value F t‖^2 := by
  simp only [mixed, Complex.mul_conj, Complex.ofReal_re, Complex.sq_norm]

private lemma eval_conjugate (G : ℂ[X]) (t : ℝ) :
    (G.map (starRingEnd ℂ)).eval (t : ℂ) = conj (value G t) := by
  simpa only [value, Complex.conj_ofReal] using
    (Polynomial.eval_map_apply (p := G) (starRingEnd ℂ) (t : ℂ))

@[fun_prop] lemma mixed_continuous (F G : ℂ[X]) : Continuous (mixed F G) := by
  unfold mixed
  exact Complex.continuous_re.comp
    ((value_continuous F).mul (Complex.continuous_conj.comp (value_continuous G)))
@[fun_prop] lemma mixedDeriv_continuous (F G : ℂ[X]) : Continuous (mixedDeriv F G) := by
  unfold mixedDeriv
  fun_prop

private lemma mixed_hasDerivAt (F G : ℂ[X]) (t : ℝ) :
    HasDerivAt (mixed F G) (mixedDeriv F G t) t := by
  let H : ℂ[X] := F * G.map (starRingEnd ℂ)
  have hd := (H.hasDerivAt (t:ℂ)).real_of_complex
  convert hd using 1
  · funext s
    simp only [H, mixed, value, eval_mul, eval_conjugate]
  · simp only [H, Polynomial.derivative_mul, Polynomial.derivative_map,
      eval_add, eval_mul, eval_conjugate, mixedDeriv, value]

/-- Cauchy--Schwarz on [0,1], from pinned Mathlib Hölder, including zero norms. -/
private lemma integral_product_norm_le (F G : ℂ[X]) :
    (∫ t in (0:ℝ)..1, ‖value F t‖ * ‖value G t‖) ≤ ltwo F * ltwo G := by
  let μ := volume.restrict (Ioc (0:ℝ) 1)
  have mem (P : ℂ[X]) : MemLp (fun t => ‖value P t‖) (ENNReal.ofReal 2) μ := by
    obtain ⟨C,hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
      (value_continuous P).continuousOn
    apply MemLp.of_bound ((value_continuous P).norm.aestronglyMeasurable) C
    apply (ae_restrict_iff' measurableSet_Ioc).2
    exact ae_of_all _ fun t ht => by
      simpa only [norm_norm] using hC t ⟨ht.1.le,ht.2⟩
  have hh := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
    (μ := μ) (ae_of_all _ fun _ => norm_nonneg _)
    (ae_of_all _ fun _ => norm_nonneg _) (mem F) (mem G)
  simpa only [ltwo, energy, intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1),
    μ, Real.rpow_two, ← Real.sqrt_eq_rpow] using hh

private lemma derivative_ltwo_le {d : ℕ} (hd : 1 ≤ d) (F : ℂ[X]) (hF : F.natDegree < d) :
    ltwo F.derivative ≤ (d:ℝ)^2 * ltwo F := by
  have he := D5.S3.Analytic.PolynomialL2Derivative.complex_polynomial_derivative_l2 d hd F hF
  change energy F.derivative ≤ (d:ℝ)^4 * energy F at he
  have hs := Real.sqrt_le_sqrt he
  calc
    ltwo F.derivative ≤ Real.sqrt ((d:ℝ)^4 * energy F) := hs
    _ = (d:ℝ)^2 * ltwo F := by
      change Real.sqrt ((d:ℝ)^4 * energy F) = (d:ℝ)^2 * Real.sqrt (energy F)
      rw [Real.sqrt_mul (by positivity), show (d:ℝ)^4 = ((d:ℝ)^2)^2 by ring,
        Real.sqrt_sq (sq_nonneg _)]

private lemma mixed_abs_le (F G : ℂ[X]) (t : ℝ) :
    |mixed F G t| ≤ ‖value F t‖ * ‖value G t‖ := by
  simpa only [mixed, norm_mul, Complex.norm_conj] using
    Complex.abs_re_le_norm (value F t * conj (value G t))

private lemma mixedDeriv_abs_le (F G : ℂ[X]) (t : ℝ) :
    |mixedDeriv F G t| ≤ ‖value F.derivative t‖*‖value G t‖ +
      ‖value F t‖*‖value G.derivative t‖ := by
  calc
    _ ≤ ‖value F.derivative t * conj (value G t) + value F t * conj (value G.derivative t)‖ :=
      Complex.abs_re_le_norm _
    _ ≤ _ := by
      simpa only [norm_mul, Complex.norm_conj] using
        (norm_add_le (value F.derivative t * conj (value G t))
          (value F t * conj (value G.derivative t)))

private lemma integral_mixed_abs_le (F G : ℂ[X]) :
    (∫ t in (0:ℝ)..1, |mixed F G t|) ≤ ltwo F * ltwo G := by
  refine (intervalIntegral.integral_mono_on (μ := volume) (by norm_num)
    ((mixed_continuous F G).abs.intervalIntegrable 0 1)
    (((value_continuous F).norm.mul (value_continuous G).norm).intervalIntegrable 0 1)
    (fun t _ => mixed_abs_le F G t)).trans (integral_product_norm_le F G)

private lemma integral_mixedDeriv_abs_le {d : ℕ} (hd : 1 ≤ d)
    (F G : ℂ[X]) (hF : F.natDegree < d) (hG : G.natDegree < d) :
    (∫ t in (0:ℝ)..1, |mixedDeriv F G t|) ≤ 2*(d:ℝ)^2 * (ltwo F * ltwo G) := by
  have hmono := intervalIntegral.integral_mono_on (μ := volume) (by norm_num : (0:ℝ) ≤ 1)
    ((mixedDeriv_continuous F G).abs.intervalIntegrable 0 1)
    ((((value_continuous F.derivative).norm.mul (value_continuous G).norm).add
      ((value_continuous F).norm.mul (value_continuous G.derivative).norm)).intervalIntegrable 0 1)
    (fun t _ => mixedDeriv_abs_le F G t)
  simp only [Pi.add_apply, Pi.mul_apply] at hmono
  have hi1 : IntervalIntegrable (fun t : ℝ => ‖value F.derivative t‖*‖value G t‖)
      volume 0 1 :=
    (((value_continuous F.derivative).norm.mul (value_continuous G).norm).intervalIntegrable 0 1)
  have hi2 : IntervalIntegrable (fun t : ℝ => ‖value F t‖*‖value G.derivative t‖)
      volume 0 1 :=
    (((value_continuous F).norm.mul (value_continuous G.derivative).norm).intervalIntegrable 0 1)
  rw [intervalIntegral.integral_add hi1 hi2] at hmono
  have h1 := (integral_product_norm_le F.derivative G).trans
    (mul_le_mul_of_nonneg_right (derivative_ltwo_le hd F hF) (ltwo_nonneg G))
  have h2 := (integral_product_norm_le F G.derivative).trans
    (mul_le_mul_of_nonneg_left (derivative_ltwo_le hd G hG) (ltwo_nonneg F))
  nlinarith only [hmono,h1,h2]

/-- The exact 4d² variation allowance, in integral function norms. -/
theorem mixed_variation_le {d : ℕ} (hd : 1 ≤ d)
    (F G : ℂ[X]) (hF : F.natDegree < d) (hG : G.natDegree < d) :
    variation (mixed F G) (mixedDeriv F G) ≤ 4*(d:ℝ)^2*(ltwo F*ltwo G) := by
  have hdR : (1:ℝ) ≤ d := by exact_mod_cast hd
  have hm : variation (mixed F G) (mixedDeriv F G) ≤
      2*(∫ t in (0:ℝ)..1, |mixed F G t|) + ∫ t in (0:ℝ)..1, |mixedDeriv F G t| := by
    unfold variation variationDensity
    have hc1 := (mixed_continuous F G).abs
    have hc2 := (mixedDeriv_continuous F G).abs
    have hmono := intervalIntegral.integral_mono_on (μ := volume) (by norm_num : (0:ℝ) ≤ 1)
      ((by fun_prop : Continuous (fun t => 2*t*|mixed F G t| + t^2*|mixedDeriv F G t|)).intervalIntegrable 0 1)
      ((by fun_prop : Continuous (fun t : ℝ => 2*|mixed F G t|+|mixedDeriv F G t|)).intervalIntegrable 0 1)
      (fun t ht => by
        have ht2 : t^2 ≤ 1 := by nlinarith [ht.1, ht.2]
        have ha := mul_le_mul_of_nonneg_right ht.2 (abs_nonneg (mixed F G t))
        have hb := mul_le_mul_of_nonneg_right ht2 (abs_nonneg (mixedDeriv F G t))
        nlinarith only [ha,hb])
    simpa only [intervalIntegral.integral_add
      ((by fun_prop : Continuous (fun t : ℝ => 2*|mixed F G t|)).intervalIntegrable 0 1)
      (hc2.intervalIntegrable 0 1), intervalIntegral.integral_const_mul] using hmono
  have ha := integral_mixed_abs_le F G
  have hb := integral_mixedDeriv_abs_le hd F G hF hG
  have hJ := mul_nonneg (ltwo_nonneg F) (ltwo_nonneg G)
  have hd2 : 1 ≤ (d:ℝ)^2 := by nlinarith
  have hex := mul_nonneg (sub_nonneg.mpr hd2) hJ
  nlinarith only [hm,ha,hb,hex]

def tailEnergy (N : ℕ) (F : ℂ[X]) : ℝ :=
  ∑' j : ℕ, ‖value F ((N:ℝ)/(N+j+1 : ℕ))‖^2 / ((N+j+1 : ℕ):ℝ)^2

lemma square_sample_summable {N : ℕ} (hN : 0 < N) (F : ℂ[X]) :
    Summable (fun j : ℕ => ‖value F ((N:ℝ)/(N+j+1 : ℕ))‖^2 / ((N+j+1 : ℕ):ℝ)^2) := by
  simpa only [weight,mixed_self] using sample_summable hN (mixed_continuous F F)

/-- Ordinary reciprocal quadrature for the squared norm of any complex polynomial. -/
theorem polynomial_quadrature {d N : ℕ} (hd : 1 ≤ d) (hN : 0 < N)
    (F : ℂ[X]) (hF : F.natDegree < d) :
    |(N:ℝ)*tailEnergy N F-energy F| ≤ 4*(d:ℝ)^2/(N:ℝ)*energy F := by
  have hNR : (0:ℝ) < N := by exact_mod_cast hN
  have hq := (right_endpoint_quadrature hN (mixed_continuous F F)
    (mixedDeriv_continuous F F) (fun t _ => mixed_hasDerivAt F F t)).2
  have hv := mixed_variation_le hd F F hF hF
  have hFF : ltwo F*ltwo F = energy F := by nlinarith only [ltwo_sq F]
  rw [hFF] at hv
  have hi : (∫ t in (0:ℝ)..1, mixed F F t) = energy F := by simp only [mixed_self,energy]
  rw [hi] at hq
  have hh := mul_le_mul_of_nonneg_left (hq.trans
    (div_le_div_of_nonneg_right hv (sq_nonneg (N:ℝ)))) hNR.le
  have he : (∑' j : ℕ, weight N (mixed F F) (N+j+1:ℕ)) = tailEnergy N F := by
    simp only [weight,mixed_self,tailEnergy]
  rw [he] at hh
  have habs : (N:ℝ)*|tailEnergy N F-energy F/(N:ℝ)| =
      |(N:ℝ)*tailEnergy N F-energy F| := by
    calc
      _ = |(N:ℝ)*(tailEnergy N F-energy F/(N:ℝ))| := by
        rw [abs_mul, abs_of_pos hNR]
      _ = _ := by
        congr 1
        field_simp [hNR.ne']
  rw [habs] at hh
  convert hh using 1
  field_simp [hNR.ne']
  <;> ring

/-- Signed reciprocal estimate with arbitrary bounded prefix sums, in function norm. -/
theorem polynomial_signed_weighted {d N : ℕ} (hd : 1 ≤ d) (hN : 0 < N)
    (F G : ℂ[X]) (hF : F.natDegree < d) (hG : G.natDegree < d)
    {x : ℕ → ℝ} {D : ℝ} (hD : 0 ≤ D)
    (hb : ∀ k, |∑ j ∈ Finset.range k, x j| ≤ D) :
    Summable (fun j : ℕ => x j * weight N (mixed F G) (N+j+1 : ℕ)) ∧
      |(N:ℝ)*(∑' j : ℕ, x j * weight N (mixed F G) (N+j+1 : ℕ))| ≤
        4*(d:ℝ)^2*D/(N:ℝ)*(ltwo F*ltwo G) := by
  have hNR : (0:ℝ) < N := by exact_mod_cast hN
  have ha := signed_weighted_reciprocal hN (mixed_continuous F G)
    (mixedDeriv_continuous F G) (fun t _ => mixed_hasDerivAt F G t) hD hb
  refine ⟨ha.1, ?_⟩
  rw [abs_mul, abs_of_pos hNR]
  have hv := mul_le_mul_of_nonneg_left (mixed_variation_le hd F G hF hG) hD
  have hh := mul_le_mul_of_nonneg_left
    (ha.2.trans (div_le_div_of_nonneg_right hv (sq_nonneg (N:ℝ)))) hNR.le
  convert hh using 1
  field_simp [hNR.ne']
  <;> ring

end D5.S3.Analytic.PolynomialReciprocalBounds
