/- GID: D5/S3/Arith/Robin/SingletonPrimeInsertionNegativeRegime
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/SingletonPrimeInsertionNegativeRegime
   mirror-E: none(waiver:analytic-inequality)
   anchors: []
   utility: none
   digest: Every increasing singleton prime insertion except (2,3) has a strictly negative complete first Laplace difference. -/

import D5.S3.Arith.Robin.PrimorialFirstOrderConcentrationCounterexample
import Mathlib.MeasureTheory.Integral.Bochner.Set

noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory
open scoped Topology

namespace D5.S3.Arith.Robin.SingletonPrimeInsertionNegativeRegime

open D5.S3.Arith.Robin.PrimorialFirstOrderConcentrationCounterexample
open D5.S3.Arith.Robin.PrimorialGlobalLaplaceEnvelope

/-- The original finite Euler product interface at the common clock log p. -/
def clockRatio (q p : ℕ) (v : ℝ) : ℝ :=
  scaledRatio {q} (Real.log p) v

def baseNumerator (q p : ℕ) (v : ℝ) : ℝ :=
  clockRatio q p v - 1 - scaledSlope {q} (Real.log p) 0 * v

def insertedNumerator (q p : ℕ) (v : ℝ) : ℝ :=
  scaledRatio {q, p} (Real.log p) v - 1 - scaledSlope {q, p} (Real.log p) 0 * v

def baseIntegral (q p : ℕ) (σ : ℝ) : ℝ :=
  ∫ v in Ioi (0 : ℝ), Real.exp (-σ * v) * baseNumerator q p v / v ^ 2

def insertedIntegral (q p : ℕ) (σ : ℝ) : ℝ :=
  ∫ v in Ioi (0 : ℝ), Real.exp (-σ * v) * insertedNumerator q p v / v ^ 2

private def kernel (q c v : ℝ) : ℝ :=
  (q - Real.exp (-c * v)) * (1 - Real.exp (-v)) - (q - 1) * v

private def kernelSlope (q c v : ℝ) : ℝ :=
  q * Real.exp (-v) + c * Real.exp (-c * v) -
    (c + 1) * Real.exp (-(c + 1) * v) - (q - 1)

private def kernelCurvature (q c v : ℝ) : ℝ :=
  -q * Real.exp (-v) - c ^ 2 * Real.exp (-c * v) +
    (c + 1) ^ 2 * Real.exp (-(c + 1) * v)

private theorem exp_deriv (k v : ℝ) :
    HasDerivAt (fun w : ℝ => Real.exp (-k * w))
      (-k * Real.exp (-k * v)) v := by
  simpa only [id_eq, mul_one, mul_comm] using
    ((hasDerivAt_id v).const_mul (-k)).exp

private theorem kernel_deriv (q c v : ℝ) :
    HasDerivAt (kernel q c) (kernelSlope q c v) v := by
  have hd := (((exp_deriv c v).const_sub q).mul
    ((exp_deriv 1 v).const_sub 1)).sub ((hasDerivAt_id v).const_mul (q - 1))
  have he : Real.exp (-c * v) * Real.exp (-v) =
      Real.exp (-(c + 1) * v) := by
    rw [← Real.exp_add]
    congr 1
    ring
  convert hd using 1 <;> try rfl
  · funext w
    simp only [kernel, neg_one_mul, id_eq, Pi.mul_apply, Pi.sub_apply]
  · simp only [kernelSlope, neg_one_mul, id_eq, mul_one]
    rw [← he]
    ring

private theorem slope_deriv (q c v : ℝ) :
    HasDerivAt (kernelSlope q c) (kernelCurvature q c v) v := by
  have hd := ((((exp_deriv 1 v).const_mul q).add
    ((exp_deriv c v).const_mul c)).sub
      ((exp_deriv (c + 1) v).const_mul (c + 1))).sub_const (q - 1)
  convert hd using 1 <;> try rfl
  · funext w
    simp only [kernelSlope, neg_one_mul, id_eq, Pi.mul_apply, Pi.sub_apply,
      Pi.add_apply]
  · simp only [kernelCurvature, neg_one_mul, id_eq, mul_one]
    ring

/-- The critical equality is retained: curvature is strictly negative away from zero. -/
private theorem curvature_negative {q c v : ℝ}
    (hq : 1 < q) (hc : 0 < c) (hcrit : 2 * c ≤ q - 1) (hv : 0 < v) :
    kernelCurvature q c v < 0 := by
  have hec : 1 < Real.exp (c * v) := Real.one_lt_exp_iff.mpr (mul_pos hc hv)
  have hev : 1 < Real.exp v := Real.one_lt_exp_iff.mpr hv
  have hbr : (c + 1) ^ 2 - q * Real.exp (c * v) - c ^ 2 * Real.exp v < 0 := by
    have hqmul : q < q * Real.exp (c * v) := by nlinarith
    have hcmul : c ^ 2 ≤ c ^ 2 * Real.exp v := by nlinarith [sq_nonneg c]
    nlinarith
  have h1 : Real.exp (-(c + 1) * v) * Real.exp (c * v) = Real.exp (-v) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have h2 : Real.exp (-(c + 1) * v) * Real.exp v = Real.exp (-c * v) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hf : kernelCurvature q c v = Real.exp (-(c + 1) * v) *
      ((c + 1) ^ 2 - q * Real.exp (c * v) - c ^ 2 * Real.exp v) := by
    unfold kernelCurvature
    rw [mul_sub, mul_sub]
    rw [show Real.exp (-(c + 1) * v) * (q * Real.exp (c * v)) =
      q * Real.exp (-v) by rw [← mul_assoc, mul_comm _ q, mul_assoc, h1]]
    rw [show Real.exp (-(c + 1) * v) * (c ^ 2 * Real.exp v) =
      c ^ 2 * Real.exp (-c * v) by rw [← mul_assoc, mul_comm _ (c ^ 2), mul_assoc, h2]]
    ring
  rw [hf]
  exact mul_neg_of_pos_of_neg (Real.exp_pos _) hbr

private theorem kernel_negative {q c v : ℝ}
    (hq : 1 < q) (hc : 0 < c) (hcrit : 2 * c ≤ q - 1) (hv : 0 < v) :
    kernel q c v < 0 := by
  have hSA : StrictAntiOn (kernelSlope q c) (Ici (0 : ℝ)) := by
    apply strictAntiOn_of_deriv_neg (convex_Ici 0)
      (fun w _ => (slope_deriv q c w).continuousAt.continuousWithinAt)
    intro w hw
    have hwpos : 0 < w := by simpa only [interior_Ici, mem_Ioi] using hw
    rw [(slope_deriv q c w).deriv]
    exact curvature_negative hq hc hcrit hwpos
  have hs0 : kernelSlope q c 0 = 0 := by simp [kernelSlope]; ring
  have hsneg {w : ℝ} (hw : 0 < w) : kernelSlope q c w < 0 := by
    have h := hSA (by simp) hw.le hw
    simpa only [hs0] using h
  have hKA : StrictAntiOn (kernel q c) (Ici (0 : ℝ)) := by
    apply strictAntiOn_of_deriv_neg (convex_Ici 0)
      (fun w _ => (kernel_deriv q c w).continuousAt.continuousWithinAt)
    intro w hw
    rw [(kernel_deriv q c w).deriv]
    exact hsneg (by simpa only [interior_Ici, mem_Ioi] using hw)
  have h := hKA (by simp) hv.le hv
  simpa [kernel] using h

private theorem curvature_bound {q c v : ℝ}
    (hq : 1 < q) (hc : 0 < c) (hv : 0 ≤ v) :
    |kernelCurvature q c v| ≤ q + c ^ 2 + (c + 1) ^ 2 := by
  have he1 : Real.exp (-v) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hec : Real.exp (-c * v) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  have hec1 : Real.exp (-(c + 1) * v) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by nlinarith)
  have h1 : |-q * Real.exp (-v)| ≤ q := by
    rw [abs_mul, abs_neg, abs_of_pos (by linarith : 0 < q), abs_of_pos (Real.exp_pos _)]
    nlinarith
  have h2 : |c ^ 2 * Real.exp (-c * v)| ≤ c ^ 2 := by
    rw [abs_of_nonneg (by positivity)]
    nlinarith [sq_nonneg c]
  have h3 : |(c + 1) ^ 2 * Real.exp (-(c + 1) * v)| ≤ (c + 1) ^ 2 := by
    rw [abs_of_nonneg (by positivity)]
    nlinarith [sq_nonneg (c + 1)]
  have hsub := abs_sub (-q * Real.exp (-v)) (c ^ 2 * Real.exp (-c * v))
  have hadd := abs_add_le (-q * Real.exp (-v) - c ^ 2 * Real.exp (-c * v))
    ((c + 1) ^ 2 * Real.exp (-(c + 1) * v))
  unfold kernelCurvature
  linarith

private theorem kernel_quadratic {q c v : ℝ}
    (hq : 1 < q) (hc : 0 < c) (hv : 0 ≤ v) :
    |kernel q c v| ≤ (q + c ^ 2 + (c + 1) ^ 2) * v ^ 2 / 2 := by
  apply exact_zero_quadratic_bound (kernel q c) (kernelSlope q c)
    (kernelCurvature q c) hv (by simp [kernel])
    (by simp [kernelSlope]; ring)
    (fun w _ => kernel_deriv q c w) (fun w _ => slope_deriv q c w)
  intro w hw
  simpa only [Real.norm_eq_abs] using curvature_bound hq hc hw.1

private theorem integrable_of_quadratic (f : ℝ → ℝ) {C σ : ℝ}
    (hC : 0 ≤ C) (hσ : 0 < σ) (hf : Continuous f)
    (hb : ∀ v : ℝ, 0 ≤ v → |f v| ≤ C * v ^ 2 / 2) :
    IntegrableOn (fun v : ℝ => Real.exp (-σ * v) * f v / v ^ 2) (Ioi 0) := by
  apply signed_integrable_of_quadratic f (C := C) hσ hf.continuousOn
  intro v hv
  calc
    |f v| ≤ C * v ^ 2 / 2 := hb v hv
    _ ≤ C * (1 + v) * v ^ 2 / 2 := by
      apply div_le_div_of_nonneg_right _ (by norm_num : (0 : ℝ) ≤ 2)
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg v)
      simpa only [mul_one] using mul_le_mul_of_nonneg_left
        (show (1 : ℝ) ≤ 1 + v by linarith) hC

private theorem kernel_integrable {q c σ : ℝ}
    (hq : 1 < q) (hc : 0 < c) (hσ : 0 < σ) :
    IntegrableOn (fun v : ℝ => Real.exp (-σ * v) * kernel q c v / v ^ 2) (Ioi 0) := by
  apply integrable_of_quadratic (kernel q c) (C := q + c ^ 2 + (c + 1) ^ 2)
    (by positivity) hσ (by unfold kernel; fun_prop)
  intro v hv
  exact kernel_quadratic hq hc hv

private def singleKernel (c v : ℝ) : ℝ := 1 - Real.exp (-c * v) - c * v

private theorem single_quadratic {c v : ℝ} (hc : 0 < c) (hv : 0 ≤ v) :
    |singleKernel c v| ≤ c ^ 2 * v ^ 2 / 2 := by
  let f' : ℝ → ℝ := fun w => c * Real.exp (-c * w) - c
  let f'' : ℝ → ℝ := fun w => -c ^ 2 * Real.exp (-c * w)
  have hd (w : ℝ) : HasDerivAt (singleKernel c) (f' w) w := by
    have h := ((exp_deriv c w).const_sub 1).sub ((hasDerivAt_id w).const_mul c)
    convert h using 1 <;> try rfl
    dsimp [f']
    ring
  have hdd (w : ℝ) : HasDerivAt f' (f'' w) w := by
    have h := ((exp_deriv c w).const_mul c).sub_const c
    convert h using 1 <;> try rfl
    dsimp [f'']
    ring
  apply exact_zero_quadratic_bound (singleKernel c) f' f'' hv
    (by simp [singleKernel]) (by simp [f']) (fun w _ => hd w) (fun w _ => hdd w)
  intro w hw
  have he : Real.exp (-c * w) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [hw.1])
  dsimp [f'']
  rw [abs_mul, abs_neg, abs_of_nonneg (sq_nonneg c),
    abs_of_pos (Real.exp_pos _)]
  nlinarith [sq_nonneg c]

private theorem ratio_exp {q p : ℕ} (hq : 1 < (q : ℝ)) (hp : 1 < (p : ℝ))
    (v : ℝ) : clockRatio q p v =
      ((q : ℝ) - Real.exp (-(Real.log q / Real.log p) * v)) / ((q : ℝ) - 1) := by
  have hq0 : 0 < (q : ℝ) := by linarith
  have hlog : Real.log (p : ℝ) ≠ 0 := ne_of_gt (Real.log_pos hp)
  have hr : (q : ℝ) ^ (-(1 + v / Real.log p)) =
      Real.exp (-(Real.log q / Real.log p) * v) / (q : ℝ) := by
    rw [Real.rpow_def_of_pos hq0]
    have he : Real.log (q : ℝ) * -(1 + v / Real.log p) =
        -Real.log q + -(Real.log q / Real.log p) * v := by ring
    rw [he, Real.exp_add, Real.exp_neg, Real.exp_log hq0]
    ring
  unfold clockRatio scaledRatio eulerProduct localFactor
  simp only [Finset.prod_singleton]
  rw [hr]
  norm_num only [Real.rpow_neg_one]
  field_simp [hq0.ne', sub_ne_zero.mpr hq.ne']
  <;> ring

private theorem numerator_models {q p : ℕ} (hq : 1 < (q : ℝ))
    (hp : 1 < (p : ℝ)) (hne : q ≠ p) (v : ℝ) :
    baseNumerator q p v = singleKernel (Real.log q / Real.log p) v / ((q : ℝ) - 1) ∧
    insertedNumerator q p v = baseNumerator q p v +
      kernel q (Real.log q / Real.log p) v / (((p : ℝ) - 1) * ((q : ℝ) - 1)) := by
  have hlog : Real.log (p : ℝ) ≠ 0 := ne_of_gt (Real.log_pos hp)
  have hq1 : (q : ℝ) - 1 ≠ 0 := sub_ne_zero.mpr hq.ne'
  have hp1 : (p : ℝ) - 1 ≠ 0 := sub_ne_zero.mpr hp.ne'
  have hnot : q ∉ ({p} : Finset ℕ) := by simpa only [Finset.mem_singleton] using hne
  have hrq := ratio_exp hq hp v
  have hrp := ratio_exp hp hp v
  rw [div_self hlog, neg_one_mul] at hrp
  have hrs : scaledRatio {q, p} (Real.log p) v = clockRatio q p v * clockRatio p p v := by
    unfold clockRatio scaledRatio eulerProduct
    simp only [Finset.prod_insert hnot, Finset.prod_singleton]
    ring
  have hs1 : scaledSlope {q} (Real.log p) 0 =
      (Real.log q / Real.log p) / ((q : ℝ) - 1) := by
    simp only [scaledSlope, eulerSlope, zero_div, add_zero, Finset.sum_singleton,
      Real.rpow_one]
    ring
  have hs2 : scaledSlope {q, p} (Real.log p) 0 =
      scaledSlope {q} (Real.log p) 0 + 1 / ((p : ℝ) - 1) := by
    simp only [scaledSlope, eulerSlope, zero_div, add_zero,
      Finset.sum_insert hnot, Finset.sum_singleton,
      Real.rpow_one]
    field_simp [hlog, hq1, hp1]
    <;> ring
  constructor
  · unfold baseNumerator singleKernel
    rw [hrq, hs1]
    field_simp [hq1]
    <;> ring
  · unfold insertedNumerator baseNumerator kernel
    rw [hrs, hrq, hrp, hs2, hs1]
    field_simp [hq1, hp1]
    <;> ring

private theorem actual_integrable {q p : ℕ} (hq : 1 < (q : ℝ))
    (hp : 1 < (p : ℝ)) (hne : q ≠ p) {σ : ℝ} (hσ : 0 < σ) :
    IntegrableOn (fun v : ℝ => Real.exp (-σ * v) * baseNumerator q p v / v ^ 2) (Ioi 0) ∧
    IntegrableOn (fun v : ℝ => Real.exp (-σ * v) * insertedNumerator q p v / v ^ 2) (Ioi 0) := by
  have hc : 0 < Real.log (q : ℝ) / Real.log p :=
    div_pos (Real.log_pos hq) (Real.log_pos hp)
  have hs := integrable_of_quadratic (singleKernel (Real.log q / Real.log p))
    (sq_nonneg _) hσ (by unfold singleKernel; fun_prop)
    (fun v hv => single_quadratic hc hv)
  have hd := (kernel_integrable hq hc hσ).div_const
    (((p : ℝ) - 1) * ((q : ℝ) - 1))
  have hb : IntegrableOn (fun v : ℝ =>
      Real.exp (-σ * v) * baseNumerator q p v / v ^ 2) (Ioi 0) := by
    apply IntegrableOn.congr_fun (hs.div_const ((q : ℝ) - 1)) _ measurableSet_Ioi
    intro v _
    dsimp only
    rw [(numerator_models hq hp hne v).1]
    ring
  refine ⟨hb, ?_⟩
  apply IntegrableOn.congr_fun (hb.add hd) _ measurableSet_Ioi
  intro v _
  simp only [Pi.add_apply]
  rw [(numerator_models hq hp hne v).2]
  ring

private theorem actual_difference_negative {q p : ℕ}
    (hq : 1 < (q : ℝ)) (hp : 1 < (p : ℝ)) (hne : q ≠ p)
    (hcrit : 2 * (Real.log (q : ℝ) / Real.log p) ≤ (q : ℝ) - 1)
    {σ : ℝ} (hσ : 0 < σ) : insertedIntegral q p σ - baseIntegral q p σ < 0 := by
  let d : ℝ → ℝ := fun v => -(Real.exp (-σ * v) *
    kernel q (Real.log q / Real.log p) v /
    (((p : ℝ) - 1) * ((q : ℝ) - 1)) / v ^ 2)
  have hc : 0 < Real.log (q : ℝ) / Real.log p :=
    div_pos (Real.log_pos hq) (Real.log_pos hp)
  have hi : IntegrableOn d (Ioi 0) := by
    have h := ((kernel_integrable hq hc hσ).div_const
      (((p : ℝ) - 1) * ((q : ℝ) - 1))).neg
    apply IntegrableOn.congr_fun h _ measurableSet_Ioi
    intro v _
    dsimp [d]
    ring
  have hpos {v : ℝ} (hv : 0 < v) : 0 < d v := by
    dsimp [d]
    have hg := kernel_negative hq hc hcrit hv
    have hden : 0 < ((p : ℝ) - 1) * ((q : ℝ) - 1) :=
      mul_pos (sub_pos.mpr hp) (sub_pos.mpr hq)
    exact neg_pos.mpr (div_neg_of_neg_of_pos
      (div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg (Real.exp_pos _) hg) hden)
      (sq_pos_of_pos hv))
  have hnonneg : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))] d :=
    ae_restrict_of_forall_mem measurableSet_Ioi (fun v hv => (hpos hv).le)
  have hsupport : Ioo (0 : ℝ) 1 ⊆ Function.support d ∩ Ioi 0 := by
    intro v hv
    exact ⟨(hpos hv.1).ne', hv.1⟩
  have hvol : 0 < volume (Ioo (0 : ℝ) 1) := by
    rw [Real.volume_Ioo]
    norm_num
  have hdpos : 0 < ∫ v in Ioi 0, d v :=
    (setIntegral_pos_iff_support_of_nonneg_ae hnonneg hi).2
      (lt_of_lt_of_le hvol (measure_mono hsupport))
  have hactual := actual_integrable hq hp hne hσ
  have heq : insertedIntegral q p σ - baseIntegral q p σ =
      -(∫ v in Ioi 0, d v) := by
    unfold insertedIntegral baseIntegral
    rw [← integral_sub hactual.2 hactual.1, ← integral_neg]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro v _
    dsimp only
    rw [(numerator_models hq hp hne v).2]
    dsimp [d]
    ring
  rw [heq]
  linarith

private theorem increasing_pair_critical {q p : ℕ}
    (hq : q.Prime) (hqp : q < p) (hex : q ≠ 2 ∨ p ≠ 3) :
    2 * (Real.log (q : ℝ) / Real.log p) ≤ (q : ℝ) - 1 := by
  have hq2 : 2 ≤ q := hq.two_le
  have hq1 : 1 < (q : ℝ) := by exact_mod_cast (by omega : 1 < q)
  have hp1 : 1 < (p : ℝ) := by exact_mod_cast (by omega : 1 < p)
  have hlp : 0 < Real.log (p : ℝ) := Real.log_pos hp1
  by_cases hqeq : q = 2
  · have hp3 : p ≠ 3 := hex.resolve_left (not_ne_iff.mpr hqeq)
    have hp4 : (4 : ℝ) ≤ p := by exact_mod_cast (by omega : 4 ≤ p)
    have hlog : 2 * Real.log (2 : ℝ) ≤ Real.log (p : ℝ) := by
      have h := Real.log_le_log (by norm_num : (0 : ℝ) < 4) hp4
      have hpow := Real.log_pow (2 : ℝ) 2
      norm_num at hpow
      linarith
    subst q
    norm_num only [Nat.cast_ofNat]
    rw [← mul_div_assoc, div_le_iff₀ hlp]
    linarith
  · have hq3 : (3 : ℝ) ≤ q := by exact_mod_cast (by omega : 3 ≤ q)
    have hlog : Real.log (q : ℝ) < Real.log (p : ℝ) :=
      Real.log_lt_log (by linarith) (by exact_mod_cast hqp)
    have hc : Real.log (q : ℝ) / Real.log p < 1 := by
      rw [div_lt_iff₀ hlp]
      simpa only [one_mul] using hlog
    linarith

/-- Apart from (2,3), every increasing pair of actual primes gives a negative
first compensated Laplace difference at every positive damping. Both literal
singleton/two-prime integrands are absolutely integrable. This does not concern
consecutive full prime cutoffs or the complete Robin pairing. -/
theorem result {q p : ℕ} (hq : q.Prime) (hp : p.Prime)
    (hqp : q < p) (hex : q ≠ 2 ∨ p ≠ 3) :
    ∀ σ : ℝ, 0 < σ →
      IntegrableOn (fun v : ℝ =>
        Real.exp (-σ * v) * baseNumerator q p v / v ^ 2) (Ioi 0) ∧
      IntegrableOn (fun v : ℝ =>
        Real.exp (-σ * v) * insertedNumerator q p v / v ^ 2) (Ioi 0) ∧
      insertedIntegral q p σ - baseIntegral q p σ < 0 := by
  have hqr : 1 < (q : ℝ) := by exact_mod_cast hq.one_lt
  have hpr : 1 < (p : ℝ) := by exact_mod_cast hp.one_lt
  intro σ hσ
  have hi := actual_integrable hqr hpr hqp.ne hσ
  exact ⟨hi.1, hi.2, actual_difference_negative hqr hpr hqp.ne
    (increasing_pair_critical hq hqp hex) hσ⟩

end D5.S3.Arith.Robin.SingletonPrimeInsertionNegativeRegime
