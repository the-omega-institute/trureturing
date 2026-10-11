/- GID: D5/S3/Arith/Robin/PrimorialGlobalLaplaceEnvelope
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/PrimorialGlobalLaplaceEnvelope
   mirror-E: none(waiver:analytic-inequality)
   anchors: []
   utility: none
   digest: The literal finite-prime Euler ratio has a global original-profile envelope. -/

import D5.S3.Weil.Mertens.Estimates
import Mathlib.NumberTheory.AbelSummation
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic

/-! The classical cumulative first-Mertens bound and prime correction sum are
reused from the frozen supplier. The actual all-parameter estimate keeps the
endpoint and full derivative mass in its weighted Abel error. All intermediate
statements below are used by the one actual envelope endpoint; none is an
independent classical first-freeze claim. The original profile is defined by
its literal compensated integral, with the nonsingular Ein bridge used in the
proof. This candidate does not assert an actual signed-kernel limit. -/

noncomputable section
set_option autoImplicit false
open Set Filter Finset MeasureTheory
open scoped BigOperators Topology Interval

namespace D5.S3.Arith.Robin.PrimorialGlobalLaplaceEnvelope


def primeCutoff (z : ℝ) : Finset ℕ :=
  (Finset.Ioc 0 ⌊z⌋₊).filter Nat.Prime

private def weightedPrimeSum (z v : ℝ) : ℝ :=
  ∑ p ∈ primeCutoff z,
    (Real.log (p : ℝ) / (p : ℝ)) *
      Real.exp (-v * Real.log (p : ℝ) / Real.log z)

private def primeCoefficient (n : ℕ) : ℝ :=
  if n.Prime then Real.log (n : ℝ) / (n : ℝ) else 0

private theorem prime_filter_Icc (t : ℝ) :
    (Finset.Icc 0 ⌊t⌋₊).filter Nat.Prime = primeCutoff t := by
  ext n
  simp only [primeCutoff, Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ioc]
  constructor
  · rintro ⟨⟨_, hn⟩, hp⟩
    exact ⟨⟨hp.pos, hn⟩, hp⟩
  · rintro ⟨⟨_, hn⟩, hp⟩
    exact ⟨⟨Nat.zero_le n, hn⟩, hp⟩

private theorem primeCoefficient_sum (t : ℝ) :
    (∑ n ∈ Finset.Icc 0 ⌊t⌋₊, primeCoefficient n) =
      ∑ p ∈ primeCutoff t, Real.log (p : ℝ) / (p : ℝ) := by
  unfold primeCoefficient
  rw [← Finset.sum_filter, prime_filter_Icc]

private theorem cumulative_log_weight_bound
    (c : ℕ → ℝ) (hc0 : c 0 = 0) {z K : ℝ} (hz : 1 ≤ z)
    (hA : ∀ t : ℝ, 1 ≤ t →
      |(∑ n ∈ Finset.Icc 0 ⌊t⌋₊, c n) - Real.log t| ≤ K)
    (f f' : ℝ → ℝ)
    (hf : ∀ t ∈ Set.Icc (1 : ℝ) z, HasDerivAt f (f' t) t)
    (hf'cont : ContinuousOn f' (Set.Icc (1 : ℝ) z))
    (hf1 : f 1 = 1)
    (hfnn : ∀ t ∈ Set.Icc (1 : ℝ) z, 0 ≤ f t)
    (hf'np : ∀ t ∈ Set.Icc (1 : ℝ) z, f' t ≤ 0) :
    |(∑ n ∈ Finset.Icc 0 ⌊z⌋₊, f (n : ℝ) * c n) -
      ∫ t in (1 : ℝ)..z, f t * t⁻¹| ≤ K := by
  let A : ℝ → ℝ := fun t => ∑ n ∈ Finset.Icc 0 ⌊t⌋₊, c n
  have ht0 : ∀ t ∈ Set.Icc (1 : ℝ) z, t ≠ 0 := by
    intro t ht
    linarith [ht.1]
  have hfc : ContinuousOn f (Set.Icc (1 : ℝ) z) := by
    intro t ht
    exact (hf t ht).continuousAt.continuousWithinAt
  have hlogc : ContinuousOn Real.log (Set.Icc (1 : ℝ) z) := by
    intro t ht
    exact (Real.continuousAt_log (ht0 t ht)).continuousWithinAt
  have hinvc : ContinuousOn (fun t : ℝ => t⁻¹) (Set.Icc (1 : ℝ) z) := by
    intro t ht
    have htn := ht0 t ht
    fun_prop (disch := assumption)
  have hderiv_eq : ∀ t ∈ Set.Icc (1 : ℝ) z, deriv f t = f' t := by
    intro t ht
    exact (hf t ht).deriv
  have hderivc : ContinuousOn (deriv f) (Set.Icc (1 : ℝ) z) :=
    hf'cont.congr hderiv_eq
  have hfp : IntervalIntegrable f' volume 1 z :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hz).2 hf'cont.integrableOn_Icc
  have hfpA : IntervalIntegrable (fun t => f' t * A t) volume 1 z := by
    apply (intervalIntegrable_iff_integrableOn_Icc_of_le hz).2
    simpa only [A] using
      integrableOn_mul_sum_Icc c (a := (1 : ℝ)) (b := z) zero_le_one
        hf'cont.integrableOn_Icc
  have hfplog : IntervalIntegrable (fun t => f' t * Real.log t) volume 1 z :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hz).2
      (hf'cont.mul hlogc).integrableOn_Icc
  have hfinv : IntervalIntegrable (fun t => f t * t⁻¹) volume 1 z :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hz).2
      (hfc.mul hinvc).integrableOn_Icc
  have hAbel0 := sum_mul_eq_sub_integral_mul₀ c hc0 z
    (fun t ht => (hf t ht).differentiableAt) hderivc.integrableOn_Icc
  rw [← intervalIntegral.integral_of_le hz] at hAbel0
  have hAbel :
      (∑ n ∈ Finset.Icc 0 ⌊z⌋₊, f (n : ℝ) * c n) =
        f z * A z - ∫ t in (1 : ℝ)..z, f' t * A t := by
    rw [hAbel0]
    congr 1
    apply intervalIntegral.integral_congr
    intro t ht
    have hti : t ∈ Set.Icc (1 : ℝ) z := by
      simpa only [Set.uIcc_of_le hz] using ht
    change deriv f t * A t = f' t * A t
    rw [hderiv_eq t hti]
  have hprodder : ∀ t ∈ Set.uIcc (1 : ℝ) z,
      HasDerivAt (fun t => f t * Real.log t)
        (f' t * Real.log t + f t * t⁻¹) t := by
    intro t ht
    have hti : t ∈ Set.Icc (1 : ℝ) z := by
      simpa only [Set.uIcc_of_le hz] using ht
    exact (hf t hti).mul (Real.hasDerivAt_log (ht0 t hti))
  have hprod := intervalIntegral.integral_eq_sub_of_hasDerivAt hprodder
    (hfplog.add hfinv)
  rw [intervalIntegral.integral_add hfplog hfinv] at hprod
  simp only [Real.log_one, mul_zero, sub_zero] at hprod
  have hErrInt :
      (∫ t in (1 : ℝ)..z, f' t * (A t - Real.log t)) =
        (∫ t in (1 : ℝ)..z, f' t * A t) -
          ∫ t in (1 : ℝ)..z, f' t * Real.log t := by
    simp_rw [mul_sub]
    rw [intervalIntegral.integral_sub hfpA hfplog]
  have hErr :
      (∑ n ∈ Finset.Icc 0 ⌊z⌋₊, f (n : ℝ) * c n) -
        (∫ t in (1 : ℝ)..z, f t * t⁻¹) =
      f z * (A z - Real.log z) -
        ∫ t in (1 : ℝ)..z, f' t * (A t - Real.log t) := by
    rw [hAbel, hErrInt, mul_sub]
    linarith [hprod]
  have hFTC : (∫ t in (1 : ℝ)..z, f' t) = f z - f 1 := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt _ hfp
    intro t ht
    apply hf t
    simpa only [Set.uIcc_of_le hz] using ht
  have hErrBd :
      |∫ t in (1 : ℝ)..z, f' t * (A t - Real.log t)| ≤ K * (1 - f z) := by
    calc
      |∫ t in (1 : ℝ)..z, f' t * (A t - Real.log t)| =
          ‖∫ t in (1 : ℝ)..z, f' t * (A t - Real.log t)‖ := by
            rw [Real.norm_eq_abs]
      _ ≤ ∫ t in (1 : ℝ)..z, K * (-f' t) := by
        apply intervalIntegral.norm_integral_le_of_norm_le hz
          (Filter.Eventually.of_forall ?_) (hfp.neg.const_mul K)
        intro t ht
        have hti : t ∈ Set.Icc (1 : ℝ) z := ⟨ht.1.le, ht.2⟩
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonpos (hf'np t hti)]
        have hb : |A t - Real.log t| ≤ K := hA t hti.1
        calc
          (-f' t) * |A t - Real.log t| ≤ (-f' t) * K :=
            mul_le_mul_of_nonneg_left hb (neg_nonneg.mpr (hf'np t hti))
          _ = K * (-f' t) := by ring
      _ = K * (1 - f z) := by
        rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_neg, hFTC, hf1]
        ring
  have hzmem : z ∈ Set.Icc (1 : ℝ) z := ⟨hz, le_rfl⟩
  have hEndpoint : |f z * (A z - Real.log z)| ≤ f z * K := by
    rw [abs_mul, abs_of_nonneg (hfnn z hzmem)]
    exact mul_le_mul_of_nonneg_left (hA z hz) (hfnn z hzmem)
  rw [hErr]
  calc
    |f z * (A z - Real.log z) -
        ∫ t in (1 : ℝ)..z, f' t * (A t - Real.log t)| ≤
      |f z * (A z - Real.log z)| +
        |∫ t in (1 : ℝ)..z, f' t * (A t - Real.log t)| := abs_sub _ _
    _ ≤ f z * K + K * (1 - f z) := add_le_add hEndpoint hErrBd
    _ = K := by ring

private def logWeight (z v t : ℝ) : ℝ :=
  Real.exp (-v * Real.log t / Real.log z)

private def logWeightDeriv (z v t : ℝ) : ℝ :=
  logWeight z v t * ((-v / Real.log z) * t⁻¹)

private theorem hasDerivAt_logWeight (z v : ℝ) {t : ℝ} (ht : t ≠ 0) :
    HasDerivAt (logWeight z v) (logWeightDeriv z v t) t := by
  have h := (((Real.hasDerivAt_log ht).const_mul (-v)).div_const
    (Real.log z)).exp
  change HasDerivAt (fun x : ℝ => Real.exp (-v * Real.log x / Real.log z))
    (Real.exp (-v * Real.log t / Real.log z) * ((-v / Real.log z) * t⁻¹)) t
  convert h using 1 <;> ring

private theorem normalized_log_integral {z v : ℝ} (hz : 1 < z) :
    (1 / Real.log z) * (∫ t in (1 : ℝ)..z, logWeight z v t * t⁻¹) =
      ∫ b in (0 : ℝ)..1, Real.exp (-v * b) := by
  have hL : 0 < Real.log z := Real.log_pos hz
  have hsub := intervalIntegral.integral_comp_mul_deriv
    (f := fun t : ℝ => Real.log t / Real.log z)
    (f' := fun t : ℝ => t⁻¹ / Real.log z)
    (g := fun b : ℝ => Real.exp (-v * b))
    (a := (1 : ℝ)) (b := z)
    (by
      intro t ht
      have hti : t ∈ Set.Icc (1 : ℝ) z := by
        simpa only [Set.uIcc_of_le hz.le] using ht
      have ht0 : t ≠ 0 := by linarith [hti.1]
      exact (Real.hasDerivAt_log ht0).div_const (Real.log z))
    (by
      intro t ht
      have hti : t ∈ Set.Icc (1 : ℝ) z := by
        simpa only [Set.uIcc_of_le hz.le] using ht
      have ht0 : t ≠ 0 := by linarith [hti.1]
      fun_prop (disch := assumption))
    (by fun_prop)
  have hsub' :
      (∫ t in (1 : ℝ)..z,
        ((fun b : ℝ => Real.exp (-v * b)) ∘
          (fun t : ℝ => Real.log t / Real.log z)) t *
            (t⁻¹ / Real.log z)) =
      ∫ b in (0 : ℝ)..1, Real.exp (-v * b) := by
    simpa only [Real.log_one, zero_div, div_self hL.ne'] using hsub
  calc
    (1 / Real.log z) * (∫ t in (1 : ℝ)..z, logWeight z v t * t⁻¹) =
        ∫ t in (1 : ℝ)..z, (1 / Real.log z) * (logWeight z v t * t⁻¹) :=
      (intervalIntegral.integral_const_mul _ _).symm
    _ = ∫ t in (1 : ℝ)..z,
        ((fun b : ℝ => Real.exp (-v * b)) ∘
          (fun t : ℝ => Real.log t / Real.log z)) t *
            (t⁻¹ / Real.log z) := by
      apply intervalIntegral.integral_congr
      intro t ht
      dsimp [logWeight, Function.comp_def]
      have he : -v * Real.log t / Real.log z = -v * (Real.log t / Real.log z) := by
        ring
      rw [he]
      ring
    _ = ∫ b in (0 : ℝ)..1, Real.exp (-v * b) := hsub'

private theorem weighted_prime_laplace_first_mertens {z v : ℝ} (hz : 2 ≤ z) (hv : 0 ≤ v) :
    |(1 / Real.log z) * weightedPrimeSum z v -
      ∫ b in (0 : ℝ)..1, Real.exp (-v * b)| ≤
        (Real.log 4 + 4) / Real.log z := by
  have hz1 : 1 < z := by linarith
  have hL : 0 < Real.log z := Real.log_pos hz1
  have hcum : ∀ t : ℝ, 1 ≤ t →
      |(∑ n ∈ Finset.Icc 0 ⌊t⌋₊, primeCoefficient n) - Real.log t| ≤
        Real.log 4 + 4 := by
    intro t ht
    rw [primeCoefficient_sum]
    exact Mertens.sum_log_prime_div_eq_log ht
  have hw : ∀ t ∈ Set.Icc (1 : ℝ) z,
      HasDerivAt (logWeight z v) (logWeightDeriv z v t) t := by
    intro t ht
    apply hasDerivAt_logWeight
    linarith [ht.1]
  have hwcont : ContinuousOn (logWeight z v) (Set.Icc (1 : ℝ) z) := by
    intro t ht
    exact (hw t ht).continuousAt.continuousWithinAt
  have hinvc : ContinuousOn (fun t : ℝ => t⁻¹) (Set.Icc (1 : ℝ) z) := by
    intro t ht
    have ht0 : t ≠ 0 := by linarith [ht.1]
    fun_prop (disch := assumption)
  have hwdcont : ContinuousOn (logWeightDeriv z v) (Set.Icc (1 : ℝ) z) := by
    exact hwcont.mul (continuousOn_const.mul hinvc)
  have hwnn : ∀ t ∈ Set.Icc (1 : ℝ) z, 0 ≤ logWeight z v t := by
    intro t ht
    exact (Real.exp_pos _).le
  have hwdnp : ∀ t ∈ Set.Icc (1 : ℝ) z, logWeightDeriv z v t ≤ 0 := by
    intro t ht
    exact mul_nonpos_of_nonneg_of_nonpos (hwnn t ht)
      (mul_nonpos_of_nonpos_of_nonneg
        (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hv) hL.le)
        (inv_nonneg.mpr (by linarith [ht.1])))
  have hbound := cumulative_log_weight_bound primeCoefficient
    (by simp [primeCoefficient, Nat.not_prime_zero]) hz1.le hcum
    (logWeight z v) (logWeightDeriv z v) hw hwdcont
    (by simp [logWeight]) hwnn hwdnp
  have hsum :
      (∑ n ∈ Finset.Icc 0 ⌊z⌋₊, logWeight z v (n : ℝ) * primeCoefficient n) =
        weightedPrimeSum z v := by
    unfold weightedPrimeSum
    calc
      (∑ n ∈ Finset.Icc 0 ⌊z⌋₊, logWeight z v (n : ℝ) * primeCoefficient n) =
          ∑ n ∈ Finset.Icc 0 ⌊z⌋₊,
            if n.Prime then
              (Real.log (n : ℝ) / (n : ℝ)) *
                Real.exp (-v * Real.log (n : ℝ) / Real.log z) else 0 := by
        apply Finset.sum_congr rfl
        intro n hn
        by_cases hp : n.Prime <;> simp [primeCoefficient, logWeight, hp, mul_comm]
      _ = ∑ p ∈ primeCutoff z,
          (Real.log (p : ℝ) / (p : ℝ)) *
            Real.exp (-v * Real.log (p : ℝ) / Real.log z) := by
        rw [← Finset.sum_filter, prime_filter_Icc]
  rw [hsum] at hbound
  rw [← normalized_log_integral hz1, ← mul_sub, abs_mul,
    abs_of_nonneg (one_div_nonneg.mpr hL.le)]
  calc
    (1 / Real.log z) *
        |weightedPrimeSum z v - ∫ t in (1 : ℝ)..z, logWeight z v t * t⁻¹| ≤
      (1 / Real.log z) * (Real.log 4 + 4) :=
        mul_le_mul_of_nonneg_left hbound (one_div_nonneg.mpr hL.le)
    _ = (Real.log 4 + 4) / Real.log z := by ring

def localFactor (p : ℕ) (s : ℝ) : ℝ := 1 - (p : ℝ) ^ (-s)

def eulerProduct (S : Finset ℕ) (s : ℝ) : ℝ :=
  ∏ p ∈ S, localFactor p s

def eulerSlope (S : Finset ℕ) (s : ℝ) : ℝ :=
  ∑ p ∈ S, Real.log (p : ℝ) / ((p : ℝ) ^ s - 1)

def scaledRatio (S : Finset ℕ) (L v : ℝ) : ℝ :=
  eulerProduct S (1 + v / L) / eulerProduct S 1

def scaledSlope (S : Finset ℕ) (L v : ℝ) : ℝ :=
  eulerSlope S (1 + v / L) / L

private def reciprocalSlope (S : Finset ℕ) (L v : ℝ) : ℝ :=
  (∑ p ∈ S, Real.log (p : ℝ) / (p : ℝ) ^ (1 + v / L)) / L

private def denominatorBudget (S : Finset ℕ) : ℝ :=
  ∑ p ∈ S, Real.log (p : ℝ) / ((p : ℝ) * ((p : ℝ) - 1))

private theorem prime_cast_one_lt {p : ℕ} (hp : p.Prime) :
    1 < (p : ℝ) := by
  exact_mod_cast hp.one_lt

private theorem prime_cast_pos {p : ℕ} (hp : p.Prime) :
    0 < (p : ℝ) := lt_trans (by norm_num) (prime_cast_one_lt hp)

private theorem localFactor_pos {p : ℕ} (hp : p.Prime) {s : ℝ} (hs : 0 < s) :
    0 < localFactor p s := by
  apply sub_pos.mpr
  exact Real.rpow_lt_one_of_one_lt_of_neg (prime_cast_one_lt hp) (by linarith)

private theorem eulerProduct_pos (S : Finset ℕ)
    (hPrime : ∀ p ∈ S, p.Prime) {s : ℝ} (hs : 0 < s) :
    0 < eulerProduct S s := by
  exact Finset.prod_pos (fun p hp => localFactor_pos (hPrime p hp) hs)

private theorem prime_rpow_sub_one_pos {p : ℕ} (hp : p.Prime)
    {s : ℝ} (hs : 0 < s) : 0 < (p : ℝ) ^ s - 1 := by
  exact sub_pos.mpr (Real.one_lt_rpow (prime_cast_one_lt hp) hs)

private theorem hasDerivAt_localFactor {p : ℕ} (hp : p.Prime) (s : ℝ) :
    HasDerivAt (localFactor p)
      (Real.log (p : ℝ) * (p : ℝ) ^ (-s)) s := by
  have h := ((hasDerivAt_id s).neg.const_rpow (prime_cast_pos hp)).const_sub (1 : ℝ)
  apply h.congr_deriv
  change -(Real.log (p : ℝ) * (-1) * (p : ℝ) ^ (-s)) =
    Real.log (p : ℝ) * (p : ℝ) ^ (-s)
  ring

private theorem localFactor_logarithmic_derivative {p : ℕ} (hp : p.Prime)
    {s : ℝ} (hs : 0 < s) :
    (Real.log (p : ℝ) * (p : ℝ) ^ (-s)) / localFactor p s =
      Real.log (p : ℝ) / ((p : ℝ) ^ s - 1) := by
  have hpow : (p : ℝ) ^ s ≠ 0 := (Real.rpow_pos_of_pos (prime_cast_pos hp) s).ne'
  have hden : (p : ℝ) ^ s - 1 ≠ 0 := (prime_rpow_sub_one_pos hp hs).ne'
  rw [localFactor, Real.rpow_neg (prime_cast_pos hp).le]
  have hfactor : 1 - ((p : ℝ) ^ s)⁻¹ =
      ((p : ℝ) ^ s - 1) / ((p : ℝ) ^ s) := by
    field_simp [hpow]
  rw [hfactor]
  field_simp [hpow, hden]

private theorem hasDerivAt_log_eulerProduct (S : Finset ℕ)
    (hPrime : ∀ p ∈ S, p.Prime) {s : ℝ} (hs : 0 < s) :
    HasDerivAt (fun t : ℝ => Real.log (eulerProduct S t))
      (eulerSlope S s) s := by
  have hdiff : DifferentiableAt ℝ (eulerProduct S) s :=
    (HasDerivAt.fun_finsetProd
      (fun p hp => hasDerivAt_localFactor (hPrime p hp) s)).differentiableAt
  have hdiv : deriv (eulerProduct S) s / eulerProduct S s = eulerSlope S s := by
    change logDeriv (eulerProduct S) s = eulerSlope S s
    unfold eulerProduct
    rw [logDeriv_fun_prod
      (fun p hp => (localFactor_pos (hPrime p hp) hs).ne')
      (fun p hp => (hasDerivAt_localFactor (hPrime p hp) s).differentiableAt)]
    unfold eulerSlope
    apply Finset.sum_congr rfl
    intro p hp
    rw [logDeriv_apply, (hasDerivAt_localFactor (hPrime p hp) s).deriv]
    exact localFactor_logarithmic_derivative (hPrime p hp) hs
  exact (hdiff.hasDerivAt.log (eulerProduct_pos S hPrime hs).ne').congr_deriv hdiv

private theorem hasDerivAt_eulerProduct (S : Finset ℕ)
    (hPrime : ∀ p ∈ S, p.Prime) {s : ℝ} (hs : 0 < s) :
    HasDerivAt (eulerProduct S)
      (eulerProduct S s * eulerSlope S s) s := by
  have hdiff : DifferentiableAt ℝ (eulerProduct S) s :=
    (HasDerivAt.fun_finsetProd
      (fun p hp => hasDerivAt_localFactor (hPrime p hp) s)).differentiableAt
  have hlog := hasDerivAt_log_eulerProduct S hPrime hs
  have heq : deriv (eulerProduct S) s / eulerProduct S s = eulerSlope S s := by
    have h := (hdiff.hasDerivAt.log (eulerProduct_pos S hPrime hs).ne').deriv
    rw [hlog.deriv] at h
    exact h.symm
  apply hdiff.hasDerivAt.congr_deriv
  calc
    deriv (eulerProduct S) s = eulerSlope S s * eulerProduct S s :=
      (div_eq_iff (eulerProduct_pos S hPrime hs).ne').mp heq
    _ = eulerProduct S s * eulerSlope S s := mul_comm _ _

private theorem scaledRatio_pos (S : Finset ℕ)
    (hPrime : ∀ p ∈ S, p.Prime) {L v : ℝ} (hL : 0 < L) (hv : 0 ≤ v) :
    0 < scaledRatio S L v := by
  apply div_pos
  · exact eulerProduct_pos S hPrime (by have := div_nonneg hv hL.le; linarith)
  · exact eulerProduct_pos S hPrime (by norm_num)

private theorem scaledRatio_zero (S : Finset ℕ)
    (hPrime : ∀ p ∈ S, p.Prime) (L : ℝ) : scaledRatio S L 0 = 1 := by
  simp only [scaledRatio, zero_div, add_zero]
  exact div_self (eulerProduct_pos S hPrime (by norm_num)).ne'

private theorem hasDerivAt_scaledRatio (S : Finset ℕ)
    (hPrime : ∀ p ∈ S, p.Prime) {L v : ℝ} (hL : 0 < L) (hv : 0 ≤ v) :
    HasDerivAt (scaledRatio S L)
      (scaledRatio S L v * scaledSlope S L v) v := by
  have hs : 0 < 1 + v / L := by
    have := div_nonneg hv hL.le
    linarith
  have hlin : HasDerivAt (fun w : ℝ => 1 + w / L) (1 / L) v :=
    ((hasDerivAt_id v).div_const L).const_add 1
  have h := ((hasDerivAt_eulerProduct S hPrime hs).comp v hlin).div_const
    (eulerProduct S 1)
  apply h.congr_deriv
  unfold scaledRatio scaledSlope
  ring

private theorem hasDerivAt_log_scaledRatio (S : Finset ℕ)
    (hPrime : ∀ p ∈ S, p.Prime) {L v : ℝ} (hL : 0 < L) (hv : 0 ≤ v) :
    HasDerivAt (fun w : ℝ => Real.log (scaledRatio S L w))
      (scaledSlope S L v) v := by
  have h := (hasDerivAt_scaledRatio S hPrime hL hv).log
    (scaledRatio_pos S hPrime hL hv).ne'
  apply h.congr_deriv
  exact mul_div_cancel_left₀ _ (scaledRatio_pos S hPrime hL hv).ne'

private theorem prime_denominator_replacement_bounds {p : ℕ} (hp : p.Prime)
    {s : ℝ} (hs : 1 ≤ s) :
    0 ≤ Real.log (p : ℝ) / ((p : ℝ) ^ s - 1) -
      Real.log (p : ℝ) / (p : ℝ) ^ s ∧
    Real.log (p : ℝ) / ((p : ℝ) ^ s - 1) -
      Real.log (p : ℝ) / (p : ℝ) ^ s ≤
      Real.log (p : ℝ) / ((p : ℝ) * ((p : ℝ) - 1)) := by
  have hp0 := prime_cast_pos hp
  have hp1 := prime_cast_one_lt hp
  have hs0 : 0 < s := lt_of_lt_of_le (by norm_num) hs
  have hq0 := Real.rpow_pos_of_pos hp0 s
  have hq1 := prime_rpow_sub_one_pos hp hs0
  have hpq : (p : ℝ) ≤ (p : ℝ) ^ s := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hp1.le hs
  have hlog : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg hp1.le
  have heq : Real.log (p : ℝ) / ((p : ℝ) ^ s - 1) -
      Real.log (p : ℝ) / (p : ℝ) ^ s =
      Real.log (p : ℝ) / ((p : ℝ) ^ s * ((p : ℝ) ^ s - 1)) := by
    field_simp [hq0.ne', hq1.ne']
    ring
  rw [heq]
  refine ⟨div_nonneg hlog (mul_pos hq0 hq1).le, ?_⟩
  apply div_le_div_of_nonneg_left hlog (mul_pos hp0 (sub_pos.mpr hp1))
  exact mul_le_mul hpq (sub_le_sub_right hpq 1) (sub_pos.mpr hp1).le hq0.le

private theorem scaledSlope_sub_reciprocal_bounds (S : Finset ℕ)
    (hPrime : ∀ p ∈ S, p.Prime) {L v : ℝ} (hL : 0 < L) (hv : 0 ≤ v) :
    0 ≤ scaledSlope S L v - reciprocalSlope S L v ∧
      scaledSlope S L v - reciprocalSlope S L v ≤ denominatorBudget S / L := by
  have hs : 1 ≤ 1 + v / L := by
    have := div_nonneg hv hL.le
    linarith
  have heq : scaledSlope S L v - reciprocalSlope S L v =
      (∑ p ∈ S,
        (Real.log (p : ℝ) / ((p : ℝ) ^ (1 + v / L) - 1) -
          Real.log (p : ℝ) / (p : ℝ) ^ (1 + v / L))) / L := by
    unfold scaledSlope eulerSlope reciprocalSlope
    rw [Finset.sum_sub_distrib]
    ring
  rw [heq]
  constructor
  · apply div_nonneg _ hL.le
    apply Finset.sum_nonneg
    intro p hp
    exact (prime_denominator_replacement_bounds (hPrime p hp) hs).1
  · apply div_le_div_of_nonneg_right _ hL.le
    apply Finset.sum_le_sum
    intro p hp
    exact (prime_denominator_replacement_bounds (hPrime p hp) hs).2

private theorem reciprocal_prime_term_eq_exp {p : ℕ} (hp : p.Prime) (L v : ℝ) :
    Real.log (p : ℝ) / (p : ℝ) ^ (1 + v / L) =
      (Real.log (p : ℝ) / (p : ℝ)) *
        Real.exp (-v * Real.log (p : ℝ) / L) := by
  rw [Real.rpow_def_of_pos (prime_cast_pos hp)]
  have hexponent : Real.log (p : ℝ) * (1 + v / L) =
      Real.log (p : ℝ) + v * Real.log (p : ℝ) / L := by ring
  rw [hexponent, Real.exp_add, Real.exp_log (prime_cast_pos hp)]
  have hnegative : -v * Real.log (p : ℝ) / L =
      -(v * Real.log (p : ℝ) / L) := by ring
  rw [hnegative, Real.exp_neg]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

private theorem reciprocalSlope_eq_exp_sum (S : Finset ℕ)
    (hPrime : ∀ p ∈ S, p.Prime) (L v : ℝ) :
    reciprocalSlope S L v =
      (∑ p ∈ S, (Real.log (p : ℝ) / (p : ℝ)) *
        Real.exp (-v * Real.log (p : ℝ) / L)) / L := by
  unfold reciprocalSlope
  congr 1
  apply Finset.sum_congr rfl
  intro p hp
  exact reciprocal_prime_term_eq_exp (hPrime p hp) L v

private theorem denominatorBudget_le_MertensE1 (S : Finset ℕ)
    (hPrime : ∀ p ∈ S, p.Prime) : denominatorBudget S ≤ Mertens.E₁ := by
  unfold denominatorBudget
  calc
    (∑ p ∈ S, Real.log (p : ℝ) / ((p : ℝ) * ((p : ℝ) - 1))) =
        ∑ p ∈ S, if p.Prime then
          Real.log (p : ℝ) / ((p : ℝ) * ((p : ℝ) - 1)) else 0 := by
            apply Finset.sum_congr rfl
            intro p hp
            simp only [if_pos (hPrime p hp)]
    _ ≤ Mertens.E₁ :=
      Mertens.E₁.summable.sum_le_tsum S (fun p _ => Mertens.E₁.summand_nonneg p)

def actualEuler (z s : ℝ) : ℝ :=
  eulerProduct (primeCutoff z) s

def actualRatio (z v : ℝ) : ℝ :=
  actualEuler z (1 + v / Real.log z) / actualEuler z 1

private def actualSlope (z v : ℝ) : ℝ :=
  scaledSlope (primeCutoff z) (Real.log z) v

private theorem actual_cutoff_prime (z : ℝ) :
    ∀ p ∈ primeCutoff z, p.Prime := by
  intro p hp
  exact (Finset.mem_filter.mp hp).2

private theorem actual_log_pos {z : ℝ} (hz : 2 ≤ z) : 0 < Real.log z :=
  Real.log_pos (lt_of_lt_of_le (by norm_num) hz)

private theorem actualRatio_pos {z v : ℝ} (hz : 2 ≤ z) (hv : 0 ≤ v) :
    0 < actualRatio z v :=
  scaledRatio_pos _ (actual_cutoff_prime z) (actual_log_pos hz) hv

private theorem hasDerivAt_log_actualRatio {z v : ℝ} (hz : 2 ≤ z) (hv : 0 ≤ v) :
    HasDerivAt (fun w : ℝ => Real.log (actualRatio z w)) (actualSlope z v) v :=
  hasDerivAt_log_scaledRatio _ (actual_cutoff_prime z) (actual_log_pos hz) hv

private theorem actualSlope_first_mertens_bound {z v : ℝ} (hz : 2 ≤ z) (hv : 0 ≤ v) :
    |actualSlope z v - ∫ b in (0 : ℝ)..1, Real.exp (-v * b)| ≤
      (Real.log 4 + 4 + denominatorBudget (primeCutoff z)) /
        Real.log z := by
  let S := primeCutoff z
  let L := Real.log z
  have hL : 0 < L := actual_log_pos hz
  have hcorrection := scaledSlope_sub_reciprocal_bounds S (actual_cutoff_prime z) hL hv
  have hreciprocal : reciprocalSlope S L v =
      (1 / Real.log z) * weightedPrimeSum z v := by
    rw [reciprocalSlope_eq_exp_sum S (actual_cutoff_prime z) L v]
    unfold weightedPrimeSum
    change (∑ p ∈ S, (Real.log (p : ℝ) / (p : ℝ)) *
      Real.exp (-v * Real.log (p : ℝ) / L)) / L =
        (1 / L) * (∑ p ∈ S, (Real.log (p : ℝ) / (p : ℝ)) *
          Real.exp (-v * Real.log (p : ℝ) / L))
    ring
  have hweighted := weighted_prime_laplace_first_mertens hz hv
  change |scaledSlope S L v - ∫ b in (0 : ℝ)..1, Real.exp (-v * b)| ≤
    (Real.log 4 + 4 + denominatorBudget S) / L
  calc
    |scaledSlope S L v - ∫ b in (0 : ℝ)..1, Real.exp (-v * b)| =
        |(scaledSlope S L v - reciprocalSlope S L v) +
          (reciprocalSlope S L v - ∫ b in (0 : ℝ)..1, Real.exp (-v * b))| := by
            congr 1
            ring
    _ ≤ |scaledSlope S L v - reciprocalSlope S L v| +
        |reciprocalSlope S L v - ∫ b in (0 : ℝ)..1, Real.exp (-v * b)| :=
      abs_add_le _ _
    _ ≤ denominatorBudget S / L + (Real.log 4 + 4) / L := by
      apply add_le_add
      · rw [abs_of_nonneg hcorrection.1]
        exact hcorrection.2
      · rw [hreciprocal]
        exact hweighted
    _ = (Real.log 4 + 4 + denominatorBudget S) / L := by ring

private theorem actualSlope_first_mertens_uniform {z v : ℝ} (hz : 2 ≤ z) (hv : 0 ≤ v) :
    |actualSlope z v - ∫ b in (0 : ℝ)..1, Real.exp (-v * b)| ≤
      (Real.log 4 + 4 + Mertens.E₁) / Real.log z := by
  apply (actualSlope_first_mertens_bound hz hv).trans
  apply div_le_div_of_nonneg_right _ (actual_log_pos hz).le
  simpa only [add_comm] using add_le_add_left
    (denominatorBudget_le_MertensE1 _ (actual_cutoff_prime z)) (Real.log 4 + 4)

noncomputable def rate (v : ℝ) : ℝ := ∫ b in (0 : ℝ)..1, Real.exp (-v * b)

private noncomputable def ein (v : ℝ) : ℝ := ∫ w in (0 : ℝ)..v, rate w

private noncomputable def phi (v : ℝ) : ℝ := Real.exp (ein v)

private theorem continuous_rate : Continuous rate := by
  unfold rate
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (by fun_prop) 0 1

private theorem hasDerivAt_ein (v : ℝ) : HasDerivAt ein (rate v) v :=
  (continuous_rate.integral_hasStrictDerivAt 0 v).hasDerivAt

private theorem rate_eq {v : ℝ} (hv : v ≠ 0) :
    rate v = (1 - Real.exp (-v)) / v := by
  unfold rate
  rw [intervalIntegral.integral_comp_mul_left Real.exp (neg_ne_zero.mpr hv)]
  simp only [mul_zero, mul_one, integral_exp, Real.exp_zero, smul_eq_mul]
  field_simp
  ring

private theorem ein_original_integral (v : ℝ) :
    ein v = ∫ b in (0 : ℝ)..1, (1 - Real.exp (-v * b)) / b := by
  by_cases hv : v = 0
  · simp [hv, ein]
  have heq : (∫ b in (0 : ℝ)..1, (1 - Real.exp (-v * b)) / b) =
      ∫ b in (0 : ℝ)..1, v * rate (v * b) := by
    apply intervalIntegral.integral_congr_Ioo_of_le zero_le_one
    intro b hb
    change (1 - Real.exp (-v * b)) / b = v * rate (v * b)
    rw [rate_eq (mul_ne_zero hv (ne_of_gt hb.1))]
    have harg : -(v * b) = -v * b := by ring
    rw [harg]
    field_simp
  rw [heq, intervalIntegral.integral_const_mul]
  simpa [ein, smul_eq_mul] using
    (intervalIntegral.smul_integral_comp_mul_left rate (a := 0) (b := 1) v).symm

theorem rate_le_one {v : ℝ} (hv : 0 ≤ v) : rate v ≤ 1 := by
  have h := intervalIntegral.integral_mono_on (a := (0 : ℝ)) (b := 1)
    (μ := volume) (f := fun b => Real.exp (-v * b)) (g := fun _ => (1 : ℝ)) zero_le_one
    ((show Continuous (fun b : ℝ => Real.exp (-v * b)) by fun_prop).intervalIntegrable 0 1)
    intervalIntegrable_const (fun b hb => ?_)
  · simpa [rate] using h
  · exact (Real.exp_le_one_iff.mpr (by nlinarith [hb.1]))

private theorem ein_le_self {v : ℝ} (hv : 0 ≤ v) : ein v ≤ v := by
  have h := intervalIntegral.integral_mono_on hv
    (continuous_rate.intervalIntegrable 0 v) (intervalIntegrable_const :
      IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume 0 v)
    (fun w hw => rate_le_one hw.1)
  simpa [ein] using h

private theorem rate_le_inv {v : ℝ} (hv : 0 < v) : rate v ≤ 1 / v := by
  rw [rate_eq hv.ne']
  exact div_le_div_of_nonneg_right (by linarith [Real.exp_pos (-v)]) hv.le

private theorem ein_le_one_add_log {v : ℝ} (hv : 1 ≤ v) :
    ein v ≤ 1 + Real.log v := by
  have hsplit := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (continuous_rate.intervalIntegrable 0 1) (continuous_rate.intervalIntegrable 1 v)
  have hcont : ContinuousOn (fun w : ℝ => 1 / w) (Icc 1 v) := by
    apply continuousOn_const.div continuousOn_id
    intro w hw
    exact ne_of_gt (lt_of_lt_of_le zero_lt_one hw.1)
  have hcomp := intervalIntegral.integral_mono_on (μ := volume) hv
    (continuous_rate.intervalIntegrable 1 v) (hcont.intervalIntegrable_of_Icc hv)
    (fun w hw => rate_le_inv (by linarith [hw.1]))
  rw [integral_one_div_of_pos (by norm_num) (by linarith)] at hcomp
  simp only [div_one] at hcomp
  have hfirst := ein_le_self (v := 1) (by norm_num)
  unfold ein at *
  linarith

private theorem phi_linear_envelope {v : ℝ} (hv : 0 ≤ v) :
    phi v ≤ Real.exp 1 * (1 + v) := by
  by_cases hsmall : v ≤ 1
  · have h := Real.exp_le_exp.mpr ((ein_le_self hv).trans hsmall)
    unfold phi
    nlinarith [Real.exp_pos (1 : ℝ)]
  · have h := Real.exp_le_exp.mpr (ein_le_one_add_log (le_of_lt (lt_of_not_ge hsmall)))
    rw [Real.exp_add, Real.exp_log (by linarith : 0 < v)] at h
    unfold phi
    nlinarith [Real.exp_pos (1 : ℝ)]

noncomputable def budget : ℝ := Real.log 4 + 4 + Mertens.E₁

noncomputable def actualPhi (v : ℝ) : ℝ :=
  Real.exp (∫ b in (0 : ℝ)..1, (1 - Real.exp (-v * b)) / b)

theorem hasDerivAt_actualPhi (v : ℝ) :
    HasDerivAt actualPhi (actualPhi v * rate v) v := by
  have heq : actualPhi = phi := by
    funext w
    unfold actualPhi phi
    rw [ein_original_integral]
  rw [heq]
  exact (hasDerivAt_ein v).exp

theorem actualPhi_zero : actualPhi 0 = 1 := by
  simp [actualPhi]

theorem actualPhi_pos (v : ℝ) : 0 < actualPhi v := by
  unfold actualPhi
  exact Real.exp_pos _

theorem actualPhi_linear_envelope {v : ℝ} (hv : 0 ≤ v) :
    actualPhi v ≤ Real.exp 1 * (1 + v) := by
  have heq : actualPhi v = phi v := by
    unfold actualPhi phi
    rw [ein_original_integral]
  rw [heq]
  exact phi_linear_envelope hv

private theorem actual_log_ratio_ein_error {z v : ℝ} (hz : 2 ≤ z) (hv : 0 ≤ v) :
    |Real.log (actualRatio z v) - ein v| ≤ budget * v / Real.log z := by
  let g : ℝ → ℝ := fun w => Real.log (actualRatio z w) - ein w
  have hd (w : ℝ) (hw : 0 ≤ w) :
      HasDerivAt g (actualSlope z w - rate w) w :=
    (hasDerivAt_log_actualRatio hz hw).sub (hasDerivAt_ein w)
  have hdiff : ∀ w ∈ Icc (0 : ℝ) v, DifferentiableAt ℝ g w :=
    fun w hw => (hd w hw.1).differentiableAt
  have hbound : ∀ w ∈ Icc (0 : ℝ) v, ‖deriv g w‖ ≤ budget / Real.log z := by
    intro w hw
    rw [(hd w hw.1).deriv, Real.norm_eq_abs]
    exact actualSlope_first_mertens_uniform hz hw.1
  have h := (convex_Icc (0 : ℝ) v).norm_image_sub_le_of_norm_deriv_le
    hdiff hbound (x := 0) (y := v) ⟨le_rfl, hv⟩ ⟨hv, le_rfl⟩
  have hratio : actualRatio z 0 = 1 := by
    exact scaledRatio_zero (primeCutoff z)
      (fun p hp => (Finset.mem_filter.mp hp).2) (Real.log z)
  have hgzero : g 0 = 0 := by simp [g, hratio, ein]
  rw [hgzero, sub_zero, Real.norm_eq_abs, sub_zero, Real.norm_eq_abs, abs_of_nonneg hv]
    at h
  change |Real.log (actualRatio z v) - ein v| ≤ _ at h
  convert h using 1 <;> ring

private theorem actual_euler_global_phi_envelope {z v : ℝ} (hz : 2 ≤ z) (hv : 0 ≤ v) :
    Real.exp (-(budget * v / Real.log z)) * actualPhi v ≤ actualRatio z v ∧
      actualRatio z v ≤ Real.exp (budget * v / Real.log z) * actualPhi v := by
  have hphi : actualPhi v = phi v := by
    unfold actualPhi phi
    rw [ein_original_integral]
  rw [hphi]
  have h := abs_le.mp (actual_log_ratio_ein_error hz hv)
  have hpos := actualRatio_pos hz hv
  constructor
  · have he := Real.exp_le_exp.mpr (show
        -(budget * v / Real.log z) + ein v ≤ Real.log (actualRatio z v) by linarith)
    simpa [Real.exp_add, Real.exp_log hpos, phi] using he
  · have he := Real.exp_le_exp.mpr (show
        Real.log (actualRatio z v) ≤ budget * v / Real.log z + ein v by linarith)
    simpa [Real.exp_add, Real.exp_log hpos, phi] using he

private theorem actual_euler_global_linear_envelope {z v : ℝ} (hz : 2 ≤ z) (hv : 0 ≤ v) :
    actualRatio z v ≤ Real.exp (budget * v / Real.log z + 1) * (1 + v) := by
  calc
    actualRatio z v ≤ Real.exp (budget * v / Real.log z) * actualPhi v :=
      (actual_euler_global_phi_envelope hz hv).2
    _ ≤ Real.exp (budget * v / Real.log z) * (Real.exp 1 * (1 + v)) :=
      mul_le_mul_of_nonneg_left (by
        have hphi : actualPhi v = phi v := by
          unfold actualPhi phi
          rw [ein_original_integral]
        rw [hphi]
        exact phi_linear_envelope hv) (Real.exp_pos _).le
    _ = Real.exp (budget * v / Real.log z + 1) * (1 + v) := by
      rw [Real.exp_add]
      ring

/-- For every actual cutoff z ≥ 2 and every v ≥ 0, the finite Euler ratio
is bounded above and below by the original integral profile, and has a paid
linear profile tail with the same explicit all-parameter error budget. -/
theorem result {z v : ℝ} (hz : 2 ≤ z) (hv : 0 ≤ v) :
    (Real.exp (-(budget * v / Real.log z)) * actualPhi v ≤ actualRatio z v ∧
      actualRatio z v ≤ Real.exp (budget * v / Real.log z) * actualPhi v) ∧
      actualRatio z v ≤ Real.exp (budget * v / Real.log z + 1) * (1 + v) := by
  exact ⟨actual_euler_global_phi_envelope hz hv,
    actual_euler_global_linear_envelope hz hv⟩

end D5.S3.Arith.Robin.PrimorialGlobalLaplaceEnvelope
