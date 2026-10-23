/- GID: D5/S1/Recurrence/Algebraic/HannaLogarithmicPowerClosure
   generality: I
   mirror-B: D5/B/S1/Recurrence/Algebraic/HannaLogarithmicPowerClosure
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Hanna's logarithmic integer-series closure for every positive pointwise power. -/

import D5.S1.Recurrence.Periodic.IntegralEgfTotientPeriod
import D5.S1.Recurrence.Periodic.ScaledLogColumnPeriodicity
import Mathlib.Algebra.BigOperators.Field

open PowerSeries Finset
open D5.S1.Recurrence.Periodic.StirlingTransformTotientPeriod
namespace D5.S1.Recurrence.Algebraic.HannaLogarithmicPowerClosure

noncomputable def egf {K : Type*} [Field K] [CharZero K] (L : ℕ → K) : PowerSeries K :=
  mk fun n => L n / (n.factorial : K)

noncomputable def logarithmicTransform {K : Type*} [Field K] [CharZero K]
    (L : ℕ → K) : PowerSeries K := (egf L).subst (log K)

def IntegralSeries {K : Type*} [Field K] [CharZero K] (f : PowerSeries K) : Prop :=
  ∀ n, ∃ z : ℤ, coeff n f = (z : K)

/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license. Full text:
docs/reports/log-inverse-suppliers/mathlib-LICENSE.txt.
Authors: Ralf Stephan
Adapted from Mathlib/RingTheory/PowerSeries/Log.lean at
ff5815e8fe1ecf6880c38ea997fb56395951822b for Lean 4.33 and rational coefficients.
The derivative API and the inverse-composition argument use the adopted pin's APIs.
Retire these inverse leaves when our adopted Mathlib Log.lean contains
PowerSeries.subst_exp_log and PowerSeries.subst_log_exp_sub_one with equivalent types.
-/
private theorem eq_of_derivative_mul_one_add_X_eq_self {g : PowerSeries ℚ}
    (hderiv : derivative (R := ℚ) g * (1 + X) = g) :
    g = constantCoeff g • (1 + X) := by
  let : Invertible (1 + X : PowerSeries ℚ) :=
    (isUnit_iff_constantCoeff.mpr (by simp)).invertible
  have hcu : constantCoeff (⅟(1 + X) : PowerSeries ℚ) = 1 := by
    have h := congrArg (constantCoeff (R := ℚ)) (mul_invOf_self (1 + X : PowerSeries ℚ))
    rw [map_mul] at h
    simpa using h
  have hg : g * ⅟(1 + X) = derivative (R := ℚ) g := by
    conv_lhs => rw [← hderiv]
    rw [mul_assoc, mul_invOf_self, mul_one]
  have key : g * ⅟(1 + X) = C (constantCoeff g) := by
    refine derivative.ext ?_ ?_
    · simp only [Derivation.leibniz, derivative_invOf, map_add, derivative_one, derivative_X,
        zero_add, derivative_C, mul_one, smul_eq_mul, ← hg]
      ring
    · simp [hcu]
  rw [smul_eq_C_mul, ← key, mul_assoc, invOf_mul_self, mul_one]

theorem subst_exp_log : (exp ℚ).subst (log ℚ) = 1 + X := by
  have hd : derivative (R := ℚ) ((exp ℚ).subst (log ℚ)) * (1 + X) =
      (exp ℚ).subst (log ℚ) := by
    rw [derivative_subst (HasSubst.log), derivative_exp, mul_assoc,
      D5.S1.Recurrence.Periodic.ScaledLogColumnPeriodicity.log_derivative_mul, mul_one]
  have hc : constantCoeff ((exp ℚ).subst (log ℚ)) = 1 := by
    rw [← coeff_zero_eq_constantCoeff]
    rw [coeff_subst' HasSubst.log]
    rw [finsum_eq_single _ 0]
    · simp [coeff_exp]
    · intro n hn
      have hz : coeff 0 (log ℚ ^ n) = 0 :=
        X_pow_dvd_iff.mp (pow_dvd_pow_of_dvd (X_dvd_iff.mpr constantCoeff_log) n) 0
          (Nat.pos_of_ne_zero hn)
      simp [hz]
  have h := eq_of_derivative_mul_one_add_X_eq_self hd
  rwa [hc, one_smul] at h

theorem subst_log_exp_sub_one : (log ℚ).subst (exp ℚ - 1) = X := by
  let P : PowerSeries ℚ := exp ℚ - 1
  have hp : constantCoeff P = 0 := by simp [P]
  have hunit : IsUnit (coeff 1 P) := by simp [P, coeff_exp]
  let Q := P.substInvOfIsUnit hunit
  have hleft : (P.subst (log ℚ)) = X := by
    change (exp ℚ - 1).subst (log ℚ) = X
    rw [subst_sub HasSubst.log, subst_exp_log,
      ← coe_substAlgHom HasSubst.log (R := ℚ), map_one]
    ring
  have hlog : log ℚ = Q := by
    have hleftQ : Q.subst P = X := subst_substInvOfIsUnit_left P hp hunit
    calc
      log ℚ = PowerSeries.subst (log ℚ) (PowerSeries.subst P Q) := by
        rw [hleftQ, subst_X HasSubst.log]
      _ = PowerSeries.subst (PowerSeries.subst (log ℚ) P) Q := by
        rw [subst_comp_subst_apply (.of_constantCoeff_zero hp) HasSubst.log]
      _ = Q := by rw [hleft, X_subst]
  rw [hlog]
  exact subst_substInvOfIsUnit_left P hp hunit

def q (i n : ℕ) : ℤ := (i.factorial : ℤ) * (Nat.stirlingSecond n i : ℤ)

theorem egf_q (i : ℕ) : egf (fun n => (q i n : ℚ)) = (exp ℚ - 1) ^ i := by
  ext n
  rw [egf, coeff_mk]
  have h := D5.S1.Recurrence.Periodic.IntegralEgfTotientPeriod.exp_shift_power n i
  have hf : (n.factorial : ℚ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  simp only [q, Int.cast_mul, Int.cast_natCast]
  exact (div_eq_iff hf).mpr (by simpa [mul_comm] using h.symm)

theorem coeff_transform (L : ℕ → ℚ) (r : ℕ) :
    coeff r (logarithmicTransform L) =
      ∑ n ∈ range (r + 1), L n / (n.factorial : ℚ) * coeff r (log ℚ ^ n) := by
  rw [logarithmicTransform, coeff_subst' HasSubst.log]
  simp only [egf, coeff_mk, smul_eq_mul]
  apply finsum_eq_sum_of_support_subset
  intro n hn
  by_contra h
  have hlt : r < n := by
    simp only [Finset.mem_coe, mem_range] at h
    omega
  have hz : coeff r (log ℚ ^ n) = 0 :=
    X_pow_dvd_iff.mp (pow_dvd_pow_of_dvd (X_dvd_iff.mpr constantCoeff_log) n) r hlt
  change L n / (n.factorial : ℚ) * coeff r (log ℚ ^ n) ≠ 0 at hn
  exact hn (by rw [hz, mul_zero])

private noncomputable def kernel (i j : ℕ) : PowerSeries ℤ :=
  ∑ s ∈ range (i + 1), C ((-1 : ℤ) ^ (i - s) * (i.choose s : ℤ)) *
    (((1 : PowerSeries ℤ) + X) ^ s - 1) ^ j

private theorem egf_product_columns (i j : ℕ) :
    egf (fun n => (q i n : ℚ) * (q j n : ℚ)) =
      ∑ s ∈ range (i + 1), C ((-1 : ℚ) ^ (i - s) * (i.choose s : ℚ)) *
        ((exp ℚ) ^ s - 1) ^ j := by
  ext n
  rw [egf, coeff_mk, map_sum]
  have hi := congrArg (Int.castRingHom ℚ)
    (D5.S1.Recurrence.Parity.StirlingPowerFactorialPrimePeriod.stirling2_inclusion_exclusion n i)
  simp only [map_sum, map_mul, map_pow, map_neg, map_one, map_natCast] at hi
  have hqi : (q i n : ℚ) = (i.factorial : ℚ) * (Nat.stirlingSecond n i : ℚ) := by
    simp [q]
  rw [hqi, hi, sum_mul, sum_div]
  apply sum_congr rfl
  intro s hs
  rw [coeff_C_mul, exp_pow_eq_rescale_exp]
  have he : (rescale (s : ℚ) (exp ℚ) - 1) ^ j = rescale (s : ℚ) ((exp ℚ - 1) ^ j) := by
    rw [← coe_rescaleAlgHom, map_pow, map_sub, map_one, coe_rescaleAlgHom]
  rw [he, coeff_rescale, ← egf_q, egf, coeff_mk]
  ring

private theorem transform_product_columns (i j : ℕ) :
    logarithmicTransform (fun n => (q i n : ℚ) * (q j n : ℚ)) =
      (kernel i j).map (Int.castRingHom ℚ) := by
  rw [logarithmicTransform, egf_product_columns]
  rw [← coe_substAlgHom HasSubst.log]
  simp only [map_sum, map_mul, map_pow, map_sub, map_one]
  simp only [coe_substAlgHom, subst_C]
  have he : PowerSeries.subst (log ℚ) (exp ℚ) = (1 : PowerSeries ℚ) + X := subst_exp_log
  erw [he]
  simp [kernel]

private theorem egf_T (a : ℕ → ℤ) :
    egf (fun n => (T a n : ℚ)) =
      (mk (fun n => (a n : ℚ))).subst (exp ℚ - 1) := by
  ext n
  rw [egf, coeff_mk]
  have h := D5.S1.Recurrence.Periodic.IntegralEgfTotientPeriod.egf_shift_eq_stirling_transform a n
  have hf : (n.factorial : ℚ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  exact (div_eq_iff hf).mpr (by simpa [mul_comm] using h.symm)

theorem transform_T (a : ℕ → ℤ) :
    logarithmicTransform (fun n => (T a n : ℚ)) = mk (fun n => (a n : ℚ)) := by
  rw [logarithmicTransform, egf_T,
    subst_comp_subst_apply HasSubst.exp_sub_one HasSubst.log]
  have he : (exp ℚ - 1).subst (log ℚ) = X := by
    rw [subst_sub HasSubst.log, subst_exp_log,
      ← coe_substAlgHom HasSubst.log (R := ℚ), map_one]
    ring
  change (mk (fun n => (a n : ℚ))).subst ((exp ℚ - 1).subst (log ℚ)) = _
  rw [he, X_subst]

theorem T_window (a : ℕ → ℤ) {n r : ℕ} (hn : n ≤ r) :
    T a n = ∑ i ∈ range (r + 1), a i * q i n := by
  rw [T]
  simp only [q, ← mul_assoc]
  apply sum_subset (range_mono (by omega))
  intro i hi hin
  have hlt : n < i := by simp only [mem_range] at hin; omega
  simp [Nat.stirlingSecond_eq_zero_of_lt hlt]

private theorem transform_T_mul (a b : ℕ → ℤ) (r : ℕ) :
    coeff r (logarithmicTransform (fun n => (T a n : ℚ) * (T b n : ℚ))) =
      ((∑ i ∈ range (r + 1), ∑ j ∈ range (r + 1),
          a i * b j * coeff r (kernel i j) : ℤ) : ℚ) := by
  rw [coeff_transform]
  have he (n : ℕ) (hn : n ∈ range (r + 1)) :
      (T a n : ℚ) * (T b n : ℚ) / (n.factorial : ℚ) * coeff r (log ℚ ^ n) =
        ∑ i ∈ range (r + 1), ∑ j ∈ range (r + 1),
          (a i : ℚ) * (b j : ℚ) *
            ((q i n : ℚ) * (q j n : ℚ) / (n.factorial : ℚ) * coeff r (log ℚ ^ n)) := by
    rw [T_window a (Nat.le_of_lt_succ (mem_range.mp hn)),
      T_window b (Nat.le_of_lt_succ (mem_range.mp hn))]
    simp only [Int.cast_sum, Int.cast_mul]
    rw [sum_mul_sum]
    simp only [sum_div, sum_mul]
    apply sum_congr rfl
    intro i hi
    apply sum_congr rfl
    intro j hj
    ring
  rw [sum_congr rfl he, sum_comm]
  conv_lhs =>
    arg 2
    ext i
    rw [sum_comm]
  simp only [← mul_sum]
  push_cast
  apply sum_congr rfl
  intro i hi
  apply sum_congr rfl
  intro j hj
  rw [← coeff_transform, transform_product_columns, coeff_map]
  rfl

private theorem map_egf {K : Type*} [Field K] [CharZero K] (L : ℕ → ℚ) :
    (egf L).map (algebraMap ℚ K) = egf (fun n => algebraMap ℚ K (L n)) := by
  ext n
  simp [egf, coeff_map]

private theorem map_substitution {K : Type*} [Field K] [CharZero K]
    (f g : PowerSeries ℚ) (hg : HasSubst g) :
    PowerSeries.map (algebraMap ℚ K) (PowerSeries.subst g f) =
      PowerSeries.subst (PowerSeries.map (algebraMap ℚ K) g)
        (PowerSeries.map (algebraMap ℚ K) f) := by
  exact PowerSeries.map_subst hg f

theorem map_transform {K : Type*} [Field K] [CharZero K] (L : ℕ → ℚ) :
    (logarithmicTransform L).map (algebraMap ℚ K) =
      logarithmicTransform (fun n => algebraMap ℚ K (L n)) := by
  unfold logarithmicTransform
  erw [map_substitution (K := K) (egf L) (log ℚ) HasSubst.log]
  rw [map_egf, map_log]

theorem reconstruction {K : Type*} [Field K] [CharZero K] (L : ℕ → K)
    (h : IntegralSeries (logarithmicTransform L)) :
    ∃ a : ℕ → ℤ, ∀ n, L n = (T a n : K) := by
  choose a ha using h
  have hf : logarithmicTransform L = (mk (fun n => (a n : ℚ))).map (algebraMap ℚ K) := by
    ext n
    simp only [coeff_map, coeff_mk]
    simpa using ha n
  have hinv : (log K).subst (exp K - 1) = X := by
    have he := congrArg (map (algebraMap ℚ K)) subst_log_exp_sub_one
    rw [map_substitution _ _ HasSubst.exp_sub_one, map_log, map_sub, map_exp, map_one, map_X] at he
    exact he
  have hE : egf L = (egf (fun n => (T a n : ℚ))).map (algebraMap ℚ K) := by
    calc
      egf L = (logarithmicTransform L).subst (exp K - 1) := by
        rw [logarithmicTransform, subst_comp_subst_apply HasSubst.log HasSubst.exp_sub_one,
          hinv, X_subst]
      _ = ((mk (fun n => (a n : ℚ))).map (algebraMap ℚ K)).subst (exp K - 1) := by rw [hf]
      _ = (egf (fun n => (T a n : ℚ))).map (algebraMap ℚ K) := by
        rw [egf_T, map_substitution _ _ HasSubst.exp_sub_one, map_sub, map_exp, map_one]
  refine ⟨a, fun n => ?_⟩
  have hn := congrArg (coeff n) hE
  have hn' : L n / (n.factorial : K) = (T a n : K) / (n.factorial : K) := by
    simpa [egf, coeff_map] using hn
  have hfac : (n.factorial : K) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  exact (div_left_inj' hfac).mp hn'

private theorem binary_closure (L M : ℕ → ℚ)
    (hL : IntegralSeries (logarithmicTransform L))
    (hM : IntegralSeries (logarithmicTransform M)) :
    IntegralSeries (logarithmicTransform (fun n => L n * M n)) := by
  obtain ⟨a, ha⟩ := reconstruction L hL
  obtain ⟨b, hb⟩ := reconstruction M hM
  intro r
  refine ⟨∑ i ∈ range (r + 1), ∑ j ∈ range (r + 1), a i * b j * coeff r (kernel i j), ?_⟩
  simpa only [funext ha, funext hb] using transform_T_mul a b r

private theorem rational_powers (L : ℕ → ℚ) (h : IntegralSeries (logarithmicTransform L)) :
    ∀ m : ℕ, 0 < m → IntegralSeries (logarithmicTransform (fun n => L n ^ m)) := by
  intro m hm
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
  clear hm
  induction k with
  | zero => simpa using h
  | succ k ih =>
    simpa only [pow_succ] using binary_closure (fun n => L n ^ (k + 1)) L ih h

/-- The full Hanna closure conjecture, including degree zero and arbitrary L(0). -/
theorem result (K : Type*) [Field K] [CharZero K] (L : ℕ → K)
    (h : IntegralSeries (logarithmicTransform L)) (m : ℕ) (hm : 0 < m) :
    IntegralSeries (logarithmicTransform (fun n => L n ^ m)) := by
  obtain ⟨a, ha⟩ := reconstruction L h
  have hQ : IntegralSeries (logarithmicTransform (fun n => (T a n : ℚ))) := by
    intro n
    refine ⟨a n, ?_⟩
    rw [transform_T, coeff_mk]
  have hp := rational_powers (fun n => (T a n : ℚ)) hQ m hm
  intro r
  obtain ⟨z, hz⟩ := hp r
  refine ⟨z, ?_⟩
  have he := congrArg (algebraMap ℚ K) hz
  rw [← coeff_map, map_transform] at he
  simpa only [map_pow, map_intCast, ← ha] using he

#print axioms result

end D5.S1.Recurrence.Algebraic.HannaLogarithmicPowerClosure
