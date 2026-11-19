/- GID: D5/S1/Recurrence/Algebraic/HannaA300591RationalModel
   generality: I
   mirror-B: D5/B/S1/Recurrence/Algebraic/HannaA300591RationalModel
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Rational triangular construction for Hanna's squared exponential equations. -/

import D5.S1.Recurrence.Invariants.PowerSeriesNormalizedContraction
import D5.S1.Recurrence.Algebraic.DoldExponentialIntegrality
import D5.S1.Recurrence.Algebraic.HannaA300591AssemblyCoefficients
import Mathlib.RingTheory.PowerSeries.Log
import Mathlib.Data.Nat.Prime.Factorial

/-! Rational existence is independent of both arithmetic conjectures. -/

set_option autoImplicit false

open PowerSeries Finset
open D5.S1.Recurrence.Invariants.UnitReversionSquareParity

namespace D5.S1.Recurrence.Algebraic.HannaA300591RationalModel

/-- Formal exponential of a rational scalar times a series. -/
noncomputable def expSeries (t : ℚ) (F : PowerSeries ℚ) : PowerSeries ℚ :=
  (exp ℚ).subst (C t * F)

/-- The ordinary generating-series equation, with its zero normalization. -/
def IsSource (F : PowerSeries ℚ) : Prop :=
  constantCoeff F = 0 ∧ ∀ n : ℕ, 1 ≤ n →
    coeff n (expSeries ((n : ℚ) ^ 2) F) =
      (n : ℚ) ^ 2 * coeff (n - 1) (expSeries ((n : ℚ) ^ 2) F)

theorem expSeries_zero (t : ℚ) {F : PowerSeries ℚ}
    (hF : constantCoeff F = 0) : constantCoeff (expSeries t F) = 1 := by
  unfold expSeries
  exact D5.S1.Recurrence.Residue.ParametricExponentialSquareCongruence.exp_subst_zero
    (C t * F) (by simp [hF])

theorem expSeries_agree (t : ℚ) {d : ℕ} {F G : PowerSeries ℚ}
    (hF : constantCoeff F = 0) (hG : constantCoeff G = 0) (h : Agree d F G) :
    Agree d (expSeries t F) (expSeries t G) := by
  apply subst_inner_agree (f := exp ℚ) (u := C t * F) (v := C t * G)
  · intro n hn
    simp only [coeff_C_mul, h n hn]
  · simp [hF]
  · simp [hG]

theorem expSeries_derivative (t : ℚ) {F : PowerSeries ℚ}
    (hF : constantCoeff F = 0) :
    derivative (R := ℚ) (expSeries t F) = C t * derivative (R := ℚ) F * expSeries t F := by
  unfold expSeries
  rw [D5.S1.Recurrence.Algebraic.DoldExponentialIntegrality.expSeries_derivative
    (by simp [hF] : constantCoeff (C t * F) = 0)]
  simp only [Derivation.leibniz, derivative_C, mul_zero, add_zero, smul_eq_mul]
  ring

/-- The degree-n exponential residual depends only on the strict prefix. -/
theorem expSeries_residual {n : ℕ} (hn : 1 ≤ n) (t : ℚ)
    {F G : PowerSeries ℚ} (hF : constantCoeff F = 0) (hG : constantCoeff G = 0)
    (h : Agree n F G) :
    coeff n (expSeries t F) - t * coeff n F =
      coeff n (expSeries t G) - t * coeff n G := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  have he := expSeries_agree t hF hG h
  have recurrence (H : PowerSeries ℚ) (hH : constantCoeff H = 0) :
      coeff (k + 1) (expSeries t H) * (k + 1 : ℚ) =
        t * (coeff (k + 1) H * (k + 1 : ℚ) +
          ∑ j ∈ range k, (coeff (j + 1) H * (j + 1 : ℚ)) *
            coeff (k - j) (expSeries t H)) := by
    have hd := congrArg (coeff k) (expSeries_derivative t hH)
    rw [coeff_derivative, mul_assoc, coeff_C_mul, coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (fun i j => coeff i (derivative (R := ℚ) H) * coeff j (expSeries t H)) k,
      sum_range_succ] at hd
    simpa only [coeff_derivative, Nat.sub_self, coeff_zero_eq_constantCoeff,
      expSeries_zero t hH, mul_one, add_comm] using hd
  have hs : (∑ j ∈ range k, (coeff (j + 1) F * (j + 1 : ℚ)) *
      coeff (k - j) (expSeries t F)) =
      ∑ j ∈ range k, (coeff (j + 1) G * (j + 1 : ℚ)) *
        coeff (k - j) (expSeries t G) := by
    apply sum_congr rfl
    intro j hj
    rw [h (j + 1) (by have := mem_range.mp hj; omega), he (k - j) (by omega)]
  have hf := recurrence F hF
  have hg := recurrence G hG
  rw [hs] at hf
  have hk : (k + 1 : ℚ) ≠ 0 := by positivity
  apply mul_right_cancel₀ hk
  linear_combination hf - hg

private noncomputable def advance (lam mu : ℕ → ℚ) (F : PowerSeries ℚ) : PowerSeries ℚ :=
  mk fun n => if n = 0 then 0 else
    (mu n * coeff (n - 1) (expSeries (lam n) F) -
      (coeff n (expSeries (lam n) F) - lam n * coeff n F)) / lam n

private theorem advance_zero (lam mu : ℕ → ℚ) (F : PowerSeries ℚ) :
    constantCoeff (advance lam mu F) = 0 := by simp [advance]

private theorem advance_agree (lam mu : ℕ → ℚ) {d : ℕ}
    {F G : PowerSeries ℚ} (hF : constantCoeff F = 0) (hG : constantCoeff G = 0)
    (h : Agree d F G) : Agree (d + 1) (advance lam mu F) (advance lam mu G) := by
  intro n hn
  by_cases hn0 : n = 0
  · subst n; simp [advance]
  have hn1 : 1 ≤ n := by omega
  have hp : Agree n F G := agree_mono h (by omega)
  have he := expSeries_agree (lam n) hF hG hp
  simp only [advance, coeff_mk, ite_eq_right hn0]
  rw [he (n - 1) (by omega), expSeries_residual hn1 (lam n) hF hG hp]

theorem triangular_exists_unique (lam mu : ℕ → ℚ)
    (hlam : ∀ n, 1 ≤ n → lam n ≠ 0) :
    ∃! F : PowerSeries ℚ, constantCoeff F = 0 ∧ ∀ n : ℕ, 1 ≤ n →
      coeff n (expSeries (lam n) F) = mu n * coeff (n - 1) (expSeries (lam n) F) := by
  let step : PowerSeries ℚ → PowerSeries ℚ := fun B => 1 + advance lam mu (B - 1)
  have hstep0 (B : PowerSeries ℚ) (_ : constantCoeff B = 1) : constantCoeff (step B) = 1 := by
    simp [step, advance_zero]
  have hstep {d : ℕ} {B D : PowerSeries ℚ} (_hd : 1 ≤ d)
      (hB : constantCoeff B = 1) (hD : constantCoeff D = 1) (h : Agree d B D) :
      Agree (d + 1) (step B) (step D) := by
    have ha := advance_agree lam mu (by simp [hB] : constantCoeff (B - 1) = 0)
      (by simp [hD] : constantCoeff (D - 1) = 0)
      (show Agree d (B - 1) (D - 1) from fun n hn => by simp only [map_sub, h n hn])
    intro n hn
    simp only [step, map_add, ha n hn]
  obtain ⟨B, hB, hfix, huniq⟩ :=
    D5.S1.Recurrence.Invariants.PowerSeriesNormalizedContraction.exists_unique_fixed
      step hstep0 @hstep
  have fix_iff (F : PowerSeries ℚ) (hF : constantCoeff F = 0) :
      F = advance lam mu F ↔ ∀ n : ℕ, 1 ≤ n →
        coeff n (expSeries (lam n) F) = mu n * coeff (n - 1) (expSeries (lam n) F) := by
    constructor
    · intro hf n hn
      have he := congrArg (coeff n) hf
      simp only [advance, coeff_mk, ite_eq_right (by omega : n ≠ 0)] at he
      have he' := (eq_div_iff (hlam n hn)).mp he
      linear_combination he'
    · intro hf
      ext n
      by_cases hn : n = 0
      · subst n
        simpa only [coeff_zero_eq_constantCoeff] using hF.trans (advance_zero lam mu F).symm
      simp only [advance, coeff_mk, ite_eq_right hn]
      apply (eq_div_iff (hlam n (by omega))).mpr
      rw [hf n (by omega)]
      ring
  refine ⟨B - 1, ⟨by simp [hB], ?_⟩, ?_⟩
  · apply (fix_iff (B - 1) (by simp [hB])).mp
    dsimp [step] at hfix
    linear_combination hfix
  · intro F hF
    have hf := (fix_iff F hF.1).mpr hF.2
    have he : F + 1 = step (F + 1) := by
      dsimp [step]
      rw [add_sub_cancel_right, ← hf, add_comm]
    have hu := huniq (F + 1) (by simp [hF.1]) he
    linear_combination hu

theorem expSeries_one (F : PowerSeries ℚ) :
    expSeries 1 F = (exp ℚ).subst F := by simp [expSeries]

theorem expSeries_nat (F : PowerSeries ℚ) (hF : constantCoeff F = 0) (k : ℕ) :
    expSeries (k : ℚ) F = expSeries 1 F ^ k := by
  rw [expSeries_one]
  simpa only [expSeries, nsmul_eq_mul, ← Nat.cast_smul_eq_nsmul ℚ,
    smul_eq_C_mul] using
    D5.S1.Recurrence.Algebraic.DoldExponentialIntegrality.expSeries_nsmul hF k

theorem log_expSeries {F : PowerSeries ℚ} (hF : constantCoeff F = 0) :
    logOf (expSeries 1 F) = F := by
  have hs : HasSubst F := .of_constantCoeff_zero' hF
  have hone : (1 : PowerSeries ℚ).subst F = 1 := by simpa using subst_C (a := F) (1 : ℚ)
  rw [logOf_eq, expSeries_one, ← hone, ← subst_sub hs,
    ← subst_comp_subst_apply HasSubst.exp_sub_one hs, subst_log_exp_sub_one, subst_X hs]

theorem expSeries_log {B : PowerSeries ℚ} (hB : constantCoeff B = 1) :
    expSeries 1 (logOf B) = B := by
  have hs : HasSubst (B - 1) := .of_constantCoeff_zero' (by simp [hB])
  rw [expSeries_one, logOf_eq,
    ← subst_comp_subst_apply HasSubst.log hs, subst_exp_log, subst_add hs, subst_X hs]
  have hone : (1 : PowerSeries ℚ).subst (B - 1) = 1 := by
    simpa using subst_C (a := B - 1) (1 : ℚ)
  rw [hone]
  ring

end D5.S1.Recurrence.Algebraic.HannaA300591RationalModel

namespace D5.S1.Recurrence.Algebraic.HannaA300591RationalModel

open D5.S1.Recurrence.Algebraic.DoldExponentialIntegrality

private theorem valuation_add_bound (p : ℕ) [Fact p.Prime] (b : ℤ) (u v : ℚ)
    (hu : u ≠ 0 → b ≤ padicValRat p u) (hv : v ≠ 0 → b ≤ padicValRat p v) :
    u + v ≠ 0 → b ≤ padicValRat p (u + v) := by
  intro huv
  by_cases hu0 : u = 0
  · simpa [hu0] using hv (by simpa [hu0] using huv)
  by_cases hv0 : v = 0
  · simpa [hv0] using hu (by simpa [hv0] using huv)
  exact le_trans (le_min (hu hu0) (hv hv0)) (padicValRat.min_le_padicValRat_add huv)

private theorem valuation_sum_bound (p : ℕ) [Fact p.Prime] (b : ℤ)
    (s : Finset ℕ) (f : ℕ → ℚ)
    (h : ∀ j ∈ s, f j ≠ 0 → b ≤ padicValRat p (f j)) :
    ∑ j ∈ s, f j ≠ 0 → b ≤ padicValRat p (∑ j ∈ s, f j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [sum_insert ha]
    exact valuation_add_bound p b _ _ (h a (mem_insert_self a s))
      (ih (fun j hj => h j (mem_insert_of_mem hj)))

private theorem exp_prefix_bound (p : ℕ) (hp : p.Prime) (t : ℚ) (ht : t ≠ 0)
    (htv : 1 ≤ padicValRat p t) (P : PowerSeries ℚ)
    (hP0 : constantCoeff P = 0) (hP : IsRIntegralPS p P)
    (d : ℕ) (_hd : 1 ≤ d) (m : ℕ) (hm : m = 1 ∨ m = 2)
    (hsmall : ∀ j < m, coeff d (P ^ j) = 0) :
    coeff d (expSeries t P) ≠ 0 →
      (m : ℤ) * padicValRat p t - (m - 1 : ℕ) ≤
        padicValRat p (coeff d (expSeries t P)) := by
  let : Fact p.Prime := ⟨hp⟩
  rw [expSeries, expSeries_coeff _ (by simp [hP0])]
  apply valuation_sum_bound
  intro j hj hterm
  have hcoeff : coeff d (P ^ j) ≠ 0 := by
    intro hz
    apply hterm
    simp [mul_pow, ← map_pow, coeff_C_mul, hz]
  have hjm : m ≤ j := by
    by_contra hjm
    exact hcoeff (hsmall j (by omega))
  have hj0 : j ≠ 0 := by rcases hm with rfl | rfl <;> omega
  have hv := (localRat_iff_val_nonneg p hp _).mp (hP.pow j d)
  have hfac := padicValNat_factorial_lt_of_ne_zero p hj0
  have he : coeff d ((C t * P) ^ j) / (j.factorial : ℚ) =
      t ^ j * coeff d (P ^ j) / (j.factorial : ℚ) := by
    rw [mul_pow, ← map_pow, coeff_C_mul]
  rw [he, padicValRat.div (mul_ne_zero (pow_ne_zero _ ht) hcoeff)
    (by exact_mod_cast Nat.factorial_ne_zero j),
    padicValRat.mul (pow_ne_zero _ ht) hcoeff, padicValRat.pow, padicValRat.of_nat]
  have hjz : (m : ℤ) ≤ (j : ℤ) := by exact_mod_cast hjm
  have hfacz : (padicValNat p j.factorial : ℤ) ≤ (j : ℤ) - 1 := by omega
  have hprod : 0 ≤ ((j : ℤ) - m) * (padicValRat p t - 1) :=
    mul_nonneg (by omega) (by omega)
  rcases hm with rfl | rfl <;>
    norm_num only [Nat.cast_one, Nat.cast_ofNat, Nat.reduceSub] at * <;> nlinarith

theorem local_automatic_bound (p : ℕ) (hp : p.Prime) (t : ℚ)
    (ht : t ≠ 0) (htv : 1 ≤ padicValRat p t)
    (F : PowerSeries ℚ) (hF : constantCoeff F = 0) (n : ℕ) (hn : 2 ≤ n)
    (hprefix : ∀ j < n, IsRIntegralRat p (coeff j F))
    (heq : coeff n (expSeries t F) = t * coeff (n - 1) (expSeries t F)) :
    coeff n F ≠ 0 → padicValRat p t - 1 ≤ padicValRat p (coeff n F) := by
  let : Fact p.Prime := ⟨hp⟩
  let P : PowerSeries ℚ := mk fun j => if j < n then coeff j F else 0
  have hP0 : constantCoeff P = 0 := by simp [P, show 0 < n by omega, hF]
  have hPn : coeff n P = 0 := by simp [P]
  have hP : IsRIntegralPS p P := by
    intro j
    by_cases hj : j < n
    · simpa [P, hj] using hprefix j hj
    · simpa [P, hj] using IsRIntegralRat.zero p
  have hagree : Agree n F P := by intro j hj; simp [P, hj]
  have hres := expSeries_residual (by omega : 1 ≤ n) t hF hP0 hagree
  have hprev := expSeries_agree t hF hP0 hagree (n - 1) (by omega)
  have hsolve : coeff n F = coeff (n - 1) (expSeries t P) -
      coeff n (expSeries t P) / t := by
    rw [heq, hprev, hPn, mul_zero, sub_zero] at hres
    field_simp
    linear_combination -hres
  have ha := exp_prefix_bound p hp t ht htv P hP0 hP (n - 1) (by omega)
    1 (Or.inl rfl) (by
      intro j hj
      have : j = 0 := by omega
      subst j
      simp [show n - 1 ≠ 0 by omega])
  have hb := exp_prefix_bound p hp t ht htv P hP0 hP n (by omega)
    2 (Or.inr rfl) (by
      intro j hj
      interval_cases j
      · simp [show n ≠ 0 by omega]
      · simpa using hPn)
  rw [hsolve, sub_eq_add_neg]
  apply valuation_add_bound p (padicValRat p t - 1)
  · intro h
    have hh := ha h
    norm_num at hh
    omega
  · intro h
    have hb0 : coeff n (expSeries t P) ≠ 0 := by
      intro hz; simp [hz] at h
    have hh := hb hb0
    rw [padicValRat.neg, padicValRat.div hb0 ht]
    norm_num at hh
    omega

/-- At primes dividing the index, the strict local prefix already forces an integral quotient. -/
theorem source_local_quotient (F : PowerSeries ℚ) (hF : IsSource F)
    (n : ℕ) (hn : 2 ≤ n) (p : ℕ) (hp : p.Prime) (hpn : p ∣ n)
    (hprefix : ∀ j < n, IsRIntegralRat p (coeff j F)) :
    IsRIntegralRat p (coeff n F / (n : ℚ)) := by
  let : Fact p.Prime := ⟨hp⟩
  have hn0 : n ≠ 0 := by omega
  have hnq : (n : ℚ) ≠ 0 := by exact_mod_cast hn0
  have hvn : 1 ≤ padicValNat p n := one_le_padicValNat_of_dvd hn0 hpn
  apply (localRat_iff_val_nonneg p hp _).mpr
  by_cases hc : coeff n F = 0
  · simp [hc]
  have ht : padicValRat p ((n : ℚ) ^ 2) = 2 * padicValNat p n := by
    simp [padicValRat.pow]
  have hb := local_automatic_bound p hp ((n : ℚ) ^ 2) (pow_ne_zero _ hnq)
    (by rw [ht]; omega) F hF.1 n hn hprefix (hF.2 n (by omega)) hc
  rw [ht] at hb
  rw [padicValRat.div hc hnq, padicValRat.of_nat]
  omega

private theorem exp_prefix_integral (p : ℕ) (hp : p.Prime) (t : ℚ) (ht : t ≠ 0)
    (htp : IsRIntegralRat p t) (P : PowerSeries ℚ)
    (hP0 : constantCoeff P = 0) (hP : IsRIntegralPS p P)
    (d : ℕ) (hd : d < p) : IsRIntegralRat p (coeff d (expSeries t P)) := by
  let : Fact p.Prime := ⟨hp⟩
  have htv := (localRat_iff_val_nonneg p hp _).mp htp
  apply (localRat_iff_val_nonneg p hp _).mpr
  rw [expSeries, expSeries_coeff _ (by simp [hP0])]
  have hbound : ∑ j ∈ range (d + 1), coeff d ((C t * P) ^ j) / (j.factorial : ℚ) ≠ 0 →
      0 ≤ padicValRat p (∑ j ∈ range (d + 1), coeff d ((C t * P) ^ j) / (j.factorial : ℚ)) := by
    apply valuation_sum_bound
    intro j hj hterm
    have hcoeff : coeff d (P ^ j) ≠ 0 := by
      intro hz
      apply hterm
      simp [mul_pow, ← map_pow, coeff_C_mul, hz]
    have hv := (localRat_iff_val_nonneg p hp _).mp (hP.pow j d)
    have hfac : padicValNat p j.factorial = 0 :=
      padicValNat.eq_zero_of_not_dvd (by rw [hp.dvd_factorial]; have := mem_range.mp hj; omega)
    rw [mul_pow, ← map_pow, coeff_C_mul,
      padicValRat.div (mul_ne_zero (pow_ne_zero _ ht) hcoeff)
        (by exact_mod_cast Nat.factorial_ne_zero j),
      padicValRat.mul (pow_ne_zero _ ht) hcoeff, padicValRat.pow,
      padicValRat.of_nat, hfac]
    simpa only [Nat.cast_zero, sub_zero] using
      (add_nonneg (mul_nonneg (Int.natCast_nonneg j) htv) hv)
  by_cases hz : ∑ j ∈ range (d + 1), coeff d ((C t * P) ^ j) / (j.factorial : ℚ) = 0
  · simp [hz]
  · exact hbound hz

private theorem source_large_prime_quotient (F : PowerSeries ℚ) (hF : IsSource F)
    (n : ℕ) (hn : 1 ≤ n) (p : ℕ) (hp : p.Prime) (hnp : n < p)
    (hprefix : ∀ j < n, IsRIntegralRat p (coeff j F)) :
    IsRIntegralRat p (coeff n F / (n : ℚ)) := by
  let : Fact p.Prime := ⟨hp⟩
  have hn0 : n ≠ 0 := by omega
  have hnq : (n : ℚ) ≠ 0 := by exact_mod_cast hn0
  have hvn : padicValNat p n = 0 :=
    padicValNat.eq_zero_of_not_dvd (Nat.not_dvd_of_pos_of_lt (by omega) hnp)
  have hunit : IsRIntegralRat p ((n : ℚ)⁻¹) := by
    apply (localRat_iff_val_nonneg p hp _).mpr
    simp [padicValRat.inv, hvn]
  let P : PowerSeries ℚ := mk fun j => if j < n then coeff j F else 0
  have hP0 : constantCoeff P = 0 := by simp [P, show 0 < n by omega, hF.1]
  have hPn : coeff n P = 0 := by simp [P]
  have hP : IsRIntegralPS p P := by
    intro j
    by_cases hj : j < n
    · simpa [P, hj] using hprefix j hj
    · simpa [P, hj] using IsRIntegralRat.zero p
  have hagree : Agree n F P := by intro j hj; simp [P, hj]
  have hres := expSeries_residual hn ((n : ℚ) ^ 2) hF.1 hP0 hagree
  have hprev := expSeries_agree ((n : ℚ) ^ 2) hF.1 hP0 hagree (n - 1) (by omega)
  have hsolve : coeff n F = coeff (n - 1) (expSeries ((n : ℚ) ^ 2) P) -
      coeff n (expSeries ((n : ℚ) ^ 2) P) / (n : ℚ) ^ 2 := by
    rw [hF.2 n hn, hprev, hPn, mul_zero, sub_zero] at hres
    field_simp
    linear_combination -hres
  have ht : IsRIntegralRat p ((n : ℚ) ^ 2) := by simp [IsRIntegralRat]
  have ha := exp_prefix_integral p hp _ (pow_ne_zero _ hnq) ht P hP0 hP
    (n - 1) (by omega)
  have hb := exp_prefix_integral p hp _ (pow_ne_zero _ hnq) ht P hP0 hP n hnp
  have hc : IsRIntegralRat p (coeff n F) := by
    rw [hsolve, div_eq_mul_inv, ← inv_pow, sub_eq_add_neg]
    simpa only [pow_two] using ha.add ((hb.mul_coprime (hunit.mul_coprime hunit)).neg)
  exact hc.mul_coprime hunit

private theorem source_coeff_one (F : PowerSeries ℚ) (hF : IsSource F) : coeff 1 F = 1 := by
  have hd := congrArg (coeff 0) (expSeries_derivative 1 hF.1)
  simp only [coeff_derivative, Nat.cast_zero, zero_add, mul_one, map_one, one_mul,
    coeff_zero_eq_constantCoeff, map_mul, expSeries_zero 1 hF.1] at hd
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_derivative] at hd
  norm_num at hd
  have he := hF.2 1 (by omega)
  norm_num [expSeries_zero 1 hF.1] at he
  linear_combination he - hd

/-- A first noninteger coefficient can only have small denominator primes coprime to its index. -/
theorem source_denominator_obstruction (F : PowerSeries ℚ) (hF : IsSource F)
    (n : ℕ)
    (hprefix : ∀ j < n, ∃ z : ℤ, coeff j F = (z : ℚ))
    (hbad : ¬ ∃ z : ℤ, coeff n F = (z : ℚ)) :
    2 ≤ n ∧ ∃ p : ℕ, p.Prime ∧ p < n ∧ ¬ p ∣ n ∧ p ∣ (coeff n F).den := by
  have hn0 : n ≠ 0 := by
    intro he
    subst n
    exact hbad ⟨0, by simpa [coeff_zero_eq_constantCoeff] using hF.1⟩
  have hn1 : n ≠ 1 := by
    intro he
    subst n
    exact hbad ⟨1, by simpa using source_coeff_one F hF⟩
  have hn : 2 ≤ n := by omega
  refine ⟨hn, ?_⟩
  have hd : (coeff n F).den ≠ 1 := by
    intro hd
    exact hbad ⟨(coeff n F).num, (Rat.den_eq_one_iff _).mp hd |>.symm⟩
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hd
  have hpre : ∀ j < n, IsRIntegralRat p (coeff j F) := by
    intro j hj
    obtain ⟨z, hz⟩ := hprefix j hj
    simp [hz, IsRIntegralRat]
  have hnot : ¬ IsRIntegralRat p (coeff n F) := by
    intro h
    exact (hp.coprime_iff_not_dvd.mp h.symm) hpd
  have hlocal (hq : IsRIntegralRat p (coeff n F / (n : ℚ))) : False := by
    apply hnot
    have hnat : IsRIntegralRat p (n : ℚ) := by simp [IsRIntegralRat]
    have he : coeff n F / (n : ℚ) * n = coeff n F :=
      div_mul_cancel₀ _ (by exact_mod_cast (show n ≠ 0 by omega))
    simpa only [he] using hq.mul_coprime hnat
  have hpn : ¬ p ∣ n := by
    intro hpn
    exact hlocal (source_local_quotient F hF n hn p hp hpn hpre)
  have hnp : ¬ n < p := by
    intro hnp
    exact hlocal (source_large_prime_quotient F hF n (by omega) p hp hnp hpre)
  refine ⟨p, hp, ?_, hpn, hpd⟩
  have hne : p ≠ n := by intro he; exact hpn (he ▸ dvd_refl p)
  omega

/-- Once ordinary integrality is established, every positive coefficient has an integer quotient. -/
theorem source_divisible_of_integral (F : PowerSeries ℚ) (hF : IsSource F)
    (hints : ∀ r : ℕ, ∃ z : ℤ, coeff r F = (z : ℚ)) :
    ∀ n : ℕ, 1 ≤ n → ∃ q : ℤ, coeff n F = (n : ℚ) * (q : ℚ) := by
  let Q : PowerSeries ℚ := mk fun n => coeff n F / (n : ℚ)
  have hQ : ∀ p : ℕ, p.Prime → IsRIntegralPS p Q := by
    intro p hp n
    dsimp only [Q]
    rw [coeff_mk]
    by_cases hn0 : n = 0
    · simp [hn0, IsRIntegralRat]
    by_cases hn1 : n = 1
    · obtain ⟨z, hz⟩ := hints n
      rw [hz]
      simp [hn1, IsRIntegralRat]
    by_cases hpn : p ∣ n
    · apply source_local_quotient F hF n (by omega) p hp hpn
      intro j hj
      obtain ⟨z, hz⟩ := hints j
      simp [hz, IsRIntegralRat]
    · let : Fact p.Prime := ⟨hp⟩
      obtain ⟨z, hz⟩ := hints n
      apply (localRat_iff_val_nonneg p hp _).mpr
      by_cases hz0 : z = 0
      · simp [hz, hz0]
      have hnq : (n : ℚ) ≠ 0 := by exact_mod_cast hn0
      rw [hz, padicValRat.div (by exact_mod_cast hz0) hnq,
        padicValRat.of_int, padicValRat.of_nat, padicValNat.eq_zero_of_not_dvd hpn]
      simp
  have hi := integral_of_local Q hQ
  intro n hn
  obtain ⟨q, hq⟩ := hi n
  refine ⟨q, ?_⟩
  have hnq : (n : ℚ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have he : (q : ℚ) = coeff n F / (n : ℚ) := by simpa [Q] using hq.symm
  rw [he]
  field_simp

open HannaA300591AssemblyCoefficients

/-- The source equations force ordinary integrality in every degree and integer
index quotients at every positive degree, with no arithmetic premise. -/
theorem source_integral_and_divisible (F : PowerSeries ℚ) (hF : IsSource F) :
    (∀ r : ℕ, ∃ z : ℤ, coeff r F = (z : ℚ)) ∧
      ∀ n : ℕ, 1 ≤ n → ∃ q : ℤ, coeff n F = (n : ℚ) * (q : ℚ) := by
  classical
  have hints : ∀ n : ℕ, ∃ z : ℤ, coeff n F = (z : ℚ) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      by_contra hbad
      obtain ⟨hn, p, hp, hplt, hpn, hpd⟩ := source_denominator_obstruction F hF n ih hbad
      let a : ℕ → ℤ := fun j => if hj : j < n then Classical.choose (ih j hj) else 0
      let P := prefixSeries n a
      have hP : constantCoeff P = 0 := by simp [P, prefixSeries]
      have hPF : Agree n P F := by
        intro j hj
        by_cases hj0 : j = 0
        · subst j
          simpa [coeff_zero_eq_constantCoeff, hP] using hF.1.symm
        · have hz : coeff j F = (a j : ℚ) := by
            simp only [a, dif_pos hj]
            exact Classical.choose_spec (ih j hj)
          simpa [P, prefixSeries, hj, Nat.pos_of_ne_zero hj0] using hz.symm
      have hFP : Agree n F P := fun j hj => (hPF j hj).symm
      have hlower : ∀ f : ℕ, 1 ≤ f → f < n →
          let H := (exp ℚ).subst (C ((f : ℚ) ^ 2) * prefixSeries n a)
          coeff f H = (f : ℚ) ^ 2 * coeff (f - 1) H := by
        intro f hf hfn
        have he := expSeries_agree ((f : ℚ) ^ 2) hP hF.1 hPF
        change coeff f (expSeries ((f : ℚ) ^ 2) P) =
          (f : ℚ) ^ 2 * coeff (f - 1) (expSeries ((f : ℚ) ^ 2) P)
        rw [he f hfn, he (f - 1) (by omega)]
        exact hF.2 f hf
      have hlocal := signed_prefix_residual_local_integral n a (by omega) p hp hpn hlower
      have hres := expSeries_residual (by omega : 1 ≤ n) ((n : ℚ) ^ 2) hF.1 hP hFP
      have he := expSeries_agree ((n : ℚ) ^ 2) hF.1 hP hFP
      have hnP : coeff n P = 0 := by simp [P, prefixSeries]
      have hminus := he (n - 1) (by omega)
      have heqn := hF.2 n (by omega)
      have hr : coeff n (expSeries ((n : ℚ) ^ 2) P) -
          (n : ℚ) ^ 2 * coeff (n - 1) (expSeries ((n : ℚ) ^ 2) P) =
          -((n : ℚ) ^ 2 * coeff n F) := by
        rw [hnP, mul_zero, sub_zero] at hres
        rw [hminus] at heqn
        linear_combination -hres + heqn
      change IsRIntegralRat p (coeff n (expSeries ((n : ℚ) ^ 2) P) -
        (n : ℚ) ^ 2 * coeff (n - 1) (expSeries ((n : ℚ) ^ 2) P)) at hlocal
      rw [hr] at hlocal
      letI : Fact p.Prime := ⟨hp⟩
      have hc : coeff n F ≠ 0 := by
        intro hc
        exact hbad ⟨0, by simpa using hc⟩
      have hnq : (n : ℚ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
      have hv := (localRat_iff_val_nonneg p hp _).mp hlocal
      rw [padicValRat.neg, padicValRat.mul (pow_ne_zero _ hnq) hc,
        padicValRat.pow, padicValRat.of_nat, padicValNat.eq_zero_of_not_dvd hpn] at hv
      have hi : IsRIntegralRat p (coeff n F) :=
        (localRat_iff_val_nonneg p hp _).mpr (by simpa using hv)
      exact (hp.coprime_iff_not_dvd.mp hi.symm) hpd
  exact ⟨hints, source_divisible_of_integral F hF hints⟩

end D5.S1.Recurrence.Algebraic.HannaA300591RationalModel
