/- GID: D5/S1/Recurrence/Algebraic/HannaA300595Integrality
   generality: I
   mirror-B: D5/B/S1/Recurrence/Algebraic/HannaA300595Integrality
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: The normalized rational cubic exponential series has integral ordinary coefficients. -/

import D5.S1.Recurrence.Algebraic.HannaA300591RationalModel
import D5.S1.Recurrence.Algebraic.MarkedAssemblyCoefficients
import D5.S1.Recurrence.Residue.IntegralEGFComposition

set_option autoImplicit false

open PowerSeries Finset
open D5.S1.Recurrence.Invariants.UnitReversionSquareParity

namespace D5.S1.Recurrence.Algebraic.HannaA300595Integrality

open HannaA300591RationalModel (expSeries expSeries_zero expSeries_agree
  expSeries_derivative expSeries_residual triangular_exists_unique expSeries_nat
  log_expSeries expSeries_log local_automatic_bound)
open MarkedAssemblyCoefficients (prefixSeries)
open DoldExponentialIntegrality

/-- The normalized rational ordinary-series definition of OEIS A300595. -/
def IsSource (F : PowerSeries ℚ) : Prop :=
  constantCoeff F = 0 ∧ ∀ n : ℕ, 1 ≤ n →
    coeff n (expSeries ((n : ℚ) ^ 3) F) =
      (n : ℚ) ^ 3 * coeff (n - 1) (expSeries ((n : ℚ) ^ 3) F)

/-- The normalized unit companion, using ordinary coefficients in its power equation. -/
def IsCompanion (B : PowerSeries ℚ) : Prop :=
  constantCoeff B = 1 ∧ ∀ n : ℕ, 1 ≤ n →
    coeff n (B ^ (n ^ 3)) = (n : ℚ) ^ 3 * coeff (n - 1) (B ^ (n ^ 3))

private theorem source_integral (F : PowerSeries ℚ) (hF : IsSource F) :
    ∀ r : ℕ, ∃ z : ℤ, coeff r F = (z : ℚ) := by
  classical
  have hone : coeff 1 F = 1 := by
    have hd := congrArg (coeff 0) (expSeries_derivative 1 hF.1)
    simp only [coeff_derivative, Nat.cast_zero, zero_add, mul_one, map_one, one_mul,
      coeff_zero_eq_constantCoeff, map_mul, expSeries_zero 1 hF.1] at hd
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_derivative] at hd
    norm_num at hd
    have he := hF.2 1 (by omega)
    norm_num [expSeries_zero 1 hF.1] at he
    linear_combination he - hd
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn0 : n = 0
    · subst n
      exact ⟨0, by simpa [coeff_zero_eq_constantCoeff] using hF.1⟩
    by_cases hn1 : n = 1
    · subst n
      exact ⟨1, by simpa using hone⟩
    have hn : 2 ≤ n := by omega
    by_contra hbad
    have hd : (coeff n F).den ≠ 1 := by
      intro hd
      exact hbad ⟨(coeff n F).num, (Rat.den_eq_one_iff _).mp hd |>.symm⟩
    obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hd
    letI : Fact p.Prime := ⟨hp⟩
    have hc : coeff n F ≠ 0 := by
      intro hc
      exact hbad ⟨0, by simpa using hc⟩
    have hnq : (n : ℚ) ≠ 0 := by exact_mod_cast hn0
    have hpre : ∀ j < n, IsRIntegralRat p (coeff j F) := by
      intro j hj
      obtain ⟨z, hz⟩ := ih j hj
      simp [hz, IsRIntegralRat]
    have hlocal : IsRIntegralRat p (coeff n F) := by
      by_cases hpn : p ∣ n
      · have hvn : 1 ≤ padicValNat p n := one_le_padicValNat_of_dvd hn0 hpn
        have ht : padicValRat p ((n : ℚ) ^ 3) = 3 * padicValNat p n := by
          simp [padicValRat.pow]
        have hb := local_automatic_bound p hp ((n : ℚ) ^ 3) (pow_ne_zero _ hnq)
          (by rw [ht]; omega) F hF.1 n hn hpre (hF.2 n (by omega)) hc
        rw [ht] at hb
        exact (localRat_iff_val_nonneg p hp _).mpr (by omega)
      · let a : ℕ → ℤ := fun j => if hj : j < n then Classical.choose (ih j hj) else 0
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
            let H := (exp ℚ).subst (C ((f : ℚ) ^ 3) * prefixSeries n a)
            coeff f H = (f : ℚ) ^ 3 * coeff (f - 1) H := by
          intro f hf hfn
          have he := expSeries_agree ((f : ℚ) ^ 3) hP hF.1 hPF
          change coeff f (expSeries ((f : ℚ) ^ 3) P) =
            (f : ℚ) ^ 3 * coeff (f - 1) (expSeries ((f : ℚ) ^ 3) P)
          rw [he f hfn, he (f - 1) (by omega)]
          exact hF.2 f hf
        have hl := MarkedAssemblyCoefficients.signed_prefix_residual_local_integral
          3 n a (by omega) p hp hpn hlower
        have hres := expSeries_residual (by omega : 1 ≤ n) ((n : ℚ) ^ 3) hF.1 hP hFP
        have he := expSeries_agree ((n : ℚ) ^ 3) hF.1 hP hFP
        have hnP : coeff n P = 0 := by simp [P, prefixSeries]
        have hminus := he (n - 1) (by omega)
        have heqn := hF.2 n (by omega)
        have hr : coeff n (expSeries ((n : ℚ) ^ 3) P) -
            (n : ℚ) ^ 3 * coeff (n - 1) (expSeries ((n : ℚ) ^ 3) P) =
            -((n : ℚ) ^ 3 * coeff n F) := by
          rw [hnP, mul_zero, sub_zero] at hres
          rw [hminus] at heqn
          linear_combination -hres + heqn
        change IsRIntegralRat p (coeff n (expSeries ((n : ℚ) ^ 3) P) -
          (n : ℚ) ^ 3 * coeff (n - 1) (expSeries ((n : ℚ) ^ 3) P)) at hl
        rw [hr] at hl
        have hv := (localRat_iff_val_nonneg p hp _).mp hl
        rw [padicValRat.neg, padicValRat.mul (pow_ne_zero _ hnq) hc,
          padicValRat.pow, padicValRat.of_nat, padicValNat.eq_zero_of_not_dvd hpn] at hv
        exact (localRat_iff_val_nonneg p hp _).mpr (by simpa using hv)
    exact (hp.coprime_iff_not_dvd.mp hlocal.symm) hpd

private theorem source_to_companion {F : PowerSeries ℚ} (hF : IsSource F) :
    IsCompanion (expSeries 1 F) := by
  refine ⟨expSeries_zero 1 hF.1, ?_⟩
  intro n hn
  simpa only [← expSeries_nat F hF.1, Nat.cast_pow] using hF.2 n hn

private theorem companion_to_source {B : PowerSeries ℚ} (hB : IsCompanion B) :
    IsSource (logOf B) := by
  have hz := constantCoeff_logOf hB.1
  refine ⟨hz, ?_⟩
  intro n hn
  simpa only [show (n : ℚ) ^ 3 = ((n ^ 3 : ℕ) : ℚ) by simp,
    expSeries_nat (logOf B) hz, expSeries_log hB.1] using hB.2 n hn

/-- Unique rational characterization, all ordinary coefficients integral, and the exact
normalized exponential/logarithmic companion with its EGF coefficient convention. -/
theorem result :
    (∃! F : PowerSeries ℚ, IsSource F) ∧
    ∀ F : PowerSeries ℚ, IsSource F →
      (∀ m : ℕ, 1 ≤ m → ∃ z : ℤ, coeff m F = (z : ℚ)) ∧
      IsCompanion (expSeries 1 F) ∧ logOf (expSeries 1 F) = F ∧
      (∀ n : ℕ, expSeries ((n : ℚ) ^ 3) F = expSeries 1 F ^ (n ^ 3)) ∧
      (∀ B : PowerSeries ℚ, IsCompanion B → B = expSeries 1 F) ∧
      (mk (fun r =>
        D5.S1.Recurrence.Residue.IntegralEGFComposition.eCoeff (expSeries 1 F) r /
          (r.factorial : ℚ)) = expSeries 1 F) := by
  have hu : ∃! F : PowerSeries ℚ, IsSource F :=
    triangular_exists_unique (fun n => (n : ℚ) ^ 3) (fun n => (n : ℚ) ^ 3)
      (fun n hn => pow_ne_zero _ (by exact_mod_cast (show n ≠ 0 by omega)))
  refine ⟨hu, ?_⟩
  intro F hF
  refine ⟨(fun m _ => source_integral F hF m), source_to_companion hF,
    log_expSeries hF.1, ?_, ?_, ?_⟩
  · intro n
    have he := expSeries_nat F hF.1 (n ^ 3)
    norm_cast at he ⊢
  · intro B hB
    obtain ⟨G, hG, huniq⟩ := hu
    have he : logOf B = F :=
      (huniq (logOf B) (companion_to_source hB)).trans (huniq F hF).symm
    rw [← he, expSeries_log hB.1]
  · ext r
    simp [D5.S1.Recurrence.Residue.IntegralEGFComposition.eCoeff,
      Nat.factorial_ne_zero]

end D5.S1.Recurrence.Algebraic.HannaA300595Integrality
