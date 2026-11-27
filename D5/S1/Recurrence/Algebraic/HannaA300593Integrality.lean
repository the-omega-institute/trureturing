/- GID: D5/S1/Recurrence/Algebraic/HannaA300593Integrality
   generality: I
   mirror-B: D5/B/S1/Recurrence/Algebraic/HannaA300593Integrality
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: The square-exponential series with cubic multiplier has integral coefficients. -/

import D5.S1.Recurrence.Algebraic.HannaA300591RationalModel
import D5.S1.Recurrence.Algebraic.MarkedAssemblyExtraMarker
import D5.S1.Recurrence.Residue.IntegralEGFComposition

/-! The all-degree A300593 conjecture and the A300592 companion. -/

set_option autoImplicit false

open PowerSeries
open D5.S1.Recurrence.Invariants.UnitReversionSquareParity

namespace D5.S1.Recurrence.Algebraic.HannaA300593Integrality

open HannaA300591RationalModel (expSeries expSeries_zero expSeries_agree expSeries_residual
  triangular_exists_unique expSeries_nat log_expSeries expSeries_log exp_prefix_bound
  valuation_add_bound)
open MarkedAssemblyCoefficients (prefixSeries)
open DoldExponentialIntegrality
open D5.S1.Recurrence.Residue.IntegralEGFComposition (eCoeff)

/-- The normalized rational ordinary series of OEIS A300593. -/
def IsSource (F : PowerSeries ℚ) : Prop :=
  constantCoeff F = 0 ∧ ∀ n : ℕ, 1 ≤ n →
    coeff n (expSeries ((n : ℚ) ^ 2) F) =
      (n : ℚ) ^ 3 * coeff (n - 1) (expSeries ((n : ℚ) ^ 2) F)

/-- The unit EGF of OEIS A300592, with ordinary extraction in its power equation. -/
def IsCompanion (B : PowerSeries ℚ) : Prop :=
  constantCoeff B = 1 ∧ ∀ n : ℕ, 1 ≤ n →
    coeff n (B ^ (n ^ 2)) = (n : ℚ) ^ 3 * coeff (n - 1) (B ^ (n ^ 2))

private theorem dividing_prime_bound (p : ℕ) (hp : p.Prime) {n : ℕ}
    (hn : 2 ≤ n) (hpn : p ∣ n) {P : PowerSeries ℚ}
    (hP0 : constantCoeff P = 0) (hPn : coeff n P = 0) (hP : IsRIntegralPS p P) :
    let t := (n : ℚ) ^ 2
    let q := (n : ℚ) * coeff (n - 1) (expSeries t P) - coeff n (expSeries t P) / t
    q ≠ 0 → 2 * (padicValNat p n : ℤ) - 1 ≤ padicValRat p q := by
  let : Fact p.Prime := ⟨hp⟩
  let t := (n : ℚ) ^ 2
  have hnq : (n : ℚ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have ht : t ≠ 0 := pow_ne_zero _ hnq
  have hs : 1 ≤ padicValNat p n := one_le_padicValNat_of_dvd (by omega) hpn
  have hv : padicValRat p t = 2 * (padicValNat p n : ℤ) := by simp [t, padicValRat.pow]
  have htval : 1 ≤ padicValRat p t := by rw [hv]; omega
  have ha := exp_prefix_bound p hp t ht htval P hP0 hP (n - 1) (by omega)
    1 (Or.inl rfl) (by
      intro j hj
      interval_cases j
      simp [show n - 1 ≠ 0 by omega])
  have hb := exp_prefix_bound p hp t ht htval P hP0 hP n (by omega)
    2 (Or.inr rfl) (by
      intro j hj
      interval_cases j
      · simp [show n ≠ 0 by omega]
      · simpa using hPn)
  change (n : ℚ) * coeff (n - 1) (expSeries t P) - coeff n (expSeries t P) / t ≠ 0 → _
  rw [sub_eq_add_neg]
  apply valuation_add_bound
  · intro h
    have ha0 := right_ne_zero_of_mul h
    have ha' := ha ha0
    rw [padicValRat.mul hnq ha0, padicValRat.of_nat]
    norm_num at ha'
    omega
  · intro h
    have hb0 : coeff n (expSeries t P) ≠ 0 := by
      intro hz
      simp [hz] at h
    have hb' := hb hb0
    rw [padicValRat.neg, padicValRat.div hb0 ht]
    norm_num at hb'
    omega

private theorem source_integral (F : PowerSeries ℚ) (hF : IsSource F) :
    ∀ n : ℕ, ∃ z : ℤ, coeff n F = (z : ℚ) := by
  classical
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn0 : n = 0
    · subst n
      exact ⟨0, by simpa [coeff_zero_eq_constantCoeff] using hF.1⟩
    have hn : 1 ≤ n := by omega
    have hnq : (n : ℚ) ≠ 0 := by exact_mod_cast hn0
    by_contra hbad
    have hd : (coeff n F).den ≠ 1 := by
      intro hd
      exact hbad ⟨(coeff n F).num, (Rat.den_eq_one_iff _).mp hd |>.symm⟩
    obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hd
    let : Fact p.Prime := ⟨hp⟩
    have hc : coeff n F ≠ 0 := by
      intro hc
      exact hbad ⟨0, by simpa using hc⟩
    let a : ℕ → ℤ := fun j => if hj : j < n then Classical.choose (ih j hj) else 0
    let P := prefixSeries n a
    have hP0 : constantCoeff P = 0 := by simp [P, prefixSeries]
    have hPn : coeff n P = 0 := by simp [P, prefixSeries]
    have hPF : Agree n P F := by
      intro j hj
      by_cases hj0 : j = 0
      · subst j
        simpa [coeff_zero_eq_constantCoeff, hP0] using hF.1.symm
      · have hz : coeff j F = (a j : ℚ) := by
          simp only [a, dite_eq_left hj]
          exact Classical.choose_spec (ih j hj)
        simpa [P, prefixSeries, hj, Nat.pos_of_ne_zero hj0] using hz.symm
    have hFP : Agree n F P := fun j hj => (hPF j hj).symm
    let t := (n : ℚ) ^ 2
    have hres := expSeries_residual hn t hF.1 hP0 hFP
    have hprev := expSeries_agree t hF.1 hP0 hFP (n - 1) (by omega)
    have hrec := hF.2 n hn
    change coeff n (expSeries t F) = _ at hrec
    change _ = coeff (n - 1) (expSeries t P) at hprev
    have hr : coeff n (expSeries t P) - (n : ℚ) ^ 3 * coeff (n - 1) (expSeries t P) =
        -(t * coeff n F) := by
      rw [hPn, mul_zero, sub_zero] at hres
      rw [show (n : ℚ) ^ 2 = t from rfl, hprev] at hrec
      linear_combination -hres + hrec
    have hlocal : IsRIntegralRat p (coeff n F) := by
      apply (localRat_iff_val_nonneg p hp _).mpr
      by_cases hpn : p ∣ n
      · have hn2 : 2 ≤ n := by
          have h := Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hpn
          exact hp.two_le.trans h
        have hP : IsRIntegralPS p P := by
          intro j
          by_cases hj : 0 < j ∧ j < n <;> simp [P, prefixSeries, hj, IsRIntegralRat]
        have hsolve : coeff n F = (n : ℚ) * coeff (n - 1) (expSeries t P) -
            coeff n (expSeries t P) / t := by
          have ht : t ≠ 0 := pow_ne_zero _ hnq
          field_simp
          dsimp [t] at hr ⊢
          linear_combination hr
        have hv := dividing_prime_bound p hp hn2 hpn hP0 hPn hP (hsolve ▸ hc)
        rw [← hsolve] at hv
        have hs := one_le_padicValNat_of_dvd hn0 hpn
        omega
      · have hlower : ∀ f : ℕ, 1 ≤ f → f < n →
            let H := (exp ℚ).subst (C ((f : ℚ) ^ 2) * prefixSeries n a)
            coeff f H = (f : ℚ) ^ 3 * coeff (f - 1) H := by
          intro f hf hfn
          have he := expSeries_agree ((f : ℚ) ^ 2) hP0 hF.1 hPF
          change coeff f (expSeries ((f : ℚ) ^ 2) P) =
            (f : ℚ) ^ 3 * coeff (f - 1) (expSeries ((f : ℚ) ^ 2) P)
          rw [he f hfn, he (f - 1) (by omega)]
          exact hF.2 f hf
        have hv := MarkedAssemblyExtraMarker.signed_prefix_residual_local_integral
          2 n a hn p hp hpn hlower
        change 0 ≤ padicValRat p (coeff n (expSeries t P) -
          (n : ℚ) ^ 3 * coeff (n - 1) (expSeries t P)) at hv
        rw [hr, padicValRat.neg, padicValRat.mul (pow_ne_zero _ hnq) hc] at hv
        simpa [padicValRat.pow, padicValNat.eq_zero_of_not_dvd hpn] using hv
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
  simpa only [show (n : ℚ) ^ 2 = ((n ^ 2 : ℕ) : ℚ) by simp,
    expSeries_nat (logOf B) hz, expSeries_log hB.1] using hB.2 n hn

/-- The complete A300593 integrality assertion and the unique normalized A300592 companion. -/
theorem result :
    (∃! F : PowerSeries ℚ, IsSource F) ∧
    ∀ F : PowerSeries ℚ, IsSource F →
      (∀ m : ℕ, ∃ z : ℤ, coeff m F = (z : ℚ)) ∧
      IsCompanion (expSeries 1 F) ∧ logOf (expSeries 1 F) = F ∧
      (∀ n : ℕ, expSeries ((n : ℚ) ^ 2) F = expSeries 1 F ^ (n ^ 2)) ∧
      (∀ B : PowerSeries ℚ, IsCompanion B → B = expSeries 1 F ∧ logOf B = F) ∧
      (mk (fun r => eCoeff (expSeries 1 F) r / (r.factorial : ℚ)) = expSeries 1 F) := by
  have hu : ∃! F : PowerSeries ℚ, IsSource F :=
    triangular_exists_unique (fun n => (n : ℚ) ^ 2) (fun n => (n : ℚ) ^ 3)
      (fun n hn => pow_ne_zero _ (by exact_mod_cast (show n ≠ 0 by omega)))
  refine ⟨hu, fun F hF => ⟨source_integral F hF, source_to_companion hF,
    log_expSeries hF.1, ?_, ?_, ?_⟩⟩
  · intro n
    have he := expSeries_nat F hF.1 (n ^ 2)
    exact_mod_cast he
  · intro B hB
    obtain ⟨G, hG, huniq⟩ := hu
    have he : logOf B = F :=
      (huniq (logOf B) (companion_to_source hB)).trans (huniq F hF).symm
    exact ⟨by rw [← he, expSeries_log hB.1], he⟩
  · ext r
    simp [eCoeff, Nat.factorial_ne_zero]

end D5.S1.Recurrence.Algebraic.HannaA300593Integrality
