/- GID: D5/S3/Analytic/Asymptotics/PrimeDeletedLambertMellin
   generality: G
   mirror-B: D5/B/S3/Analytic/Asymptotics/PrimeDeletedLambertMellin
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Mellin transform of a prime-deleted Lambert heat kernel. -/

/- Library-search audit trail (2026-08-28):
* Searches for prime-deleted divisor sums, Lambert heat kernels, and Mellin bridges in `D5`
  found no matching definition or theorem.
* Pinned Mathlib's `hasSum_mellin` supplies the Gamma integral and the integral/sum exchange.
  `LSeries.convolution_def` and `LSeries_convolution'` supply the divisor-antidiagonal and
  product-series bridges. `DirichletCharacter.LFunctionTrivChar_eq_mul_riemannZeta` supplies
  the deleted Euler factor.
* The explicit deletion/trivial-character identification, heat-kernel summability bound, and
  exponent-shift bridge are proved locally below.
-/

import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.NumberTheory.LSeries.MellinEqDirichlet

open scoped LSeries.notation
open Complex LSeries Real Set

namespace D5.S3.Analytic.Asymptotics.PrimeDeletedLambertMellin

noncomputable section

/-- The source weight `d ^ (-r)`, retained exactly when the prime does not divide `d`. -/
noncomputable def primeDeletedDivisorPower (prime exponent divisor : Nat) : Complex :=
  if prime ∣ divisor then 0 else ((divisor : Complex) ^ exponent)⁻¹

/-- The prime-deleted negative-power divisor sum. The antidiagonal lists each divisor once. -/
noncomputable def primeDeletedDivisorSum (prime exponent n : Nat) : Complex :=
  ∑ pair ∈ n.divisorsAntidiagonal, primeDeletedDivisorPower prime exponent pair.1

/-- The source Lambert heat kernel, including only positive indices because its zero coefficient
vanishes. -/
noncomputable def primeDeletedLambertKernel (prime exponent : Nat) (t : Real) : Complex :=
  ∑' n : Nat, primeDeletedDivisorSum prime exponent n * Real.exp (-n * t)

private lemma deleted_power_eq_trivial_character
    (prime exponent divisor : Nat) (hprime : prime.Prime) :
    primeDeletedDivisorPower prime exponent divisor =
      (1 : DirichletCharacter Complex prime) divisor *
        ((divisor : Complex) ^ exponent)⁻¹ := by
  by_cases hdivides : prime ∣ divisor
  · rw [primeDeletedDivisorPower, if_pos hdivides]
    have hnonunit : ¬ IsUnit (divisor : ZMod prime) := by
      rw [ZMod.isUnit_iff_coprime, Nat.coprime_comm,
        hprime.coprime_iff_not_dvd]
      exact not_not.mpr hdivides
    rw [MulChar.map_nonunit _ hnonunit, zero_mul]
  · rw [primeDeletedDivisorPower, if_neg hdivides]
    have hunit : IsUnit (divisor : ZMod prime) := by
      rw [ZMod.isUnit_iff_coprime, Nat.coprime_comm,
        hprime.coprime_iff_not_dvd]
      exact hdivides
    rw [MulChar.one_apply hunit, one_mul]

private lemma deleted_divisor_sum_eq_convolution (prime exponent : Nat) :
    primeDeletedDivisorSum prime exponent =
      primeDeletedDivisorPower prime exponent ⍟ (1 : Nat -> Complex) := by
  funext n
  simp only [primeDeletedDivisorSum, LSeries.convolution_def, Pi.one_apply, mul_one]

private lemma term_deleted_power_eq_shift
    (prime exponent n : Nat) (hprime : prime.Prime) (w : Complex) :
    term (primeDeletedDivisorPower prime exponent) w n =
      term (fun n : Nat => (1 : DirichletCharacter Complex prime) n)
        (w + exponent) n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · rw [term_of_ne_zero hn, term_of_ne_zero hn,
      deleted_power_eq_trivial_character prime exponent n hprime,
      cpow_add _ _ (Nat.cast_ne_zero.mpr hn), cpow_natCast]
    field_simp

private lemma deleted_power_lSeriesSummable
    (prime exponent : Nat) (hprime : prime.Prime) (w : Complex)
    (hshift : 1 < (w + exponent).re) :
    LSeriesSummable (primeDeletedDivisorPower prime exponent) w := by
  refine (DirichletCharacter.LSeriesSummable_of_one_lt_re
    (1 : DirichletCharacter Complex prime) hshift).congr ?_
  exact fun n => (term_deleted_power_eq_shift prime exponent n hprime w).symm

private lemma lSeries_deleted_power
    (prime exponent : Nat) (hprime : prime.Prime) (w : Complex)
    (hshift : 1 < (w + exponent).re) :
    L (primeDeletedDivisorPower prime exponent) w =
      riemannZeta (w + exponent) *
        (1 - (prime : Complex) ^ (-(w + exponent))) := by
  letI : NeZero prime := ⟨hprime.ne_zero⟩
  calc
    L (primeDeletedDivisorPower prime exponent) w =
        L (fun n : Nat => (1 : DirichletCharacter Complex prime) n)
          (w + exponent) := by
      rw [LSeries]
      exact tsum_congr fun n => term_deleted_power_eq_shift prime exponent n hprime w
    _ = DirichletCharacter.LFunctionTrivChar prime (w + exponent) := by
      rw [DirichletCharacter.LFunctionTrivChar,
        DirichletCharacter.LFunction_eq_LSeries _ hshift]
    _ = (∏ q ∈ prime.primeFactors,
          (1 - (q : Complex) ^ (-(w + exponent)))) *
        riemannZeta (w + exponent) :=
      DirichletCharacter.LFunctionTrivChar_eq_mul_riemannZeta
        (by
          intro h
          have hre := congrArg Complex.re h
          simp only [one_re] at hre
          linarith)
    _ = riemannZeta (w + exponent) *
        (1 - (prime : Complex) ^ (-(w + exponent))) := by
      rw [hprime.primeFactors]
      simp [mul_comm]

private lemma fst_injOn_divisorsAntidiagonal (n : Nat) :
    Set.InjOn Prod.fst (n.divisorsAntidiagonal : Set (Nat × Nat)) := by
  intro a ha b hb hab
  apply Prod.ext hab
  have ha_mul := (Nat.mem_divisorsAntidiagonal.mp ha).1
  have hb_mul := (Nat.mem_divisorsAntidiagonal.mp hb).1
  have ha_ne := Nat.left_ne_zero_of_mem_divisorsAntidiagonal ha
  apply Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero ha_ne)
  rw [ha_mul, hab, hb_mul]

private lemma card_divisorsAntidiagonal_le (n : Nat) :
    n.divisorsAntidiagonal.card ≤ n := by
  calc
    n.divisorsAntidiagonal.card =
        (n.divisorsAntidiagonal.image Prod.fst).card :=
      (Finset.card_image_of_injOn (fst_injOn_divisorsAntidiagonal n)).symm
    _ = n.divisors.card := by rw [Nat.image_fst_divisorsAntidiagonal]
    _ ≤ n := Nat.card_divisors_le_self n

private lemma norm_deleted_power_le_one (prime exponent divisor : Nat) :
    ‖primeDeletedDivisorPower prime exponent divisor‖ ≤ 1 := by
  rw [primeDeletedDivisorPower]
  split_ifs with h
  · simp
  · have hn : divisor ≠ 0 := fun hn => h (hn ▸ dvd_zero prime)
    simp only [norm_inv, norm_pow, Complex.norm_natCast]
    have hn_one : (1 : Real) ≤ divisor := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
    exact (inv_le_one₀ (by positivity)).2 (one_le_pow₀ hn_one)

private lemma norm_deleted_divisor_sum_le (prime exponent n : Nat) :
    ‖primeDeletedDivisorSum prime exponent n‖ ≤ n := by
  calc
    ‖primeDeletedDivisorSum prime exponent n‖ ≤
        ∑ pair ∈ n.divisorsAntidiagonal,
          ‖primeDeletedDivisorPower prime exponent pair.1‖ := by
      exact norm_sum_le _ _
    _ ≤ ∑ _pair ∈ n.divisorsAntidiagonal, (1 : Real) := by
      gcongr with pair hpair
      exact norm_deleted_power_le_one prime exponent pair.1
    _ = n.divisorsAntidiagonal.card := by simp
    _ ≤ n := by exact_mod_cast card_divisorsAntidiagonal_le n

private lemma summable_lambert_kernel
    (prime exponent : Nat) {t : Real} (ht : 0 < t) :
    Summable fun n : Nat =>
      primeDeletedDivisorSum prime exponent n * Real.exp (-n * t) := by
  apply Summable.of_norm_bounded (Real.summable_pow_mul_exp_neg_nat_mul 1 ht)
  intro n
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  calc
    ‖primeDeletedDivisorSum prime exponent n‖ * Real.exp (-n * t) ≤
        n * Real.exp (-n * t) :=
      mul_le_mul_of_nonneg_right
        (norm_deleted_divisor_sum_le prime exponent n) (Real.exp_nonneg _)
    _ = (n : Real) ^ (1 : Nat) * Real.exp (-t * n) := by ring_nf

/- **Prime-deleted Lambert--Mellin bridge.** In the source's absolute-convergence region,
the Mellin transform of the explicitly constructed deleted-divisor heat kernel is the product
of the Gamma factor, two zeta factors, and the deleted prime's Euler factor. -/
theorem prime_deleted_lambert_mellin
    (prime exponent : Nat) (hprime : prime.Prime) (hexponent : 1 < exponent)
    (w : Complex) (hw : 1 < w.re) :
    mellin (primeDeletedLambertKernel prime exponent) w =
      Gamma w * riemannZeta w * riemannZeta (w + exponent) *
        (1 - (prime : Complex) ^ (-(w + exponent))) := by
  have hshift : 1 < (w + exponent).re := by
    simp only [add_re, natCast_re]
    have hexponent_pos : (0 : Real) < exponent := by
      exact_mod_cast (lt_trans Nat.zero_lt_one hexponent)
    linarith
  have hdeleted := deleted_power_lSeriesSummable prime exponent hprime w hshift
  have hone : LSeriesSummable (1 : Nat -> Complex) w :=
    LSeriesSummable_one_iff.mpr hw
  have hcoefficient : LSeriesSummable (primeDeletedDivisorSum prime exponent) w := by
    rw [deleted_divisor_sum_eq_convolution]
    exact hdeleted.convolution hone
  have hnorm : Summable fun n : Nat =>
      ‖primeDeletedDivisorSum prime exponent n‖ / (n : Real) ^ w.re := by
    refine hcoefficient.norm.congr fun n => ?_
    rw [norm_term_eq]
    split_ifs with hn
    · subst n
      simp [primeDeletedDivisorSum]
    · rfl
  have hMellin := hasSum_mellin
    (a := primeDeletedDivisorSum prime exponent)
    (p := fun n : Nat => (n : Real))
    (F := primeDeletedLambertKernel prime exponent) (s := w)
    (fun n => by
      rcases n with _ | n
      · exact Or.inl (by simp [primeDeletedDivisorSum])
      · exact Or.inr (by positivity))
    (lt_trans zero_lt_one hw)
    (fun t ht => by
      simpa only [primeDeletedLambertKernel] using
        (summable_lambert_kernel prime exponent ht).hasSum)
    hnorm
  have hMellin' :
      HasSum (fun n : Nat =>
        Gamma w * term (primeDeletedDivisorSum prime exponent) w n)
        (mellin (primeDeletedLambertKernel prime exponent) w) := by
    refine hMellin.congr_fun fun n => ?_
    rcases eq_or_ne n 0 with rfl | hn
    · simp [primeDeletedDivisorSum]
    · rw [term_of_ne_zero hn, mul_div_assoc]
      simp only [ofReal_natCast]
  calc
    mellin (primeDeletedLambertKernel prime exponent) w =
        ∑' n : Nat,
          Gamma w * term (primeDeletedDivisorSum prime exponent) w n :=
      hMellin'.tsum_eq.symm
    _ = Gamma w * L (primeDeletedDivisorSum prime exponent) w := by
      rw [tsum_mul_left]
      rfl
    _ = Gamma w *
        (L (primeDeletedDivisorPower prime exponent) w * L (1 : Nat -> Complex) w) := by
      rw [deleted_divisor_sum_eq_convolution,
        LSeries_convolution' hdeleted hone]
    _ = Gamma w *
        (riemannZeta (w + exponent) *
          (1 - (prime : Complex) ^ (-(w + exponent))) * riemannZeta w) := by
      rw [lSeries_deleted_power prime exponent hprime w hshift,
        LSeries_one_eq_riemannZeta hw]
    _ = Gamma w * riemannZeta w * riemannZeta (w + exponent) *
        (1 - (prime : Complex) ^ (-(w + exponent))) := by ring

#print axioms prime_deleted_lambert_mellin

end

end D5.S3.Analytic.Asymptotics.PrimeDeletedLambertMellin
