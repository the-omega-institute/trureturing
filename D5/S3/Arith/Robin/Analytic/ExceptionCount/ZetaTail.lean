/- GID: D5/S3/Arith/Robin/Analytic/ExceptionCount/ZetaTail
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/Analytic/ExceptionCount/ZetaTail
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A power-decaying Euler-log tail uniform in the real zeta parameter. -/

import D5.S3.Analytic.Zeta.EulerLogBridge
import D5.S3.Arith.Robin.Analytic.LcmPowerEndpointExpansion

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Real Filter Finset
open scoped Topology BigOperators

namespace D5.S3.Arith.Robin.Analytic.ExceptionCount.ZetaTail

private def eulerLog (κ : ℝ) (p : Nat.Primes) : ℝ :=
  -log (1 - (p.1 : ℝ) ^ (-κ))

private lemma eulerLog_le {κ : ℝ} (hκ : 1 < κ) (p : Nat.Primes) :
    eulerLog κ p ≤ 2 * (p.1 : ℝ) ^ (-κ) := by
  have hp : (1 : ℝ) < p.1 := by exact_mod_cast p.2.one_lt
  have hq : (p.1 : ℝ) ^ (-κ) ≤ (1 / 2 : ℝ) := by
    calc
      _ ≤ (p.1 : ℝ) ^ (-1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hp.le (by linarith)
      _ = (p.1 : ℝ)⁻¹ := Real.rpow_neg_one _
      _ ≤ _ := by
        simpa using inv_anti₀ (by norm_num : (0 : ℝ) < 2)
          (show (2 : ℝ) ≤ p.1 by exact_mod_cast p.2.two_le)
  have hd : 0 < 1 - (p.1 : ℝ) ^ (-κ) := by linarith
  have h := log_le_sub_one_of_pos (inv_pos.mpr hd)
  rw [log_inv] at h
  apply h.trans
  have he : (1 - (p.1 : ℝ) ^ (-κ))⁻¹ - 1 =
      (p.1 : ℝ) ^ (-κ) / (1 - (p.1 : ℝ) ^ (-κ)) := by
    field_simp
    <;> ring
  rw [he, div_le_iff₀ hd]
  nlinarith [Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ p.1) (-κ)]

/-- Uniform decay for the logarithm of the omitted prime Euler factors. -/
theorem uniform_tail {delta : ℝ} (hdelta : 0 < delta) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (κ P : ℝ), 1 + delta ≤ κ → 2 ≤ P →
      log (riemannZeta (κ : ℂ)).re +
        ∑ p ∈ (Ioc 0 ⌊P⌋₊).filter Nat.Prime, log (1 - (p : ℝ) ^ (-κ)) ≤
          C * P ^ (-(delta / 2)) := by
  let a : ℝ := delta / 2
  let w : Nat.Primes → ℝ := fun p => (p.1 : ℝ) ^ (-(1 + a))
  have ha : 0 < a := by dsimp [a]; positivity
  have hw : Summable w := by
    exact (D5.S3.Analytic.ZetaGibbs.summable_real_weight (1 + a) (by linarith)).comp_injective
      Subtype.coe_injective
  refine ⟨2 * ∑' p : Nat.Primes, w p, by positivity, ?_⟩
  intro κ P hκ hP
  have hκ1 : 1 < κ := by linarith
  let F : Finset Nat.Primes := ((Ioc 0 ⌊P⌋₊).filter Nat.Prime).subtype Nat.Prime
  have hsum : Summable (eulerLog κ) :=
    D5.S3.Analytic.Zeta.EulerLogBridge.summable_prime_eulerLog κ hκ1
  have hEuler : (∑' p : Nat.Primes, eulerLog κ p) = log (riemannZeta (κ : ℂ)).re := by
    have hz := congrArg Complex.re
      (D5.S3.Analytic.ZetaGibbs.partition_function_toReal_eq_riemannZeta κ hκ1)
    simp only [Complex.ofReal_re] at hz
    rw [← hz]
    exact (D5.S3.Analytic.Zeta.EulerLogBridge.log_partitionFunction_eq_tsum_prime κ hκ1).symm
  have hfinite : ∑ p ∈ F, eulerLog κ p =
      -∑ p ∈ (Ioc 0 ⌊P⌋₊).filter Nat.Prime, log (1 - (p : ℝ) ^ (-κ)) := by
    change (∑ p ∈
      ((Ioc 0 ⌊P⌋₊).filter Nat.Prime).subtype Nat.Prime,
      -log (1 - (p.1 : ℝ) ^ (-κ))) = _
    simpa only [sum_neg_distrib] using
      (Finset.sum_subtype_of_mem (s := (Ioc 0 ⌊P⌋₊).filter Nat.Prime)
        (p := Nat.Prime) (fun p : ℕ => -log (1 - (p : ℝ) ^ (-κ)))
        (fun p hp => (Finset.mem_filter.mp hp).2))
  have hpoint (p : {p : Nat.Primes // p ∉ F}) :
      eulerLog κ p.1 ≤ (2 * P ^ (-a)) * w p.1 := by
    have hp : (1 : ℝ) < p.1.1 := by exact_mod_cast p.1.2.one_lt
    have hpP : P < (p.1.1 : ℝ) := by
      by_contra! h
      apply p.2
      change p.1 ∈ ((Ioc 0 ⌊P⌋₊).filter Nat.Prime).subtype Nat.Prime
      apply Finset.mem_subtype.mpr
      exact Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨p.1.2.pos, Nat.le_floor h⟩, p.1.2⟩
    have hpow : (p.1.1 : ℝ) ^ (-κ) ≤ P ^ (-a) * w p.1 := by
      calc
        _ ≤ (p.1.1 : ℝ) ^ (-(1 + a) + -a) :=
          Real.rpow_le_rpow_of_exponent_le hp.le (by dsimp [a] at *; linarith)
        _ = w p.1 * (p.1.1 : ℝ) ^ (-a) := by rw [Real.rpow_add (by linarith)]
        _ ≤ w p.1 * P ^ (-a) :=
          mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow_of_nonpos (by linarith : 0 < P) hpP.le (by linarith))
            (by dsimp [w]; positivity)
        _ = _ := mul_comm _ _
    calc
      _ ≤ 2 * (p.1.1 : ℝ) ^ (-κ) := eulerLog_le hκ1 _
      _ ≤ 2 * (P ^ (-a) * w p.1) := mul_le_mul_of_nonneg_left hpow (by norm_num)
      _ = _ := by ring
  have htail : (∑' p : {p : Nat.Primes // p ∉ F}, eulerLog κ p.1) ≤
      (2 * P ^ (-a)) * ∑' p : Nat.Primes, w p := by
    have hsub := hw.subtype (fun p => p ∉ F)
    calc
      _ ≤ ∑' p : {p : Nat.Primes // p ∉ F}, (2 * P ^ (-a)) * w p.1 :=
        (hsum.subtype _).tsum_le_tsum hpoint (hsub.mul_left _)
      _ = (2 * P ^ (-a)) * ∑' p : {p : Nat.Primes // p ∉ F}, w p.1 := tsum_mul_left
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Summable.tsum_subtype_le w (fun p => p ∉ F) (fun p => by dsimp [w]; positivity) hw)
        (by positivity)
  have heq := hsum.sum_add_tsum_subtype_compl F
  rw [hEuler, hfinite] at heq
  dsimp only [a] at htail
  nlinarith [htail]

end D5.S3.Arith.Robin.Analytic.ExceptionCount.ZetaTail
