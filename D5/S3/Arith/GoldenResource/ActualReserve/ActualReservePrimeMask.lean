/- GID: D5/S3/Arith/GoldenResource/ActualReserve/ActualReservePrimeMask
   generality: I
   mirror-B: D5/B/S3/Arith/GoldenResource/ActualReserve/ActualReservePrimeMask
   mirror-E: none(waiver:general-real-price)
   anchors: []
   utility: none
   digest: Arbitrary actual prime masks pay the same unrestricted reserve and retain the integer defect. -/

import D5.S3.Arith.GoldenResource.ActualReserve.HarmonicReference
import D5.S3.Arith.GoldenResource.GoldenResourceSupremum
import D5.S3.Arith.GoldenResource.FirstLayerMarginalAntitone
import D5.S3.Arith.GoldenResource5040PriceInterval
import D5.S3.Arith.GoldenFutureExtensionMaximum

/- Original ordinary composition: theory §§87.2–87.4 and Robin Dyadic §481.
   §93.2 is a stronger EXISTING two-candidate producer, not a new discovery.
   The new formal work joins the finite harmonic-reference optimizer to actual
   factorization on referencePrimes union n.primeFactors, retains both slacks,
   and applies the uniform bound to an attained UNRESTRICTED maximum.
   No optimizer support premise, positive n cutoff, distribution assumption,
   selected integer domain, scalar-only witness, or changed judge is used.
   All new public theorem audits remain linked to issue #5214; no registration
   status is asserted without compiled source binding and variation evidence. -/

namespace D5.S3.Arith.GoldenResource.ActualReserve.ActualReservePrimeMask

open Finset
open D5.S3.Arith.GoldenResourceOptimalInteger
open D5.S3.Arith.GoldenLocalThreshold
open D5.S3.Arith.GoldenLayerMarginalDecay
open D5.S3.Arith.GoldenResourceObjectiveFactorization
open D5.S3.Arith.GoldenFutureExtensionMaximum
open D5.S3.Arith.GoldenResource5040PriceInterval
open D5.S3.Arith.GoldenResource.GoldenResourceSupremum
open D5.S3.Arith.GoldenResource.FirstLayerMarginalAntitone
open D5.S3.Arith.GoldenResource.ActualReserve.HarmonicReference

noncomputable section

/-- Arbitrary finite actual primes, with BOTH weak endpoints included. -/
def PrimeMask (x : ℝ) (s : Finset ℕ) : Prop :=
  ∀ p ∈ s, p.Prime ∧ 2 * x ≤ (p : ℝ) ^ 2 ∧ (p : ℝ) + 1 ≤ x

/-- The original first-prefix deficit, aggregated on the actual mask. -/
def maskMass (s : Finset ℕ) : ℝ :=
  ∑ p ∈ s, 1 / (p : ℝ) - Real.log (1 + 1 / (p : ℝ))

/-- No restriction on actual integers; the unit belongs to this supremum. -/
def actualPressure (x : ℝ) : ℝ :=
  sSup {y : ℝ | ∃ n : ℕ, 1 ≤ n ∧ goldenResourceObjective (referencePrice x) n = y}

/-- The actual unrestricted reserve F-M, never a selected optimizer substitute. -/
def actualReserve (x : ℝ) : ℝ := referencePressure x - actualPressure x

/-- The defect of the SAME integer and SAME actual pressure. -/
def actualDefect (x : ℝ) (n : ℕ) : ℝ :=
  actualPressure x - goldenResourceObjective (referencePrice x) n

/-- Exact nonnegative slack for the actual integer on the mask. -/
def maskSlack (x : ℝ) (s : Finset ℕ) (n : ℕ) : ℝ :=
  ∑ p ∈ s, goldenPrimeLocalObjective (referencePrice x) p 1 -
    goldenPrimeLocalObjective (referencePrice x) p (n.factorization p)

/-- The full complement; primes of n beyond the reference support are retained. -/
def complementGap (x : ℝ) (s : Finset ℕ) (n : ℕ) : ℝ :=
  ∑ p ∈ (referencePrimes x ∪ n.primeFactors) \ s,
    referenceObjective x p (referenceCutoff x p) -
      goldenPrimeLocalObjective (referencePrice x) p (n.factorization p)

private theorem mask_subset {x : ℝ} (hx : 1 < x) {s : Finset ℕ}
    (hs : PrimeMask x s) : s ⊆ referencePrimes x := by
  intro p hp
  have h := hs p hp
  exact mem_filter.mpr ⟨mem_Icc.mpr ⟨h.1.two_le,
    (Nat.le_floor_iff (by linarith : 0 ≤ x)).mpr (by linarith [h.2.2])⟩, h.1⟩

private theorem mask_cutoff {x : ℝ} (hx : 1 < x) {p : ℕ} (hp : p.Prime)
    (h2 : 2 * x ≤ (p : ℝ) ^ 2) (h1 : (p : ℝ) + 1 ≤ x) :
    referenceCutoff x p = 1 := by
  have hge : 1 ≤ referenceCutoff x p :=
    (reference_cutoff_spec hx hp 1).mpr (by simpa using (show (p : ℝ) ≤ x by linarith))
  have hlt : ¬ 2 ≤ referenceCutoff x p := by
    intro h
    have hpow := (reference_cutoff_spec hx hp 2).mp h
    linarith
  omega

private theorem mask_thresholds {x : ℝ} (hx : 1 < x) {p : ℕ} (hp : p.Prime)
    (h2 : 2 * x ≤ (p : ℝ) ^ 2) (h1 : (p : ℝ) + 1 ≤ x) :
    goldenLayerMarginal p 2 < referencePrice x ∧
      referencePrice x < goldenLayerMarginal p 1 := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hlp : 0 < Real.log (p : ℝ) := Real.log_pos hp1
  have hx0 : 0 < x := by linarith
  have hlx : 0 < Real.log x := Real.log_pos hx
  have hpx : (p : ℝ) < x := by linarith
  have hlogs : Real.log (p : ℝ) < Real.log x := Real.log_lt_log hp0 hpx
  have he : Real.exp (-1 : ℝ) < 1 := by
    simpa using (Real.exp_lt_exp.mpr (show (-1 : ℝ) < 0 by norm_num))
  have hmono := Real.mul_log_strictMonoOn.monotoneOn
    (he.le.trans (show 1 ≤ 2 * x by linarith))
    (he.le.trans (show 1 ≤ (p : ℝ) ^ 2 by nlinarith)) h2
  rw [Real.log_pow, Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hx0.ne'] at hmono
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hden : x * Real.log x < (p : ℝ) ^ 2 * Real.log p := by
    nlinarith [mul_pos hx0 hlog2]
  constructor
  · apply (golden_layer_marginal_le_inv_pow hp (by norm_num : 1 ≤ 2)).trans_lt
    have harith : (p : ℝ)⁻¹ ^ 2 / Real.log p =
        1 / ((p : ℝ) ^ 2 * Real.log p) := by
      rw [inv_pow]
      field_simp [hp0.ne', hlp.ne'] <;> ring
    rw [harith, referencePrice]
    exact (one_div_lt_one_div (mul_pos (pow_pos hp0 2) hlp)
      (mul_pos hx0 hlx)).mpr hden
  · rw [golden_layer_marginal_one_eq_log_one_add_inv hp]
    apply (lt_div_iff₀ hlp).mpr
    have hinv : 0 < (p : ℝ)⁻¹ := inv_pos.mpr hp0
    have hloglower := Real.lt_log_one_add_of_pos hinv
    have hbound : 1 / ((p : ℝ) + 1) ≤
        2 * (p : ℝ)⁻¹ / ((p : ℝ)⁻¹ + 2) := by
      apply (div_le_div_iff₀ (by positivity : 0 < (p : ℝ) + 1)
        (by positivity : 0 < (p : ℝ)⁻¹ + 2)).mpr
      have hinvp : (p : ℝ)⁻¹ * p = 1 := inv_mul_cancel₀ hp0.ne'
      nlinarith
    have hfirst : 1 / x < Real.log (1 + 1 / (p : ℝ)) := by
      exact (one_div_le_one_div_of_le (by positivity : 0 < (p : ℝ) + 1) h1).trans_lt
        (hbound.trans_lt (by simpa [one_div] using hloglower))
    have hprice : referencePrice x * Real.log p < 1 / x := by
      unfold referencePrice
      have heq : 1 / x = Real.log x / (x * Real.log x) := by
        field_simp [hx0.ne', hlx.ne'] <;> ring
      rw [heq]
      have hrepr : 1 / (x * Real.log x) * Real.log p =
          Real.log p / (x * Real.log x) := by ring
      rw [hrepr]
      exact (div_lt_div_iff_of_pos_right (mul_pos hx0 hlx)).mpr hlogs
    exact hprice.trans hfirst

private theorem mask_local_maximum {x : ℝ} (hx : 1 < x) {p : ℕ} (hp : p.Prime)
    (h2 : 2 * x ≤ (p : ℝ) ^ 2) (h1 : (p : ℝ) + 1 ≤ x) (a : ℕ) :
    goldenPrimeLocalObjective (referencePrice x) p a ≤
      goldenPrimeLocalObjective (referencePrice x) p 1 ∧
    (goldenPrimeLocalObjective (referencePrice x) p a =
      goldenPrimeLocalObjective (referencePrice x) p 1 ↔ a = 1) := by
  have h := mask_thresholds hx hp h2 h1
  exact golden_prime_local_objective_unique_maximal_of_strict_threshold hp
    (referencePrice x) h.1 (Or.inr h.2) a

private theorem mask_local_gap {x : ℝ} (hx : 1 < x) {p : ℕ} (hp : p.Prime)
    (h2 : 2 * x ≤ (p : ℝ) ^ 2) (h1 : (p : ℝ) + 1 ≤ x) (a : ℕ) :
    referenceObjective x p (referenceCutoff x p) -
        goldenPrimeLocalObjective (referencePrice x) p a =
      (1 / (p : ℝ) - Real.log (1 + 1 / (p : ℝ))) +
        (goldenPrimeLocalObjective (referencePrice x) p 1 -
          goldenPrimeLocalObjective (referencePrice x) p a) := by
  have hlp : Real.log (p : ℝ) ≠ 0 := (Real.log_pos (by exact_mod_cast hp.one_lt)).ne'
  have hlocal : goldenPrimeLocalObjective (referencePrice x) p 1 =
      Real.log (1 + 1 / (p : ℝ)) - referencePrice x * Real.log p := by
    rw [local_eq_layer_sum (referencePrice x) hp 1]
    simp only [Icc_self, sum_singleton]
    rw [golden_layer_marginal_one_eq_log_one_add_inv hp]
    field_simp [hlp] <;> ring
  rw [mask_cutoff hx hp h2 h1, hlocal]
  simp [referenceObjective, D5.S3.Arith.GoldenResource.PrefixDeficitKernel.Q, one_div] <;> ring

private theorem kernel_mask_bound {p : ℕ} (hp : p.Prime) :
    1 / (2 * (p : ℝ) * ((p : ℝ) + 1)) ≤
      1 / (p : ℝ) - Real.log (1 + 1 / (p : ℝ)) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hz1 : (p : ℝ)⁻¹ < 1 :=
    (inv_lt_one₀ hp0).mpr (by exact_mod_cast hp.one_lt)
  have h := (D5.S3.Arith.GoldenResource.PrefixDeficitKernel.result 1 (p : ℝ)⁻¹
    (by norm_num) (inv_pos.mpr hp0) hz1).2.2.1
  norm_num [D5.S3.Arith.GoldenResource.PrefixDeficitKernel.D,
    D5.S3.Arith.GoldenResource.PrefixDeficitKernel.Q,
    D5.S3.Arith.GoldenResource.PrefixDeficitKernel.S] at h
  have heq : (p : ℝ)⁻¹ ^ 2 / (2 * (1 + (p : ℝ)⁻¹)) =
      1 / (2 * (p : ℝ) * ((p : ℝ) + 1)) := by
    field_simp [hp0.ne', (show (p : ℝ) + 1 ≠ 0 by positivity)] <;> ring
  simpa only [heq, one_div] using h

/-- Exact all-integer decomposition and both nonnegative remainder sums. -/
theorem actual_reference_gap_decomposition {x : ℝ} (hx : 1 < x)
    (s : Finset ℕ) (hs : PrimeMask x s) {n : ℕ} (hn : 1 ≤ n) :
    referencePressure x - goldenResourceObjective (referencePrice x) n =
      maskMass s + maskSlack x s n + complementGap x s n ∧
    0 ≤ maskSlack x s n ∧ 0 ≤ complementGap x s n ∧
    (∑ p ∈ s, 1 / (2 * (p : ℝ) * ((p : ℝ) + 1))) ≤ maskMass s := by
  classical
  let U := referencePrimes x ∪ n.primeFactors
  have hprime : ∀ p ∈ U, p.Prime := by
    intro p hp
    rcases mem_union.mp hp with hp | hp
    · exact (mem_filter.mp hp).2
    · exact Nat.prime_of_mem_primeFactors hp
  have hsU : s ⊆ U := (mask_subset hx hs).trans subset_union_left
  have hgap : referencePressure x - goldenResourceObjective (referencePrice x) n =
      ∑ p ∈ U, referenceObjective x p (referenceCutoff x p) -
        goldenPrimeLocalObjective (referencePrice x) p (n.factorization p) := by
    rw [reference_pressure_sum_on hx U subset_union_left hprime,
      golden_resource_objective_sum_on (referencePrice x) hn U subset_union_right,
      sum_sub_distrib]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hgap, ← sum_sdiff hsU]
    have hmask : (∑ p ∈ s, referenceObjective x p (referenceCutoff x p) -
        goldenPrimeLocalObjective (referencePrice x) p (n.factorization p)) =
        maskMass s + maskSlack x s n := by
      unfold maskMass maskSlack
      rw [← sum_add_distrib]
      apply sum_congr rfl
      intro p hp
      have h := hs p hp
      exact mask_local_gap hx h.1 h.2.1 h.2.2 (n.factorization p)
    rw [hmask]
    change complementGap x s n + (maskMass s + maskSlack x s n) = _
    ring
  · apply sum_nonneg
    intro p hp
    have h := hs p hp
    exact sub_nonneg.mpr (mask_local_maximum hx h.1 h.2.1 h.2.2 _).1
  · apply sum_nonneg
    intro p hp
    exact sub_nonneg.mpr (actual_local_le_reference_maximum hx
      (hprime p (mem_sdiff.mp hp).1) _)
  · apply sum_le_sum
    intro p hp
    exact kernel_mask_bound (hs p hp).1

/-- The SAME attained unrestricted Res pays every arbitrary mask, and the
    complete integer gap is Res+d with d>=0 for every n>=1, including n=1. -/
theorem actual_reserve_prime_mask {x : ℝ} (hx : 1 < x) (s : Finset ℕ)
    (hs : PrimeMask x s) {n : ℕ} (hn : 1 ≤ n) :
    (∑ p ∈ s, 1 / (2 * (p : ℝ) * ((p : ℝ) + 1))) ≤ maskMass s ∧
    maskMass s ≤ actualReserve x ∧ 0 ≤ actualDefect x n ∧
    referencePressure x -
      (Real.log ((ArithmeticFunction.sigma 1 n : ℝ) / n) - referencePrice x * Real.log n) =
        actualReserve x + actualDefect x n ∧
    maskMass s ≤ actualReserve x + actualDefect x n := by
  have hprice : 0 < referencePrice x :=
    one_div_pos.mpr (mul_pos (by linarith) (Real.log_pos hx))
  obtain ⟨m, _, hm, hmax⟩ := golden_future_extension_maximum_attained hprice (n := 1) le_rfl
  have hgreatest : IsGreatest
      {y : ℝ | ∃ k : ℕ, 1 ≤ k ∧ goldenResourceObjective (referencePrice x) k = y}
      (goldenResourceObjective (referencePrice x) m) := by
    refine ⟨⟨m, hm, rfl⟩, ?_⟩
    rintro y ⟨k, hk, rfl⟩
    have h := hmax k (one_dvd k) hk
    linarith
  have hpressure : actualPressure x = goldenResourceObjective (referencePrice x) m :=
    hgreatest.csSup_eq
  have hgap := actual_reference_gap_decomposition hx s hs hm
  have hres : maskMass s ≤ actualReserve x := by
    unfold actualReserve
    rw [hpressure, hgap.1]
    linarith [hgap.2.1, hgap.2.2.1]
  have hd : 0 ≤ actualDefect x n := by
    unfold actualDefect
    rw [hpressure]
    exact sub_nonneg.mpr (hgreatest.2 ⟨n, hn, rfl⟩)
  refine ⟨hgap.2.2.2, hres, hd, ?_, by linarith⟩
  rw [← golden_resource_sigma_identity (referencePrice x) hn]
  unfold actualReserve actualDefect
  ring

end

#print axioms actual_reference_gap_decomposition
#print axioms actual_reserve_prime_mask

end D5.S3.Arith.GoldenResource.ActualReserve.ActualReservePrimeMask
