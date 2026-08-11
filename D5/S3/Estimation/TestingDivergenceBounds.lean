/- GID: D5/S3/Estimation/TestingDivergenceBounds
   generality: G
   mirror-B: D5/B/S3/Estimation/TestingDivergenceBounds
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Derive and compare divergence lower bounds for finite two-point testing error. -/

/- Library-search audit trail (2026-08-11):
   * Pinned-mathlib declaration searches covered Assouad, minimax, Le Cam, Pinsker,
     Bretagnolle--Huber, and testing-versus-divergence bounds. They found the generic
     `ProbabilityTheory.minimaxRisk` API, but no Assouad declaration or statistical
     testing-versus-divergence lower bound. `Real.sqrt_lt'` supplies the strict square-root
     comparison used below.
   * Declaration-shaped searches over this repository found no Assouad or minimax declaration;
     rearranged testing/divergence and testing/KL searches under `D5/S3` also had no matches.
     The frozen Le Cam, Pinsker, and Bretagnolle--Huber declarations are therefore consumed
     directly.
-/

import D5.S3.Estimation.LeCamTight
import D5.S3.TotalVariation.Bhattacharyya

/-!
# Testing-error bounds from divergence

Both bounds are CHAINED COROLLARIES of frozen results: Le Cam's bound composed with a frozen
TV-vs-divergence inequality. They are NOT new mathematics. `LeCamTight` identifies `1 - TV` as
the optimum; these lower bounds replace TV by a divergence upper bound.

The comparison is the estimation-side payoff: Pinsker's floor is nonpositive from divergence
two onward, whereas the Bretagnolle--Huber floor stays strictly positive for every finite real
divergence.
-/

namespace D5.S3.Estimation.TestingDivergenceBounds

open D5.S3.Divergence.ClassicalDPI
open D5.S3.Estimation.LeCam
open D5.S3.TotalVariation.Bhattacharyya
open D5.S3.TotalVariation.Metric
open D5.S3.TotalVariation.Pinsker

open Classical in
/-- Pinsker composed with Le Cam: every finite test has the displayed divergence error floor. -/
theorem testing_error_pinsker {ι : Type*} [Fintype ι]
    (p q : ι → ℝ) (A : Finset ι)
    (hp : (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1)
    (hq : (∀ i, 0 ≤ q i) ∧ ∑ i, q i = 1)
    (hac : ∀ i, q i = 0 → p i = 0) :
    1 - Real.sqrt (klDivergence p q / 2) ≤
      (∑ i ∈ A, p i) + ∑ i ∈ Aᶜ, q i := by
  have htv :
      totalVariation p q ≤ Real.sqrt (klDivergence p q / 2) := by
    calc
      totalVariation p q = Real.sqrt (totalVariation p q ^ 2) :=
        (Real.sqrt_sq (total_variation_nonneg p q)).symm
      _ ≤ Real.sqrt (klDivergence p q / 2) :=
        Real.sqrt_le_sqrt (by nlinarith [pinsker_inequality p q hp hq hac])
  calc
    1 - Real.sqrt (klDivergence p q / 2) ≤ 1 - totalVariation p q :=
      sub_le_sub_left htv 1
    _ ≤ (∑ i ∈ A, p i) + ∑ i ∈ Aᶜ, q i :=
      le_cam_two_point_sum p q A (hp.2.trans hq.2.symm) hq.2

open Classical in
/-- Bretagnolle--Huber composed with Le Cam: every finite test has the displayed divergence
error floor. -/
theorem testing_error_bretagnolle_huber {ι : Type*} [Fintype ι]
    (p q : ι → ℝ) (A : Finset ι)
    (hp : (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1)
    (hq : (∀ i, 0 ≤ q i) ∧ ∑ i, q i = 1)
    (hac : ∀ i, q i = 0 → p i = 0) :
    1 - Real.sqrt (1 - Real.exp (-klDivergence p q)) ≤
      (∑ i ∈ A, p i) + ∑ i ∈ Aᶜ, q i := by
  calc
    1 - Real.sqrt (1 - Real.exp (-klDivergence p q)) ≤
        1 - totalVariation p q :=
      sub_le_sub_left (bretagnolle_huber p q hp hq hac) 1
    _ ≤ (∑ i ∈ A, p i) + ∑ i ∈ Aᶜ, q i :=
      le_cam_two_point_sum p q A (hp.2.trans hq.2.symm) hq.2

/-- The Pinsker-form floor is nonpositive once the divergence is at least two. -/
theorem pinsker_floor_nonpos_of_two_le (D : ℝ) (hD : 2 ≤ D) :
    1 - Real.sqrt (D / 2) ≤ 0 := by
  apply sub_nonpos.mpr
  rw [← Real.sqrt_one]
  exact Real.sqrt_le_sqrt (by linarith)

/-- The Bretagnolle--Huber-form floor is strictly positive for every finite real divergence. -/
theorem bretagnolle_huber_floor_pos (D : ℝ) :
    0 < 1 - Real.sqrt (1 - Real.exp (-D)) := by
  apply sub_pos.mpr
  exact (Real.sqrt_lt' zero_lt_one).2 (by nlinarith [Real.exp_pos (-D)])

open Classical in
example {ι : Type*} [Fintype ι]
    (p q : ι → ℝ) (A : Finset ι)
    (hp : (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1)
    (hq : (∀ i, 0 ≤ q i) ∧ ∑ i, q i = 1)
    (hac : ∀ i, q i = 0 → p i = 0) :
    1 - Real.sqrt (klDivergence p q / 2) ≤
      (∑ i ∈ A, p i) + ∑ i ∈ Aᶜ, q i := by
  fail_if_success rfl
  fail_if_success (simp; done)
  exact testing_error_pinsker p q A hp hq hac

open Classical in
example {ι : Type*} [Fintype ι]
    (p q : ι → ℝ) (A : Finset ι)
    (hp : (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1)
    (hq : (∀ i, 0 ≤ q i) ∧ ∑ i, q i = 1)
    (hac : ∀ i, q i = 0 → p i = 0) :
    1 - Real.sqrt (1 - Real.exp (-klDivergence p q)) ≤
      (∑ i ∈ A, p i) + ∑ i ∈ Aᶜ, q i := by
  fail_if_success rfl
  fail_if_success (simp; done)
  exact testing_error_bretagnolle_huber p q A hp hq hac

example (D : ℝ) (hD : 2 ≤ D) :
    1 - Real.sqrt (D / 2) ≤ 0 := by
  fail_if_success rfl
  fail_if_success (simp; done)
  exact pinsker_floor_nonpos_of_two_le D hD

example (D : ℝ) :
    0 < 1 - Real.sqrt (1 - Real.exp (-D)) := by
  fail_if_success rfl
  fail_if_success (simp; done)
  exact bretagnolle_huber_floor_pos D

#print axioms testing_error_pinsker
#print axioms testing_error_bretagnolle_huber
#print axioms pinsker_floor_nonpos_of_two_le
#print axioms bretagnolle_huber_floor_pos

end D5.S3.Estimation.TestingDivergenceBounds
