/- GID: D5/S3/Estimation/LeCamTight
   generality: G
   mirror-B: D5/B/S3/Estimation/LeCamTight
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Exhibit the likelihood comparison test attaining Le Cam's total-error floor. -/

/- Library-search audit trail (2026-08-11):
   * Local pinned-mathlib searches covered `Le Cam`/`le_cam`/`lecam`, two-point testing,
     hypothesis-testing error/risk, and total variation near event/optimality/attainment.
     No statistical Le Cam tightness or finite-event attainment theorem was found. Mathlib's
     `SignedMeasure.totalVariation` is measure-valued and does not supply this finite-real result.
   * Repository searches over every Lean file below `D5/S3` covered tightness, attainment,
     optimal tests, Le Cam/testing error, and every total-variation declaration. They found only
     the lower bound in `Estimation.LeCam` and the two named total-variation characterizations;
     no tightness theorem exists, and `IsGreatest.1` has no consumer below `D5/S3`.
   * The proof uses `total_variation_eq_sum_positive` with `p` and `q` reversed. This retains the
     negative-gap sign needed by the test, whereas extracting an absolute-gap witness from
     `total_variation_eq_sup_event_gap` would require recovering that sign separately.
-/

import D5.S3.Estimation.LeCam

/-!
# Tightness of Le Cam's two-point lemma

The optimal test says "law `q`" exactly where `q` dominates `p`. Equal total mass alone identifies
the resulting negative event gap with minus total variation; nonnegativity is not needed.
-/

namespace D5.S3.Estimation.LeCamTight

open D5.S3.Estimation.LeCam
open D5.S3.TotalVariation.Metric
open D5.S3.TotalVariation.Pinsker

open Classical in
/-- The explicit negative-gap event attains the common-mass Le Cam total-error floor. -/
theorem le_cam_two_point_sum_mass_tight {ι : Type*} [Fintype ι]
    (p q : ι → ℝ) (hmass : ∑ i, p i = ∑ i, q i) :
    (∑ i ∈ Finset.univ.filter (fun i ↦ p i ≤ q i), p i) +
        ∑ i ∈ (Finset.univ.filter (fun i ↦ p i ≤ q i))ᶜ, q i =
      (∑ i, q i) - totalVariation p q := by
  have htv :
      totalVariation p q =
        ∑ i with p i ≤ q i, (q i - p i) := by
    calc
      totalVariation p q = totalVariation q p := total_variation_comm p q
      _ = ∑ i with p i ≤ q i, (q i - p i) :=
        total_variation_eq_sum_positive q p hmass.symm
  rw [Finset.sum_sub_distrib] at htv
  linarith [Finset.sum_add_sum_compl
    (Finset.univ.filter (fun i ↦ p i ≤ q i)) q]

open Classical in
/-- Unit-mass form for the explicit negative-gap test. Together with `le_cam_two_point_sum`,
this equality says that the minimum total error over all finite test events is exactly
`1 - totalVariation p q`. -/
theorem le_cam_two_point_sum_tight {ι : Type*} [Fintype ι]
    (p q : ι → ℝ)
    (hmass : ∑ i, p i = ∑ i, q i) (hunit : ∑ i, q i = 1) :
    (∑ i ∈ Finset.univ.filter (fun i ↦ p i ≤ q i), p i) +
        ∑ i ∈ (Finset.univ.filter (fun i ↦ p i ≤ q i))ᶜ, q i =
      1 - totalVariation p q := by
  simpa only [hunit] using le_cam_two_point_sum_mass_tight p q hmass

/-- On a concrete two-point pair, the positive-gap event is the worst-sign test and the
negative-gap event is the optimal-sign test. Here the common mass is `1`, total variation is
`1 / 2`, and the displayed errors are consequently `3 / 2` and `1 / 2`. -/
theorem two_point_le_cam_sign_check :
    let p : Bool → ℝ := fun b ↦ if b then 1 / 4 else 3 / 4
    let q : Bool → ℝ := fun b ↦ if b then 3 / 4 else 1 / 4
    let Aplus : Finset Bool := Finset.univ.filter (fun i ↦ q i ≤ p i)
    let Aminus : Finset Bool := Finset.univ.filter (fun i ↦ p i ≤ q i)
    ((∑ i ∈ Aplus, p i) + ∑ i ∈ Aplusᶜ, q i =
        (∑ i, q i) + totalVariation p q) ∧
      ((∑ i ∈ Aminus, p i) + ∑ i ∈ Aminusᶜ, q i =
        (∑ i, q i) - totalVariation p q) := by
  norm_num [totalVariation, Finset.sum_filter]

open Classical in
/- Neither reflexivity nor simplification proves common-mass attainment. -/
example {ι : Type*} [Fintype ι]
    (p q : ι → ℝ) (hmass : ∑ i, p i = ∑ i, q i) :
    (∑ i ∈ Finset.univ.filter (fun i ↦ p i ≤ q i), p i) +
        ∑ i ∈ (Finset.univ.filter (fun i ↦ p i ≤ q i))ᶜ, q i =
      (∑ i, q i) - totalVariation p q := by
  fail_if_success rfl
  fail_if_success (simp; done)
  exact le_cam_two_point_sum_mass_tight p q hmass

open Classical in
/- Neither reflexivity nor simplification proves unit-mass attainment. -/
example {ι : Type*} [Fintype ι]
    (p q : ι → ℝ)
    (hmass : ∑ i, p i = ∑ i, q i) (hunit : ∑ i, q i = 1) :
    (∑ i ∈ Finset.univ.filter (fun i ↦ p i ≤ q i), p i) +
        ∑ i ∈ (Finset.univ.filter (fun i ↦ p i ≤ q i))ᶜ, q i =
      1 - totalVariation p q := by
  fail_if_success rfl
  fail_if_success (simp; done)
  exact le_cam_two_point_sum_tight p q hmass hunit

/- Neither reflexivity nor simplification proves the concrete sign check. -/
example :
    let p : Bool → ℝ := fun b ↦ if b then 1 / 4 else 3 / 4
    let q : Bool → ℝ := fun b ↦ if b then 3 / 4 else 1 / 4
    let Aplus : Finset Bool := Finset.univ.filter (fun i ↦ q i ≤ p i)
    let Aminus : Finset Bool := Finset.univ.filter (fun i ↦ p i ≤ q i)
    ((∑ i ∈ Aplus, p i) + ∑ i ∈ Aplusᶜ, q i =
        (∑ i, q i) + totalVariation p q) ∧
      ((∑ i ∈ Aminus, p i) + ∑ i ∈ Aminusᶜ, q i =
        (∑ i, q i) - totalVariation p q) := by
  fail_if_success rfl
  fail_if_success (simp; done)
  exact two_point_le_cam_sign_check

#print axioms le_cam_two_point_sum_mass_tight
#print axioms le_cam_two_point_sum_tight
#print axioms two_point_le_cam_sign_check

end D5.S3.Estimation.LeCamTight
