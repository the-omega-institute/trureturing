/- GID: D5/S3/Estimation/LeCam
   generality: G
   mirror-B: D5/B/S3/Estimation/LeCam
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Bound the error of every finite two-point test by total variation. -/

/- Library-search audit trail (2026-08-11):
   * Local pinned-mathlib grep terms covered `Le Cam`/`le_cam`/`lecam`, `two-point`,
     hypothesis testing, testing error/risk/bounds, and total variation near test/error/event.
     No statistical Le Cam or two-point testing bound was found. Mathlib's `TwoPointing`
     declarations concern bipointed types and are unrelated.
   * Every declaration-shaped line under `D5/S3` was scanned, followed by the same rearranged
     searches. The only matching declaration is
     `renyi_divergence_two_point_order_two`, an unrelated order-two witness; there is no Le Cam,
     hypothesis-testing, or testing-error declaration.
   * The proof therefore applies the upper-bound half of
     `TotalVariation.Metric.total_variation_eq_sup_event_gap` directly.
-/

import D5.S3.TotalVariation.Metric

/-!
# Le Cam's two-point lemma

The test says "law `q`" on `A`. Its two error masses are therefore the `p`-mass of `A` and the
`q`-mass of `Aᶜ`. The first theorem keeps the common total mass explicit; the usual unit-mass
form and its maximum-error consequence follow immediately.
-/

namespace D5.S3.Estimation.LeCam

open D5.S3.TotalVariation.Metric
open D5.S3.TotalVariation.Pinsker

open Classical in
/-- Common-mass form of Le Cam's two-point sum bound, for an arbitrary test event. -/
theorem le_cam_two_point_sum_mass {ι : Type*} [Fintype ι]
    (p q : ι → ℝ) (A : Finset ι) (hmass : ∑ i, p i = ∑ i, q i) :
    (∑ i, q i) - totalVariation p q ≤
      (∑ i ∈ A, p i) + ∑ i ∈ Aᶜ, q i := by
  have hgap :
      |(∑ i ∈ A, p i) - ∑ i ∈ A, q i| ≤ totalVariation p q :=
    (total_variation_eq_sup_event_gap p q hmass).2 ⟨A, rfl⟩
  have hlower := (abs_le.mp hgap).1
  linarith [Finset.sum_add_sum_compl A q]

open Classical in
/-- Unit-mass form of Le Cam's two-point sum bound, for an arbitrary test event. -/
theorem le_cam_two_point_sum {ι : Type*} [Fintype ι]
    (p q : ι → ℝ) (A : Finset ι)
    (hmass : ∑ i, p i = ∑ i, q i) (hunit : ∑ i, q i = 1) :
    1 - totalVariation p q ≤
      (∑ i ∈ A, p i) + ∑ i ∈ Aᶜ, q i := by
  simpa only [hunit] using le_cam_two_point_sum_mass p q A hmass

open Classical in
/-- At least one of the two error masses is half the Le Cam sum lower bound. -/
theorem le_cam_two_point_max {ι : Type*} [Fintype ι]
    (p q : ι → ℝ) (A : Finset ι)
    (hmass : ∑ i, p i = ∑ i, q i) (hunit : ∑ i, q i = 1) :
    (1 - totalVariation p q) / 2 ≤
      max (∑ i ∈ A, p i) (∑ i ∈ Aᶜ, q i) := by
  have hsum := le_cam_two_point_sum p q A hmass hunit
  have hp :
      (∑ i ∈ A, p i) ≤ max (∑ i ∈ A, p i) (∑ i ∈ Aᶜ, q i) :=
    le_max_left _ _
  have hq :
      (∑ i ∈ Aᶜ, q i) ≤ max (∑ i ∈ A, p i) (∑ i ∈ Aᶜ, q i) :=
    le_max_right _ _
  linarith

/- Identical unit masses make the sum bound tight for every test. -/
example (A : Finset Unit) :
    let p : Unit → ℝ := fun _ ↦ 1
    1 - totalVariation p p =
      (∑ i ∈ A, p i) + ∑ i ∈ Aᶜ, p i := by
  classical
  dsimp
  simpa [totalVariation] using
    (Finset.sum_add_sum_compl A (fun _ : Unit ↦ (1 : ℝ))).symm

/- Disjoint laws and a test that always selects `p` make the sum bound strict. -/
example :
    let p : Bool → ℝ := fun b ↦ if b then 0 else 1
    let q : Bool → ℝ := fun b ↦ if b then 1 else 0
    let A : Finset Bool := ∅
    1 - totalVariation p q <
      (∑ i ∈ A, p i) + ∑ i ∈ Aᶜ, q i := by
  norm_num [totalVariation]

open Classical in
/- Neither reflexivity nor simplification proves the common-mass sum bound. -/
example {ι : Type*} [Fintype ι]
    (p q : ι → ℝ) (A : Finset ι) (hmass : ∑ i, p i = ∑ i, q i) :
    (∑ i, q i) - totalVariation p q ≤
      (∑ i ∈ A, p i) + ∑ i ∈ Aᶜ, q i := by
  fail_if_success rfl
  fail_if_success (simp; done)
  exact le_cam_two_point_sum_mass p q A hmass

open Classical in
/- Neither reflexivity nor simplification proves the unit-mass sum bound. -/
example {ι : Type*} [Fintype ι]
    (p q : ι → ℝ) (A : Finset ι)
    (hmass : ∑ i, p i = ∑ i, q i) (hunit : ∑ i, q i = 1) :
    1 - totalVariation p q ≤
      (∑ i ∈ A, p i) + ∑ i ∈ Aᶜ, q i := by
  fail_if_success rfl
  fail_if_success (simp; done)
  exact le_cam_two_point_sum p q A hmass hunit

open Classical in
/- Neither reflexivity nor simplification proves the maximum-error bound. -/
example {ι : Type*} [Fintype ι]
    (p q : ι → ℝ) (A : Finset ι)
    (hmass : ∑ i, p i = ∑ i, q i) (hunit : ∑ i, q i = 1) :
    (1 - totalVariation p q) / 2 ≤
      max (∑ i ∈ A, p i) (∑ i ∈ Aᶜ, q i) := by
  fail_if_success rfl
  fail_if_success (simp; done)
  exact le_cam_two_point_max p q A hmass hunit

#print axioms le_cam_two_point_sum_mass
#print axioms le_cam_two_point_sum
#print axioms le_cam_two_point_max

end D5.S3.Estimation.LeCam
