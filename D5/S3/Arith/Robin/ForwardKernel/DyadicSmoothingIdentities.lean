/- GID: D5/S3/Arith/Robin/ForwardKernel/DyadicSmoothingIdentities
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/ForwardKernel/DyadicSmoothingIdentities
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Dyadic smoothing blocks and residuals are averages of fixed increments. -/

import D5.S3.Arith.Robin.ForwardKernel.AveragingRegularity

/-! Exact algebraic identities for double forward averages. -/

namespace D5.S3.Arith.Robin.ForwardKernel.DyadicSmoothingIdentities

open Set MeasureTheory
open VarianceTransferDefs CrossExponentDefs AveragingRegularity

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private lemma shifted_integrable {E : ℝ → ℝ}
    (hi : ∀ a b, IntervalIntegrable E volume a b) (x a b : ℝ) :
    IntervalIntegrable (fun r => E (x + r)) volume a b := by
  simpa using (hi (x + a) (x + b)).comp_add_left x

private lemma average_add {f g : ℝ → ℝ} {R : ℝ}
    (hf : ∀ a b, IntervalIntegrable f volume a b)
    (hg : ∀ a b, IntervalIntegrable g volume a b) (x : ℝ) :
    windowAverage R (fun y => f y + g y) x =
      windowAverage R f x + windowAverage R g x := by
  simp only [windowAverage, intervalIntegral.integral_add
    (shifted_integrable hf x 0 R) (shifted_integrable hg x 0 R), add_div]

private lemma average_sub {f g : ℝ → ℝ} {R : ℝ}
    (hf : ∀ a b, IntervalIntegrable f volume a b)
    (hg : ∀ a b, IntervalIntegrable g volume a b) (x : ℝ) :
    windowAverage R (fun y => f y - g y) x =
      windowAverage R f x - windowAverage R g x := by
  simp only [windowAverage, intervalIntegral.integral_sub
    (shifted_integrable hf x 0 R) (shifted_integrable hg x 0 R), sub_div]

private lemma average_div (f : ℝ → ℝ) (R c x : ℝ) :
    windowAverage R (fun y => f y / c) x = windowAverage R f x / c := by
  simp only [windowAverage, intervalIntegral.integral_div]
  ring

private lemma average_translate (f : ℝ → ℝ) (R u x : ℝ) :
    windowAverage R (fun y => f (y + u)) x = windowAverage R f (x + u) := by
  simp only [windowAverage]
  congr 2
  funext r
  congr 1
  ring

private lemma average_two_scale {E : ℝ → ℝ}
    (hi : ∀ a b, IntervalIntegrable E volume a b) {R : ℝ} (hR : 0 < R) (x : ℝ) :
    windowAverage (2 * R) E x =
      (windowAverage R E x + windowAverage R E (x + R)) / 2 := by
  have hsum := intervalIntegral.integral_add_adjacent_intervals
    (shifted_integrable hi x 0 R) (shifted_integrable hi x R (2 * R))
  have ht := intervalIntegral.integral_comp_add_left (fun r => E (x + r)) R
    (a := 0) (b := R)
  simp only [add_zero, show R + R = 2 * R by ring] at ht
  have he : (∫ r in R..2 * R, E (x + r)) =
      ∫ r in (0 : ℝ)..R, E (x + R + r) := by
    rw [← ht]
    congr 1
    funext r
    congr 1
    ring
  rw [he] at hsum
  unfold windowAverage
  rw [← hsum]
  field_simp

private lemma double_increment {E : ℝ → ℝ} (hE : LocallyBoundedMeasurable E)
    {R : ℝ} (hR : 0 < R) (u x : ℝ) :
    doubleAverage R (increment E u) x = doubleAverage R E (x + u) - doubleAverage R E x := by
  have hi := locallyBoundedMeasurable_intervalIntegrable hE
  have he : windowAverage R (increment E u) =
      fun y => windowAverage R E (y + u) - windowAverage R E y := by
    funext y
    change windowAverage R (fun z => E (z + u) - E z) y = _
    rw [average_sub (f := fun z => E (z + u))
      (fun a b => by simpa [add_comm] using shifted_integrable hi u a b) hi,
      average_translate]
  have hc := windowAverage_continuous hE hR
  unfold doubleAverage
  rw [he, average_sub (f := fun y => windowAverage R E (y + u)) (g := windowAverage R E)
    (fun a b => (hc.comp (continuous_id.add continuous_const)).intervalIntegrable a b)
    (fun a b => hc.intervalIntegrable a b), average_translate]

/-- A dyadic smoothing block is a linear combination of double-averaged increments. -/
theorem smoothingBlock_eq_averaged_increments {E : ℝ → ℝ}
    (hE : LocallyBoundedMeasurable E) {R : ℝ} (hR : 0 < R) (x : ℝ) :
    smoothingBlock R E x =
      -(1 / 2 : ℝ) * doubleAverage R (increment E R) x -
        (1 / 4 : ℝ) * doubleAverage R (increment E (2 * R)) x := by
  have hi := locallyBoundedMeasurable_intervalIntegrable hE
  have hc := windowAverage_continuous hE hR
  have he : windowAverage (2 * R) E = fun y =>
      (windowAverage R E y + windowAverage R E (y + R)) / 2 :=
    funext (average_two_scale hi hR)
  have hav (y : ℝ) : windowAverage R (windowAverage (2 * R) E) y =
      (doubleAverage R E y + doubleAverage R E (y + R)) / 2 := by
    rw [he, average_div, average_add (f := windowAverage R E)
      (g := fun y => windowAverage R E (y + R))
      (fun a b => hc.intervalIntegrable a b)
      (fun a b => (hc.comp (continuous_id.add continuous_const)).intervalIntegrable a b),
      average_translate]
    rfl
  have hz : doubleAverage (2 * R) E x =
      (doubleAverage R E x + 2 * doubleAverage R E (x + R) +
        doubleAverage R E (x + 2 * R)) / 4 := by
    unfold doubleAverage
    rw [average_two_scale (fun a b =>
      (windowAverage_continuous hE (by positivity : 0 < 2 * R)).intervalIntegrable a b) hR,
      hav x, hav (x + R), show x + R + R = x + 2 * R by ring]
    dsimp only [doubleAverage]
    ring
  unfold smoothingBlock
  rw [hz, double_increment hE hR, double_increment hE hR]
  ring

end
end D5.S3.Arith.Robin.ForwardKernel.DyadicSmoothingIdentities
