/- GID: D5/S3/Weil/TestFunctions/LiCaratheodoryIdentity
   generality: I
   mirror-B: D5/B/S3/Weil/TestFunctions/LiCaratheodoryIdentity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Li curvature has the completed-zeta logarithmic derivative continuation. -/

import D5.S3.Zeros.CompletedZeta
import Mathlib.Analysis.Meromorphic.IsolatedZeros
import Mathlib.Analysis.Calculus.LogDeriv

/- Library-search audit trail (2026-09-03):
   * D5 name searches for Li--Caratheodory, Keiper--Li, Li coefficients,
     second differences, and logarithmic derivatives found no exact owner.
   * D5 body-shape searches for shifted coefficient sequences, second
     differences, and derivative quotients found the adjacent
     `LiCurvatureCriterion`, `LiCurvatureFourierRepresentation`,
     `FirstLiCoefficientNormalization`, and `XiLogDeriv` modules, but no
     generating-function identity. The canonical `xiReading` is reused here.
   * Pinned Mathlib has no exact Li--Caratheodory theorem. It supplies
     `logDeriv`, `hasSum_nat_add_iff'`, the `HasSum` ring operations, and
     meromorphic composition with an analytic map, all used below.
   * Installed non-Mathlib Lake packages contain no exact matching theorem. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Complex Filter Set
open scoped Topology BigOperators
open D5.S3.Zeros.CompletedZeta

namespace D5.S3.Weil.TestFunctions.LiCaratheodoryIdentity

/-- The standard local generating law for a real Li coefficient sequence
turns its normalized second-difference series into the logarithmic derivative
of the canonical completed-zeta reading. The right side is the meromorphic
continuation of that local germ on the plane punctured at the Mobius pole. -/
theorem li_caratheodory_identity
    (liCoefficient : Nat -> Real)
    (liZero : liCoefficient 0 = 0)
    (liOnePositive : 0 < liCoefficient 1)
    (keiperLiExpansion : ∀ᶠ z in nhds (0 : Complex),
      HasSum (fun n : Nat => (liCoefficient (n + 1) : Complex) * z ^ n)
        ((1 - z) ^ (-2 : Int) *
          logDeriv xiReading (1 / (1 - z)))) :
    let liCaratheodory : Complex -> Complex := fun z =>
      1 + 2 * tsum (fun n : Nat =>
        ((liCoefficient (n + 2) : Complex) -
          2 * (liCoefficient (n + 1) : Complex) +
          (liCoefficient n : Complex)) /
            (2 * (liCoefficient 1 : Complex)) * z ^ (n + 1))
    let continuation : Complex -> Complex := fun z =>
      (1 / (liCoefficient 1 : Complex)) *
        logDeriv xiReading (1 / (1 - z))
    (liCaratheodory =ᶠ[nhds 0] continuation) /\
      MeromorphicOn continuation ({1}ᶜ : Set Complex) := by
  dsimp only
  constructor
  · have nearOne : ∀ᶠ z : Complex in nhds 0, z ≠ 1 :=
      eventually_ne_nhds (by norm_num)
    filter_upwards [keiperLiExpansion, nearOne] with z expansion hz
    let a : Nat -> Complex := fun n => (liCoefficient (n + 1) : Complex) * z ^ n
    let generator : Complex :=
      (1 - z) ^ (-2 : Int) * logDeriv xiReading (1 / (1 - z))
    have expansion' : HasSum a generator := by
      simpa only [a, generator] using expansion
    have next : HasSum (fun n => a (n + 1)) (generator - a 0) :=
      by simpa [Finset.sum_range_succ] using (hasSum_nat_add_iff' 1).2 expansion'
    have current : HasSum (fun n => 2 * z * a n) (2 * z * generator) :=
      expansion'.mul_left (2 * z)
    have previousTail :
        HasSum (fun n => (z ^ 2) * a n) (z ^ 2 * generator) :=
      expansion'.mul_left (z ^ 2)
    let previous : Nat -> Complex := fun n => (liCoefficient n : Complex) * z ^ (n + 1)
    have previousSum : HasSum previous (z ^ 2 * generator) := by
      have previousTail' :
          HasSum (fun n => previous (n + 1)) (z ^ 2 * generator) := by
        convert previousTail using 1
        funext n
        simp only [previous, a]
        rw [pow_succ, pow_succ]
        ring
      apply (hasSum_nat_add_iff' 1).1
      simpa [previous, liZero, Finset.sum_range_succ] using previousTail'
    have curvatureNumerator :
        HasSum (fun n : Nat =>
          ((liCoefficient (n + 2) : Complex) -
            2 * (liCoefficient (n + 1) : Complex) +
            (liCoefficient n : Complex)) * z ^ (n + 1))
          ((1 - z) ^ 2 * generator - (liCoefficient 1 : Complex)) := by
      have combined := (next.sub current).add previousSum
      have combined' : HasSum (fun n : Nat =>
          ((liCoefficient (n + 2) : Complex) -
            2 * (liCoefficient (n + 1) : Complex) +
            (liCoefficient n : Complex)) * z ^ (n + 1))
          (generator - a 0 - 2 * z * generator + z ^ 2 * generator) := by
        apply HasSum.congr_fun combined
        intro n
        simp only [a, previous]
        rw [pow_succ]
        ring
      have limitIdentity :
          generator - a 0 - 2 * z * generator + z ^ 2 * generator =
            (1 - z) ^ 2 * generator - (liCoefficient 1 : Complex) := by
        simp only [a, pow_zero, mul_one]
        ring
      rw [limitIdentity] at combined'
      exact combined'
    have liOneNe : (liCoefficient 1 : Complex) ≠ 0 := by
      exact_mod_cast liOnePositive.ne'
    have normalized := curvatureNumerator.mul_left
      (1 / (2 * (liCoefficient 1 : Complex)))
    have curvatureSum :
        HasSum (fun n : Nat =>
          ((liCoefficient (n + 2) : Complex) -
            2 * (liCoefficient (n + 1) : Complex) +
            (liCoefficient n : Complex)) /
              (2 * (liCoefficient 1 : Complex)) * z ^ (n + 1))
          ((1 / (2 * (liCoefficient 1 : Complex))) *
            ((1 - z) ^ 2 * generator - (liCoefficient 1 : Complex))) := by
      apply HasSum.congr_fun normalized
      intro n
      field_simp [liOneNe]
    rw [curvatureSum.tsum_eq]
    dsimp only [generator]
    rw [zpow_neg, zpow_ofNat]
    field_simp [liOneNe, sub_ne_zero.mpr hz]
    ring
  · intro z hz
    have hz' : z ≠ 1 := by simpa using hz
    have xiMeromorphic : Meromorphic xiReading := fun w =>
      (xi_reading_differentiable.analyticAt w).meromorphicAt
    have mobiusAnalytic : AnalyticAt Complex (fun w : Complex => 1 / (1 - w)) z := by
      exact analyticAt_const.div (analyticAt_const.sub analyticAt_id)
        (sub_ne_zero.mpr hz'.symm)
    have composed : MeromorphicAt
        (logDeriv xiReading ∘ fun w : Complex => 1 / (1 - w)) z :=
      MeromorphicAt.comp_analyticAt (f := logDeriv xiReading)
        (g := fun w : Complex => 1 / (1 - w))
        (xiMeromorphic.logDeriv (1 / (1 - z))) mobiusAnalytic
    have scaled := (MeromorphicAt.const (1 / (liCoefficient 1 : Complex)) z).mul composed
    change MeromorphicAt
      ((fun _ : Complex => 1 / (liCoefficient 1 : Complex)) *
        (logDeriv xiReading ∘ fun w : Complex => 1 / (1 - w))) z
    exact scaled

#print axioms li_caratheodory_identity

end D5.S3.Weil.TestFunctions.LiCaratheodoryIdentity
