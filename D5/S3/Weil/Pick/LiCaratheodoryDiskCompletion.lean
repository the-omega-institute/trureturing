/- GID: D5/S3/Weil/Pick/LiCaratheodoryDiskCompletion
   generality: I
   mirror-B: D5/B/S3/Weil/Pick/LiCaratheodoryDiskCompletion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The Li identity includes its disk half-plane map and unit normalization. -/

import D5.S3.Weil.TestFunctions.LiCaratheodoryIdentity

/- Library-search audit trail (2026-09-03):
   * D5 searches for the Li--Caratheodory identity, its value at zero, and the
     Mobius disk-to-half-plane inequality found the frozen local identity and
     first-coefficient endpoint modules, but no owner stating all three clauses.
   * Pinned Mathlib has no exact theorem for the map `z |-> 1 / (1 - z)` from
     the unit disk. It supplies `Complex.inv_re`, `Complex.normSq_pos`, and
     `Complex.sq_norm`, which are used in the direct calculation below.
   * Installed non-Mathlib Lake packages contain no exact matching theorem. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Complex Filter Set
open scoped Topology BigOperators
open D5.S3.Zeros.CompletedZeta
open D5.S3.Weil.TestFunctions.LiCaratheodoryIdentity

namespace D5.S3.Weil.Pick.LiCaratheodoryDiskCompletion

/-- The normalized Li second-difference series has the frozen local
logarithmic-derivative identity and meromorphic continuation. The same public
statement records that its Mobius argument lies to the right of the critical
midline throughout the unit disk and that the constructed series equals one
at the origin. -/
theorem li_caratheodory_disk_completion
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
    ((liCaratheodory =ᶠ[nhds 0] continuation) /\
      MeromorphicOn continuation ({1}ᶜ : Set Complex)) /\
    (∀ z : Complex, ‖z‖ < 1 ->
      (1 / 2 : Real) < (1 / (1 - z)).re) /\
    liCaratheodory 0 = 1 := by
  dsimp only
  refine ⟨li_caratheodory_identity liCoefficient liZero liOnePositive
    keiperLiExpansion, ?_, ?_⟩
  · intro z hz
    have hzNeOne : z ≠ 1 := by
      intro h
      subst z
      norm_num at hz
    have denominatorPositive : 0 < Complex.normSq (1 - z) :=
      Complex.normSq_pos.mpr (sub_ne_zero.mpr hzNeOne.symm)
    have normNonnegative : 0 ≤ ‖z‖ := norm_nonneg z
    have normSquared : ‖z‖ ^ 2 < 1 := by
      nlinarith
    rw [Complex.sq_norm, Complex.normSq_apply] at normSquared
    simp only [one_div, Complex.inv_re]
    rw [lt_div_iff₀ denominatorPositive]
    rw [Complex.normSq_apply]
    simp only [sub_re, one_re, sub_im, one_im, zero_sub]
    nlinarith
  · simp

#print axioms li_caratheodory_disk_completion

end D5.S3.Weil.Pick.LiCaratheodoryDiskCompletion
