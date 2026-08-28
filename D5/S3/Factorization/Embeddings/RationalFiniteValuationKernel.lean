/- GID: D5/S3/Factorization/Embeddings/RationalFiniteValuationKernel
   generality: G
   mirror-B: D5/B/S3/Factorization/Embeddings/RationalFiniteValuationKernel
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Finite rational prime coordinates leave exactly a sign ambiguity. -/

import D5.S3.Factorization.PositiveRationalGroup
import Mathlib.Data.Sign.Basic

/- Library-search audit trail (2026-08-26):
   * The frozen `prime_valuation_observers_faithful` theorem concerns fractional
     ideals, not nonzero rationals, so it is not an exact bind.
   * Repository body-shape searches for a rational absolute-value unit mapped
     through `primeExponentEquivPositiveRational.symm` found no existing profile.
   * Pinned Mathlib's `Rat.nnabs`, `abs_eq_abs`, and `SignType.sign` are exact
     primitive hits. The repository's canonical signed-prime equivalence is
     applied directly; no new `def` or `abbrev` is introduced. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Factorization.Embeddings.RationalFiniteValuationKernel

open D5.S3.Factorization.PositiveRationalGroup

/-- The canonical finite-prime ledger of a nonzero rational forgets only its
sign. Its kernel is exactly the two rational units `1` and `-1`, and adjoining
the archimedean sign recovers the rational uniquely. -/
theorem rational_finite_valuation_kernel_and_sign_recovery (x y : ℚˣ) :
    let finiteProfile : ℚˣ → SignedPrimeLedger := fun q =>
      primeExponentEquivPositiveRational.symm
        (Additive.ofMul (Units.mk0 (Rat.nnabs (q : ℚ)) (by
          intro h
          apply q.ne_zero
          have h' := congrArg (fun r : ℚ≥0 => (r : ℚ)) h
          simpa only [Rat.coe_nnabs, NNRat.coe_zero, abs_eq_zero] using h')))
    (finiteProfile x = finiteProfile y →
        (x : ℚ) = (y : ℚ) ∨ (x : ℚ) = -(y : ℚ)) ∧
      (∀ z : ℚˣ, finiteProfile z = 0 ↔
        (z : ℚ) = 1 ∨ (z : ℚ) = -1) ∧
      (finiteProfile x = finiteProfile y →
        SignType.sign (x : ℚ) = SignType.sign (y : ℚ) →
        (x : ℚ) = (y : ℚ)) := by
  let finiteProfile : ℚˣ → SignedPrimeLedger := fun q =>
    primeExponentEquivPositiveRational.symm
      (Additive.ofMul (Units.mk0 (Rat.nnabs (q : ℚ)) (by
        intro h
        apply q.ne_zero
        have h' := congrArg (fun r : ℚ≥0 => (r : ℚ)) h
        simpa only [Rat.coe_nnabs, NNRat.coe_zero, abs_eq_zero] using h')))
  change (finiteProfile x = finiteProfile y →
      (x : ℚ) = (y : ℚ) ∨ (x : ℚ) = -(y : ℚ)) ∧
    (∀ z : ℚˣ, finiteProfile z = 0 ↔
      (z : ℚ) = 1 ∨ (z : ℚ) = -1) ∧
    (finiteProfile x = finiteProfile y →
      SignType.sign (x : ℚ) = SignType.sign (y : ℚ) →
      (x : ℚ) = (y : ℚ))
  have profile_eq_nnabs {a b : ℚˣ} (h : finiteProfile a = finiteProfile b) :
      Rat.nnabs (a : ℚ) = Rat.nnabs (b : ℚ) := by
    change primeExponentEquivPositiveRational.symm _ =
      primeExponentEquivPositiveRational.symm _ at h
    have hadd := primeExponentEquivPositiveRational.symm.injective h
    have hunit := Additive.toMul.injective hadd
    exact congrArg (fun q : PositiveRational => (q : NNRat)) hunit
  have profile_eq_abs {a b : ℚˣ} (h : finiteProfile a = finiteProfile b) :
      |(a : ℚ)| = |(b : ℚ)| := by
    have h' := congrArg (fun r : ℚ≥0 => (r : ℚ)) (profile_eq_nnabs h)
    simpa only [Rat.coe_nnabs] using h'
  have profile_one : finiteProfile (1 : ℚˣ) = 0 := by
    unfold finiteProfile
    rw [← map_zero primeExponentEquivPositiveRational.symm]
    apply congrArg primeExponentEquivPositiveRational.symm
    apply Additive.toMul.injective
    apply Units.ext
    apply Subtype.ext
    change ((Rat.nnabs (1 : ℚ) : ℚ≥0) : ℚ) = 1
    rw [Rat.coe_nnabs]
    norm_num
  constructor
  · intro h
    exact abs_eq_abs.mp (profile_eq_abs h)
  constructor
  · intro z
    constructor
    · intro hz
      exact abs_eq_abs.mp (profile_eq_abs (hz.trans profile_one.symm))
    · rintro (hz | hz)
      · have : z = (1 : ℚˣ) := Units.ext hz
        simpa [this] using profile_one
      · have : z = (-1 : ℚˣ) := Units.ext hz
        subst z
        unfold finiteProfile
        rw [← map_zero primeExponentEquivPositiveRational.symm]
        apply congrArg primeExponentEquivPositiveRational.symm
        apply Additive.toMul.injective
        apply Units.ext
        apply Subtype.ext
        change ((Rat.nnabs (-1 : ℚ) : ℚ≥0) : ℚ) = 1
        rw [Rat.coe_nnabs]
        norm_num
  · intro hprofile hsign
    rcases abs_eq_abs.mp (profile_eq_abs hprofile) with h | h
    · exact h
    · rcases lt_or_gt_of_ne y.ne_zero with hy | hy
      · have hx : 0 < (x : ℚ) := h.symm ▸ neg_pos.mpr hy
        rw [sign_pos hx, sign_neg hy] at hsign
        norm_num at hsign
      · have hx : (x : ℚ) < 0 := h.symm ▸ neg_neg_of_pos hy
        rw [sign_neg hx, sign_pos hy] at hsign
        norm_num at hsign

#print axioms rational_finite_valuation_kernel_and_sign_recovery

end D5.S3.Factorization.Embeddings.RationalFiniteValuationKernel
