/- GID: D5/S3/Fourier/GoldenReductionKernel
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: For 0 < k, the golden sine is nonzero; the frozen reduction identity therefore holds without its sine nonzero premise. -/

import Mathlib
import D5.S3.Fourier.ReductionKernel

/- Provenance: Native proof over pinned mathlib. -/

/- SEARCH RECEIPT:
  * The frozen theorem reused here is
    D5/S3/Fourier/ReductionKernel.lean:34-45, whose conclusion is copied
    character for character below.
  * The zero-set characterization used in Layer 1 is
    .lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Trigonometric/Basic.lean:507-515,
    namely Real.sin_eq_zero_iff with orientation
    (n : ℝ) * Real.pi = x.
  * The literal golden ratio is definitionally Real.goldenRatio at
    .lake/packages/mathlib/Mathlib/NumberTheory/Real/GoldenRatio.lean:36-37,
    and its irrationality is proved at :119-125.
  * The multiplication family in
    .lake/packages/mathlib/Mathlib/NumberTheory/Real/Irrational.lean:296-327
    was enumerated: mul_cases, of_mul_ratCast, mul_ratCast, of_ratCast_mul,
    ratCast_mul, of_mul_intCast, of_intCast_mul, mul_intCast, intCast_mul,
    of_mul_natCast, of_natCast_mul, mul_natCast, and natCast_mul.  The
    selected result is natCast_mul at :326-327, in the order (k : ℝ) * phi.
  * Irrational.ne_int, which supplies the final contradiction, is at
    .lake/packages/mathlib/Mathlib/NumberTheory/Real/Irrational.lean:181-185.
    Nat.ne_of_gt converts 0 < k to k != 0 at the pinned Lean core file
    Init/Data/Nat/Basic.lean:441.
  * Real.pi_ne_zero, used for cancellation, is at
    .lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Trigonometric/Basic.lean:164-166.
    The cancellation lemma mul_left_cancel₀ is at
    .lake/packages/mathlib/Mathlib/Algebra/GroupWithZero/Defs.lean:55-56.
  * Repository search for sin(pi * k * phi) or an equivalent golden-ratio
    sine nonvanishing theorem found no existing discharge.  Nearby search
    hits included generic uses of Real.sin_eq_zero_iff at
    D5/S3/Analytic/LiCausalTrichotomy.lean:561 and
    D5/S3/Fourier/WindowDiffractionExtinction.lean:26,65; neither proves
    this golden-ratio statement.
  * The positive hypothesis 0 < k is load-bearing: it supplies k != 0 to
    natCast_mul, while k = 0 gives sin 0 = 0.
  * Layer 2 derives the frozen theorem's unchanged conclusion for every k > 0
    without requiring a separately supplied sine-nonzero proof.  Stated
    precisely, the frozen form is (for all k) sin(...) != 0 -> C k and this
    form is (for all k) 0 < k -> C k, so the premise is replaced rather than
    deleted; on the natural numbers the two premises coincide, since 0 < k
    gives the sine nonvanishing above and k = 0 makes the sine zero.
-/

namespace D5.S3.Fourier.GoldenReductionKernel

theorem golden_sin_ne_zero (k : ℕ) (hk : 0 < k) :
    Real.sin (Real.pi * (k : ℝ) * ((1 + Real.sqrt 5) / 2)) ≠ 0 := by
  intro hs
  rcases Real.sin_eq_zero_iff.mp hs with ⟨n, hn⟩
  have hn' : Real.pi * (n : ℝ) =
      Real.pi * ((k : ℝ) * Real.goldenRatio) := by
    simpa [Real.goldenRatio, mul_assoc, mul_left_comm, mul_comm] using hn
  have hnk : (n : ℝ) = (k : ℝ) * Real.goldenRatio :=
    mul_left_cancel₀ Real.pi_ne_zero hn'
  have hirr : Irrational ((k : ℝ) * Real.goldenRatio) :=
    Real.goldenRatio_irrational.natCast_mul (Nat.ne_of_gt hk)
  exact hirr.ne_int n hnk.symm

theorem reduction_kernel_golden_unconditional (k : ℕ) (hk : 0 < k) :
    Real.cos (4 * Real.pi * (k : ℝ) * ((1 + Real.sqrt 5) / 2)) *
        (Real.cos (Real.pi * (k : ℝ) * ((1 + Real.sqrt 5) / 2)) /
          Real.sin (Real.pi * (k : ℝ) * ((1 + Real.sqrt 5) / 2))) =
      Real.cos (Real.pi * (k : ℝ) * ((1 + Real.sqrt 5) / 2)) /
          Real.sin (Real.pi * (k : ℝ) * ((1 + Real.sqrt 5) / 2)) -
        2 * Real.sin (2 * Real.pi * (k : ℝ) * ((1 + Real.sqrt 5) / 2)) -
        Real.sin (4 * Real.pi * (k : ℝ) * ((1 + Real.sqrt 5) / 2)) := by
  exact ReductionKernel.reduction_kernel_golden k (golden_sin_ne_zero k hk)

#print axioms golden_sin_ne_zero
#print axioms reduction_kernel_golden_unconditional

end D5.S3.Fourier.GoldenReductionKernel
