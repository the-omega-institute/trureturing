/- GID: D5/S1/Deficit/PullbackReflectionCoordinate
   generality: I
   mirror-B: D5/B/S1/Deficit/PullbackReflectionCoordinate
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Golden-square scaling conjugates the pullback reflection to s maps to one minus s; its structural line is invariant, while its pointwise fixed locus is the single real structural point. -/

import D5.S1.Deficit.Beatty.GoldenSpectralCoordinate

/- Library-search audit trail (2026-09-04):
   * D5 searches for pullback/reflection spellings, `1 / phi ^ 2 - s`,
     conjugacy, invariant lines, and fixed loci found no whole target.
   * `GoldenSpectralCoordinate` owns the public `phi`, `structuralZero`, and
     `goldenNaturalScale` used here. Its line theorem is adjacent but does not
     state the reflection conjugacy or distinguish setwise invariance from
     pointwise fixedness.
   * Pinned Mathlib supplies only field normalization and complex extensionality;
     no packaged theorem states this golden-coordinate calculation. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Deficit.PullbackReflectionCoordinate

open D5.S1.Deficit.Beatty.GoldenObserverRoute
open D5.S1.Deficit.Beatty.GoldenSpectralCoordinate

/-- The affine reflection obtained by pulling `z ↦ 1 - z` back through
golden-square scaling. -/
noncomputable def qcReflection (s : ℂ) : ℂ :=
  (((1 / phi ^ 2 : ℝ) : ℂ) - s)

/-- Golden-square scaling conjugates `qcReflection` to `z ↦ 1 - z`.
The vertical structural line is setwise invariant. Its pointwise fixed locus,
however, is only the real structural point; this corrects the source's use of
"fixed line" for the map `s ↦ 1 / phi^2 - s`. -/
theorem pullback_reflection_coordinate (s : ℂ) :
    goldenNaturalScale (qcReflection s) = 1 - goldenNaturalScale s ∧
      ((qcReflection s).re = structuralZero ↔ s.re = structuralZero) ∧
      (qcReflection s = s ↔ s = (structuralZero : ℂ)) := by
  have hphi : phi ≠ 0 := by
    change Real.goldenRatio ≠ 0
    exact ne_of_gt (lt_trans zero_lt_one Real.one_lt_goldenRatio)
  have hstruct : (1 / phi ^ 2 : ℝ) / 2 = structuralZero := by
    unfold structuralZero
    field_simp [hphi]
  constructor
  · unfold qcReflection goldenNaturalScale
    push_cast
    field_simp [hphi]
  constructor
  · unfold qcReflection
    simp only [Complex.sub_re, Complex.ofReal_re]
    rw [← hstruct]
    constructor <;> intro h <;> linarith
  · constructor
    · intro h
      have hre := congrArg Complex.re h
      have him := congrArg Complex.im h
      simp only [qcReflection, Complex.sub_re, Complex.ofReal_re] at hre
      simp only [qcReflection, Complex.sub_im, Complex.ofReal_im, zero_sub] at him
      apply Complex.ext
      · simp only [Complex.ofReal_re]
        rw [← hstruct]
        linarith
      · simp only [Complex.ofReal_im]
        linarith
    · intro h
      rw [h]
      apply Complex.ext
      · simp only [qcReflection, Complex.sub_re, Complex.ofReal_re]
        rw [← hstruct]
        ring
      · simp only [qcReflection, Complex.sub_im, Complex.ofReal_im, zero_sub, neg_zero]

#print axioms pullback_reflection_coordinate

end D5.S1.Deficit.PullbackReflectionCoordinate
