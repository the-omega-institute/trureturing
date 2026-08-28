/- GID: D5/S3/Analytic/Dilation/GoldenUnitZetaReflection
   generality: I
   mirror-B: D5/B/S3/Analytic/Dilation/GoldenUnitZetaReflection
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Golden-unit lattice conjugation reflects the flow and joins its regulator period. -/

import D5.S3.Analytic.Dilation.GoldenUnitZetaPeriodicity

/- Library-search audit trail (2026-08-28):
   * Current-tree searches for golden-unit zeta reflection and conjugate
     reindexing found no exact D5 theorem.
   * The exact period clause is imported from
     `GoldenUnitZetaPeriodicity.golden_unit_zeta_periodicity`; its carrier and
     local constructions are reused verbatim rather than wrapped in new defs.
   * Pinned Mathlib supplies `Equiv.subtypeEquiv`, `Equiv.tsum_eq`, and the
     golden-ratio conjugacy identity used for the new reflection clause. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Analytic.Dilation.GoldenUnitZetaReflection

open scoped goldenRatio

noncomputable section

/-- On the coefficient lattice for `Z[phi]`, conjugation is the involution
`(a,b) ↦ (a+b,-b)`. It exchanges the two real embeddings, so the anisotropic
zeta is even in its flow parameter. Together with the imported regulator
period, this exposes the reflection and translation generators publicly. -/
theorem golden_unit_zeta_reflection :
    let sigmaPlus : Int × Int -> Real := fun alpha =>
      (alpha.1 : Real) + (alpha.2 : Real) * Real.goldenRatio
    let sigmaMinus : Int × Int -> Real := fun alpha =>
      (alpha.1 : Real) + (alpha.2 : Real) * Real.goldenConj
    let anisotropicForm : Real -> Int × Int -> Real := fun eta alpha =>
      Real.exp eta * sigmaPlus alpha ^ 2 +
        Real.exp (-eta) * sigmaMinus alpha ^ 2
    let goldenUnitZeta : Complex -> Real -> Complex := fun s eta =>
      ∑' alpha : {alpha : Int × Int // alpha ≠ 0},
        (anisotropicForm eta alpha : Complex) ^ (-s)
    (∀ (s : Complex) (eta : Real),
        goldenUnitZeta s eta = goldenUnitZeta s (-eta)) ∧
      (∀ (s : Complex) (eta : Real),
        goldenUnitZeta s (eta + 2 * Real.log Real.goldenRatio) =
          goldenUnitZeta s eta) := by
  dsimp only
  constructor
  · intro s eta
    let conjugatePair : Int × Int -> Int × Int := fun alpha =>
      (alpha.1 + alpha.2, -alpha.2)
    have conjugatePair_involutive : Function.Involutive conjugatePair := by
      rintro ⟨a, b⟩
      simp [conjugatePair]
    have conjugatePair_bijective : Function.Bijective conjugatePair :=
      conjugatePair_involutive.bijective
    let conjugation : Int × Int ≃ Int × Int :=
      Equiv.ofBijective conjugatePair conjugatePair_bijective
    have conjugation_apply (alpha : Int × Int) :
        conjugation alpha = conjugatePair alpha := by
      rfl
    have conjugation_zero : conjugation (0 : Int × Int) = 0 := by
      rfl
    let conjugationNonzero : {alpha : Int × Int // alpha ≠ 0} ≃
        {alpha : Int × Int // alpha ≠ 0} :=
      conjugation.subtypeEquiv fun alpha => by
        rw [ne_eq, ne_eq]
        constructor
        · intro hAlpha hConj
          apply hAlpha
          exact conjugation.injective (hConj.trans conjugation_zero.symm)
        · intro hConj hAlpha
          apply hConj
          simpa [hAlpha] using conjugation_zero
    have conjugationNonzero_apply
        (alpha : {alpha : Int × Int // alpha ≠ 0}) :
        (conjugationNonzero alpha).1 = conjugation alpha.1 := by
      rfl
    let sigmaPlus : Int × Int -> Real := fun alpha =>
      (alpha.1 : Real) + (alpha.2 : Real) * Real.goldenRatio
    let sigmaMinus : Int × Int -> Real := fun alpha =>
      (alpha.1 : Real) + (alpha.2 : Real) * Real.goldenConj
    let anisotropicForm : Real -> Int × Int -> Real := fun flow alpha =>
      Real.exp flow * sigmaPlus alpha ^ 2 +
        Real.exp (-flow) * sigmaMinus alpha ^ 2
    let summand : Real -> {alpha : Int × Int // alpha ≠ 0} -> Complex :=
      fun flow alpha => (anisotropicForm flow alpha : Complex) ^ (-s)
    change (∑' alpha, summand eta alpha) = ∑' alpha, summand (-eta) alpha
    have plus_conjugate (alpha : Int × Int) :
        sigmaPlus (conjugation alpha) = sigmaMinus alpha := by
      simp only [sigmaPlus, sigmaMinus]
      rw [conjugation_apply]
      simp only [conjugatePair]
      push_cast
      linear_combination (alpha.2 : Real) *
        Real.goldenRatio_add_goldenConj
    have minus_conjugate (alpha : Int × Int) :
        sigmaMinus (conjugation alpha) = sigmaPlus alpha := by
      simp only [sigmaPlus, sigmaMinus]
      rw [conjugation_apply]
      simp only [conjugatePair]
      push_cast
      linear_combination (alpha.2 : Real) *
        Real.goldenRatio_add_goldenConj
    have form_conjugate (alpha : Int × Int) :
        anisotropicForm (-eta) (conjugation alpha) =
          anisotropicForm eta alpha := by
      simp only [anisotropicForm]
      rw [plus_conjugate, minus_conjugate]
      ring_nf
    have summand_reflection
        (alpha : {alpha : Int × Int // alpha ≠ 0}) :
        summand eta alpha = summand (-eta) (conjugationNonzero alpha) := by
      simp only [summand]
      rw [conjugationNonzero_apply, form_conjugate]
    calc
      (∑' alpha, summand eta alpha) =
          ∑' alpha, summand (-eta) (conjugationNonzero alpha) :=
        tsum_congr summand_reflection
      _ = ∑' alpha, summand (-eta) alpha :=
        conjugationNonzero.tsum_eq (summand (-eta))
  · exact
      D5.S3.Analytic.Dilation.GoldenUnitZetaPeriodicity.golden_unit_zeta_periodicity

#print axioms golden_unit_zeta_reflection

end

end D5.S3.Analytic.Dilation.GoldenUnitZetaReflection
