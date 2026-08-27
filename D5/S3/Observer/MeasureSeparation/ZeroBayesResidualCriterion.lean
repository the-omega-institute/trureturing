/- GID: D5/S3/Observer/MeasureSeparation/ZeroBayesResidualCriterion
   generality: G
   mirror-B: D5/B/S3/Observer/MeasureSeparation/ZeroBayesResidualCriterion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Equal-prior statistical residual vanishes exactly for mutually singular laws. -/

import Mathlib.MeasureTheory.Measure.MutuallySingular
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/- Library-search audit trail (2026-08-28):
   * Current-tree name and body-shape searches for statistical residual,
     equal-prior Bayes residual, and real mass of the measure infimum found no
     canonical D5 definition or exact zero criterion.
   * `SingularProbabilityPerfectSeparator` supplies one operational direction,
     but does not define the Bayes residual or state the required equivalence.
   * Exact pinned-Mathlib hit `Measure.mutuallySingular_iff_disjoint` identifies
     mutual singularity with measure-lattice disjointness. `disjoint_iff`,
     `measure_univ_eq_zero`, and `measureReal_eq_zero_iff` supply the remaining
     canonical bridges. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Set
open scoped MeasureTheory

namespace D5.S3.Observer.MeasureSeparation.ZeroBayesResidualCriterion

/-- Equal-prior Bayes residual in its canonical common-mass form: one half of
the total mass shared by the two laws. -/
noncomputable def statisticalResidual {Transcript : Type*}
    [MeasurableSpace Transcript] (probabilityX probabilityY : Measure Transcript) : Real :=
  (probabilityX ⊓ probabilityY).real univ / 2

/-- The equal-prior statistical residual is zero exactly when the two
probability laws are mutually singular. -/
theorem statistical_residual_eq_zero_iff_mutually_singular
    {Transcript : Type*} [MeasurableSpace Transcript]
    (probabilityX probabilityY : Measure Transcript)
    [IsProbabilityMeasure probabilityX]
    [IsProbabilityMeasure probabilityY] :
    statisticalResidual probabilityX probabilityY = 0 ↔
      probabilityX ⟂ₘ probabilityY := by
  have hfinite : (probabilityX ⊓ probabilityY) univ ≠ ⊤ :=
    ne_top_of_le_ne_top (measure_ne_top probabilityX univ)
      ((inf_le_left : probabilityX ⊓ probabilityY ≤ probabilityX) univ)
  calc
    statisticalResidual probabilityX probabilityY = 0 ↔
        (probabilityX ⊓ probabilityY).real univ = 0 := by
      simp [statisticalResidual]
    _ ↔ (probabilityX ⊓ probabilityY) univ = 0 :=
      measureReal_eq_zero_iff hfinite
    _ ↔ probabilityX ⊓ probabilityY = 0 := Measure.measure_univ_eq_zero
    _ ↔ Disjoint probabilityX probabilityY := disjoint_iff.symm
    _ ↔ probabilityX ⟂ₘ probabilityY :=
      Measure.mutuallySingular_iff_disjoint.symm

#print axioms statistical_residual_eq_zero_iff_mutually_singular

end D5.S3.Observer.MeasureSeparation.ZeroBayesResidualCriterion
