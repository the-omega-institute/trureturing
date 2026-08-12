/- GID: D5/S3/Constants/SturmianDirichletValue
   generality: G
   mirror-B: D5/B/S3/Constants/SturmianDirichletValue
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The source value equals its golden-ratio and cotangent-constant expression. -/

/- Library-search audit trail (2026-08-12):
   * `Mathlib.NumberTheory.Real.GoldenRatio` defines `Real.goldenRatio` as
     `(1 + Real.sqrt 5) / 2`; this module imports and reuses that definition.
   * Searches for the coefficient patterns `27, 13` and `57, 25` found no
     matching declaration in pinned Mathlib or in D5.
-/

import Mathlib.NumberTheory.Real.GoldenRatio

namespace D5.S3.Constants.SturmianDirichletValue

/-- The exact real value assigned to the source's Sturmian-Dirichlet constant. -/
noncomputable def sturmianDirichletValue : Real :=
  (27 - 13 * Real.sqrt 5) / 24

/-- The exact real value assigned to the source's twisted cotangent constant. -/
noncomputable def twistedCotangentConstant : Real :=
  (57 - 25 * Real.sqrt 5) / 24

/-- The exact Sturmian-Dirichlet value is the golden ratio minus seven fourths,
with the twisted cotangent constant added. -/
theorem sturmian_dirichlet_value_eq :
    sturmianDirichletValue =
      Real.goldenRatio - 7 / 4 + twistedCotangentConstant := by
  unfold sturmianDirichletValue twistedCotangentConstant Real.goldenRatio
  ring

/- Changing one numerator coefficient breaks the audited identity. -/
example :
    Ne sturmianDirichletValue
      (Real.goldenRatio - 7 / 4 + (58 - 25 * Real.sqrt 5) / 24) := by
  rw [sturmian_dirichlet_value_eq]
  unfold twistedCotangentConstant
  intro h
  have : (0 : Real) = 1 := by linarith
  norm_num at this

#print axioms sturmian_dirichlet_value_eq

end D5.S3.Constants.SturmianDirichletValue
