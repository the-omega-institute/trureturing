/- GID: D5/S3/HomologicalAlgebra/Solid/LocalizationDefect
   generality: G
   mirror-B: D5/B/S3/HomologicalAlgebra/Solid/LocalizationDefect
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Unbounded solid derived construction with exact protected objects and all quasi-isomorphisms. -/

import D5.S3.HomologicalAlgebra.Solid.Colimits
import D5.S3.HomologicalAlgebra.Solid.ComplexAdjunction

/-!
The exact unbounded locality test for the protected solidification reflector.
This constructs the actual two-term defect, not a replacement hypothesis.
Its vanishing detects solid homology in every integer degree.  A universal
local replacement and its comparison with `DerivedCategory Solid` remain
separate mathematical obligations.
-/

noncomputable section
open CategoryTheory Limits MonoidalCategory MonoidalClosed HomologicalComplex

namespace LightCondensed.Solid

/-- The defining map acts on internal Hom degreewise on unbounded complexes. -/
def solidComplexEndomorphism :
    (ihom P).mapHomologicalComplex (.up ℤ) ⟶
      (ihom P).mapHomologicalComplex (.up ℤ) :=
  (MonoidalClosed.pre oneMinusShift).mapHomologicalComplex _

/-- The two-term locality defect applied to an arbitrary unbounded complex. -/
def solidComplexDefect (K : CochainComplex LightCondAb ℤ) :
    CochainComplex LightCondAb ℤ :=
  CochainComplex.mappingCone (solidComplexEndomorphism.app K)

set_option backward.isDefEq.respectTransparency false in
/-- The defining map is a quasi-isomorphism exactly when all homology
objects of the original unbounded complex are protected solid objects. -/
theorem quasiIso_solidComplexEndomorphism_iff
    (K : CochainComplex LightCondAb ℤ) :
    QuasiIso (solidComplexEndomorphism.app K) ↔
      ∀ n : ℤ, isSolid (K.homology n) := by
  rw [quasiIso_iff]
  apply forall_congr'
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap]
  have h : homologyMap (solidComplexEndomorphism.app K) n =
      ((K.sc n).mapHomologyIso (ihom P)).hom ≫
        (MonoidalClosed.pre oneMinusShift).app (K.homology n) ≫
          ((K.sc n).mapHomologyIso (ihom P)).inv :=
    (K.sc n).homologyMap_mapNatTrans (MonoidalClosed.pre oneMinusShift)
  rw [h, isIso_comp_left_iff, isIso_comp_right_iff]
  rfl

/-- The same defining map is an actual natural transformation on the
unbounded derived category, since internal Hom out of `P` is exact. -/
def solidDerivedEndomorphism :
    (ihom P).mapDerivedCategory ⟶ (ihom P).mapDerivedCategory :=
  (MonoidalClosed.pre oneMinusShift).mapDerivedCategory

set_option backward.isDefEq.respectTransparency false in
/-- The defect vanishes in the derived category precisely for complexes
whose homology is solid; no bound on degrees is imposed. -/
theorem isZero_solidComplexDefect_iff (K : CochainComplex LightCondAb ℤ) :
    IsZero (DerivedCategory.Q.obj (solidComplexDefect K)) ↔
      ∀ n : ℤ, isSolid (K.homology n) := by
  let f := solidComplexEndomorphism.app K
  have ht := DerivedCategory.mappingCone_triangle_distinguished f
  have h := (DerivedCategory.Q.mapTriangle.obj
    (CochainComplex.mappingCone.triangle f)).isZero₃_iff_isIso₁ ht
  exact h.trans ((DerivedCategory.isIso_Q_map_iff_quasiIso LightCondAb f).trans
    (quasiIso_solidComplexEndomorphism_iff K))

set_option backward.isDefEq.respectTransparency false in
/-- The derived natural transformation on the localization of any complex
has the same exact all-degree locality criterion. -/
theorem isIso_solidDerivedEndomorphism_Q_iff (K : CochainComplex LightCondAb ℤ) :
    IsIso (solidDerivedEndomorphism.app (DerivedCategory.Q.obj K)) ↔
      ∀ n : ℤ, isSolid (K.homology n) := by
  rw [solidDerivedEndomorphism, NatTrans.mapDerivedCategory_app_Q_obj,
    isIso_comp_left_iff, isIso_comp_right_iff,
    DerivedCategory.isIso_Q_map_iff_quasiIso]
  exact quasiIso_solidComplexEndomorphism_iff K

end LightCondensed.Solid
