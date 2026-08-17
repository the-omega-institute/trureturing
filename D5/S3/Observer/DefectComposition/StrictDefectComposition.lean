/- GID: D5/S3/Observer/DefectComposition/StrictDefectComposition
   generality: G
   mirror-B: D5/B/S3/Observer/DefectComposition/StrictDefectComposition
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Strict difference defects add exactly under map composition. -/

import Mathlib

/- Library-search audit trail (2026-08-17):
   * Repository searches for a strict-difference defect and an exact composition theorem found
     no packaged declaration; the nearest results are Lipschitz upper bounds.
   * The pinned Mathlib search found `sub_add_sub_cancel`, the exact algebraic identity applied
     below. Searches for `delta_M` and strict defect composition found no exact hit.
   * LeanSearch and Loogle web attempts for the full typed statement returned no exact theorem.
-/

namespace D5.S3.Observer.DefectComposition.StrictDefectComposition

/- The strict difference between a source dissimilarity and the pulled-back target dissimilarity. -/
def strictDefect {X Y : Type*}
    (sourceMeasure : X → X → ℝ) (targetMeasure : Y → Y → ℝ)
    (q : X → Y) (x y : X) : ℝ :=
  sourceMeasure x y - targetMeasure (q x) (q y)

/- For a composable pair of maps, the strict differences telescope exactly. -/
theorem strict_defect_composition
    {X Y Z : Type*}
    (sourceMeasure : X → X → ℝ)
    (middleMeasure : Y → Y → ℝ)
    (targetMeasure : Z → Z → ℝ)
    (q : X → Y) (r : Y → Z) (x y : X) :
    strictDefect sourceMeasure targetMeasure (r ∘ q) x y =
      strictDefect sourceMeasure middleMeasure q x y +
        strictDefect middleMeasure targetMeasure r (q x) (q y) := by
  simp only [strictDefect, Function.comp_apply]
  exact (sub_add_sub_cancel (sourceMeasure x y)
    (middleMeasure (q x) (q y)) (targetMeasure (r (q x)) (r (q y)))).symm

/- The hypotheses are inhabited by the constant-zero measures and identity maps. -/
example :
    strictDefect (fun _ _ : Unit => (0 : ℝ)) (fun _ _ : Unit => (0 : ℝ))
        ((fun _ : Unit => ()) ∘ (fun _ : Unit => ())) () () =
      strictDefect (fun _ _ : Unit => (0 : ℝ)) (fun _ _ : Unit => (0 : ℝ))
          (fun _ : Unit => ()) () () +
        strictDefect (fun _ _ : Unit => (0 : ℝ)) (fun _ _ : Unit => (0 : ℝ))
          (fun _ : Unit => ()) () () :=
  strict_defect_composition
    (sourceMeasure := fun _ _ : Unit => (0 : ℝ))
    (middleMeasure := fun _ _ : Unit => (0 : ℝ))
    (targetMeasure := fun _ _ : Unit => (0 : ℝ))
    (q := fun _ : Unit => ()) (r := fun _ : Unit => ()) () ()

#print axioms strict_defect_composition

end D5.S3.Observer.DefectComposition.StrictDefectComposition
