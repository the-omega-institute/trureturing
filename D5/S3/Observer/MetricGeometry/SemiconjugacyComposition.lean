/- GID: D5/S3/Observer/MetricGeometry/SemiconjugacyComposition
   generality: G
   mirror-B: D5/B/S3/Observer/MetricGeometry/SemiconjugacyComposition
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A Lipschitz post-map bounds composite defect by its two component defects. -/

import Mathlib.Topology.EMetricSpace.Lipschitz

namespace D5.S3.Observer.MetricGeometry.SemiconjugacyComposition

/-- The uniform extended-distance defect of a map between two updated spaces. -/
noncomputable def semiconjugacyDefect
    {A B : Type*} [PseudoEMetricSpace B]
    (updateA : A -> A) (updateB : B -> B) (projection : A -> B) : ENNReal :=
  iSup fun y => edist (projection (updateA y)) (updateB (projection y))

/-- Composing with a Lipschitz map amplifies the first semiconjugacy defect by at
most its Lipschitz constant, then adds the second semiconjugacy defect. -/
theorem semiconjugacy_defect_composition
    {Y Z W : Type*} [PseudoEMetricSpace Z] [PseudoEMetricSpace W]
    (tau : Y -> Y) (sigma : Z -> Z) (omega : W -> W)
    (pi : Y -> Z) (rho : Z -> W) (K : NNReal)
    (hrho : LipschitzWith K rho) :
    semiconjugacyDefect tau omega (Function.comp rho pi) <=
      (K : ENNReal) * semiconjugacyDefect tau sigma pi +
        semiconjugacyDefect sigma omega rho := by
  apply iSup_le
  intro y
  calc
    edist ((Function.comp rho pi) (tau y))
        (omega ((Function.comp rho pi) y)) <=
        edist (rho (pi (tau y))) (rho (sigma (pi y))) +
          edist (rho (sigma (pi y))) (omega (rho (pi y))) := by
      simpa only [Function.comp_apply] using
        edist_triangle (rho (pi (tau y))) (rho (sigma (pi y))) (omega (rho (pi y)))
    _ <= (K : ENNReal) * edist (pi (tau y)) (sigma (pi y)) +
          edist (rho (sigma (pi y))) (omega (rho (pi y))) :=
      add_le_add (hrho.edist_le_mul _ _) le_rfl
    _ <= (K : ENNReal) * semiconjugacyDefect tau sigma pi +
          semiconjugacyDefect sigma omega rho := by
      apply add_le_add
      · exact mul_le_mul_right (le_iSup (fun y =>
          edist (pi (tau y)) (sigma (pi y))) y) _
      · exact le_iSup (fun z => edist (rho (sigma z)) (omega (rho z))) (pi y)

end D5.S3.Observer.MetricGeometry.SemiconjugacyComposition
