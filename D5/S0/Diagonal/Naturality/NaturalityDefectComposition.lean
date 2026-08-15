/- GID: D5/S0/Diagonal/Naturality/NaturalityDefectComposition
   generality: G
   mirror-B: D5/B/S0/Diagonal/Naturality/NaturalityDefectComposition
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Pointwise naturality defects satisfy a Lipschitz composition bound. -/

import Mathlib.Topology.MetricSpace.Lipschitz

/- Library-search audit trail (2026-08-16):
   * Loogle name queries found the exact supporting declarations `dist_triangle`
     and `LipschitzWith.dist_le_mul`; both are imported and applied below.
   * LeanSearch web endpoints returned no usable result for the full statement.
   * Pinned-Mathlib searches found the same two supporting declarations but no
     complete theorem for the pointwise defect of composed approximations.
   * Repository searches found related update and semiconjugacy bounds, each
     frozen for a different atom, but no theorem with this typed composition shape. -/

namespace D5.S0.Diagonal.Naturality.NaturalityDefectComposition

/-- The pointwise mismatch between a global map followed by target projection
and its local approximation applied after source projection. -/
def naturalityDefect
    {A Am B Bm : Type*} [PseudoMetricSpace Bm]
    (projectA : A -> Am) (projectB : B -> Bm)
    (globalMap : A -> B) (localMap : Am -> Bm) (x : A) : Real :=
  dist (projectB (globalMap x)) (localMap (projectA x))

/-- The defect of a composite is at most the outer defect plus the inner defect
amplified by the Lipschitz constant of the outer local approximation. -/
theorem naturality_defect_comp_le
    {A Am B Bm C Cm : Type*}
    [PseudoMetricSpace Bm] [PseudoMetricSpace Cm]
    (projectA : A -> Am) (projectB : B -> Bm) (projectC : C -> Cm)
    (globalF : B -> C) (localF : Bm -> Cm)
    (globalG : A -> B) (localG : Am -> Bm)
    (K : NNReal) (hlocalF : LipschitzWith K localF) (x : A) :
    naturalityDefect projectA projectC (globalF ∘ globalG) (localF ∘ localG) x <=
      naturalityDefect projectB projectC globalF localF (globalG x) +
        K * naturalityDefect projectA projectB globalG localG x := by
  unfold naturalityDefect
  simp only [Function.comp_apply]
  calc
    dist (projectC (globalF (globalG x))) (localF (localG (projectA x))) <=
        dist (projectC (globalF (globalG x))) (localF (projectB (globalG x))) +
          dist (localF (projectB (globalG x))) (localF (localG (projectA x))) :=
      dist_triangle _ _ _
    _ <= dist (projectC (globalF (globalG x))) (localF (projectB (globalG x))) +
          K * dist (projectB (globalG x)) (localG (projectA x)) :=
      add_le_add_right (hlocalF.dist_le_mul _ _) _

example : Unit := ()

example : LipschitzWith (1 : NNReal) (id : Real -> Real) := LipschitzWith.id

#print axioms naturality_defect_comp_le

end D5.S0.Diagonal.Naturality.NaturalityDefectComposition
