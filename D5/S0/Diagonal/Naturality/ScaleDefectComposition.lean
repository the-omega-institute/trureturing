/- GID: D5/S0/Diagonal/Naturality/ScaleDefectComposition
   generality: G
   mirror-B: D5/B/S0/Diagonal/Naturality/ScaleDefectComposition
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Coherent scale projections compose pointwise diagonal defects. -/

/- Library-search audit trail (2026-08-23):
   * The exact repository family primitive
     `D5.S0.Diagonal.Naturality.NaturalityDefectComposition.naturalityDefect`
     is imported and used for every displayed scale error.
   * The neighboring `naturality_defect_comp_le` composes horizontal global and local maps;
     the present source theorem instead composes vertical table and output projections.
   * Pinned Mathlib exact hits `dist_triangle` and `LipschitzWith.dist_le_mul` are applied
     directly. Repository and pinned-library searches found no complete theorem for this
     vertically composed, coherently projected three-scale defect. -/

import D5.S0.Diagonal.Naturality.NaturalityDefectComposition

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S0.Diagonal.Naturality.ScaleDefectComposition

open D5.S0.Diagonal.Naturality.NaturalityDefectComposition

/-- For three ordered scales, coherent table and output projections compose the pointwise
diagonal naturality error. The intermediate output projection amplifies the finer-scale error
by at most its Lipschitz constant. -/
theorem diagonal_scale_defect_comp_le
    {Scale : Type*} [Preorder Scale]
    (Table Output : Scale → Type*)
    (k i j : Scale) (hki : k ≤ i) (hij : i ≤ j)
    [PseudoMetricSpace (Output i)] [PseudoMetricSpace (Output k)]
    (projectTable : ∀ {high low : Scale}, low ≤ high → Table high → Table low)
    (projectOutput : ∀ {high low : Scale}, low ≤ high → Output high → Output low)
    (diagonal : ∀ scale : Scale, Table scale → Output scale)
    (hTableCoherence :
      projectTable (hki.trans hij) = projectTable hki ∘ projectTable hij)
    (hOutputCoherence :
      projectOutput (hki.trans hij) = projectOutput hki ∘ projectOutput hij)
    (L : NNReal) (hLipschitz : LipschitzWith L (projectOutput hki))
    (E : Table j) :
    naturalityDefect (projectTable (hki.trans hij)) (projectOutput (hki.trans hij))
        (diagonal j) (diagonal k) E ≤
      L * naturalityDefect (projectTable hij) (projectOutput hij)
          (diagonal j) (diagonal i) E +
        naturalityDefect (projectTable hki) (projectOutput hki)
          (diagonal i) (diagonal k) (projectTable hij E) := by
  unfold naturalityDefect
  rw [hTableCoherence, hOutputCoherence]
  simp only [Function.comp_apply]
  calc
    dist (projectOutput hki (projectOutput hij (diagonal j E)))
        (diagonal k (projectTable hki (projectTable hij E))) ≤
      dist (projectOutput hki (projectOutput hij (diagonal j E)))
          (projectOutput hki (diagonal i (projectTable hij E))) +
        dist (projectOutput hki (diagonal i (projectTable hij E)))
          (diagonal k (projectTable hki (projectTable hij E))) :=
      dist_triangle _ _ _
    _ ≤ L * dist (projectOutput hij (diagonal j E))
          (diagonal i (projectTable hij E)) +
        dist (projectOutput hki (diagonal i (projectTable hij E)))
          (diagonal k (projectTable hki (projectTable hij E))) :=
      add_le_add (hLipschitz.dist_le_mul _ _) le_rfl

#print axioms diagonal_scale_defect_comp_le

end D5.S0.Diagonal.Naturality.ScaleDefectComposition
