/- GID: D5/S3/Observer/MetricGeometryLaws/MetricEntourageComposition
   generality: G
   mirror-B: D5/B/S3/Observer/MetricGeometryLaws/MetricEntourageComposition
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Metric entourages compose inside the entourage at the sum of radii. -/

import Mathlib.Topology.MetricSpace.Basic

/- Library-search audit trail (2026-08-28):
   * The repository search for metric-entourage and relation-composition declarations
     found no matching primitive; neighboring observer modules only use `dist_triangle`.
   * The pinned Mathlib declaration `dist_triangle` is the exact proof ingredient and
     is applied directly below. No exact theorem for this relation inclusion was found.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.MetricGeometryLaws.MetricEntourageComposition

def metricEntourage {X : Type*} [PseudoMetricSpace X] (radius : ℝ) : Set (X × X) :=
  {pair | dist pair.1 pair.2 ≤ radius}

def relationCompose {X : Type*} (left right : Set (X × X)) : Set (X × X) :=
  {pair | ∃ middle, (pair.1, middle) ∈ left ∧ (middle, pair.2) ∈ right}

theorem metric_entourage_comp_subset
    {X : Type*} [PseudoMetricSpace X] (epsilon delta : ℝ) :
    relationCompose (metricEntourage (X := X) epsilon)
        (metricEntourage (X := X) delta) ⊆
      metricEntourage (X := X) (epsilon + delta) := by
  intro pair hpair
  rcases hpair with ⟨middle, hfirst, hsecond⟩
  exact (dist_triangle pair.1 middle pair.2).trans
    (add_le_add hfirst hsecond)

example :
    relationCompose (metricEntourage (X := ℝ) (1 : ℝ))
        (metricEntourage (X := ℝ) 2) ⊆
      metricEntourage (X := ℝ) ((1 : ℝ) + 2) := by
  simpa using (metric_entourage_comp_subset (X := ℝ) 1 2)

#print axioms metric_entourage_comp_subset

end D5.S3.Observer.MetricGeometryLaws.MetricEntourageComposition
