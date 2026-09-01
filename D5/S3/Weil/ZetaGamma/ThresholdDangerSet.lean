/- GID: D5/S3/Weil/ZetaGamma/ThresholdDangerSet
   generality: G
   mirror-B: D5/B/S3/Weil/ZetaGamma/ThresholdDangerSet
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A positive threshold cuts out the strict sublevel danger set of a real multiplier. -/

import Mathlib.Data.Real.Basic

/- Library-search audit trail (2026-09-01):
   * The atom remains in `residual-open` with empty `coverage_gids`, and its
     id occurs in no formalization receipt or `absorbed-closed` entry.
     Repository searches for danger sets, strict sublevels, and threshold
     sets found no public constructor with this statement. The neighboring
     `ArchimedeanConfinement` module uses the same set expression internally
     for a specific completed-zeta multiplier, while its abstract helper is
     private. `DepthClosedFiltration.depthSublevel` instead has a natural-valued
     function and a non-strict inequality.
   * Pinned Mathlib provides the underlying `Set` constructor and interval
     notation. `Sion.sublevelLeft` is a non-strict, subtype-parameterized
     sublevel family, not this strict real sublevel definition.
   * Searches of the pinned non-Mathlib Lean packages found no danger-set or
     strict-sublevel declaration matching the source definition. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Weil.ZetaGamma.ThresholdDangerSet

/-- The strict threshold danger set of an abstract real multiplier. The
positivity proof records the source's stated domain; the set depends on the
multiplier and threshold values. -/
def thresholdDangerSet (m : ℝ → ℝ) (a : ℝ) (_ha : 0 < a) : Set ℝ :=
  {xi | m xi < a}

@[simp]
theorem mem_thresholdDangerSet (m : ℝ → ℝ) (a : ℝ) (ha : 0 < a) (xi : ℝ) :
    xi ∈ thresholdDangerSet m a ha ↔ m xi < a :=
  Iff.rfl

/-- Definition 398.1: a positive threshold cuts out precisely the points at
which the abstract multiplier lies strictly below that threshold. -/
theorem threshold_danger_set_definition (m : ℝ → ℝ) (a : ℝ) (ha : 0 < a) :
    thresholdDangerSet m a ha = {xi : ℝ | m xi < a} :=
  rfl

/-- The zero multiplier at threshold one gives a concrete nonempty danger
set. This is a realizability witness, not a claim that every danger set is
nonempty. -/
theorem zero_multiplier_unit_threshold_nonempty :
    (thresholdDangerSet (fun _ : ℝ => 0) 1 zero_lt_one).Nonempty := by
  refine ⟨0, ?_⟩
  change (0 : ℝ) < 1
  exact zero_lt_one

/-- The constant-one multiplier at threshold one gives a concrete empty
danger set. -/
theorem unit_multiplier_unit_threshold_empty :
    thresholdDangerSet (fun _ : ℝ => 1) 1 zero_lt_one = ∅ := by
  ext xi
  simp [thresholdDangerSet]

#print axioms threshold_danger_set_definition
#print axioms zero_multiplier_unit_threshold_nonempty
#print axioms unit_multiplier_unit_threshold_empty

end D5.S3.Weil.ZetaGamma.ThresholdDangerSet
