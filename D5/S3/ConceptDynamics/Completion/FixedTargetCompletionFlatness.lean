/- GID: D5/S3/ConceptDynamics/Completion/FixedTargetCompletionFlatness
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Completion/FixedTargetCompletionFlatness
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Fixed target completions have empty order curvature. -/

import D5.S3.ConceptDynamics.Completion.TargetClosureOperator
import Mathlib.Data.Set.SymmDiff

/- Library-search audit trail (2026-08-27):
   * Repository searches for fixed-target closure commutativity, flatness, and
     kernel symmetric differences found no exact theorem.
   * The related `commuting_target_defect_empty` concerns commuting state maps
     under an explicit hypothesis, not the two canonical target closures here.
   * Exact family hits `targetClosure`, `conceptJoin`, and
     `canonicalTargetReadout` construct the source closures from the current
     concept and fixed target maps; they are imported rather than redeclared.
   * Exact pinned Mathlib hit `Set.symmDiff_eq_empty` reduces zero curvature to
     equality of the two indistinguishability kernels and is applied below. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped symmDiff

namespace D5.S3.ConceptDynamics.Completion.FixedTargetCompletionFlatness

open D5.S3.ConceptDynamics.Completion.TargetClosureOperator
open D5.S3.ConceptDynamics.ConceptFiberDecomposition
open D5.S3.ConceptDynamics.ConceptJoinUniversal
open D5.S3.ConceptDynamics.Sufficiency.UniversalSufficiencyFactorization

/-- Completing a concept by two fixed targets in either order produces the same
indistinguishability kernel, so their source-defined curvature is empty. -/
theorem fixed_target_completion_curvature_empty
    {X C S T : Type*} (concept : Concept X C)
    (firstTarget : X -> S) (secondTarget : X -> T) :
    ({pair : X × X |
        Setoid.ker
          (targetClosure (targetClosure concept secondTarget) firstTarget)
          pair.1 pair.2} ∆
      {pair : X × X |
        Setoid.ker
          (targetClosure (targetClosure concept firstTarget) secondTarget)
          pair.1 pair.2}) = ∅ := by
  rw [Set.symmDiff_eq_empty]
  ext pair
  change
    (((concept pair.1, canonicalTargetReadout secondTarget pair.1),
          canonicalTargetReadout firstTarget pair.1) =
        ((concept pair.2, canonicalTargetReadout secondTarget pair.2),
          canonicalTargetReadout firstTarget pair.2)) ↔
      (((concept pair.1, canonicalTargetReadout firstTarget pair.1),
          canonicalTargetReadout secondTarget pair.1) =
        ((concept pair.2, canonicalTargetReadout firstTarget pair.2),
          canonicalTargetReadout secondTarget pair.2))
  simp only [Prod.mk.injEq]
  tauto

#print axioms fixed_target_completion_curvature_empty

end D5.S3.ConceptDynamics.Completion.FixedTargetCompletionFlatness
