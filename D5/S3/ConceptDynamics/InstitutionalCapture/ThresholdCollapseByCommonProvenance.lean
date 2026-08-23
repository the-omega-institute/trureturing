/- GID: D5/S3/ConceptDynamics/InstitutionalCapture/ThresholdCollapseByCommonProvenance
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/InstitutionalCapture/ThresholdCollapseByCommonProvenance
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Common provenance separates formal role count from the actual capture threshold. -/

import D5.S3.ConceptDynamics.InstitutionalCapture.IndependentSourceCaptureLowerBound

/- Library-search audit trail (2026-08-22):
   * `rg -n -F 'threshold_collapse_by_common_provenance' D5 Golden/Frozen/accepted`
     found no existing declaration.
   * The required ConceptDynamics search for `threshold`, `capture`, `provenance`,
     and `separation.*duties` found the two institutional-capture siblings below,
     but no theorem comparing equal formal role counts with different thresholds.
   * This module reuses `captureNumber` and
     `common_source_capture_number_eq_one` from `CommonSourceCaptureCollapse`, and
     `independentNecessarySources` and `independent_source_capture_lower_bound`
     from `IndependentSourceCaptureLowerBound`; only concrete witness construction,
     extensional separation, and finite-cardinality arithmetic remain local. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.InstitutionalCapture.ThresholdCollapseByCommonProvenance

open D5.S3.ConceptDynamics.ConceptFiberDecomposition
open D5.S3.ConceptDynamics.InstitutionalCapture.CommonSourceCaptureCollapse
open D5.S3.ConceptDynamics.InstitutionalCapture.IndependentSourceCaptureLowerBound

/-- Every named role exposes the same readout, so all role outputs have one provenance. -/
def commonProvenanceReadout {n : Nat} (_ : Fin n) : Concept (Fin n × Bool) Bool :=
  fun state => state.2

/-- Each named role exposes only the Boolean stored under its own provenance label. -/
def independentProvenanceReadout {n : Nat} (source : Fin n) :
    Concept (Fin n × Bool) Bool :=
  fun state => if state.1 = source then state.2 else false

/-- For every positive formal role count, identical interface names support both a
common-provenance design with capture threshold one and an independent-provenance
design whose capture threshold equals the full role count. -/
theorem threshold_collapse_by_common_provenance (n : Nat) (positive : 0 < n) :
    Fintype.card (Fin n) = n ∧
      captureNumber (@commonProvenanceReadout n) (@commonProvenanceReadout n) = 1 ∧
      captureNumber (@independentProvenanceReadout n)
        (@independentProvenanceReadout n) = n := by
  haveI : Nonempty (Fin n) := ⟨⟨0, positive⟩⟩
  refine ⟨Fintype.card_fin n, ?_, ?_⟩
  · apply common_source_capture_number_eq_one _ _ ⟨0, positive⟩
    intro branch
    exact Function.FactorsThrough.rfl
  · let readout := @independentProvenanceReadout n
    have independent : independentNecessarySources readout readout id := by
      refine ⟨Function.injective_id, ?_⟩
      intro branch candidate
      constructor
      · intro factors
        by_contra unequal
        change candidate ≠ branch at unequal
        have sameCandidate :
            readout candidate (branch, false) = readout candidate (branch, true) := by
          simp [readout, independentProvenanceReadout, Ne.symm unequal]
        have sameBranch := factors sameCandidate
        simp [readout, independentProvenanceReadout] at sameBranch
      · intro candidateEq
        subst candidate
        exact Function.FactorsThrough.rfl
    apply le_antisymm
    · rw [captureNumber]
      apply Nat.sInf_le
      refine ⟨Set.univ, Set.finite_univ, by simp, ?_⟩
      intro branch
      exact ⟨branch, Set.mem_univ branch, Function.FactorsThrough.rfl⟩
    · simpa [readout] using
        independent_source_capture_lower_bound readout readout id independent

example :
    Fintype.card (Fin 3) = 3 ∧
      captureNumber (@commonProvenanceReadout 3) (@commonProvenanceReadout 3) = 1 ∧
      captureNumber (@independentProvenanceReadout 3)
        (@independentProvenanceReadout 3) = 3 := by
  simpa using threshold_collapse_by_common_provenance 3 (by omega)

#print axioms threshold_collapse_by_common_provenance

end D5.S3.ConceptDynamics.InstitutionalCapture.ThresholdCollapseByCommonProvenance
