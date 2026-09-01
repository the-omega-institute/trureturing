/- GID: D5/S3/ConceptDynamics/DefinitionEscape/CompletionBarycenterOfflineZeroEscape
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/DefinitionEscape/CompletionBarycenterOfflineZeroEscape
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The completion barycenter loses the squared offline-zero coordinate. -/

import D5.S3.ConceptDynamics.DefinitionEscape.ResidualJoinLaw
import D5.S3.ConceptDynamics.Restoration.TargetRecoveryCriterion
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

/- Library-search audit trail (2026-09-01):
   * The atom occurs only in the observer-adelic completion ledger's
     `residual-open` directory, with empty `coverage_gids`; its exact atom-id
     search found no formalization receipt. Immediate source neighbors 631,
     632, 634, and 635 are likewise residual-open.
   * Repository searches covered `DefinitionEscape`, escape, indistinguishable,
     `Setoid.ker`, identifiability, observational equivalence, `targetEscape`,
     completion barycenters, offline zeros, squared offsets, factorization, and
     recovery. The exact general hits are `target_recovery_criterion` (a target
     is unrecoverable exactly when its defect is nonempty) and
     `residual_join_law` (joining a definition intersects the old defect with
     its kernel); both are imported and applied directly below. The same-volume
     bound neighbor `BareValueObservationNoninjective` concerns structural
     certificates at `pi`, not this spectral-state readout or squared target.
   * Pinned Mathlib defines `Function.FactorsThrough` and proves
     `Function.factorsThrough_iff`; no upstream theorem packages this concrete
     complex observer, interval subtype, and squared target. `loogle` and
     `leansearch` were not on PATH. Searches of the other pinned Lean packages
     found no matching domain theorem.
   * The state space is modeled as the subtype of `Real × Real` satisfying the
     source's open interval condition on the second coordinate. The owning
     directory had 13 Lean modules on `origin/dev` before this addition. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.DefinitionEscape.CompletionBarycenterOfflineZeroEscape

open D5.S3.ConceptDynamics.ConceptFiberDecomposition
open D5.S3.ConceptDynamics.ConceptJoinUniversal
open D5.S3.ConceptDynamics.DefinitionEscape.ResidualJoinLaw
open D5.S3.ConceptDynamics.Restoration.TargetRecoveryCriterion
open D5.S3.ConceptDynamics.TargetRisk.RefinementRiskCostTradeoff

noncomputable section

/-- Candidate spectral states `(gamma, delta)` with the source's strict
offline displacement bound. -/
def SpectralState :=
  {pair : Real × Real // -(1 / 2 : Real) < pair.2 ∧ pair.2 < (1 / 2 : Real)}

/-- The current completion observer retains only the barycenter and height. -/
def completionObserver (state : SpectralState) : Complex :=
  (1 / 2 : Complex) + (state.1.1 : Complex) * Complex.I

/-- The target coordinate omitted by the completion observer. -/
def squareTarget (state : SpectralState) : Real :=
  state.1.2 ^ 2

/-- The source's first explicit state, with displacement `1 / 4`. -/
def quarterState : SpectralState :=
  ⟨(0, 1 / 4), by norm_num⟩

/-- The source's second explicit state, with displacement `1 / 3`. -/
def thirdState : SpectralState :=
  ⟨(0, 1 / 3), by norm_num⟩

/-- The two legal states have the same completion reading `1 / 2`, while the
target is computed explicitly as `1 / 16` and `1 / 9`. -/
theorem offline_zero_escape_witness :
    completionObserver quarterState = (1 / 2 : Complex) ∧
      completionObserver thirdState = (1 / 2 : Complex) ∧
      completionObserver quarterState = completionObserver thirdState ∧
      squareTarget quarterState = (1 / 16 : Real) ∧
      squareTarget thirdState = (1 / 9 : Real) ∧
      squareTarget quarterState ≠ squareTarget thirdState ∧
      (quarterState, thirdState) ∈
        defectRelation completionObserver squareTarget := by
  norm_num [completionObserver, squareTarget, quarterState, thirdState,
    defectRelation]

/-- The completion observer cannot determine the squared displacement target:
no real-valued function on complex observations recovers it on every legal
spectral state. -/
theorem completion_barycenter_offline_zero_escape :
    ¬ ∃ recover : Complex → Real, ∀ state : SpectralState,
      squareTarget state = recover (completionObserver state) := by
  letI : Nonempty SpectralState := ⟨quarterState⟩
  have nonemptyDefect :
      (defectRelation completionObserver squareTarget).Nonempty :=
    ⟨(quarterState, thirdState), offline_zero_escape_witness.2.2.2.2.2.2⟩
  have noRecovery :
      ¬ ∃ recover : Complex → Real,
        squareTarget = recover ∘ completionObserver :=
    (target_recovery_criterion completionObserver squareTarget).2.2.2.mpr
      nonemptyDefect
  rintro ⟨recover, recovers⟩
  apply noRecovery
  refine ⟨recover, ?_⟩
  funext state
  exact recovers state

/-- Adding the omitted square itself as a new definition removes the entire
target defect, by the repository's canonical residual intersection law. -/
theorem square_coordinate_eliminates_escape :
    defectRelation (conceptJoin completionObserver squareTarget) squareTarget =
      ∅ := by
  rw [residual_join_law]
  ext pair
  simp [defectRelation, Setoid.ker_def]

/-- Two zero-displacement states with different heights receive different
observations, so the observer genuinely retains the `gamma` direction. -/
theorem completion_observer_retains_height :
    let first : SpectralState := ⟨(1, 0), by norm_num⟩
    let second : SpectralState := ⟨(2, 0), by norm_num⟩
    completionObserver first = (1 / 2 : Complex) + Complex.I ∧
      completionObserver second = (1 / 2 : Complex) + 2 * Complex.I ∧
      completionObserver first ≠ completionObserver second := by
  dsimp
  refine ⟨by norm_num [completionObserver],
    by norm_num [completionObserver], ?_⟩
  intro sameObservation
  have sameImaginaryPart := congrArg Complex.im sameObservation
  norm_num [completionObserver] at sameImaginaryPart

#print axioms offline_zero_escape_witness
#print axioms completion_barycenter_offline_zero_escape
#print axioms square_coordinate_eliminates_escape
#print axioms completion_observer_retains_height

end

end D5.S3.ConceptDynamics.DefinitionEscape.CompletionBarycenterOfflineZeroEscape
