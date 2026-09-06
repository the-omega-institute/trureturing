/- GID: D5/S3/ConceptDynamics/NormativeRequirements/NecessarySafeguardObstruction
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/NormativeRequirements/NecessarySafeguardObstruction
   mirror-E: none(waiver:pure-conditional-decision-boundary)
   anchors: []
   utility: none
   digest: A necessary safeguard can obstruct both goal sufficiency and outcome-only decisions. -/

import D5.S3.ConceptDynamics.NormativeStructure.HistorySensitiveOutcomeReductionObstruction
import Mathlib.Data.Set.Basic

/- Search (2026-09-06): the existing history-sensitive outcome obstruction
   supplies the complete factorization step. Set.notMem_subset and Set.not_subset
   supply the exclusion and counterexample steps. No inspected repository theorem
   composes these with independent necessary requirements. Loogle's safeguard
   name query returned zero hits; no global novelty claim is made. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.NormativeRequirements.NecessarySafeguardObstruction

open D5.S3.ConceptDynamics.ConceptFiberDecomposition
open D5.S3.ConceptDynamics.NormativeStructure.HistorySensitiveOutcomeReductionObstruction

/-- The necessity rule is an input; this theorem does not choose the rule. -/
theorem violated_requirement_excludes_permission
    {Path Requirement : Type*}
    (permitted : Concept Path Prop)
    (requirement : Requirement -> Concept Path Prop)
    (necessary : ∀ path, permitted path -> ∀ key, requirement key path)
    (path : Path) (failure : ∃ key, ¬ requirement key path) :
    ¬ permitted path := by
  obtain ⟨key, missing⟩ := failure
  exact Set.notMem_subset
    (s := {path | permitted path}) (t := {path | requirement key path})
    (fun candidate admitted => necessary candidate admitted key) missing

/-- A goal-satisfying counterexample to a necessary safeguard also refutes
the universal claim that satisfying the goal suffices for permission. -/
theorem rationale_does_not_supply_necessary_safeguard
    {Path : Type*}
    (goal permitted safeguard : Concept Path Prop)
    (necessary : ∀ path, permitted path -> safeguard path)
    (path : Path) (achievesGoal : goal path) (missing : ¬ safeguard path) :
    ¬ permitted path ∧ ¬ (∀ candidate, goal candidate -> permitted candidate) := by
  have excluded := violated_requirement_excludes_permission
    permitted (fun _ : Unit => safeguard)
    (fun candidate admitted _ => necessary candidate admitted)
    path ⟨(), missing⟩
  exact ⟨excluded, Set.not_subset.mpr ⟨path, achievesGoal, excluded⟩⟩

/-- An accepted path and a path violating a necessary safeguard cannot share
an outcome-only permission rule when their observed outcomes coincide. -/
theorem necessary_safeguard_blocks_readout_factorization
    {Path Outcome : Type*}
    (outcome : Concept Path Outcome) (permitted safeguard : Concept Path Prop)
    (necessary : ∀ path, permitted path -> safeguard path)
    (accepted blocked : Path)
    (sameOutcome : outcome accepted = outcome blocked)
    (admitted : permitted accepted) (missing : ¬ safeguard blocked) :
    ¬ ∃ decision : Outcome -> Prop, permitted = decision ∘ outcome := by
  have excluded := violated_requirement_excludes_permission
    permitted (fun _ : Unit => safeguard)
    (fun candidate allowed _ => necessary candidate allowed)
    blocked ⟨(), missing⟩
  have different : permitted accepted ≠ permitted blocked := by
    intro equalPermissions
    exact excluded (equalPermissions ▸ admitted)
  exact history_sensitive_evaluation_not_outcome_reducible
    outcome permitted ⟨accepted, blocked, sameOutcome, different⟩

/-- Capacity and parity constraints give an inhabited specialization unrelated
to political interpretation. The observed endpoint omits both constraints. -/
example :
    ¬ ∃ decision : Unit -> Prop,
      (fun state : Nat × Nat => state.2 ≤ state.1 ∧ state.2 % 2 = 0) =
        decision ∘ (fun _ : Nat × Nat => ()) := by
  exact necessary_safeguard_blocks_readout_factorization
    (fun _ : Nat × Nat => ())
    (fun state => state.2 ≤ state.1 ∧ state.2 % 2 = 0)
    (fun state => state.2 % 2 = 0)
    (fun _ admitted => admitted.2)
    (4, 2) (4, 3) rfl (by decide) (by decide)

/-- Removing the violated requirement removes the obstruction: a constant
permission rule can then factor through a constant outcome. -/
example :
    ∃ decision : Unit -> Prop,
      (fun _ : Bool => True) = decision ∘ (fun _ : Bool => ()) := by
  exact ⟨fun _ => True, rfl⟩

#print axioms violated_requirement_excludes_permission
#print axioms rationale_does_not_supply_necessary_safeguard
#print axioms necessary_safeguard_blocks_readout_factorization

end D5.S3.ConceptDynamics.NormativeRequirements.NecessarySafeguardObstruction
