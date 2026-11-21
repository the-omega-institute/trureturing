import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Graph.Walks.MeyerovitchYoungQ61DFAIntersection
import Reg.Support.DependentFamily

/-! The charged-segment count and the current state set as observations of a word. -/

namespace Reg.D5.S3.Combinatorics.Graph.Walks.MeyerovitchYoungQ61DFAIntersection

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.MeyerovitchYoungQ61DFAIntersection
open _root_.MeyerovitchYoungQ61Complete (matrixMinimum)

set_option autoImplicit false

universe u v x
noncomputable section

set_option linter.checkUnivs false in
abbrev Parameters :=
  Σ Q : Type u, Σ Letter : Type v, Σ _ : DecidableEq Q, Σ _ : Fintype Q,
    Σ _ : Q → Letter → Q, Σ _ : Finset Q, Finset Q

abbrev wordSignature (output : Parameters.{u, v} → Type x) : Signature where
  Params := Parameters.{u, v}
  State parameters := List (Option parameters.2.1)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ := output
  Anchor := Empty
  finiteAnchor := inferInstance

abbrev countSignature := wordSignature.{u, v} (fun _ => ℤ)

def countActual : Realization countSignature.{u, v} :=
  realize countSignature
    (fun _ ⟨Q, Letter, d, f, δ, S, F⟩ w => (@scan Q Letter d f δ S F w).1)
    (fun e => nomatch e)

def countRejected : Realization countSignature.{u, v} :=
  realize countSignature (fun _ _ _ => 1) (fun e => nomatch e)

abbrev countArena : Arena where
  signature := countSignature.{u, v}
  Law R := ∀ {Q : Type u} {Letter : Type v} [d : DecidableEq Q] [f : Fintype Q] [Nonempty Q]
    (δ : Q → Letter → Q) (S F : Finset Q) (_hS : S.Nonempty) (w : List (Option Letter)),
    matrixMinimum (costs δ S F) w = R.readout () ⟨Q, Letter, d, f, δ, S, F⟩ w ∧
    ∀ j, endpointScores δ S F w j = matrixMinimum (costs δ S F) w ↔ j ∈ (scan δ S F w).2

private theorem countRejected_fails : ¬ countArena.{u, v}.Law countRejected := by
  intro law
  let δ : ULift.{u} Unit → ULift.{v} Unit → ULift.{u} Unit := fun i _ => i
  let S : Finset (ULift.{u} Unit) := Finset.univ
  have bad := (law δ S S Finset.univ_nonempty []).1
  rw [(matrixMinimum_eq_score δ S S Finset.univ_nonempty []).1] at bad
  change (0 : ℤ) = 1 at bad
  exact zero_ne_one bad

def countFamily : Registration countArena.{u, v} (type_of% @matrixMinimum_eq_score.{u, v}) where
  actual := countActual
  bridge := Iff.rfl
  variation := ⟨@matrixMinimum_eq_score.{u, v}, countRejected, countRejected_fails⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨countRejected, ?_, rfl, countRejected_fails⟩
      intro other h
      exact (h (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro role
    let δ : ULift.{u} Unit → ULift.{v} Unit → ULift.{u} Unit := fun i _ => i
    let S : Finset (ULift.{u} Unit) := Finset.univ
    refine ⟨⟨ULift.{u} Unit, ULift.{v} Unit, inferInstance, inferInstance, δ, S, S⟩,
      [], [none], ?_⟩
    change ((scan δ S S []).1 : ℤ) ≠ (scan δ S S [none]).1
    decide

abbrev stateSignature := wordSignature.{u, v} (fun p => Finset p.1)

def stateActual : Realization stateSignature.{u, v} :=
  realize stateSignature
    (fun _ ⟨Q, Letter, d, f, δ, S, F⟩ w => (@scan Q Letter d f δ S F w).2)
    (fun e => nomatch e)

def stateRejected : Realization stateSignature.{u, v} :=
  realize stateSignature (fun _ _ _ => ∅) (fun e => nomatch e)

abbrev stateArena : Arena where
  signature := stateSignature.{u, v}
  Law R := ∀ {Q : Type u} {Letter : Type v} [d : DecidableEq Q] [f : Fintype Q] [Nonempty Q]
    (δ : Q → Letter → Q) (S F : Finset Q) (_hS : S.Nonempty) (w : List (Option Letter)),
    0 < matrixMinimum (costs δ S F) w ↔
    ∃ u v, w = u ++ none :: v ∧ R.readout () ⟨Q, Letter, d, f, δ, S, F⟩ u ⊆ F

private theorem stateRejected_fails : ¬ stateArena.{u, v}.Law stateRejected := by
  intro law
  let δ : ULift.{u} Unit → ULift.{v} Unit → ULift.{u} Unit := fun i _ => i
  let S : Finset (ULift.{u} Unit) := Finset.univ
  have bad := (law δ S ∅ Finset.univ_nonempty [none]).2 ⟨[], [], rfl, Finset.empty_subset _⟩
  rw [(matrixMinimum_eq_score δ S ∅ Finset.univ_nonempty [none]).1] at bad
  have h : (scan δ S ∅ [none]).1 = 0 := by decide
  rw [h] at bad
  exact (lt_irrefl (0 : ℤ)) bad

def stateFamily : Registration stateArena.{u, v} (type_of% @matrixMinimum_pos_iff.{u, v}) where
  actual := stateActual
  bridge := Iff.rfl
  variation := ⟨@matrixMinimum_pos_iff.{u, v}, stateRejected, stateRejected_fails⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨stateRejected, ?_, rfl, stateRejected_fails⟩
      intro other h
      exact (h (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro role
    let δ : ULift.{u} (Fin 2) → ULift.{v} Unit → ULift.{u} (Fin 2) := fun _ _ => ⟨0⟩
    let S : Finset (ULift.{u} (Fin 2)) := Finset.univ
    refine ⟨⟨ULift.{u} (Fin 2), ULift.{v} Unit, inferInstance, inferInstance, δ, S, S⟩,
      [], [some ⟨()⟩], ?_⟩
    change (scan δ S S []).2 ≠ (scan δ S S [some ⟨()⟩]).2
    decide

def countRegistration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@matrixMinimum_eq_score.{u, v}) (Realization countSignature.{u, v}) Unit Unit where
  unitName := `Reg.D5.S3.Combinatorics.Graph.Walks.MeyerovitchYoungQ61DFAIntersection.countUnit
  realizationName :=
    `Reg.D5.S3.Combinatorics.Graph.Walks.MeyerovitchYoungQ61DFAIntersection.countFamily
  realizationSource := none
  generated := false
  arena := .source ⟨countArena.{u, v}⟩
  objectArena := .source ⟨countArena.{u, v}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source countArena.{u, v} ⟨countFamily.{u, v}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize countSignature.{u, v} countActual.readout countActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.Walks.MeyerovitchYoungQ61DFAIntersection
    definition := none
    coordinates := #[0, 1, 5, 6, 7]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "fn", "arg", "arg"]
      stateBinder := 9
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def stateRegistration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@matrixMinimum_pos_iff.{u, v}) (Realization stateSignature.{u, v}) Unit Unit where
  unitName := `Reg.D5.S3.Combinatorics.Graph.Walks.MeyerovitchYoungQ61DFAIntersection.stateUnit
  realizationName :=
    `Reg.D5.S3.Combinatorics.Graph.Walks.MeyerovitchYoungQ61DFAIntersection.stateFamily
  realizationSource := none
  generated := false
  arena := .source ⟨stateArena.{u, v}⟩
  objectArena := .source ⟨stateArena.{u, v}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source stateArena.{u, v} ⟨stateFamily.{u, v}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize stateSignature.{u, v} stateActual.readout stateActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.Walks.MeyerovitchYoungQ61DFAIntersection
    definition := none
    coordinates := #[0, 1, 5, 6, 7]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "arg", "arg", "body", "arg", "body", "arg", "fn", "arg"]
      stateBinder := 10
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.Combinatorics.Graph.Walks.MeyerovitchYoungQ61DFAIntersection
