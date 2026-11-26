import D5.S3.Combinatorics.Graph.Queries.KnownNameExplorationSize
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

/-! The final number of known names in a rooted graph exploration. -/

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Combinatorics.Graph.Queries.KnownNameExplorationSize
open _root_.D5.S3.Combinatorics.Graph.Queries.KnownNameSimulation
open _root_.D5.S3.Combinatorics.Graph.Queries.NamedNeighborhoodHistory (nameReply)

namespace Reg.D5.S3.Combinatorics.Graph.Queries.KnownNameExplorationSize

noncomputable section
universe u v

private abbrev seenSignature : Signature where
  Params := Type v
  State N := Set N
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

private def seenCard : Realization seenSignature.{v} :=
  realize seenSignature (fun _ _ names => names.ncard) (fun e => nomatch e)

private def alwaysTwo : Realization seenSignature.{v} :=
  realize seenSignature (fun _ _ _ => 2) (fun e => nomatch e)

private abbrev explorationArena : Arena where
  signature := seenSignature.{v}
  Law R := ∀ {V : Type u} {N : Type v} [Finite N] (G : SimpleGraph V) (f : V ↪ N)
    (root : V) (cap : ℕ) (_hRoot : (G.neighborSet root).ncard ≤ cap)
    (_hDegree : ∀ x, (G.neighborSet x).ncard ≤ cap + 1) (p : Protocol N),
    let record := simulate (fun n => nameReply G n f) p {f root}
    let finalNames := record.foldl (fun seen entry => namesAfter seen entry.1 entry.2) {f root}
    let seenCount := R.readout () N finalNames
    seenCount ≤ 1 + cap * (sentNames {f root} record).length

private theorem rejectsTwo : ¬ explorationArena.{u, v}.Law alwaysTwo := by
  intro h
  let f : ULift.{u} Unit ↪ ULift.{v} Unit :=
    ⟨fun _ => ⟨()⟩, fun _ _ _ => Subsingleton.elim _ _⟩
  have hbad := h (⊥ : SimpleGraph (ULift.{u} Unit)) f ⟨()⟩ 0 (by simp)
    (fun _ => by simp) .stop
  simpa [alwaysTwo, realize] using hbad

private theorem seenCard_varies :
    seenCard.{v}.readout () (ULift.{v} Unit) ∅ ≠
      seenCard.{v}.readout () (ULift.{v} Unit) {⟨()⟩} := by
  simp [seenCard, realize]

def explorationEvidence : Registration explorationArena.{u, v}
    (type_of% (@known_names_card_bound.{u, v})) where
  actual := seenCard
  bridge := Iff.rfl
  variation := ⟨@known_names_card_bound.{u, v}, alwaysTwo, rejectsTwo⟩
  sensitivity := ⟨fun i =>
    ⟨alwaysTwo, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejectsTwo⟩,
    fun e => nomatch e⟩
  dependence := fun _ => ⟨ULift.{v} Unit, ∅, {⟨()⟩}, seenCard_varies⟩

def explorationRegistration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@known_names_card_bound.{u, v}) (Realization seenSignature.{v}) Unit Unit := {
  unitName := `Reg.D5.S3.Combinatorics.Graph.Queries.KnownNameExplorationSize.known_names_card_bound
  realizationName := `Reg.D5.S3.Combinatorics.Graph.Queries.KnownNameExplorationSize.explorationEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨explorationArena.{u, v}⟩
  objectArena := .source ⟨explorationArena.{u, v}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source explorationArena.{u, v} ⟨explorationEvidence.{u, v}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize seenSignature (fun _ _ names => names.ncard) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.Queries.KnownNameExplorationSize
    definition := none
    coordinates := #[1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "value"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end
end Reg.D5.S3.Combinatorics.Graph.Queries.KnownNameExplorationSize
