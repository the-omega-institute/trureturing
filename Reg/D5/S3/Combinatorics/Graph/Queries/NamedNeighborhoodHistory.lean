import D5.S3.Combinatorics.Graph.Queries.NamedNeighborhoodHistory
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

/-! The fresh-name count and the set allowed by the recorded answers. -/

open LeanInformationAudit
open _root_.D5.S3.Combinatorics.Graph.Queries.NamedNeighborhoodHistory
open _root_.D5.S3.ConceptDynamics.Experiment.PassiveAdaptiveTranscriptUpperBound
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S0.Diagonal.Probability.EquivariantEscape (uniformPmf)
open scoped ENNReal

namespace Reg.D5.S3.Combinatorics.Graph.Queries.NamedNeighborhoodHistory

noncomputable section
universe u v

private abbrev freshCountSignature : Signature where
  Params := Type v
  State N := Set N
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

private def freshCountActual : Realization freshCountSignature.{v} :=
  realize freshCountSignature (fun _ _ names => names.ncard) (fun e => nomatch e)

private def freshCountZero : Realization freshCountSignature.{v} :=
  realize freshCountSignature (fun _ _ _ => 0) (fun e => nomatch e)

private abbrev freshCountArena : Arena where
  signature := freshCountSignature.{v}
  Law R := ∀ {V : Type u} {N : Type v} [Fintype V] [Fintype N]
    (G : SimpleGraph V) (p : PassiveProtocol N (fun _ => Option (Set N))) (ref : V ↪ N)
    (initial : Set N) (_hinit : initial ⊆ Set.range ref),
    let T := runPassiveProtocol (nameReply G) p ref
    let S := initial ∪ revealedNames T
    let A := (S ∪ absentNames T)ᶜ
    let freshCount := R.readout () N A
    let : Nonempty (V ↪ N) := ⟨ref⟩
    ∃ ν : PMF (CompatibleNaming G p ref initial),
      (∀ hs, (uniformPmf (V ↪ N)).filter {f | runPassiveProtocol (nameReply G) p f = T ∧
        ∀ v, ref v ∈ initial → f v = ref v} hs = ν.map Subtype.val) ∧
      ∀ a : A, ν.toOuterMeasure {f | a.1 ∈ Set.range f.1} =
        ((Fintype.card V - Nat.card S : ℕ) : ℝ≥0∞) / freshCount

private theorem rejectsZeroCount : ¬ freshCountArena.{u, v}.Law freshCountZero := by
  intro h
  let V := ULift.{u} Unit
  let N := ULift.{v} Unit
  let ref : V ↪ N := ⟨fun _ => ⟨()⟩, fun _ _ _ => Subsingleton.elim _ _⟩
  let G : SimpleGraph V := ⊥
  let p : PassiveProtocol N (fun _ => Option (Set N)) := .stop
  obtain ⟨ν, _, hMass⟩ := h G p ref ∅ (Set.empty_subset _)
  let T := runPassiveProtocol (nameReply G) p ref
  have hObserved : (∅ : Set N) ∪ revealedNames T = ∅ := by
    simp [T, p, runPassiveProtocol, revealedNames]
  have hAbsent : absentNames T = ∅ := by
    simp [T, p, runPassiveProtocol, absentNames]
  let A : Set N := (((∅ : Set N) ∪ revealedNames T) ∪ absentNames T)ᶜ
  let a : A := ⟨⟨()⟩, by simp [A, hObserved, hAbsent]⟩
  have hcard : Nat.card (↑((∅ : Set N) ∪ revealedNames T)) = 0 := by
    rw [hObserved]
    simp
  have hV : Fintype.card V = 1 := by simp [V]
  have hz : freshCountZero.readout () N A = 0 := rfl
  have hm := hMass a
  have htop : ν.toOuterMeasure {f | a.1 ∈ Set.range f.1} = ∞ := by
    change ν.toOuterMeasure {f | a.1 ∈ Set.range f.1} =
      ((Fintype.card V - Nat.card (↑((∅ : Set N) ∪ revealedNames T)) : ℕ) : ℝ≥0∞) /
        (freshCountZero.readout () N A : ℝ≥0∞) at hm
    simpa only [hV, hcard, hz, Nat.sub_zero, Nat.cast_one, Nat.cast_zero, one_div,
      ENNReal.inv_zero] using hm
  have hle : ν.toOuterMeasure {f | a.1 ∈ Set.range f.1} ≤ ν.toOuterMeasure Set.univ :=
    ν.toOuterMeasure.mono (Set.subset_univ _)
  rw [(ν.toOuterMeasure_apply_eq_one_iff Set.univ).mpr (Set.subset_univ _)] at hle
  rw [htop] at hle
  exact (not_le_of_gt ENNReal.one_lt_top) hle

private theorem freshCountVaries :
    freshCountActual.{v}.readout () (ULift.{v} Unit) ∅ ≠
      freshCountActual.{v}.readout () (ULift.{v} Unit) {⟨()⟩} := by
  simp [freshCountActual, realize]

def freshCountEvidence : Registration freshCountArena.{u, v}
    (type_of% (@conditional_unseen_name_hit.{u, v})) where
  actual := freshCountActual
  bridge := Iff.rfl
  variation := ⟨@conditional_unseen_name_hit.{u, v}, freshCountZero, rejectsZeroCount⟩
  sensitivity := ⟨fun i => ⟨freshCountZero,
    fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejectsZeroCount⟩, fun e => nomatch e⟩
  dependence := fun _ => ⟨ULift.{v} Unit, ∅, {⟨()⟩}, freshCountVaries⟩

def freshCountRegistration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@conditional_unseen_name_hit.{u, v}) (Realization freshCountSignature.{v}) Unit Unit := {
  unitName :=
    `Reg.D5.S3.Combinatorics.Graph.Queries.NamedNeighborhoodHistory.conditional_unseen_name_hit
  realizationName :=
    `Reg.D5.S3.Combinatorics.Graph.Queries.NamedNeighborhoodHistory.freshCountEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨freshCountArena.{u, v}⟩
  objectArena := .source ⟨freshCountArena.{u, v}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source freshCountArena.{u, v} ⟨freshCountEvidence.{u, v}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize freshCountSignature (fun _ _ names => names.ncard) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.Queries.NamedNeighborhoodHistory
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


private abbrev replaySignature : Signature where
  Params := Type v
  State N := Set N
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ N := Set N
  Anchor := Empty
  finiteAnchor := inferInstance

private def replayActual : Realization replaySignature.{v} :=
  realize replaySignature (fun _ _ banned => bannedᶜ) (fun e => nomatch e)

private def replayEmpty : Realization replaySignature.{v} :=
  realize replaySignature (fun _ _ _ => ∅) (fun e => nomatch e)

private abbrev replayArena : Arena where
  signature := replaySignature.{v}
  Law R := ∀ {V : Type u} {N : Type v}
    (G : SimpleGraph V) (p : PassiveProtocol N (fun _ => Option (Set N))) (f ref : V ↪ N)
    (initial : Set N) (_hinit : initial ⊆ Set.range ref),
    let record := runPassiveProtocol (nameReply G) p ref
    let observed := initial ∪ revealedNames record
    let available := R.readout () N (observed ∪ absentNames record)
    let agrees := ∀ v, ref v ∈ observed → f v = ref v
    (runPassiveProtocol (nameReply G) p f = record ∧ agrees) ↔
      (agrees ∧ ∀ v, ref v ∉ observed → f v ∈ available)

private theorem rejectsEmptyReplay : ¬ replayArena.{u, v}.Law replayEmpty := by
  intro h
  let f : ULift.{u} Unit ↪ ULift.{v} Unit := ⟨fun _ => ⟨()⟩, fun _ _ _ => Subsingleton.elim _ _⟩
  let p : PassiveProtocol (ULift.{v} Unit) (fun _ => Option (Set (ULift.{v} Unit))) := .stop
  have hr := (h ⊥ p f f ∅ (Set.empty_subset _)).mp ⟨rfl, fun _ _ => rfl⟩
  have hObs : f ⟨()⟩ ∉ (∅ : Set (ULift.{v} Unit)) ∪
      revealedNames (runPassiveProtocol (nameReply ⊥) p f) := by
    simp [p, runPassiveProtocol, revealedNames]
  exact hr.2 ⟨()⟩ hObs

private theorem replayVaries :
    replayActual.{v}.readout () (ULift.{v} Unit) ∅ ≠
      replayActual.{v}.readout () (ULift.{v} Unit) Set.univ := by
  intro h
  have hs := congrArg (fun s : Set (ULift.{v} Unit) => (⟨()⟩ : ULift.{v} Unit) ∈ s) h
  simp [replayActual, realize] at hs

def replayEvidence : Registration replayArena.{u, v} (type_of% (@history_fiber_iff.{u, v})) where
  actual := replayActual
  bridge := Iff.rfl
  variation := ⟨@history_fiber_iff.{u, v}, replayEmpty, rejectsEmptyReplay⟩
  sensitivity := ⟨fun i => ⟨replayEmpty,
    fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejectsEmptyReplay⟩, fun e => nomatch e⟩
  dependence := fun _ => ⟨ULift.{v} Unit, ∅, Set.univ, replayVaries⟩

def replayRegistration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@history_fiber_iff.{u, v}) (Realization replaySignature.{v}) Unit Unit := {
  unitName := `Reg.D5.S3.Combinatorics.Graph.Queries.NamedNeighborhoodHistory.history_fiber_iff
  realizationName :=
    `Reg.D5.S3.Combinatorics.Graph.Queries.NamedNeighborhoodHistory.replayEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨replayArena.{u, v}⟩
  objectArena := .source ⟨replayArena.{u, v}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source replayArena.{u, v} ⟨replayEvidence.{u, v}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize replaySignature (fun _ _ banned => bannedᶜ) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.Queries.NamedNeighborhoodHistory
    definition := none
    coordinates := #[1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "value"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

private abbrev answerSignature : Signature where
  Params := Type v
  State N := Set N
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ N := Option (Set N)
  Anchor := Empty
  finiteAnchor := inferInstance

private def answerActual : Realization answerSignature.{v} :=
  realize answerSignature (fun _ _ neighbors => some neighbors) (fun e => nomatch e)

private def answerMiss : Realization answerSignature.{v} :=
  realize answerSignature (fun _ _ _ => none) (fun e => nomatch e)

private abbrev answerArena : Arena where
  signature := answerSignature.{v}
  Law R := ∀ {V : Type u} {N : Type v} (G : SimpleGraph V) (f : V ↪ N) (x : V),
    nameReply G (f x) f = R.readout () N (f '' G.neighborSet x)

private theorem rejectsMiss : ¬ answerArena.{u, v}.Law answerMiss := by
  intro h
  let f : ULift.{u} Unit ↪ ULift.{v} Unit :=
    ⟨fun _ => ⟨()⟩, fun _ _ _ => Subsingleton.elim _ _⟩
  have hmiss := h (⊥ : SimpleGraph (ULift.{u} Unit)) f ⟨()⟩
  rw [answer_at_name] at hmiss
  change some _ = none at hmiss
  cases hmiss

private theorem answerVaries :
    answerActual.{v}.readout () (ULift.{v} Unit) ∅ ≠
      answerActual.{v}.readout () (ULift.{v} Unit) Set.univ := by
  change some ∅ ≠ some (Set.univ : Set (ULift.{v} Unit))
  exact fun h => Set.notMem_empty (⟨()⟩ : ULift.{v} Unit)
    ((Option.some.inj h).symm ▸ Set.mem_univ _)

def answerEvidence : Registration answerArena.{u, v} (type_of% (@answer_at_name.{u, v})) where
  actual := answerActual
  bridge := Iff.rfl
  variation := ⟨@answer_at_name.{u, v}, answerMiss, rejectsMiss⟩
  sensitivity := ⟨fun i => ⟨answerMiss, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl,
    rejectsMiss⟩, fun e => nomatch e⟩
  dependence := fun _ => ⟨ULift.{v} Unit, ∅, Set.univ, answerVaries⟩

def answerRegistration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@answer_at_name.{u, v}) (Realization answerSignature.{v}) Unit Unit := {
  unitName := `Reg.D5.S3.Combinatorics.Graph.Queries.NamedNeighborhoodHistory.answer_at_name
  realizationName := `Reg.D5.S3.Combinatorics.Graph.Queries.NamedNeighborhoodHistory.answerEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨answerArena.{u, v}⟩
  objectArena := .source ⟨answerArena.{u, v}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source answerArena.{u, v} ⟨answerEvidence.{u, v}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize answerSignature (fun _ _ neighbors => some neighbors)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.Queries.NamedNeighborhoodHistory
    definition := none
    coordinates := #[1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end
end Reg.D5.S3.Combinatorics.Graph.Queries.NamedNeighborhoodHistory
