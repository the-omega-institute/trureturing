import D5.S3.Combinatorics.Graph.Queries.KnownNameSimulation
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import Mathlib.Probability.ProbabilityMassFunction.Monad

/-! Oracle call counts and the record coordinates of known-name simulation. -/

open LeanInformationAudit
open _root_.D5.S3.Combinatorics.Graph.Queries.KnownNameSimulation
open _root_.D5.S3.ConceptDynamics.Experiment.PassiveAdaptiveTranscriptUpperBound
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.Combinatorics.Graph.Queries.KnownNameSimulation

noncomputable section
universe u v

private abbrev budgetSignature : Signature where
  Params := Type u
  State N := List N
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

private def actualBudget : Realization budgetSignature.{u} :=
  realize budgetSignature (fun _ _ calls => calls.length) (fun e => nomatch e)

private def positiveBudget : Realization budgetSignature.{u} :=
  realize budgetSignature (fun _ _ _ => 1) (fun e => nomatch e)

private abbrev budgetArena : Arena where
  signature := budgetSignature.{u}
  Law R := ∀ {N : Type u} (read : N → Reply N) (p : Protocol N)
    (known : Set N) (n : ℕ) (_hn : depthBound p n),
    let callCount := R.readout () N (sentNames known (simulate read p known))
    callCount ≤ n

private theorem rejectsPositiveBudget : ¬ budgetArena.{u}.Law positiveBudget := by
  intro h
  exact (by decide : ¬ (1 : ℕ) ≤ 0)
    (h (fun _ : ULift.{u} Unit => none) .stop ∅ 0 trivial)

private theorem budgetVaries :
    actualBudget.{u}.readout () (ULift.{u} Unit) [] ≠
      actualBudget.{u}.readout () (ULift.{u} Unit) [⟨()⟩] := by
  simp [actualBudget, realize]

def budgetEvidence : Registration budgetArena.{u} (type_of% (@simulated_sent_names_bound.{u})) where
  actual := actualBudget
  bridge := Iff.rfl
  variation := ⟨@simulated_sent_names_bound.{u}, positiveBudget, rejectsPositiveBudget⟩
  sensitivity := ⟨fun i => ⟨positiveBudget,
    fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejectsPositiveBudget⟩,
    fun e => nomatch e⟩
  dependence := fun _ => ⟨ULift.{u} Unit, [], [⟨()⟩], budgetVaries⟩

def budgetRegistration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@simulated_sent_names_bound.{u}) (Realization budgetSignature.{u}) Unit Unit := {
  unitName := `Reg.D5.S3.Combinatorics.Graph.Queries.KnownNameSimulation.simulated_sent_names_bound
  realizationName := `Reg.D5.S3.Combinatorics.Graph.Queries.KnownNameSimulation.budgetEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨budgetArena.{u}⟩
  objectArena := .source ⟨budgetArena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source budgetArena.{u} ⟨budgetEvidence.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize budgetSignature (fun _ _ calls => calls.length) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.Queries.KnownNameSimulation
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "value"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

private abbrev successSignature : Signature where
  Params := Type v
  State W := Set W
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ W := Set W
  Anchor := Empty
  finiteAnchor := inferInstance

private def actualSuccess : Realization successSignature.{v} :=
  realize successSignature (fun _ _ noGuess => noGuessᶜ) (fun e => nomatch e)

private def emptySuccess : Realization successSignature.{v} :=
  realize successSignature (fun _ _ _ => ∅) (fun e => nomatch e)

private abbrev successArena : Arena where
  signature := successSignature.{v}
  Law R := ∀ {N : Type u} {W : Type v}
    (μ : PMF W) (read : W → N → Reply N) (p : Protocol N) (known : Set N)
    (wins : W → Record N → Prop),
    let noGuessEvent := {w | noGuessedHit known (replayPassiveProtocol p (read w))}
    let guessedHit := R.readout () W noGuessEvent
    μ.toOuterMeasure {w | wins w (replayPassiveProtocol p (read w))} ≤
      μ.toOuterMeasure {w | wins w (simulate (read w) p known)} + μ.toOuterMeasure guessedHit

private theorem rejectsEmptySuccess : ¬ successArena.{u, v}.Law emptySuccess := by
  classical
  intro h
  let N := ULift.{u} Unit
  let W := ULift.{v} Unit
  let query : N := ⟨()⟩
  let p : Protocol N := .query query (fun _ => .stop)
  let read : W → N → Reply N := fun _ _ => some ∅
  let μ : PMF W := PMF.pure ⟨()⟩
  let wins (_ : W) (record : Record N) : Prop :=
    record.head?.map (fun entry => entry.2.isSome) = some true
  have hReal : {w | wins w (replayPassiveProtocol p (read w))} = Set.univ := by
    ext w
    simp [wins, p, read, replayPassiveProtocol]
  have hSimulated : {w | wins w (simulate (read w) p ∅)} = ∅ := by
    ext w
    simp [wins, p, simulate]
  have hBad := h μ read p ∅ wins
  change μ.toOuterMeasure {w | wins w (replayPassiveProtocol p (read w))} ≤
    μ.toOuterMeasure {w | wins w (simulate (read w) p ∅)} + μ.toOuterMeasure ∅ at hBad
  rw [hReal, hSimulated, (μ.toOuterMeasure_apply_eq_one_iff Set.univ).mpr (Set.subset_univ _)] at hBad
  simp at hBad

private theorem successVaries :
    actualSuccess.{v}.readout () (ULift.{v} Unit) ∅ ≠
      actualSuccess.{v}.readout () (ULift.{v} Unit) Set.univ := by
  intro h
  have hs := congrArg (fun s : Set (ULift.{v} Unit) => (⟨()⟩ : ULift.{v} Unit) ∈ s) h
  simp [actualSuccess, realize] at hs

def successEvidence : Registration successArena.{u, v}
    (type_of% (@success_mass_le_simulated_add_guessed_hit.{u, v})) where
  actual := actualSuccess
  bridge := Iff.rfl
  variation := ⟨@success_mass_le_simulated_add_guessed_hit.{u, v},
    emptySuccess, rejectsEmptySuccess⟩
  sensitivity := ⟨fun i => ⟨emptySuccess,
    fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejectsEmptySuccess⟩,
    fun e => nomatch e⟩
  dependence := fun _ => ⟨ULift.{v} Unit, ∅, Set.univ, successVaries⟩

def successRegistration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@success_mass_le_simulated_add_guessed_hit.{u, v}) (Realization successSignature.{v})
        Unit Unit := {
  unitName :=
    `Reg.D5.S3.Combinatorics.Graph.Queries.KnownNameSimulation.success_mass_le_simulated_add_guessed_hit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.Queries.KnownNameSimulation.successEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨successArena.{u, v}⟩
  objectArena := .source ⟨successArena.{u, v}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source successArena.{u, v} ⟨successEvidence.{u, v}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize successSignature (fun _ _ noGuess => noGuessᶜ) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.Queries.KnownNameSimulation
    definition := none
    coordinates := #[1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "value"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

private abbrev nextSignature : Signature where
  Params := Type u
  State N := Option (Σ _ : N, Reply N)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ N := Option N
  Anchor := Empty
  finiteAnchor := inferInstance

private def actualNext : Realization nextSignature.{u} :=
  realize nextSignature (fun _ _ entry => entry.map Sigma.fst) (fun e => nomatch e)

private def emptyNext : Realization nextSignature.{u} :=
  realize nextSignature (fun _ _ _ => none) (fun e => nomatch e)

private abbrev nextArena : Arena where
  signature := nextSignature.{u}
  Law R := ∀ {N : Type u} (read : N → Reply N) (p : Protocol N) (n : ℕ),
    let recordedQuery := R.readout () N (replayPassiveProtocol p read)[n]?
    nextQuery p (replayPassiveProtocol (truncate p n) read) = recordedQuery

private theorem rejectsEmptyNext : ¬ nextArena.{u}.Law emptyNext := by
  intro h
  let q : ULift.{u} Unit := ⟨()⟩
  have hb := h (fun _ => none) (.query q (fun _ => .stop)) 0
  simpa [emptyNext, realize, truncate, replayPassiveProtocol, nextQuery] using hb

private theorem nextVaries :
    actualNext.{u}.readout () (ULift.{u} Unit) none ≠
      actualNext.{u}.readout () (ULift.{u} Unit) (some ⟨⟨()⟩, none⟩) := by
  simp [actualNext, realize]

def nextEvidence : Registration nextArena.{u} (type_of% (@nextQuery_of_prefix.{u})) where
  actual := actualNext
  bridge := Iff.rfl
  variation := ⟨@nextQuery_of_prefix.{u}, emptyNext, rejectsEmptyNext⟩
  sensitivity := ⟨fun i => ⟨emptyNext,
    fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejectsEmptyNext⟩, fun e => nomatch e⟩
  dependence := fun _ => ⟨ULift.{u} Unit, none, some ⟨⟨()⟩, none⟩, nextVaries⟩

def nextRegistration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@nextQuery_of_prefix.{u}) (Realization nextSignature.{u}) Unit Unit := {
  unitName := `Reg.D5.S3.Combinatorics.Graph.Queries.KnownNameSimulation.nextQuery_of_prefix
  realizationName := `Reg.D5.S3.Combinatorics.Graph.Queries.KnownNameSimulation.nextEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨nextArena.{u}⟩
  objectArena := .source ⟨nextArena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source nextArena.{u} ⟨nextEvidence.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize nextSignature (fun _ _ entry => entry.map Sigma.fst)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.Queries.KnownNameSimulation
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "value"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end
end Reg.D5.S3.Combinatorics.Graph.Queries.KnownNameSimulation
