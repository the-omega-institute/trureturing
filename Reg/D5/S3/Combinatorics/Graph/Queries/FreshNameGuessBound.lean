import D5.S3.Combinatorics.Graph.Queries.FreshNameGuessBound
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.ConceptDynamics.Experiment.PassiveAdaptiveTranscriptUpperBound
open _root_.D5.S0.Diagonal.Probability.EquivariantEscape
open _root_.D5.S3.Combinatorics.Graph.Queries.NamedNeighborhoodHistory
open _root_.D5.S3.Combinatorics.Graph.Queries.KnownNameSimulation
open _root_.D5.S3.Combinatorics.Graph.Queries.FreshNameGuessBound
open scoped ENNReal

namespace Reg.D5.S3.Combinatorics.Graph.Queries.FreshNameGuessBound

noncomputable section
universe u v

private abbrev signature : Signature where
  Params := Type v
  State N := Set N
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

private def actual : Realization signature.{v} :=
  realize signature (fun _ _ names => names.ncard) (fun e => nomatch e)

private def one : Realization signature.{v} :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

private abbrev arena : Arena where
  signature := signature.{v}
  Law R := ∀ {V : Type u} {N : Type v} [Fintype V] [Fintype N]
    (G : SimpleGraph V) (p : Protocol N) (base : V ↪ N)
    (initial : Set N) (_hinit : initial ⊆ Set.range base) (q : ℕ),
    let available := Fintype.card N - R.readout () N initial
    let invalid := Fintype.card N - Fintype.card V
    let r := min q available
    let X := {f : V ↪ N // ∀ v, base v ∈ initial → f v = base v}
    let : Fintype X := Fintype.ofFinite X
    let : Nonempty X := ⟨⟨base, fun _ _ => rfl⟩⟩
    (↑(invalid.choose r) : ℝ≥0∞) / ↑(available.choose r) ≤
      (uniformPmf X).toOuterMeasure
        {f | noGuessedHit initial (runPassiveProtocol (nameReply G) (truncate p q) f.1)}

private theorem rejectsOne : ¬ arena.{u, v}.Law one := by
  classical
  intro h
  let G : SimpleGraph (ULift.{u} Unit) := ⊥
  let name : ULift.{v} Unit := ⟨()⟩
  let f : ULift.{u} Unit ↪ ULift.{v} Unit :=
    ⟨fun _ => name, fun _ _ _ => Subsingleton.elim _ _⟩
  let p : Protocol (ULift.{v} Unit) := .query name (fun _ => .stop)
  have hbad := h G p f ∅ (Set.empty_subset _) 1
  dsimp only [one, realize] at hbad
  have hLeft : (↑((Fintype.card (ULift.{v} Unit) - Fintype.card (ULift.{u} Unit)).choose
      (min 1 (Fintype.card (ULift.{v} Unit) - 1))) : ℝ≥0∞) /
      ↑((Fintype.card (ULift.{v} Unit) - 1).choose
      (min 1 (Fintype.card (ULift.{v} Unit) - 1))) = 1 := by simp
  rw [hLeft] at hbad
  let X := {g : ULift.{u} Unit ↪ ULift.{v} Unit // ∀ v, f v ∈ (∅ : Set (ULift.{v} Unit)) → g v = f v}
  have hE : ({g : X | noGuessedHit ∅
      (runPassiveProtocol (nameReply G) (truncate p 1) g.1)} : Set X) = ∅ := by
    ext g
    have hname : name ∈ Set.range g.1 := ⟨⟨()⟩, Subsingleton.elim _ _⟩
    have hr : nameReply G name g.1 = some (g.1 '' G.neighborSet hname.choose) := by
      rw [nameReply, dite_eq_left hname]
    change noGuessedHit ∅ [⟨name, nameReply G name g.1⟩] ↔ False
    rw [hr]
    simp [noGuessedHit]
  rw [hE, MeasureTheory.measure_empty] at hbad
  exact not_le_of_gt zero_lt_one hbad

private theorem actualVaries :
    actual.{v}.readout () (ULift.{v} Unit) ∅ ≠
      actual.{v}.readout () (ULift.{v} Unit) Set.univ := by
  simp [actual, realize, Nat.card_eq_fintype_card]

def evidence : Registration arena.{u, v} (type_of% (@fresh_guess_survival_ge.{u, v})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@fresh_guess_survival_ge.{u, v}, one, rejectsOne⟩
  sensitivity := ⟨fun i => ⟨one, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejectsOne⟩,
    fun e => nomatch e⟩
  dependence := fun _ => ⟨ULift.{v} Unit, ∅, Set.univ, actualVaries⟩

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@fresh_guess_survival_ge.{u, v}) (Realization signature.{v}) Unit Unit := {
  unitName := `Reg.D5.S3.Combinatorics.Graph.Queries.FreshNameGuessBound.fresh_guess_survival_ge
  realizationName := `Reg.D5.S3.Combinatorics.Graph.Queries.FreshNameGuessBound.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u, v}⟩
  objectArena := .source ⟨arena.{u, v}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u, v} ⟨evidence.{u, v}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ names => names.ncard) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.Queries.FreshNameGuessBound
    definition := none
    coordinates := #[1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "value", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }


private def zero : Realization signature.{v} :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

private abbrev attainmentArena : Arena where
  signature := signature.{v}
  Law R := ∀ {V : Type u} {N : Type v} [Fintype V] [Fintype N]
    (G : SimpleGraph V) (base : V ↪ N) (initial : Set N)
    (_hinit : initial ⊆ Set.range base) (q : ℕ),
    let available := Fintype.card N - R.readout () N initial
    let invalid := Fintype.card N - Fintype.card V
    let r := min q available
    let X := {f : V ↪ N // ∀ v, base v ∈ initial → f v = base v}
    let : Fintype X := Fintype.ofFinite X
    let : Nonempty X := ⟨⟨base, fun _ _ => rfl⟩⟩
    ∃ p : Protocol N, depthBound p q ∧
      (uniformPmf X).toOuterMeasure
        {f | noGuessedHit initial (runPassiveProtocol (nameReply G) (truncate p q) f.1)} =
      (↑(invalid.choose r) : ℝ≥0∞) / ↑(available.choose r)

private theorem rejectsZero : ¬ attainmentArena.{u, v}.Law zero := by
  classical
  intro h
  let V := ULift.{u} Unit
  let N := ULift.{v} Unit
  let G : SimpleGraph V := ⊥
  let base : V ↪ N := ⟨fun _ => ⟨()⟩, fun _ _ _ => Subsingleton.elim _ _⟩
  have hinit : Set.univ ⊆ Set.range base := fun n _ => ⟨⟨()⟩, Subsingleton.elim _ _⟩
  obtain ⟨p, _, hm⟩ := h G base Set.univ hinit 1
  let X := {f : V ↪ N // ∀ v, base v ∈ (Set.univ : Set N) → f v = base v}
  have hE : ({f : X | noGuessedHit Set.univ
      (runPassiveProtocol (nameReply G) (truncate p 1) f.1)} : Set X) = Set.univ := by
    ext f
    simp only [Set.mem_univ, iff_true]
    cases p with
    | stop => trivial
    | query name next =>
      simp [truncate, runPassiveProtocol, noGuessedHit]
  rw [hE] at hm
  let : Fintype X := Fintype.ofFinite X
  let : Nonempty X := ⟨⟨base, fun _ _ => rfl⟩⟩
  have hone : (uniformPmf X).toOuterMeasure Set.univ = 1 :=
    ((uniformPmf X).toOuterMeasure_apply_eq_one_iff Set.univ).mpr (Set.subset_univ _)
  rw [hone] at hm
  dsimp only [zero, realize] at hm
  simp [V, N] at hm

def attainmentEvidence :
    Registration attainmentArena.{u, v}
      (type_of% (@exists_strategy_attaining_guess_survival.{u, v})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@exists_strategy_attaining_guess_survival.{u, v}, zero, rejectsZero⟩
  sensitivity := ⟨fun i => ⟨zero, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejectsZero⟩,
    fun e => nomatch e⟩
  dependence := fun _ => ⟨ULift.{v} Unit, ∅, Set.univ, actualVaries⟩

def attainmentRegistration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@exists_strategy_attaining_guess_survival.{u, v}) (Realization signature.{v}) Unit Unit := {
  unitName := `Reg.D5.S3.Combinatorics.Graph.Queries.FreshNameGuessBound.exists_strategy_attaining_guess_survival
  realizationName := `Reg.D5.S3.Combinatorics.Graph.Queries.FreshNameGuessBound.attainmentEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨attainmentArena.{u, v}⟩
  objectArena := .source ⟨attainmentArena.{u, v}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source attainmentArena.{u, v} ⟨attainmentEvidence.{u, v}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ names => names.ncard) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.Queries.FreshNameGuessBound
    definition := none
    coordinates := #[1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "value", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end
end Reg.D5.S3.Combinatorics.Graph.Queries.FreshNameGuessBound
