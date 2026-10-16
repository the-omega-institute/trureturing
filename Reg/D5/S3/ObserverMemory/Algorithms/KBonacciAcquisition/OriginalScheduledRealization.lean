import D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.OriginalScheduledRealization
import Reg.Support.DependentFamily
import LeanInformationAuditInterface.Contract.Registration

open D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.OriginalScheduledRealization
open D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.OriginalScheduledWitnessTables
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.OriginalScheduledRealization
noncomputable section

abbrev Parameters := Σ L : ℕ, Σ stop : Bool,
  Σ _ : (Catalog stop L → List ℕ), Catalog stop L

@[reducible] def signature : Signature where
  Params := Parameters
  State _ := Source
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Config p.1
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature (fun _ p x =>
  ([], acquired p.2.1 (p.2.2.1 p.2.2.2) (reply x), some (p.2.2.2.val (fun i => reply x i))))
  (fun e => nomatch e)

def rejected : Realization signature := realize signature (fun _ p x =>
  ([], acquired p.2.1 (p.2.2.1 p.2.2.2) (reply x), some 0)) (fun e => nomatch e)

@[reducible] def arena : Arena where
  signature := signature
  Law R := ∀ (L : ℕ) (stop : Bool),
    ∃ schedule : Catalog stop L → List ℕ,
      (∀ f, (schedule f).length ≤ 2 ∧ (∀ i ∈ schedule f, i < L) ∧
        (stop = true → (schedule f).Pairwise (· < ·))) ∧
      ∀ f x,
        let b : Fin L → Bool := fun i => reply x i
        let log := acquired stop (schedule f) (reply x)
        let last := R.readout () ⟨L, stop, schedule, f⟩ x
        (last, log) ∈ StateTransition.eval
          (D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.OriginalScheduledWitnessTables.step
            (program stop (schedule f) f.val) (reply x)) ((schedule f, [], none), []) ∧
        log.length ≤ 2 ∧ log.map Prod.snd = view stop (schedule f) (reply x) ∧
        handoff x last = (x, mark (f.val b).val) ∧ consumer (handoff x last).2 = none

private theorem positive : arena.Law actual := original_scheduled_realization
private theorem faithful_bridge : (type_of% original_scheduled_realization) ↔ arena.Law actual :=
  Iff.rfl

private theorem negative : ¬arena.Law rejected := by
  intro law
  obtain ⟨schedule, _, result⟩ := law 1 false
  let f : Catalog false 1 := ⟨fun _ => 1, [], by simp, by simp, by simp, by simp⟩
  let x : Source := ⟨(5,1), by norm_num [Nat.fib]⟩
  have tape := congrArg (fun z : Source × Tape => z.2)
    (result f x).2.2.2.1
  have coord := congrArg (fun t : Tape => t.elim
    (fun z => z.2.val) (fun z => z.2.val)) tape
  norm_num [rejected, realize, handoff, f, mark] at coord

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  let f : Catalog false 1 := ⟨fun _ => 0, [], by simp, by simp, by simp, by simp⟩
  let p : Parameters := ⟨1,false,fun _ => [0],f⟩
  let x : Source := ⟨(5,1), by norm_num [Nat.fib]⟩
  let y : Source := ⟨(7,2), by norm_num [Nat.fib]⟩
  refine ⟨p,x,y,?_⟩
  intro h
  have logs := congrArg (fun z : Config 1 => z.2.1) h
  norm_num [actual, realize, p, f, x, y, acquired, reply, Nat.fib] at logs

def evidence : Registration arena (type_of% original_scheduled_realization) where
  actual := actual
  bridge := faithful_bridge
  variation := ⟨positive, rejected, negative⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, (by intro j hj; exact (hj (Subsingleton.elim _ _)).elim),
        (by funext e; exact nomatch e), negative⟩
    · intro e; exact nomatch e
  dependence := dependence

noncomputable def registration : LeanInformationAudit.Contract.Registration.{0,0,1,0,0,0,0,0,0,0,0,0}
    original_scheduled_realization
    (type_of% (realize signature actual.readout actual.anchor)) Unit Unit := {
  unitName := `Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.OriginalScheduledRealization.original_scheduled_realization,
  realizationName := `Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.OriginalScheduledRealization.evidence,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨evidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature (fun _ p x =>
    ([], acquired p.2.1 (p.2.2.1 p.2.2.2) (reply x), some (p.2.2.2.val (fun i => reply x i))))
    (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.OriginalScheduledRealization,
    definition := none, coordinates := #[0, 1, 2, 3],
    readouts := #[{
      path := #["body", "body", "arg", "body", "arg", "body", "body", "body", "body", "value"],
      stateBinder := 4, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none, options := #[] }

#print axioms faithful_bridge
#print axioms evidence
#print axioms registration
end
end Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.OriginalScheduledRealization
