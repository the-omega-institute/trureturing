import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.FibonacciAtomic.Acquisition.SameHandleContinuation
import Reg.Support.DependentFamily

/-! The full returned-service law, with its actual earned entry readout. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open _root_.D5.S3.Arith.FibonacciAtomic.Acquisition.SameHandleContinuation
open _root_.D5.S3.Arith.FibonacciAtomic.Acquisition
open _root_.D5.S3.Arith.FibonacciAtomic.TerminalGcdAcquisitionCost
  (residueSource runWord terminalGcd step quantity costBound)
open _root_.D5.S3.Arith.FibonacciAtomic.Acquisition.ContinuousAcquisitionTransport
  (Controller Run paidReads)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.Arith.FibonacciAtomic.Acquisition.SameHandleContinuation
universe u

structure Parameters where
  Handle : Type
  World : Type
  H : ℕ
  service : SourceService Handle World
  handle : Handle
  tariffs : Tariffs

abbrev signature : Signature where
  Params := Parameters
  State a := a.World
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ a := ZMod a.H × ZMod a.H
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ a x => residueSource a.H (a.service.value a.handle x))
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => (0, 0)) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {Handle World : Type} (H : ℕ) (_hH : 1 ≤ H)
    (B : SourceService Handle World) (h : Handle) (_complete : Completion B h H)
    (p : Tariffs) (x : World) (_hx : B.lawful h x) ,
    let v := B.value h x
    let w := PositiveClosingExecution.executionWord H v
    let es := PositiveClosingExecution.executionEvents H v
    let e := R.readout () ⟨Handle, World, H, B, h, p⟩ x
    ∃ t y,
      ServiceRun B h p (PositiveClosingExecution.controller H) H
        (PositiveClosingExecution.controller H).initial x es t y e (serviceBill p es v) ∧
      B.value h y = runWord w v ∧ B.lawful h y ∧
      paidReads es = (if H = 1 then 0 else 2 * costBound H) ∧
      (H = 1 → y = x) ∧
      (∀ (S : Type u) (P : Controller S (ZMod H × ZMod H)) (J : ℕ),
        (∀ z : ℕ × ℕ, ∃ rs s u,
          Run P H P.initial z rs s u (residueSource H z) ∧ paidReads rs ≤ J) →
        paidReads es ≤ J) ∧
      Continued B h H v e y ∧
      (∀ rs t' y' l' n',
        ServiceRun B h p (PositiveClosingExecution.controller H) H
          (PositiveClosingExecution.controller H).initial x rs t' y' l' n' →
        rs = es ∧ t' = t ∧ l' = e ∧
        B.value h y' = runWord w v ∧ B.lawful h y' ∧
        n' = serviceBill p es v ∧ (H = 1 → y' = x) ∧ Continued B h H v e y')

private def arithmeticService (H : ℕ) : SourceService Unit (ℕ × ℕ) where
  value _ x := x
  lawful _ _ := True
  action _ b x y := y = step b x
  read _ K x g y := K = H ∧ y = x ∧ g = Nat.gcd (quantity x) H
  action_effect := by
    intro h b x y hx ha
    exact ⟨ha, trivial⟩
  read_effect := by
    intro h H x g y hx hr
    rcases hr with ⟨rfl, rfl, rfl⟩
    exact ⟨rfl, rfl, trivial⟩

private theorem arithmeticComplete (H : ℕ) : Completion (arithmeticService H) () H :=
  ⟨fun b x _ => ⟨step b x, rfl⟩,
    fun x _ => ⟨Nat.gcd (quantity x) H, x, rfl, rfl, rfl⟩⟩

private def zeroTariffs : Tariffs := ⟨fun _ => 0, fun _ => 0, fun _ => 0⟩

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro bad
  obtain ⟨t, y, hr, hv, hl, reads, h1, competitor, continued, allAcquisitions⟩ :=
    @bad Unit (ℕ × ℕ) 2 (by decide) (arithmeticService 2) () (arithmeticComplete 2)
      zeroTariffs (1, 0) trivial
  obtain ⟨aligned, cuts, continuations, actualWords, future⟩ := continued
  have hf := (future [true]).1.trans (future [true]).2
  have hp : predict 2 (0, 0) [true] = 2 := by decide +kernel
  have hq : terminalGcd 2 [true] (1, 0) = 1 := by decide +kernel
  change predict 2 (0, 0) [true] = terminalGcd 2 [true] (1, 0) at hf
  rw [hp, hq] at hf
  omega

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨Unit, ℕ × ℕ, 2, arithmeticService 2, (), zeroTariffs⟩, (0, 0), (1, 0), ?_⟩
  intro h
  have he := congrArg Prod.fst h
  change (0 : ZMod 2) = 1 at he
  exact zero_ne_one he

def sourceRegistration : Registration arena.{u} (type_of% (@same_handle_return.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨same_handle_return, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, rejected_law⟩,
    fun i => nomatch i⟩
  dependence := dependence

def registration : Contract.Registration.{1,1,1,0,0,0,1,0,0,0,0,0} (@same_handle_return.{u})
    (Realization signature) Type Unit where
  unitName := `sameHandleReturn
  realizationName :=
    `Reg.D5.S3.Arith.FibonacciAtomic.Acquisition.SameHandleContinuation.sourceRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena.{u} ⟨sourceRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ a x => residueSource a.H (a.service.value a.handle x)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Acquisition.SameHandleContinuation
    definition := none
    coordinates := #[0, 1, 2, 4, 5, 7]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "letValue"]
      stateBinder := 8
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `autoImplicit, value := .bool false },
    { name := `relaxedAutoImplicit, value := .bool false }]

#print axioms sourceRegistration

run_cmd do
  let allowed : Array Lean.Name := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``same_handle_return, ``sourceRegistration, ``registration] do
    let axioms ← Lean.collectAxioms name
    for axiomName in axioms do
      unless allowed.contains axiomName do
        throwError "nonstandard axiom {axiomName} in {name}"

end Reg.D5.S3.Arith.FibonacciAtomic.Acquisition.SameHandleContinuation
