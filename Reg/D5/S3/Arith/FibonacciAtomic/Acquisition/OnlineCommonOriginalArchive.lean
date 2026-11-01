import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.FibonacciAtomic.Acquisition.OnlineCommonOriginalArchive
import Reg.Support.DependentFamily

/-! Whole online archive law with a varying common-original readout. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open _root_.D5.S3.Arith.FibonacciAtomic.Acquisition
open _root_.D5.S3.Arith.FibonacciAtomic.Acquisition.OnlineCommonOriginalArchive
open _root_.D5.S3.Arith.FibonacciAtomic.Acquisition.SameHandleContinuation
  (SourceService Tariffs ServiceRun)
open _root_.D5.S3.Arith.FibonacciAtomic.TerminalGcdAcquisitionCost
  (residueSource step quantity costBound)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.Arith.FibonacciAtomic.Acquisition.OnlineCommonOriginalArchive

abbrev signature : Signature where
  Params := ℕ
  State _ := ℕ × ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ H := ZMod H × ZMod H
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ H v => residueSource H v) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => (0, 0)) (fun e => nomatch e)

/-- The original-label observation is the varying source field. All other
clauses retain their full operational meaning and original telescope. -/
structure ObservedSound (R : Realization signature) {Handle World : Type}
    (B : SourceService Handle World) (h : Handle) (x₀ : World) (a : Memory) (x : World) : Prop where
  tape : TapeRun B h x₀ a.tape x
  lawful : B.lawful h x
  positive : 0 < a.joint
  joint_eq : a.joint = joint a.requests
  maximum_eq : costBound a.joint = maximum a.requests
  precision_eq : a.precision = budget (costBound a.joint)
  original_eq : a.original = R.readout () (envelope a.precision) (B.value h x₀)
  current_eq : a.current = residueSource (envelope a.precision) (B.value h x)
  covered : ∀ H ∈ a.requests, 0 < H ∧ H ∣ envelope a.precision
  payment : if costBound a.joint = 0 then reads a.tape = 0 else
    reads a.tape ≤ 4 * a.precision - 2 ∧ 4 * a.precision - 2 < 8 * costBound a.joint

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {Handle World : Type} (B : SourceService Handle World)
    (h : Handle) (_complete : VariableCompletion B h) (p : Tariffs)
    (x₀ : World) (_hx₀ : B.lawful h x₀),
    (∀ is : List Input, ∃ a x, OnlineRun B h p initial x₀ is a x) ∧
    (∀ is a x, OnlineRun B h p initial x₀ is a x →
      ObservedSound R B h x₀ a x ∧ ArchiveService B h x₀ a x) ∧
    (∀ is a x H, 0 < H → OnlineRun B h p initial x₀ is a x →
      ∀ b y, RequestRun B h p a H x b y → Compatible a b) ∧
    (∀ old x E, 1 < E → TapeRun B h x₀ old x →
      ∀ es t y d n, ServiceRun B h p (PositiveClosingExecution.controller E) E
        (PositiveClosingExecution.controller E).initial x es t y d n →
      UpgradeRecovery B h x₀ old x E es d y)

private theorem actual_bridge : arena.Law actual ↔ type_of% (@complete_online_archive) := by
  constructor
  · intro law Handle World B h complete p x₀ hx₀
    obtain ⟨existsRun, safety, compatibility⟩ := law B h complete p x₀ hx₀
    refine ⟨existsRun, ?_, compatibility⟩
    intro is a x hr
    obtain ⟨s, service⟩ := safety is a x hr
    exact ⟨⟨s.tape, s.lawful, s.positive, s.joint_eq, s.maximum_eq,
      s.precision_eq, s.original_eq, s.current_eq, s.covered, s.payment⟩, service⟩
  · intro law Handle World B h complete p x₀ hx₀
    obtain ⟨existsRun, safety, compatibility⟩ := law B h complete p x₀ hx₀
    refine ⟨existsRun, ?_, compatibility⟩
    intro is a x hr
    obtain ⟨s, service⟩ := safety is a x hr
    exact ⟨⟨s.tape, s.lawful, s.positive, s.joint_eq, s.maximum_eq,
      s.precision_eq, s.original_eq, s.current_eq, s.covered, s.payment⟩, service⟩

private def arithmeticService : SourceService Unit (ℕ × ℕ) where
  value _ v := v
  lawful _ _ := True
  action _ b x y := y = step b x
  read _ H x g y := y = x ∧ g = Nat.gcd (quantity x) H
  action_effect := by intro h b x y hx ha; exact ⟨ha, trivial⟩
  read_effect := by intro h H x g y hx hr; exact ⟨hr.1, hr.2, trivial⟩

private theorem arithmetic_complete : VariableCompletion arithmeticService () := by
  intro H hH
  exact ⟨fun b x _ => ⟨step b x, rfl⟩,
    fun x _ => ⟨Nat.gcd (quantity x) H, x, rfl, rfl⟩⟩

private def zeroTariffs : Tariffs := ⟨fun _ => 0, fun _ => 0, fun _ => 0⟩

private theorem rejected_law : ¬ arena.Law rejected := by
  intro bad
  have good := complete_online_archive arithmeticService () arithmetic_complete
    zeroTariffs (1, 0) trivial
  obtain ⟨a, x, hr⟩ := good.1 [.request 2 (by decide)]
  have s := (good.2.1 _ _ _ hr).1
  have falseSound :=
    ((bad arithmeticService () arithmetic_complete zeroTariffs (1, 0) trivial).2.1 _ _ _ hr).1
  have ho : residueSource (envelope a.precision) (1, 0) = (0, 0) :=
    s.original_eq.symm.trans falseSound.original_eq
  have request_present : 2 ∈ a.requests := by
    cases hr with
    | request req tail =>
      cases tail
      cases req <;> simp [hit, install, initial]
  have hd := (s.covered 2 request_present).2
  have one_zero := congrArg Prod.fst ho
  have hom := ZMod.castHom hd (ZMod 2)
  have absurd := congrArg hom one_zero
  have : (1 : ZMod 2) = 0 := by simpa [residueSource] using absurd
  exact one_ne_zero this

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨2, (0, 0), (1, 0), ?_⟩
  intro he
  have h := congrArg Prod.fst he
  change (0 : ZMod 2) = 1 at h
  exact zero_ne_one h

def sourceRegistration : Registration arena (type_of% (@complete_online_archive)) where
  actual := actual
  bridge := actual_bridge.symm
  variation := ⟨actual_bridge.mpr complete_online_archive, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, rejected_law⟩,
    fun i => nomatch i⟩
  dependence := dependence

def registration : Contract.Registration.{0,1,1,0,0,0,0,0,0,0,0,0} (@complete_online_archive)
    (Realization signature) Type Unit where
  unitName := `completeOnlineArchive
  realizationName :=
    `Reg.D5.S3.Arith.FibonacciAtomic.Acquisition.OnlineCommonOriginalArchive.sourceRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨sourceRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ H v => residueSource H v) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `autoImplicit, value := .bool false },
    { name := `relaxedAutoImplicit, value := .bool false }]

#print axioms sourceRegistration

run_cmd do
  let allowed : Array Lean.Name := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``complete_online_archive, ``sourceRegistration, ``registration] do
    let axioms ← Lean.collectAxioms name
    for axiomName in axioms do
      unless allowed.contains axiomName do
        throwError "nonstandard axiom {axiomName} in {name}"

end Reg.D5.S3.Arith.FibonacciAtomic.Acquisition.OnlineCommonOriginalArchive
