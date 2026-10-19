import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.OriginalNativeServiceBridge
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Classical MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.OriginalNativeServiceBridge
open _root_.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws
open FourthSegmentStoppedLaw NativeAcquiredPrefixState NativeAcquiredPrefixCylinder
open NativeFullResidual OriginalNativeServiceBridge
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev receiptSignature : Signature where
  Params := AcquiredNativeState × List Operation
  State _ := List Operation
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := List (List OriginalEvent) × List Letter
  Anchor := Empty
  finiteAnchor := inferInstance

def receiptActual : Realization receiptSignature :=
  realize receiptSignature (fun _ cv p =>
    (eventBlocks cv.1.source.finiteFields (p ++ cv.2),
     acquiredLetters (eventBlocks cv.1.source.finiteFields (p ++ cv.2)).flatten))
    (fun e => nomatch e)
def receiptBad : Realization receiptSignature :=
  realize receiptSignature (fun _ _ _ => ([], [])) (fun e => nomatch e)
def receiptArena : Arena where
  signature := receiptSignature
  Law Q := ∀ (c d e : AcquiredNativeState) (p v : List Operation),
    execute c p = some d → execute d v = some e →
    (Q.readout () (c,v) p).1 =
      eventBlocks c.source.finiteFields p ++ eventBlocks d.source.finiteFields v ∧
    (Q.readout () (c,v) p).2 = readLetters p ++ readLetters v
def afterFirst : AcquiredNativeState := (nativeStep initial (.read 0)).getD initial
private theorem receipt_bad_invalid : ¬ receiptArena.Law receiptBad := by
  intro h
  have hh := (h initial afterFirst afterFirst [.read 0] [] rfl rfl).2
  simpa [receiptBad, realize, readLetters] using hh
def receiptRecord : Registration receiptArena (type_of% (@lawful_receipt_extension)) where
  actual := receiptActual
  bridge := Iff.rfl
  variation := ⟨lawful_receipt_extension, receiptBad, receipt_bad_invalid⟩
  sensitivity := by
    letI : Subsingleton receiptArena.signature.Role := by change Subsingleton Unit; infer_instance
    constructor
    · intro i
      refine ⟨receiptBad, ?_, rfl, receipt_bad_invalid⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro i; exact nomatch i
  dependence := by
    intro i
    refine ⟨(initial,[]), [], [.read 0], ?_⟩
    intro h
    have hh := congrArg Prod.snd h
    simpa [receiptActual, realize, acquiredLetters, acquiredEvent,
      eventBlocks, eventBlock, initial] using hh

def receiptRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@lawful_receipt_extension) (type_of% (realize receiptSignature
      (fun _ cv p => (eventBlocks cv.1.source.finiteFields (p ++ cv.2),
        acquiredLetters (eventBlocks cv.1.source.finiteFields (p ++ cv.2)).flatten))
      (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.OriginalNativeServiceBridge.lawful_receipt_extension.__information_unit,
  realizationName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.OriginalNativeServiceBridge.receiptRecord,
  realizationSource := none, generated := false,
  arena := .source ⟨receiptArena⟩, objectArena := .source ⟨receiptArena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source receiptArena ⟨receiptRecord⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize receiptSignature
    (fun _ cv p => (eventBlocks cv.1.source.finiteFields (p ++ cv.2),
      acquiredLetters (eventBlocks cv.1.source.finiteFields (p ++ cv.2)).flatten))
    (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.OriginalNativeServiceBridge,
    definition := none, coordinates := #[0,4],
    readouts := #[
      { path := #["body","body","body","body","body","body","body","fn","arg","fn","arg"],
        stateBinder := 3, functionOperand := false, stateOperand := none, booleanPredicate := false },
      { path := #["body","body","body","body","body","body","body","arg","fn","arg"],
        stateBinder := 3, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none,
  options := #[{ name := `relaxedAutoImplicit, value := .bool false }] }


namespace InitializationAudit
open Set
open scoped ENNReal BigOperators
open _root_.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FiniteFairBitFirstReturn
open _root_.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.OriginalNativeServiceBridge.Initialization
open _root_.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FiniteFairBitExitLaws
open _root_.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FiniteFairBitDenominator

structure Family where
  S : Type
  H : Type
  T : Type
  headEq : DecidableEq H
  symbolEq : DecidableEq T
  B : ℕ
  A : @Architecture S H T headEq symbolEq B

abbrev prefixSignature : Signature where
  Params := Family
  State C := C.S × (ℕ → Bool) × ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ C := PrefixValue C.S C.T
  Anchor := Empty
  finiteAnchor := inferInstance

def prefixActual : Realization prefixSignature :=
  realize prefixSignature (fun _ C z => @nativePrefix C.S C.H C.T C.headEq C.symbolEq C.B
    C.A z.1 z.2.1 z.2.2) (fun e => nomatch e)
def prefixBad : Realization prefixSignature :=
  realize prefixSignature (fun _ C z =>
    let p := @nativePrefix C.S C.H C.T C.headEq C.symbolEq C.B C.A z.1 z.2.1 z.2.2
    { p with requests := p.requests + 1 }) (fun e => nomatch e)

def prefixArena : Arena where
  signature := prefixSignature
  Law Q := ∀ {S H T : Type} [DecidableEq H] [DecidableEq T] {B : ℕ}
    (A : Architecture S H T B) (s : S) (ω : ℕ → Bool) (n : ℕ),
    Q.readout () ⟨S,H,T,inferInstance,inferInstance,B,A⟩ (s,ω,n) = graphPrefix A s ω n ∧
    NativePrefix A s ω n
      (Q.readout () ⟨S,H,T,inferInstance,inferInstance,B,A⟩ (s,ω,n)).statesAndReceipts
      (Q.readout () ⟨S,H,T,inferInstance,inferInstance,B,A⟩ (s,ω,n)).unused

-- One reachable snapshot still pays the literal resident bit.
def unitArchitecture : Architecture Unit Unit Unit 1 where
  headFinite := inferInstance
  symbolFinite := inferInstance
  paid := {
    resident := [false]
    residentSite := ⟨fun _ => 0, by
      intro i j h
      apply Fin.ext
      have hi : i.val < 1 := i.isLt
      have hj : j.val < 1 := j.isLt
      omega⟩
    complete := ⟨fun _ _ => false, fun _ _ _ => Subsingleton.elim _ _⟩
    resident_exact := by intro s i; have hi : i = 0 := Fin.ext (by
      change i.val = 0
      have h := i.isLt; simp only [List.length_cons, List.length_nil] at h; omega); subst i; rfl
    runtimePeak := 0
    installationTotalPeak := 1
    online_bound := by decide
    installation_bound := by decide }
  memoryCell := fun _ => True
  head := fun _ _ => 0
  head_owned := by intros; trivial
  buffer := fun _ => none
  pc := fun _ => 0
  branchBit := fun _ => 0
  branchZero := fun _ => 0
  branchOne := fun _ => 0
  randomCell := fun _ => none
  readLatch := fun _ => 0
  initFrame := fun _ => none
  ready := fun _ => True
  action := fun _ => .booleanBranch
  enabled := fun _ => True
  nativeEdge := fun _ _ r => r = ((), ⟨none,none,none⟩)
  result := fun _ _ => ((), ⟨none,none,none⟩)
  result_iff := by intros; simp
  deterministic := by intros; rfl
  local_effect := by intro s b h; dsimp; simp

private theorem prefix_bad_invalid : ¬ prefixArena.Law prefixBad := by
  intro h
  have hh := (h unitArchitecture () (fun _ => false) 0).1
  have hr := congrArg PrefixValue.requests hh
  norm_num [prefixBad, realize, nativePrefix, graphPrefix] at hr

def prefixRecord : Registration prefixArena
    (type_of% (@original_primitive_prefix_refinement)) where
  actual := prefixActual
  bridge := Iff.rfl
  variation := ⟨original_primitive_prefix_refinement, prefixBad, prefix_bad_invalid⟩
  sensitivity := by
    letI : Subsingleton prefixArena.signature.Role := by change Subsingleton Unit; infer_instance
    constructor
    · intro i
      refine ⟨prefixBad, ?_, rfl, prefix_bad_invalid⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro i; exact nomatch i
  dependence := by
    intro i
    refine ⟨⟨Unit,Unit,Unit,inferInstance,inferInstance,1,unitArchitecture⟩,
      ((),(fun _ => false),0), ((),(fun _ => false),1), ?_⟩
    intro h
    have hh := congrArg PrefixValue.statesAndReceipts h
    simp [prefixActual, realize, nativePrefix, nativeTick, unitArchitecture] at hh

def prefixRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@original_primitive_prefix_refinement)
    (type_of% (realize prefixSignature (fun _ C z =>
      @nativePrefix C.S C.H C.T C.headEq C.symbolEq C.B C.A z.1 z.2.1 z.2.2)
      (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.OriginalNativeServiceBridge.original_primitive_prefix_refinement.__information_unit,
  realizationName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.OriginalNativeServiceBridge.InitializationAudit.prefixRecord,
  realizationSource := none, generated := false,
  arena := .source ⟨prefixArena⟩, objectArena := .source ⟨prefixArena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source prefixArena ⟨prefixRecord⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize prefixSignature (fun _ C z =>
    @nativePrefix C.S C.H C.T C.headEq C.symbolEq C.B C.A z.1 z.2.1 z.2.2)
    (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none,
  escapeFrom := none, sourceSelection := none,
  continuation := .unknown, familyRecord := none,
  options := #[{ name := `relaxedAutoImplicit, value := .bool false }] }

structure InitFamily extends Family where
  finiteS : Fintype S
  measurableS : MeasurableSpace S
  singletonS : @MeasurableSingletonClass S measurableS
  P : @InitProtocol S H T headEq symbolEq B A

abbrev initSignature : Signature where
  Params := InitFamily
  State C := (C.S ⊕ @Ready C.S C.H C.T C.headEq C.symbolEq C.B C.A) ×
    (@Ready C.S C.H C.T C.headEq C.symbolEq C.B C.A)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ≥0∞
  Anchor := Empty
  finiteAnchor := inferInstance

def initActual : Realization initSignature :=
  realize initSignature (fun _ C z => @eta C.S C.H C.T C.headEq C.symbolEq C.B C.A z.1 z.2)
    (fun e => nomatch e)
def initBad : Realization initSignature :=
  realize initSignature (fun _ _ _ => 0) (fun e => nomatch e)

def initArena : Arena where
  signature := initSignature
  Law Q := ∀ {S H T : Type} [DecidableEq H] [DecidableEq T] {B : ℕ}
    [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]
    (A : Architecture S H T B) (P : InitProtocol A)
    (hReturn : ∀ a ∈ P.entrances, tapeLaw (nativeNever A a) = 0),
    (∀ a n x, nativeFirstReturn A a n x = hit (initInstruction A) a n x) ∧
    (∀ a x, nativeExits A a x = exits (initInstruction A) a x) ∧
    (∀ a, nativeNever A a = never (initInstruction A) a) ∧
    (∀ a ∈ P.entrances, ∀ ω n x, ω ∈ nativeFirstReturn A a n x →
      P.actualFields x.val = initial.source.finiteFields) ∧
    ∃ d : ℕ, 0 < d ∧ d ≤ 4 ^ (2 ^ B) ∧
      (∀ a ∈ P.entrances, ∀ x,
        Clears d (Q.readout ()
          ⟨⟨S,H,T,inferInstance,inferInstance,B,A⟩,inferInstance,inferInstance,inferInstance,P⟩
          (a,x)).toReal) ∧
      (∀ a ∈ P.entrances, ∑ x, Q.readout ()
        ⟨⟨S,H,T,inferInstance,inferInstance,B,A⟩,inferInstance,inferInstance,inferInstance,P⟩
        (a,x) = 1)

def immediateProtocol : InitProtocol unitArchitecture where
  entrances := {.inr ⟨(), trivial⟩}
  running_frame := by intro s hs; cases hs
  immediate_frame := by intros; rfl
  actualFields := fun _ => initial.source.finiteFields
  immediate_initial := by intros; rfl
  outer_initial := by intros; rfl

private theorem init_bad_invalid : ¬ initArena.Law initBad := by
  intro h
  have hn : ∀ a ∈ immediateProtocol.entrances, tapeLaw (nativeNever unitArchitecture a) = 0 := by
    intro a ha
    have he : a = .inr ⟨(), trivial⟩ := ha
    subst a
    have hz : nativeNever unitArchitecture (.inr ⟨(), trivial⟩) = ∅ := by
      ext ω
      simp only [nativeNever, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      intro hh
      obtain ⟨s, hs⟩ := hh 0
      cases hs
    rw [hz, measure_empty]
  obtain ⟨d,hd,hB,hc,hnorm⟩ := (h unitArchitecture immediateProtocol hn).2.2.2.2
  have hh := hnorm (.inr ⟨(), trivial⟩) (Set.mem_singleton _)
  simpa [initBad,realize] using hh

def initRecord : Registration initArena
    (type_of% (@original_initialization_exit_certificate)) where
  actual := initActual
  bridge := Iff.rfl
  variation := ⟨original_initialization_exit_certificate, initBad, init_bad_invalid⟩
  sensitivity := by
    letI : Subsingleton initArena.signature.Role := by change Subsingleton Unit; infer_instance
    constructor
    · intro i
      refine ⟨initBad, ?_, rfl, init_bad_invalid⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro i; exact nomatch i
  dependence := by
    intro i
    let C : InitFamily := ⟨⟨Unit,Unit,Unit,inferInstance,inferInstance,1,unitArchitecture⟩,
      inferInstance,inferInstance,inferInstance,immediateProtocol⟩
    refine ⟨C, (.inr ⟨(),trivial⟩,⟨(),trivial⟩), (.inl (),⟨(),trivial⟩), ?_⟩
    -- This carrier's enabled loop never returns, whereas its genuine immediate
    -- entrance returns the complete current snapshot at time zero.
    intro he
    have hz : nativeExits unitArchitecture (.inl ()) ⟨(),trivial⟩ = ∅ := by
      ext ω
      simp only [nativeExits, Set.mem_iUnion, nativeFirstReturn, Set.mem_ofPred_eq,
        Set.mem_empty_iff_false, iff_false]
      rintro ⟨n, hn, _⟩
      have hl : ∀ n, nativeUntil unitArchitecture (.inl ()) ω n = .inl () := by
        intro n
        induction n with
        | zero => rfl
        | succ n ih => simpa [nativeUntil, nativeTick, tickReturn, currentReturn,
            unitArchitecture] using ih
      rw [hl n] at hn
      cases hn
    have hone : nativeExits unitArchitecture (.inr ⟨(),trivial⟩) ⟨(),trivial⟩ = univ := by
      ext ω
      simp only [nativeExits, Set.mem_iUnion, Set.mem_univ, iff_true]
      exact ⟨0,rfl,fun k hk => (Nat.not_lt_zero k hk).elim⟩
    change tapeLaw (nativeExits unitArchitecture (.inr ⟨(),trivial⟩) ⟨(),trivial⟩) =
      tapeLaw (nativeExits unitArchitecture (.inl ()) ⟨(),trivial⟩) at he
    rw [hz,hone,measure_empty,measure_univ] at he
    exact one_ne_zero he

def initRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@original_initialization_exit_certificate)
    (type_of% (realize initSignature (fun _ C z =>
      @eta C.S C.H C.T C.headEq C.symbolEq C.B C.A z.1 z.2) (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.OriginalNativeServiceBridge.original_initialization_exit_certificate.__information_unit,
  realizationName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.OriginalNativeServiceBridge.InitializationAudit.initRecord,
  realizationSource := none, generated := false,
  arena := .source ⟨initArena⟩, objectArena := .source ⟨initArena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source initArena ⟨initRecord⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize initSignature (fun _ C z =>
    @eta C.S C.H C.T C.headEq C.symbolEq C.B C.A z.1 z.2) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none,
  escapeFrom := none, sourceSelection := none,
  continuation := .unknown, familyRecord := none,
  options := #[{ name := `relaxedAutoImplicit, value := .bool false }] }
#print axioms prefixRecord
#print axioms initRecord
end InitializationAudit


namespace ReadAudit
open InitializationAudit
open _root_.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.OriginalNativeServiceBridge.Initialization
open _root_.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FiniteFairBitFirstReturn
open _root_.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FiniteFairBitExitLaws
open _root_.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FiniteFairBitDenominator

structure ReadFamily extends Family where
  finiteS : Fintype S
  measurableS : MeasurableSpace S
  singletonS : @MeasurableSingletonClass S measurableS
  P : @ReadUpdate.Protocol S H T headEq symbolEq B A

abbrev signature : Signature where
  Params := ReadFamily
  State C := Letter × @Ready C.S C.H C.T C.headEq C.symbolEq C.B C.A ×
    @Ready C.S C.H C.T C.headEq C.symbolEq C.B C.A
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ≥0∞
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ C z => @ReadUpdate.row C.S C.H C.T
    C.headEq C.symbolEq C.B C.A C.P z.1 z.2.1 z.2.2) (fun e => nomatch e)
def bad : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law Q := ∀ {S Head Symbol : Type} [DecidableEq Head] [DecidableEq Symbol] {B : ℕ}
    [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]
    (A : Architecture S Head Symbol B)
    (P : ReadUpdate.Protocol A)
    (hReturn : ∀ x a, a ∈ ReadUpdate.entrances A P x →
      tapeLaw (nativeNever A a) = 0),
    (∀ a n y, nativeFirstReturn A a n y = hit (initInstruction A) a n y) ∧
    (∀ a y, nativeExits A a y = exits (initInstruction A) a y) ∧
    (∀ a, nativeNever A a = never (initInstruction A) a) ∧
    (∀ x z a, P.arrival z x = some a → ∀ ω n y,
      ω ∈ nativeFirstReturn A a n y →
      finiteRead (P.fields z.val) x = some (P.fields y.val) ∧
      OriginalEvent.acquired x :: ReadUpdate.nativeEvents A P a ω n =
        eventBlock (P.fields z.val) (.read x)) ∧
    (∀ x z a, P.arrival z x = some a → ∀ y,
      finiteRead (P.fields z.val) x ≠ some (P.fields y.val) → eta A a y = 0) ∧
    (∀ x, ∃ d : ℕ, 0 < d ∧ d ≤ 4 ^ (2 ^ B) ∧
      (∀ z y, Clears d (Q.readout ()
        ⟨⟨S,Head,Symbol,inferInstance,inferInstance,B,A⟩,inferInstance,inferInstance,inferInstance,P⟩ (x,z,y)).toReal) ∧
      (∀ z, ∑ y, Q.readout ()
        ⟨⟨S,Head,Symbol,inferInstance,inferInstance,B,A⟩,inferInstance,inferInstance,inferInstance,P⟩ (x,z,y) = 1)) ∧
    (∀ x z, (ReadUpdate.actual A P x z).isSome ↔
      (finiteRead (P.fields z.val) x).isSome) ∧
    (∀ x z, finiteRead (P.fields z.val) x = none →
      P.arrival z x = none ∧ ReadUpdate.actual A P x z = none ∧
      ∀ y, Q.readout ()
        ⟨⟨S,Head,Symbol,inferInstance,inferInstance,B,A⟩,inferInstance,inferInstance,inferInstance,P⟩ (x,z,y) = if y = z then 1 else 0)

def pending : FiniteFields :=
  { initial.source.finiteFields with control := .fourth (.pending 0) }

def terminalProtocol {S H T : Type} [DecidableEq H] [DecidableEq T] {B : ℕ}
    (A : Architecture S H T B) : ReadUpdate.Protocol A where
  fields := fun _ => pending
  inputSite := fun _ => False
  offered := fun _ => none
  arrival := fun _ _ => none
  menu := by intro z x; simp [pending,finiteRead]
  boundary := by intro z x a h; cases h
  decodeSymbol := fun _ _ => none
  Tracks := fun _ _ _ _ => False
  start := by intro z x a h; cases h
  step := by intro f x todo s b h; cases h

private theorem bad_invalid : ¬ arena.Law bad := by
  intro h
  have hn : ∀ x a, a ∈ ReadUpdate.entrances unitArchitecture
      (terminalProtocol unitArchitecture) x → tapeLaw (nativeNever unitArchitecture a) = 0 := by
    intro x a ha
    obtain ⟨z,hz⟩ := ha
    cases hz
  obtain ⟨d,hd,hbound,hclear,hnorm⟩ :=
    (h unitArchitecture (terminalProtocol unitArchitecture) hn).2.2.2.2.2.1 0
  have hh := hnorm ⟨(),trivial⟩
  simpa [bad,realize] using hh

/-- Two full terminal snapshots differ in an actually paid private phase. -/
def phaseArchitecture : Architecture Bool Unit Unit 2 where
  headFinite := inferInstance
  symbolFinite := inferInstance
  paid := {
    resident := [false]
    residentSite := ⟨fun _ => 0,by
      intro i j h; apply Fin.ext
      have hi := i.isLt; have hj := j.isLt
      simp only [List.length_cons,List.length_nil] at hi hj
      omega⟩
    complete := ⟨fun s i => if i = 0 then false else s,by
      intro s t h; have hh := congrFun h (1 : Fin 2); simpa using hh⟩
    resident_exact := by
      intro s i; have hi : i = 0 := Fin.ext (by
        change i.val = 0
        have h := i.isLt; simp only [List.length_cons,List.length_nil] at h; omega)
      subst i; rfl
    runtimePeak := 1
    installationTotalPeak := 2
    online_bound := by decide
    installation_bound := by decide }
  memoryCell := fun _ => True
  head := fun _ _ => 0
  head_owned := by intros; trivial
  buffer := fun _ => none
  pc := fun _ => 0
  branchBit := fun _ => 0
  branchZero := fun _ => 0
  branchOne := fun _ => 0
  randomCell := fun _ => none
  readLatch := fun _ => 0
  initFrame := fun _ => none
  ready := fun _ => True
  action := fun _ => .booleanBranch
  enabled := fun _ => True
  nativeEdge := fun s _ r => r = (s,⟨none,none,none⟩)
  result := fun s _ => (s,⟨none,none,none⟩)
  result_iff := by intros; simp
  deterministic := by intros; rfl
  local_effect := by intro s b h; dsimp; simp

def record : Registration arena (type_of% (@original_read_update_rows)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨original_read_update_rows,bad,bad_invalid⟩
  sensitivity := by
    letI : Subsingleton arena.signature.Role := by change Subsingleton Unit; infer_instance
    constructor
    · intro i
      refine ⟨bad,?_,rfl,bad_invalid⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro i; exact nomatch i
  dependence := by
    intro i
    let C : ReadFamily := ⟨⟨Bool,Unit,Unit,inferInstance,inferInstance,2,phaseArchitecture⟩,
      inferInstance,inferInstance,inferInstance,terminalProtocol phaseArchitecture⟩
    refine ⟨C,(0,⟨false,trivial⟩,⟨false,trivial⟩),
      (0,⟨false,trivial⟩,⟨true,trivial⟩),?_⟩
    have hne : (⟨true,trivial⟩ : Ready phaseArchitecture) ≠ ⟨false,trivial⟩ := by
      intro h; have hh := congrArg Subtype.val h; cases hh
    simp [actual,realize,C,ReadUpdate.row,ReadUpdate.actual,terminalProtocol,hne]
    exact (one_ne_zero : (1 : ℝ≥0∞) ≠ 0)

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@original_read_update_rows)
    (type_of% (realize signature (fun _ C z => @ReadUpdate.row C.S C.H C.T
      C.headEq C.symbolEq C.B C.A C.P z.1 z.2.1 z.2.2) (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.OriginalNativeServiceBridge.original_read_update_rows.__information_unit,
  realizationName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.OriginalNativeServiceBridge.ReadAudit.record,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨record⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature (fun _ C z => @ReadUpdate.row C.S C.H C.T
    C.headEq C.symbolEq C.B C.A C.P z.1 z.2.1 z.2.2) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none,
  escapeFrom := none, sourceSelection := none,
  continuation := .unknown, familyRecord := none,
  options := #[{ name := `relaxedAutoImplicit, value := .bool false }] }
#print axioms record
end ReadAudit

end Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.OriginalNativeServiceBridge
