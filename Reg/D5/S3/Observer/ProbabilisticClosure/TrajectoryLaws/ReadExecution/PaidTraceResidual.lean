import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.ReadExecution.PaidTraceResidual
import Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.OriginalNativeServiceBridge
import Reg.Support.DependentFamily
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Classical MeasureTheory Set
open scoped ENNReal BigOperators
local instance {O : Type} : MeasurableSpace (Option O) := ⊤
local instance {O : Type} : MeasurableSingletonClass (Option O) := ⟨fun _ => trivial⟩
namespace Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.ReadExecution.PaidTraceResidual
open _root_.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws
open OriginalNativeServiceBridge OriginalNativeServiceBridge.Initialization
open ReadExecution.PaidTraceResidual
open FiniteFairBitFirstReturn FiniteFairBitExitLaws
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.OriginalNativeServiceBridge.InitializationAudit

structure Family where
  S : Type
  H : Type
  T : Type
  headEq : DecidableEq H
  symbolEq : DecidableEq T
  B : ℕ
  A : @Architecture S H T headEq symbolEq B
  C : @ReturnCut S H T headEq symbolEq B A
abbrev signature : Signature where
  Params := Family
  State F := (F.S ⊕ @Ready F.S F.H F.T F.headEq F.symbolEq F.B F.A) × (ℕ → Bool) × ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ F := (F.S ⊕ @Ready F.S F.H F.T F.headEq F.symbolEq F.B F.A) × List (Receipt F.S F.T)
  Anchor := Empty
  finiteAnchor := inferInstance
def actual : Realization signature :=
  realize signature (fun _ F p => @sourceTrace F.S F.H F.T F.headEq F.symbolEq F.B F.A F.C p.1 p.2.1 p.2.2)
    (fun e => nomatch e)
def bad : Realization signature :=
  realize signature (fun _ F p => ((@sourceTrace F.S F.H F.T F.headEq F.symbolEq F.B F.A F.C p.1 p.2.1 p.2.2).1,[]))
    (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law Q := ∀ {S H T : Type} [DecidableEq H] [DecidableEq T] {B : ℕ}
    [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]
    (A : Architecture S H T B) (C : ReturnCut A),
    (∀ s p y, Complete A C s p y ↔
      ∃ ω n, Q.readout () ⟨S,H,T,inferInstance,inferInstance,B,A,C⟩ (.inl s,ω,n) = (.inr y,p)) ∧
    (∀ a ω n, (Q.readout () ⟨S,H,T,inferInstance,inferInstance,B,A,C⟩ (a,ω,n)).1 = path (instruction A C) a ω n) ∧
    (∀ a ω n, 0 < tapeLaw {σ | Q.readout () ⟨S,H,T,inferInstance,inferInstance,B,A,C⟩ (a,σ,n) =
      Q.readout () ⟨S,H,T,inferInstance,inferInstance,B,A,C⟩ (a,ω,n)}) ∧
    (∀ a ω n, (Q.readout () ⟨S,H,T,inferInstance,inferInstance,B,A,savedCut A⟩ (a,ω,n)).1 = nativeUntil A a ω n) ∧
    (∀ a, tapeLaw (never (instruction A C) a) = 0 →
      Measurable (FiniteFairBitReturnRestart.restart (instruction A C) a) ∧
      tapeLaw.map (FiniteFairBitReturnRestart.restart (instruction A C) a) =
        (tapeLaw.map (fun ω => (FiniteFairBitReturnRestart.restart (instruction A C) a ω).1)).prod tapeLaw)

def unitCut : ReturnCut unitArchitecture where
  observe := fun _ _ => some ⟨(),trivial⟩
  state := by intros; exact Subsingleton.elim _ _
private theorem bad_invalid : ¬ arena.Law bad := by
  intro h
  let r : Unit × PrimitiveReceipt Unit := ((),⟨none,none,none⟩)
  have hc : Complete unitArchitecture unitCut () [((),r)] ⟨(),trivial⟩ :=
    Complete.exit ⟨⟨false,by simp [unitArchitecture,r]⟩,rfl⟩
  obtain ⟨ω,n,hn⟩ := ((h unitArchitecture unitCut).1 () [((),r)] ⟨(),trivial⟩).mp hc
  have hh := congrArg Prod.snd hn
  simp [bad,realize] at hh

def record : Registration arena (type_of% (@paid_receipt_execution)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨paid_receipt_execution,bad,bad_invalid⟩
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
    let F : Family := ⟨Unit,Unit,Unit,inferInstance,inferInstance,1,unitArchitecture,unitCut⟩
    refine ⟨F,(.inl (),fun _ => false,0),(.inl (),fun _ => false,1),?_⟩
    intro h
    have hh := congrArg Prod.snd h
    simp [actual,realize,F,sourceTrace,nativeTick,unitArchitecture,tickTarget,target,unitCut] at hh

def receiptRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@paid_receipt_execution)
    (type_of% (realize signature (fun _ F p =>
      @sourceTrace F.S F.H F.T F.headEq F.symbolEq F.B F.A F.C p.1 p.2.1 p.2.2)
      (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.ReadExecution.PaidTraceResidual.paid_receipt_execution.__information_unit,
  realizationName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.ReadExecution.PaidTraceResidual.record,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨record⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature (fun _ F p =>
    @sourceTrace F.S F.H F.T F.headEq F.symbolEq F.B F.A F.C p.1 p.2.1 p.2.2)
    (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none,
  escapeFrom := none, sourceSelection := none, continuation := .unknown, familyRecord := none,
  options := #[{ name := `relaxedAutoImplicit, value := .bool false }] }
namespace ResidualAudit
open NativeAcquiredPrefixState NativeFullResidual FourthSegmentStoppedLaw

/-- A two-send model for audit variation, not a class-wide source interpreter. -/
def A : Architecture (Fin 3) Unit Bool 2 where
  headFinite := inferInstance
  symbolFinite := inferInstance
  paid := {
    resident := []
    residentSite := ⟨Fin.elim0,by intro i; exact Fin.elim0 i⟩
    complete := ⟨fun s i => s.val.testBit i.val,by decide⟩
    resident_exact := by intro s i; exact Fin.elim0 i
    runtimePeak := 2
    installationTotalPeak := 2
    online_bound := by decide
    installation_bound := by decide }
  memoryCell := fun _ => True
  head := fun _ _ => 0
  head_owned := by intros; trivial
  buffer := fun s => some (s ≠ 0)
  pc := fun _ => 0
  branchBit := fun _ => 0
  branchZero := fun _ => 0
  branchOne := fun _ => 0
  randomCell := fun _ => none
  readLatch := fun _ => 0
  initFrame := fun _ => none
  ready := fun _ => True
  action := fun _ => .sendBuffer
  enabled := fun s => s ≠ 2
  nativeEdge := fun s _ r => s ≠ 2 ∧
    r = (if s = 0 then 1 else 2,⟨none,none,some (s ≠ 0)⟩)
  result := fun s _ => (if s = 0 then 1 else 2,⟨none,none,some (s ≠ 0)⟩)
  result_iff := by intros; rfl
  deterministic := by intros; rfl
  local_effect := by intro s b h; simp

def C : ReturnCut A where
  observe := fun s r => if s = 1 then some ⟨r.1,trivial⟩ else none
  state := by
    intro s r y h
    split_ifs at h
    · exact congrArg Subtype.val (Option.some.inj h).symm
abbrev f : FiniteFields := initial.source.finiteFields
def fields (s : Fin 3) : FiniteFields :=
  if s = 2 then { f with control := .seed (some 0) } else f
def decode (_ : Fin 3) (b : Bool) : Option OriginalEvent :=
  some (if b then .held f.registers else .moved (.seed (some 0)))
def arrival (z : Ready A) (x : Letter) : Option (Fin 3 ⊕ Ready A) :=
  if z.val = 0 ∧ x = 0 then some (.inl 0) else none
private theorem after_two (ω : ℕ → Bool) (n : ℕ) :
    sourceTrace A C (.inl 0) ω (n+2) =
      (.inr ⟨2,trivial⟩,[(0,(1,⟨none,none,some false⟩)),(1,(2,⟨none,none,some true⟩))]) := by
  cases n <;> simp [sourceTrace,nativeTick,A,C,tickTarget,target]

private theorem returns : ∀ z x a, arrival z x = some a →
    tapeLaw (never (instruction A C) a) = 0 := by
  intro z x a ha
  simp only [arrival] at ha
  split_ifs at ha with h
  · have he : a = .inl 0 := (Option.some.inj ha).symm
    subst a
    have hz : never (instruction A C) (.inl 0) = ∅ := by
      ext ω
      simp only [never,mem_iInter,mem_empty_iff_false,iff_false]
      intro h
      obtain ⟨s,hs⟩ := h 2
      have hh := (paid_receipt_execution A C).2.1 (.inl 0) ω 2
      rw [after_two ω 0] at hh
      change path (instruction A C) (.inl 0) ω 2 = .inl s at hs
      rw [← hh] at hs
      cases hs
    rw [hz,measure_empty]

private theorem correct : ∀ z x a, arrival z x = some a →
    ∀ᵐ ω ∂tapeLaw, ∀ n, Correct A fields decode (fields z.val) x (sourceTrace A C a ω n) := by
  intro z x a ha
  simp only [arrival] at ha
  split_ifs at ha with h
  · have he : a = .inl 0 := (Option.some.inj ha).symm
    subst a
    filter_upwards [] with ω
    intro n y hy
    obtain ⟨hz,hx⟩ := h
    cases n with
    | zero => cases hy
    | succ n =>
      cases n with
      | zero => simp [sourceTrace,nativeTick,A,C,tickTarget,target] at hy
      | succ n =>
        have hh := after_two ω n
        rw [hh] at hy
        have hyy : y = ⟨2,trivial⟩ := (Sum.inr.inj hy).symm
        subst y
        rw [hh]
        simp [fields,hz,hx,f,Correct,finiteRead,ReadUpdate.body,eventBlock,events,decode,initial]

structure ReadFamily extends Family where
  fields : S → FiniteFields
  decode : S → T → Option OriginalEvent
  arrival : @Ready S H T headEq symbolEq B A → Letter → Option (S ⊕ @Ready S H T headEq symbolEq B A)
abbrev readSignature : Signature where
  Params := ReadFamily
  State F := (F.S ⊕ @Ready F.S F.H F.T F.headEq F.symbolEq F.B F.A) × (ℕ → Bool) × ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ F := (F.S ⊕ @Ready F.S F.H F.T F.headEq F.symbolEq F.B F.A) × List (Receipt F.S F.T)
  Anchor := Empty
  finiteAnchor := inferInstance
def readActual : Realization readSignature :=
  realize readSignature (fun _ F p => @sourceTrace F.S F.H F.T F.headEq F.symbolEq F.B F.A F.C p.1 p.2.1 p.2.2)
    (fun e => nomatch e)
def readBad : Realization readSignature :=
  realize readSignature (fun _ F p => ((@sourceTrace F.S F.H F.T F.headEq F.symbolEq F.B F.A F.C p.1 p.2.1 p.2.2).1,[]))
    (fun e => nomatch e)
def readArena : Arena where
  signature := readSignature
  Law Q := ∀ {S H T : Type} [DecidableEq H] [DecidableEq T] {B : ℕ}
    [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]
    (A : Architecture S H T B) (C : ReturnCut A)
    (fields : S → FiniteFields) (decode : S → T → Option OriginalEvent)
    (arrival : Ready A → Letter → Option (S ⊕ Ready A))
    (hReturn : ∀ z x a, arrival z x = some a → tapeLaw (never (instruction A C) a) = 0)
    (hCorrect : ∀ z x a, arrival z x = some a →
      ∀ᵐ ω ∂tapeLaw, ∀ n, Correct A fields decode (fields z.val) x (sourceTrace A C a ω n)),
    (∀ z x a, arrival z x = some a → ∀ ω n,
      Correct A fields decode (fields z.val) x
        (Q.readout () ⟨⟨S,H,T,inferInstance,inferInstance,B,A,C⟩,fields,decode,arrival⟩ (a,ω,n))) ∧
    (∀ z x a, arrival z x = some a → match a with
      | .inl s => Tracks A C fields decode arrival (fields z.val) x (ReadUpdate.body (fields z.val) x) s
      | .inr y => finiteRead (fields z.val) x = some (fields y.val) ∧ ReadUpdate.body (fields z.val) x = []) ∧
    (∀ f x todo s b, Tracks A C fields decode arrival f x todo s → A.enabled s →
      match C s (A.result s b) with
      | some y => finiteRead f x = some (fields y.val) ∧ todo = ReadUpdate.committed decode s (A.result s b)
      | none => ∃ rest, todo = ReadUpdate.committed decode s (A.result s b) ++ rest ∧
          Tracks A C fields decode arrival f x rest (A.result s b).1)
private theorem read_bad_invalid : ¬ readArena.Law readBad := by
  intro h
  have hh := (h A C fields decode arrival returns correct).1 ⟨0,trivial⟩ 0 (.inl 0)
    (by simp [arrival]) (fun _ => false) 2 ⟨2,trivial⟩
  have ht := after_two (fun _ => false) 0
  simp only [readBad,realize,ht] at hh
  have hf := (hh trivial).2
  simp [events,ReadUpdate.body,eventBlock,fields,f,initial] at hf

def readRecord : Registration readArena (type_of% (@paid_read_residual)) where
  actual := readActual
  bridge := Iff.rfl
  variation := ⟨paid_read_residual,readBad,read_bad_invalid⟩
  sensitivity := by
    letI : Subsingleton readArena.signature.Role := by change Subsingleton Unit; infer_instance
    constructor
    · intro i
      refine ⟨readBad,?_,rfl,read_bad_invalid⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro i; exact nomatch i
  dependence := by
    intro i
    let F : ReadFamily := ⟨⟨Fin 3,Unit,Bool,inferInstance,inferInstance,2,A,C⟩,fields,decode,arrival⟩
    refine ⟨F,(.inl 0,fun _ => false,0),(.inl 0,fun _ => false,2),?_⟩
    intro h
    have hh := congrArg Prod.snd h
    change (sourceTrace A C (.inl 0) (fun _ => false) 0).2 =
      (sourceTrace A C (.inl 0) (fun _ => false) 2).2 at hh
    rw [after_two (fun _ => false) 0] at hh
    simp [sourceTrace] at hh

def residualRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@paid_read_residual)
    (type_of% (realize readSignature (fun _ F p =>
      @sourceTrace F.S F.H F.T F.headEq F.symbolEq F.B F.A F.C p.1 p.2.1 p.2.2)
      (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.ReadExecution.PaidTraceResidual.paid_read_residual.__information_unit,
  realizationName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.ReadExecution.PaidTraceResidual.ResidualAudit.readRecord,
  realizationSource := none, generated := false,
  arena := .source ⟨readArena⟩, objectArena := .source ⟨readArena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source readArena ⟨readRecord⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize readSignature (fun _ F p =>
    @sourceTrace F.S F.H F.T F.headEq F.symbolEq F.B F.A F.C p.1 p.2.1 p.2.2)
    (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none,
  escapeFrom := none, sourceSelection := none, continuation := .unknown, familyRecord := none,
  options := #[{ name := `relaxedAutoImplicit, value := .bool false }] }
#print axioms readRecord
end ResidualAudit
#print axioms record
end Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.ReadExecution.PaidTraceResidual
