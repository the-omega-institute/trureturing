import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FiniteFairBitFirstReturn
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Classical MeasureTheory ProbabilityTheory Set Finset
open scoped ENNReal BigOperators
namespace Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FiniteFairBitFirstReturn
open _root_.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FiniteFairBitFirstReturn
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

structure PrefixFamily where
  S : Type
  decode : S → Instruction S
  initial : S

abbrev prefixSignature : Signature where
  Params := PrefixFamily
  State _ := ℕ → Bool
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ C := ℕ → C.S
  Anchor := Empty
  finiteAnchor := inferInstance

def prefixActual : Realization prefixSignature :=
  realize prefixSignature (fun _ C ω => run C.decode C.initial ω) (fun e => nomatch e)
def prefixRejected : Realization prefixSignature :=
  realize prefixSignature (fun _ C _ _ => C.initial) (fun e => nomatch e)
def prefixArena : Arena where
  signature := prefixSignature
  Law R := ∀ {S : Type} [Countable S] [MeasurableSpace S] [MeasurableSingletonClass S]
    (decode : S → Instruction S) (s : S) (n : ℕ) (w : Fin (n+1) → S),
    (tapeLaw.map (fun ω i => R.readout () ⟨S,decode,s⟩ ω (i : Fin (n+1)))) {w} =
      ((instructionLaw decode s).map (fun x i => x (i : Fin (n+1)))) {w}

private theorem prefix_rejected : ¬ prefixArena.Law prefixRejected := by
  intro h
  let d : Bool → Instruction Bool := fun _ => .fair false true
  let w : Fin 2 → Bool := ![false,true]
  have hf : (fun (_ : ℕ → Bool) (_ : Fin 2) => false) ⁻¹' {w} = ∅ := by
    ext ω
    simp only [Set.mem_preimage,Set.mem_singleton_iff,Set.mem_empty_iff_false,iff_false]
    intro he
    have := congrFun he 1
    simp [w] at this
  have hh := h d false 1 w
  change (tapeLaw.map (fun (_ : ℕ → Bool) (_ : Fin 2) => false)) {w} = _ at hh
  rw [Measure.map_apply (by fun_prop) (measurableSet_singleton _),hf,measure_empty] at hh
  rw [instructionLaw,
    _root_.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.MarkovPrefixMass.markov_chain_law_map_prefix_apply_singleton] at hh
  norm_num [instructionKernel,Kernel.ofFunOfCountable,row,d,w,PMF.toMeasure_apply_singleton,
    PMF.map_apply,tsum_fintype,Fintype.sum_bool,fairBit,PMF.bernoulli_apply] at hh
  exact (ENNReal.inv_ne_zero.mpr (by simp)) hh.symm

def prefixRecord : Registration prefixArena (type_of% (@execution_prefix_law)) where
  actual := prefixActual
  bridge := Iff.rfl
  variation := ⟨execution_prefix_law,prefixRejected,prefix_rejected⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨prefixRejected,?_,rfl,prefix_rejected⟩
      intro j hj
      exact (hj (@Subsingleton.elim Unit _ j i)).elim
    · intro i; exact nomatch i
  dependence := by
    intro i
    cases i
    refine ⟨⟨Bool,fun _ => .fair false true,false⟩, (fun _ => false),(fun _ => true),?_⟩
    intro he
    have h1 := congrFun he 1
    simp [prefixActual,realize,run,successor] at h1

structure InvocationFamily where
  p : ℕ
  m : ℕ
  a : ℕ
  program : Program p a
  initial : Snapshot p m a
  mode : ServiceMode
  input : Option _root_.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FourthSegmentStoppedLaw.Letter
  bound : ℕ

abbrev invocationSignature : Signature where
  Params := InvocationFamily
  State _ := ℕ → Bool
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ C := Option (Snapshot C.p C.m C.a)
  Anchor := Empty
  finiteAnchor := inferInstance

def invocationActual : Realization invocationSignature :=
  realize invocationSignature (fun _ C ω =>
    executeUntil C.program (launch C.program C.initial C.mode C.input) ω C.bound)
    (fun e => nomatch e)
def invocationRejected : Realization invocationSignature :=
  realize invocationSignature (fun _ _ _ => none) (fun e => nomatch e)
def invocationArena : Arena where
  signature := invocationSignature
  Law R := ∀ {p m a : ℕ} (P : Program p a) (s : Snapshot p m a) (mode : ServiceMode)
    (input : Option _root_.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FourthSegmentStoppedLaw.Letter)
    (ω : ℕ → Bool) (n : ℕ) (t : Snapshot p m a),
    R.readout () ⟨p,m,a,P,s,mode,input,n⟩ ω = some t ↔
      ∃ k ≤ n, firstReturnAt P (launch P s mode input) ω k ∧
        (trace P (launch P s mode input) ω k).1.snapshot = t

private def idle : Snapshot 2 0 0 :=
  ⟨fun _ => false,0,0,.alpha,none,none⟩
private def immediate : Program 2 0 := ⟨fun _ => .finish,fun _ => none⟩
private def storing : Program 2 0 :=
  ⟨fun pc => if pc=0 then .fairStore 1 else .finish,fun _ => some 0⟩

private theorem invocation_rejected : ¬ invocationArena.Law invocationRejected := by
  intro h
  have hh := (h immediate idle .alpha none (fun _ => false) 0 idle).mpr
    ⟨0,le_rfl,by simp [firstReturnAt,trace,launch,immediate],
      by simp [trace,launch,immediate,idle]⟩
  cases hh

def invocationRecord : Registration invocationArena (type_of% (@invocation_return_iff)) where
  actual := invocationActual
  bridge := Iff.rfl
  variation := ⟨invocation_return_iff,invocationRejected,invocation_rejected⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨invocationRejected,?_,rfl,invocation_rejected⟩
      intro j hj
      exact (hj (@Subsingleton.elim Unit _ j i)).elim
    · intro i; exact nomatch i
  dependence := by
    intro i
    cases i
    refine ⟨⟨2,0,0,storing,idle,.alpha,none,2⟩,(fun _ => false),(fun _ => true),?_⟩
    intro he
    have hh := congrArg (fun z => z.map (fun s => s.tape 0)) he
    norm_num [invocationActual,realize,executeUntil,launch,storing,idle,asks,act,
      Function.update] at hh


structure SuffixFamily where
  p : ℕ
  m : ℕ
  a : ℕ
  program : Program p a
  initial : Snapshot p m a
  bound : ℕ

abbrev suffixSignature : Signature where
  Params := SuffixFamily
  State _ := ℕ → Bool
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ → Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def suffixActual : Realization suffixSignature :=
  realize suffixSignature (fun _ C ω => unused (decoded C.program) C.initial ω C.bound)
    (fun e => nomatch e)
def suffixRejected : Realization suffixSignature :=
  realize suffixSignature (fun _ _ _ _ => false) (fun e => nomatch e)
def suffixArena : Arena where
  signature := suffixSignature
  Law R := ∀ {p m a B : ℕ} (P : Program p a)
    (entrances : Set (Snapshot p m a))
    (c : CompleteCodec P {t | Reachable P entrances t} B)
    (ready : Set {t | Reachable P entrances t})
    [MeasurableSpace (Snapshot p m a)] [MeasurableSingletonClass (Snapshot p m a)]
    (s : Snapshot p m a) (hs : Reachable P entrances s)
    (n : ℕ) (w : Fin (n+1) → Snapshot p m a),
    Nat.card {t | Reachable P entrances t} ≤ 2^B ∧ Nat.card ready ≤ 2^B ∧
    (∀ ω : ℕ → Bool, Reachable P entrances (physicalRun P s ω n)) ∧
    (∀ (z : Snapshot p m a) (b : Bool), asks (P.code z.pc) = false →
      act P z b = act P z false) ∧
    (∀ (ω : ℕ → Bool) (k : ℕ), R.readout () ⟨p,m,a,P,s,n⟩ ω k =
      ω (k + requests (decoded P) s ω n)) ∧
    (tapeLaw.map (fun ω i => physicalRun P s ω (i : Fin (n+1)))) {w} =
      ((instructionLaw (decoded P) s).map (fun x i => x (i : Fin (n+1)))) {w}

private def finishing : Program 2 0 := ⟨fun _ => .finish,fun _ => some 0⟩
private theorem finishing_reachable (t : Snapshot 2 0 0)
    (h : Reachable finishing {idle} t) : t = idle := by
  induction h with
  | entrance h => exact h
  | step h b ih => simpa [act,finishing] using ih

private def singletonCodec : CompleteCodec finishing {t | Reachable finishing {idle} t} 1024 where
  encode _ _ := false
  decode _ := some (finishing,idle)
  roundtrip s := by rw [finishing_reachable s.val s.property]

private theorem suffix_rejected : ¬ suffixArena.Law suffixRejected := by
  letI : MeasurableSpace (Snapshot 2 0 0) := ⊤
  letI : MeasurableSingletonClass (Snapshot 2 0 0) := ⟨fun _ => trivial⟩
  intro h
  have hh := h finishing {idle} singletonCodec ∅ idle (Reachable.entrance rfl) 0
    (fun _ => idle)
  have hs := hh.2.2.2.2.1 (fun _ => true) 0
  change false = true at hs
  cases hs

def suffixRecord : Registration suffixArena (type_of% (@charged_execution_prefix)) where
  actual := suffixActual
  bridge := Iff.rfl
  variation := ⟨charged_execution_prefix,suffixRejected,suffix_rejected⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨suffixRejected,?_,rfl,suffix_rejected⟩
      intro j hj
      exact (hj (@Subsingleton.elim Unit _ j i)).elim
    · intro i; exact nomatch i
  dependence := by
    intro i
    cases i
    refine ⟨⟨2,0,0,finishing,idle,0⟩,(fun _ => false),(fun _ => true),?_⟩
    intro he
    have hh := congrFun he 0
    change false = true at hh
    cases hh




def prefixRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@execution_prefix_law) (type_of% (realize prefixSignature (fun _ C ω => run C.decode C.initial ω) (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FiniteFairBitFirstReturn.execution_prefix_law.__information_unit,
  realizationName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FiniteFairBitFirstReturn.prefixRecord,
  realizationSource := none, generated := false,
  arena := .source ⟨prefixArena⟩, objectArena := .source ⟨prefixArena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source prefixArena ⟨prefixRecord⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize prefixSignature (fun _ C ω => run C.decode C.initial ω) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FiniteFairBitFirstReturn, definition := none, coordinates := #[0,4,5],
    readouts := #[{
      path := #["body","body","body","body","body","body","body","body","fn","arg","fn","arg","fn","arg","body","body","fn"],
      stateBinder := 8, functionOperand := false, stateOperand := none,
      booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none,
  options := #[{ name := `relaxedAutoImplicit, value := .bool false }] }

def invocationRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@invocation_return_iff) (type_of% (realize invocationSignature (fun _ C ω => executeUntil C.program (launch C.program C.initial C.mode C.input) ω C.bound) (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FiniteFairBitFirstReturn.invocation_return_iff.__information_unit,
  realizationName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FiniteFairBitFirstReturn.invocationRecord,
  realizationSource := none, generated := false,
  arena := .source ⟨invocationArena⟩, objectArena := .source ⟨invocationArena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source invocationArena ⟨invocationRecord⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize invocationSignature (fun _ C ω => executeUntil C.program (launch C.program C.initial C.mode C.input) ω C.bound) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FiniteFairBitFirstReturn, definition := none, coordinates := #[0,1,2,3,4,5,6,8],
    readouts := #[{
      path := #["body","body","body","body","body","body","body","body","body","body","fn","arg","fn","arg"],
      stateBinder := 0, functionOperand := false, stateOperand := some #["fn","arg"],
      booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none,
  options := #[{ name := `relaxedAutoImplicit, value := .bool false }] }

def suffixRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@charged_execution_prefix) (type_of% (realize suffixSignature (fun _ C ω => unused (decoded C.program) C.initial ω C.bound) (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FiniteFairBitFirstReturn.charged_execution_prefix.__information_unit,
  realizationName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FiniteFairBitFirstReturn.suffixRecord,
  realizationSource := none, generated := false,
  arena := .source ⟨suffixArena⟩, objectArena := .source ⟨suffixArena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source suffixArena ⟨suffixRecord⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize suffixSignature (fun _ C ω => unused (decoded C.program) C.initial ω C.bound) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FiniteFairBitFirstReturn, definition := none, coordinates := #[0,1,2,4,10,12],
    readouts := #[{
      path := #["body","body","body","body","body","body","body","body","body","body","body","body","body","body","arg","arg","arg","arg","fn","arg","body","body","fn","arg","fn"],
      stateBinder := 14, functionOperand := false, stateOperand := none,
      booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none,
  options := #[{ name := `relaxedAutoImplicit, value := .bool false }] }

abbrev splitSignature : Signature where
  Params := Unit
  State _ := ℕ → Bool
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Bool × (ℕ → Bool)
  Anchor := Empty
  finiteAnchor := inferInstance

def splitActual : Realization splitSignature :=
  realize splitSignature (fun _ _ ω => (ω 0,tail ω)) (fun e => nomatch e)
def splitBad : Realization splitSignature :=
  realize splitSignature (fun _ _ ω => (false,ω)) (fun e => nomatch e)
def splitArena : Arena where
  signature := splitSignature
  Law R := tapeLaw.map (R.readout () ()) = fairBit.toMeasure.prod tapeLaw
private theorem split_bad : ¬ splitArena.Law splitBad := by
  intro h
  have hm := congrArg (fun μ : Measure (Bool × (ℕ → Bool)) =>
    μ (({true} : Set Bool) ×ˢ univ)) h
  change (tapeLaw.map (fun ω : ℕ → Bool => (false,ω))) _ = _ at hm
  rw [Measure.map_apply (by fun_prop) ((measurableSet_singleton true).prod MeasurableSet.univ)] at hm
  have he : (fun ω : ℕ → Bool => (false,ω)) ⁻¹' (({true} : Set Bool) ×ˢ univ) = ∅ := by
    ext ω; simp
  rw [he,measure_empty,Measure.prod_prod,measure_univ,mul_one,
    PMF.toMeasure_apply_singleton] at hm
  · norm_num [fairBit,PMF.bernoulli_apply] at hm
    exact (ENNReal.inv_ne_zero.mpr (by simp)) hm.symm
  · exact measurableSet_singleton true

def splitRecord : Registration splitArena (type_of% (@split_tape)) where
  actual := splitActual
  bridge := Iff.rfl
  variation := ⟨split_tape,splitBad,split_bad⟩
  sensitivity := by
    letI : Subsingleton splitArena.signature.Role := by change Subsingleton Unit; infer_instance
    constructor
    · intro i
      refine ⟨splitBad,?_,rfl,split_bad⟩
      intro j hj; exact (hj (Subsingleton.elim _ _)).elim
    · intro i; exact nomatch i
  dependence := by
    intro i; cases i
    refine ⟨(),(fun _ => false),(fun _ => true),?_⟩
    intro h
    have hh := congrArg Prod.fst h
    change false = true at hh
    cases hh

def splitRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@split_tape) (type_of% (realize splitSignature (fun _ _ ω => (ω 0,tail ω))
      (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FiniteFairBitFirstReturn.split_tape.__information_unit,
  realizationName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FiniteFairBitFirstReturn.splitRecord,
  realizationSource := none, generated := false,
  arena := .source ⟨splitArena⟩, objectArena := .source ⟨splitArena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source splitArena ⟨splitRecord⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize splitSignature (fun _ _ ω => (ω 0,tail ω)) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := none, continuation := .unknown, familyRecord := none,
  options := #[{ name := `relaxedAutoImplicit, value := .bool false }] }

end Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FiniteFairBitFirstReturn
