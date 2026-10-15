import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Arith.FibonacciAtomic.Observer.NativeFibonacciStaticScan

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeFibonacciStaticScan
open _root_.D5.S3.Arith.FibonacciAtomic
open Observer
open Observer.NativeFibonacciStaticScan
open Observer.NativeSerialMachine (Event)
open Observer.NativeControlConjugacy
open Observer.NativeActiveParityExecution (chartOf source labels bit parity)
open ActualTreeReadoutAcquisition (Address Reply readout)
open GenealogicalFiberTransport (Source substitution)
open Observer.DelayedOriginalReadout (rights)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section
abbrev scanSignature := Reg.Support.SingleDependentReadout.signature (List Address)
  (fun _ => Source) (fun _ => Source)
def scanActual : Realization scanSignature := realize scanSignature (fun _ _ u => u) (fun e => nomatch e)
def scanRejected : Realization scanSignature := realize scanSignature (fun _ _ _ => .of true) (fun e => nomatch e)
abbrev scanArena : Arena where
  signature := scanSignature
  Law R := ∀ (ps : List Address) (u : Source),
    TableFacts ps ∧ ExecutionFacts ps (R.readout () ps u) (accumulate u false ps) (scanTrace u 0 ps) ∧
      (scanTrace u 0 ps).length = 3*ps.length + (ps.map (fun p => bit (psi (readout p u)))).sum
private theorem scanNegative : ¬ scanArena.Law scanRejected := by
  intro law
  have facts := (law [[]] (.of false)).2.1
  obtain ⟨p,h⟩ := facts.events (.read 0 [] .beta) (by decide)
  cases p <;> simp [readout,scanRejected,realize] at h
def scanEvidence : Registration scanArena (type_of% (@native_static_complete_scan)) where
  actual := scanActual
  bridge := Iff.rfl
  variation := ⟨native_static_complete_scan,scanRejected,scanNegative⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ scanNegative
  dependence := by
    intro i
    refine ⟨[],(.of true : Source),(.of false : Source),?_⟩
    intro same
    cases same

def scan : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@NativeFibonacciStaticScan.native_static_complete_scan) (Realization scanSignature) Unit Unit where
  unitName := `D5.S3.Arith.FibonacciAtomic.Observer.NativeFibonacciStaticScan.native_static_complete_scan.__information_unit
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeFibonacciStaticScan.scanEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨scanArena⟩
  objectArena := .source ⟨scanArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source scanArena ⟨scanEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize scanSignature scanActual.readout scanActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.NativeFibonacciStaticScan
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body","body","arg","fn","arg","fn","fn","arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

abbrev originalSignature := Reg.Support.SingleDependentReadout.signature Source
  (fun S => Fin S.length → Bool) (fun _ => Source)
def originalActual : Realization originalSignature :=
  realize originalSignature (fun _ S x => source (chartOf S) x) (fun e => nomatch e)
def originalRejected : Realization originalSignature :=
  realize originalSignature (fun _ _ _ => .of true) (fun e => nomatch e)
abbrev originalArena : Arena where
  signature := originalSignature
  Law R := ∀ (S : Source) (x : Fin S.length → Bool)
    (t K : Nat) (bound : t ≤ 2*K) (regime : S.length%2=0 ∨ t=0),
    let C := chartOf S
    let ps := dataList C K
    let u := substitution^[t] (R.readout () S x)
    TableFacts ps ∧ ps.length = S.length*(K+1) ∧
      ExecutionFacts ps u (parity (labels x) S.length) (scanTrace u 0 ps) ∧
      (scanTrace u 0 ps).length = 3*(S.length*(K+1)) + contributions x t ∧
      (ps.map List.length).sum = (K+1)*addressMass C + S.length*K*(K+1)/2 ∧
      (∀ p ∈ ps, p.length ≤ depth C+K) ∧ (∃ p ∈ ps, p.length = depth C+K) ∧
      SubmittedMaximum (scanTrace u 0 ps) (depth C+K) ∧
      (∀ i : Fin S.length, ∀ s : Nat,
        let n := t+bit (x i)
        let r := readout (C.address i ++ rights s) u
        n/2 ≤ K ∧
        (r = .absent ↔ n < 2*s) ∧ (r = .alpha ↔ n = 2*s) ∧
        (r = .beta ↔ n = 2*s+1) ∧ (r = .branch ↔ 2*s+2 ≤ n))
private theorem originalNegative : ¬ originalArena.Law originalRejected := by
  intro law
  have facts := (law (.of true) (fun _ => true) 0 0 (by decide) (Or.inr rfl)).2.2.1
  obtain ⟨trace,run,_⟩ := facts.first.1
  have forced := (native_static_complete_scan [[]] (.of true)).2.1.native
  have wrong : accumulate (.of true) false [[]] = false := rfl
  rw [wrong] at forced
  change Observer.NativeSerialMachine.Run (program [[]]) (start 1) 0 (.of true) trace true at run
  have incompatible := Observer.NativeSerialDepth.run_unique run forced
  cases incompatible.2
def originalEvidence : Registration originalArena (type_of% (@original_static_parity_scan)) where
  actual := originalActual
  bridge := Iff.rfl
  variation := ⟨original_static_parity_scan,originalRejected,originalNegative⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ originalNegative
  dependence := by
    intro i
    refine ⟨(.of true : Source),(fun _ => false),(fun _ => true),?_⟩
    intro same
    have raw := congrArg (readout []) same
    change Reply.alpha = Reply.beta at raw
    cases raw

def original : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@NativeFibonacciStaticScan.original_static_parity_scan) (Realization originalSignature) Unit Unit where
  unitName := `D5.S3.Arith.FibonacciAtomic.Observer.NativeFibonacciStaticScan.original_static_parity_scan.__information_unit
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeFibonacciStaticScan.originalEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨originalArena⟩
  objectArena := .source ⟨originalArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source originalArena ⟨originalEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize originalSignature originalActual.readout originalActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.NativeFibonacciStaticScan
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body","body","body","body","body","body","body","body","value","arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms scanEvidence
#print axioms originalEvidence
abbrev paritySumSignature : Signature where
  Params := Nat
  State _ := Nat → Bool
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def paritySumActual : Realization paritySumSignature :=
  realize paritySumSignature (fun _ n x => parity x n) (fun e => nomatch e)
def paritySumBad : Realization paritySumSignature :=
  realize paritySumSignature (fun _ _ _ => false) (fun e => nomatch e)
abbrev paritySumArena : Arena where
  signature := paritySumSignature
  Law R := ∀ (x : Nat → Bool) (n : Nat),
    R.readout () n x = decide (((List.range n).map (fun i => bit (x i))).sum%2=1)
private theorem parity_sum_bad : ¬ paritySumArena.Law paritySumBad := by
  intro law
  have no := law (fun _ => true) 1
  change false = true at no
  cases no

def paritySumEvidence : Registration paritySumArena (type_of% (@parity_sum)) where
  actual := paritySumActual
  bridge := Iff.rfl
  variation := ⟨@parity_sum,paritySumBad,parity_sum_bad⟩
  sensitivity := ⟨fun i => ⟨paritySumBad,
    fun j h => (h (Subsingleton.elim j i)).elim,rfl,parity_sum_bad⟩, fun e => nomatch e⟩
  dependence := by
    intro i
    refine ⟨1,(fun _ => false),(fun _ => true),?_⟩
    change false ≠ true
    decide

noncomputable def parity_sum_registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeFibonacciStaticScan.parity_sum) (Realization paritySumSignature) Unit Unit where
  unitName := `D5.S3.Arith.FibonacciAtomic.Observer.NativeFibonacciStaticScan.parity_sum.__information_unit
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeFibonacciStaticScan.paritySumEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨paritySumArena⟩
  objectArena := .source ⟨paritySumArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source paritySumArena ⟨paritySumEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize paritySumSignature paritySumActual.readout paritySumActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.NativeFibonacciStaticScan
    definition := none
    coordinates := #[1]
    readouts := #[{
      path := #["body","body","fn","arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn","arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]


end
end Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeFibonacciStaticScan
