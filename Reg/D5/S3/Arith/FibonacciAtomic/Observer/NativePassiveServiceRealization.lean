import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.FibonacciAtomic.Observer.NativePassiveServiceRealization
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false

open D5.S3.Arith.FibonacciAtomic.Observer
open D5.S3.Arith.FibonacciAtomic.GenealogicalFiberTransport (Source)
open D5.S3.Arith.FibonacciAtomic.ActualTreeReadoutAcquisition (Address Reply readout)
open NativeSerialMachine NativeSerialEffective NativePassiveServiceRealization
open D5.S3.ConceptDynamics.Experiment.PassivePolicyNormalization (execute)
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativePassiveServiceRealization

abbrev signature : Signature where
  Params := Nat
  State _ := PaidHistory
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Trace
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ N t => paidTrace N t) (fun e => nomatch e)

def bad : Realization signature := realize signature
  (fun _ _ _ => [.localStep]) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {L O : Type} [Primcodable O]
    (π : PaidHistory → Sum Address L) (enc : L → O) (fallback : O)
    (K fuel : Nat) (h : PaidHistory) (input N : Nat) (prior : List OriginalEvent)
    (r : Source) (t : PaidHistory) (o : L),
    execute readout π fuel h r = some (t,o) → t.length ≤ K →
    let table := materialize π enc fallback K h
    OriginalRun (tableService table fallback) (input,0,N,prior) r
      (R.readout () N t) (enc o) ∧
    (∃ final : OriginalState,
      executeTable table fallback fuel (input,0,N,prior) r =
        some (paidTrace N t,final,enc o) ∧
      final.input = input ∧ final.epoch = N ∧
      final.history = prior ++ recordReads N t) ∧
    reads (paidTrace N t) = t.map (fun a => (N,a.1,a.2)) ∧
    answers (paidTrace N t) = t.map Sigma.snd ∧
    (answers (paidTrace N t)).length = t.length

private theorem bad_law : ¬ arena.Law bad := by
  intro law
  have supplied := law (fun _ : PaidHistory => (Sum.inr () : Sum Address Unit))
    id () 0 1 [] 0 0 [] (.of true) [] () rfl (by simp)
  have impossible := supplied.1
  cases impossible

def proof : Registration arena (type_of% (@bounded_passive_realization)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@bounded_passive_realization,bad,bad_law⟩
  sensitivity := ⟨fun i => ⟨bad,fun j h => (h (Subsingleton.elim j i)).elim,rfl,bad_law⟩,
    fun i => nomatch i⟩
  dependence := by
    intro i
    refine ⟨0,[],[⟨[],Reply.alpha⟩],?_⟩
    simp [actual,realize,paidTrace]

noncomputable def bounded_passive_realization_registration :
    LeanInformationAudit.Contract.Registration.{0,1,1,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.Arith.FibonacciAtomic.Observer.NativePassiveServiceRealization.bounded_passive_realization)
    (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativePassiveServiceRealization.bounded_passive_realization
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativePassiveServiceRealization.proof
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨proof⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.NativePassiveServiceRealization
    definition := none
    coordinates := #[10]
    readouts := #[{ path := #["body","body","body","body","body","body","body","body","body","body","body","body","body","body","body","body","body","body","fn","arg","fn","arg"], stateBinder := 13, functionOperand := false, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms proof
#print axioms bounded_passive_realization_registration
end Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativePassiveServiceRealization
