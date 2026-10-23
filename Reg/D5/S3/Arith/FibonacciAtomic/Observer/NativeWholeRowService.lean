import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.FibonacciAtomic.Observer.NativeFiniteBudgetClassification
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false

open D5.S3.Arith.FibonacciAtomic.GenealogicalFiberTransport (Source substitution)
open D5.S3.Arith.FibonacciAtomic.ActualTreeReadoutAcquisition (Address Reply readout)
open D5.S3.Arith.FibonacciAtomic.Observer.ActualCutPartitionRecovery
open D5.S3.Arith.FibonacciAtomic.Observer.ActualCutPartitionDecoder
open D5.S3.Arith.FibonacciAtomic.Observer.NativeDepthPatterns (History Consistent)
open D5.S3.Arith.FibonacciAtomic.Observer.NativeWholeRowService
open D5.S3.Arith.FibonacciAtomic.Observer.NativeFiniteBudgetClassification
open D5.S3.ConceptDynamics.Experiment.PassivePolicyNormalization (Hist execute execute_mono)
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeWholeRowService
abbrev signature : Signature where
  Params := CutSet
  State _ := Source
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Record
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ Q u => literalRecord Q u) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (P Q : CutSet) (_ : CutPrefixFree P) (_ : CutPrefixFree Q)
    (base : Source) (H : History),
    (analyze (canonicalRow P base) Q H).passes = true → ∀ (N : Nat) (u : Source),
    canonicalRow P u = canonicalRow P base → Consistent H u →
    ∃ fuel trace,
      execute readout (controller (compileService (canonicalRow P base) Q H N)) fuel []
        (substitution^[N] u) = some (trace,R.readout () Q u) ∧
      trace.length ≤ K0 (canonicalRow P base) Q H

theorem bridge : (type_of% (@stationary_whole_fiber_service)) ↔ arena.Law actual := Iff.rfl

theorem actual_law : arena.Law actual := @stationary_whole_fiber_service

def bad : Realization signature := realize signature
  (fun _ _ _ => (.of (.inl true),∅)) (fun e => nomatch e)

private theorem empty_prefixFree : CutPrefixFree (∅ : CutSet) := by
  intro p hp
  simpa using hp

private theorem bad_law : ¬ arena.Law bad := by
  intro law
  let beta : Source := .of false
  have good : (analyze (canonicalRow ∅ beta) ∅ []).passes = true := by
    apply Bool.eq_true_of_not_eq_false
    intro failed
    obtain ⟨u,v,hu,hv,same,different⟩ := criterion_failure_arbitrary_depth
      ∅ ∅ empty_prefixFree empty_prefixFree beta [] failed 0
    exact different (hu.1.trans hv.1.symm)
  have hist : Consistent [] beta := by simp [Consistent]
  obtain ⟨m,t,run,budget⟩ := law ∅ ∅ empty_prefixFree empty_prefixFree beta [] good 0 beta rfl hist
  obtain ⟨n,s,correct,budget'⟩ := stationary_whole_fiber_service
    ∅ ∅ empty_prefixFree empty_prefixFree beta [] good 0 beta rfl hist
  let prog := controller (compileService (canonicalRow ∅ beta) ∅ [] 0)
  have run' := execute_mono readout prog m (max m n) [] beta t (bad.readout () ∅ beta)
    (Nat.le_max_left _ _) run
  have correct' := execute_mono readout prog n (max m n) [] beta s (literalRecord ∅ beta)
    (Nat.le_max_right _ _) correct
  have results := Option.some.inj (run'.symm.trans correct')
  have rows := congrArg Prod.snd results
  have exterior := congrArg Prod.fst rows
  change (FreeMagma.of (.inl true) : HoleExterior) = .of (.inl false) at exterior
  cases exterior

def proof : Registration arena (type_of% (@stationary_whole_fiber_service)) where
  actual := actual
  bridge := bridge
  variation := ⟨actual_law,bad,bad_law⟩
  sensitivity := ⟨fun i => ⟨bad,fun j h => (h (Subsingleton.elim j i)).elim,rfl,bad_law⟩,
    fun i => nomatch i⟩
  dependence := by
    intro i
    refine ⟨∅,.of true,.of false,?_⟩
    intro eq
    have exterior := congrArg Prod.fst eq
    change (FreeMagma.of (.inl true) : HoleExterior) = .of (.inl false) at exterior
    cases exterior

noncomputable def stationary_whole_fiber_service_registration :
    LeanInformationAudit.Contract.Registration.{0,1,1,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeWholeRowService.stationary_whole_fiber_service)
    (Realization signature)
    ((P Q : CutSet) → CutPrefixFree P → CutPrefixFree Q →
      (base : Source) → (H : History) → (analyze (canonicalRow P base) Q H).passes = true → Nat → Type) Unit where
  unitName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeWholeRowService.stationary_whole_fiber_service
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeWholeRowService.proof
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨proof⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ Q u => literalRecord Q u) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some (fun (P Q : CutSet) (_ : CutPrefixFree P) (_ : CutPrefixFree Q)
    (base : Source) (H : History) (_ : (analyze (canonicalRow P base) Q H).passes = true)
    (_ : Nat) => Source)
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.NativeWholeRowService
    definition := none
    coordinates := #[0,1,2,3,4,5,6,7]
    readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "body", "arg", "body", "fn", "arg", "arg", "arg", "arg"], stateBinder := 8, functionOperand := false, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms proof
#print axioms stationary_whole_fiber_service_registration
end Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeWholeRowService
