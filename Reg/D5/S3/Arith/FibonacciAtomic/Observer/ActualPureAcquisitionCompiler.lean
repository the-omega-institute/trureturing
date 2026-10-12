import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.FibonacciAtomic.Observer.ActualPureAcquisitionCompiler
import Reg.Support.DependentFamily
import Reg.Support.FibonacciAtomic.ActualPureAcquisitionCompiler

set_option autoImplicit false
set_option relaxedAutoImplicit false

open D5.S3.Arith.FibonacciAtomic.Observer.ActualPureAcquisitionCompiler
open D5.S3.Arith.FibonacciAtomic.Observer.ActualAcquisitionCacheFiber
open D5.S3.Arith.FibonacciAtomic.Observer.ActualObserverAbsorbingNormalization
open D5.S3.Arith.FibonacciAtomic.ActualFiniteObserverAbsentElimination
open D5.S3.Arith.FibonacciAtomic.ActualTreeReadoutAcquisition
open D5.S3.Arith.FibonacciAtomic.GenealogicalFiberTransport (Source)
open D5.S3.Arith.FibonacciAtomic.ActualCoarseReadoutHistory (kappa_hist)
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.Arith.FibonacciAtomic.Observer.ActualPureAcquisitionCompiler

noncomputable def pureState_card_registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Arith.FibonacciAtomic.Observer.ActualPureAcquisitionCompiler.pureState_card) (Realization countArena.signature) Unit Unit where
  unitName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.ActualPureAcquisitionCompiler.pureState_card
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.ActualPureAcquisitionCompiler.countProof
  realizationSource := none
  generated := false
  arena := .source ⟨countArena⟩
  objectArena := .source ⟨countArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source countArena ⟨countProof⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize countArena.signature countActual.readout countActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.ActualPureAcquisitionCompiler
    definition := none
    coordinates := #[]
    readouts := #[{ path := #["body", "fn", "arg"], stateBinder := 0, functionOperand := false, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms pureState_card_registration

noncomputable def trace_addresses_registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Arith.FibonacciAtomic.Observer.ActualPureAcquisitionCompiler.trace_addresses) (Realization traceArena.signature) Unit Unit where
  unitName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.ActualPureAcquisitionCompiler.trace_addresses
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.ActualPureAcquisitionCompiler.traceProof
  realizationSource := none
  generated := false
  arena := .source ⟨traceArena⟩
  objectArena := .source ⟨traceArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source traceArena ⟨traceProof⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize traceArena.signature traceActual.readout traceActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.ActualPureAcquisitionCompiler
    definition := none
    coordinates := #[1]
    readouts := #[{ path := #["body", "body", "fn", "arg"], stateBinder := 0, functionOperand := false, stateOperand := some #["arg", "arg"], booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms trace_addresses_registration

noncomputable def pure_all_history_factorization_registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Arith.FibonacciAtomic.Observer.ActualPureAcquisitionCompiler.pure_all_history_factorization) (Realization quotientArena.signature) Unit Unit where
  unitName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.ActualPureAcquisitionCompiler.pure_all_history_factorization
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.ActualPureAcquisitionCompiler.quotientProof
  realizationSource := none
  generated := false
  arena := .source ⟨quotientArena⟩
  objectArena := .source ⟨quotientArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source quotientArena ⟨quotientProof⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize quotientArena.signature quotientActual.readout quotientActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.ActualPureAcquisitionCompiler
    definition := none
    coordinates := #[]
    readouts := #[{ path := #["body", "body", "arg"], stateBinder := 0, functionOperand := true, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms pure_all_history_factorization_registration

noncomputable def pure_acquisition_run_registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Arith.FibonacciAtomic.Observer.ActualPureAcquisitionCompiler.pure_acquisition_run) (Realization runArena.signature) Unit Unit where
  unitName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.ActualPureAcquisitionCompiler.pure_acquisition_run
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.ActualPureAcquisitionCompiler.runProof
  realizationSource := none
  generated := false
  arena := .source ⟨runArena⟩
  objectArena := .source ⟨runArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source runArena ⟨runProof⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize runArena.signature runActual.readout runActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.ActualPureAcquisitionCompiler
    definition := none
    coordinates := #[]
    readouts := #[{ path := #["body", "body", "body", "body", "arg", "body", "fn", "fn", "arg"], stateBinder := 2, functionOperand := false, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms pure_acquisition_run_registration

private abbrev cacheTraceArena : Arena where
  signature := runSignature
  Law R := ∀ (N : Nat) (positive : 1 ≤ N) (U : Source), Allowed N U →
    ∀ {e : PureState N} {h : RawHistory}, ActualPrefix (pureObserver N positive) U e h →
      h.IsPrefix (R.readout () () U) ∧ (pureObserver N positive).decoder e = h ∧ CacheTruth h U

private theorem cacheTrace_rejected : ¬ cacheTraceArena.Law runRejected := by
  intro h
  obtain ⟨f, run⟩ := pure_acquisition_run 1 (by omega) (.of true) (by exact Nat.le_refl 1)
  have pref := (run_from_actualPrefix _ _ run ActualPrefix.initial).1
  simp only [List.nil_append] at pref
  have bad := (h 1 (by omega) (.of true) (by exact Nat.le_refl 1) pref).1
  change (acquisitionTrace [] (.of true)).IsPrefix [] at bad
  have empty := List.eq_nil_of_prefix_nil bad
  simp [acquisitionTrace] at empty

private def cacheTraceProof : Registration cacheTraceArena (type_of% (@pure_actual_prefix_cache)) where
  actual := runActual
  bridge := Iff.rfl
  variation := ⟨pure_actual_prefix_cache, runRejected, cacheTrace_rejected⟩
  sensitivity := ⟨fun i => ⟨runRejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, cacheTrace_rejected⟩,
    fun i => nomatch i⟩
  dependence := by
    intro i
    refine ⟨(), .of true, .of false, ?_⟩
    intro bad
    cases bad

#print axioms cacheTraceProof
#print axioms _root_.D5.S3.Arith.FibonacciAtomic.Observer.ActualPureAcquisitionCompiler.pure_actual_prefix_cache

noncomputable def pure_actual_prefix_cache_registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Arith.FibonacciAtomic.Observer.ActualPureAcquisitionCompiler.pure_actual_prefix_cache) (Realization cacheTraceArena.signature) Unit Unit where
  unitName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.ActualPureAcquisitionCompiler.pure_actual_prefix_cache
  realizationName := ``cacheTraceProof
  realizationSource := none
  generated := false
  arena := .source ⟨cacheTraceArena⟩
  objectArena := .source ⟨cacheTraceArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source cacheTraceArena ⟨cacheTraceProof⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize cacheTraceArena.signature runActual.readout runActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.ActualPureAcquisitionCompiler
    definition := none
    coordinates := #[]
    readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "fn", "arg", "arg"], stateBinder := 2, functionOperand := false, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms pure_actual_prefix_cache_registration

noncomputable def pure_admissible_registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Arith.FibonacciAtomic.Observer.ActualPureAcquisitionCompiler.pure_admissible) (Realization admissibleArena.signature) Unit Unit where
  unitName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.ActualPureAcquisitionCompiler.pure_admissible
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.ActualPureAcquisitionCompiler.admissibleProof
  realizationSource := none
  generated := false
  arena := .source ⟨admissibleArena⟩
  objectArena := .source ⟨admissibleArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source admissibleArena ⟨admissibleProof⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize admissibleArena.signature admissibleActual.readout admissibleActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.ActualPureAcquisitionCompiler
    definition := none
    coordinates := #[0]
    readouts := #[{ path := #["body", "body"], stateBinder := 0, functionOperand := false, stateOperand := some #["arg"], booleanPredicate := true }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms pure_admissible_registration

noncomputable def pure_node_fee_registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Arith.FibonacciAtomic.Observer.ActualPureAcquisitionCompiler.pure_node_fee) (Realization nodeArena.signature) Unit Unit where
  unitName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.ActualPureAcquisitionCompiler.pure_node_fee
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.ActualPureAcquisitionCompiler.nodeProof
  realizationSource := none
  generated := false
  arena := .source ⟨nodeArena⟩
  objectArena := .source ⟨nodeArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source nodeArena ⟨nodeProof⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize nodeArena.signature nodeActual.readout nodeActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.ActualPureAcquisitionCompiler
    definition := none
    coordinates := #[2]
    readouts := #[{ path := #["body", "body", "body", "body", "body", "arg"], stateBinder := 3, functionOperand := false, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms pure_node_fee_registration

noncomputable def pure_joint_price_registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Arith.FibonacciAtomic.Observer.ActualPureAcquisitionCompiler.pure_joint_price) (Realization nominalPriceArena.signature) Unit Unit where
  unitName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.ActualPureAcquisitionCompiler.pure_joint_price
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.ActualPureAcquisitionCompiler.nominalPriceProof
  realizationSource := none
  generated := false
  arena := .source ⟨nominalPriceArena⟩
  objectArena := .source ⟨nominalPriceArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source nominalPriceArena ⟨nominalPriceProof⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize nominalPriceArena.signature nominalPriceActual.readout nominalPriceActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.ActualPureAcquisitionCompiler
    definition := none
    coordinates := #[0]
    readouts := #[{ path := #["body", "body", "body", "body", "fn", "arg", "arg", "fn", "arg"], stateBinder := 3, functionOperand := false, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms pure_joint_price_registration

namespace NodeDepth

abbrev signature : Signature where
  Params := Source
  State _ := Address
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Nat
  Anchor := Empty
  finiteAnchor := inferInstance

noncomputable def actual : Realization signature :=
  realize signature (fun _ _ q => q.length) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (U : Source) (q : Address), q ∈ nodes U →
    R.readout () U q + 1 ≤ U.length

theorem bridge : (type_of% (@nodes_length)) ↔ arena.Law actual := Iff.rfl

theorem actual_law : arena.Law actual := nodes_length

noncomputable def bad : Realization signature :=
  realize signature (fun _ U _ => U.length) (fun e => nomatch e)

theorem bad_law : ¬ arena.Law bad := by
  intro law
  have impossible := law (.of true) [] (by simp [nodes])
  exact (by decide : ¬ ((1 : Nat) + 1 ≤ 1)) impossible

theorem variation : Variation arena actual := ⟨actual_law, bad, bad_law⟩

theorem sensitivity : Sensitivity arena actual := by
  constructor
  · intro i
    refine ⟨bad, ?_, ?_, bad_law⟩
    · intro j different
      exact (different (Subsingleton.elim j i)).elim
    · funext e
      cases e
  · intro e
    cases e

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨.mul (.of true) (.of false), [], [false], ?_⟩
  change (0 : Nat) ≠ 1
  decide

noncomputable def family : Registration arena (type_of% (@nodes_length)) where
  actual := actual
  bridge := bridge
  variation := variation
  sensitivity := sensitivity
  dependence := dependence

noncomputable def registration : LeanInformationAudit.Contract.Registration.{_, _, _,
    0, 0, 0, 0, 0, 0, 0, 0, 0} (@nodes_length) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.ActualPureAcquisitionCompiler.NodeDepth.unit
  realizationName :=
    `Reg.D5.S3.Arith.FibonacciAtomic.Observer.ActualPureAcquisitionCompiler.NodeDepth.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := true
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .evidence ⟨(True.intro : True)⟩ True.intro
  readout := some (realize signature actual.readout actual.anchor)
  variation := .evidence ⟨(True.intro : True)⟩ True.intro
  sensitivity := .evidence ⟨(True.intro : True)⟩ True.intro
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.ActualPureAcquisitionCompiler
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }]
  }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms family
#print axioms registration

end NodeDepth

namespace NodeDistinct

abbrev signature : Signature where
  Params := Unit
  State _ := Source
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := List Address
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ U => nodes U) (fun e => nomatch e)

def bad : Realization signature :=
  realize signature (fun _ _ _ => [[],[]]) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ U : Source, (R.readout () () U).Nodup

private theorem bad_law : ¬ arena.Law bad := by
  intro h
  simpa [bad,realize] using h (.of true)

def proof : Registration arena (type_of% (@nodes_nodup)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨nodes_nodup,bad,bad_law⟩
  sensitivity := ⟨fun i => ⟨bad,
    fun j h => (h (Subsingleton.elim j i)).elim,rfl,bad_law⟩,fun i => nomatch i⟩
  dependence := by
    intro i
    refine ⟨(),.of true,.mul (.of true) (.of true),?_⟩
    simp [actual,realize,nodes]

noncomputable def registration :
    LeanInformationAudit.Contract.Registration.{0,1,1,0,0,0,0,0,0,0,0,0}
    (@nodes_nodup) (Realization signature) Type Unit where
  unitName :=
    `Reg.D5.S3.Arith.FibonacciAtomic.Observer.ActualPureAcquisitionCompiler.NodeDistinct.unit
  realizationName :=
    `Reg.D5.S3.Arith.FibonacciAtomic.Observer.ActualPureAcquisitionCompiler.NodeDistinct.proof
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨proof⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ U => nodes U) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some Source
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.ActualPureAcquisitionCompiler
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body","arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end NodeDistinct

end Reg.D5.S3.Arith.FibonacciAtomic.Observer.ActualPureAcquisitionCompiler
