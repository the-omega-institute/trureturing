import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.FibonacciAtomic.Observer.SparseLiteralParityReadLowerBound
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false

open D5.S3.Arith.FibonacciAtomic.GenealogicalFiberTransport (Source substitution)
open D5.S3.Arith.FibonacciAtomic.ActualTreeReadoutAcquisition (Address Reply readout)
open D5.S3.Arith.FibonacciAtomic.Observer.NativeSerialMachine (Op Event Trace Run reads)
open D5.S3.Arith.FibonacciAtomic.Observer.NativeDepthPatterns (Frontier fill frontierAddress)
open D5.S3.Arith.FibonacciAtomic.Observer.NativePolynomialDescriptorObstruction (fullPattern)
open D5.S3.Arith.FibonacciAtomic.Observer.SparseLiteralControlTable
open D5.S3.Arith.FibonacciAtomic.Observer.SparseLiteralParityReadLowerBound
open D5.S3.Arith.FibonacciAtomic
open D5.S3.Arith.FibonacciAtomic.Observer
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.Arith.FibonacciAtomic.Observer.SparseLiteralParityReadLowerBound
noncomputable section
attribute [local instance] Classical.propDecidable

abbrev paritySignature : Signature where
  Params := Nat
  State h := Fin h → Bool
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def parityActual : Realization paritySignature :=
  realize paritySignature (fun _ _ x => parity x) (fun e => nomatch e)

def parityBad : Realization paritySignature :=
  realize paritySignature (fun _ _ _ => false) (fun e => nomatch e)

abbrev readArena : Arena where
  signature := paritySignature
  Law R := ∀ {h depth : Nat} {C : Type}
    (slots : Fin h → Frontier (fullPattern depth))
    (distinct : Function.Injective (fun i => frontierAddress (fullPattern depth) (slots i)))
    (δ : C → Op C Bool) (start : C)
    (sound : ∀ x t out, Run δ start 0 (source slots x) t out → out = R.readout () h x)
    (x : Fin h → Bool) (trace : Trace) (out : Bool)
    (run : Run δ start 0 (source slots x) trace out),
    h ≤ (reads trace).length ∧
    ∀ i : Fin h, ∃ e a r, Event.read e a r ∈ trace ∧
      (frontierAddress (fullPattern depth) (slots i)).IsPrefix a

abbrev literalArena : Arena where
  signature := paritySignature
  Law R := ∀ {h depth : Nat} {C : Type} [Fintype C]
    (positive : 0 < h) (q : Fin h → Address) (lengths : ∀ i, (q i).length = depth)
    (distinct : Function.Injective q) (δ : C → Op C Bool) (start : C)
    (sound : ∀ x t out, Run δ start 0 (originalSource depth q lengths x) t out → out = R.readout () h x)
    (total : ∀ x, ∃ t out, Run δ start 0 (originalSource depth q lengths x) t out),
    (∀ x i, ActualLeafHistoryRigidity.subtree (q i) (originalSource depth q lengths x) =
      some (.of (!(x i)))) ∧
    (∀ x j, (∀ i, frontierAddress (fullPattern depth) j ≠ q i) →
      ActualLeafHistoryRigidity.subtree (frontierAddress (fullPattern depth) j)
        (originalSource depth q lengths x) = some (.of true)) ∧
    h + 2 ≤ Fintype.card C ∧
    (∀ x trace out, Run δ start 0 (originalSource depth q lengths x) trace out →
      h ≤ (reads trace).length) ∧
    ∀ (width : Nat) (encode : C → {w : Fin width → Bool //
      D5.S1.Words.AdmissibleWords.AdmissibleCount.Adm width w}),
      Function.Injective encode → h + 2 ≤ Nat.fib (width + 2)

private theorem stop_output {C : Type} {c : C} {e : Nat} {u : Source}
    {t : Trace} {o : Bool} (r : Run (fun _ : C => .stop false) c e u t o) : o = false := by
  cases r with
  | stop row => exact (Op.stop.inj row).symm
  | localStep row _ => cases row
  | update row _ => cases row
  | read row _ _ => cases row

private theorem read_bad : ¬ readArena.Law parityBad := by
  intro law
  have result := @law 1 0 Unit (fun _ => ())
    (fun i j _ => Subsingleton.elim i j) (fun _ => .stop false) ()
    (fun _ _ _ r => stop_output r) (fun _ => false) [] false (Run.stop rfl)
  have impossible : 1 ≤ 0 := result.1
  omega

private theorem literal_bad : ¬ literalArena.Law parityBad := by
  intro law
  have result := @law 1 0 Unit inferInstance (by decide) (fun _ => []) (fun _ => rfl)
    (fun i j _ => Subsingleton.elim i j) (fun _ => .stop false) ()
    (fun _ _ _ r => stop_output r) (fun _ => ⟨[], false, Run.stop rfl⟩)
  have impossible : 3 ≤ 1 := result.2.2.1
  omega

private theorem parity_dependence : ObservationalDependence paritySignature parityActual := by
  intro i
  refine ⟨1, (fun _ => false), (fun _ => true), ?_⟩
  simp [parityActual, realize, parity]

def readProof : Registration readArena (type_of% (@parity_read_lower_bound)) where
  actual := parityActual
  bridge := Iff.rfl
  variation := ⟨@parity_read_lower_bound, parityBad, read_bad⟩
  sensitivity := ⟨fun i => ⟨parityBad,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, read_bad⟩, fun i => nomatch i⟩
  dependence := parity_dependence

def literalProof : Registration literalArena (type_of% (@literal_parity_lower_bounds)) where
  actual := parityActual
  bridge := Iff.rfl
  variation := ⟨@literal_parity_lower_bounds, parityBad, literal_bad⟩
  sensitivity := ⟨fun i => ⟨parityBad,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, literal_bad⟩, fun i => nomatch i⟩
  dependence := parity_dependence

abbrev recoverySignature : Signature where
  Params := Σ _ : Nat, Nat → Address
  State _ := List Bool
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Source
  Anchor := Empty
  finiteAnchor := inferInstance

def recoveryActual : Realization recoverySignature :=
  realize recoverySignature (fun _ p bits => familySource p.1 p.2 bits) (fun e => nomatch e)

def recoveryBad : Realization recoverySignature :=
  realize recoverySignature (fun _ _ _ => .of true) (fun e => nomatch e)

abbrev recoveryArena : Arena where
  signature := recoverySignature
  Law R := ∀ (depth : Nat) (q : Nat → Address) (bits : List Bool)
    (positive : 0 < bits.length)
    (lengths : ∀ i < bits.length, (q i).length = depth)
    (distinct : Function.Injective (fun i : Fin bits.length => q i)),
    Recovery q (R.readout () ⟨depth,q⟩ bits) bits positive

private theorem recovery_bad : ¬ recoveryArena.Law recoveryBad := by
  intro law
  have result := law 0 (fun _ => []) [true] (by decide) (fun _ _ => rfl)
    (by
      intro i j _
      apply Fin.ext
      have hi := i.isLt
      have hj := j.isLt
      change i.val < 1 at hi
      change j.val < 1 at hj
      omega)
  have run := result.2.1
  cases run with
  | read row reply tail =>
      simp only [table] at row
      cases row
      cases tail with
      | stop row =>
          simp [table, responseSuccessor, decodeBit, recoveryBad, realize,
            queries, DelayedOriginalReadout.rights, readout] at row

private theorem recovery_dependence :
    ObservationalDependence recoverySignature recoveryActual := by
  intro i
  refine ⟨⟨0, fun _ => []⟩, [false], [true], ?_⟩
  simp [recoveryActual, realize, familySource, fullPattern, fill, familyLabel,
    frontierAddress]
  intro eq
  cases eq

def recoveryProof : Registration recoveryArena (type_of% (@complete_skeleton_recovery)) where
  actual := recoveryActual
  bridge := Iff.rfl
  variation := ⟨@complete_skeleton_recovery, recoveryBad, recovery_bad⟩
  sensitivity := ⟨fun i => ⟨recoveryBad,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, recovery_bad⟩, fun i => nomatch i⟩
  dependence := recovery_dependence

noncomputable def parity_read_lower_bound_registration : LeanInformationAudit.Contract.Registration.{0,1,1,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.Arith.FibonacciAtomic.Observer.SparseLiteralParityReadLowerBound.parity_read_lower_bound)
    (Realization paritySignature) Type Unit where
  unitName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.SparseLiteralParityReadLowerBound.parity_read_lower_bound
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.SparseLiteralParityReadLowerBound.readProof
  realizationSource := none
  generated := false
  arena := .source ⟨readArena⟩
  objectArena := .source ⟨readArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source readArena ⟨readProof⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize paritySignature parityActual.readout parityActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.SparseLiteralParityReadLowerBound
    definition := none
    coordinates := #[0]
    readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "domain", "body", "body", "body", "body", "arg"], stateBinder := 7, functionOperand := false, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

noncomputable def literal_parity_lower_bounds_registration : LeanInformationAudit.Contract.Registration.{0,1,1,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.Arith.FibonacciAtomic.Observer.SparseLiteralParityReadLowerBound.literal_parity_lower_bounds)
    (Realization paritySignature) Type Unit where
  unitName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.SparseLiteralParityReadLowerBound.literal_parity_lower_bounds
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.SparseLiteralParityReadLowerBound.literalProof
  realizationSource := none
  generated := false
  arena := .source ⟨literalArena⟩
  objectArena := .source ⟨literalArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source literalArena ⟨literalProof⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize paritySignature parityActual.readout parityActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.SparseLiteralParityReadLowerBound
    definition := none
    coordinates := #[0]
    readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "domain", "body", "body", "body", "body", "arg"], stateBinder := 10, functionOperand := false, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

noncomputable def complete_skeleton_recovery_registration : LeanInformationAudit.Contract.Registration.{0,1,1,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.Arith.FibonacciAtomic.Observer.SparseLiteralControlTable.complete_skeleton_recovery)
    (Realization recoverySignature) Type Unit where
  unitName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.SparseLiteralParityReadLowerBound.complete_skeleton_recovery
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.SparseLiteralParityReadLowerBound.recoveryProof
  realizationSource := none
  generated := false
  arena := .source ⟨recoveryArena⟩
  objectArena := .source ⟨recoveryArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source recoveryArena ⟨recoveryProof⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize recoverySignature recoveryActual.readout recoveryActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.SparseLiteralParityReadLowerBound
    definition := none
    coordinates := #[0, 1]
    readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "fn", "fn", "arg"], stateBinder := 2, functionOperand := false, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

abbrev flipArena : Arena where
  signature := paritySignature
  Law R := ∀ {h : Nat} (x : Fin h → Bool) (i : Fin h),
    parity (Function.update x i (!(x i))) ≠ R.readout () h x
private theorem flip_bad : ¬ flipArena.Law parityBad := by
  intro law
  have no := @law 1 (fun _ => true) 0
  change false ≠ false at no
  exact no rfl

def flipEvidence : Registration flipArena (type_of% (@parity_flip)) where
  actual := parityActual
  bridge := Iff.rfl
  variation := ⟨@parity_flip,parityBad,flip_bad⟩
  sensitivity := ⟨fun i => ⟨parityBad,
    fun j h => (h (Subsingleton.elim j i)).elim,rfl,flip_bad⟩, fun e => nomatch e⟩
  dependence := parity_dependence

noncomputable def parity_flip_registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Arith.FibonacciAtomic.Observer.SparseLiteralParityReadLowerBound.parity_flip) (Realization paritySignature) Unit Unit where
  unitName := `D5.S3.Arith.FibonacciAtomic.Observer.SparseLiteralParityReadLowerBound.parity_flip.__information_unit
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.SparseLiteralParityReadLowerBound.flipEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨flipArena⟩
  objectArena := .source ⟨flipArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source flipArena ⟨flipEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize paritySignature parityActual.readout parityActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.SparseLiteralParityReadLowerBound
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body","body","body","arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]


end
end Reg.D5.S3.Arith.FibonacciAtomic.Observer.SparseLiteralParityReadLowerBound
