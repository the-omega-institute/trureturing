import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.FibonacciAtomic.Observer.FiniteMenu.NativeStationaryIntervalResources
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace Reg.D5.S3.Arith.FibonacciAtomic.Observer.FiniteMenu.NativeStationaryIntervalResources
open _root_.D5.S3.Arith.FibonacciAtomic.GenealogicalFiberTransport (Source)
open _root_.D5.S3.Arith.FibonacciAtomic.ActualTreeReadoutAcquisition (Address Reply readout)
open _root_.D5.S3.Arith.FibonacciAtomic.Geometry.AncestorAreaInstability (T)
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativePassiveServiceRealization (Dialogue)
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeClassRootSimulation (wordBound)
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeSerialMachine
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.FiniteMenu.NativeStationaryIntervalResources
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Capacity
abbrev signature : Signature where
  Params := Nat × Nat × Nat
  State _ := Dialogue Nat
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ p d => Identifies d p.1 p.2.1 p.2.2) (fun e => nomatch e)
def bad : Realization signature := realize signature (fun _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (L U : Nat), L ≤ U →
    (∀ k, (∃ (C : Type) (δ : C → Op C Nat) (c : C),
        Stationary δ ∧ SerialCorrect δ c L U k) ↔
      U-L+1 ≤ if L = 0 then zeroCapacity k else positiveCapacity k) ∧
    (∀ k, (∃ d : Dialogue Nat, R.readout () (L,U,k) d) ↔ minimumCalls L U ≤ k) ∧
    (∃ d : Dialogue Nat, R.readout () (L,U,minimumCalls L U) d) ∧
    (∀ (C O : Type) (δ : C → Op C O) (c : C) (_fallback : O) (k : Nat),
      Stationary δ → k < minimumCalls L U →
      (∀ n, L ≤ n → n ≤ U → ∃ t o, Run δ c 0 (T n) t o ∧ (answers t).length ≤ k) →
      ∃ a ∈ Finset.Icc L U, ∃ b ∈ Finset.Icc L U, a ≠ b ∧
        ∃ t o, Run δ c 0 (T a) t o ∧ Run δ c 0 (T b) t o)

private theorem bad_law : ¬ arena.Law bad := by
  intro h
  obtain ⟨d,hd⟩ := (h 0 0 le_rfl).2.2.1
  exact hd
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(0,0,0),.stop 0,.stop 1,?_⟩
  intro eq
  have yes : actual.readout () (0,0,0) (.stop 0) := by
    intro n lo hi
    change n ≤ 0 at hi
    have hn : n = 0 := Nat.eq_zero_of_le_zero hi
    subst n
    exact ⟨rfl,le_rfl⟩
  have no := Eq.mp eq yes
  have impossible := (no 0 le_rfl le_rfl).1
  cases impossible

def family : Registration arena (type_of% (@native_interval_capacity)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨native_interval_capacity,bad,bad_law⟩
  sensitivity := ⟨fun i => ⟨bad,fun j h => (h (Subsingleton.elim j i)).elim,rfl,bad_law⟩,
    fun e => nomatch e⟩
  dependence := dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@native_interval_capacity)
    (type_of% (realize signature actual.readout actual.anchor)) Type Unit where
  unitName := `D5.S3.Arith.FibonacciAtomic.Observer.FiniteMenu.NativeStationaryIntervalResources.native_interval_capacity.__information_unit
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.FiniteMenu.NativeStationaryIntervalResources.Capacity.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.FiniteMenu.NativeStationaryIntervalResources
    definition := none
    coordinates := #[0,1,3]
    readouts := #[{
      path := #["body","body","body","arg","fn","arg","body","fn","arg","arg","body"],
      stateBinder := 0, functionOperand := false,
      stateOperand := some #["fn","fn","fn","arg"], booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Capacity

namespace Recode
abbrev signature : Signature where
  Params := Nat
  State _ := Address
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Reply
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature (fun _ n p => readout p (T n))
  (fun e => nomatch e)
def bad : Realization signature := realize signature (fun _ _ _ => .absent) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (U : Nat), 1 ≤ U → ∀ p : Address,
    ∃ (q : Address) (phi : Reply → Reply), q.length ≤ min p.length ((U-1)/2) ∧
      ∀ n, n ≤ U → readout p (T n) = phi (R.readout () n q)
private theorem bad_law : ¬ arena.Law bad := by
  intro h
  obtain ⟨q,phi,_,eq⟩ := h 1 le_rfl []
  have zero := eq 0 (by decide)
  have one := eq 1 le_rfl
  have impossible := zero.trans one.symm
  cases impossible
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  exact ⟨0,[],[true],by change Reply.alpha ≠ .absent; decide⟩
def family : Registration arena (type_of% (@bounded_query_recode)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨bounded_query_recode,bad,bad_law⟩
  sensitivity := ⟨fun i => ⟨bad,fun j h => (h (Subsingleton.elim j i)).elim,rfl,bad_law⟩,
    fun e => nomatch e⟩
  dependence := dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@bounded_query_recode)
    (type_of% (realize signature actual.readout actual.anchor)) Type Unit where
  unitName := `D5.S3.Arith.FibonacciAtomic.Observer.FiniteMenu.NativeStationaryIntervalResources.bounded_query_recode.__information_unit
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.FiniteMenu.NativeStationaryIntervalResources.Recode.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.FiniteMenu.NativeStationaryIntervalResources
    definition := none
    coordinates := #[5]
    readouts := #[{
      path := #["body","body","body","arg","body","arg","body","arg","body","body","arg","arg"],
      stateBinder := 0, functionOperand := false,
      stateOperand := some #["fn","arg"], booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Recode

namespace Joint
abbrev signature : Signature where
  Params := Unit
  State _ := Dialogue Nat
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Nat
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature (fun _ _ e => wordBound e)
  (fun e => nomatch e)
def bad : Realization signature := realize signature (fun _ _ _ => 1) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (L U : Nat), L ≤ U →
    (∀ k d, (∃ (C : Type) (δ : C → Op C Nat) (c : C),
      Stationary δ ∧ SerialBudgets δ c L U k d) ↔
      minimumCalls L U ≤ k ∧ (L = U ∨ U ≤ 2*d+2)) ∧
    (∃ e : Dialogue Nat, Identifies e L U (minimumCalls L U) ∧
      R.readout () () e ≤ if L = U then 0 else (U-1)/2)
private theorem bad_law : ¬ arena.Law bad := by
  intro h
  obtain ⟨e,_,impossible⟩ := (h 0 0 le_rfl).2
  exact (by decide : ¬ (1 : Nat) ≤ 0) impossible
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  exact ⟨(),.stop 0,.read [true] (.stop 0) (.stop 0) (.stop 0) (.stop 0),by change (0 : Nat) ≠ 1; decide⟩
def family : Registration arena (type_of% (@native_interval_joint_optimum)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨native_interval_joint_optimum,bad,bad_law⟩
  sensitivity := ⟨fun i => ⟨bad,fun j h => (h (Subsingleton.elim j i)).elim,rfl,bad_law⟩,
    fun e => nomatch e⟩
  dependence := dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@native_interval_joint_optimum)
    (type_of% (realize signature actual.readout actual.anchor)) Type Unit where
  unitName := `D5.S3.Arith.FibonacciAtomic.Observer.FiniteMenu.NativeStationaryIntervalResources.native_interval_joint_optimum.__information_unit
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.FiniteMenu.NativeStationaryIntervalResources.Joint.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.FiniteMenu.NativeStationaryIntervalResources
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body","body","body","arg","arg","body","arg","fn","arg"],
      stateBinder := 0, functionOperand := false,
      stateOperand := some #["arg"], booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Joint

end Reg.D5.S3.Arith.FibonacciAtomic.Observer.FiniteMenu.NativeStationaryIntervalResources
