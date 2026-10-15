import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.FibonacciAtomic.Observer.FiniteMenu.NativeLiteralMoore
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace Reg.D5.S3.Arith.FibonacciAtomic.Observer.FiniteMenu.NativeLiteralMoore
open _root_.D5.S3.Arith.FibonacciAtomic.GenealogicalFiberTransport (Source substitution)
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.ActualCutPartitionRecovery
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.FiniteMenu.NativeSharedMooreSynthesis
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.FiniteMenu.NativeLiteralMoore
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open private zero_call_literal from
  D5.S3.Arith.FibonacciAtomic.Observer.FiniteMenu.NativeLiteralMoore
private theorem rootPrefix : CutPrefixFree {[]} := by
  intro a ha b hb _
  have ea : a = [] := by simpa using ha
  have eb : b = [] := by simpa using hb
  exact ea.trans eb.symm
private theorem rootRoot : RootLiteralFeasible
    (canonicalRow {[]} (substitution (.of true))) 1 1 0 0 :=
  zero_call_literal _ 1 1 0 0 ((zero_call_endpoint _ _ _).mpr (by decide +kernel))
private theorem rootNative : NativeLiteralFeasible {[]}
    (canonicalRow {[]} (substitution (.of true))) 1 1 0 0 :=
  (literal_moore_feasibility {[]} rootPrefix (.of true) 1 1 0 0
    (by decide) (by decide)).mpr rootRoot

private theorem rightPrefix : CutPrefixFree {[true]} := by
  intro a ha b hb _
  have ea : a = [true] := by simpa using ha
  have eb : b = [true] := by simpa using hb
  exact ea.trans eb.symm
private theorem rightNative : NativeLiteralFeasible {[true]}
    (canonicalRow {[true]} (substitution (.of false))) 2 2 0 0 :=
  (zero_budget_endpoint {[true]} rightPrefix (.of false) 2 2 0 0
    (by decide) (by decide) (Or.inl rfl)).mpr (by decide +kernel)
private theorem rightNotNative : ¬ NativeLiteralFeasible {[true]}
    (canonicalRow {[true]} (substitution (.of false))) 1 2 0 0 := by
  intro feasible
  have lower := (zero_budget_endpoint {[true]} rightPrefix (.of false) 1 2 0 0
    (by decide) (by decide) (Or.inl rfl)).mp feasible
  exact (by decide +kernel : ¬ targetCount
    (canonicalRow {[true]} (substitution (.of false))) ≤ 1) lower.1

namespace Transfer
abbrev signature : Signature where
  Params := CutSet × Source × Nat × Nat × Nat
  State _ := Nat
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ p r => RootLiteralFeasible (canonicalRow p.1 (substitution p.2.1)) r p.2.2.1 p.2.2.2.1 p.2.2.2.2) (fun e => nomatch e)
def bad : Realization signature := realize signature (fun _ _ _ => False)
  (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ P (_ : CutPrefixFree P) u₀ r K q ell (_ : 1 ≤ r) (_ : 1 ≤ K),
    NativeLiteralFeasible P (canonicalRow P (substitution u₀)) r K q ell ↔
      R.readout () (P,u₀,K,q,ell) r
private theorem bad_law : ¬ arena.Law bad := by
  intro law
  exact (law {[]} rootPrefix (.of true) 1 1 0 0 (by decide) (by decide)).mp rootNative
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨({[true]},.of false,2,0,0),1,2,?_⟩
  intro he
  have good := (literal_moore_feasibility {[true]} rightPrefix (.of false) 2 2 0 0
    (by decide) (by decide)).mp rightNative
  have impossible : RootLiteralFeasible
      (canonicalRow {[true]} (substitution (.of false))) 1 2 0 0 := Eq.mpr he good
  exact rightNotNative ((literal_moore_feasibility {[true]} rightPrefix (.of false)
    1 2 0 0 (by decide) (by decide)).mpr impossible)

def family : Registration arena (type_of% (@literal_moore_feasibility)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨literal_moore_feasibility,bad,bad_law⟩
  sensitivity := ⟨fun i => ⟨bad,fun j h => (h (Subsingleton.elim j i)).elim,rfl,bad_law⟩,
    fun e => nomatch e⟩
  dependence := dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@literal_moore_feasibility) (type_of% (realize signature actual.readout actual.anchor)) Type Unit where
  unitName := `D5.S3.Arith.FibonacciAtomic.Observer.FiniteMenu.NativeLiteralMoore.literal_moore_feasibility.__information_unit
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.FiniteMenu.NativeLiteralMoore.Transfer.family
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
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.FiniteMenu.NativeLiteralMoore
    definition := none
    coordinates := #[0,2,4,5,6]
    readouts := #[{
      path := #["body","body","body","body","body","body","body","body","body","arg"],
      stateBinder := 0, functionOperand := false,
      stateOperand := some #["fn","fn","fn","arg"], booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Transfer

namespace Synthesis
abbrev signature : Signature where
  Params := CutSet × Source × Nat × Nat × Nat
  State _ := Nat
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ p r => (synthesizeLiteral (canonicalRow p.1 (substitution p.2.1)) r p.2.2.1 p.2.2.2.1 p.2.2.2.2).isSome) (fun e => nomatch e)
def bad : Realization signature := realize signature (fun _ _ _ => false)
  (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ P (_ : CutPrefixFree P) u₀ r K q ell (_ : 1 ≤ r) (_ : 1 ≤ K),
    R.readout () (P,u₀,K,q,ell) r = true ↔
      NativeLiteralFeasible P (canonicalRow P (substitution u₀)) r K q ell
private theorem bad_law : ¬ arena.Law bad := by
  intro law
  have no := (law {[]} rootPrefix (.of true) 1 1 0 0 (by decide) (by decide)).mpr rootNative
  cases no
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨({[true]},.of false,2,0,0),1,2,?_⟩
  intro he
  have good := (finite_literal_synthesis {[true]} rightPrefix (.of false) 2 2 0 0
    (by decide) (by decide)).mpr rightNative
  have impossible : (synthesizeLiteral
      (canonicalRow {[true]} (substitution (.of false))) 1 2 0 0).isSome = true := he.trans good
  exact rightNotNative ((finite_literal_synthesis {[true]} rightPrefix (.of false)
    1 2 0 0 (by decide) (by decide)).mp impossible)

def family : Registration arena (type_of% (@finite_literal_synthesis)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨finite_literal_synthesis,bad,bad_law⟩
  sensitivity := ⟨fun i => ⟨bad,fun j h => (h (Subsingleton.elim j i)).elim,rfl,bad_law⟩,
    fun e => nomatch e⟩
  dependence := dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@finite_literal_synthesis) (type_of% (realize signature actual.readout actual.anchor)) Type Unit where
  unitName := `D5.S3.Arith.FibonacciAtomic.Observer.FiniteMenu.NativeLiteralMoore.finite_literal_synthesis.__information_unit
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.FiniteMenu.NativeLiteralMoore.Synthesis.family
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
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.FiniteMenu.NativeLiteralMoore
    definition := none
    coordinates := #[0,2,4,5,6]
    readouts := #[{
      path := #["body","body","body","body","body","body","body","body","body","fn","arg","fn","arg"],
      stateBinder := 0, functionOperand := false,
      stateOperand := some #["arg","fn","fn","fn","arg"], booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Synthesis

namespace Endpoint
abbrev signature : Signature where
  Params := CutSet × Source × Nat × Nat × Nat
  State _ := Nat
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ p r => targetCount (canonicalRow p.1 (substitution p.2.1)) ≤ r ∧
    targetCount (canonicalRow p.1 (substitution p.2.1)) ≤ p.2.2.1) (fun e => nomatch e)
def bad : Realization signature := realize signature (fun _ _ _ => False)
  (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ P (_ : CutPrefixFree P) u₀ r K q ell (_ : 1 ≤ r) (_ : 1 ≤ K)
    (_ : q = 0 ∨ ell = 0),
    NativeLiteralFeasible P (canonicalRow P (substitution u₀)) r K q ell ↔
      R.readout () (P,u₀,K,q,ell) r
private theorem bad_law : ¬ arena.Law bad := by
  intro law
  exact (law {[]} rootPrefix (.of true) 1 1 0 0
    (by decide) (by decide) (Or.inl rfl)).mp rootNative
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  cases i
  refine ⟨({[true]},.of false,2,0,0),1,2,?_⟩
  intro he
  have good : actual.readout () ({[true]},.of false,2,0,0) 2 := by
    change targetCount (canonicalRow {[true]} (substitution (.of false))) ≤ 2 ∧
      targetCount (canonicalRow {[true]} (substitution (.of false))) ≤ 2
    decide +kernel
  have impossible : actual.readout () ({[true]},.of false,2,0,0) 1 := Eq.mpr he good
  change targetCount (canonicalRow {[true]} (substitution (.of false))) ≤ 1 ∧
    targetCount (canonicalRow {[true]} (substitution (.of false))) ≤ 2 at impossible
  exact (by decide +kernel : ¬ targetCount
    (canonicalRow {[true]} (substitution (.of false))) ≤ 1) impossible.1

def family : Registration arena (type_of% (@zero_budget_endpoint)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨zero_budget_endpoint,bad,bad_law⟩
  sensitivity := ⟨fun i => ⟨bad,fun j h => (h (Subsingleton.elim j i)).elim,rfl,bad_law⟩,
    fun e => nomatch e⟩
  dependence := dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@zero_budget_endpoint) (type_of% (realize signature actual.readout actual.anchor)) Type Unit where
  unitName := `D5.S3.Arith.FibonacciAtomic.Observer.FiniteMenu.NativeLiteralMoore.zero_budget_endpoint.__information_unit
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.FiniteMenu.NativeLiteralMoore.Endpoint.family
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
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.FiniteMenu.NativeLiteralMoore
    definition := none
    coordinates := #[0,2,4,5,6]
    readouts := #[{
      path := #["body","body","body","body","body","body","body","body","body","body","arg"],
      stateBinder := 0, functionOperand := false,
      stateOperand := some #["fn","arg","arg"], booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Endpoint
end Reg.D5.S3.Arith.FibonacciAtomic.Observer.FiniteMenu.NativeLiteralMoore
