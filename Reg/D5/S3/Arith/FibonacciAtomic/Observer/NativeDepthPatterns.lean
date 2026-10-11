import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.FibonacciAtomic.Observer.NativeDepthPatterns
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false

open D5.S3.Arith.FibonacciAtomic.GenealogicalFiberTransport (Source substitution)
open D5.S3.Arith.FibonacciAtomic.ActualTreeReadoutAcquisition (Address Reply readout)
open D5.S3.Arith.FibonacciAtomic.ActualLeafHistoryRigidity (subtree)
open D5.S3.Arith.FibonacciAtomic.Observer.NativeDepthPatterns
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeDepthPatterns

abbrev localitySignature : Signature where
  Params := Nat × Address
  State _ := Source
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Reply
  Anchor := Empty
  finiteAnchor := inferInstance

def localityActual : Realization localitySignature :=
  realize localitySignature (fun _ p u => readout p.2 (substitution^[p.1] u)) (fun e => nomatch e)

def localityBad : Realization localitySignature :=
  realize localitySignature (fun _ _ u => readout [false] u) (fun e => nomatch e)

abbrev localityArena : Arena where
  signature := localitySignature
  Law R := ∀ (n : Nat) (s : Address) (u v : Source),
    (∀ a : Address, a.length ≤ s.length → readout a u = readout a v) →
    R.readout () (n,s) u = R.readout () (n,s) v

private theorem locality_bad : ¬ localityArena.Law localityBad := by
  intro h
  have eq := h 0 [] (.mul (.of true) (.of true)) (.mul (.of false) (.of true)) (by
    intro a ha
    have ae : a = [] := List.length_eq_zero_iff.mp (Nat.le_zero.mp ha)
    subst a; rfl)
  cases eq

def localityProof : Registration localityArena (type_of% (@original_prefix_locality)) where
  actual := localityActual
  bridge := Iff.rfl
  variation := ⟨original_prefix_locality, localityBad, locality_bad⟩
  sensitivity := ⟨fun i => ⟨localityBad,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, locality_bad⟩, fun i => nomatch i⟩
  dependence := by
    intro i
    refine ⟨(0,[]), .of true, .of false, ?_⟩
    intro eq; cases eq

abbrev transportSignature : Signature where
  Params := Nat × Address
  State _ := Source
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Option Source
  Anchor := Empty
  finiteAnchor := inferInstance

def transportActual : Realization transportSignature :=
  realize transportSignature (fun _ p u => subtree p.2 (substitution^[p.1] u)) (fun e => nomatch e)

def transportBad : Realization transportSignature :=
  realize transportSignature (fun _ _ _ => none) (fun e => nomatch e)

abbrev transportArena : Arena where
  signature := transportSignature
  Law R := ∀ (n : Nat) (a : Address) (u t : Source), subtree a u = some t →
    R.readout () (n,a) u = some (substitution^[n] t)

private theorem transport_bad : ¬ transportArena.Law transportBad := by
  intro h
  have eq := h 0 [] (.of true) (.of true) rfl
  cases eq

def transportProof : Registration transportArena (type_of% (@original_present_transport)) where
  actual := transportActual
  bridge := Iff.rfl
  variation := ⟨original_present_transport, transportBad, transport_bad⟩
  sensitivity := ⟨fun i => ⟨transportBad,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, transport_bad⟩, fun i => nomatch i⟩
  dependence := by
    intro i
    refine ⟨(0,[]), .of true, .of false, ?_⟩
    intro eq; cases eq

abbrev frontierSignature : Signature where
  Params := Σ d : Nat, Pattern d
  State p := Frontier p.2 → Source
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Frontier p.2 → Option Source
  Anchor := Empty
  finiteAnchor := inferInstance

def frontierActual : Realization frontierSignature :=
  realize frontierSignature (fun _ p f x => subtree (frontierAddress p.2 x) (fill p.2 f))
    (fun e => nomatch e)

def frontierBad : Realization frontierSignature :=
  realize frontierSignature (fun _ _ _ _ => none) (fun e => nomatch e)

abbrev frontierArena : Arena where
  signature := frontierSignature
  Law R := ∀ (d : Nat) (p : Pattern d),
    (∀ x : Frontier p, (frontierAddress p x).length = d) ∧
    (∀ (f : Frontier p → Source) (x : Frontier p), R.readout () ⟨d,p⟩ f x = some (f x)) ∧
    (∀ (f : Frontier p → Source) (a : Address), a.length = d →
      ((subtree a (fill p f)).isSome ↔ ∃ x : Frontier p, frontierAddress p x = a))

private theorem frontier_bad : ¬ frontierArena.Law frontierBad := by
  intro h
  have eq := (h 0 ()).2.1 (fun _ => .of true) ()
  cases eq

def frontierProof : Registration frontierArena (type_of% (@frontier_geometry)) where
  actual := frontierActual
  bridge := Iff.rfl
  variation := ⟨frontier_geometry, frontierBad, frontier_bad⟩
  sensitivity := ⟨fun i => ⟨frontierBad,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, frontier_bad⟩, fun i => nomatch i⟩
  dependence := by
    intro i
    refine ⟨⟨0,()⟩, (fun _ => .of true), (fun _ => .of false), ?_⟩
    intro eq
    have no := congrFun eq ()
    cases no

noncomputable def original_prefix_locality_registration : LeanInformationAudit.Contract.Registration.{0,1,1,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeDepthPatterns.original_prefix_locality)
    (Realization localitySignature) (Type) Unit where
  unitName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeDepthPatterns.original_prefix_locality
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeDepthPatterns.localityProof
  realizationSource := none
  generated := false
  arena := .source ⟨localityArena⟩
  objectArena := .source ⟨localityArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source localityArena ⟨localityProof⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize localitySignature (fun _ p u => readout p.2 (substitution^[p.1] u)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some Source
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.NativeDepthPatterns
    definition := none
    coordinates := #[0,1]
    readouts := #[{ path := #["body","body","body","body","body","fn","arg"], stateBinder := 2, functionOperand := false, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms localityProof
#print axioms original_prefix_locality_registration

noncomputable def original_present_transport_registration : LeanInformationAudit.Contract.Registration.{0,1,1,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeDepthPatterns.original_present_transport)
    (Realization transportSignature) (Type) Unit where
  unitName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeDepthPatterns.original_present_transport
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeDepthPatterns.transportProof
  realizationSource := none
  generated := false
  arena := .source ⟨transportArena⟩
  objectArena := .source ⟨transportArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source transportArena ⟨transportProof⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize transportSignature (fun _ p u => subtree p.2 (substitution^[p.1] u)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some Source
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.NativeDepthPatterns
    definition := none
    coordinates := #[0,1]
    readouts := #[{ path := #["body","body","body","body","body","fn","arg"], stateBinder := 2, functionOperand := false, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms transportProof
#print axioms original_present_transport_registration

noncomputable def frontier_geometry_registration : LeanInformationAudit.Contract.Registration.{0,1,1,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeDepthPatterns.frontier_geometry)
    (Realization frontierSignature) ((d : Nat) → Pattern d → Type) Unit where
  unitName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeDepthPatterns.frontier_geometry
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeDepthPatterns.frontierProof
  realizationSource := none
  generated := false
  arena := .source ⟨frontierArena⟩
  objectArena := .source ⟨frontierArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source frontierArena ⟨frontierProof⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize frontierSignature (fun _ p f x => subtree (frontierAddress p.2 x) (fill p.2 f)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some (fun d (p : Pattern d) => Frontier p → Source)
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.NativeDepthPatterns
    definition := none
    coordinates := #[0,1]
    readouts := #[{ path := #["body","body","arg","fn","arg","body","body","fn","arg"], stateBinder := 2, functionOperand := false, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms frontierProof
#print axioms frontier_geometry_registration

end Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeDepthPatterns
