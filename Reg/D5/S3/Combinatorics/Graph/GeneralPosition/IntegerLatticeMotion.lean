import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Graph.GeneralPosition.IntegerLatticeMotion
import Reg.Support.SingleDependentReadout

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
namespace Reg.D5.S3.Combinatorics.Graph.GeneralPosition.IntegerLatticeMotion
open _root_.D5.S3.Combinatorics.Graph.GeneralPosition.IntegerLatticeMotion
namespace Distance
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature (Σ k : ℕ, Vertex k)
    (fun p => Vertex p.1) (fun _ => ℕ)
def observation : ∀ (_ : Unit) p, signature.State p → ℕ := fun _ p y => l1 p.2 y
def actual : Realization signature := realize signature observation (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ => 1) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ k : ℕ, (lattice k).Connected ∧
    ∀ x y : Vertex k, (lattice k).dist x y = R.readout () ⟨k,x⟩ y
private theorem rejectedLaw : ¬ arena.Law rejected := by
  intro h
  have hh := (h 0).2 (fun j => Fin.elim0 j) (fun j => Fin.elim0 j)
  simpa [rejected, realize] using hh
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨1, fun _ => 0⟩, (fun _ => 0), (fun _ => 1), ?_⟩
  norm_num [actual, observation, realize, l1, Fin.sum_univ_one]
def family : Registration arena (type_of% (@lattice_distance)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨lattice_distance, rejected, rejectedLaw⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejectedLaw
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@D5.S3.Combinatorics.Graph.GeneralPosition.IntegerLatticeMotion.lattice_distance) (Realization signature) Unit Unit where
  unitName := `D5.S3.Combinatorics.Graph.GeneralPosition.IntegerLatticeMotion.lattice_distance.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.GeneralPosition.IntegerLatticeMotion.Distance.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature observation (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.GeneralPosition.IntegerLatticeMotion
    definition := none
    coordinates := #[0,1]
    readouts := #[{
      path := #["body","arg","body","body","arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
#print axioms family
#print axioms audit
end Distance
namespace Geodesic
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature (Σ k : ℕ, Vertex k × Vertex k)
    (fun p => Vertex p.1) (fun _ => Prop)
def observation : ∀ (_ : Unit) p, signature.State p → Prop :=
  fun _ p z => Between p.2.1 p.2.2 z
def actual : Realization signature := realize signature observation (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {k : ℕ} (x y z : Vertex k),
    R.readout () ⟨k,x,y⟩ z ↔
      _root_.D5.S3.Combinatorics.Graph.GeneralPosition.CylinderSevenTen.OnGeodesic (lattice k) x y z
private theorem rejectedLaw : ¬ arena.Law rejected := by
  intro h
  let x : Vertex 0 := fun j => Fin.elim0 j
  exact (h x x x).mpr ((between_iff_geodesic x x x).mp (by intro j; exact Fin.elim0 j))
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨1, (fun _ => 0), (fun _ => 1)⟩, (fun _ => 2), (fun _ => 0), ?_⟩
  simp [actual, observation, realize, Between, Fin.forall_fin_one]
def family : Registration arena (type_of% (@between_iff_geodesic)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@between_iff_geodesic, rejected, rejectedLaw⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejectedLaw
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@D5.S3.Combinatorics.Graph.GeneralPosition.IntegerLatticeMotion.between_iff_geodesic) (Realization signature) Unit Unit where
  unitName := `D5.S3.Combinatorics.Graph.GeneralPosition.IntegerLatticeMotion.between_iff_geodesic.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.GeneralPosition.IntegerLatticeMotion.Geodesic.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature observation (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.GeneralPosition.IntegerLatticeMotion
    definition := none
    coordinates := #[0,1,2]
    readouts := #[{
      path := #["body","body","body","body","fn","arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
#print axioms family
#print axioms audit
end Geodesic
namespace Trace
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature ℕ
    (fun k => Finset (Vertex k)) (fun _ => Prop)
def observation : ∀ (_ : Unit) k, signature.State k → Prop := fun _ _ S => S.Nonempty
def actual : Realization signature := realize signature observation (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ => True) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {k : ℕ}, 1 ≤ k → ∀ S : Finset (Vertex k), R.readout () k S →
    (∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S,
      a ≠ b → b ≠ c → a ≠ c → ¬ Between a b c) →
    ∃ (s : Fin S.card → Vertex k) (p : ℕ → Fin S.card → Vertex k),
      Function.Injective s ∧ Finset.univ.image s = S ∧ ScaledCoveringTrace s p
private theorem rejectedLaw : ¬ arena.Law rejected := by
  intro h
  obtain ⟨s,p,_,_,ht⟩ := h (k := 1) (by decide) ∅ trivial (by simp)
  obtain ⟨i,_⟩ := ht.2.2.2.1 0
  exact Fin.elim0 (by simpa using i)
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨1, ∅, {fun _ => 0}, ?_⟩
  simp [actual, observation, realize]
def family : Registration arena (type_of% (@scaled_finset_trace)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@scaled_finset_trace, rejected, rejectedLaw⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejectedLaw
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@D5.S3.Combinatorics.Graph.GeneralPosition.IntegerLatticeMotion.scaled_finset_trace) (Realization signature) Unit Unit where
  unitName := `D5.S3.Combinatorics.Graph.GeneralPosition.IntegerLatticeMotion.scaled_finset_trace.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.GeneralPosition.IntegerLatticeMotion.Trace.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature observation (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.GeneralPosition.IntegerLatticeMotion
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body","body","body","domain"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
#print axioms family
#print axioms audit
end Trace
end Reg.D5.S3.Combinatorics.Graph.GeneralPosition.IntegerLatticeMotion
