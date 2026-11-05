import D5.S3.HilbertOperators.WoldDecomposition
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import Reg.Support.RealScalarLift

open _root_.D5.S3.HilbertOperators.WoldDecomposition
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
noncomputable section
universe u v
namespace Reg.D5.S3.HilbertOperators.WoldDecomposition

structure Scope where
  k : Type u
  [scalar : RCLike k]
  H : Type v
  [additive : NormedAddCommGroup H]
  [inner : InnerProductSpace k H]

structure CompleteScope extends Scope.{u,v} where
  [complete : CompleteSpace H]

namespace Finite
abbrev signature : Signature where
  Params := CompleteScope.{u,v}
  State p := p.H
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := p.H → p.H
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u,v} :=
  realize signature (fun _ p x y => by letI := p.additive; exact x + y) (fun e => nomatch e)
def rejected : Realization signature.{u,v} :=
  realize signature (fun _ p _ _ => by letI := p.additive; exact (0 : p.H)) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature.{u,v}
  Law R := ∀ {k : Type u} [RCLike k] {H : Type v} [NormedAddCommGroup H]
    [InnerProductSpace k H] [CompleteSpace H] (V : H →ₗᵢ[k] H) (x : H) (n : ℕ),
    ∃ w : ℕ → H, ∃ y : H, (∀ j, w j ∈ wanderingSub V) ∧ (∀ j ≥ n, w j = 0) ∧
      x = R.readout () ⟨⟨k, H⟩⟩ (∑ j ∈ Finset.range n, (V ^ j) (w j)) ((V ^ n) y) ∧
      ‖x‖ ^ 2 = (∑ j ∈ Finset.range n, ‖w j‖ ^ 2) + ‖y‖ ^ 2
private theorem rejected_law : ¬ arena.{u,v}.Law rejected := by
  intro h
  obtain ⟨w, y, hw, hs, hx, hn⟩ := h (k := ULift.{u} ℝ) (H := ULift.{v} ℝ)
    (LinearIsometry.id : ULift.{v} ℝ →ₗᵢ[ULift.{u} ℝ] ULift.{v} ℝ) (ULift.up 1) 0
  have hz : (ULift.up 1 : ULift.{v} ℝ) = 0 := hx
  exact one_ne_zero (congrArg ULift.down hz)
private theorem dependence : ObservationalDependence signature.{u,v} actual := by
  intro i
  let p : CompleteScope.{u,v} := ⟨⟨ULift.{u} ℝ, ULift.{v} ℝ⟩⟩
  refine ⟨p, 0, ULift.up 1, ?_⟩
  intro h
  have hz := congrArg (fun f : ULift.{v} ℝ → ULift.{v} ℝ => (f 0).down) h
  have hz' : (0 : ℝ) = 1 := by simpa [actual, realize, p] using hz
  exact zero_ne_one hz'

def family : Registration arena.{u,v} (type_of% (@exists_wold_decomposition.{u,v})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@exists_wold_decomposition.{u,v}, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, rejected_law⟩,
    fun e => nomatch e⟩
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@exists_wold_decomposition.{u,v}) (Realization signature.{u,v}) Unit Unit where
  unitName := `Reg.D5.S3.HilbertOperators.WoldDecomposition.Finite.unit
  realizationName := `Reg.D5.S3.HilbertOperators.WoldDecomposition.Finite.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p x y => by letI := p.additive; exact x + y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.HilbertOperators.WoldDecomposition
    definition := none
    coordinates := #[0,2]
    readouts := #[{
      path := #["body","body","body","body","body","body","body","body","body",
        "arg","body","arg","body","arg","arg","fn","arg","arg","fn","fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Finite

namespace Norm
abbrev signature : Signature where
  Params := Scope.{u,v}
  State p := p.H
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u,v} :=
  realize signature (fun _ p x => by letI := p.additive; exact ‖x‖) (fun e => nomatch e)
def rejected : Realization signature.{u,v} :=
  realize signature (fun _ _ _ => (1 : ℝ)) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature.{u,v}
  Law R := ∀ {k : Type u} [RCLike k] {H : Type v} [NormedAddCommGroup H]
    [InnerProductSpace k H] (V : H →ₗᵢ[k] H) (n : ℕ) (w : ℕ → H)
    (hw : ∀ j, w j ∈ wanderingSub V) (y : H) (x : H)
    (hx : x = (∑ j ∈ Finset.range n, (V ^ j) (w j)) + (V ^ n) y),
    (R.readout () ⟨k, H⟩ x) ^ 2 = (∑ j ∈ Finset.range n, ‖w j‖ ^ 2) + ‖y‖ ^ 2
private theorem rejected_law : ¬ arena.{u,v}.Law rejected := by
  intro h
  have hz := h (k := ULift.{u} ℝ) (H := ULift.{v} ℝ)
    (LinearIsometry.id : ULift.{v} ℝ →ₗᵢ[ULift.{u} ℝ] ULift.{v} ℝ) 0 (fun _ => 0) (fun _ => zero_mem _) 0 0 (by simp)
  norm_num [rejected, realize] at hz
private theorem dependence : ObservationalDependence signature.{u,v} actual := by
  intro i
  let p : Scope.{u,v} := ⟨ULift.{u} ℝ, ULift.{v} ℝ⟩
  refine ⟨p, 0, ULift.up 1, ?_⟩
  intro h
  have hz : ‖(0 : ℝ)‖ = ‖(1 : ℝ)‖ := h
  norm_num at hz

def family : Registration arena.{u,v} (type_of% (@wold_norm_sq.{u,v})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@wold_norm_sq.{u,v}, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, rejected_law⟩,
    fun e => nomatch e⟩
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@wold_norm_sq.{u,v}) (Realization signature.{u,v}) Unit Unit where
  unitName := `Reg.D5.S3.HilbertOperators.WoldDecomposition.Norm.unit
  realizationName := `Reg.D5.S3.HilbertOperators.WoldDecomposition.Norm.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p x => by letI := p.additive; exact ‖x‖) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.HilbertOperators.WoldDecomposition
    definition := none
    coordinates := #[0,2]
    readouts := #[{
      path := #["body","body","body","body","body","body","body","body","body","body","body","body",
        "fn","arg","fn","arg","fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Norm
#print axioms Finite.family
#print axioms Norm.family
end Reg.D5.S3.HilbertOperators.WoldDecomposition
