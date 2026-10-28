import D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryOperator
import Reg.Support.DependentFamily
import Reg.D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryFreeRootForm
import LeanInformationAuditInterface.Contract.Registration

/-! Full original operator, resolvent and eigenspace laws. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
attribute [local instance] Classical.propDecidable
namespace Reg.D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryOperator

open _root_.D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryOperator
open _root_.D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryTrace (G J)
open _root_.D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryStopping (G0)
open _root_.D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryPathSplit (constG)
open _root_.D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryFreeRootForm (D weakGraph)
open _root_.D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryCentering
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open scoped Topology

abbrev signature : Signature where
  Params := Unit
  State _ := G × G
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ x => decide (x ∈ boundaryOperator.graph)) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => false) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R :=
    DenseRange J ∧ DenseRange centeredTrace ∧ ¬ FiniteDimensional ℝ G0 ∧
    Dense (D : Set G) ∧
    Dense (boundaryOperator.domain : Set G) ∧ IsSelfAdjoint boundaryOperator ∧
    (∀ u h : G, R.readout () () (u,h) = true ↔ weakGraph u h) ∧
    (∀ u : G, (u,0) ∈ boundaryOperator.graph ↔ ∃ c : ℝ, u = constG c)

private theorem graph_zero : ((0 : G),0) ∈ boundaryOperator.graph :=
  (actual_self_adjoint_realization.2.2.2.2.2.2.2 0).mpr ⟨0,(map_zero constG).symm⟩

private theorem graph_bad : ¬ ((0 : G),constG 1) ∈ boundaryOperator.graph := by
  intro h
  have hw := (actual_self_adjoint_realization.2.2.2.2.2.2.1 0 (constG 1)).mp h
  have hm := ( _root_.D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryFreeRootForm.free_root_variational_graph.2.2.2.2.2 0 (constG 1)).mp hw |>.1
  rw [centered_suffix_residual.2.1] at hm
  exact one_ne_zero hm

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hw := (actual_self_adjoint_realization.2.2.2.2.2.2.1 0 0).mp graph_zero
  have he := (h.2.2.2.2.2.2.1 (0 : G) 0).mpr hw
  exact Bool.false_ne_true he

def familyRegistration : Registration arena (type_of% actual_self_adjoint_realization) where
  actual := actual
  bridge := by simp only [arena,actual,realize,decide_eq_true_eq]
  variation := ⟨by simpa only [arena,actual,realize,decide_eq_true_eq] using actual_self_adjoint_realization,rejected,rejected_law⟩
  sensitivity := ⟨by
    intro i
    refine ⟨rejected,?_,rfl,rejected_law⟩
    intro j hji
    exact (hji (Subsingleton.elim j i)).elim,
    fun e => nomatch e⟩
  dependence := by
    intro i
    refine ⟨(),(0,0),(0,constG 1),?_⟩
    change decide (((0 : G),0) ∈ boundaryOperator.graph) ≠
      decide (((0 : G),constG 1) ∈ boundaryOperator.graph)
    simp only [decide_eq_true graph_zero,decide_eq_false graph_bad]
    decide

def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@actual_self_adjoint_realization)
    (type_of% (realize signature (fun _ _ x => decide (x ∈ boundaryOperator.graph))
      (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryOperator.actual_self_adjoint_realization.information_unit,
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryOperator.familyRegistration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨familyRegistration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature (fun _ _ x => decide (x ∈ boundaryOperator.graph))
    (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryOperator,
    definition := none, coordinates := #[],
    readouts := #[{
      path := #["arg","arg","arg","arg","arg","arg","fn","arg",
        "body","body","fn","arg"],
      stateBinder := 0, functionOperand := false, stateOperand := some #["arg"],
      booleanPredicate := true }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

#print axioms familyRegistration

namespace Resolvent
abbrev signature : Signature where
  Params := Unit
  State _ := G
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := G
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ f => boundaryResolvent f) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ f => boundaryResolvent f+constG 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := IsCompactOperator boundaryResolvent ∧
    (∀ u h : G, (u,h) ∈ boundaryOperator.graph ↔ R.readout () () (u+h) = u) ∧
    (∀ (lam : ℝ), 0 < lam → ∀ u : G,
      (u,lam • u) ∈ boundaryOperator.graph ↔
        mean u = 0 ∧ boundaryCovariance u = lam⁻¹ • u)

private theorem const_ne_zero : constG 1 ≠ 0 := by
  intro he
  have hh := congrArg mean he
  rw [centered_suffix_residual.2.1,map_zero] at hh
  exact one_ne_zero hh

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := (h.2.1 0 0).mp graph_zero
  change boundaryResolvent (0+0)+constG 1 = 0 at he
  rw [add_zero,map_zero,zero_add] at he
  exact const_ne_zero he

private theorem resolvent_one : boundaryResolvent (constG 1) = constG 1 := by
  have hg := (actual_self_adjoint_realization.2.2.2.2.2.2.2 (constG 1)).mpr ⟨1,rfl⟩
  simpa only [add_zero] using (actual_compact_resolvent.2.1 (constG 1) 0).mp hg

def familyRegistration : Registration arena (type_of% actual_compact_resolvent) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_compact_resolvent,rejected,rejected_law⟩
  sensitivity := ⟨by
    intro i
    refine ⟨rejected,?_,rfl,rejected_law⟩
    intro j hji
    exact (hji (Subsingleton.elim j i)).elim,
    fun e => nomatch e⟩
  dependence := by
    intro i
    refine ⟨(),0,constG 1,?_⟩
    change boundaryResolvent 0 ≠ boundaryResolvent (constG 1)
    rw [map_zero,resolvent_one]
    exact const_ne_zero.symm

def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@actual_compact_resolvent)
    (type_of% (realize signature (fun _ _ f => boundaryResolvent f)
      (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryOperator.actual_compact_resolvent.information_unit,
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryOperator.Resolvent.familyRegistration,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨familyRegistration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature (fun _ _ f => boundaryResolvent f)
    (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryOperator,
    definition := none, coordinates := #[],
    readouts := #[{
      path := #["arg","fn","arg","body","body","arg","fn","arg"],
      stateBinder := 0, functionOperand := false, stateOperand := some #["arg"],
      booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none, options := #[] }
end Resolvent

namespace Eigenspaces
open _root_.D5.S3.Arith.FibonacciAtomic.Geometry.FiniteSourceHardy (H)
open _root_.D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryFreeRootForm (Sigma K)

abbrev signature : Signature where
  Params := Unit
  State _ := H
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := G
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ z => C z) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ z => C z+constG 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (mu : ℝ) (hmu : 0 < mu),
    (∀ z : Module.End.eigenspace Sigma.toLinearMap mu, z.val ∈ K) ∧
    (∀ z : Module.End.eigenspace Sigma.toLinearMap mu,
      (covarianceEigenEquiv mu hmu z).val = R.readout () () z.val) ∧
    (∀ u : boundaryEigenspace mu⁻¹,
      ((covarianceEigenEquiv mu hmu).symm u).val = mu⁻¹ • C.adjoint u.val) ∧
    FiniteDimensional ℝ (boundaryEigenspace mu⁻¹)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := (h 1 (by norm_num)).2.1 0
  change (covarianceEigenEquiv 1 _ 0).val = C 0+constG 1 at he
  rw [map_zero,map_zero,zero_add] at he
  exact Resolvent.const_ne_zero he.symm

def familyRegistration : Registration arena (type_of% actual_covariance_eigenspaces) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_covariance_eigenspaces,rejected,rejected_law⟩
  sensitivity := ⟨by
    intro i
    refine ⟨rejected,?_,rfl,rejected_law⟩
    intro j hji
    exact (hji (Subsingleton.elim j i)).elim,
    fun e => nomatch e⟩
  dependence := by
    intro i
    obtain ⟨p,z,w,hzw⟩ :=
      _root_.Reg.D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryFreeRootForm.Covariance.familyRegistration.dependence ()
    refine ⟨(),z,w,?_⟩
    change C z ≠ C w
    change ‖C z‖^2 ≠ ‖C w‖^2 at hzw
    exact fun he => hzw (congrArg (fun x : G => ‖x‖^2) he)

def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@actual_covariance_eigenspaces)
    (type_of% (realize signature (fun _ _ z => C z) (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryOperator.actual_covariance_eigenspaces.information_unit,
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryOperator.Eigenspaces.familyRegistration,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨familyRegistration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature (fun _ _ z => C z) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryOperator,
    definition := none, coordinates := #[],
    readouts := #[{
      path := #["body","body","arg","fn","arg","body","arg"],
      stateBinder := 0, functionOperand := false, stateOperand := some #["arg"],
      booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none, options := #[] }
end Eigenspaces

#print axioms Resolvent.familyRegistration
#print axioms Eigenspaces.familyRegistration
end Reg.D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryOperator
