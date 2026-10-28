import D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryOperator
import Reg.Support.DependentFamily
import LeanInformationAuditInterface.Contract.Registration

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
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
end Reg.D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryOperator
