import D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryFreeRootForm
import Reg.Support.DependentFamily
import LeanInformationAuditInterface.Contract.Registration

/-! Actual covariance, original extension energy and the complete weak graph. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Reg.D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryFreeRootForm

open _root_.D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryFreeRootForm
open _root_.D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryTrace
  (G J M cylinder mass cylinder_mass indicator)
open _root_.D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryCentering (mean Pi C centered_suffix_residual)
open _root_.D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryPathSplit (constG)
open _root_.D5.S3.Arith.FibonacciAtomic.Geometry.FiniteSourceHardy (H Edge)
open _root_.D5.S3.Arith.FibonacciAtomic.Geometry.FiniteSourceMass (a)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open InnerProductSpace MeasureTheory
open scoped ENNReal

private abbrev actualSigma : H →L[ℝ] H :=
  _root_.D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryFreeRootForm.Sigma

private def edge : Edge := ⟨[false], by simp⟩

namespace Covariance
abbrev signature : Signature where
  Params := Unit
  State _ := H
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ z => ‖C z‖ ^ 2) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R :=     IsCompactOperator J ∧ IsCompactOperator C ∧ IsCompactOperator actualSigma ∧
    actualSigma = J.adjoint.comp J - rankOne ℝ v v ∧
    (∀ z w : H, inner ℝ z (actualSigma w) = inner ℝ (C z) (C w)) ∧
    (∀ z : H, inner ℝ z (actualSigma z) = R.readout () () z) ∧
    actualSigma.ker = C.ker ∧
    (∀ p q : Edge,
      inner ℝ (lp.single 2 p (1 : ℝ)) (actualSigma (lp.single 2 q (1 : ℝ))) =
        M.real (cylinder p.val ∩ cylinder q.val)-
          M.real (cylinder p.val)*M.real (cylinder q.val))

def rejected : Realization signature :=
  realize signature (fun _ _ _ => (-1 : ℝ)) (fun e => nomatch e)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := h.2.2.2.2.2.1 0
  change inner ℝ (0 : H) (actualSigma 0) = (-1 : ℝ) at he
  simp only [inner_zero_left] at he
  norm_num at he

def familyRegistration : Registration arena (type_of% actual_compact_covariance) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_compact_covariance, rejected, rejected_law⟩
  sensitivity := ⟨by
    intro i
    refine ⟨rejected, ?_, rfl, rejected_law⟩
    intro j hji
    exact (hji (Subsingleton.elim j i)).elim,
    fun e => nomatch e⟩
  dependence := by
    intro i
    refine ⟨(), (0 : H), lp.single 2 edge (1 : ℝ), ?_⟩
    change ‖C (0 : H)‖ ^ 2 ≠ ‖C (lp.single 2 edge (1 : ℝ))‖ ^ 2
    rw [map_zero,norm_zero,zero_pow (by decide : 2 ≠ 0)]
    have hq := actual_compact_covariance.2.2.2.2.2.1 (lp.single 2 edge (1 : ℝ))
    have he := actual_compact_covariance.2.2.2.2.2.2.2 edge edge
    rw [← hq,he,Set.inter_self]
    simp only [measureReal_def,cylinder_mass,edge,mass,List.map_cons,List.map_nil,
      List.prod_cons,List.prod_nil,Bool.false_eq_true,↓reduceIte,mul_one]
    have hp := _root_.D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryTrace.a_pos
    have hl := _root_.D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryTrace.a_lt_one
    nlinarith

def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@actual_compact_covariance)
    (type_of% (realize signature (fun _ _ z => ‖C z‖ ^ 2) (fun e => nomatch e)))
    Unit Unit := {
  unitName := `Reg.D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryFreeRootForm.Covariance.unit,
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryFreeRootForm.Covariance.familyRegistration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨familyRegistration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature (fun _ _ z => ‖C z‖ ^ 2) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryFreeRootForm,
    definition := none, coordinates := #[],
    readouts := #[{
      path := #["arg", "arg", "arg", "arg", "arg", "fn", "arg", "body", "arg"],
      stateBinder := 0, functionOperand := false, stateOperand := none,
      booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }
end Covariance

namespace Energy
abbrev signature : Signature where
  Params := Unit
  State _ := H
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ z => ‖z‖ ^ 2) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ F : D,
    lift F ∈ K ∧ C (lift F) = Pi F.val ∧
    F.val = constG (mean F.val-mean (J (lift F)))+J (lift F) ∧
    energy F.val = ‖lift F‖^2 ∧
    (∀ (c : ℝ) (z : H), F.val = constG c+J z →
      lift F = K.starProjection z ∧ ‖lift F‖^2 ≤ R.readout () () z) ∧
    (∀ z : H, z ∈ K → C z = Pi F.val → z = lift F)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => (-1 : ℝ)) (fun e => nomatch e)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := ((h ⟨0,D.zero_mem⟩).2.2.2.2.1 0 0 (by simp)).2
  change ‖lift ⟨0,D.zero_mem⟩‖ ^ 2 ≤ (-1 : ℝ) at he
  nlinarith [sq_nonneg ‖lift ⟨0,D.zero_mem⟩‖]

def familyRegistration : Registration arena (type_of% free_root_least_energy) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨free_root_least_energy, rejected, rejected_law⟩
  sensitivity := ⟨by
    intro i
    refine ⟨rejected, ?_, rfl, rejected_law⟩
    intro j hji
    exact (hji (Subsingleton.elim j i)).elim,
    fun e => nomatch e⟩
  dependence := by
    intro i
    refine ⟨(), (0 : H), lp.single 2 edge (1 : ℝ), ?_⟩
    change ‖(0 : H)‖ ^ 2 ≠ ‖(lp.single 2 edge (1 : ℝ) : H)‖ ^ 2
    rw [lp.norm_single (by norm_num : (0 : ℝ≥0∞) < 2)]
    norm_num

def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@free_root_least_energy)
    (type_of% (realize signature (fun _ _ z => ‖z‖ ^ 2) (fun e => nomatch e)))
    Unit Unit := {
  unitName := `Reg.D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryFreeRootForm.Energy.unit,
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryFreeRootForm.Energy.familyRegistration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨familyRegistration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature (fun _ _ z => ‖z‖ ^ 2) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryFreeRootForm,
    definition := none, coordinates := #[],
    readouts := #[{
      path := #["body", "arg", "arg", "arg", "arg", "fn", "arg", "body", "body", "body", "arg", "arg"],
      stateBinder := 2, functionOperand := false, stateOperand := none,
      booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }
end Energy

namespace Graph
abbrev signature : Signature where
  Params := Unit
  State _ := G
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ F => mean F) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R :=     (∀ F : D, form F F = energy F.val) ∧
    (∀ F T : D, form F T = (energy (F+T).val-energy (F-T).val)/4) ∧
    IsClosed {x : G × H | ∃ F : D, x = (F.val,lift F)} ∧
    (∀ x : formSpace, ∃ F : D,
      x.val = (F.val,lift F) ∧ energy F.val = ‖x.val.2‖^2) ∧
    IsCompactOperator formInclusion ∧
    (∀ u h : G, weakGraph u h ↔ R.readout () () h = 0 ∧
      u = constG (mean u)+C (C.adjoint h))

def rejected : Realization signature :=
  realize signature (fun _ _ _ => (1 : ℝ)) (fun e => nomatch e)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hz : weakGraph 0 0 := (free_root_variational_graph.2.2.2.2.2 0 0).mpr
    ⟨by simp,by simp⟩
  have he := ((h.2.2.2.2.2 0 0).mp hz).1
  change (1 : ℝ) = 0 at he
  norm_num at he

def familyRegistration : Registration arena (type_of% free_root_variational_graph) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨free_root_variational_graph, rejected, rejected_law⟩
  sensitivity := ⟨by
    intro i
    refine ⟨rejected, ?_, rfl, rejected_law⟩
    intro j hji
    exact (hji (Subsingleton.elim j i)).elim,
    fun e => nomatch e⟩
  dependence := by
    intro i
    refine ⟨(), constG 0, constG 1, ?_⟩
    change mean (constG 0) ≠ mean (constG 1)
    rw [centered_suffix_residual.2.1,centered_suffix_residual.2.1]
    norm_num

def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@free_root_variational_graph)
    (type_of% (realize signature (fun _ _ F => mean F) (fun e => nomatch e)))
    Unit Unit := {
  unitName := `Reg.D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryFreeRootForm.Graph.unit,
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryFreeRootForm.Graph.familyRegistration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨familyRegistration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature (fun _ _ F => mean F) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryFreeRootForm,
    definition := none, coordinates := #[],
    readouts := #[{
      path := #["arg", "arg", "arg", "arg", "arg", "body", "body", "arg", "fn", "arg", "fn", "arg"],
      stateBinder := 1, functionOperand := false, stateOperand := none,
      booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }
end Graph

namespace MeanIndicator

abbrev signature : Signature where
  Params := Unit
  State _ := Edge
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ p => mean (indicator p)) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ p : Edge, R.readout () () p = M.real (cylinder p.val)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => (-1 : ℝ)) (fun e => nomatch e)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := h edge
  change (-1 : ℝ) = M.real (cylinder edge.val) at he
  have hp : 0 ≤ M.real (cylinder edge.val) := measureReal_nonneg
  linarith

def familyRegistration : Registration arena (type_of% mean_indicator) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨mean_indicator, rejected, rejected_law⟩
  sensitivity := ⟨by
    intro i
    refine ⟨rejected, ?_, rfl, rejected_law⟩
    intro j hji
    exact (hji (Subsingleton.elim j i)).elim,
    fun e => nomatch e⟩
  dependence := by
    intro i
    let longer : Edge := ⟨[false, false], by simp⟩
    refine ⟨(), edge, longer, ?_⟩
    change mean (indicator edge) ≠ mean (indicator longer)
    rw [mean_indicator, mean_indicator]
    simp only [measureReal_def, cylinder_mass]
    simp only [edge, longer, mass, List.map_cons, List.map_nil,
      List.prod_cons, List.prod_nil, Bool.false_eq_true, ↓reduceIte, mul_one]
    have hp := _root_.D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryTrace.a_pos
    have hl := _root_.D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryTrace.a_lt_one
    nlinarith

def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@mean_indicator)
    (type_of% (realize signature (fun _ _ p => mean (indicator p)) (fun e => nomatch e)))
    Unit Unit := {
  unitName := `Reg.D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryFreeRootForm.MeanIndicator.unit,
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryFreeRootForm.MeanIndicator.familyRegistration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨familyRegistration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature (fun _ _ p => mean (indicator p)) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := none,
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

end MeanIndicator

end Reg.D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryFreeRootForm
