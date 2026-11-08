import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Geometry.TwoAxisFiniteRotation

/-! Exact finite-list observations and fixed-output moving-axis observations. -/

noncomputable section

open scoped InnerProductSpace
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Geometry.TwoAxisFiniteRotation

namespace Reg.D5.S3.Geometry.TwoAxisFiniteRotation

private def firstAxis : Space := WithLp.toLp 2 ![1, 0, 0]
private def secondAxis : Space := WithLp.toLp 2 ![0, 1, 0]

private theorem firstAxis_norm : ‖firstAxis‖ = 1 := by
  norm_num [firstAxis, EuclideanSpace.norm_eq, Fin.sum_univ_succ]

private theorem axes_gram :
    ⟪firstAxis, secondAxis⟫_ℝ ^ 2 < ‖firstAxis‖ ^ 2 * ‖secondAxis‖ ^ 2 := by
  norm_num [firstAxis, secondAxis, PiLp.inner_apply, Fin.sum_univ_succ,
    RCLike.inner_apply, EuclideanSpace.norm_eq]

private def halfturn : Orthogonal := (ℝ ∙ secondAxis).reflection

private theorem halfturn_firstAxis : halfturn firstAxis = -firstAxis := by
  apply Submodule.reflection_mem_subspace_orthogonalComplement_eq_neg
  rw [Submodule.mem_orthogonal_singleton_iff_inner_right]
  norm_num [firstAxis, secondAxis, PiLp.inner_apply, Fin.sum_univ_succ,
    RCLike.inner_apply]

namespace Words

abbrev signature : Signature where
  Params := Space × Space × Orthogonal
  State _ := List Orthogonal
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := by
  classical
  exact realize signature (fun _ p l => decide (IsAxisWord p.1 p.2.1 l ∧ l.prod = p.2.2))
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => false) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law O := ∀ (a b : Space),
    ⟪a, b⟫_ℝ ^ 2 < ‖a‖ ^ 2 * ‖b‖ ^ 2 →
    ∀ (R : Orthogonal), determinant R = 1 →
      ∃ l : List Orthogonal, O.readout () (a, b, R) l = true

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨l, hl⟩ := h firstAxis secondAxis axes_gram 1 (by change LinearMap.det (1 : Space →ₗ[ℝ] Space) = 1; simp)
  exact Bool.false_ne_true hl

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  have hn : halfturn ≠ 1 := by
    intro heq
    have h := congrArg (fun R : Orthogonal => R firstAxis) heq
    change halfturn firstAxis = firstAxis at h
    rw [halfturn_firstAxis] at h
    have hc := congrArg (fun v : Space => v 0) h
    change (-1 : ℝ) = 1 at hc
    norm_num at hc
  refine ⟨(firstAxis, secondAxis, 1), [], [halfturn], ?_⟩
  intro heq
  have hnil : actual.readout i (firstAxis, secondAxis, 1) [] = true := by
    change decide (IsAxisWord firstAxis secondAxis [] ∧ ([] : List Orthogonal).prod = 1) = true
    simp [IsAxisWord]
  have hsingle : actual.readout i (firstAxis, secondAxis, 1) [halfturn] = true :=
    heq.symm.trans hnil
  have hp : IsAxisWord firstAxis secondAxis [halfturn] ∧ [halfturn].prod = 1 :=
    of_decide_eq_true hsingle
  exact hn (by simpa only [List.prod_singleton] using hp.2)

def family : Registration arena (type_of% (@two_axis_finite_word)) where
  actual := actual
  bridge := by simp only [arena, actual, realize, decide_eq_true_eq]
  variation := ⟨by simpa only [arena, actual, realize, decide_eq_true_eq]
    using two_axis_finite_word, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, rejected_law⟩,
    fun e => nomatch e⟩
  dependence := dependence

def registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@two_axis_finite_word) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Geometry.TwoAxisFiniteRotation.Words.__information_unit
  realizationName := `Reg.D5.S3.Geometry.TwoAxisFiniteRotation.Words.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := by
    classical
    exact some (realize signature
      (fun _ p l => decide (IsAxisWord p.1 p.2.1 l ∧ l.prod = p.2.2)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Geometry.TwoAxisFiniteRotation
    definition := none
    coordinates := #[0, 1, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg", "body"]
      stateBinder := 5
      functionOperand := false
      stateOperand := none
      booleanPredicate := true }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Words

namespace Transport

universe u

structure Parameters where
  Y : Type u
  F : (Space × Space) → Y
  p : Space × Space
  a : Space
  b : Space

abbrev signature : Signature where
  Params := Parameters.{u}
  State _ := Orthogonal
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := p.Y
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ p R => p.F (rotatePair R p.p)) (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ p _ => p.F (0, 0)) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law O := ∀ (Y : Type u) (F : (Space × Space) → Y) (p : Space × Space)
    (a b : Space),
    ⟪a, b⟫_ℝ ^ 2 < ‖a‖ ^ 2 * ‖b‖ ^ 2 →
    (∀ (Q : Orthogonal), determinant Q = 1 → ∀ (T : Orthogonal),
      (T ∈ axisCircle (Q a) ∨ T ∈ axisCircle (Q b)) →
      F (rotatePair T (rotatePair Q p)) = F (rotatePair Q p)) →
    ∀ (R : Orthogonal), determinant R = 1 →
      O.readout () ⟨Y, F, p, a, b⟩ R = F p

private def normParameters : Parameters.{u} where
  Y := ULift.{u} ℝ
  F p := ⟨‖p.1‖⟩
  p := (firstAxis, 0)
  a := firstAxis
  b := secondAxis

private theorem norm_local :
    ∀ (Q : Orthogonal), determinant Q = 1 → ∀ (T : Orthogonal),
      (T ∈ axisCircle (Q normParameters.{u}.a) ∨
        T ∈ axisCircle (Q normParameters.{u}.b)) →
      normParameters.{u}.F (rotatePair T (rotatePair Q normParameters.{u}.p)) =
        normParameters.{u}.F (rotatePair Q normParameters.{u}.p) := by
  intro Q hQ T hT
  change (ULift.up ‖T (Q firstAxis)‖ : ULift.{u} ℝ) = ULift.up ‖Q firstAxis‖
  simp

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have heq := h normParameters.{u}.Y normParameters.{u}.F normParameters.{u}.p
    normParameters.{u}.a normParameters.{u}.b axes_gram norm_local
    1 (by change LinearMap.det (1 : Space →ₗ[ℝ] Space) = 1; simp)
  have hnorm := congrArg ULift.down heq
  change ‖(0 : Space)‖ = ‖firstAxis‖ at hnorm
  exact (zero_ne_one : (0 : ℝ) ≠ 1)
    (by simpa only [norm_zero, firstAxis_norm] using hnorm)

private def coordinateParameters : Parameters.{u} where
  Y := ULift.{u} ℝ
  F p := ⟨p.1 0⟩
  p := (firstAxis, 0)
  a := firstAxis
  b := secondAxis

private theorem dependence : ObservationalDependence signature.{u} actual := by
  intro i
  refine ⟨coordinateParameters, 1, halfturn, ?_⟩
  intro heq
  have h := congrArg ULift.down heq
  change firstAxis 0 = (halfturn firstAxis) 0 at h
  rw [halfturn_firstAxis] at h
  change (1 : ℝ) = -1 at h
  norm_num at h

def family : Registration arena.{u} (type_of% (@moving_axis_invariance.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@moving_axis_invariance.{u}, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, rejected_law⟩,
    fun e => nomatch e⟩
  dependence := dependence

def registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@moving_axis_invariance.{u}) (Realization signature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.Geometry.TwoAxisFiniteRotation.Transport.__information_unit
  realizationName := `Reg.D5.S3.Geometry.TwoAxisFiniteRotation.Transport.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p R => p.F (rotatePair R p.p))
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Geometry.TwoAxisFiniteRotation
    definition := none
    coordinates := #[0, 1, 2, 3, 4]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 7
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Transport

end Reg.D5.S3.Geometry.TwoAxisFiniteRotation
