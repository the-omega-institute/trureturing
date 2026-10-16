import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Foundation.FiniteTraceDistance
import Reg.Support.DependentFamily
import Mathlib.Algebra.Field.ULift
import Mathlib.Order.ULift

namespace Reg.D5.S3.Quantum.Foundation.FiniteTraceDistance
open _root_.D5.S3.Quantum.Foundation.FiniteTraceDistance
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open scoped BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.checkUnivs false
noncomputable section
universe u_1 u_2

private instance liftedRealNormedField : NormedField (ULift.{u_2} ℝ) :=
  { (inferInstance : NormedCommRing (ULift.{u_2} ℝ)),
    (inferInstance : Field (ULift.{u_2} ℝ)) with
    norm_mul a b := norm_mul a.down b.down }

private instance liftedRealDenselyNormedField : DenselyNormedField (ULift.{u_2} ℝ) where
  toNormedField := liftedRealNormedField
  lt_norm_lt x y hx hxy := by
    obtain ⟨a, ha⟩ := DenselyNormedField.lt_norm_lt (α := ℝ) x y hx hxy
    exact ⟨⟨a⟩, ha⟩

private instance liftedRealStarRing : StarRing (ULift.{u_2} ℝ) where
  star := id
  star_involutive := fun _ => rfl
  star_mul := fun a b => mul_comm a b
  star_add := fun _ _ => rfl

private instance liftedRealRCLike : RCLike (ULift.{u_2} ℝ) where
  toDenselyNormedField := liftedRealDenselyNormedField
  toStarRing := liftedRealStarRing
  toNormedAlgebra := inferInstance
  toCompleteSpace := inferInstance
  re := { toFun := ULift.down, map_zero' := rfl, map_add' := fun _ _ => rfl }
  im := 0
  I := 0
  I_re_ax := rfl
  I_mul_I_ax := Or.inl rfl
  re_add_im_ax := by intro z; change ULift.up z.down + 0 * 0 = z; simp
  ofReal_re_ax := fun _ => rfl
  ofReal_im_ax := fun _ => rfl
  mul_re_ax := by intro z w; change z.down * w.down = z.down * w.down - 0 * 0; ring
  mul_im_ax := by intro z w; change (0 : ℝ) = z.down * 0 + 0 * w.down; ring
  conj_re_ax := fun _ => rfl
  conj_im_ax := by intro z; change (0 : ℝ) = -0; simp
  conj_I_ax := by change (0 : ULift.{u_2} ℝ) = -0; simp
  norm_sq_eq_def_ax := by
    intro z
    change ‖z.down‖ ^ 2 = z.down * z.down + 0 * 0
    rw [Real.norm_eq_abs, sq_abs]
    ring
  mul_im_I_ax := by intro z; change (0 : ℝ) * 0 = 0; simp
  toPartialOrder := inferInstance
  le_iff_re_im := by
    intro z w
    change z.down ≤ w.down ↔ z.down ≤ w.down ∧ (0 : ℝ) = 0
    simp
  toDecidableEq := Classical.decEq _

/-- Evaluate the source trace map at the Hermitian matrix. -/
abbrev signature : Signature where
  Params := Σ n : Type u_1, Σ R : Type u_2, Matrix n n R
  State p := Matrix p.1 p.1 p.2.1 → p.2.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := p.2.1
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p trace => trace p.2.2) (fun e => Empty.elim e)

/-- Repeat a single row; empty matrix domains retain their unique matrix. -/
def rejected : Realization signature :=
  realize signature
    (fun _ p trace => trace (fun i j => p.2.2 (Classical.choice (⟨i⟩ : Nonempty p.1)) j))
    (fun e => Empty.elim e)

abbrev arena : Arena where
  signature := signature
  Law r := ∀ {n : Type u_1} {R : Type u_2} [Fintype n] [RCLike R]
    {A : Matrix n n R}, A.IsHermitian →
      (RCLike.re A.trace : R) = r.readout () ⟨n, ⟨R, A⟩⟩ Matrix.trace

theorem rejected_law : ¬ arena.{u_1,u_2}.Law rejected := by
  intro h
  let n := ULift.{u_1} Bool
  let R := ULift.{u_2} ℝ
  have he := h (n := n) (R := R) (A := 1) Matrix.isHermitian_one
  have hr : rejected.readout () ⟨n, ⟨R, (1 : Matrix n n R)⟩⟩ Matrix.trace = 1 := by
    classical
    have hn : Nonempty n := inferInstance
    change (∑ i, (1 : Matrix n n R) (Classical.choice hn) i) = 1
    simp only [Matrix.one_apply]
    exact Fintype.sum_ite_eq (Classical.choice hn) (fun _ => (1 : R))
  rw [hr] at he
  have hd := congrArg ULift.down he
  norm_num [Matrix.trace, n] at hd
  change (2 : ℝ) = 1 at hd
  norm_num at hd

def source_registration : Registration arena.{u_1,u_2}
    (type_of% @re_trace_eq_trace.{u_1,u_2}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨re_trace_eq_trace, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨⟨ULift.{u_1} Unit, ⟨ULift.{u_2} Bool, fun _ _ => ⟨false⟩⟩⟩,
      (fun _ => ⟨false⟩), (fun _ => ⟨true⟩), ?_⟩
    intro h
    have he := congrArg ULift.down h
    change false = true at he
    cases he

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Quantum.Foundation.FiniteTraceDistance.re_trace_eq_trace.{u_1,u_2})
      (Realization signature.{u_1,u_2}) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Foundation.FiniteTraceDistance.unit
  realizationName := `Reg.D5.S3.Quantum.Foundation.FiniteTraceDistance.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p trace => trace p.2.2) (fun e => Empty.elim e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Foundation.FiniteTraceDistance
    definition := none
    coordinates := #[0, 1, 4]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.Quantum.Foundation.FiniteTraceDistance
