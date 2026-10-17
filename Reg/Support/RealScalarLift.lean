import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Algebra.Field.ULift
import Mathlib.Analysis.Normed.Operator.NormedSpace

noncomputable section
universe u
namespace Reg.Support.RealScalarLift

instance normedField : NormedField (ULift.{u} ℝ) where
  __ := (inferInstance : Field (ULift.{u} ℝ))
  __ := (inferInstance : MetricSpace (ULift.{u} ℝ))
  norm z := ‖z.down‖
  dist_eq x y := by exact dist_eq_norm_neg_add x.down y.down
  norm_mul x y := norm_mul x.down y.down

instance denselyNormedField : DenselyNormedField (ULift.{u} ℝ) where
  __ := normedField
  lt_norm_lt r s hr hrs := by
    obtain ⟨x, hx, hxs⟩ := DenselyNormedField.lt_norm_lt (α := ℝ) r s hr hrs
    exact ⟨ULift.up x, hx, hxs⟩

instance starRing : StarRing (ULift.{u} ℝ) := starRingOfComm

instance rclike : RCLike (ULift.{u} ℝ) where
  __ := denselyNormedField
  __ := starRing
  __ := (inferInstance : NormedAlgebra ℝ (ULift.{u} ℝ))
  __ := (inferInstance : CompleteSpace (ULift.{u} ℝ))
  re := { toFun := ULift.down, map_zero' := rfl, map_add' := fun _ _ => rfl }
  im := 0
  I := 0
  I_re_ax := rfl
  I_mul_I_ax := Or.inl rfl
  re_add_im_ax z := by ext; simp
  ofReal_re_ax r := rfl
  ofReal_im_ax _ := rfl
  mul_re_ax z w := by simp
  mul_im_ax _ _ := by simp
  conj_re_ax _ := rfl
  conj_im_ax _ := by simp
  conj_I_ax := by simp
  norm_sq_eq_def_ax z := by
    change ‖z.down‖ ^ 2 = z.down * z.down + 0 * 0
    rw [Real.norm_eq_abs, sq_abs]
    ring
  mul_im_I_ax _ := by simp
  toPartialOrder := inferInstance
  le_iff_re_im := by intro z w; simp
  toDecidableEq := Classical.decEq _

universe v

instance realLine : InnerProductSpace (ULift.{u} ℝ) (ULift.{v} ℝ) where
  __ := (inferInstance : Module (ULift.{u} ℝ) (ULift.{v} ℝ))
  norm_smul_le r x := by
    change ‖r.down * x.down‖ ≤ ‖r.down‖ * ‖x.down‖
    exact le_of_eq (norm_mul _ _)
  inner x y := ULift.up (x.down * y.down)
  norm_sq_eq_re_inner x := by
    change ‖x.down‖ ^ 2 = x.down * x.down
    rw [Real.norm_eq_abs, sq_abs, pow_two]
  conj_inner_symm x y := by
    apply ULift.ext
    change y.down * x.down = x.down * y.down
    ring
  add_left x y z := by
    apply ULift.ext
    change (x.down + y.down) * z.down = x.down * z.down + y.down * z.down
    ring
  smul_left x y r := by
    apply ULift.ext
    change (r.down * x.down) * y.down = r.down * (x.down * y.down)
    ring

universe w

def lineIsometry : ULift.{v} ℝ →ₗᵢ[ULift.{u} ℝ] ULift.{w} ℝ where
  toLinearMap := {
    toFun := fun x => ULift.up x.down
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }
  norm_map' _ := rfl

abbrev lineMap : ULift.{v} ℝ →L[ULift.{u} ℝ] ULift.{w} ℝ :=
  lineIsometry.{u,v,w}.toContinuousLinearMap

@[simp] theorem lineMap_norm (x : ULift.{v} ℝ) :
    ‖lineMap.{u,v,w} x‖ = ‖x‖ := rfl

@[simp] theorem norm_lineMap : ‖lineMap.{u,v,w}‖ = 1 :=
  lineIsometry.{u,v,w}.norm_toContinuousLinearMap

end Reg.Support.RealScalarLift
