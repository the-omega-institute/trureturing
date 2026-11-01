import D5.S3.HilbertOperators.AlternatingProjectionStrong
import Mathlib.Algebra.Field.ULift
import Reg.Support.DependentFamily
import Reg.Support.SourceSelection
import LeanInformationAuditInterface.Contract.Registration

/-! Full-telescope observation of the actual alternating-projection orbit. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u v
namespace Reg.D5.S3.HilbertOperators.AlternatingProjectionStrong
open Filter
open scoped Topology
open _root_.D5.S3.HilbertOperators.AlternatingProjectionStrong
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

structure Parameters where
  k : Type u
  [scalar : RCLike k]
  H : Type v
  [additive : NormedAddCommGroup H]
  [inner : InnerProductSpace k H]
  [complete : CompleteSpace H]
  U : ClosedSubmodule k H
  V : ClosedSubmodule k H


abbrev signature : Signature where
  Params := Parameters.{u,v}
  State p := p.H
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := ℕ → p.H
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u,v} :=
  realize signature
    (fun _ p => by
      letI := p.scalar
      letI := p.additive
      letI := p.inner
      letI := p.complete
      exact fun x n => ((p.U.toSubmodule.starProjection ∘L p.V.toSubmodule.starProjection) ^ n) x)
    (fun e => nomatch e)

def rejected : Realization signature.{u,v} :=
  realize signature (fun _ _ x _ => x) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u,v}
  Law R := ∀ {k : Type u} [RCLike k] {H : Type v} [NormedAddCommGroup H]
    [InnerProductSpace k H] [CompleteSpace H] (U V : ClosedSubmodule k H) (x : H),
    Tendsto (R.readout () (@Parameters.mk k inferInstance H inferInstance inferInstance inferInstance U V) x)
      atTop (𝓝 ((U ⊓ V).toSubmodule.starProjection x))

private theorem actual_law : arena.{u,v}.Law actual :=
  @tendsto_alternating_projection_pow.{u,v}


local instance realLiftNormedField : NormedField (ULift.{u} ℝ) :=
  NormedField.induced (ULift.{u} ℝ) ℝ (ULift.ringEquiv : ULift.{u} ℝ ≃+* ℝ) ULift.down_injective
local instance realLiftDenselyNormedField : DenselyNormedField (ULift.{u} ℝ) where
  lt_norm_lt x y hx hxy := by
    obtain ⟨a, ha, hb⟩ := DenselyNormedField.lt_norm_lt x y hx hxy (α := ℝ)
    exact ⟨ULift.up a, ha, hb⟩
local instance realLiftStarRing : StarRing (ULift.{u} ℝ) := starRingOfComm
local instance realLiftRCLike : RCLike (ULift.{u} ℝ) where
  __ := realLiftDenselyNormedField
  __ := realLiftStarRing
  __ := (inferInstance : NormedAlgebra ℝ (ULift.{u} ℝ))
  __ := (inferInstance : CompleteSpace (ULift.{u} ℝ))
  re := (ULift.ringEquiv : ULift.{u} ℝ ≃+* ℝ).toAddEquiv.toAddMonoidHom
  im := 0
  I := 0
  I_re_ax := rfl
  I_mul_I_ax := Or.inl rfl
  re_add_im_ax z := by
    ext
    change z.down + 0 * 0 = z.down
    simp
  ofReal_re_ax r := by rfl
  ofReal_im_ax r := rfl
  mul_re_ax z w := by simp
  mul_im_ax z w := by simp
  conj_re_ax z := rfl
  conj_im_ax z := by simp
  conj_I_ax := by simp
  norm_sq_eq_def_ax z := by
    change |z.down| ^ 2 = z.down * z.down + 0 * 0
    simp [pow_two]
  mul_im_I_ax z := by simp
  toPartialOrder := inferInstance
  le_iff_re_im := by
    intro z w
    change z.down ≤ w.down ↔ z.down ≤ w.down ∧ (0 : ℝ) = 0
    simp
  toDecidableEq := Classical.decEq _

local instance realLiftNormedSpace : NormedSpace (ULift.{u} ℝ) (ULift.{v} ℝ) where
  norm_smul_le a x := by
    change |a.down * x.down| ≤ |a.down| * |x.down|
    exact le_of_eq (abs_mul _ _)
local instance realLiftInner : InnerProductSpace (ULift.{u} ℝ) (ULift.{v} ℝ) where
  inner x y := ULift.up (x.down * y.down)
  norm_sq_eq_re_inner x := by
    change |x.down| ^ 2 = x.down * x.down
    simp [pow_two]
  conj_inner_symm x y := by
    change ULift.up (y.down * x.down) = ULift.up (x.down * y.down)
    rw [mul_comm]
  add_left x y z := by
    change ULift.up ((x.down + y.down) * z.down) = ULift.up (x.down * z.down + y.down * z.down)
    rw [add_mul]
  smul_left x y z := by
    change ULift.up ((z.down * x.down) * y.down) = ULift.up (z.down * (x.down * y.down))
    rw [mul_assoc]
private theorem rejected_law : ¬ arena.{u,v}.Law rejected := by
  intro h
  have ht := h (k := ULift.{u} ℝ) (H := ULift.{v} ℝ) ⊥ ⊥ (ULift.up 1)
  have hz : (ULift.up 1 : ULift.{v} ℝ) = 0 := by
    simpa [rejected, realize] using ht
  have hreal := congrArg ULift.down hz
  exact one_ne_zero hreal

private theorem dependence : ObservationalDependence signature.{u,v} actual := by
  intro i
  let p : Parameters.{u,v} :=
    @Parameters.mk (ULift.{u} ℝ) inferInstance (ULift.{v} ℝ)
      inferInstance inferInstance inferInstance ⊤ ⊤
  refine ⟨p, 0, ULift.up 1, ?_⟩
  intro h
  have hz := congrArg (fun f : ℕ → ULift.{v} ℝ => (f 0).down) h
  change (0 : ℝ) = 1 at hz
  exact zero_ne_one hz

def familyRegistration : Registration arena.{u,v}
    (type_of% (@tendsto_alternating_projection_pow.{u,v})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, rejected_law⟩,
    fun e => nomatch e⟩
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@tendsto_alternating_projection_pow.{u,v})
      (Realization signature.{u,v}) Unit Unit where
  unitName := `Reg.D5.S3.HilbertOperators.AlternatingProjectionStrong.unit
  realizationName := `Reg.D5.S3.HilbertOperators.AlternatingProjectionStrong.familyRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨familyRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ p => by
      letI := p.scalar
      letI := p.additive
      letI := p.inner
      letI := p.complete
      exact fun x n => ((p.U.toSubmodule.starProjection ∘L p.V.toSubmodule.starProjection) ^ n) x)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.HilbertOperators.AlternatingProjectionStrong
    definition := none
    coordinates := #[0,1,2,3,4,5,6,7]
    readouts := #[{
      path := #["body","body","body","body","body","body","body","body","body",
        "fn","fn","arg"]
      stateBinder := 8
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.HilbertOperators.AlternatingProjectionStrong
