import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Geometry.NonlinearSkewRigidity

/-! Whole-family observation of the outer application in the square conclusion. -/

noncomputable section
open scoped InnerProductSpace
open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Geometry.NonlinearSkewRigidity

namespace Reg.D5.S3.Geometry.NonlinearSkewRigidity
universe u

abbrev signature : Signature where
  Params := Σ W : Type u, W → W
  State p := p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := p.1
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ p y => p.2 y) (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ y => y) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {W : Type u} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    (r : ℝ), 0 < r → r < 1 → ∀ F : W → W,
    (∀ y, ⟪y, F y⟫_ℝ = 0) → (∀ y, ‖F y‖ = r * ‖y‖) →
    (∀ y z, (⟪y, z⟫_ℝ + ⟪F y, F z⟫_ℝ) *
      (⟪y, F z⟫_ℝ + ⟪F y, z⟫_ℝ) = 0) →
    (∀ y z, F (y + z) = F y + F z) ∧
    (∀ (a : ℝ) y, F (a • y) = a • F y) ∧
    (∀ y z, ⟪F y, z⟫_ℝ = -⟪y, F z⟫_ℝ) ∧
    (∀ y, R.readout () ⟨W, F⟩ (F y) = -(r ^ 2) • y)

private instance liftInner : InnerProductSpace ℝ (ULift.{u} ℂ) where
  __ := (inferInstance : NormedSpace ℝ (ULift.{u} ℂ))
  inner x y := ⟪x.down, y.down⟫_ℝ
  norm_sq_eq_re_inner x := norm_sq_eq_re_inner (𝕜 := ℝ) x.down
  conj_inner_symm x y := InnerProductSpace.conj_inner_symm x.down y.down
  add_left x y z := inner_add_left x.down y.down z.down
  smul_left x y r := inner_smul_left x.down y.down r

private def rotation (z : ULift.{u} ℂ) : ULift.{u} ℂ :=
  ⟨(1 / 2 : ℝ) • (Complex.I * z.down)⟩

private theorem rotation_orth (z : ULift.{u} ℂ) : ⟪z, rotation z⟫_ℝ = 0 := by
  change ⟪z.down, (1 / 2 : ℝ) • (Complex.I * z.down)⟫_ℝ = 0
  simp [Complex.inner, Complex.mul_re, Complex.mul_im]
  <;> ring

private theorem rotation_norm (z : ULift.{u} ℂ) : ‖rotation z‖ = (1 / 2 : ℝ) * ‖z‖ := by
  change ‖(1 / 2 : ℝ) • (Complex.I * z.down)‖ = (1 / 2 : ℝ) * ‖z.down‖
  simp [norm_smul, norm_mul]

private theorem rotation_product (y z : ULift.{u} ℂ) :
    (⟪y, z⟫_ℝ + ⟪rotation y, rotation z⟫_ℝ) *
      (⟪y, rotation z⟫_ℝ + ⟪rotation y, z⟫_ℝ) = 0 := by
  have hs : ⟪y, rotation z⟫_ℝ + ⟪rotation y, z⟫_ℝ = 0 := by
    change ⟪y.down, (1 / 2 : ℝ) • (Complex.I * z.down)⟫_ℝ +
      ⟪(1 / 2 : ℝ) • (Complex.I * y.down), z.down⟫_ℝ = 0
    simp [Complex.inner, Complex.mul_re, Complex.mul_im]
    <;> ring
  rw [hs, mul_zero]

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have hs := (@h (ULift.{u} ℂ) inferInstance inferInstance (1 / 2)
    (by norm_num) (by norm_num) rotation rotation_orth rotation_norm rotation_product).2.2.2
      (ULift.up (1 : ℂ))
  have hi := congrArg (fun z : ULift.{u} ℂ => z.down.im) hs
  norm_num [rejected, realize, rotation] at hi

private theorem dependence : ObservationalDependence signature.{u} actual := by
  intro i
  refine ⟨⟨ULift.{u} ℝ, id⟩, ULift.up 0, ULift.up 1, ?_⟩
  change (ULift.up (0 : ℝ) : ULift.{u} ℝ) ≠ ULift.up 1
  intro h
  have hh := congrArg ULift.down h
  norm_num at hh

def family : Registration arena.{u} (type_of% (@nonlinear_skew_rigidity.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@nonlinear_skew_rigidity, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, rejected_law⟩,
    fun e => nomatch e⟩
  dependence := dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@nonlinear_skew_rigidity.{u}) (Realization signature.{u}) (Type u → Type u) Unit where
  unitName := `Reg.D5.S3.Geometry.NonlinearSkewRigidity.unit
  realizationName := `Reg.D5.S3.Geometry.NonlinearSkewRigidity.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p y => p.2 y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Geometry.NonlinearSkewRigidity
    definition := none
    coordinates := #[0, 6]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "arg", "arg", "arg", "body", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms registration

end Reg.D5.S3.Geometry.NonlinearSkewRigidity
