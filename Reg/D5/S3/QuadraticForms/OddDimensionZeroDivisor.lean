import LeanInformationAuditInterface.Contract.Registration
import D5.S3.QuadraticForms.OddDimensionZeroDivisor
import D5.S3.Geometry.AlgebraicBoundary.TauCeti.FieldTheory.IsRealClosed.Real
import Reg.Support.DependentFamily
import Mathlib.Algebra.Field.ULift
import Mathlib.Algebra.Module.ULift
import Mathlib.Algebra.Order.Ring.InjSurj

/-! Source-bound audit of the eigenvalue of an endomorphism of odd dimension over a real closed
field. The readout is the eigenvalue. -/

namespace Reg.D5.S3.QuadraticForms.OddDimensionZeroDivisor

open _root_.D5.S3.QuadraticForms.OddDimensionZeroDivisor
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Module

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.longLine false
noncomputable section
universe u v

/-! ## Real closed scalars in an arbitrary universe -/

/-- The lifted real numbers form a real closed field. -/
theorem isRealClosed_ulift : IsRealClosed (ULift.{u} ℝ) := by
  have : IsStrictOrderedRing (ULift.{u} ℝ) :=
    Function.Injective.isStrictOrderedRing ULift.down rfl rfl (fun _ _ => rfl) (fun _ _ => rfl)
      Iff.rfl Iff.rfl
  refine IsRealClosed.of_linearOrderedField (fun {x} hx => ?_) (fun {f} hf => ?_)
  · obtain ⟨r, hr⟩ := (IsRealClosed.nonneg_iff_isSquare (R := ℝ)).1 (show (0 : ℝ) ≤ x.down from hx)
    exact ⟨⟨r⟩, ULift.ext hr⟩
  · let e : ULift.{u} ℝ ≃+* ℝ := ULift.ringEquiv
    obtain ⟨y, hy⟩ := IsRealClosed.exists_isRoot_of_odd_natDegree (f := f.map e.toRingHom)
      (by rwa [Polynomial.natDegree_map_eq_of_injective e.injective])
    refine ⟨e.symm y, ?_⟩
    rw [← Polynomial.isRoot_map_iff (f := e.toRingHom) e.injective]
    simpa using hy

/-- A line over the lifted reals, in another universe. -/
abbrev RLine := ULift.{v} ℝ

/-- The coordinate of the line. -/
def rlineCoord.{ua, ub} : RLine.{ub} ≃ₗ[ULift.{ua} ℝ] ULift.{ua} ℝ where
  toFun x := ⟨x.down⟩
  invFun y := ⟨y.down⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

theorem rlineFinite.{ua, ub} : FiniteDimensional (ULift.{ua} ℝ) RLine.{ub} :=
  Module.Finite.equiv rlineCoord.{ua, ub}.symm

theorem finrank_rline.{ua, ub} : finrank (ULift.{ua} ℝ) RLine.{ub} = 1 := by
  rw [LinearEquiv.finrank_eq rlineCoord.{ua, ub}, Module.finrank_self]

/-! ## `exists_hasEigenvalue_of_odd_finrank`: the eigenvalue -/
namespace Eigenvalue

/-- The scalars: the eigenvalue is an element of the field. -/
abbrev signature.{uu} : Signature where
  Params := Type uu
  State p := p
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := p
  Anchor := Empty
  finiteAnchor := inferInstance

def actual.{uu} : Realization signature.{uu} :=
  realize signature (fun _ _ μ => μ) (fun e => nomatch e)

/-- A constant reading: one fixed element of the scalars, chosen once the scalars are known to be
nonempty. -/
def rejected.{uu} : Realization signature.{uu} :=
  realize signature (fun _ _ μ => Classical.choice ⟨μ⟩) (fun e => nomatch e)

/-- Retain the complete scalar, space, instance, endomorphism and parity telescope of
`exists_hasEigenvalue_of_odd_finrank`; only the eigenvalue is read out. -/
abbrev arena.{uu, vv} : Arena where
  signature := signature.{uu}
  Law r := ∀ {K : Type uu} {U : Type vv} [Field K] [IsRealClosed K] [AddCommGroup U]
    [Module K U] [FiniteDimensional K U] (f : Module.End K U),
    Odd (Module.finrank K U) → ∃ μ : K, f.HasEigenvalue (r.readout () K μ)

/-- With the constant reading `c`, the endomorphism `(c + 1) • id` of the real line would have the
eigenvalue `c`. -/
theorem rejected_law.{uu, vv} : ¬ arena.{uu, vv}.Law rejected := by
  intro h
  have := isRealClosed_ulift.{uu}
  have : FiniteDimensional (ULift.{uu} ℝ) RLine.{vv} := rlineFinite.{uu, vv}
  let c : ULift.{uu} ℝ := Classical.choice ⟨0⟩
  obtain ⟨μ, hμ⟩ := h (K := ULift.{uu} ℝ) (U := RLine.{vv}) ((c + 1) • LinearMap.id)
    (by rw [finrank_rline.{uu, vv}]; exact odd_one)
  obtain ⟨x, hx⟩ := hμ.exists_hasEigenvector
  have hx0 := Module.End.mem_eigenspace_iff.1 hx.1
  change ((c + 1) • LinearMap.id : Module.End (ULift.{uu} ℝ) RLine.{vv}) x = c • x at hx0
  rw [LinearMap.smul_apply, LinearMap.id_apply, add_smul, one_smul] at hx0
  exact hx.2 (add_left_cancel (hx0.trans (add_zero _).symm))

theorem dependence.{uu} : ObservationalDependence signature.{uu} actual := by
  intro i
  cases i
  refine ⟨ULift.{uu} Bool, ⟨true⟩, ⟨false⟩, fun h => ?_⟩
  change (⟨true⟩ : ULift.{uu} Bool) = ⟨false⟩ at h
  exact absurd (congrArg ULift.down h) (by decide)

/-- The exact statement of the source theorem. -/
abbrev sourceStatement.{uu, vv} : Prop := type_of% @exists_hasEigenvalue_of_odd_finrank.{uu, vv}

def source_registration.{uu, vv} : Registration arena.{uu, vv} sourceStatement.{uu, vv} where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@exists_hasEigenvalue_of_odd_finrank.{uu, vv}, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

end Eigenvalue


def exists_hasEigenvalue_of_odd_finrank_registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@exists_hasEigenvalue_of_odd_finrank.{u, v}) (Realization Eigenvalue.signature.{u}) Unit Unit := {
  unitName := `Reg.D5.S3.QuadraticForms.OddDimensionZeroDivisor.exists_hasEigenvalue_of_odd_finrank_unit
  realizationName := `Reg.D5.S3.QuadraticForms.OddDimensionZeroDivisor.Eigenvalue.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨Eigenvalue.arena.{u, v}⟩
  objectArena := .source ⟨Eigenvalue.arena.{u, v}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source Eigenvalue.arena.{u, v} ⟨Eigenvalue.source_registration.{u, v}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize Eigenvalue.signature.{u} (fun _ _ μ => μ) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.QuadraticForms.OddDimensionZeroDivisor
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "body", "arg"]
      stateBinder := 9
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end
end Reg.D5.S3.QuadraticForms.OddDimensionZeroDivisor
