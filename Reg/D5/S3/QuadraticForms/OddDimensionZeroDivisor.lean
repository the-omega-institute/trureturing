import LeanInformationAuditInterface.Contract.Registration
import D5.S3.QuadraticForms.OddDimensionZeroDivisor
import D5.S3.Geometry.AlgebraicBoundary.TauCeti.FieldTheory.IsRealClosed.Real
import Reg.Support.DependentFamily
import Mathlib.Algebra.Field.ULift
import Mathlib.Algebra.Module.ULift
import Mathlib.Algebra.Order.Ring.InjSurj

/-! Source-bound audits of the eigenvalue of an endomorphism of odd dimension over a real closed
field and of the zero divisors of a bilinear map. The readouts are the eigenvalue and the first
factor `a` of the zero divisor pair. -/

namespace Reg.D5.S3.QuadraticForms.OddDimensionZeroDivisor

open _root_.D5.S3.QuadraticForms.OddDimensionZeroDivisor
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Module

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.longLine false
noncomputable section
universe u v u₁ u₂ u₃ u₄

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

/-- A field: the eigenvalue is a scalar. -/
abbrev signature.{uu} : Signature where
  Params := Σ K : Type uu, Field K
  State p := p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := p.1
  Anchor := Empty
  finiteAnchor := inferInstance

def actual.{uu} : Realization signature.{uu} :=
  realize signature (fun _ _ μ => μ) (fun e => nomatch e)

/-- The constant reading `0`. -/
def rejected.{uu} : Realization signature.{uu} :=
  realize signature (fun _ p _ => letI := p.2; (0 : p.1)) (fun e => nomatch e)

/-- Retain the complete scalar, space, instance, endomorphism and parity telescope of
`exists_hasEigenvalue_of_odd_finrank`; only the eigenvalue is read out. -/
abbrev arena.{uu, vv} : Arena where
  signature := signature.{uu}
  Law r := ∀ {K : Type uu} {U : Type vv} [iK : Field K] [IsRealClosed K] [AddCommGroup U]
    [Module K U] [FiniteDimensional K U] (f : Module.End K U),
    Odd (Module.finrank K U) → ∃ μ : K, f.HasEigenvalue (r.readout () ⟨K, iK⟩ μ)

/-- With the constant reading `0`, the identity of the real line would have the eigenvalue `0`. -/
theorem rejected_law.{uu, vv} : ¬ arena.{uu, vv}.Law rejected := by
  intro h
  have := isRealClosed_ulift.{uu}
  have : FiniteDimensional (ULift.{uu} ℝ) RLine.{vv} := rlineFinite.{uu, vv}
  obtain ⟨μ, hμ⟩ := h (K := ULift.{uu} ℝ) (U := RLine.{vv}) LinearMap.id
    (by rw [finrank_rline.{uu, vv}]; exact odd_one)
  obtain ⟨x, hx⟩ := hμ.exists_hasEigenvector
  have hx0 := Module.End.mem_eigenspace_iff.1 hx.1
  exact hx.2 (by simpa [rejected, realize] using hx0)

theorem dependence.{uu} : ObservationalDependence signature.{uu} actual := by
  intro i
  cases i
  exact ⟨⟨ULift.{uu} ℝ, inferInstance⟩, (0 : ULift.{uu} ℝ), (1 : ULift.{uu} ℝ), zero_ne_one⟩

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

/-! ## `exists_zero_divisor`: the product of the zero divisor pair -/

/-- Rational scalars in universe `u`. -/
abbrev Q := ULift.{u} ℚ

/-- The plane `ℚ²` in universe `v`, a vector space over the lifted rationals. -/
abbrev Plane := ULift.{v} (Fin 2 → ℚ)

/-- The line `ℚ` in universe `v`. -/
abbrev QLine := ULift.{v} ℚ

def planeCoord.{ua, ub} : Plane.{ub} ≃ₗ[Q.{ua}] (Fin 2 → Q.{ua}) where
  toFun x i := ⟨x.down i⟩
  invFun f := ⟨fun i => (f i).down⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

def qlineCoord.{ua, ub} : QLine.{ub} ≃ₗ[Q.{ua}] Q.{ua} where
  toFun x := ⟨x.down⟩
  invFun y := ⟨y.down⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

theorem qlineFinite.{ua, ub} : FiniteDimensional Q.{ua} QLine.{ub} :=
  Module.Finite.equiv qlineCoord.{ua, ub}.symm

theorem finrank_plane.{ua, ub} : finrank Q.{ua} Plane.{ub} = 2 := by
  rw [LinearEquiv.finrank_eq planeCoord.{ua, ub}, Module.finrank_fin_fun]

theorem finrank_qline.{ua, ub} : finrank Q.{ua} QLine.{ub} = 1 := by
  rw [LinearEquiv.finrank_eq qlineCoord.{ua, ub}, Module.finrank_self]

namespace ZeroDivisor

/-- The first factor of the zero divisor pair, an element of a commutative group. -/
abbrev signature.{w₂} : Signature where
  Params := Σ U : Type w₂, AddCommGroup U
  State p := p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := p.1
  Anchor := Empty
  finiteAnchor := inferInstance

def actual.{w₂} : Realization signature.{w₂} :=
  realize signature (fun _ _ a => a) (fun e => nomatch e)

/-- The constant reading `0`. -/
def rejected.{w₂} : Realization signature.{w₂} :=
  realize signature (fun _ p _ => letI := p.2; (0 : p.1)) (fun e => nomatch e)

/-- Retain the complete scalar, space, instance, bilinear map and hypothesis telescope of
`exists_zero_divisor`; only the first factor `a` of the zero divisor pair is read out, at its
nonvanishing condition. -/
abbrev arena.{w₁, w₂, w₃, w₄} : Arena where
  signature := signature.{w₂}
  Law r := ∀ {K : Type w₁} {U : Type w₂} {V : Type w₃} {W : Type w₄} [Field K]
    [iU : AddCommGroup U] [Module K U] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    (m : U →ₗ[K] V →ₗ[K] W),
    (Module.finrank K W = Module.finrank K U →
      ∀ f : Polynomial K, f.natDegree = Module.finrank K U → ∃ x, f.IsRoot x) →
    Module.finrank K W ≤ Module.finrank K U → 2 ≤ Module.finrank K V →
    ∃ a b, r.readout () ⟨U, iU⟩ a ≠ 0 ∧ b ≠ 0 ∧ m a b = 0

/-- On `ℚ² × ℚ² → ℚ` with the zero map the rejected reading would require `0 ≠ 0`. -/
theorem rejected_law.{w₁, w₂, w₃, w₄} : ¬ arena.{w₁, w₂, w₃, w₄}.Law rejected := by
  intro h
  have : FiniteDimensional Q.{w₁} QLine.{w₄} := qlineFinite.{w₁, w₄}
  obtain ⟨a, b, ha, -, -⟩ := h (K := Q.{w₁}) (U := Plane.{w₂}) (V := Plane.{w₃})
    (W := QLine.{w₄}) 0
    (fun hd => absurd hd (by rw [finrank_qline.{w₁, w₄}, finrank_plane.{w₁, w₂}]; norm_num))
    (by rw [finrank_qline.{w₁, w₄}, finrank_plane.{w₁, w₂}]; norm_num) (by rw [finrank_plane.{w₁, w₃}])
  exact ha rfl

theorem dependence.{w₂} : ObservationalDependence signature.{w₂} actual := by
  intro i
  cases i
  refine ⟨⟨Plane.{w₂}, inferInstance⟩, (⟨![1, 0]⟩ : Plane.{w₂}), (0 : Plane.{w₂}), fun h => ?_⟩
  change (⟨![1, 0]⟩ : Plane.{w₂}) = 0 at h
  have h0 : (1 : ℚ) = 0 := congrArg (fun z : Plane.{w₂} => z.down 0) h
  exact one_ne_zero h0

/-- The exact statement of the source theorem. -/
abbrev sourceStatement.{w₁, w₂, w₃, w₄} : Prop := type_of% @exists_zero_divisor.{w₁, w₂, w₃, w₄}

def source_registration.{w₁, w₂, w₃, w₄} : Registration arena.{w₁, w₂, w₃, w₄} sourceStatement.{w₁, w₂, w₃, w₄} where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@exists_zero_divisor.{w₁, w₂, w₃, w₄}, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

end ZeroDivisor

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

def exists_zero_divisor_registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@exists_zero_divisor.{u₁, u₂, u₃, u₄})
      (Realization ZeroDivisor.signature.{u₂}) Unit Unit := {
  unitName := `Reg.D5.S3.QuadraticForms.OddDimensionZeroDivisor.exists_zero_divisor_unit
  realizationName := `Reg.D5.S3.QuadraticForms.OddDimensionZeroDivisor.ZeroDivisor.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨ZeroDivisor.arena.{u₁, u₂, u₃, u₄}⟩
  objectArena := .source ⟨ZeroDivisor.arena.{u₁, u₂, u₃, u₄}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source ZeroDivisor.arena.{u₁, u₂, u₃, u₄}
    ⟨ZeroDivisor.source_registration.{u₁, u₂, u₃, u₄}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize ZeroDivisor.signature.{u₂} (fun _ _ a => a) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.QuadraticForms.OddDimensionZeroDivisor
    definition := none
    coordinates := #[1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "body", "arg", "body", "fn", "arg", "fn", "arg"]
      stateBinder := 16
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end
end Reg.D5.S3.QuadraticForms.OddDimensionZeroDivisor
