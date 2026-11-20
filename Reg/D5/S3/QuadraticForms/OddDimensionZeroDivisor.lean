import LeanInformationAuditInterface.Contract.Registration
import D5.S3.QuadraticForms.OddDimensionZeroDivisor
import D5.S3.Geometry.AlgebraicBoundary.TauCeti.FieldTheory.IsRealClosed.Real
import Reg.Support.DependentFamily
import Mathlib.Algebra.Field.ULift
import Mathlib.Algebra.Module.ULift
import Mathlib.Algebra.Order.Ring.InjSurj

/-! Source-bound audits of the eigenvalue of an endomorphism of odd dimension over a real closed
field and of the zero divisors of a bilinear map. The readouts are the eigenvalue and the product
`m a b` of the zero divisor pair. -/

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
  haveI : IsStrictOrderedRing (ULift.{u} ℝ) :=
    Function.Injective.isStrictOrderedRing ULift.down rfl rfl (fun _ _ => rfl) (fun _ _ => rfl)
      Iff.rfl Iff.rfl
  refine IsRealClosed.of_linearOrderedField (fun {x} hx => ?_) (fun {f} hf => ?_)
  · obtain ⟨r, hr⟩ := (IsRealClosed.nonneg_iff_isSquare (R := ℝ)).1 (show (0 : ℝ) ≤ x.down from hx)
    exact ⟨⟨r⟩, ULift.ext _ _ hr⟩
  · let e : ULift.{u} ℝ ≃+* ℝ := ULift.ringEquiv
    obtain ⟨y, hy⟩ := IsRealClosed.exists_isRoot_of_odd_natDegree (f := f.map e.toRingHom)
      (by rwa [Polynomial.natDegree_map_eq_of_injective e.injective])
    refine ⟨e.symm y, ?_⟩
    rw [← Polynomial.isRoot_map_iff (f := e.toRingHom) e.injective]
    simpa using hy

/-- A line over the lifted reals, in another universe. -/
abbrev RLine := ULift.{v} ℝ

/-- The coordinate of the line. -/
def rlineCoord : RLine.{v} ≃ₗ[ULift.{u} ℝ] ULift.{u} ℝ where
  toFun x := ⟨x.down⟩
  invFun y := ⟨y.down⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

instance rlineFinite : FiniteDimensional (ULift.{u} ℝ) RLine.{v} :=
  Module.Finite.equiv rlineCoord.{v, u}.symm

theorem finrank_rline : finrank (ULift.{u} ℝ) RLine.{v} = 1 := by
  rw [rlineCoord.{v, u}.finrank_eq, Module.finrank_self]

/-! ## `exists_hasEigenvalue_of_odd_finrank`: the eigenvalue -/
namespace Eigenvalue

/-- A field: the eigenvalue is a scalar. -/
abbrev signature : Signature where
  Params := Σ K : Type u, Field K
  State p := p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := p.1
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ _ μ => μ) (fun e => nomatch e)

/-- The constant reading `0`. -/
def rejected : Realization signature.{u} :=
  realize signature (fun _ p _ => letI := p.2; (0 : p.1)) (fun e => nomatch e)

/-- Retain the complete scalar, space, instance, endomorphism and parity telescope of
`exists_hasEigenvalue_of_odd_finrank`; only the eigenvalue is read out. -/
abbrev arena : Arena where
  signature := signature.{u}
  Law r := ∀ {K : Type u} {U : Type v} [iK : Field K] [IsRealClosed K] [AddCommGroup U]
    [Module K U] [FiniteDimensional K U] (f : Module.End K U),
    Odd (Module.finrank K U) → ∃ μ : K, f.HasEigenvalue (r.readout () ⟨K, iK⟩ μ)

/-- With the constant reading `0`, the identity of the real line would have the eigenvalue `0`. -/
theorem rejected_law : ¬ arena.{u, v}.Law rejected := by
  intro h
  haveI := isRealClosed_ulift.{u}
  obtain ⟨μ, hμ⟩ := h (K := ULift.{u} ℝ) (U := RLine.{v}) LinearMap.id
    (by rw [finrank_rline]; exact odd_one)
  obtain ⟨x, hx⟩ := hμ.exists_hasEigenvector
  have hx0 := Module.End.mem_eigenspace_iff.1 hx.1
  exact hx.2 (by simpa [rejected, realize] using hx0)

theorem dependence : ObservationalDependence signature.{u} actual := by
  intro i
  cases i
  exact ⟨⟨ULift.{u} ℝ, inferInstance⟩, (0 : ULift.{u} ℝ), (1 : ULift.{u} ℝ), zero_ne_one⟩

/-- The exact statement of the source theorem. -/
abbrev sourceStatement : Prop := type_of% @exists_hasEigenvalue_of_odd_finrank.{u, v}

def source_registration : Registration arena.{u, v} sourceStatement.{u, v} where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@exists_hasEigenvalue_of_odd_finrank.{u, v}, rejected, rejected_law⟩
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

def planeCoord : Plane.{v} ≃ₗ[Q.{u}] (Fin 2 → Q.{u}) where
  toFun x i := ⟨x.down i⟩
  invFun f := ⟨fun i => (f i).down⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

def qlineCoord : QLine.{v} ≃ₗ[Q.{u}] Q.{u} where
  toFun x := ⟨x.down⟩
  invFun y := ⟨y.down⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

instance qlineFinite : FiniteDimensional Q.{u} QLine.{v} :=
  Module.Finite.equiv qlineCoord.{v, u}.symm

theorem finrank_plane : finrank Q.{u} Plane.{v} = 2 := by
  rw [planeCoord.{v, u}.finrank_eq, Module.finrank_fin_fun]

theorem finrank_qline : finrank Q.{u} QLine.{v} = 1 := by
  rw [qlineCoord.{v, u}.finrank_eq, Module.finrank_self]

/-- The product `(a₀ b₀)` of the first coordinates, a nonzero bilinear map `ℚ² × ℚ² → ℚ`. -/
def firstProduct : Plane.{u₂} →ₗ[Q.{u₁}] Plane.{u₃} →ₗ[Q.{u₁}] QLine.{u₄} :=
  ((LinearMap.mul Q.{u₁} Q.{u₁}).compl₁₂
      ((LinearMap.proj 0).comp planeCoord.{u₂, u₁}.toLinearMap)
      ((LinearMap.proj 0).comp planeCoord.{u₃, u₁}.toLinearMap)).compr₂
    qlineCoord.{u₄, u₁}.symm.toLinearMap

theorem firstProduct_apply (a : Plane.{u₂}) (b : Plane.{u₃}) :
    firstProduct.{u₁, u₂, u₃, u₄} a b = ⟨a.down 0 * b.down 0⟩ := rfl

namespace ZeroDivisor

/-- Scalars, the three spaces with their dictionaries, the bilinear map and the first factor. -/
abbrev Params := Σ K : Type u₁, Σ U : Type u₂, Σ V : Type u₃, Σ W : Type u₄,
  Σ _ : Field K, Σ _ : AddCommGroup U, Σ _ : Module K U, Σ _ : AddCommGroup V,
  Σ _ : Module K V, Σ iW : AddCommGroup W, Σ _ : Module K W, Σ _ : U →ₗ[K] V →ₗ[K] W, U

/-- The product `m a b` of the first factor `a` with a second factor `b`. -/
abbrev signature : Signature where
  Params := Params.{u₁, u₂, u₃, u₄}
  State p := p.2.2.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := p.2.2.2.1
  Anchor := Empty
  finiteAnchor := inferInstance

/-- The value `m a b`. -/
def observe (p : Params.{u₁, u₂, u₃, u₄}) (b : p.2.2.1) : p.2.2.2.1 :=
  letI := p.2.2.2.2.1; letI := p.2.2.2.2.2.1; letI := p.2.2.2.2.2.2.1
  letI := p.2.2.2.2.2.2.2.1; letI := p.2.2.2.2.2.2.2.2.1; letI := p.2.2.2.2.2.2.2.2.2.1
  letI := p.2.2.2.2.2.2.2.2.2.2.1
  p.2.2.2.2.2.2.2.2.2.2.2.1 p.2.2.2.2.2.2.2.2.2.2.2.2 b

/-- `0` at the second factor `0`, and a fixed nonzero vector of the target, when there is one,
at every other second factor. -/
def rejectedObserve (p : Params.{u₁, u₂, u₃, u₄}) (b : p.2.2.1) : p.2.2.2.1 := by
  classical
  letI := p.2.2.2.2.2.2.2.1
  letI := p.2.2.2.2.2.2.2.2.2.1
  exact if b = 0 then 0 else if h : ∃ w : p.2.2.2.1, w ≠ 0 then h.choose else 0

def actual : Realization signature.{u₁, u₂, u₃, u₄} :=
  realize signature (fun _ => observe) (fun e => nomatch e)

def rejected : Realization signature.{u₁, u₂, u₃, u₄} :=
  realize signature (fun _ => rejectedObserve) (fun e => nomatch e)

/-- Retain the complete scalar, space, instance, bilinear map and hypothesis telescope of
`exists_zero_divisor`; only the product `m a b` is read out. -/
abbrev arena : Arena where
  signature := signature.{u₁, u₂, u₃, u₄}
  Law r := ∀ {K : Type u₁} {U : Type u₂} {V : Type u₃} {W : Type u₄} [iK : Field K]
    [iU : AddCommGroup U] [mU : Module K U] [iV : AddCommGroup V] [mV : Module K V]
    [iW : AddCommGroup W] [mW : Module K W] [FiniteDimensional K W]
    (m : U →ₗ[K] V →ₗ[K] W),
    (Module.finrank K W = Module.finrank K U →
      ∀ f : Polynomial K, f.natDegree = Module.finrank K U → ∃ x, f.IsRoot x) →
    Module.finrank K W ≤ Module.finrank K U → 2 ≤ Module.finrank K V →
    ∃ a b, a ≠ 0 ∧ b ≠ 0 ∧ r.readout () ⟨K, U, V, W, iK, iU, mU, iV, mV, iW, mW, m, a⟩ b = 0

/-- On `ℚ² × ℚ² → ℚ` with the zero map the rejected reading would make a nonzero vector of the
line vanish. -/
theorem rejected_law : ¬ arena.{u₁, u₂, u₃, u₄}.Law rejected := by
  intro h
  obtain ⟨a, b, -, hb, hab⟩ := h (K := Q.{u₁}) (U := Plane.{u₂}) (V := Plane.{u₃})
    (W := QLine.{u₄}) 0
    (fun hd => absurd hd (by rw [finrank_qline, finrank_plane]; norm_num))
    (by rw [finrank_qline, finrank_plane]; norm_num) (by rw [finrank_plane])
  have hex : ∃ w : QLine.{u₄}, w ≠ 0 := ⟨⟨1⟩, fun h1 => one_ne_zero (congrArg ULift.down h1)⟩
  simp only [rejected, realize, rejectedObserve, if_neg hb, dif_pos hex] at hab
  exact hex.choose_spec hab

theorem dependence : ObservationalDependence signature.{u₁, u₂, u₃, u₄} actual := by
  intro i
  cases i
  refine ⟨⟨Q.{u₁}, Plane.{u₂}, Plane.{u₃}, QLine.{u₄}, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    firstProduct.{u₁, u₂, u₃, u₄}, ⟨![1, 0]⟩⟩, (⟨![1, 0]⟩ : Plane.{u₃}), 0, ?_⟩
  change firstProduct.{u₁, u₂, u₃, u₄} ⟨![1, 0]⟩ ⟨![1, 0]⟩ ≠ firstProduct ⟨![1, 0]⟩ 0
  rw [map_zero, firstProduct_apply]
  intro h1
  have := congrArg ULift.down h1
  norm_num at this

/-- The exact statement of the source theorem. -/
abbrev sourceStatement : Prop := type_of% @exists_zero_divisor.{u₁, u₂, u₃, u₄}

def source_registration : Registration arena.{u₁, u₂, u₃, u₄} sourceStatement.{u₁, u₂, u₃, u₄} where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@exists_zero_divisor.{u₁, u₂, u₃, u₄}, rejected, rejected_law⟩
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
      (Realization ZeroDivisor.signature.{u₁, u₂, u₃, u₄}) Unit Unit := {
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
  readout := some (realize ZeroDivisor.signature.{u₁, u₂, u₃, u₄}
    (fun _ => ZeroDivisor.observe) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.QuadraticForms.OddDimensionZeroDivisor
    definition := none
    coordinates := #[0, 1, 2, 3, 12, 16]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "body", "arg", "body", "arg", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end
end Reg.D5.S3.QuadraticForms.OddDimensionZeroDivisor
