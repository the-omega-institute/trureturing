import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Algebra.Comparison.LowDimensionInvariantMetric
import Reg.Support.DependentFamily
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Algebra.Field.ULift

/-! Source-bound audits of the two theorems on Lie algebras with an invariant form in
dimension at most three. -/

namespace Reg.D5.S3.Quantum.Algebra.Comparison.LowDimensionInvariantMetric

open _root_.D5.S3.Quantum.Algebra.Comparison.LowDimensionInvariantMetric
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Module

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.longLine false
noncomputable section
universe u v

/-! ## The two-dimensional non-abelian Lie algebra over the rationals

On `ℚ²` the bracket `⁅x, y⁆ = (0, x₀ y₁ - y₀ x₁)` gives `⁅e₀, e₁⁆ = e₁`. Both the scalars and
the carrier are lifted so that the model lives in arbitrary universes. -/

/-- Rational scalars in universe `u`. -/
abbrev Q := ULift.{u} ℚ

/-- The carrier `ℚ²` in universe `v`. -/
abbrev Two := ULift.{v} (Fin 2 → ℚ)

instance twoLieRing : LieRing Two.{v} where
  bracket x y := ⟨![0, x.down 0 * y.down 1 - y.down 0 * x.down 1]⟩
  add_lie x y z := by
    ext1; funext i; fin_cases i <;> simp
    ring
  lie_add x y z := by
    ext1; funext i; fin_cases i <;> simp
    ring
  lie_self x := by
    ext1; funext i; fin_cases i <;> simp
  leibniz_lie x y z := by
    ext1; funext i; fin_cases i <;> simp
    ring

theorem two_bracket (x y : Two.{v}) :
    (⁅x, y⁆ : Two.{v}) = ⟨![0, x.down 0 * y.down 1 - y.down 0 * x.down 1]⟩ := rfl

instance twoLieAlgebra : LieAlgebra Q.{u} Two.{v} where
  lie_smul c x y := by
    ext1; funext i; fin_cases i <;> simp [two_bracket, ULift.smul_def]
    ring

/-- Coordinates of `ℚ²` over the lifted rationals. -/
def twoCoord : Two.{v} ≃ₗ[Q.{u}] (Fin 2 → Q.{u}) where
  toFun x i := ⟨x.down i⟩
  invFun f := ⟨fun i => (f i).down⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

instance twoFinite : FiniteDimensional Q.{u} Two.{v} :=
  Module.Finite.equiv twoCoord.{u, v}.symm

theorem two_finrank : finrank Q.{u} Two.{v} ≤ 2 := by
  rw [twoCoord.{u, v}.finrank_eq, Module.finrank_fin_fun]

theorem two_nonabelian : ¬ IsLieAbelian Two.{v} := by
  intro h
  have h1 := h.trivial (⟨![1, 0]⟩ : Two.{v}) ⟨![0, 1]⟩
  rw [two_bracket] at h1
  have h2 := congrArg (fun z : Two.{v} => z.down 1) h1
  simp at h2

/-- The standard dot product of the coordinates. -/
def twoDot : LinearMap.BilinForm Q.{u} Two.{v} :=
  (dotProductBilin Q.{u} Q.{u}).compl₁₂ twoCoord.toLinearMap twoCoord.toLinearMap

theorem twoDot_separating : LinearMap.SeparatingLeft twoDot.{u, v} := by
  intro x hx
  have hc : twoCoord.{u, v} x = 0 := by
    funext i
    have h := hx (twoCoord.{u, v}.symm (Pi.single i 1))
    simpa [twoDot, dotProduct_single] using h
  simpa using hc

theorem zero_not_separating : ¬ LinearMap.SeparatingLeft (0 : LinearMap.BilinForm Q.{u} Two.{v}) := by
  intro h
  have h1 := h (⟨![1, 0]⟩ : Two.{v}) (fun y => by simp)
  have h2 := congrArg (fun z : Two.{v} => z.down 0) h1
  simp at h2

/-! ## The cross-product Lie algebra on `ℝ³` -/

/-- The carrier `ℝ³` in universe `u`. -/
abbrev Cross3 := ULift.{u} (Fin 3 → ℝ)

instance crossLieRing : LieRing Cross3.{u} where
  bracket x y := ⟨crossProduct x.down y.down⟩
  add_lie x y z := by ext1; simp
  lie_add x y z := by ext1; simp
  lie_self x := by ext1; simp
  leibniz_lie x y z := by ext1; exact leibniz_cross x.down y.down z.down

instance crossLieAlgebra : LieAlgebra ℝ Cross3.{u} where
  lie_smul c x y := by ext1; exact (crossProduct x.down).map_smul c y.down

theorem cross_bracket (x y : Cross3.{u}) :
    (⁅x, y⁆ : Cross3.{u}) = ⟨crossProduct x.down y.down⟩ := rfl

theorem cross_finrank : finrank ℝ Cross3.{u} = 3 := by
  rw [finrank_ulift, Module.finrank_fin_fun]

theorem cross_nonabelian : ¬ IsLieAbelian Cross3.{u} := by
  intro h
  have h1 := h.trivial (⟨![1, 0, 0]⟩ : Cross3.{u}) ⟨![0, 1, 0]⟩
  rw [cross_bracket] at h1
  have h2 := congrArg (fun z : Cross3.{u} => z.down 2) h1
  simp [cross_apply] at h2

/-- The dot product on `ℝ³`. -/
def crossDot : LinearMap.BilinForm ℝ Cross3.{u} :=
  LinearMap.mk₂ ℝ (fun x y : Cross3.{u} => x.down ⬝ᵥ y.down)
    (fun x y z => add_dotProduct x.down y.down z.down)
    (fun c x y => smul_dotProduct c x.down y.down)
    (fun x y z => dotProduct_add x.down y.down z.down)
    (fun c x y => dotProduct_smul c x.down y.down)

theorem crossDot_apply (x y : Cross3.{u}) :
    crossDot x y = x.down 0 * y.down 0 + x.down 1 * y.down 1 + x.down 2 * y.down 2 := by
  simp [crossDot, dotProduct, Fin.sum_univ_three]

theorem crossDot_invariant : crossDot.{u}.lieInvariant Cross3.{u} := by
  intro x y z
  simp only [crossDot_apply, cross_bracket, cross_apply]
  simp
  ring

theorem crossDot_pos (x : Cross3.{u}) (hx : x ≠ 0) : 0 < crossDot x x := by
  rw [crossDot_apply]
  by_contra h
  apply hx
  have h0 : x.down 0 = 0 := by
    nlinarith [sq_nonneg (x.down 0), sq_nonneg (x.down 1), sq_nonneg (x.down 2)]
  have h1 : x.down 1 = 0 := by
    nlinarith [sq_nonneg (x.down 0), sq_nonneg (x.down 1), sq_nonneg (x.down 2)]
  have h2 : x.down 2 = 0 := by
    nlinarith [sq_nonneg (x.down 0), sq_nonneg (x.down 1), sq_nonneg (x.down 2)]
  ext i
  fin_cases i <;> simp [h0, h1, h2]

/-- The cross-product algebra with the dot product satisfies every hypothesis of
`exists_basis_bracket_eq_smul_cross`. -/
theorem cross_hypotheses :
    crossDot.{u}.lieInvariant Cross3.{u} ∧ (∀ x : Cross3.{u}, x ≠ 0 → 0 < crossDot x x) ∧
      finrank ℝ Cross3.{u} = 3 ∧ ¬ IsLieAbelian Cross3.{u} :=
  ⟨crossDot_invariant, crossDot_pos, cross_finrank, cross_nonabelian⟩

/-! ## `isLieAbelian_of_finrank_le_two`: the form tested for separation -/
namespace Separation

set_option linter.checkUnivs false in
/-- The bilinear forms on `L` over `K`, read without change. -/
abbrev signature : Signature where
  Params := Σ K : Type u, Σ L : Type v, Σ _ : Field K, Σ _ : LieRing L, LieAlgebra K L
  State p := letI := p.2.2.1; letI := p.2.2.2.1; letI := p.2.2.2.2; LinearMap.BilinForm p.1 p.2.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := letI := p.2.2.1; letI := p.2.2.2.1; letI := p.2.2.2.2; LinearMap.BilinForm p.1 p.2.1
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u, v} :=
  realize signature (fun _ _ s => s) (fun e => nomatch e)

/-- Test separation on some separating form, whenever one exists, instead of the invariant
form itself. -/
def rejected : Realization signature.{u, v} := by
  classical
  exact realize signature (fun _ p s => letI := p.2.2.1; letI := p.2.2.2.1; letI := p.2.2.2.2;
    if h : ∃ B : LinearMap.BilinForm p.1 p.2.1, LinearMap.SeparatingLeft B then h.choose else s)
    (fun e => nomatch e)

set_option linter.checkUnivs false in
/-- Retain the complete scalar, carrier, instance, form and hypothesis telescope of
`isLieAbelian_of_finrank_le_two`. -/
abbrev arena : Arena where
  signature := signature.{u, v}
  Law r := ∀ {K : Type u} {L : Type v} [iK : Field K] [iL : LieRing L] [iA : LieAlgebra K L]
    [FiniteDimensional K L] (Φ : LinearMap.BilinForm K L), Φ.lieInvariant L →
    LinearMap.SeparatingLeft (r.readout () ⟨K, L, iK, iL, iA⟩ Φ) → finrank K L ≤ 2 →
    IsLieAbelian L

/-- On the two-dimensional non-abelian algebra the zero form is invariant and some other
form separates, so separating and invariant forms must coincide in the law. -/
theorem rejected_law : ¬ arena.{u, v}.Law rejected := by
  intro h
  have hex : ∃ B : LinearMap.BilinForm Q.{u} Two.{v}, LinearMap.SeparatingLeft B :=
    ⟨twoDot, twoDot_separating⟩
  refine two_nonabelian.{v} (h (K := Q.{u}) (L := Two.{v}) 0 (fun x y z => by simp) ?_
    two_finrank.{u, v})
  simp only [rejected, realize, dite_eq_left hex]
  exact hex.choose_spec

theorem dependence : ObservationalDependence signature.{u, v} actual := by
  intro i
  cases i
  refine ⟨⟨Q.{u}, Two.{v}, inferInstance, inferInstance, inferInstance⟩, twoDot.{u, v}, 0, ?_⟩
  change twoDot.{u, v} ≠ 0
  intro h
  exact zero_not_separating.{u, v} (h ▸ twoDot_separating)

def source_registration :
    Registration arena.{u, v} (type_of% @isLieAbelian_of_finrank_le_two.{u, v}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@isLieAbelian_of_finrank_le_two.{u, v}, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

end Separation

def isLieAbelian_of_finrank_le_two_registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@isLieAbelian_of_finrank_le_two.{u, v}) (Realization Separation.signature.{u, v}) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Algebra.Comparison.LowDimensionInvariantMetric.isLieAbelian_of_finrank_le_two_unit
  realizationName := `Reg.D5.S3.Quantum.Algebra.Comparison.LowDimensionInvariantMetric.Separation.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨Separation.arena.{u, v}⟩
  objectArena := .source ⟨Separation.arena.{u, v}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source Separation.arena.{u, v} ⟨Separation.source_registration.{u, v}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize Separation.signature.{u, v} (fun _ _ s => s) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Algebra.Comparison.LowDimensionInvariantMetric
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "domain", "arg"]
      stateBinder := 6
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

/-! ## `exists_basis_bracket_eq_smul_cross`: the positivity hypothesis, read as the form -/
namespace Positivity

/-- The value `Φ x s` of a form against a fixed first argument. -/
abbrev signature : Signature where
  Params := Σ L : Type u, Σ _ : LieRing L, Σ _ : LieAlgebra ℝ L,
    Σ _ : LinearMap.BilinForm ℝ L, L
  State p := p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ p s => p.2.2.2.1 p.2.2.2.2 s) (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

/-- Retain the complete carrier, instance, form, hypothesis and conclusion telescope of
`exists_basis_bracket_eq_smul_cross`. -/
abbrev arena : Arena where
  signature := signature.{u}
  Law r := ∀ {L : Type u} [iL : LieRing L] [iA : LieAlgebra ℝ L] (Φ : LinearMap.BilinForm ℝ L),
    Φ.lieInvariant L → (∀ x : L, x ≠ 0 → 0 < r.readout () ⟨L, iL, iA, Φ, x⟩ x) →
    finrank ℝ L = 3 → ¬ IsLieAbelian L →
    ∃ (b : Basis (Fin 3) ℝ L) (c : ℝ), 0 < c ∧
      (∀ i j, Φ (b i) (b j) = if i = j then 1 else 0) ∧
      ∀ x y : L, b.equivFun ⁅x, y⁆ = c • crossProduct (b.equivFun x) (b.equivFun y)

theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  obtain ⟨b, -, -, hON, -⟩ := h (L := Cross3.{u}) 0 (fun x y z => by simp)
    (fun _ _ => (one_pos : (0 : ℝ) < 1)) cross_finrank cross_nonabelian
  have h00 := hON 0 0
  simp at h00

theorem dependence : ObservationalDependence signature.{u} actual := by
  intro i
  cases i
  refine ⟨⟨Cross3.{u}, inferInstance, inferInstance, crossDot.{u}, ⟨![1, 0, 0]⟩⟩,
    ⟨![1, 0, 0]⟩, 0, ?_⟩
  change crossDot.{u} ⟨![1, 0, 0]⟩ ⟨![1, 0, 0]⟩ ≠ crossDot.{u} ⟨![1, 0, 0]⟩ 0
  rw [map_zero, crossDot_apply]
  simp

def source_registration :
    Registration arena.{u} (type_of% @exists_basis_bracket_eq_smul_cross.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@exists_basis_bracket_eq_smul_cross.{u}, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

end Positivity

def exists_basis_bracket_eq_smul_cross_registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@exists_basis_bracket_eq_smul_cross.{u}) (Realization Positivity.signature.{u}) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Algebra.Comparison.LowDimensionInvariantMetric.exists_basis_bracket_eq_smul_cross_unit
  realizationName := `Reg.D5.S3.Quantum.Algebra.Comparison.LowDimensionInvariantMetric.Positivity.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨Positivity.arena.{u}⟩
  objectArena := .source ⟨Positivity.arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source Positivity.arena.{u} ⟨Positivity.source_registration.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize Positivity.signature.{u}
    (fun _ p s => p.2.2.2.1 p.2.2.2.2 s) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Algebra.Comparison.LowDimensionInvariantMetric
    definition := none
    coordinates := #[0, 3, 5]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "domain", "body", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end
end Reg.D5.S3.Quantum.Algebra.Comparison.LowDimensionInvariantMetric
