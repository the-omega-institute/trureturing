import D5.S3.Topology.JBComplexification
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

/-! Exact source applications and the full norm-core and original quadratic source families. Variation,
sensitivity, observational dependence and source-coordinate selection remain
unsupplied; this partial audit asserts no four-slot registration. -/

set_option autoImplicit false
noncomputable section
universe u

namespace Reg.D5.S3.Topology.JBComplexification

open _root_.D5.S3.Topology
open _root_.D5.S3.Topology.JBComplexification
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

abbrev coreScope : Prop := type_of% (@normCore.{u})
abbrev productScope : Prop := type_of% (@squareNorm_mul_le.{u})
abbrev scalarScope : Prop := type_of% (@squareNorm_complex_smul.{u})
abbrev isometryScope : Prop := type_of% (@realEquiv_isometry.{u})

theorem core_actual : coreScope.{u} := @normCore.{u}
theorem product_actual : productScope.{u} := @squareNorm_mul_le.{u}
theorem scalar_actual : scalarScope.{u} := @squareNorm_complex_smul.{u}
theorem isometry_actual : isometryScope.{u} := @realEquiv_isometry.{u}

structure Inputs where
  R : Type u
  [ring : NormedCommRing R]
  [algebra : NormedAlgebra ℝ R]
  laws : SquareLaws R

attribute [instance] Inputs.ring Inputs.algebra

abbrev signature : Signature where
  Params := Inputs.{u}
  State P := Complexification P.R
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ _ z => squareNorm z) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law readout := ∀ P : Inputs.{u},
    letI : Norm (Complexification P.R) := ⟨readout.readout () P⟩
    NormedSpace.Core ℝ (Complexification P.R)

theorem source_bridge : coreScope.{u} ↔ arena.{u}.Law actual.{u} := by
  constructor
  · intro h P
    exact @h P.R P.ring P.algebra P.laws
  · intro h R ring algebra laws
    exact h (@Inputs.mk R ring algebra laws)

theorem actual_positive : arena.{u}.Law actual.{u} := source_bridge.mp core_actual

abbrev inverseScope : Prop := type_of% (@generated_inverse_of_quadratic_bijective.{u})

theorem inverse_actual : inverseScope.{u} := @generated_inverse_of_quadratic_bijective.{u}

structure QuadraticInputs where
  X : Type u
  [normed : NormedAddCommGroup X]
  [space : NormedSpace ℝ X]
  [complete : CompleteSpace X]
  S : X →ₗ[ℝ] X →ₗ[ℝ] X
  unit : X
  laws : JBAlgebra.Data X S unit

attribute [instance] QuadraticInputs.normed QuadraticInputs.space QuadraticInputs.complete

abbrev inverseSignature : Signature where
  Params := QuadraticInputs.{u}
  State P := P.X
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ P := P.X → P.X
  Anchor := Empty
  finiteAnchor := inferInstance

def inverseActual : Realization inverseSignature.{u} :=
  realize inverseSignature (fun _ P a => JBPositiveShift.quadratic P.S a) (fun e => nomatch e)

abbrev inverseArena : Arena where
  signature := inverseSignature.{u}
  Law readout := ∀ (P : QuadraticInputs.{u}) (a : P.X),
    Function.Bijective (readout.readout () P a) →
    ∃ b : P.X, b ∈ JBAlgebra.generated P.S P.unit a ∧ P.S a b = P.unit

theorem inverse_source_bridge : inverseScope.{u} ↔ inverseArena.{u}.Law inverseActual.{u} := by
  constructor
  · intro h P a hQ
    exact @h P.X P.normed P.space P.S P.unit P.complete P.laws a hQ
  · intro h X normed space S unit complete A a hQ
    exact h (@QuadraticInputs.mk X normed space complete S unit A) a hQ

theorem inverse_actual_positive : inverseArena.{u}.Law inverseActual.{u} :=
  inverse_source_bridge.mp inverse_actual

abbrev positivityScope : Prop := type_of% (@quadratic_preserves_squares.{u})

theorem positivity_actual : positivityScope.{u} := @quadratic_preserves_squares.{u}

abbrev positivityArena : Arena where
  signature := inverseSignature.{u}
  Law readout := ∀ (P : QuadraticInputs.{u}) (a x : P.X),
    ∃ y : P.X, readout.readout () P a (P.S x x) = P.S y y

theorem positivity_source_bridge : positivityScope.{u} ↔ positivityArena.{u}.Law inverseActual.{u} := by
  constructor
  · intro h P a x
    exact @h P.X P.normed P.space P.S P.unit P.complete P.laws a x
  · intro h X normed space S unit complete A a x
    exact h (@QuadraticInputs.mk X normed space complete S unit A) a x

theorem positivity_actual_positive : positivityArena.{u}.Law inverseActual.{u} :=
  positivity_source_bridge.mp positivity_actual

section Original

variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]
  {S : X →ₗ[ℝ] X →ₗ[ℝ] X} {unit : X} (A : JBAlgebra.Data X S unit) (a : X)

/-- Exact raw-Data application, with no assumed C* structure. -/
@[instance_reducible]
def original_cstar [CompleteSpace X] : CommCStarAlgebra (GeneratedComplex A a) := inferInstance

theorem original_isometry : Isometry (realEquiv (R := Generated A a)) := realEquiv_isometry

theorem original_norm (z : GeneratedComplex A a) :
    ‖z‖ = Real.sqrt ‖S z.re.val z.re.val + S z.im.val z.im.val‖ := by
  change Real.sqrt ‖z.re ^ 2 + z.im ^ 2‖ = _
  rw [pow_two, pow_two]
  rfl

theorem original_inclusion (r : Generated A a) :
    (realEquiv r : GeneratedComplex A a) = ⟨r, 0⟩ := rfl

theorem original_star (z : GeneratedComplex A a) : star z = ⟨z.re, -z.im⟩ := by
  apply QuadraticAlgebra.ext <;> simp

theorem original_product (z w : GeneratedComplex A a) :
    z * w = ⟨z.re * w.re - z.im * w.im, z.re * w.im + z.im * w.re⟩ := by
  apply QuadraticAlgebra.ext <;> simp [sub_eq_add_neg]

include A in
theorem original_U [CompleteSpace X] (x : X) :
    ∃ y : X, (2 : ℝ) • S a (S a (S x x)) - S (S a a) (S x x) = S y y :=
  quadratic_preserves_squares A a x

end Original
end Reg.D5.S3.Topology.JBComplexification
