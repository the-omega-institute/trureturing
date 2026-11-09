import D5.S3.Topology.JBComplexification
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

/-! Exact source applications and the full norm-core source family. Variation,
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

end Original
end Reg.D5.S3.Topology.JBComplexification
