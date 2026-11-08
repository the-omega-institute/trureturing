import D5.S3.Quantum.Algebra.PBWeightedZeroBudget
import Reg.Support.DependentFamily

/-! Source reconstruction for original weighted response compressions.
Whole-family variation, sensitivity and observational dependence remain absent;
these source applications are not a completed registration. -/

set_option autoImplicit false
noncomputable section
universe u v w

namespace Reg.D5.S3.Quantum.Algebra.PBWeightedZeroBudget

open _root_.D5.S3.Quantum.Algebra.PBWeightedZeroBudget
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

structure Inputs where
  E : Type u
  I : Type v
  A : Type w
  [group : AddCommGroup E]
  [space : Module ℝ E]
  [algebra : CStarAlgebra A]
  [order : PartialOrder A]
  [starOrder : StarOrderedRing A]
  S : E →ₗ[ℝ] E →ₗ[ℝ] E
  D : E → E → E
  C : Set E
  evaluation : I → E →ₗ[ℝ] ℝ
  tables : OriginalTables S D C evaluation
  rotation : RotationInvariant D
  inclusion : E →ₗ[ℝ] A
  cone : ∀ x, x ∈ C ↔ 0 ≤ inclusion x
  squares : ∀ x, inclusion (S x x) = inclusion x * inclusion x

attribute [instance] Inputs.group Inputs.space Inputs.algebra Inputs.order Inputs.starOrder

structure State (X : Inputs.{u,v,w}) where
  P : X.E
  F : X.E
  projection : IsStarProjection (X.inclusion P)
  alpha : ℝ
  beta : ℝ
  theta : ℝ
  positive : 0 < alpha
  ordered : alpha ≤ beta
  z : X.A
  kernel : let r := Real.cos theta • (alpha • P) - Real.sin theta • (beta • F)
           let s := Real.sin theta • (alpha • P) + Real.cos theta • (beta • F)
           X.inclusion (X.S r s) * z = 0

abbrev signature : Signature where
  Params := Inputs.{u,v,w}
  State := State
  Role := Fin 3
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ X => X.A
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u,v,w} :=
  realize signature (fun role X s =>
    let T := X.D (s.alpha • s.P) (s.beta • s.F)
    if role = 0 then X.inclusion T
    else if role = 1 then X.inclusion (X.S s.P T)
    else X.inclusion (X.S s.F T)) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u,v,w}
  Law R := ∀ (X : Inputs.{u,v,w}) (s : State X),
    let Q := 1 - X.inclusion s.P
    Q * R.readout 0 X s * Q = 0 ∧
      star s.z * R.readout 1 X s * s.z = 0 ∧
        star s.z * R.readout 2 X s * s.z = 0

abbrev sourceScope : Prop := type_of% (@weighted_compressed_directions.{u,v,w})

theorem source_bridge : sourceScope.{u,v,w} ↔ arena.{u,v,w}.Law actual := by
  constructor
  · intro h X s
    exact h X.tables X.rotation X.inclusion X.cone X.squares
      s.P s.F s.projection s.alpha s.beta s.theta s.positive s.ordered s.z s.kernel
  · intro h E I group space S D C evaluation A algebra order starOrder
      tables rotation inclusion cone squares P F projection alpha beta theta positive ordered z kernel
    exact h ⟨E,I,A,S,D,C,evaluation,tables,rotation,inclusion,cone,squares⟩
      ⟨P,F,projection,alpha,beta,theta,positive,ordered,z,kernel⟩

theorem actual_law : arena.{u,v,w}.Law actual :=
  source_bridge.mp (@weighted_compressed_directions.{u,v,w})

theorem zero_budget_source_application : type_of% (@zero_budget_directions.{u,v}) :=
  @zero_budget_directions.{u,v}

theorem weighted_read_source_application : type_of% (@weighted_rotated_directions.{u,v}) :=
  @weighted_rotated_directions.{u,v}

theorem null_input_source_application : type_of% (@response_compression_of_annihilation.{u,v,w}) :=
  @response_compression_of_annihilation.{u,v,w}

theorem projection_flip_source_application : type_of% (@projection_flip_weighted_compressions.{u,v,w}) :=
  @projection_flip_weighted_compressions.{u,v,w}

end Reg.D5.S3.Quantum.Algebra.PBWeightedZeroBudget
