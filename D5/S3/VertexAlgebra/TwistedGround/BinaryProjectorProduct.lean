/- GID: D5/S3/VertexAlgebra/TwistedGround/BinaryProjectorProduct
   generality: G
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/BinaryProjectorProduct
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A binary character projector is the product of its commuting half-sum involutions. -/

import D5.S3.VertexAlgebra.TwistedGround.BinaryOrbit
import Mathlib.Algebra.MonoidAlgebra.Basic

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.TwistedGround.BinaryProjectorProduct

open LatticeTwistedGroundRealization LatticeTwistedGroundRealization.SignQuotient
open scoped BigOperators

noncomputable section

universe groundUniverse

variable {number : ℕ} {V : Type groundUniverse} [AddCommGroup V] [Module ℂ V]
variable (actions : BinaryOrbit.Actions number V)

def rightHom : Multiplicative (Half number) →* Module.End ℂ V where
  toFun half := actions.right half.toAdd
  map_one' := actions.right_zero
  map_mul' first second := actions.right_add first.toAdd second.toAdd

def rightAlgebra : AddMonoidAlgebra ℂ (Half number) →ₐ[ℂ] Module.End ℂ V :=
  AddMonoidAlgebra.lift ℂ (Module.End ℂ V) (Half number) (rightHom actions)

def algebraFactor (index : Fin number) : AddMonoidAlgebra ℂ (Half number) :=
  (2 : ℂ)⁻¹ • (1 + AddMonoidAlgebra.single (Pi.single index 1) 1)

def projectorFactor (index : Fin number) : Module.End ℂ V :=
  (2 : ℂ)⁻¹ • (1 + actions.right (Pi.single index 1))

theorem factors_commute (first second : Fin number) :
    Commute (projectorFactor actions first) (projectorFactor actions second) := by
  change _ * _ = _ * _
  unfold projectorFactor
  simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
  congr 1
  have commuting : actions.right (Pi.single first 1) * actions.right (Pi.single second 1) =
      actions.right (Pi.single second 1) * actions.right (Pi.single first 1) := by
    rw [← actions.right_add, ← actions.right_add, add_comm]
  simp only [add_mul, mul_add, one_mul, mul_one, commuting]
  abel

theorem algebra_product : (∏ index : Fin number, algebraFactor index) =
    ((2 : ℂ) ^ number)⁻¹ • ∑ half : Half number, AddMonoidAlgebra.single half 1 := by
  classical
  have binary_sum (index : Fin number) :
      (∑ bit : F₂, (AddMonoidAlgebra.single (Pi.single index bit) 1 :
        AddMonoidAlgebra ℂ (Half number))) =
          1 + AddMonoidAlgebra.single (Pi.single index 1) 1 := by
    have finiteUniverse : (Finset.univ : Finset F₂) = {0, 1} := by decide
    rw [finiteUniverse]
    simp [Pi.single_zero, AddMonoidAlgebra.one_def]
  have product_single (half : Half number) :
      (∏ index : Fin number, (AddMonoidAlgebra.single (Pi.single index (half index)) 1 :
        AddMonoidAlgebra ℂ (Half number))) = AddMonoidAlgebra.single half 1 := by
    change (∏ index : Fin number, AddMonoidAlgebra.of ℂ (Half number)
      (Multiplicative.ofAdd (Pi.single index (half index)))) =
        AddMonoidAlgebra.of ℂ (Half number) (Multiplicative.ofAdd half)
    rw [← map_prod, ← ofAdd_sum]
    congr 1
    change (∑ index : Fin number, Pi.single index (half index)) = half
    ext index
    simpa only [Finset.sum_apply] using Fintype.sum_pi_single index half
  unfold algebraFactor
  rw [Finset.prod_smul, Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← inv_pow]
  congr 1
  simp_rw [← binary_sum]
  rw [Fintype.prod_sum]
  simp_rw [product_single]

theorem product_equals_plus :
    Finset.univ.noncommProd (projectorFactor actions)
      (fun first _ second _ _ => factors_commute actions first second) =
        BinaryOrbit.plusProjector actions := by
  classical
  have mapped := congrArg (rightAlgebra actions) (@algebra_product number)
  rw [← Finset.noncommProd_eq_prod, Finset.map_noncommProd] at mapped
  simpa [rightAlgebra, rightHom, algebraFactor, projectorFactor,
    AddMonoidAlgebra.lift_single, map_smul, map_sum,
    BinaryOrbit.plusProjector, BinaryOrbit.characterProjector, dot, sign_zero] using mapped

end

end D5.S3.VertexAlgebra.TwistedGround.BinaryProjectorProduct
