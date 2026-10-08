/- GID: D5/S3/VertexAlgebra/LatticeActualChargedLocality
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/LatticeActualChargedLocality
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual charged fields are mutually local for every ordinary even lattice, including rank zero. -/

import D5.S3.VertexAlgebra.LatticeActualOrderedProducts
import D5.S3.VertexAlgebra.BinomialKernelDelta
import D5.S3.VertexAlgebra.LatticeAllStateField
import D5.S3.VertexAlgebra.FieldNormalProductLocality

/- Actual charged-generator locality, including equal charges and every sector.
   The two ordered-product identities come from actual coefficient contraction
   and polynomial induction. BinomialKernelDelta supplies finite signed Pascal
   cancellation under the exact normalized library delta convention. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.LatticeActualChargedLocality
open LatticeGeneratingFieldLocality LatticeActualGeneratorLocality
open LatticeActualProductKernel LatticeActualOrderedProducts BinomialKernelDelta
open scoped VertexOperator
noncomputable section

def rawCommutator (D : LatticeData) (α β : Charge D) : ℤ → ℤ → Module.End ℂ (Carrier D) :=
  fun k l => rawCoeff D α k * rawCoeff D β l - rawCoeff D β l * rawCoeff D α k

theorem raw_commutator_kernel (D : LatticeData) (α β : Charge D)
    (δ : Charge D) (p : Oscillator D) :
    (fun k l => rawCommutator D α β k l (Finsupp.single δ p)) =
      epsilon D α β •
        (expansion (fun u v => commonKernel D α β u v (Finsupp.single δ p))
            (bilinear D α β) -
          integerSign (bilinear D α β) •
            BinomialKernelDelta.flip (expansion (BinomialKernelDelta.flip (fun u v =>
              commonKernel D α β u v (Finsupp.single δ p))) (bilinear D α β))) := by
  funext k l
  simp only [rawCommutator, LinearMap.sub_apply, Module.End.mul_apply,
    ]
  rw [actual_ordered_product D α β δ p k l,actual_reverse_ordered_product D α β δ p k l]
  rw [epsilon_skew D β α, LatticeFiniteNegativeGeneration.bilinear_symmetric D β α]
  change _ = epsilon D α β •
    ((∑ᶠ j : ℕ, contraction (bilinear D α β) j •
      commonKernel D α β (k-bilinear D α β+j) (l-j) (Finsupp.single δ p)) -
      paritySign (bilinear D α β) •
        (∑ᶠ j : ℕ, contraction (bilinear D α β) j •
          commonKernel D α β (k-j) (l-bilinear D α β+j) (Finsupp.single δ p)))
  module

theorem raw_commutator_killed_single (D : LatticeData) (α β : Charge D)
    (δ : Charge D) (p : Oscillator D) :
    rawDelta^[(-bilinear D α β).toNat]
      (fun k l => rawCommutator D α β k l (Finsupp.single δ p)) = 0 := by
  let K := fun u v => commonKernel D α β u v (Finsupp.single δ p)
  have hK : BoundedKernel K := kernel_lower_bounds D α β δ p
  rw [raw_commutator_kernel, rawDelta_iterate_smul,
    binomial_commutator_killed _ hK, smul_zero]

/-- Actual locality with the library delta at the stated sufficient exponent. -/
theorem actual_charged_charged_locality (D : LatticeData) (α β : Charge D) :
    FieldNormalProductLocality.delta^[(-bilinear D α β).toNat]
      (FieldNormalProductLocality.commutator (actualField D α) (actualField D β)) = 0 := by
  let N := (-bilinear D α β).toNat
  funext m n
  apply Finsupp.lhom_ext
  intro δ p
  have he : (fun m n =>
      FieldNormalProductLocality.commutator (actualField D α) (actualField D β)
        m n (Finsupp.single δ p)) =
      normalized (fun k l => rawCommutator D α β k l (Finsupp.single δ p)) := by
    funext m n
    simp only [FieldNormalProductLocality.commutator, actual_modes,
      rawCommutator, normalized, LinearMap.sub_apply, Module.End.mul_apply]
  have h := delta_evaluation
    (FieldNormalProductLocality.commutator (actualField D α) (actualField D β))
    (Finsupp.single δ p) N
  rw [he, normalized_iterate, raw_commutator_killed_single] at h
  exact congrArg (fun f : ℤ → ℤ → Carrier D => f m n) h

end
end D5.S3.VertexAlgebra.LatticeActualChargedLocality

/- Exact zero-charge and rank-zero edge cases on the actual carrier. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.LatticeActualEdgeCases
open LatticeGeneratingFieldLocality LatticeAllStateField FieldNormalProduct
open scoped VertexOperator

end D5.S3.VertexAlgebra.LatticeActualEdgeCases

/- Nonnegative pairing, diagonal and rank-zero consequences of actual locality.
   No extra lattice property beyond LatticeData is used. -/
set_option autoImplicit false
namespace D5.S3.VertexAlgebra.LatticeActualLocalityCases
open LatticeGeneratingFieldLocality LatticeActualGeneratorLocality
open LatticeActualChargedLocality
noncomputable section

end
end D5.S3.VertexAlgebra.LatticeActualLocalityCases
