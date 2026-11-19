/- GID: D5/S3/VertexAlgebra/BRST/OriginalOrbifoldMatterVertexAlgebra
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/BRST/OriginalOrbifoldMatterVertexAlgebra
   mirror-E: none(waiver:algebraic-original-matter-vertex-algebra)
   anchors: []
   utility: none
   digest: All-state locality and Borcherds identity on the native BRST matter tensor. -/

import D5.S3.VertexAlgebra.BRST.OriginalOrbifoldMatterTensorProducts
import D5.S3.VertexAlgebra.StateField.TensorCoefficientLocality
import D5.S3.VertexAlgebra.StateField.BorcherdsFromLocality

/-! The two ordered coefficient products transfer constituent locality to pure
tensor states. Additivity extends locality to the algebraic matter tensor, and
the locality theorem supplies the full Borcherds identity on that carrier. -/

set_option autoImplicit false

noncomputable section

open scoped TensorProduct VertexOperator

namespace D5.S3.VertexAlgebra.OriginalOrbifoldMatterVertexAlgebra

open OriginalOrbifoldCriticalMatter
open OriginalOrbifoldMatterTensorField (stateField stateField_vacuum stateField_creation
  stateField_creativity stressState)
open OriginalOrbifoldMatterTensorProducts (ordered_product_tmul translation_vacuum
  stateField_covariance)
open FieldNormalProductLocality (commutator delta)
open FiniteFieldLocality (Local localAdd localSymm)
open StateField.TensorCoefficientLocality (tensorField_locality_of_ordered_products)

private theorem pure_locality (a c : Orbifold) (b d : Hyperbolic) :
    Local (stateField (a ⊗ₜ[ℂ] b)) (stateField (c ⊗ₜ[ℂ] d)) := by
  obtain ⟨p, hp⟩ := orbifoldVertexAlgebra.locality a c
  obtain ⟨q, hq⟩ := LatticeAllStateLocality.stateField_locality hyperbolicData b d
  exact ⟨p + q, tensorField_locality_of_ordered_products
    (orbifoldVertexAlgebra.stateField a) (orbifoldVertexAlgebra.stateField c)
    (LatticeAllStateField.Y hyperbolicData b) (LatticeAllStateField.Y hyperbolicData d)
    (stateField (a ⊗ₜ[ℂ] b)) (stateField (c ⊗ₜ[ℂ] d)) p q hp hq
    (fun x y m n => ordered_product_tmul a c x b d y m n)
    (fun x y n m => ordered_product_tmul c a x d b y n m)⟩

/-- A single exponent for each pair of matter states kills the operator commutator. -/
theorem stateField_locality (s t : Matter) :
    ∃ N : ℕ, delta^[N] (commutator (stateField s) (stateField t)) = 0 := by
  change Local (stateField s) (stateField t)
  induction s using TensorProduct.inductionOn with
  | tmul a b =>
    induction t using TensorProduct.inductionOn with
    | tmul c d => exact pure_locality a c b d
    | add t u ht hu =>
      rw [map_add]
      exact localSymm _ _ (localAdd _ _ _ (localSymm _ _ ht) (localSymm _ _ hu))
  | add s u hs hu =>
    rw [map_add]
    exact localAdd _ _ _ hs hu

/-- The native BRST matter state-field algebra with its full integer Borcherds identity. -/
def actualVertexAlgebra : LatticeActualVertexAlgebra.StateFieldVertexAlgebra Matter :=
  StateField.BorcherdsFromLocality.ofLocality stateField matterVacuum
    (OriginalOrbifoldCriticalMatter.mode (-1)) stateField_vacuum translation_vacuum
    stateField_creation stateField_creativity stateField_covariance stateField_locality

#check (rfl : actualVertexAlgebra.stateField = stateField)
#check (rfl : actualVertexAlgebra.vacuum = matterVacuum)
#check (rfl : actualVertexAlgebra.translation = OriginalOrbifoldCriticalMatter.mode (-1))
#check (OriginalOrbifoldMatterTensorField.stressState_modes : ∀ n : ℤ,
  ((actualVertexAlgebra.stateField stressState)[[n + 1]]) = OriginalOrbifoldCriticalMatter.mode n)
#check actualVertexAlgebra.borcherds
#print axioms stateField_locality
#print axioms actualVertexAlgebra

end D5.S3.VertexAlgebra.OriginalOrbifoldMatterVertexAlgebra
