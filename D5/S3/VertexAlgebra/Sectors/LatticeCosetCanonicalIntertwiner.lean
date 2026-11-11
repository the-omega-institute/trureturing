/- GID: D5/S3/VertexAlgebra/Sectors/LatticeCosetCanonicalIntertwiner
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Sectors/LatticeCosetCanonicalIntertwiner
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Complete rational Hahn reindexing of native compressed lattice fields. -/

/-
proof_shape: field_coeff, field_coeff_off, mode_integer, ground_coefficient,
ground_scalar, intertwiner_ne_zero: bind-only (consumed helpers).
consumers: field_coeff -> intertwiner, mode_integer, ground_coefficient;
field_coeff_off -> intertwiner, mode_off; mode_integer -> mixed_integer,
source_derivative, target_derivative; ground_coefficient -> ground_scalar;
ground_scalar -> intertwiner_ne_zero, canonical_groundEvaluation;
intertwiner_ne_zero -> LatticeDualCosetFusion.scalarInclusion_injective.
Private normalization helpers external_ground_pairing and external_ground_sign
are consumed by compressed_ground, which is consumed by ground_coefficient.
escape_witness: none in these normalization lemmas alone. The constructed
Hahn field is consumed by the full-law content in the co-delivered
LatticeCosetCanonicalNeutral, Jacobi and Laws modules.
admission_basis: co-delivered escape-witness content, not independent novelty.

Classical lattice-field conventions: Bakalov--Kac, math/0402315v1,
section 4.1. Native residue and Sugawara suppliers retain their Scott
Carnahan and Kalle Kytölä attributions. No mathematical novelty, physical
realization, categorical completion or string completion is claimed.
-/

import D5.S3.VertexAlgebra.Sectors.LatticeCosetOperatorCorrection
import D5.S3.VertexAlgebra.Sectors.LatticeDualCosetVirasoro

/-! Rational Hahn reindexing of the complete native compressed field and its ground normalization. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.LatticeCosetCanonicalIntertwiner

open LatticeGeneratingFieldLocality LatticeAllStateField LatticeFiniteNegativeGeneration
open LatticeCosetCompression LatticeCosetInnerExpansion LatticeDiscriminantTheta
open scoped BigOperators VertexOperator
noncomputable section

open private compressedField_modes from D5.S3.VertexAlgebra.Sectors.LatticeCosetInnerExpansion

variable (D : LatticeData) {e : ℕ} (B : Matrix (Fin D.rank) (Fin e) ℤ)

abbrev zeroSymm : ∀ i j : Fin e, (0 : Matrix (Fin e) (Fin e) ℤ) i j = (0 : Matrix (Fin e) (Fin e) ℤ) j i :=
  fun _ _ => rfl
abbrev zeroEven : ∀ i : Fin e, Even ((0 : Matrix (Fin e) (Fin e) ℤ) i i) :=
  fun _ => ⟨0, by simp⟩

/-- The raw rational exponent offset, computed with the old inverse Gram form. -/
def shift (a b : Fin e → ℤ) : ℚ :=
  ∑ j, ∑ k, (a j : ℚ) * (∑ i, (B i j : ℚ) * longitudinal D B i k) * (b k : ℚ)

def exponentEmbedding (q : ℚ) : ℤ ↪o ℚ :=
  OrderEmbedding.ofStrictMono (fun k : ℤ => q + (k : ℚ)) (by
    intro i j hij
    have hij' : (i : ℚ) < (j : ℚ) := by exact_mod_cast hij
    dsimp only
    linarith)

/-- The complete compressed native field, reindexed in rational Hahn exponents. -/
def field (a b : Fin e → ℤ) (u : Carrier D) :
    HVertexOperator ℚ ℂ (Carrier D) (Carrier D) where
  toFun v := HahnModule.of ℂ (HahnSeries.embDomain (exponentEmbedding (shift D B a b))
    ((HahnModule.of ℂ).symm (compressedField D B 0 zeroSymm zeroEven a b u v)))
  map_add' v w := by
    apply (HahnModule.of ℂ).symm.injective
    simp only [Equiv.symm_apply_apply, HahnModule.of_symm_add, map_add,
      HahnSeries.embDomain_add]
  map_smul' z v := by
    classical
    apply (HahnModule.of ℂ).symm.injective
    simp only [RingHom.id_apply, Equiv.symm_apply_apply, HahnModule.of_symm_smul, map_smul]
    apply HahnSeries.ext
    funext x
    by_cases hx : x ∈ Set.range (exponentEmbedding (shift D B a b))
    · obtain ⟨k, rfl⟩ := hx
      simp only [HahnSeries.embDomain_coeff, HahnSeries.coeff_smul]
    · simp only [HahnSeries.embDomain_of_notMem_range hx, HahnSeries.coeff_smul, smul_zero]

theorem field_coeff (a b : Fin e → ℤ) (u v : Carrier D) (k : ℤ) :
    HVertexOperator.coeff (field D B a b u) (shift D B a b + (k : ℚ)) v =
      HVertexOperator.coeff (compressedField D B 0 zeroSymm zeroEven a b u) k v := by
  change (HahnSeries.embDomain (exponentEmbedding (shift D B a b))
      ((HahnModule.of ℂ).symm (compressedField D B 0 zeroSymm zeroEven a b u v))).coeff
        (exponentEmbedding (shift D B a b) k) = _
  rw [HahnSeries.embDomain_coeff]
  rfl

theorem field_coeff_off (a b : Fin e → ℤ) (u v : Carrier D) (x : ℚ)
    (hx : x ∉ Set.range (exponentEmbedding (shift D B a b))) :
    HVertexOperator.coeff (field D B a b u) x v = 0 := by
  exact HahnSeries.embDomain_of_notMem_range hx

/-- Source linearity is inherited from the actual ambient state-field map. -/
def intertwiner (a b : Fin e → ℤ) :
    Carrier D →ₗ[ℂ] HVertexOperator ℚ ℂ (Carrier D) (Carrier D) where
  toFun := field D B a b
  map_add' u w := by
    apply HVertexOperator.coeff_inj
    funext x
    apply LinearMap.ext
    intro v
    by_cases hx : x ∈ Set.range (exponentEmbedding (shift D B a b))
    · obtain ⟨k, rfl⟩ := hx
      simp only [map_add, Pi.add_apply, LinearMap.add_apply]
      change HVertexOperator.coeff (field D B a b (u+w)) (shift D B a b + (k : ℚ)) v =
        HVertexOperator.coeff (field D B a b u) (shift D B a b + (k : ℚ)) v +
        HVertexOperator.coeff (field D B a b w) (shift D B a b + (k : ℚ)) v
      simp only [field_coeff, VertexOperator.coeff_eq_ncoeff, compressedField_modes]
      simp [compressed, map_add]
    · simp [field_coeff_off D B a b _ _ _ hx]
  map_smul' z u := by
    apply HVertexOperator.coeff_inj
    funext x
    apply LinearMap.ext
    intro v
    by_cases hx : x ∈ Set.range (exponentEmbedding (shift D B a b))
    · obtain ⟨k, rfl⟩ := hx
      simp only [RingHom.id_apply, map_smul, Pi.smul_apply, LinearMap.smul_apply]
      change HVertexOperator.coeff (field D B a b (z • u)) (shift D B a b + (k : ℚ)) v =
        z • HVertexOperator.coeff (field D B a b u) (shift D B a b + (k : ℚ)) v
      simp only [field_coeff, VertexOperator.coeff_eq_ncoeff, compressedField_modes]
      simp [compressed, map_smul]
    · simp [field_coeff_off D B a b _ _ _ hx]

/-- Rational modes use the convention that mode tau has raw exponent -tau-1. -/
def mode (a b : Fin e → ℤ) (u : Carrier D) (tau : ℚ) : Carrier D →ₗ[ℂ] Carrier D :=
  HVertexOperator.coeff (intertwiner D B a b u) (-tau-1)

theorem mode_integer (a b : Fin e → ℤ) (u v : Carrier D) (m : ℤ) :
    mode D B a b u ((m : ℚ)-shift D B a b) v =
      compressed D B 0 zeroSymm zeroEven a b u m v := by
  unfold mode
  change HVertexOperator.coeff (field D B a b u) _ v = _
  rw [show -((m : ℚ)-shift D B a b)-1 = shift D B a b + ((-m-1 : ℤ) : ℚ) by push_cast; ring,
    field_coeff, VertexOperator.coeff_eq_ncoeff,
    show -(-m-1)-1 = m by omega, compressedField_modes]

open private actual_negative_single from D5.S3.VertexAlgebra.LatticeFiniteNegativeGeneration
open private injection_single projection_single from
  D5.S3.VertexAlgebra.Sectors.LatticeCosetCompression

private theorem external_ground_pairing (a b : Fin e → ℤ) :
    bilinear (ambient D e B 0 zeroSymm zeroEven)
      (liftCharge D B 0 zeroSymm zeroEven a 0)
      (liftCharge D B 0 zeroSymm zeroEven b 0) = 0 := by
  simp [bilinear, Fin.sum_univ_add, ambient, liftCharge]

private theorem external_ground_sign (a b : Fin e → ℤ) :
    epsilon (ambient D e B 0 zeroSymm zeroEven)
      (liftCharge D B 0 zeroSymm zeroEven a 0)
      (liftCharge D B 0 zeroSymm zeroEven b 0) = 1 := by
  classical
  simp [epsilon, lowerCocycleExponent, Finset.sum_filter, Fin.sum_univ_add,
    ambient, liftCharge, halfDiagonal, paritySign]

private theorem compressed_ground (a b : Fin e → ℤ) :
    compressed D B 0 zeroSymm zeroEven a b (vacuum D) (-1) (vacuum D) = vacuum D := by
  classical
  unfold compressed vacuum
  simp only [LinearMap.comp_apply, injection_single, map_one]
  rw [stateField_ground]
  have h := actual_negative_single (ambient D e B 0 zeroSymm zeroEven)
    (liftCharge D B 0 zeroSymm zeroEven a 0)
    (liftCharge D B 0 zeroSymm zeroEven b 0)
    (by rw [external_ground_pairing])
  rw [external_ground_pairing, external_ground_sign] at h
  simp only [neg_zero, zero_sub, one_smul] at h
  rw [h]
  have he : externalCharge D B 0 zeroSymm zeroEven
      (liftCharge D B 0 zeroSymm zeroEven a 0 + liftCharge D B 0 zeroSymm zeroEven b 0) = a+b := by
    funext j
    simp [externalCharge, liftCharge]
  have ho : oldCharge D B 0 zeroSymm zeroEven
      (liftCharge D B 0 zeroSymm zeroEven a 0 + liftCharge D B 0 zeroSymm zeroEven b 0) = 0 := by
    funext i
    simp [oldCharge, liftCharge]
  rw [projection_single]
  simp [he, ho]

/-- The raw-q coefficient is the full nonzero ground vector. -/
theorem ground_coefficient (a b : Fin e → ℤ) :
    HVertexOperator.coeff (intertwiner D B a b (vacuum D)) (shift D B a b)
      (vacuum D) = vacuum D := by
  change HVertexOperator.coeff (field D B a b (vacuum D)) _ _ = _
  rw [show shift D B a b = shift D B a b + ((0 : ℤ) : ℚ) by simp,
    field_coeff, VertexOperator.coeff_eq_ncoeff, compressedField_modes]
  simpa using compressed_ground D B a b

/-- The charge-zero oscillator-constant coordinate equals one. -/
theorem ground_scalar (a b : Fin e → ℤ) :
    ((HVertexOperator.coeff (intertwiner D B a b (vacuum D)) (shift D B a b)
        (vacuum D)) (0 : Charge D)).coeff 0 = 1 := by
  rw [ground_coefficient]
  simp [vacuum]

theorem intertwiner_ne_zero (a b : Fin e → ℤ) : intertwiner D B a b ≠ 0 := by
  intro hz
  have h := ground_scalar D B a b
  rw [hz] at h
  simpa using h

end
end D5.S3.VertexAlgebra.LatticeCosetCanonicalIntertwiner
