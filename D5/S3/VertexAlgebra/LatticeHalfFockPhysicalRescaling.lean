/- GID: D5/S3/VertexAlgebra/LatticeHalfFockPhysicalRescaling
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/LatticeHalfFockPhysicalRescaling
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Direct signed physical slices of the canonical singleton normal operation. -/

/- Copyright (c) 2025 Kalle Kytölä; additional half-integer implementation
   copyright (c) 2026. Apache 2.0. Normal-product architecture: Scott Carnahan,
   vertexAlg 4453e34ec390e82a0c789c731ada8f9a6e86bdea. Signed partition adapted
   from the preserved NormalInsertion source efcb0545c399cdf758215ca0014b92ac1160f7c72f30153bf5b4819a95f91974.
   Classical twisted lattice calculus: Dong--Nagatomo math/9808088v1 §3.2;
   Bakalov--Kac math/0402315v1 §4. -/
import D5.S3.VertexAlgebra.LatticeHalfFockOriginalTranslation
import D5.S3.VertexAlgebra.FieldNormalProduct

/-! Signed slices identify the actual singleton field with the ordinary normal product. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.LatticeHalfFockPhysicalRescaling
open LatticeGeneratingFieldLocality LatticeHalfFockChargedTensorCoefficients
open LatticeHalfFockFockNormalField FieldNormalProduct
open scoped BigOperators VertexOperator
noncomputable section

def physicalSlice (D : LatticeData) (hu : IsUnit D.G.det)
    (field : NativeField D hu) (shift : ℤ) : VertexOperator ℂ (ActualTensor D hu) :=
  VertexOperator.of_coeff (fun exponent => field.coeff (2 * exponent - shift)) (by
    intro vector
    refine ⟨(((HahnModule.of ℂ).symm (field vector)).order + shift) / 2 - 1, ?_⟩
    intro exponent member
    by_contra outside
    apply member
    change ((HahnModule.of ℂ).symm (field vector)).coeff (2 * exponent - shift) = 0
    apply HahnSeries.coeff_eq_zero_of_lt_order
    omega)

theorem physicalSlice_mode (D : LatticeData) (hu : IsUnit D.G.det)
    (field : NativeField D hu) (shift mode : ℤ) :
    (physicalSlice D hu field shift)[[mode]] = field.coeff (-2 * mode - shift - 2) := by
  simp only [physicalSlice, VertexOperator.ncoeff_of_coeff]
  rw [show 2 * (-mode - 1) - shift = -2 * mode - shift - 2 by omega]

def physicalJet (D : LatticeData) (hu : IsUnit D.G.det) (index : Index D) :
    VertexOperator ℂ (ActualTensor D hu) :=
  VertexOperator.of_coeff (fun exponent => jetCurrent D hu index (-exponent - 1)) (by
    intro vector
    obtain ⟨cutoff, bound⟩ :=
      LatticeHalfFock.tensor_current_truncation D (ActualGround D hu) vector
    refine ⟨-(cutoff : ℤ) - 1, ?_⟩
    intro exponent member
    by_contra outside
    apply member
    simp only [jetCurrent, LinearMap.smul_apply,
      bound index.1 (-exponent - 1) (by omega), smul_zero])

theorem physicalJet_mode (D : LatticeData) (hu : IsUnit D.G.det)
    (index : Index D) (mode : ℤ) :
    (physicalJet D hu index)[[mode]] = jetCurrent D hu index mode := by
  simp only [physicalJet, VertexOperator.ncoeff_of_coeff]
  congr 1
  omega

private theorem finsum_integer_split {Value : Type*} [AddCommMonoid Value]
    (terms : ℤ → Value) (finite : Function.HasFiniteSupport terms) :
    (∑ᶠ mode : ℤ, terms mode) =
      (∑ᶠ offset : ℕ, terms (-(offset : ℤ) - 1)) + ∑ᶠ offset : ℕ, terms offset := by
  have cover : Set.range (fun offset : ℕ => -(offset : ℤ) - 1) ∪
      Set.range (fun offset : ℕ => (offset : ℤ)) = Set.univ := by
    ext mode
    simp only [Set.mem_union, Set.mem_range, Set.mem_univ, iff_true]
    by_cases negative : mode < 0
    · exact Or.inl ⟨(-mode - 1).toNat, by omega⟩
    · exact Or.inr ⟨mode.toNat, by omega⟩
  have disjoint : Disjoint (Set.range (fun offset : ℕ => -(offset : ℤ) - 1))
      (Set.range (fun offset : ℕ => (offset : ℤ))) := by
    rw [Set.disjoint_left]
    rintro mode ⟨negative, rfl⟩ ⟨positive, equality⟩
    dsimp at equality
    omega
  rw [← finsum_mem_univ, ← cover, finsum_mem_union' disjoint
    (finite.subset Set.inter_subset_right) (finite.subset Set.inter_subset_right)]
  rw [finsum_mem_range (by intro first second equality; dsimp at equality; omega),
    finsum_mem_range (by intro first second equality; dsimp at equality; omega)]

/-- The exhaustive signed-mode split is the ordinary minus-one product,
pointwise at each actual tensor state. -/
theorem physicalSlice_singletonLinear (D : LatticeData) (hu : IsUnit D.G.det)
    (index : Index D) (field : NativeField D hu) (shift : ℤ) :
    physicalSlice D hu (singletonLinear D hu index field)
        (shift + 2 * index.2 + 1) =
      (normalMinusOne (physicalJet D hu index) (physicalSlice D hu field shift)).val := by
  have modes (mode : ℤ) :
      (physicalSlice D hu (singletonLinear D hu index field)
        (shift + 2 * index.2 + 1))[[mode]] =
      (normalMinusOne (physicalJet D hu index) (physicalSlice D hu field shift)).val[[mode]] := by
    apply LinearMap.ext
    intro vector
    rw [physicalSlice_mode, singletonLinear_coefficient, (normalMinusOne _ _).property]
    have finite : Function.HasFiniteSupport (fun m : ℤ =>
        flatTerm D hu field [index] (-2 * mode - (shift + 2 * index.2 + 1) - 2)
          vector (m, ())) :=
      (flatTerm_finite D hu field [index] _ vector).comp_of_injective
        (by intro a b h; exact congrArg Prod.fst h)
    rw [finsum_integer_split _ finite]
    congr 1
    · apply finsum_congr
      intro offset
      rw [physicalJet_mode, physicalSlice_mode]
      simp only [flatTerm, flatCoefficient, if_pos (show -(offset : ℤ) - 1 < 0 by omega),
        Module.End.mul_apply]
      congr 2
      ring
    · apply finsum_congr
      intro offset
      rw [physicalJet_mode, physicalSlice_mode]
      simp only [flatTerm, flatCoefficient, if_neg (show ¬ (offset : ℤ) < 0 by omega),
        Module.End.mul_apply]
      congr 2
      ring
  apply HVertexOperator.coeff_inj
  funext exponent
  simpa only [VertexOperator.ncoeff_apply,
    show -(-exponent - 1) - 1 = exponent by omega] using modes (-exponent - 1)

end
end D5.S3.VertexAlgebra.LatticeHalfFockPhysicalRescaling
