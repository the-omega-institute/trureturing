/- GID: D5/S3/VertexAlgebra/FormalSeries/ThreeFieldInnerLaurentFiber
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/FormalSeries/ThreeFieldInnerLaurentFiber
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The exact signed finite fiber of the raw inner inverse. -/
import D5.S3.VertexAlgebra.FormalSeries.SupportedThreeFieldCollision

/-! The indices r,j,l expand b/(x-z), z/x, and b/z respectively.
All three numerator coordinates are tested before any signed toNat bound.
The integer-binomial normalization is inherited from the residue suppliers. -/
set_option autoImplicit false
namespace D5.S3.VertexAlgebra.ThreeFieldInnerLaurentFiber
open UniformGradedLocalCorrelator UngradedLocalWordSeries
open StateFieldResidueReconstruction (integerBinomial)
open scoped BigOperators
noncomputable section

abbrev InnerIndex := ℕ × (ℕ × ℕ)

def innerInput (k : ℕ) (a : Fin 3 → ℕ) (x b z : ℤ)
    (i : InnerIndex) : Exponent 3 :=
  ![x + a 0 + 2 * k + i.1 + i.2.1, b + k - i.1 - i.2.2,
    z + a 1 + a 2 - i.2.1 + i.2.2]

def innerWeight (k : ℕ) (a : Fin 3 → ℕ) (i : InnerIndex) : ℂ :=
  ((-1 : ℂ) ^ (i.1 + i.2.1)) * integerBinomial (-(k : ℤ)) i.1 *
    integerBinomial (-((2 * k + i.1 : ℕ) : ℤ)) i.2.1 *
      integerBinomial (-(a 1 : ℤ)) i.2.2

def InnerAdmissible (k : ℕ) (a : Fin 3 → ℕ) (x b z : ℤ)
    (i : InnerIndex) : Prop := ∀ c : Fin 3, 0 ≤ innerInput k a x b z i c

theorem inner_bounds (k : ℕ) (a : Fin 3 → ℕ) (x b z : ℤ)
    (i : InnerIndex) (hi : InnerAdmissible k a x b z i) :
    (i.1 : ℤ) + i.2.2 ≤ b + k ∧
    (i.1 : ℤ) + i.2.1 ≤ b + z + k + a 1 + a 2 ∧
    0 ≤ b + k ∧ 0 ≤ b + z + k + a 1 + a 2 ∧
    0 ≤ x + b + z + a 0 + 3 * k + a 1 + a 2 := by
  have h0 := hi 0
  have h1 := hi 1
  have h2 := hi 2
  simp only [innerInput, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at h0 h1 h2
  omega

def innerFiber (k : ℕ) (a : Fin 3 → ℕ) (x b z : ℤ) : Finset InnerIndex := by
  classical
  exact ((Finset.range ((b + k).toNat + 1)).product
    ((Finset.range ((b + z + k + a 1 + a 2).toNat + 1)).product
      (Finset.range ((b + k).toNat + 1)))).filter (InnerAdmissible k a x b z)

theorem mem_innerFiber_iff (k : ℕ) (a : Fin 3 → ℕ) (x b z : ℤ)
    (i : InnerIndex) : i ∈ innerFiber k a x b z ↔ InnerAdmissible k a x b z i := by
  classical
  constructor
  · exact fun h => (Finset.mem_filter.mp h).2
  · intro hi
    obtain ⟨hrl, hrj, hb, hbz, he⟩ := inner_bounds k a x b z i hi
    apply Finset.mem_filter.mpr
    refine ⟨?_, hi⟩
    exact Finset.mem_product.mpr ⟨Finset.mem_range.mpr (by omega),
      Finset.mem_product.mpr ⟨Finset.mem_range.mpr (by omega),
        Finset.mem_range.mpr (by omega)⟩⟩

def innerCoefficient {R : Type*} [CommRing R] [Algebra ℂ R]
    (P : MvPowerSeries (Fin 3) R) (k : ℕ) (a : Fin 3 → ℕ) (x b z : ℤ) : R :=
  ∑ i ∈ innerFiber k a x b z, innerWeight k a i • signedExtend P (innerInput k a x b z i)

end
end D5.S3.VertexAlgebra.ThreeFieldInnerLaurentFiber
