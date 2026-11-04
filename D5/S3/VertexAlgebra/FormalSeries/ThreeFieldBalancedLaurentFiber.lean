/- GID: D5/S3/VertexAlgebra/FormalSeries/ThreeFieldBalancedLaurentFiber
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/FormalSeries/ThreeFieldBalancedLaurentFiber
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact finite signed numerator fibers for the balanced channel. -/
import D5.S3.VertexAlgebra.FormalSeries.ThreeFieldInnerLaurentFiber

/-! The indices expand s/(x-z), z/x and s/x. Nonnegativity is checked
on all three original numerator coordinates before signed bounds are converted. -/
set_option autoImplicit false
namespace D5.S3.VertexAlgebra.ThreeFieldBalancedLaurentFiber
open UniformGradedLocalCorrelator UngradedLocalWordSeries
open StateFieldResidueReconstruction (integerBinomial)
open scoped BigOperators
noncomputable section
abbrev BalancedIndex := ℕ × (ℕ × ℕ)

def balancedInput (k : ℕ) (a : Fin 3 → ℕ) (s x z : ℤ)
    (i : BalancedIndex) : Exponent 3 :=
  ![s + k - i.1 - i.2.2, x + a 0 + a 1 + 2 * k + i.1 + i.2.1 + i.2.2,
    z + a 2 - i.2.1]

def balancedWeight (k : ℕ) (a : Fin 3 → ℕ) (i : BalancedIndex) : ℂ :=
  integerBinomial (-(k : ℤ)) i.1 * integerBinomial (-(a 0 : ℤ)) i.2.2 *
    (-1 : ℂ) ^ i.2.1 * integerBinomial (-((2 * k + i.1 : ℕ) : ℤ)) i.2.1

def BalancedAdmissible (k : ℕ) (a : Fin 3 → ℕ) (s x z : ℤ)
    (i : BalancedIndex) : Prop := ∀ c : Fin 3, 0 ≤ balancedInput k a s x z i c

theorem balanced_input_total (k : ℕ) (a : Fin 3 → ℕ) (s x z : ℤ)
    (i : BalancedIndex) :
    balancedInput k a s x z i 0 + balancedInput k a s x z i 1 +
      balancedInput k a s x z i 2 = s + x + z + 3 * k + a 0 + a 1 + a 2 := by
  simp only [balancedInput, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  omega


theorem balanced_bounds (k : ℕ) (a : Fin 3 → ℕ) (s x z : ℤ)
    (i : BalancedIndex) (hi : BalancedAdmissible k a s x z i) :
    (i.1 : ℤ) + i.2.2 ≤ s + k ∧ (i.2.1 : ℤ) ≤ z + a 2 ∧
    (i.1 : ℤ) + i.2.1 + i.2.2 ≤ s + z + k + a 2 ∧
    0 ≤ s + k ∧ 0 ≤ z + a 2 ∧ 0 ≤ s + z + k + a 2 ∧
    0 ≤ s + x + z + 3 * k + a 0 + a 1 + a 2 := by
  have h0 := hi 0
  have h1 := hi 1
  have h2 := hi 2
  simp only [balancedInput, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at h0 h1 h2
  refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, ?_⟩
  rw [← balanced_input_total k a s x z i]
  exact add_nonneg (add_nonneg h0 h1) h2


def balancedFiber (k : ℕ) (a : Fin 3 → ℕ) (s x z : ℤ) : Finset BalancedIndex := by
  classical
  exact ((Finset.range ((s + k).toNat + 1)).product
    ((Finset.range ((z + a 2).toNat + 1)).product
      (Finset.range ((s + k).toNat + 1)))).filter (BalancedAdmissible k a s x z)

theorem mem_balancedFiber_iff (k : ℕ) (a : Fin 3 → ℕ) (s x z : ℤ)
    (i : BalancedIndex) : i ∈ balancedFiber k a s x z ↔ BalancedAdmissible k a s x z i := by
  classical
  constructor
  · exact fun h => (Finset.mem_filter.mp h).2
  · intro hi
    obtain ⟨hrl, hj, hrjl, hs, hz, hsz, he⟩ := balanced_bounds k a s x z i hi
    apply Finset.mem_filter.mpr
    refine ⟨?_, hi⟩
    exact Finset.mem_product.mpr ⟨Finset.mem_range.mpr (by omega),
      Finset.mem_product.mpr ⟨Finset.mem_range.mpr (by omega),
        Finset.mem_range.mpr (by omega)⟩⟩

def balancedCoefficient {R : Type*} [CommRing R] [Algebra ℂ R]
    (P : MvPowerSeries (Fin 3) R) (k : ℕ) (a : Fin 3 → ℕ) (s x z : ℤ) : R :=
  ∑ i ∈ balancedFiber k a s x z,
    balancedWeight k a i • signedExtend P (balancedInput k a s x z i)
end
end D5.S3.VertexAlgebra.ThreeFieldBalancedLaurentFiber
