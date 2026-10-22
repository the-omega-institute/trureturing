/- GID: D5/S3/VertexAlgebra/LatticeHalfFockCurrentBorcherds
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/LatticeHalfFockCurrentBorcherds
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Pointwise finite residues of the original twisted current fields. -/

import D5.S3.VertexAlgebra.LatticeHalfFockCurrentSeed

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.LatticeHalfFockCurrentBorcherds

open LatticeGeneratingFieldLocality LatticeFiniteNegativeGeneration
open LatticeSugawaraCurrents
open LatticeHalfFockFirstDescendant LatticeHalfFockOriginalMixedIterate
open LatticeHalfFockAllStateCurrentCommutator LatticeHalfFockAllStateField
open LatticeHalfFockChargedTensorCoefficients LatticeHalfFockFockNormalField
open scoped BigOperators VertexOperator

noncomputable section

def leftTerm (D : LatticeData) (hu : IsUnit D.G.det) (h : Fin D.rank → ℂ)
    (state : Carrier D) (vector : ActualTensor D hu) (order mode exponent : ℤ)
    (degree : ℕ) : ActualTensor D hu :=
  Ring.choose (LatticeHalfFock.frequency mode) degree •
    (Ytw D hu (((sourceCurrent D h)[[order + degree]]) state)).coeff
      (exponent + 2 * degree) vector

def rightFirst (D : LatticeData) (hu : IsUnit D.G.det) (h : Fin D.rank → ℂ)
    (state : Carrier D) (vector : ActualTensor D hu) (order mode exponent : ℤ)
    (degree : ℕ) : ActualTensor D hu :=
  currentCombination D hu h (mode + order - degree)
    ((Ytw D hu state).coeff (exponent + 2 * mode + 1 - 2 * degree) vector)

def rightSecond (D : LatticeData) (hu : IsUnit D.G.det) (h : Fin D.rank → ℂ)
    (state : Carrier D) (vector : ActualTensor D hu) (order mode exponent : ℤ)
    (degree : ℕ) : ActualTensor D hu :=
  (Ytw D hu state).coeff (exponent + 2 * mode + 1 - 2 * order + 2 * degree)
    (currentCombination D hu h (mode + degree) vector)

def rightTerm (D : LatticeData) (hu : IsUnit D.G.det) (h : Fin D.rank → ℂ)
    (state : Carrier D) (vector : ActualTensor D hu) (order mode exponent : ℤ)
    (degree : ℕ) : ActualTensor D hu :=
  ((-1 : ℂ) ^ degree * Ring.choose (order : ℂ) degree) •
    (rightFirst D hu h state vector order mode exponent degree -
      (-1 : ℂ) ^ order • rightSecond D hu h state vector order mode exponent degree)

def leftResidue (D : LatticeData) (hu : IsUnit D.G.det) (h : Fin D.rank → ℂ)
    (state : Carrier D) (vector : ActualTensor D hu) (order mode exponent : ℤ) :
    ActualTensor D hu := ∑ᶠ degree, leftTerm D hu h state vector order mode exponent degree

def rightResidue (D : LatticeData) (hu : IsUnit D.G.det) (h : Fin D.rank → ℂ)
    (state : Carrier D) (vector : ActualTensor D hu) (order mode exponent : ℤ) :
    ActualTensor D hu := ∑ᶠ degree, rightTerm D hu h state vector order mode exponent degree

def discrepancy (D : LatticeData) (hu : IsUnit D.G.det) (h : Fin D.rank → ℂ)
    (state : Carrier D) (vector : ActualTensor D hu) (order mode exponent : ℤ) :
    ActualTensor D hu := leftResidue D hu h state vector order mode exponent -
      rightResidue D hu h state vector order mode exponent

theorem signed_source_support (D : LatticeData) (h : Fin D.rank → ℂ)
    (state : Carrier D) (order : ℤ) :
    Function.support (fun degree : ℕ => ((sourceCurrent D h)[[order + degree]]) state) ⊆
      Finset.range (((vectorFrequencyBound D state : ℤ) - order).toNat + 1) := by
  intro degree nonzero
  simp only [Finset.mem_coe, Finset.mem_range]
  by_contra outside
  exact nonzero (sourceCurrent_upper_truncation D h state (order + degree) (by omega))

theorem leftTerm_support (D : LatticeData) (hu : IsUnit D.G.det)
    (h : Fin D.rank → ℂ) (state : Carrier D) (vector : ActualTensor D hu)
    (order mode exponent : ℤ) :
    Function.support (leftTerm D hu h state vector order mode exponent) ⊆
      Finset.range (((vectorFrequencyBound D state : ℤ) - order).toNat + 1) := by
  intro degree nonzero
  apply signed_source_support D h state order
  intro zero
  exact nonzero (by simp [leftTerm, zero])

theorem rightFirst_support (D : LatticeData) (hu : IsUnit D.G.det)
    (h : Fin D.rank → ℂ) (state : Carrier D) (vector : ActualTensor D hu)
    (order mode exponent : ℤ) :
    Function.support (rightFirst D hu h state vector order mode exponent) ⊆
      Finset.range ((exponent + 2 * mode + 1 - coefficientOrderMinimum D hu state vector +
        2 * (sourceWeightBound D state : ℤ)).toNat + 1) := by
  intro degree nonzero
  simp only [Finset.mem_coe, Finset.mem_range]
  by_contra outside
  exact nonzero (by
    rw [rightFirst, Ytw_source_lower_truncation D hu state vector _ (by omega), map_zero])

theorem rightSecond_finite (D : LatticeData) (hu : IsUnit D.G.det)
    (h : Fin D.rank → ℂ) (state : Carrier D) (vector : ActualTensor D hu)
    (order mode exponent : ℤ) :
    Function.HasFiniteSupport (rightSecond D hu h state vector order mode exponent) := by
  classical
  obtain ⟨cutoff, truncation⟩ :=
    LatticeHalfFock.tensor_current_truncation D (ActualGround D hu) vector
  apply (Finset.range (((cutoff : ℤ) - mode).toNat + 1)).finite_toSet.subset
  intro degree nonzero
  simp only [Finset.mem_coe, Finset.mem_range]
  by_contra outside
  have zero : currentCombination D hu h (mode + degree) vector = 0 := by
    simp only [currentCombination, LinearMap.sum_apply, LinearMap.smul_apply]
    apply Finset.sum_eq_zero
    intro colour member
    rw [truncation colour (mode + degree) (by omega), smul_zero]
  exact nonzero (by simp [rightSecond, zero])

theorem leftTerm_finite (D : LatticeData) (hu : IsUnit D.G.det)
    (h : Fin D.rank → ℂ) (state : Carrier D) (vector : ActualTensor D hu)
    (order mode exponent : ℤ) :
    Function.HasFiniteSupport (leftTerm D hu h state vector order mode exponent) :=
  (Finset.range (((vectorFrequencyBound D state : ℤ) - order).toNat + 1)).finite_toSet.subset
    (leftTerm_support D hu h state vector order mode exponent)

theorem rightFirst_finite (D : LatticeData) (hu : IsUnit D.G.det)
    (h : Fin D.rank → ℂ) (state : Carrier D) (vector : ActualTensor D hu)
    (order mode exponent : ℤ) :
    Function.HasFiniteSupport (rightFirst D hu h state vector order mode exponent) :=
  (Finset.range ((exponent + 2 * mode + 1 - coefficientOrderMinimum D hu state vector +
    2 * (sourceWeightBound D state : ℤ)).toNat + 1)).finite_toSet.subset
      (rightFirst_support D hu h state vector order mode exponent)

theorem rightTerm_finite (D : LatticeData) (hu : IsUnit D.G.det)
    (h : Fin D.rank → ℂ) (state : Carrier D) (vector : ActualTensor D hu)
    (order mode exponent : ℤ) :
    Function.HasFiniteSupport (rightTerm D hu h state vector order mode exponent) := by
  exact Function.HasFiniteSupport.smul_right
    (fun degree : ℕ => (-1 : ℂ) ^ degree * Ring.choose (order : ℂ) degree)
    ((rightFirst_finite D hu h state vector order mode exponent).sub
      (Function.HasFiniteSupport.smul_right (fun _ : ℕ => (-1 : ℂ) ^ order)
        (rightSecond_finite D hu h state vector order mode exponent)))

end
end D5.S3.VertexAlgebra.LatticeHalfFockCurrentBorcherds
