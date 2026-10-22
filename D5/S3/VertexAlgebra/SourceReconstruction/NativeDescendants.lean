/- GID: D5/S3/VertexAlgebra/SourceReconstruction/NativeDescendants
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/SourceReconstruction/NativeDescendants
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Triangular all-order coefficients of the actual native twisted descendant fields. -/

import D5.S3.VertexAlgebra.SourceReconstruction.CurrentRecurrences
import D5.S3.VertexAlgebra.SourceReconstruction.OscillatorWeight
import D5.S3.VertexAlgebra.LatticeHalfFockCurrentBorcherdsRecurrence

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000

namespace D5.S3.VertexAlgebra.SourceReconstruction.NativeDescendants

open LatticeGeneratingFieldLocality LatticeSugawaraCurrents
open LatticeHalfFockFirstDescendant LatticeHalfFockOriginalMixedIterate
open LatticeHalfFockAllStateField LatticeHalfFockAllStateCurrentCommutator
open LatticeHalfFockChargedTensorCoefficients LatticeHalfFockFockNormalField
open LatticeHalfFockCurrentBorcherds LatticeHalfFockCurrentBorcherdsRecurrence
open LatticeHalfFockCurrentSeedConstruction OscillatorWords CurrentRecurrences
open scoped BigOperators VertexOperator

noncomputable section

def nativeFirst (D : LatticeData) (hu : IsUnit D.G.det) (colour : Fin D.rank)
    (degree : ℕ) (source : Carrier D) (exponent : ℤ) (vector : ActualTensor D hu)
    (offset : ℕ) : ActualTensor D hu :=
  currentCombination D hu (Pi.single colour 1) (-(degree : ℤ) - 1 - offset)
    ((Ytw D hu source).coeff (exponent + 1 - 2 * offset) vector)

def nativeSecond (D : LatticeData) (hu : IsUnit D.G.det) (colour : Fin D.rank)
    (degree : ℕ) (source : Carrier D) (exponent : ℤ) (vector : ActualTensor D hu)
    (offset : ℕ) : ActualTensor D hu :=
  (Ytw D hu source).coeff (exponent + 2 * degree + 3 + 2 * offset)
    (currentCombination D hu (Pi.single colour 1) offset vector)

def nativeCorrection (D : LatticeData) (hu : IsUnit D.G.det) (colour : Fin D.rank)
    (degree : ℕ) (source : Carrier D) (exponent : ℤ) (vector : ActualTensor D hu)
    (offset : ℕ) : ActualTensor D hu :=
  (Ytw D hu (((unitCurrent D colour)[[-(degree : ℤ) + offset]]) source)).coeff
    (exponent + 2 * offset + 2) vector

theorem nativeFirst_eq (D : LatticeData) (hu : IsUnit D.G.det) (colour : Fin D.rank)
    (degree : ℕ) (source : Carrier D) (exponent : ℤ) (vector : ActualTensor D hu)
    (offset : ℕ) :
    nativeFirst D hu colour degree source exponent vector offset =
      rightFirst D hu (Pi.single colour 1) source vector (-(degree : ℤ) - 1) 0 exponent offset := by
  simp [nativeFirst, rightFirst]

theorem nativeSecond_eq (D : LatticeData) (hu : IsUnit D.G.det) (colour : Fin D.rank)
    (degree : ℕ) (source : Carrier D) (exponent : ℤ) (vector : ActualTensor D hu)
    (offset : ℕ) :
    nativeSecond D hu colour degree source exponent vector offset =
      rightSecond D hu (Pi.single colour 1) source vector (-(degree : ℤ) - 1) 0 exponent offset := by
  unfold nativeSecond rightSecond
  rw [show exponent + 2 * 0 + 1 - 2 * (-(degree : ℤ) - 1) + 2 * offset =
    exponent + 2 * degree + 3 + 2 * offset by omega, zero_add]

theorem nativeFirst_finite (D : LatticeData) (hu : IsUnit D.G.det) (colour : Fin D.rank)
    (degree : ℕ) (source : Carrier D) (exponent : ℤ) (vector : ActualTensor D hu) :
    Function.HasFiniteSupport (nativeFirst D hu colour degree source exponent vector) := by
  rw [show nativeFirst D hu colour degree source exponent vector =
    rightFirst D hu (Pi.single colour 1) source vector (-(degree : ℤ) - 1) 0 exponent from
      funext (nativeFirst_eq D hu colour degree source exponent vector)]
  exact rightFirst_finite D hu (Pi.single colour 1) source vector (-(degree : ℤ) - 1) 0 exponent

theorem nativeSecond_finite (D : LatticeData) (hu : IsUnit D.G.det) (colour : Fin D.rank)
    (degree : ℕ) (source : Carrier D) (exponent : ℤ) (vector : ActualTensor D hu) :
    Function.HasFiniteSupport (nativeSecond D hu colour degree source exponent vector) := by
  rw [show nativeSecond D hu colour degree source exponent vector =
    rightSecond D hu (Pi.single colour 1) source vector (-(degree : ℤ) - 1) 0 exponent from
      funext (nativeSecond_eq D hu colour degree source exponent vector)]
  exact rightSecond_finite D hu (Pi.single colour 1) source vector (-(degree : ℤ) - 1) 0 exponent

theorem nativeCorrection_finite (D : LatticeData) (hu : IsUnit D.G.det) (colour : Fin D.rank)
    (degree : ℕ) (source : Carrier D) (exponent : ℤ) (vector : ActualTensor D hu) :
    Function.HasFiniteSupport (nativeCorrection D hu colour degree source exponent vector) := by
  apply (Finset.range (vectorFrequencyBound D source + degree + 1)).finite_toSet.subset
  intro offset nonzero
  simp only [Finset.mem_coe, Finset.mem_range]
  by_contra outside
  have zero : ((unitCurrent D colour)[[-(degree : ℤ) + offset]]) source = 0 :=
    sourceCurrent_upper_truncation D (Pi.single colour 1) source _ (by omega)
  exact nonzero (by simp [nativeCorrection, zero])

theorem native_descendant (D : LatticeData) (hu : IsUnit D.G.det) (colour : Fin D.rank)
    (degree : ℕ) (source : Carrier D) (exponent : ℤ) (vector : ActualTensor D hu) :
    (Ytw D hu (((unitCurrent D colour)[[-(degree : ℤ) - 1]]) source)).coeff exponent vector =
      (∑ᶠ offset : ℕ, ((degree + offset).choose degree : ℂ) •
        (nativeFirst D hu colour degree source exponent vector offset +
          (-1 : ℂ) ^ degree • nativeSecond D hu colour degree source exponent vector offset)) -
      ∑ᶠ offset : ℕ, Ring.choose (1 / 2 : ℂ) (offset + 1) •
        nativeCorrection D hu colour degree source exponent vector offset := by
  have identity := actual_signed_current_borcherds D hu (Pi.single colour 1)
    source vector (-(degree : ℤ) - 1) 0 exponent
  have zero : leftTerm D hu (Pi.single colour 1) source vector
      (-(degree : ℤ) - 1) 0 exponent 0 =
      (Ytw D hu (((unitCurrent D colour)[[-(degree : ℤ) - 1]]) source)).coeff exponent vector := by
    simp [leftTerm, unitCurrent]
  have tail (offset : ℕ) : leftTerm D hu (Pi.single colour 1) source vector
      (-(degree : ℤ) - 1) 0 exponent (offset + 1) =
      Ring.choose (1 / 2 : ℂ) (offset + 1) •
        nativeCorrection D hu colour degree source exponent vector offset := by
    simp only [leftTerm, LatticeHalfFock.frequency, Int.cast_zero, zero_add,
      Nat.cast_add, Nat.cast_one, nativeCorrection, unitCurrent]
    rw [show -(degree : ℤ) - 1 + ((offset : ℤ) + 1) = -(degree : ℤ) + offset by omega,
      show exponent + 2 * ((offset : ℤ) + 1) = exponent + 2 * offset + 2 by omega]
  have right (offset : ℕ) : rightTerm D hu (Pi.single colour 1) source vector
      (-(degree : ℤ) - 1) 0 exponent offset =
      ((degree + offset).choose degree : ℂ) •
        (nativeFirst D hu colour degree source exponent vector offset +
          (-1 : ℂ) ^ degree • nativeSecond D hu colour degree source exponent vector offset) := by
    rw [rightTerm]
    simp only [Int.cast_sub, Int.cast_neg, Int.cast_natCast, Int.cast_one,
      negative_binomial, descendant_phase, neg_smul, sub_neg_eq_add,
      nativeFirst_eq, nativeSecond_eq]
  rw [leftResidue, finsum_nat_split _
    (leftTerm_finite D hu (Pi.single colour 1) source vector (-(degree : ℤ) - 1) 0 exponent),
    zero] at identity
  simp_rw [tail] at identity
  rw [rightResidue] at identity
  simp_rw [right] at identity
  exact eq_sub_of_add_eq identity

end
end D5.S3.VertexAlgebra.SourceReconstruction.NativeDescendants
