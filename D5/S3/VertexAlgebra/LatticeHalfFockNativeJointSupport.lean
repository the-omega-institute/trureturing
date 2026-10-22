/- GID: D5/S3/VertexAlgebra/LatticeHalfFockNativeJointSupport
   generality: G
   mirror-B: D5/B/S3/VertexAlgebra/LatticeHalfFockNativeJointSupport
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A single dependent finite support packages native shifts, oscillator monomials, and signed split modes without exchanging unsupported sums. -/

import D5.S3.VertexAlgebra.LatticeHalfFockNativeNormalActions
import Mathlib.Data.Finset.Sigma
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

namespace D5.S3.VertexAlgebra.LatticeHalfFockNativeJointSupport

open LatticeGeneratingFieldLocality LatticeHalfFockChargedTensorCoefficients
open LatticeHalfFockFiniteCorrection
open LatticeHalfFockFockNormalField LatticeHalfFockNativeNormalActions
open LatticeHalfFockScalarLabelledGaussian MvPolynomial
open scoped BigOperators TensorProduct

noncomputable section

abbrev NativeModeIndex (D : LatticeData) :=
  Σ shift : ℕ, Σ monomial : Index D →₀ ℕ,
    ModeTuple D (LatticeAllStateField.occurrences D monomial)

def nativeModeTerm (D : LatticeData) (hu : IsUnit D.G.det) (charge : Charge D)
    (source : CorrectionPolynomial D) (exponent : ℤ) (polynomial : Oscillator D)
    (state : ActualTensor D hu) (index : NativeModeIndex D) : ActualTensor D hu :=
  MvPolynomial.coeff index.2.1 (correctionCoefficients D source index.1) •
    normalSplitCoefficient D hu charge
      (LatticeAllStateField.occurrences D index.2.1) (exponent + 2 * index.1)
      polynomial index.2.2 state

theorem actual_native_correction_joint_finite_action (D : LatticeData)
    (hu : IsUnit D.G.det) (charge : Charge D)
    (source : CorrectionPolynomial D) (exponent : ℤ) (polynomial : Oscillator D)
    (state : ActualTensor D hu) :
    ∃ finiteModes : Finset (NativeModeIndex D),
      (∀ index ∉ finiteModes, nativeModeTerm D hu charge source exponent polynomial state index = 0) ∧
      (nativeCorrectionEvaluation D hu charge source).coeff exponent
          (tensorMultiply D hu polynomial state) =
        ∑ index ∈ finiteModes, nativeModeTerm D hu charge source exponent polynomial state index := by
  classical
  choose modeWitness modeOutside modeExpansion using
    (actual_native_correction_finite_action D hu charge source exponent polynomial state)
  let finiteModes : Finset (NativeModeIndex D) :=
    (correctionCoefficients D source).support.sigma (fun shift =>
      (correctionCoefficients D source shift).support.sigma (fun monomial =>
        modeWitness shift monomial))
  refine ⟨finiteModes, ?_, ?_⟩
  · intro index outside
    rcases index with ⟨shift, monomial, modes⟩
    have outside' : ¬ (shift ∈ (correctionCoefficients D source).support ∧
        monomial ∈ (correctionCoefficients D source shift).support ∧
          modes ∈ modeWitness shift monomial) := by
      simpa only [finiteModes, Finset.mem_sigma] using outside
    by_cases shiftMember : shift ∈ (correctionCoefficients D source).support
    · by_cases monomialMember : monomial ∈ (correctionCoefficients D source shift).support
      · have outsideModes : modes ∉ modeWitness shift monomial := by
          intro member
          exact outside' ⟨shiftMember, monomialMember, member⟩
        rw [nativeModeTerm, modeOutside shift shiftMember monomial monomialMember modes
          outsideModes, smul_zero]
      · have coefficientZero :
            MvPolynomial.coeff monomial (correctionCoefficients D source shift) = 0 := by
          by_contra nonzero
          exact monomialMember (Finsupp.mem_support_iff.mpr nonzero)
        simp [nativeModeTerm, coefficientZero]
    · have shiftZero : correctionCoefficients D source shift = 0 := by
        exact Finsupp.notMem_support_iff.mp shiftMember
      simp [nativeModeTerm, shiftZero]
  · rw [modeExpansion]
    calc
      (∑ shift ∈ (correctionCoefficients D source).support,
      ∑ monomial ∈ (correctionCoefficients D source shift).support,
        MvPolynomial.coeff monomial (correctionCoefficients D source shift) •
          ∑ modes ∈ modeWitness shift monomial,
            normalSplitCoefficient D hu charge
              (LatticeAllStateField.occurrences D monomial) (exponent + 2 * shift)
              polynomial modes state) =
        ∑ shift ∈ (correctionCoefficients D source).support,
          ∑ monomial ∈ (correctionCoefficients D source shift).support,
            ∑ modes ∈ modeWitness shift monomial,
              MvPolynomial.coeff monomial (correctionCoefficients D source shift) •
                normalSplitCoefficient D hu charge
                  (LatticeAllStateField.occurrences D monomial) (exponent + 2 * shift)
                  polynomial modes state := by
        apply Finset.sum_congr rfl
        intro shift shiftMember
        apply Finset.sum_congr rfl
        intro monomial monomialMember
        rw [Finset.smul_sum]
      _ = ∑ shift ∈ (correctionCoefficients D source).support,
          ∑ index ∈ (correctionCoefficients D source shift).support.sigma
              (fun monomial => modeWitness shift monomial),
            MvPolynomial.coeff index.1 (correctionCoefficients D source shift) •
              normalSplitCoefficient D hu charge
                (LatticeAllStateField.occurrences D index.1) (exponent + 2 * shift)
                polynomial index.2 state := by
        apply Finset.sum_congr rfl
        intro shift shiftMember
        rw [Finset.sum_sigma']
      _ = ∑ index ∈ finiteModes, nativeModeTerm D hu charge source exponent polynomial state index := by
        rw [Finset.sum_sigma']
        simp only [finiteModes, nativeModeTerm]

end

end D5.S3.VertexAlgebra.LatticeHalfFockNativeJointSupport

#print axioms D5.S3.VertexAlgebra.LatticeHalfFockNativeJointSupport.actual_native_correction_joint_finite_action
