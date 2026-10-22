/- GID: D5/S3/VertexAlgebra/LatticeHalfFockNativeSpectrum/Integral
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/LatticeHalfFockNativeSpectrum/Integral
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual oscillator parity and the native integral spectral sector. -/

import D5.S3.VertexAlgebra.LatticeHalfFockNativeSpectrum.Grading

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace D5.S3.VertexAlgebra.LatticeHalfFockNativeSpectrum

open LatticeGeneratingFieldLocality LatticeHalfFock LatticeHalfFockChargedTensorCoefficients
open MvPolynomial
open scoped BigOperators TensorProduct

noncomputable section

theorem occupation_sign (D : LatticeData) (exponent : Occupation D) :
    (-1 : ℂ) ^ (LatticeAllStateField.occurrences D exponent).length =
      (-1 : ℂ) ^ occupationWeight D exponent := by
  classical
  have count : (LatticeAllStateField.occurrences D exponent).length = Finsupp.degree exponent := by
    simp [LatticeAllStateField.occurrences, Finsupp.degree_apply, Finsupp.card_toMultiset,
      Finsupp.sum]
  have decomposition : occupationWeight D exponent =
      2 * Finsupp.weight (fun index : Index D => index.2) exponent + Finsupp.degree exponent := by
    simp only [occupationWeight, Finsupp.weight_apply, Finsupp.degree_apply, Finsupp.sum,
      smul_eq_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro index member
    ring
  rw [count, decomposition, pow_add, pow_mul]
  norm_num

def oscillatorNegation (D : LatticeData) (hu : IsUnit D.G.det) : Module.End ℂ (ActualTensor D hu) :=
  TensorProduct.map (LatticeInvolution.sigmaLinear D) LinearMap.id

theorem coefficient_parity (D : LatticeData) (hu : IsUnit D.G.det)
    (state : ActualTensor D hu) (exponent : Occupation D) :
    coefficients D hu (oscillatorNegation D hu state) exponent =
      (-1 : ℂ) ^ occupationWeight D exponent • coefficients D hu state exponent := by
  classical
  induction state using TensorProduct.induction_on with
  | zero => simp
  | add left right left_proof right_proof =>
      simp only [map_add, Finsupp.add_apply, smul_add, left_proof, right_proof]
  | tmul polynomial ground =>
      induction polynomial using MvPolynomial.induction_on' with
      | add left right left_proof right_proof =>
          simp only [TensorProduct.add_tmul, map_add, Finsupp.add_apply, smul_add,
            left_proof, right_proof]
      | monomial degree scalar =>
          have monomial_scalar : monomial degree scalar = scalar • monomial degree (1 : ℂ) := by
            simp [smul_monomial, smul_eq_mul]
          simp only [oscillatorNegation, TensorProduct.map_tmul, LinearMap.id_apply]
          change coefficients D hu (LatticeInvolution.sigma D (monomial degree scalar) ⊗ₜ[ℂ] ground)
            exponent = _
          rw [monomial_scalar, LatticeInvolution.sigma_smul, LatticeInvolution.sigma_monomial,
            occupation_sign]
          rw [← TensorProduct.smul_tmul', map_smul, ← TensorProduct.smul_tmul', map_smul]
          simp only [Finsupp.coe_smul, Pi.smul_apply,
            coefficients_tmul, coeff_monomial]
          by_cases equality : degree = exponent
          · subst degree
            simp only [coeff_smul, coeff_monomial, ite_true, smul_eq_mul, mul_one, one_smul]
            exact smul_comm scalar ((-1 : ℂ) ^ occupationWeight D exponent) ground
          · simp [equality, coeff_smul]

def oddSector (D : LatticeData) (hu : IsUnit D.G.det) : Submodule ℂ (ActualTensor D hu) :=
  LinearMap.ker (oscillatorNegation D hu + LinearMap.id)

theorem odd_support_iff (D : LatticeData) (hu : IsUnit D.G.det) (state : ActualTensor D hu) :
    state ∈ oddSector D hu ↔
      ∀ exponent, Even (occupationWeight D exponent) → coefficients D hu state exponent = 0 := by
  classical
  change oscillatorNegation D hu state + state = 0 ↔ _
  constructor
  · intro zero exponent even
    have coordinate := congrArg (fun vector => coefficients D hu vector exponent) zero
    simp only [map_add, map_zero, Finsupp.add_apply, Finsupp.zero_apply,
      coefficient_parity, even.neg_one_pow, one_smul] at coordinate
    have two : (2 : ℂ) • coefficients D hu state exponent = 0 := by
      simpa [two_smul] using coordinate
    exact (smul_eq_zero.mp two).resolve_left (by norm_num)
  · intro support
    apply (coefficients D hu).injective
    apply Finsupp.ext
    intro exponent
    simp only [map_add, map_zero, Finsupp.add_apply, Finsupp.zero_apply, coefficient_parity]
    by_cases even : Even (occupationWeight D exponent)
    · simp [support exponent even]
    · simp [neg_one_pow_eq_ite, even]

theorem integer_weight_iff (D : LatticeData) (rank24 : D.rank = 24) (level : ℕ) (value : ℤ) :
    weightValue D level = (value : ℂ) ↔ (level : ℤ) = 2 * value - 3 := by
  constructor
  · intro equality
    have cast : (level : ℂ) = 2 * (value : ℂ) - 3 := by
      simp only [weightValue, rank24] at equality
      linear_combination 2 * equality
    exact_mod_cast cast
  · intro equality
    have cast : (level : ℂ) = 2 * (value : ℂ) - 3 := by exact_mod_cast equality
    simp only [weightValue, rank24]
    linear_combination cast / 2

theorem integer_eigen_odd (D : LatticeData) (hu : IsUnit D.G.det)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (rank24 : D.rank = 24) (value : ℤ) :
    eigenspace D hu H (value : ℂ) ≤ oddSector D hu := by
  intro state homogeneous
  rw [odd_support_iff]
  intro exponent even
  apply (eigen_support_iff D hu H hHG hGH _ state).mp homogeneous exponent
  intro equality
  have integer := (integer_weight_iff D rank24 _ value).mp equality
  simp only [Nat.even_iff] at even
  omega

theorem integer_below_two (D : LatticeData) (hu : IsUnit D.G.det)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (rank24 : D.rank = 24) (value : ℤ) (below : value < 2) :
    eigenspace D hu H (value : ℂ) = ⊥ := by
  apply eq_bot_iff.mpr
  intro state homogeneous
  change state = 0
  apply (coefficients D hu).injective
  apply Finsupp.ext
  intro exponent
  simp only [map_zero, Finsupp.zero_apply]
  apply (eigen_support_iff D hu H hHG hGH _ state).mp homogeneous exponent
  intro equality
  have integer := (integer_weight_iff D rank24 _ value).mp equality
  omega

theorem integral_supremum (D : LatticeData) (hu : IsUnit D.G.det)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (rank24 : D.rank = 24) :
    (⨆ value : ℤ, eigenspace D hu H (value : ℂ)) = oddSector D hu := by
  classical
  apply le_antisymm
  · exact iSup_le (integer_eigen_odd D hu H hHG hGH rank24)
  · intro state odd_state
    have odd_support := (odd_support_iff D hu state).mp odd_state
    rw [← finite_reconstruction D hu state]
    apply Submodule.sum_mem
    intro level member
    by_cases even : Even level
    · have zero : naturalProjector D hu level state = 0 := by
        apply (coefficients D hu).injective
        apply Finsupp.ext
        intro exponent
        simp only [coefficient_projector, map_zero, Finsupp.zero_apply]
        by_cases equal : occupationWeight D exponent = level
        · simp [equal, odd_support exponent (equal.symm ▸ even)]
        · simp [equal]
      rw [zero]
      exact Submodule.zero_mem _
    · let value : ℤ := ((level : ℤ) + 3) / 2
      have integer : (level : ℤ) = 2 * value - 3 := by
        simp only [Nat.even_iff] at even
        dsimp [value]
        omega
      have equality := (integer_weight_iff D rank24 level value).mpr integer
      have homogeneous := projector_eigen D hu H hHG hGH level state
      rw [equality] at homogeneous
      exact (le_iSup (fun value : ℤ => eigenspace D hu H (value : ℂ)) value) homogeneous

end
end D5.S3.VertexAlgebra.LatticeHalfFockNativeSpectrum
