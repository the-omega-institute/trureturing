/- GID: D5/S3/VertexAlgebra/LatticeHalfFockChargedLZero
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/LatticeHalfFockChargedLZero
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The original charged tensor coefficient has exact all-state L0 displacement (e+B(a,a))/2. -/

import D5.S3.Quantum.Algebra.WeightedPolynomialSubstitution
import D5.S3.VertexAlgebra.LatticeHalfFockChargedTensorCoefficients
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped BigOperators TensorProduct

namespace D5.S3.VertexAlgebra.HalfFockSpectralFiberSource
open LatticeGeneratingFieldLocality LatticeHalfFock

/-- Exact original inverse; no alternate Gram matrix or positivity restriction. -/
def actualInverse (D : LatticeData) : Matrix (Fin D.rank) (Fin D.rank) ℂ :=
  (D.G⁻¹).map (Int.castRingHom ℂ)

theorem actualInverse_left (D : LatticeData) (hu : IsUnit D.G.det) :
    actualInverse D * gramComplex D = 1 := by
  have h := congrArg (fun M : Matrix (Fin D.rank) (Fin D.rank) ℤ =>
    M.map (Int.castRingHom ℂ)) (Matrix.nonsing_inv_mul D.G hu)
  change (D.G⁻¹).map (Int.castRingHom ℂ) * D.G.map (Int.castRingHom ℂ) = 1
  rw [← Matrix.map_mul]
  simpa using h

theorem actualInverse_right (D : LatticeData) (hu : IsUnit D.G.det) :
    gramComplex D * actualInverse D = 1 := by
  have h := congrArg (fun M : Matrix (Fin D.rank) (Fin D.rank) ℤ =>
    M.map (Int.castRingHom ℂ)) (Matrix.mul_nonsing_inv D.G hu)
  change D.G.map (Int.castRingHom ℂ) * (D.G⁻¹).map (Int.castRingHom ℂ) = 1
  rw [← Matrix.map_mul]
  simpa using h

end D5.S3.VertexAlgebra.HalfFockSpectralFiberSource

namespace D5.S3.VertexAlgebra.LatticeHalfFockChargedLZero

open D5.S3.VertexAlgebra
open LatticeGeneratingFieldLocality LatticeHalfFockChargedCoefficients
open LatticeHalfFockChargedTensorCoefficients LatticeHalfFock
open D5.S3.Quantum.Algebra.WeightedPolynomialSubstitution

/-- The ORIGINAL translation variable has total odd weight. -/
private theorem halfTranslationVariable_totalWeight (D : LatticeData) (a : Charge D)
    (x : Index D) :
    HasTotalWeight (omega D) (halfTranslationVariable D a x) (omega D x) := by
  unfold halfTranslationVariable
  apply HasTotalWeight.sub
  · exact HasTotalWeight.C (MvPolynomial.isWeightedHomogeneous_X ℂ (omega D) x)
  · have hc : HasTotalWeight (omega D)
        (Polynomial.C ((bilinear D a (unitCharge D x.1) : ℂ) •
          (1 : Oscillator D))) 0 := by
      apply HasTotalWeight.C
      exact (MvPolynomial.weightedHomogeneousSubmodule ℂ (omega D) 0).smul_mem _
        (MvPolynomial.isWeightedHomogeneous_one ℂ (omega D))
    simpa only [Nat.zero_add] using hc.mul (HasTotalWeight.X_pow (omega D) (omega D x))

/-- The missing weighted-substitution inference for the original translation. -/
private theorem halfTranslatedPolynomial_totalWeight (D : LatticeData) (a : Charge D)
    (p : Oscillator D) (N : ℕ)
    (hp : MvPolynomial.IsWeightedHomogeneous (omega D) p N) :
    HasTotalWeight (omega D) (halfTranslatedPolynomial D a p) N := by
  exact eval2_totalWeight (omega D) (omega D) (halfTranslationVariable D a)
    (halfTranslationVariable_totalWeight D a) p N hp



/-- Signed lowering retains the negative-degree boundary in the statement. -/
private theorem translated_coefficient_lowering_int (D : LatticeData) (a : Charge D)
    (p : Oscillator D) (N r : ℕ)
    (hp : MvPolynomial.IsWeightedHomogeneous (omega D) p N) :
    MvPolynomial.IsWeightedHomogeneous (fun x => (omega D x : ℤ))
      ((halfTranslatedPolynomial D a p).coeff r) ((N : ℤ) - r) :=
  (halfTranslatedPolynomial_totalWeight D a p N hp).coeff_homogeneous_int r

/-- Existing creation grading, with the ORIGINAL signed-zero branch made
explicit. In particular a negative index never becomes a constant term. -/
private theorem halfCreationCoeff_homogeneous_int (D : LatticeData) (a : Charge D) (s : ℤ) :
    MvPolynomial.IsWeightedHomogeneous (fun x => (omega D x : ℤ))
      (halfCreationCoeff D a s) s := by
  by_cases hs : s < 0
  · rw [halfCreationCoeff, if_pos hs]
    exact MvPolynomial.isWeightedHomogeneous_zero ℂ _ _
  · have h := homogeneous_intCast (half_creation_coefficient_grading D a s)
    have hc : (s.toNat : ℤ) = s := Int.toNat_of_nonneg (by omega)
    simpa only [hc] using h

/-- Every ORIGINAL summand has the same signed displacement. The cover
degree r cancels: (N-r) + (e+q+r) = N+e+q. -/
private theorem oscillatorTerm_homogeneous_int (D : LatticeData) (a : Charge D)
    (e : ℤ) (p : Oscillator D) (N r : ℕ)
    (hp : MvPolynomial.IsWeightedHomogeneous (omega D) p N) :
    MvPolynomial.IsWeightedHomogeneous (fun x => (omega D x : ℤ))
      (oscillatorTerm D a e p r) ((N : ℤ) + e + chargeNorm D a) := by
  have h := (translated_coefficient_lowering_int D a p N r hp).mul
    (halfCreationCoeff_homogeneous_int D a (e + chargeNorm D a + r))
  rw [show (N : ℤ) - r + (e + chargeNorm D a + r) =
    (N : ℤ) + e + chargeNorm D a by omega] at h
  exact h



/-- Finite expansion from the existing support theorem, without any metric
or exchange-of-infinite-sums argument. -/
private theorem oscillatorCoefficient_eq_sum (D : LatticeData) (a : Charge D)
    (e : ℤ) (p : Oscillator D) :
    oscillatorCoefficient D a e p =
      ∑ r ∈ (halfTranslatedPolynomial D a p).support, oscillatorTerm D a e p r := by
  change (∑ᶠ r : ℕ, oscillatorTerm D a e p r) = _
  exact finsum_eq_sum_of_support_subset _ (term_support D a e p)

private theorem oscillatorCoefficient_homogeneous_int (D : LatticeData) (a : Charge D)
    (e : ℤ) (p : Oscillator D) (N : ℕ)
    (hp : MvPolynomial.IsWeightedHomogeneous (omega D) p N) :
    MvPolynomial.IsWeightedHomogeneous (fun x => (omega D x : ℤ))
      (oscillatorCoefficient D a e p) ((N : ℤ) + e + chargeNorm D a) := by
  rw [oscillatorCoefficient_eq_sum]
  apply MvPolynomial.IsWeightedHomogeneous.sum
  intro r _
  exact oscillatorTerm_homogeneous_int D a e p N r hp



/-- Normalizes the EXISTING half-frequency monomial spectrum. -/
private theorem halfEnergy_eq_signedOddWeight_half (D : LatticeData) (d : Index D →₀ ℕ) :
    (∑ x ∈ d.support, (d x : ℂ) * ((x.2 : ℂ) + 1 / 2)) =
      ((Finsupp.weight (fun x => (omega D x : ℤ)) d : ℤ) : ℂ) / 2 := by
  classical
  rw [weight_intCast, Int.cast_natCast]
  simp only [Finsupp.weight_apply, Finsupp.sum, nsmul_eq_mul, Nat.cast_id,
    Nat.cast_sum, Nat.cast_mul]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro x _
  simp only [omega]
  push_cast
  ring

/-- Derived from the original monomial theorem by polynomial expansion.
H is constrained only by its two inverse laws, never by a metric. -/
private theorem L_zero_of_homogeneous_int (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (p : Oscillator D) (z : ℤ)
    (hp : MvPolynomial.IsWeightedHomogeneous (fun x => (omega D x : ℤ)) p z) :
    L D H 0 p = ((D.rank : ℂ) / 16 + (z : ℂ) / 2) • p := by
  classical
  calc
    L D H 0 p = ∑ d ∈ p.support,
        L D H 0 (MvPolynomial.monomial d (p.coeff d)) := by
      conv_lhs => rw [MvPolynomial.as_sum p]
      rw [map_sum]
    _ = ∑ d ∈ p.support, ((D.rank : ℂ) / 16 + (z : ℂ) / 2) •
        MvPolynomial.monomial d (p.coeff d) := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [L_zero_monomial_coeff D H hHG hGH, halfEnergy_eq_signedOddWeight_half,
        hp (MvPolynomial.mem_support_iff.mp hd)]
    _ = ((D.rank : ℂ) / 16 + (z : ℂ) / 2) • p := by
      rw [← Finset.smul_sum, ← MvPolynomial.as_sum p]


/-- The original oscillator coefficient displaces energy by (e+q)/2. -/
private theorem oscillatorCoefficient_L_zero (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (a : Charge D) (e : ℤ) (p : Oscillator D) (N : ℕ)
    (hp : MvPolynomial.IsWeightedHomogeneous (omega D) p N) :
    L D H 0 (oscillatorCoefficient D a e p) =
      (((D.rank : ℂ) / 16 + (N : ℂ) / 2) +
        (((e + chargeNorm D a : ℤ) : ℂ) / 2)) • oscillatorCoefficient D a e p := by
  rw [L_zero_of_homogeneous_int D H hHG hGH _ _
    (oscillatorCoefficient_homogeneous_int D a e p N hp)]
  congr 1
  push_cast
  ring

private theorem oscillator_L_zero_commutator_homogeneous (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (a : Charge D) (e : ℤ) (p : Oscillator D) (N : ℕ)
    (hp : MvPolynomial.IsWeightedHomogeneous (omega D) p N) :
    L D H 0 (oscillatorCoefficient D a e p) -
      oscillatorCoefficient D a e (L D H 0 p) =
        (((e + chargeNorm D a : ℤ) : ℂ) / 2) • oscillatorCoefficient D a e p := by
  rw [oscillatorCoefficient_L_zero D H hHG hGH a e p N hp,
    L_zero_of_homogeneous_int D H hHG hGH p (N : ℤ) (homogeneous_intCast hp)]
  simp only [Int.cast_natCast, map_smul]
  rw [← sub_smul]
  congr 1
  ring

/-- ALL oscillator polynomials: finite monomial expansion and linearity
discharge the intermediate homogeneity premise. -/
private theorem oscillator_L_zero_commutator (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (a : Charge D) (e : ℤ) (p : Oscillator D) :
    L D H 0 (oscillatorCoefficient D a e p) -
      oscillatorCoefficient D a e (L D H 0 p) =
        (((e + chargeNorm D a : ℤ) : ℂ) / 2) • oscillatorCoefficient D a e p := by
  classical
  apply sub_eq_zero.mp
  change (L D H 0 * oscillatorCoefficient D a e - oscillatorCoefficient D a e * L D H 0 -
    (((e + chargeNorm D a : ℤ) : ℂ) / 2) • oscillatorCoefficient D a e) p = 0
  rw [MvPolynomial.as_sum p, map_sum]
  apply Finset.sum_eq_zero
  intro d _
  change (L D H 0 (oscillatorCoefficient D a e (MvPolynomial.monomial d
      (p.coeff d))) -
    oscillatorCoefficient D a e (L D H 0 (MvPolynomial.monomial d
      (p.coeff d)))) -
    (((e + chargeNorm D a : ℤ) : ℂ) / 2) •
      oscillatorCoefficient D a e (MvPolynomial.monomial d (p.coeff d)) = 0
  rw [oscillator_L_zero_commutator_homogeneous D H hHG hGH a e _
    (Finsupp.weight (omega D) d)
    (MvPolynomial.isWeightedHomogeneous_monomial (omega D) d _ rfl), sub_self]


/-- Tensor extension of the SAME original maps. GroundAction remains
opaque, and chargeScalar is retained on both sides. Tensor extensionality
proves a linear-map equality, so the conclusion includes every tensor state. -/
theorem charged_tensor_L_zero_commutator (D : LatticeData)
    (hu : IsUnit D.G.det) (a : Charge D) (e : ℤ) :
    tensorL D (ActualGround D hu) (HalfFockSpectralFiberSource.actualInverse D) 0 * chargedCoefficient D hu a e -
      chargedCoefficient D hu a e * tensorL D (ActualGround D hu) (HalfFockSpectralFiberSource.actualInverse D) 0 =
        (((e + bilinear D a a : ℤ) : ℂ) / 2) • chargedCoefficient D hu a e := by
  let H := HalfFockSpectralFiberSource.actualInverse D
  have hHG := HalfFockSpectralFiberSource.actualInverse_left D hu
  have hGH := HalfFockSpectralFiberSource.actualInverse_right D hu
  apply TensorProduct.ext'
  intro p t
  simp only [tensorL, tensorEnd, chargedCoefficient, Module.End.mul_apply,
    LinearMap.sub_apply, LinearMap.smul_apply, TensorProduct.map_tmul,
    LinearMap.id_apply, map_smul]
  rw [← smul_sub, ← TensorProduct.sub_tmul, oscillator_L_zero_commutator D H hHG hGH]
  change chargeScalar D a •
      ((((e + bilinear D a a : ℤ) : ℂ) / 2) •
        (oscillatorCoefficient D a e p ⊗ₜ[ℂ] groundAction D hu a t)) =
    (((e + bilinear D a a : ℤ) : ℂ) / 2) •
      (chargeScalar D a •
        (oscillatorCoefficient D a e p ⊗ₜ[ℂ] groundAction D hu a t))
  exact smul_comm _ _ _



/-- Tensor-current zero-mode commutator for the original actual inverse.
This is consumed by ActualEnergyCovariance's induction through both normal
ordering branches. The existing private inverse witnesses stay in this file. -/
theorem tensor_current_L_zero_commutator (D : LatticeData)
    (hu : IsUnit D.G.det) (i : Fin D.rank) (k : ℤ) :
    tensorL D (ActualGround D hu) (HalfFockSpectralFiberSource.actualInverse D) 0 *
        tensorCurrent D (ActualGround D hu) i k -
      tensorCurrent D (ActualGround D hu) i k *
        tensorL D (ActualGround D hu) (HalfFockSpectralFiberSource.actualInverse D) 0 =
      -frequency k • tensorCurrent D (ActualGround D hu) i k := by
  apply TensorProduct.ext'
  intro p t
  have hc := LinearMap.congr_fun
    (L_current_commutator D (HalfFockSpectralFiberSource.actualInverse D)
      (HalfFockSpectralFiberSource.actualInverse_left D hu)
      (HalfFockSpectralFiberSource.actualInverse_right D hu) i 0 k) p
  simp only [zero_add, Module.End.mul_apply, LinearMap.sub_apply,
    LinearMap.smul_apply] at hc
  simp only [tensorL, tensorCurrent, tensorEnd, Module.End.mul_apply,
    LinearMap.sub_apply, LinearMap.smul_apply, TensorProduct.map_tmul,
    LinearMap.id_apply]
  rw [← TensorProduct.sub_tmul, hc, TensorProduct.smul_tmul']

end D5.S3.VertexAlgebra.LatticeHalfFockChargedLZero
