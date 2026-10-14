/- GID: D5/S3/VertexAlgebra/LatticeSugawaraHermitian
   generality: G
   mirror-B: D5/B/S3/VertexAlgebra/LatticeSugawaraHermitian
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Real inverse-Gram and finite neutral Sugawara adjoints on the full carrier.
-/

import D5.S3.VertexAlgebra.LatticeChargedFockForms
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Tactic

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace D5.S3.VertexAlgebra.LatticeSugawaraHermitian

open LatticeGeneratingFieldLocality LatticeSugawaraCurrents LatticeChargedFockForms
open scoped BigOperators

noncomputable section

theorem inverse_gram_symmetric (D : LatticeData)
    (matrixH : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : matrixH * gramComplex D = 1) (hGH : gramComplex D * matrixH = 1) :
    matrixH.transpose = matrixH := by
  have gramSymmetric : (gramComplex D).transpose = gramComplex D := by
    ext first second
    change (D.G second first : ℂ) = (D.G first second : ℂ)
    exact_mod_cast D.symmetric second first
  have inverseLeft : matrixH.transpose * gramComplex D = 1 := by
    simpa only [Matrix.transpose_mul, gramSymmetric, Matrix.transpose_one] using
      congrArg Matrix.transpose hGH
  calc
    matrixH.transpose = matrixH.transpose * (gramComplex D * matrixH) := by rw [hGH, mul_one]
    _ = (matrixH.transpose * gramComplex D) * matrixH := by rw [mul_assoc]
    _ = matrixH := by rw [inverseLeft, one_mul]

theorem inverse_gram_real (D : LatticeData)
    (matrixH : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : matrixH * gramComplex D = 1) (hGH : gramComplex D * matrixH = 1)
    (first second : Fin D.rank) : star (matrixH first second) = matrixH first second := by
  have gramStar : star (gramComplex D) = gramComplex D := by
    ext row column
    simp [Matrix.star_apply, gramComplex, D.symmetric column row]
  have inverseRight : gramComplex D * star matrixH = 1 := by
    simpa only [star_mul, gramStar, star_one] using congrArg star hHG
  have equality : star matrixH = matrixH := by
    calc
      star matrixH = (matrixH * gramComplex D) * star matrixH := by rw [hHG, one_mul]
      _ = matrixH * (gramComplex D * star matrixH) := by rw [mul_assoc]
      _ = matrixH := by rw [inverseRight, mul_one]
  have coefficient := congrArg (fun matrix => matrix second first) equality
  change star (matrixH first second) = matrixH second first at coefficient
  exact coefficient.trans
    (congrArg (fun matrix => matrix first second) (inverse_gram_symmetric D matrixH hHG hGH))

private theorem normal_adjoint (D : LatticeData) (first second : Fin D.rank)
    (firstMode secondMode : ℤ) (left right : Carrier D) :
    hermitianForm D (normalSummand D first second firstMode secondMode left) right =
      hermitianForm D left (normalSummand D first second (-firstMode) (-secondMode) right) := by
  by_cases negative : firstMode < 0
  · have opposite : ¬ -firstMode < 0 := by omega
    simp only [normalSummand, if_pos negative, if_neg opposite, Module.End.mul_apply]
    rw [hermitian_neutral, hermitian_neutral]
  · by_cases positive : 0 < firstMode
    · have opposite : -firstMode < 0 := by omega
      simp only [normalSummand, if_neg negative, if_pos opposite, Module.End.mul_apply]
      rw [hermitian_neutral, hermitian_neutral]
    · have zero : firstMode = 0 := by omega
      subst firstMode
      simp only [normalSummand, lt_self_iff_false, if_false, neg_zero, Module.End.mul_apply]
      rw [hermitian_neutral, hermitian_neutral, neg_zero]
      have commutator := neutralMode_heisenberg D first second 0 (-secondMode)
      simp only [Int.cast_zero, zero_mul, ite_self, zero_smul, sub_eq_zero] at commutator
      exact congrArg (hermitianForm D left)
        (congrArg (fun operator : Module.End ℂ (Carrier D) => operator right) commutator)

private theorem mode_sum (D : LatticeData)
    (matrixH : Matrix (Fin D.rank) (Fin D.rank) ℂ) (mode : ℤ)
    (state : Carrier D) (radius : ℤ)
    (lower : -radius ≤ min 0 (mode - vectorFrequencyBound D state))
    (upper : (vectorFrequencyBound D state : ℤ) ≤ radius) :
    sugawaraMode D matrixH mode state = (2 : ℂ)⁻¹ •
      ∑ first : Fin D.rank, ∑ second : Fin D.rank, matrixH first second •
        ∑ index ∈ Finset.Icc (-radius) radius,
          normalSummand D first second index (mode-index) state := by
  classical
  rw [sugawaraMode_finsum]
  congr 1
  apply Finset.sum_congr rfl
  intro first memberFirst
  apply Finset.sum_congr rfl
  intro second memberSecond
  congr 1
  apply finsum_eq_sum_of_support_subset
  intro index member
  have bounds := normalSummand_support_interval D first second mode state member
  simpa only [Finset.mem_coe, Finset.mem_Icc] using
    And.intro (le_trans lower bounds.1) (le_trans bounds.2 upper)

theorem sugawara_adjoint (D : LatticeData)
    (matrixH : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : matrixH * gramComplex D = 1) (hGH : gramComplex D * matrixH = 1)
    (mode : ℤ) (left right : Carrier D) :
    hermitianForm D (sugawaraMode D matrixH mode left) right =
      hermitianForm D left (sugawaraMode D matrixH (-mode) right) := by
  classical
  let radius : ℤ := max (vectorFrequencyBound D left : ℤ)
    (vectorFrequencyBound D right : ℤ) + mode.natAbs + 1
  have boundLeft := le_max_left (vectorFrequencyBound D left : ℤ)
    (vectorFrequencyBound D right : ℤ)
  have boundRight := le_max_right (vectorFrequencyBound D left : ℤ)
    (vectorFrequencyBound D right : ℤ)
  have absolutePositive : mode ≤ (mode.natAbs : ℤ) := Int.le_natAbs
  have absoluteNegative : -mode ≤ (mode.natAbs : ℤ) := by
    simpa only [Int.natAbs_neg] using
      (Int.le_natAbs : -mode ≤ ((-mode).natAbs : ℤ))
  have nonnegativeLeft : (0 : ℤ) ≤ vectorFrequencyBound D left := by positivity
  have nonnegativeRight : (0 : ℤ) ≤ vectorFrequencyBound D right := by positivity
  have lowerLeft : -radius ≤ min 0 (mode-vectorFrequencyBound D left) := by
    dsimp [radius]
    omega
  have lowerRight : -radius ≤ min 0 (-mode-vectorFrequencyBound D right) := by
    dsimp [radius]
    omega
  have upperLeft : (vectorFrequencyBound D left : ℤ) ≤ radius := by dsimp [radius]; omega
  have upperRight : (vectorFrequencyBound D right : ℤ) ≤ radius := by dsimp [radius]; omega
  rw [mode_sum D matrixH mode left radius lowerLeft upperLeft,
    mode_sum D matrixH (-mode) right radius lowerRight upperRight]
  simp only [LinearMap.map_smulₛₗ, LinearMap.smul_apply, map_sum, LinearMap.sum_apply,
    starRingEnd_apply, star_inv₀, star_ofNat, smul_eq_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro first memberFirst
  apply Finset.sum_congr rfl
  intro second memberSecond
  rw [inverse_gram_real D matrixH hHG hGH]
  congr 1
  simp_rw [normal_adjoint]
  apply Finset.sum_bij (fun index _ => -index)
  · intro index member
    simp only [Finset.mem_Icc] at member ⊢
    omega
  · intro firstIndex memberFirstIndex secondIndex memberSecondIndex equal
    omega
  · intro index member
    refine ⟨-index, ?_, by omega⟩
    simp only [Finset.mem_Icc] at member ⊢
    omega
  · intro index member
    simp only [show -(mode - index) = -mode - -index by omega]

end
end D5.S3.VertexAlgebra.LatticeSugawaraHermitian
