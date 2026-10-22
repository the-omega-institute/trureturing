/- GID: D5/S3/VertexAlgebra/LatticeHalfFockTargetThetaChargedWeight
   generality: G
   mirror-B: D5/B/S3/VertexAlgebra/LatticeHalfFockTargetThetaChargedWeight
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Consumed exact original suppliers with checked private visibility bridges. -/

import D5.S3.VertexAlgebra.LatticeHalfFockTargetThetaCoefficients
import Mathlib.LinearAlgebra.TensorProduct.Map
import Mathlib.Tactic.Module

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

namespace D5.S3.VertexAlgebra.LatticeHalfFock

run_cmd
  let supplier := (Lean.Name.num `_private.D5.S3.VertexAlgebra.LatticeHalfFockVirasoroSpectrum 0).append
    `D5.S3.VertexAlgebra.LatticeHalfFock.L_zero_X_mul
  Lean.Elab.Command.elabCommand
    (← `(noncomputable abbrev $(Lean.mkIdent `L_zero_X_mul) := @$(Lean.mkIdent supplier)))

end D5.S3.VertexAlgebra.LatticeHalfFock

namespace D5.S3.VertexAlgebra.LatticeHalfFockChargedTensorCoefficients

run_cmd
  let supplier := (Lean.Name.num `_private.D5.S3.VertexAlgebra.LatticeHalfFockChargedTensorCoefficients 0).append
    `D5.S3.VertexAlgebra.LatticeHalfFockChargedTensorCoefficients.nativeCoefficientMap
  Lean.Elab.Command.elabCommand
    (← `(noncomputable abbrev $(Lean.mkIdent `nativeCoefficientMap) := @$(Lean.mkIdent supplier)))

run_cmd
  let supplier := (Lean.Name.num `_private.D5.S3.VertexAlgebra.LatticeHalfFockChargedTensorCoefficients 0).append
    `D5.S3.VertexAlgebra.LatticeHalfFockChargedTensorCoefficients.nativeCoefficientMap_monomial
  Lean.Elab.Command.elabCommand
    (← `(noncomputable abbrev $(Lean.mkIdent `nativeCoefficientMap_monomial) := @$(Lean.mkIdent supplier)))

run_cmd
  let supplier := (Lean.Name.num `_private.D5.S3.VertexAlgebra.LatticeHalfFockChargedTensorCoefficients 0).append
    `D5.S3.VertexAlgebra.LatticeHalfFockChargedTensorCoefficients.oscillatorCoefficient_as_sum
  Lean.Elab.Command.elabCommand
    (← `(noncomputable abbrev $(Lean.mkIdent `oscillatorCoefficient_as_sum) := @$(Lean.mkIdent supplier)))

run_cmd
  let supplier := (Lean.Name.num `_private.D5.S3.VertexAlgebra.LatticeHalfFockChargedTensorCoefficients 0).append
    `D5.S3.VertexAlgebra.LatticeHalfFockChargedTensorCoefficients.oscillatorCoefficient_X_mul
  Lean.Elab.Command.elabCommand
    (← `(noncomputable abbrev $(Lean.mkIdent `oscillatorCoefficient_X_mul) := @$(Lean.mkIdent supplier)))


open LatticeGeneratingFieldLocality LatticeHalfFockChargedCoefficients
open scoped BigOperators TensorProduct

noncomputable section

private theorem homogeneous_energy (D : LatticeData)
    (matrixH : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : matrixH * LatticeSugawaraCurrents.gramComplex D = 1)
    (hGH : LatticeSugawaraCurrents.gramComplex D * matrixH = 1)
    (polynomial : Oscillator D) (weight : ℕ)
    (homogeneous : MvPolynomial.IsWeightedHomogeneous (omega D) polynomial weight) :
    LatticeHalfFock.L D matrixH 0 polynomial =
      ((D.rank : ℂ) / 16 + (weight : ℂ) / 2) • polynomial := by
  classical
  conv_lhs => rw [MvPolynomial.as_sum polynomial]
  rw [map_sum]
  calc
    _ = ∑ exponent ∈ polynomial.support,
        ((D.rank : ℂ) / 16 + (weight : ℂ) / 2) •
          MvPolynomial.monomial exponent (MvPolynomial.coeff exponent polynomial) := by
      apply Finset.sum_congr rfl
      intro exponent hexponent
      rw [LatticeHalfFock.L_zero_monomial_coeff D matrixH hHG hGH]
      have energy : (∑ index ∈ exponent.support,
          (exponent index : ℂ) * ((index.2 : ℂ) + 1 / 2)) =
          (Finsupp.weight (omega D) exponent : ℂ) / 2 := by
        simp only [Finsupp.weight_apply, Finsupp.sum, nsmul_eq_mul, Nat.cast_sum,
          Nat.cast_mul, omega, Nat.cast_add, Nat.cast_ofNat, Nat.cast_id,
          div_eq_mul_inv, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro index hindex
        ring
      rw [energy, homogeneous (MvPolynomial.mem_support_iff.mp hexponent)]
    _ = _ := by rw [← Finset.smul_sum, ← MvPolynomial.as_sum polynomial]

private theorem creation_energy (D : LatticeData)
    (matrixH : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : matrixH * LatticeSugawaraCurrents.gramComplex D = 1)
    (hGH : LatticeSugawaraCurrents.gramComplex D * matrixH = 1)
    (charge : Charge D) (degree : ℤ) :
    LatticeHalfFock.L D matrixH 0 (halfCreationCoeff D charge degree) =
      ((D.rank : ℂ) / 16 + (degree : ℂ) / 2) • halfCreationCoeff D charge degree := by
  by_cases negative : degree < 0
  · simp [halfCreationCoeff, negative]
  have graded := homogeneous_energy D matrixH hHG hGH _ _
    (half_creation_coefficient_grading D charge degree)
  have weight : (degree.toNat : ℂ) = (degree : ℂ) := by
    exact_mod_cast Int.toNat_of_nonneg (by omega : 0 ≤ degree)
  simpa only [weight] using graded

private theorem oscillatorCoefficient_one (D : LatticeData) (charge : Charge D) (exponent : ℤ) :
    oscillatorCoefficient D charge exponent (1 : Oscillator D) =
      halfCreationCoeff D charge (exponent + chargeNorm D charge) := by
  rw [oscillatorCoefficient_as_sum]
  have translated : halfTranslatedPolynomial D charge (1 : Oscillator D) = 1 :=
    map_one (MvPolynomial.eval₂AlgHom ℂ (halfTranslationVariable D charge))
  rw [translated]
  change nativeCoefficientMap D charge exponent (Polynomial.monomial 0 1) = _
  rw [nativeCoefficientMap_monomial]
  simp

private theorem oscillator_constant_L0 (D : LatticeData)
    (matrixH : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : matrixH * LatticeSugawaraCurrents.gramComplex D = 1)
    (hGH : LatticeSugawaraCurrents.gramComplex D * matrixH = 1)
    (charge : Charge D) (scalar : ℂ) (exponent : ℤ) :
    LatticeHalfFock.L D matrixH 0
        (oscillatorCoefficient D charge exponent (MvPolynomial.C scalar)) =
      oscillatorCoefficient D charge exponent
        (LatticeHalfFock.L D matrixH 0 (MvPolynomial.C scalar)) +
        (((exponent + chargeNorm D charge : ℤ) : ℂ) / 2) •
          oscillatorCoefficient D charge exponent (MvPolynomial.C scalar) := by
  have output : oscillatorCoefficient D charge exponent (MvPolynomial.C scalar) =
      scalar • halfCreationCoeff D charge (exponent + chargeNorm D charge) := by
    rw [MvPolynomial.C_eq_smul_one, map_smul, oscillatorCoefficient_one]
  have input : LatticeHalfFock.L D matrixH 0 (MvPolynomial.C scalar) =
      ((D.rank : ℂ) / 16) • (MvPolynomial.C scalar : Oscillator D) := by
    simpa using LatticeHalfFock.L_zero_monomial_coeff D matrixH hHG hGH 0 scalar
  simp only [input, map_smul, output,
    creation_energy D matrixH hHG hGH, smul_add, smul_smul]
  module

private theorem oscillator_L0_covariance (D : LatticeData)
    (matrixH : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : matrixH * LatticeSugawaraCurrents.gramComplex D = 1)
    (hGH : LatticeSugawaraCurrents.gramComplex D * matrixH = 1)
    (charge : Charge D) (polynomial : Oscillator D) :
    ∀ exponent : ℤ,
      LatticeHalfFock.L D matrixH 0 (oscillatorCoefficient D charge exponent polynomial) =
        oscillatorCoefficient D charge exponent (LatticeHalfFock.L D matrixH 0 polynomial) +
          (((exponent + chargeNorm D charge : ℤ) : ℂ) / 2) •
            oscillatorCoefficient D charge exponent polynomial := by
  classical
  induction polynomial using MvPolynomial.induction_on with
  | C scalar =>
    intro exponent
    exact oscillator_constant_L0 D matrixH hHG hGH charge scalar exponent
  | add left right hleft hright =>
    intro exponent
    simp only [map_add, hleft exponent, hright exponent, smul_add]
    abel
  | mul_X polynomial index inductionHypothesis =>
    intro exponent
    rw [mul_comm polynomial (MvPolynomial.X index)]
    simp only [oscillatorCoefficient_X_mul, map_sub,
      LatticeHalfFock.L_zero_X_mul D matrixH hHG hGH, map_smul, map_add,
      inductionHypothesis exponent, inductionHypothesis (exponent + omega D index), mul_add, mul_sub,
      mul_smul_comm, smul_add, smul_sub, smul_smul]
    simp only [Int.cast_add, Int.cast_natCast, omega, Nat.cast_add, Nat.cast_mul,
      Nat.cast_ofNat]
    module

private theorem oscillator_L0_operator (D : LatticeData)
    (matrixH : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : matrixH * LatticeSugawaraCurrents.gramComplex D = 1)
    (hGH : LatticeSugawaraCurrents.gramComplex D * matrixH = 1)
    (charge : Charge D) (exponent : ℤ) :
      LatticeHalfFock.L D matrixH 0 * oscillatorCoefficient D charge exponent =
        oscillatorCoefficient D charge exponent * LatticeHalfFock.L D matrixH 0 +
          (((exponent + chargeNorm D charge : ℤ) : ℂ) / 2) •
            oscillatorCoefficient D charge exponent := by
  apply LinearMap.ext
  intro polynomial
  exact oscillator_L0_covariance D matrixH hHG hGH charge polynomial exponent

private theorem tensor_L0_sum (D : LatticeData) (hu : IsUnit D.G.det)
    (matrixH : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : matrixH * LatticeSugawaraCurrents.gramComplex D = 1)
    (hGH : LatticeSugawaraCurrents.gramComplex D * matrixH = 1)
    (charge : Charge D) (exponent : ℤ) :
    TensorProduct.map (LatticeHalfFock.L D matrixH 0 * oscillatorCoefficient D charge exponent)
        (groundAction D hu charge) =
      TensorProduct.map (oscillatorCoefficient D charge exponent * LatticeHalfFock.L D matrixH 0)
        (groundAction D hu charge) +
        (((exponent + chargeNorm D charge : ℤ) : ℂ) / 2) •
          TensorProduct.map (oscillatorCoefficient D charge exponent) (groundAction D hu charge) := by
  have tensored := congrArg (fun operator : Module.End ℂ (Oscillator D) =>
    TensorProduct.map operator (groundAction D hu charge))
      (oscillator_L0_operator D matrixH hHG hGH charge exponent)
  simpa only [TensorProduct.map_add_left, TensorProduct.map_smul_left] using tensored

private theorem tensor_map_left_product (D : LatticeData) (hu : IsUnit D.G.det)
    (matrixH : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (charge : Charge D) (exponent : ℤ) :
    TensorProduct.map (LatticeHalfFock.L D matrixH 0 * oscillatorCoefficient D charge exponent)
        (groundAction D hu charge) =
      LatticeHalfFock.tensorL D (ActualGround D hu) matrixH 0 *
        TensorProduct.map (oscillatorCoefficient D charge exponent) (groundAction D hu charge) := by
  apply TensorProduct.ext'
  intro polynomial vector
  simp only [LatticeHalfFock.tensorL, LatticeHalfFock.tensorEnd,
    Module.End.mul_apply, TensorProduct.map_tmul, LinearMap.id_apply]

private theorem tensor_map_right_product (D : LatticeData) (hu : IsUnit D.G.det)
    (matrixH : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (charge : Charge D) (exponent : ℤ) :
    TensorProduct.map (oscillatorCoefficient D charge exponent * LatticeHalfFock.L D matrixH 0)
        (groundAction D hu charge) =
      TensorProduct.map (oscillatorCoefficient D charge exponent) (groundAction D hu charge) *
        LatticeHalfFock.tensorL D (ActualGround D hu) matrixH 0 := by
  apply TensorProduct.ext'
  intro polynomial vector
  simp only [LatticeHalfFock.tensorL, LatticeHalfFock.tensorEnd,
    Module.End.mul_apply, TensorProduct.map_tmul, LinearMap.id_apply]

private theorem tensor_unscaled_L0 (D : LatticeData) (hu : IsUnit D.G.det)
    (matrixH : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : matrixH * LatticeSugawaraCurrents.gramComplex D = 1)
    (hGH : LatticeSugawaraCurrents.gramComplex D * matrixH = 1)
    (charge : Charge D) (exponent : ℤ) :
    LatticeHalfFock.tensorL D (ActualGround D hu) matrixH 0 *
        TensorProduct.map (oscillatorCoefficient D charge exponent) (groundAction D hu charge) =
      TensorProduct.map (oscillatorCoefficient D charge exponent) (groundAction D hu charge) *
        LatticeHalfFock.tensorL D (ActualGround D hu) matrixH 0 +
        (((exponent + chargeNorm D charge : ℤ) : ℂ) / 2) •
          TensorProduct.map (oscillatorCoefficient D charge exponent) (groundAction D hu charge) := by
  have tensored := tensor_L0_sum D hu matrixH hHG hGH charge exponent
  rw [tensor_map_left_product, tensor_map_right_product] at tensored
  exact tensored

theorem charged_tensor_L0_covariance (D : LatticeData) (hu : IsUnit D.G.det)
    (matrixH : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : matrixH * LatticeSugawaraCurrents.gramComplex D = 1)
    (hGH : LatticeSugawaraCurrents.gramComplex D * matrixH = 1)
    (charge : Charge D) (exponent : ℤ) (state : ActualTensor D hu) :
    LatticeHalfFock.tensorL D (ActualGround D hu) matrixH 0
        (chargedCoefficient D hu charge exponent state) =
      chargedCoefficient D hu charge exponent
        (LatticeHalfFock.tensorL D (ActualGround D hu) matrixH 0 state) +
      (((exponent + chargeNorm D charge : ℤ) : ℂ) / 2) •
        chargedCoefficient D hu charge exponent state := by
  have tensored := tensor_unscaled_L0 D hu matrixH hHG hGH charge exponent
  have full :
      LatticeHalfFock.tensorL D (ActualGround D hu) matrixH 0 *
          chargedCoefficient D hu charge exponent =
        chargedCoefficient D hu charge exponent *
          LatticeHalfFock.tensorL D (ActualGround D hu) matrixH 0 +
        (((exponent + chargeNorm D charge : ℤ) : ℂ) / 2) •
          chargedCoefficient D hu charge exponent := by
    dsimp only [chargedCoefficient]
    rw [mul_smul_comm, smul_mul_assoc, tensored, smul_add]
    module
  exact congrArg (fun operator : Module.End ℂ (ActualTensor D hu) => operator state) full


end
end D5.S3.VertexAlgebra.LatticeHalfFockChargedTensorCoefficients
