/- GID: D5/S3/VertexAlgebra/LatticeHalfFockTargetThetaCovariance
   generality: G
   mirror-B: D5/B/S3/VertexAlgebra/LatticeHalfFockTargetThetaCovariance
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Consumed exact original suppliers with checked private visibility bridges. -/

import D5.S3.VertexAlgebra.LatticeHalfFockConformalIdentification
import D5.S3.VertexAlgebra.LatticeHalfFockTargetThetaChargedWeight
import D5.S3.VertexAlgebra.LatticeHalfFockTargetThetaCorrectionWeight
import Mathlib.Tactic.Module
import Mathlib.LinearAlgebra.Eigenspace.Basic

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

namespace D5.S3.VertexAlgebra.LatticeHalfFockLZeroCovariance

run_cmd
  let supplier := (Lean.Name.num `_private.D5.S3.VertexAlgebra.LatticeSugawaraConformal 0).append
    `D5.S3.VertexAlgebra.LatticeSugawaraConformal.oscillatorEuler_monomial
  Lean.Elab.Command.elabCommand
    (← `(noncomputable abbrev $(Lean.mkIdent `oscillatorEuler_monomial) := @$(Lean.mkIdent supplier)))

run_cmd
  let supplier := (Lean.Name.num `_private.D5.S3.VertexAlgebra.LatticeHalfFockFiniteCorrection 0).append
    `D5.S3.VertexAlgebra.LatticeHalfFockFiniteCorrection.wordWeight_occurrences
  Lean.Elab.Command.elabCommand
    (← `(noncomputable abbrev $(Lean.mkIdent `wordWeight_occurrences) := @$(Lean.mkIdent supplier)))


open LatticeGeneratingFieldLocality LatticeHalfFockChargedTensorCoefficients
open LatticeHalfFockFiniteCorrection LatticeHalfFockFockNormalField
open LatticeHalfFockAllStateField LatticeHalfFockCorrectionGrading
open LatticeSugawaraConformal LatticeFiniteNegativeGeneration
open LatticeSugawaraVirasoro
open LatticeSugawaraCurrents MvPolynomial
open scoped BigOperators

noncomputable section

variable (D : LatticeData) (hu : IsUnit D.G.det)
variable (matrixH : Matrix (Fin D.rank) (Fin D.rank) ℂ)
variable (hHG : matrixH * gramComplex D = 1) (hGH : gramComplex D * matrixH = 1)

include hHG hGH in
private theorem tensor_current_L0 (colour : Fin D.rank) (mode : ℤ)
    (vector : ActualTensor D hu) :
    LatticeHalfFock.tensorL D (ActualGround D hu) matrixH 0
        (LatticeHalfFock.tensorCurrent D (ActualGround D hu) colour mode vector) =
      LatticeHalfFock.tensorCurrent D (ActualGround D hu) colour mode
        (LatticeHalfFock.tensorL D (ActualGround D hu) matrixH 0 vector) +
      (-(mode : ℂ) - 1 / 2) •
        LatticeHalfFock.tensorCurrent D (ActualGround D hu) colour mode vector := by
  have scalarRule := LatticeHalfFock.L_current_commutator D matrixH hHG hGH colour 0 mode
  induction vector using TensorProduct.induction_on with
  | zero => simp
  | tmul polynomial ground =>
    have action := congrArg (fun operator : Module.End ℂ (Oscillator D) => operator polynomial)
      scalarRule
    simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply,
      zero_add] at action
    have rearranged := eq_add_of_sub_eq action
    simp only [LatticeHalfFock.tensorL, LatticeHalfFock.tensorCurrent,
      LatticeHalfFock.tensorEnd, TensorProduct.map_tmul, LinearMap.id_apply]
    rw [rearranged, TensorProduct.add_tmul, TensorProduct.smul_tmul']
    simp only [LatticeHalfFock.frequency]
    rw [show -((mode : ℂ) + 1 / 2) = -(mode : ℂ) - 1 / 2 by ring]
    exact add_comm _ _
  | add first second inductionFirst inductionSecond =>
    simp only [map_add, inductionFirst, inductionSecond, smul_add]
    abel

include hHG hGH in
private theorem jet_L0 (index : Index D) (mode : ℤ) (vector : ActualTensor D hu) :
    LatticeHalfFock.tensorL D (ActualGround D hu) matrixH 0
        (jetCurrent D hu index mode vector) =
      jetCurrent D hu index mode
        (LatticeHalfFock.tensorL D (ActualGround D hu) matrixH 0 vector) +
      (-(mode : ℂ) - 1 / 2) • jetCurrent D hu index mode vector := by
  simp only [jetCurrent, LinearMap.smul_apply, map_smul]
  rw [tensor_current_L0 D hu matrixH hHG hGH, smul_add, smul_comm]

private def coefficientWeight (charge : Charge D) (word : List (Index D))
    (exponent : ℤ) : ℂ :=
  (wordWeight D word : ℂ) + ((exponent + chargeNorm D charge : ℤ) : ℂ) / 2

private theorem coefficientWeight_cons (charge : Charge D) (index : Index D)
    (tail : List (Index D)) (mode exponent : ℤ) :
    coefficientWeight D charge tail (exponent + 2 * mode + 2 * index.2 + 3) +
        (-(mode : ℂ) - 1 / 2) = coefficientWeight D charge (index :: tail) exponent := by
  simp only [coefficientWeight, wordWeight, List.map_cons, List.sum_cons, sourceWeight]
  push_cast
  ring

include hHG hGH in
private theorem flatCoefficient_L0 (charge : Charge D) (word : List (Index D))
    (modes : ModeTuple D word) (exponent : ℤ) (vector : ActualTensor D hu) :
    LatticeHalfFock.tensorL D (ActualGround D hu) matrixH 0
        (flatCoefficient D hu (chargedField D hu charge) word modes exponent vector) =
      flatCoefficient D hu (chargedField D hu charge) word modes exponent
        (LatticeHalfFock.tensorL D (ActualGround D hu) matrixH 0 vector) +
      coefficientWeight D charge word exponent •
        flatCoefficient D hu (chargedField D hu charge) word modes exponent vector := by
  induction word generalizing exponent vector with
  | nil =>
    simpa only [flatCoefficient, chargedField, HVertexOperator.coeff_of_coeff,
      coefficientWeight, wordWeight, List.map_nil, List.sum_nil, Nat.cast_zero, zero_add]
      using charged_tensor_L0_covariance D hu matrixH hHG hGH charge exponent vector
  | cons index tail inductionProof =>
    rcases modes with ⟨mode, remaining⟩
    by_cases negative : mode < 0
    · simp only [flatCoefficient, if_pos negative, Module.End.mul_apply]
      rw [jet_L0 D hu matrixH hHG hGH, inductionProof, map_add, map_smul]
      rw [← coefficientWeight_cons D charge index tail mode exponent]
      module
    · simp only [flatCoefficient, if_neg negative, Module.End.mul_apply]
      rw [inductionProof, jet_L0 D hu matrixH hHG hGH, map_add, map_smul]
      rw [← coefficientWeight_cons D charge index tail mode exponent]
      module

include hHG hGH in
theorem normalWord_L0 (charge : Charge D) (word : List (Index D))
    (exponent : ℤ) (vector : ActualTensor D hu) :
    LatticeHalfFock.tensorL D (ActualGround D hu) matrixH 0
        ((normalWord D hu charge word).coeff exponent vector) =
      (normalWord D hu charge word).coeff exponent
        (LatticeHalfFock.tensorL D (ActualGround D hu) matrixH 0 vector) +
      ((wordWeight D word : ℂ) + ((exponent + chargeNorm D charge : ℤ) : ℂ) / 2) •
        (normalWord D hu charge word).coeff exponent vector := by
  classical
  simp only [normalWord_flattened]
  rw [map_finsum _ (flatTerm_finite D hu (chargedField D hu charge) word exponent vector)]
  simp_rw [flatTerm, flatCoefficient_L0 D hu matrixH hHG hGH]
  rw [finsum_add_distrib]
  · have scalar_sum := smul_finsum' (coefficientWeight D charge word exponent)
      (flatTerm_finite D hu (chargedField D hu charge) word exponent vector)
    simp only [flatTerm] at scalar_sum
    rw [← scalar_sum]
    rfl
  · exact flatTerm_finite D hu (chargedField D hu charge) word exponent _
  · exact Function.HasFiniteSupport.smul_right
      (fun _ : ModeTuple D word => coefficientWeight D charge word exponent)
      (flatTerm_finite D hu (chargedField D hu charge) word exponent vector)

include hHG hGH in
private theorem normalPolynomial_L0 (charge : Charge D) (polynomial : Oscillator D)
    (exponent : ℤ) (vector : ActualTensor D hu) :
    LatticeHalfFock.tensorL D (ActualGround D hu) matrixH 0
        ((normalPolynomial D hu charge polynomial).coeff exponent vector) =
      (normalPolynomial D hu charge polynomial).coeff exponent
        (LatticeHalfFock.tensorL D (ActualGround D hu) matrixH 0 vector) +
      (normalPolynomial D hu charge (oscillatorEuler D polynomial)).coeff exponent vector +
      (((exponent + chargeNorm D charge : ℤ) : ℂ) / 2) •
        (normalPolynomial D hu charge polynomial).coeff exponent vector := by
  induction polynomial using MvPolynomial.induction_on' with
  | monomial sourceExponent scalar =>
    have source : monomial sourceExponent scalar =
        scalar • (monomial sourceExponent 1 : Oscillator D) := by simp [smul_monomial]
    rw [oscillatorEuler_monomial, source]
    simp only [map_smul, Pi.smul_apply, LinearMap.smul_apply]
    rw [normalPolynomial_monomial_enumeration D hu charge sourceExponent _ (List.Perm.refl _)]
    rw [normalWord_L0 D hu matrixH hHG hGH, wordWeight_occurrences]
    rw [show Finsupp.weight (sourceWeight D) sourceExponent =
      Finsupp.weight (fun index : Index D => index.2 + 1) sourceExponent from rfl]
    module
  | add first second inductionFirst inductionSecond =>
    simp only [map_add, Pi.add_apply, LinearMap.add_apply, smul_add]
    rw [inductionFirst, inductionSecond]
    abel

include hHG hGH in
private theorem corrected_monomial_term_L0 (charge : Charge D)
    (sourceExponent : Index D →₀ ℕ) (shift : ℕ) (exponent : ℤ)
    (vector : ActualTensor D hu) :
    LatticeHalfFock.tensorL D (ActualGround D hu) matrixH 0
        ((shiftLinear D hu shift (normalPolynomial D hu charge
          (Corr D charge (monomial sourceExponent 1) shift))).coeff exponent vector) =
      (shiftLinear D hu shift (normalPolynomial D hu charge
          (Corr D charge (monomial sourceExponent 1) shift))).coeff exponent
        (LatticeHalfFock.tensorL D (ActualGround D hu) matrixH 0 vector) +
      ((Finsupp.weight (sourceWeight D) sourceExponent : ℂ) +
          ((exponent + chargeNorm D charge : ℤ) : ℂ) / 2) •
        (shiftLinear D hu shift (normalPolynomial D hu charge
          (Corr D charge (monomial sourceExponent 1) shift))).coeff exponent vector := by
  simp only [shiftLinear, LinearMap.coe_mk, AddHom.coe_mk, shiftField,
    HVertexOperator.coeff_of_coeff]
  have correction := Corr_Euler D charge (monomial sourceExponent 1) shift
  rw [oscillatorEuler_monomial, map_smul, Finsupp.smul_apply] at correction
  have mapped := congrArg (fun polynomial : Oscillator D =>
    (normalPolynomial D hu charge polynomial).coeff (exponent + 2 * shift) vector) correction
  simp only [map_add, map_smul, Pi.add_apply, LinearMap.add_apply,
    Pi.smul_apply, LinearMap.smul_apply] at mapped
  rw [normalPolynomial_L0 D hu matrixH hHG hGH]
  have scalar : (((exponent + 2 * shift + chargeNorm D charge : ℤ) : ℂ) / 2) =
      (shift : ℂ) + ((exponent + chargeNorm D charge : ℤ) : ℂ) / 2 := by
    push_cast
    ring
  rw [scalar]
  rw [eq_sub_of_add_eq mapped]
  rw [show Finsupp.weight (sourceWeight D) sourceExponent =
    Finsupp.weight (fun index : Index D => index.2 + 1) sourceExponent from rfl]
  module

include hHG hGH in
private theorem Ytw_monomial_L0 (charge : Charge D) (sourceExponent : Index D →₀ ℕ)
    (exponent : ℤ) (vector : ActualTensor D hu) :
    LatticeHalfFock.tensorL D (ActualGround D hu) matrixH 0
        ((Ytw D hu (Finsupp.single charge (monomial sourceExponent 1))).coeff exponent vector) =
      (Ytw D hu (Finsupp.single charge (monomial sourceExponent 1))).coeff exponent
        (LatticeHalfFock.tensorL D (ActualGround D hu) matrixH 0 vector) +
      ((Finsupp.weight (sourceWeight D) sourceExponent : ℂ) +
          ((exponent + chargeNorm D charge : ℤ) : ℂ) / 2) •
        (Ytw D hu (Finsupp.single charge (monomial sourceExponent 1))).coeff exponent vector := by
  classical
  simp only [Ytw, Finsupp.lsum_single]
  simp only [correctedPolynomial, LinearMap.comp_apply,
    Finsupp.lsum_apply, Finsupp.sum, map_sum, Finset.sum_apply, LinearMap.sum_apply]
  simp_rw [corrected_monomial_term_L0 D hu matrixH hHG hGH]
  rw [Finset.sum_add_distrib, Finset.smul_sum]

include hHG hGH in
theorem Ytw_L0_covariance (source : Carrier D) (exponent : ℤ) (vector : ActualTensor D hu) :
    LatticeHalfFock.tensorL D (ActualGround D hu) matrixH 0
        ((Ytw D hu source).coeff exponent vector) =
      (Ytw D hu source).coeff exponent
        (LatticeHalfFock.tensorL D (ActualGround D hu) matrixH 0 vector) +
      (Ytw D hu (sugawaraMode D matrixH 0 source)).coeff exponent vector +
      ((exponent : ℂ) / 2) • (Ytw D hu source).coeff exponent vector := by
  induction source using Finsupp.induction_linear with
  | zero => simp
  | add first second inductionFirst inductionSecond =>
    simp only [map_add, Pi.add_apply, LinearMap.add_apply, smul_add]
    rw [inductionFirst, inductionSecond]
    abel
  | single charge polynomial =>
    induction polynomial using MvPolynomial.induction_on' with
    | monomial sourceExponent scalar =>
      have source : monomial sourceExponent scalar =
          scalar • (monomial sourceExponent 1 : Oscillator D) := by simp [smul_monomial]
      have sourceMode := sugawaraMode_weighted_homogeneous D matrixH hHG hGH charge
        (monomial sourceExponent 1) (Finsupp.weight (sourceWeight D) sourceExponent)
        (isWeightedHomogeneous_monomial _ _ _ rfl)
      rw [source, ← Finsupp.smul_single]
      simp only [map_smul, Pi.smul_apply, LinearMap.smul_apply]
      rw [sourceMode]
      simp only [map_smul, Pi.smul_apply, LinearMap.smul_apply]
      rw [Ytw_monomial_L0 D hu matrixH hHG hGH]
      simp only [chargeNorm]
      push_cast
      module
    | add first second inductionFirst inductionSecond =>
      simp only [Finsupp.single_add, map_add, Pi.add_apply, LinearMap.add_apply, smul_add]
      rw [inductionFirst, inductionSecond]
      abel

include hHG in
private theorem native_stress_zero_mode :
    (Ytw D hu (LatticeActualConformalState.omega D matrixH)).coeff (-4) =
      LatticeHalfFock.tensorL D (ActualGround D hu) matrixH 0 := by
  rw [LatticeHalfFockConformalIdentification.Ytw_omega D hu matrixH hHG]
  simp only [LatticeHalfFock.tensorStressField, HVertexOperator.coeff_of_coeff,
    LatticeHalfFock.stressCoeff]
  norm_num
  rfl

include hHG hGH in
theorem Ytw_homogeneous_coefficient (source : Carrier D) (sourceEnergy targetEnergy : ℂ)
    (sourceHomogeneous : sugawaraMode D matrixH 0 source = sourceEnergy • source)
    (exponent : ℤ) (vector : ActualTensor D hu)
    (targetHomogeneous : LatticeHalfFock.tensorL D (ActualGround D hu) matrixH 0 vector =
      targetEnergy • vector) :
    (Ytw D hu (LatticeActualConformalState.omega D matrixH)).coeff (-4)
        ((Ytw D hu source).coeff exponent vector) =
      (targetEnergy + sourceEnergy + (exponent : ℂ) / 2) •
        (Ytw D hu source).coeff exponent vector := by
  rw [native_stress_zero_mode D hu matrixH hHG,
    Ytw_L0_covariance D hu matrixH hHG hGH, sourceHomogeneous, targetHomogeneous]
  simp only [map_smul, Pi.smul_apply, LinearMap.smul_apply]
  module

def homogeneousCoefficient (sourceEnergy targetEnergy : ℂ) (exponent : ℤ)
    (source : Module.End.eigenspace (sugawaraMode D matrixH 0) sourceEnergy) :
    Module.End.eigenspace (LatticeHalfFock.tensorL D (ActualGround D hu) matrixH 0) targetEnergy
      →ₗ[ℂ] Module.End.eigenspace
        (LatticeHalfFock.tensorL D (ActualGround D hu) matrixH 0)
        (targetEnergy + sourceEnergy + (exponent : ℂ) / 2) where
  toFun vector := ⟨(Ytw D hu source.val).coeff exponent vector.val, by
    apply Module.End.mem_eigenspace_iff.mpr
    have shifted := Ytw_homogeneous_coefficient D hu matrixH hHG hGH
      source.val sourceEnergy targetEnergy
      (Module.End.mem_eigenspace_iff.mp source.property) exponent vector.val
      (Module.End.mem_eigenspace_iff.mp vector.property)
    simpa only [native_stress_zero_mode D hu matrixH hHG] using shifted⟩
  map_add' first second := by
    apply Subtype.ext
    exact (Ytw D hu source.val).coeff exponent |>.map_add first.val second.val
  map_smul' scalar vector := by
    apply Subtype.ext
    exact (Ytw D hu source.val).coeff exponent |>.map_smul scalar vector.val

#print axioms normalWord_L0
#print axioms Ytw_L0_covariance
#print axioms Ytw_homogeneous_coefficient

end
end D5.S3.VertexAlgebra.LatticeHalfFockLZeroCovariance
