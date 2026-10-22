/- GID: D5/S3/VertexAlgebra/LatticeHalfFockTargetThetaCoefficients
   generality: G
   mirror-B: D5/B/S3/VertexAlgebra/LatticeHalfFockTargetThetaCoefficients
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Oscillator reflection conjugates the original charged twisted coefficients. -/

import D5.S3.VertexAlgebra.LatticeHalfFockThetaMonodromy

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.LatticeHalfFockTargetThetaCoefficients

open LatticeGeneratingFieldLocality LatticeHalfFockChargedCoefficients
open LatticeHalfFockChargedTensorCoefficients LatticeInvolution MvPolynomial
open scoped BigOperators TensorProduct

noncomputable section

def sigmaTensor (D : LatticeData) (hu : IsUnit D.G.det) :
    Module.End ℂ (ActualTensor D hu) := TensorProduct.map (sigmaLinear D) LinearMap.id

@[simp] theorem sigmaTensor_tmul (D : LatticeData) (hu : IsUnit D.G.det)
    (polynomial : Oscillator D) (ground : ActualGround D hu) :
    sigmaTensor D hu (polynomial ⊗ₜ[ℂ] ground) = sigma D polynomial ⊗ₜ[ℂ] ground := by
  rfl

theorem sigma_halfCreationSeries (D : LatticeData) (charge : Charge D) :
    PowerSeries.map (sigma D) (halfCreationSeries D charge) =
      halfCreationSeries D (-charge) := by
  ext degree
  simp only [PowerSeries.coeff_map, halfCreationSeries, PowerSeries.coeff_mk]
  split_ifs <;> simp [map_sum, sigma_smul, smul_neg, neg_smul]

theorem sigma_halfCreationExponential (D : LatticeData) (charge : Charge D) :
    PowerSeries.map (sigma D) (halfCreationExponential D charge) =
      halfCreationExponential D (-charge) := by
  have substitutable : PowerSeries.HasSubst (halfCreationSeries D charge) :=
    PowerSeries.HasSubst.of_constantCoeff_zero' (by
      simp [halfCreationSeries, ← PowerSeries.coeff_zero_eq_constantCoeff_apply])
  have transport := PowerSeries.map_subst (h := sigma D) substitutable
    (PowerSeries.exp (Oscillator D))
  change PowerSeries.map (sigma D) (halfCreationExponential D charge) =
    (PowerSeries.map (sigma D) (PowerSeries.exp (Oscillator D))).subst
      (PowerSeries.map (sigma D) (halfCreationSeries D charge)) at transport
  rw [transport, PowerSeries.map_exp, sigma_halfCreationSeries]
  rfl

theorem sigma_halfCreationCoeff (D : LatticeData) (charge : Charge D) (degree : ℤ) :
    sigma D (halfCreationCoeff D charge degree) = halfCreationCoeff D (-charge) degree := by
  unfold halfCreationCoeff
  split_ifs
  · exact map_zero _
  · rw [← PowerSeries.coeff_map, sigma_halfCreationExponential]

theorem sigma_halfTranslationVariable (D : LatticeData) (charge : Charge D)
    (index : Index D) :
    Polynomial.map (sigma D) (halfTranslationVariable D charge index) =
      -halfTranslationVariable D (-charge) index := by
  simp [halfTranslationVariable, LatticeFiniteNegativeGeneration.bilinear_neg_left,
    neg_smul, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_pow] <;> ring

theorem sigma_halfTranslatedPolynomial (D : LatticeData) (charge : Charge D)
    (polynomial : Oscillator D) :
    Polynomial.map (sigma D) (halfTranslatedPolynomial D charge polynomial) =
      halfTranslatedPolynomial D (-charge) (sigma D polynomial) := by
  induction polynomial using MvPolynomial.induction_on with
  | C scalar => simp [halfTranslatedPolynomial]
  | add first second firstProof secondProof =>
    simp only [halfTranslatedPolynomial, map_add, Polynomial.map_add] at firstProof secondProof ⊢
    rw [firstProof, secondProof]
  | mul_X polynomial index inductionProof =>
    simp only [halfTranslatedPolynomial, map_mul, Polynomial.map_mul, sigma_X,
      map_neg, MvPolynomial.eval₂AlgHom_X] at inductionProof ⊢
    rw [inductionProof, sigma_halfTranslationVariable]

theorem sigma_halfTranslatedCoefficient (D : LatticeData) (charge : Charge D)
    (polynomial : Oscillator D) (degree : ℕ) :
    sigma D ((halfTranslatedPolynomial D charge polynomial).coeff degree) =
      (halfTranslatedPolynomial D (-charge) (sigma D polynomial)).coeff degree := by
  rw [← Polynomial.coeff_map, sigma_halfTranslatedPolynomial]

theorem sigma_oscillatorTerm (D : LatticeData) (charge : Charge D) (exponent : ℤ)
    (polynomial : Oscillator D) (degree : ℕ) :
    sigma D (oscillatorTerm D charge exponent polynomial degree) =
      oscillatorTerm D (-charge) exponent (sigma D polynomial) degree := by
  simp only [oscillatorTerm, map_mul, sigma_halfTranslatedCoefficient,
    sigma_halfCreationCoeff]
  simp [chargeNorm, bilinear]

theorem sigma_oscillatorCoefficient (D : LatticeData) (charge : Charge D) (exponent : ℤ)
    (polynomial : Oscillator D) :
    sigma D (oscillatorCoefficient D charge exponent polynomial) =
      oscillatorCoefficient D (-charge) exponent (sigma D polynomial) := by
  change (sigma D).toAddMonoidHom
      (∑ᶠ degree : ℕ, oscillatorTerm D charge exponent polynomial degree) =
    ∑ᶠ degree : ℕ, oscillatorTerm D (-charge) exponent (sigma D polynomial) degree
  rw [(sigma D).toAddMonoidHom.map_finsum
    (charged_term_finite_support D charge exponent polynomial)]
  apply finsum_congr
  intro degree
  exact sigma_oscillatorTerm D charge exponent polynomial degree

theorem ground_reflection (D : LatticeData) (hu : IsUnit D.G.det) (charge : Charge D) :
    groundAction D hu (-charge) = groundAction D hu charge := by
  run_tac
    let supplier := (Lean.Name.num `_private.D5.S3.VertexAlgebra.LatticeHalfFockChargedMonodromy 0).append
      `D5.S3.VertexAlgebra.LatticeHalfFockChargedMonodromy.ground_neg
    Lean.Elab.Tactic.evalTactic (← `(tactic| exact $(Lean.mkIdent supplier) _ _ _))

theorem sigmaTensor_chargedCoefficient (D : LatticeData) (hu : IsUnit D.G.det)
    (charge : Charge D) (exponent : ℤ) (vector : ActualTensor D hu) :
    sigmaTensor D hu (chargedCoefficient D hu charge exponent vector) =
      chargedCoefficient D hu (-charge) exponent (sigmaTensor D hu vector) := by
  induction vector using TensorProduct.induction_on with
  | zero => simp
  | tmul polynomial ground =>
    simp only [chargedCoefficient, LinearMap.smul_apply, map_smul,
      TensorProduct.map_tmul, sigmaTensor_tmul, sigma_oscillatorCoefficient,
      ground_reflection]
    congr 1
    simp [chargeScalar, chargeNorm, bilinear]
  | add first second firstProof secondProof =>
    simp only [map_add, firstProof, secondProof]

#print axioms sigmaTensor_chargedCoefficient

end
end D5.S3.VertexAlgebra.LatticeHalfFockTargetThetaCoefficients
