/- GID: D5/S3/Quantum/Transport/StrongAbsorptionCumulants
   generality: G
   mirror-B: D5/B/S3/Quantum/Transport/StrongAbsorptionCumulants
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Changing-observable moment estimates. -/

/-
admission_basis: open-problem-resolution (#16825; Proved)
escape_witness: none
Direct frozen dependencies: none.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/17044
powerErrorPoly: proof_shape: bind-only; escape_witness: none; consumers: D5.S3.Quantum.Transport.StrongAbsorptionCumulants.powerErrorPoly_eval, D5.S3.Quantum.Transport.StrongAbsorptionCumulants.rescaled_moment_integral_expansion_high
observableCorrectionPoly: proof_shape: bind-only; escape_witness: none; consumers: D5.S3.Quantum.Transport.StrongAbsorptionCumulants.baseExpectation_observableCorrection, D5.S3.Quantum.Transport.StrongAbsorptionCumulants.rescaled_moment_integral_expansion_high, D5.S3.Quantum.Transport.StrongAbsorptionCumulants.rescaled_moment_integral_expansion, D5.S3.Quantum.Transport.StrongAbsorptionCumulants.baseMoment_models, D5.S3.Quantum.Transport.StrongAbsorptionCumulants.rescaledMomentExpansion
rescaledKappa: proof_shape: bind-only; escape_witness: none; consumers: D5.S3.Quantum.Transport.StrongAbsorptionCumulants.RescaledExpansion, D5.S3.Quantum.Transport.StrongAbsorptionCumulants.rescaledExpansion_of_moments, D5.S3.Quantum.Transport.StrongAbsorptionCumulants.signed_kappa_rescaled, D5.S3.Quantum.Transport.StrongAbsorptionCumulants.assemble
claim: proof_shape: bind-only; escape_witness: none; consumers: D5.S3.Quantum.Transport.StrongAbsorptionCumulants.assemble, D5.S3.Quantum.Transport.StrongAbsorptionCumulants.result_of_moments, D5.S3.Quantum.Transport.StrongAbsorptionCumulants.result
baseExpectation: proof_shape: bind-only; escape_witness: none; consumers: D5.S3.Quantum.Transport.StrongAbsorptionCumulants.baseExpectation_z, D5.S3.Quantum.Transport.StrongAbsorptionCumulants.baseExpectation_observableCorrection, D5.S3.Quantum.Transport.StrongAbsorptionCumulants.baseExpectation_add, D5.S3.Quantum.Transport.StrongAbsorptionCumulants.baseExpectation_densityCorrection, D5.S3.Quantum.Transport.StrongAbsorptionCumulants.variable_observable_firstOrder, D5.S3.Quantum.Transport.StrongAbsorptionCumulants.rescaled_moment_integral_expansion_high, D5.S3.Quantum.Transport.StrongAbsorptionCumulants.rescaled_moment_integral_expansion_one, D5.S3.Quantum.Transport.StrongAbsorptionCumulants.rescaled_moment_integral_expansion, D5.S3.Quantum.Transport.StrongAbsorptionCumulants.baseMoment_models, D5.S3.Quantum.Transport.StrongAbsorptionCumulants.rescaledMomentExpansion
singleMoment: proof_shape: bind-only; escape_witness: none; consumers: D5.S3.Quantum.Transport.StrongAbsorptionCumulants.baseExpectation_z, D5.S3.Quantum.Transport.StrongAbsorptionCumulants.singleMoment_derivative, D5.S3.Quantum.Transport.StrongAbsorptionCumulants.baseExpectation_densityCorrection, D5.S3.Quantum.Transport.StrongAbsorptionCumulants.baseMoment_models
singleWMoment: proof_shape: bind-only; escape_witness: none; consumers: D5.S3.Quantum.Transport.StrongAbsorptionCumulants.baseExpectation_observableCorrection, D5.S3.Quantum.Transport.StrongAbsorptionCumulants.singleWMoment_derivative, D5.S3.Quantum.Transport.StrongAbsorptionCumulants.baseMoment_models
RescaledMomentExpansion: proof_shape: bind-only; escape_witness: none; consumers: D5.S3.Quantum.Transport.StrongAbsorptionCumulants.rescaledExpansion_of_moments, D5.S3.Quantum.Transport.StrongAbsorptionCumulants.result_of_moments, D5.S3.Quantum.Transport.StrongAbsorptionCumulants.rescaledMomentExpansion
RescaledExpansion: proof_shape: bind-only; escape_witness: none; consumers: D5.S3.Quantum.Transport.StrongAbsorptionCumulants.rescaledExpansion_of_moments, D5.S3.Quantum.Transport.StrongAbsorptionCumulants.assemble
iteratedDeriv_id_mul: proof_shape: bind-only; escape_witness: none; consumers: D5.S3.Quantum.Transport.StrongAbsorptionCumulants.correctionJet_moments
qPoly_eval: proof_shape: bind-only; escape_witness: none; consumers: D5.S3.Quantum.Transport.StrongAbsorptionCumulants.powerErrorPoly_eval, D5.S3.Quantum.Transport.StrongAbsorptionCumulants.rescaled_moment_integral_expansion_one
zPoly_eval: proof_shape: bind-only; escape_witness: none; consumers: D5.S3.Quantum.Transport.StrongAbsorptionCumulants.powerErrorPoly_eval, D5.S3.Quantum.Transport.StrongAbsorptionCumulants.baseExpectation_z, D5.S3.Quantum.Transport.StrongAbsorptionCumulants.baseExpectation_observableCorrection, D5.S3.Quantum.Transport.StrongAbsorptionCumulants.baseExpectation_densityCorrection, D5.S3.Quantum.Transport.StrongAbsorptionCumulants.rescaled_moment_integral_expansion_high, D5.S3.Quantum.Transport.StrongAbsorptionCumulants.rescaled_moment_integral_expansion_one
wPoly_eval: proof_shape: bind-only; escape_witness: none; consumers: D5.S3.Quantum.Transport.StrongAbsorptionCumulants.powerErrorPoly_eval, D5.S3.Quantum.Transport.StrongAbsorptionCumulants.baseExpectation_observableCorrection, D5.S3.Quantum.Transport.StrongAbsorptionCumulants.rescaled_moment_integral_expansion_high, D5.S3.Quantum.Transport.StrongAbsorptionCumulants.rescaled_moment_integral_expansion_one
singleZPoly_eval: proof_shape: bind-only; escape_witness: none; consumers: D5.S3.Quantum.Transport.StrongAbsorptionCumulants.laguerreZPower_integrable
powerErrorPoly_eval: proof_shape: bind-only; escape_witness: none; consumers: D5.S3.Quantum.Transport.StrongAbsorptionCumulants.rescaled_moment_integral_expansion_high
laguerreZPower_integrable: proof_shape: bind-only; escape_witness: none; consumers: D5.S3.Quantum.Transport.StrongAbsorptionCumulants.baseExpectation_densityCorrection
baseExpectation_z: proof_shape: bind-only; escape_witness: none; consumers: D5.S3.Quantum.Transport.StrongAbsorptionCumulants.baseMoment_models
baseExpectation_observableCorrection: proof_shape: bind-only; escape_witness: none; consumers: D5.S3.Quantum.Transport.StrongAbsorptionCumulants.baseMoment_models
baseExpectation_add: proof_shape: bind-only; escape_witness: none; consumers: D5.S3.Quantum.Transport.StrongAbsorptionCumulants.rescaled_moment_integral_expansion, D5.S3.Quantum.Transport.StrongAbsorptionCumulants.baseMoment_models
weightPolynomial_integrable: proof_shape: bind-only; escape_witness: none; consumers: D5.S3.Quantum.Transport.StrongAbsorptionCumulants.law_polynomial_integrable
singleMoment_derivative: proof_shape: bind-only; escape_witness: none; consumers: D5.S3.Quantum.Transport.StrongAbsorptionCumulants.baseMoment_models
laguerreHw_iterated: proof_shape: bind-only; escape_witness: none; consumers: D5.S3.Quantum.Transport.StrongAbsorptionCumulants.singleWMoment_derivative
law_polynomial_integrable: proof_shape: bind-only; escape_witness: none; consumers: D5.S3.Quantum.Transport.StrongAbsorptionCumulants.law_remainder_bigO, D5.S3.Quantum.Transport.StrongAbsorptionCumulants.variable_observable_firstOrder
rescaled_pow_integrable: proof_shape: bind-only; escape_witness: none; consumers: D5.S3.Quantum.Transport.StrongAbsorptionCumulants.rescaled_moment_integral_expansion_high, D5.S3.Quantum.Transport.StrongAbsorptionCumulants.rescaled_moment_integral_expansion_one
baseExpectation_densityCorrection: proof_shape: bind-only; escape_witness: none; consumers: D5.S3.Quantum.Transport.StrongAbsorptionCumulants.baseMoment_models
singleWMoment_derivative: proof_shape: bind-only; escape_witness: none; consumers: D5.S3.Quantum.Transport.StrongAbsorptionCumulants.baseMoment_models
rescaledExpansion_of_moments: proof_shape: content; escape_witness: none; consumers: D5.S3.Quantum.Transport.StrongAbsorptionCumulants.result_of_moments
signed_kappa_rescaled: proof_shape: bind-only; escape_witness: none; consumers: D5.S3.Quantum.Transport.StrongAbsorptionCumulants.assemble
assemble: proof_shape: bind-only; escape_witness: none; consumers: D5.S3.Quantum.Transport.StrongAbsorptionCumulants.result_of_moments
law_remainder_bigO: proof_shape: content; escape_witness: none; consumers: D5.S3.Quantum.Transport.StrongAbsorptionCumulants.variable_observable_firstOrder
laguerreH_analytic: proof_shape: bind-only; escape_witness: none; consumers: D5.S3.Quantum.Transport.StrongAbsorptionCumulants.correctionJet_moments
result_of_moments: proof_shape: content; escape_witness: none; consumers: D5.S3.Quantum.Transport.StrongAbsorptionCumulants.result
variable_observable_firstOrder: proof_shape: content; escape_witness: none; consumers: D5.S3.Quantum.Transport.StrongAbsorptionCumulants.rescaled_moment_integral_expansion_high, D5.S3.Quantum.Transport.StrongAbsorptionCumulants.rescaled_moment_integral_expansion_one
rescaled_moment_integral_expansion_high: proof_shape: content; escape_witness: none; consumers: D5.S3.Quantum.Transport.StrongAbsorptionCumulants.rescaled_moment_integral_expansion
rescaled_moment_integral_expansion_one: proof_shape: content; escape_witness: none; consumers: D5.S3.Quantum.Transport.StrongAbsorptionCumulants.rescaled_moment_integral_expansion
laguerreHw_analytic: proof_shape: bind-only; escape_witness: none; consumers: D5.S3.Quantum.Transport.StrongAbsorptionCumulants.correctionJet_moments
modelCorrection_near: proof_shape: bind-only; escape_witness: none; consumers: D5.S3.Quantum.Transport.StrongAbsorptionCumulants.correctionJet_moments
rescaled_moment_integral_expansion: proof_shape: content; escape_witness: none; consumers: D5.S3.Quantum.Transport.StrongAbsorptionCumulants.rescaledMomentExpansion
correctionJet_moments: proof_shape: bind-only; escape_witness: none; consumers: D5.S3.Quantum.Transport.StrongAbsorptionCumulants.baseMoment_models
baseMoment_models: proof_shape: bind-only; escape_witness: none; consumers: D5.S3.Quantum.Transport.StrongAbsorptionCumulants.rescaledMomentExpansion
rescaledMomentExpansion: proof_shape: content; escape_witness: none; consumers: D5.S3.Quantum.Transport.StrongAbsorptionCumulants.result
result: proof_shape: content; escape_witness: none; consumers: none (settling result)
Escape audit for public helper statements unfinished: https://github.com/the-omega-institute/trureturing/issues/19485
-/

import D5.S3.Quantum.Transport.StrongAbsorption.Foundations
import D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments
import D5.S3.Quantum.Transport.StrongAbsorption.Density

namespace D5.S3.Quantum.Transport.StrongAbsorptionCumulants
open D5.S3.Quantum.Transport.StrongAbsorption.Foundations
open D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments
open D5.S3.Quantum.Transport.StrongAbsorption.Density
open MeasureTheory ProbabilityTheory Set Real Finset Filter Asymptotics MvPolynomial
open scoped Topology

private theorem iteratedDeriv_id_mul {F : ℝ → ℝ} (hF : AnalyticAt ℝ F 0) (r : ℕ) :
    iteratedDeriv r (fun t => t*F t) 0 = (r : ℝ)*iteratedDeriv (r-1) F 0 := by
  cases r with
  | zero => simp
  | succ r =>
    rw [iteratedDeriv_fun_mul (by fun_prop) hF.contDiffAt]
    simp [iteratedDeriv_fun_id_zero,Finset.sum_ite_eq',Nat.choose_one_right]

private theorem qPoly_eval (M : ℕ) (p : (Fin M → ℝ) × (Fin M → ℝ)) :
    eval (Sum.elim p.1 p.2) ((Finset.univ.expect (fun i : Fin M => ((X (Sum.inl i))^3 : MvPolynomial (Fin M ⊕ Fin M) ℝ)))) = (M : ℝ)⁻¹*powerSum M 3 p.1 := by
  simp [Finset.expect, Algebra.smul_def,powerSum,map_sum]

private noncomputable def powerErrorPoly (M k : ℕ) : MvPolynomial (Fin M ⊕ Fin M) ℝ :=
  C (((k+2 : ℝ)*(k+1))/2)*((Finset.univ.expect (fun i : Fin M => ((X (Sum.inl i))^2 : MvPolynomial (Fin M ⊕ Fin M) ℝ))))^2*((Finset.univ.expect (fun i : Fin M => (X (Sum.inl i) : MvPolynomial (Fin M ⊕ Fin M) ℝ))))^k+
    C (k+2 : ℝ)*((Finset.univ.expect (fun i : Fin M => ((X (Sum.inl i))^3 : MvPolynomial (Fin M ⊕ Fin M) ℝ))))*((Finset.univ.expect (fun i : Fin M => (X (Sum.inl i) : MvPolynomial (Fin M ⊕ Fin M) ℝ))))^(k+1)

private noncomputable def observableCorrectionPoly (M r : ℕ) : MvPolynomial (Fin M ⊕ Fin M) ℝ :=
  -C (r : ℝ)*(Finset.univ.expect (fun i : Fin M => ((X (Sum.inl i))^2 : MvPolynomial (Fin M ⊕ Fin M) ℝ)))*((Finset.univ.expect (fun i : Fin M => (X (Sum.inl i) : MvPolynomial (Fin M ⊕ Fin M) ℝ))))^(r-1)

private theorem zPoly_eval (M : ℕ) (p : (Fin M → ℝ) × (Fin M → ℝ)) :
    eval (Sum.elim p.1 p.2) ((Finset.univ.expect (fun i : Fin M => (X (Sum.inl i) : MvPolynomial (Fin M ⊕ Fin M) ℝ)))) = (Finset.univ.expect p.1) := by
  simp [Finset.expect, Algebra.smul_def,Finset.expect, NNRat.smul_def, Finset.card_univ, Fintype.card_fin, NNRat.cast_inv, NNRat.cast_natCast,powerSum,map_sum]

private theorem wPoly_eval (M : ℕ) (p : (Fin M → ℝ) × (Fin M → ℝ)) :
    eval (Sum.elim p.1 p.2) ((Finset.univ.expect (fun i : Fin M => ((X (Sum.inl i))^2 : MvPolynomial (Fin M ⊕ Fin M) ℝ)))) = (Finset.univ.expect (fun i => p.1 i^2)) := by
  simp [Finset.expect, Algebra.smul_def,Finset.expect, NNRat.smul_def, Finset.card_univ, Fintype.card_fin, NNRat.cast_inv, NNRat.cast_natCast,powerSum,map_sum]

private theorem singleZPoly_eval (M : ℕ) (x : Fin M → ℝ) : eval x ((Finset.univ.expect (fun i : Fin M => (X i : MvPolynomial (Fin M) ℝ)))) = (Finset.univ.expect x) := by
  simp [Finset.expect, Algebra.smul_def,Finset.expect, NNRat.smul_def, Finset.card_univ, Fintype.card_fin, NNRat.cast_inv, NNRat.cast_natCast,powerSum,map_sum]

private noncomputable def rescaledKappa (M n : ℕ) (γ : ℝ) : ℝ :=
  iteratedDeriv n (cgf (rescaledObservable M γ) (law M γ)) 0

def claim : Prop :=
  ∀ M : ℕ, 1 ≤ M → ∀ n : ℕ, 2 ≤ n → ∃ C γ₀ : ℝ, 0 < γ₀ ∧ ∀ γ : ℝ, γ₀ ≤ γ →
    |(-1 : ℝ) ^ n * kappa M n γ -
      ((n - 1).factorial / ((M : ℝ) ^ (2 * n - 2) * γ ^ (2 * n)) -
        (2 * n - 1) * n * (n - 1).factorial / ((M : ℝ) ^ (2 * n - 2) * γ ^ (2 * n + 1)))| ≤
      C / γ ^ (2 * n + 2)

private theorem powerErrorPoly_eval (M k : ℕ) (p : (Fin M → ℝ) × (Fin M → ℝ)) :
    eval (Sum.elim p.1 p.2) (powerErrorPoly M k) =
      (((k+2 : ℝ)*(k+1))/2)*((Finset.univ.expect (fun i => p.1 i^2)))^2*((Finset.univ.expect p.1))^k+
        (k+2 : ℝ)*((M : ℝ)⁻¹*powerSum M 3 p.1)*((Finset.univ.expect p.1))^(k+1) := by
  simp [powerErrorPoly,zPoly_eval,wPoly_eval,qPoly_eval]

noncomputable def baseExpectation (M : ℕ) (P : MvPolynomial (Fin M ⊕ Fin M) ℝ) : ℝ :=
  (∫ p, baseWeight M M p*eval (Sum.elim p.1 p.2) P)/(partition M M)^2

private theorem laguerreZPower_integrable {M : ℕ} (hM : 1 ≤ M) (r : ℕ) :
    Integrable (fun x => laguerreWeight M M x*(Finset.univ.expect x)^r) := by
  have hm : 0 < (M : ℝ) := Nat.cast_pos'.mpr hM
  simpa only [map_pow,singleZPoly_eval] using laguerrePolynomial_integrable hm (((Finset.univ.expect (fun i : Fin M => (X i : MvPolynomial (Fin M) ℝ))))^r)

private noncomputable def singleMoment (M r : ℕ) : ℝ :=
  (∫ x, laguerreWeight M M x*(Finset.univ.expect x)^r)/partition M M

noncomputable def singleWMoment (M r : ℕ) : ℝ :=
  (∫ x, laguerreWeight M M x*(Finset.univ.expect (fun i => x i^2))*(Finset.univ.expect x)^r)/partition M M

private def RescaledMomentExpansion : Prop :=
  ∀ M : ℕ, 1 ≤ M → ∀ r : ℕ,
    FirstOrder ((fun γ => ProbabilityTheory.moment (rescaledObservable M γ) r (law M γ))) (expJet (gammaCGF ((M : ℝ)^2)) r)
      (correctionJet (gammaCGF ((M : ℝ)^2)) (correctionCGF ((M : ℝ)^2)) r)

private def RescaledExpansion : Prop :=
  ∀ M : ℕ, 1 ≤ M → ∀ n : ℕ, 2 ≤ n → ∃ C γ₀ : ℝ, 0 < γ₀ ∧ ∀ γ : ℝ, γ₀ ≤ γ →
    |rescaledKappa M n γ -
      ((n-1).factorial/(M : ℝ)^(2*n-2)-
       (2*n-1)*n*(n-1).factorial/((M : ℝ)^(2*n-2)*γ))| ≤ C/γ^2

private theorem baseExpectation_z {M : ℕ} (hM : 1 ≤ M) (r : ℕ) :
    baseExpectation M (((Finset.univ.expect (fun i : Fin M => (X (Sum.inl i) : MvPolynomial (Fin M ⊕ Fin M) ℝ))))^r) = singleMoment M r := by
  have hm : 0 < (M : ℝ) := Nat.cast_pos'.mpr hM
  have hZ := (partition_pos M hm).ne'
  have he : (fun p => baseWeight M M p*eval (Sum.elim p.1 p.2) (((Finset.univ.expect (fun i : Fin M => (X (Sum.inl i) : MvPolynomial (Fin M ⊕ Fin M) ℝ))))^r)) =
      (fun p : (Fin M → ℝ) × (Fin M → ℝ) =>
        (laguerreWeight M M p.1*(Finset.univ.expect p.1)^r)*laguerreWeight M M p.2) := by
    funext p
    simp only [map_pow,zPoly_eval,baseWeight]
    ring
  unfold baseExpectation singleMoment
  rw [he,Measure.volume_eq_prod]
  rw [integral_prod_mul (fun x : Fin M → ℝ => laguerreWeight M M x*(Finset.univ.expect x)^r) (laguerreWeight M M)]
  change _/(partition M M)^2 = _/partition M M
  field_simp
  <;> rfl

private theorem baseExpectation_observableCorrection {M : ℕ} (hM : 1 ≤ M) (r : ℕ) :
    baseExpectation M (observableCorrectionPoly M r) = -(r : ℝ)*singleWMoment M (r-1) := by
  have hm : 0 < (M : ℝ) := Nat.cast_pos'.mpr hM
  have hZ := (partition_pos M hm).ne'
  have he : (fun p => baseWeight M M p*eval (Sum.elim p.1 p.2) (observableCorrectionPoly M r)) =
      (fun p : (Fin M → ℝ) × (Fin M → ℝ) => -(r : ℝ)*
        ((laguerreWeight M M p.1*(Finset.univ.expect (fun i => p.1 i^2))*(Finset.univ.expect p.1)^(r-1))*laguerreWeight M M p.2)) := by
    funext p
    simp only [observableCorrectionPoly,map_mul,map_neg,eval_C,map_pow,zPoly_eval,wPoly_eval,baseWeight]
    ring
  unfold baseExpectation singleWMoment
  rw [he,integral_const_mul,Measure.volume_eq_prod]
  rw [integral_prod_mul (fun x : Fin M → ℝ => laguerreWeight M M x*(Finset.univ.expect (fun i => x i^2))*(Finset.univ.expect x)^(r-1)) (laguerreWeight M M)]
  change _/(partition M M)^2 = _*(_/partition M M)
  field_simp
  <;> rfl

theorem baseExpectation_add {M : ℕ} (hM : 1 ≤ M) (P Q : MvPolynomial (Fin M ⊕ Fin M) ℝ) :
    baseExpectation M (P+Q) = baseExpectation M P+baseExpectation M Q := by
  have hm : 0 < (M : ℝ) := Nat.cast_pos'.mpr hM
  unfold baseExpectation
  simp only [map_add,mul_add]
  rw [integral_add (basePolynomial_integrable hm P) (basePolynomial_integrable hm Q),add_div]

private theorem weightPolynomial_integrable {M : ℕ} (hM : 1 ≤ M) {γ : ℝ} (hγ : 0 < γ)
    (P : MvPolynomial (Fin M ⊕ Fin M) ℝ) :
    Integrable (fun p => weight M γ p*eval (Sum.elim p.1 p.2) P) := by
  have hm : 0 < (M : ℝ) := Nat.cast_pos'.mpr hM
  have h := ((crossIntegrand_integrable hm γ⁻¹ P).indicator (measurableSet_tailSet M γ).compl).const_mul (γ^(M^2))
  apply h.congr
  apply Eventually.of_forall
  intro p
  dsimp only
  rw [weight_scaled_cutoff hγ]
  by_cases hp : p ∈ (tailSet M γ)ᶜ <;> simp [hp,Set.indicator] <;> ring

private theorem singleMoment_derivative {M : ℕ} (hM : 1 ≤ M) (r : ℕ) :
    singleMoment M r = iteratedDeriv r (laguerreH M) 0 := by
  have h := laguerreWeighted_mgf_derivative hM 1 (by intro x; simp) r
  simpa only [singleMoment,laguerreH,map_one,mul_one] using h.symm

private theorem laguerreHw_iterated {M : ℕ} (hM : 1 ≤ M) (r : ℕ) :
    iteratedDeriv r (laguerreHw M) 0 =
      (∫ x, laguerreWeight M M x*(Finset.univ.expect (fun i => x i^2))*(Finset.univ.expect x)^r)/partition M M := by
  have h := laguerreWeighted_mgf_derivative hM ((Finset.univ.expect (fun i : Fin M => ((X i)^2 : MvPolynomial (Fin M) ℝ)))) (singleWPoly_nonneg M) r
  simpa only [laguerreHw,singleWPoly_eval] using h

theorem law_polynomial_integrable {M : ℕ} (hM : 1 ≤ M) {γ : ℝ} (hγ : 0 < γ)
    (P : MvPolynomial (Fin M ⊕ Fin M) ℝ) :
    Integrable (fun p => eval (Sum.elim p.1 p.2) P) (law M γ) := by
  unfold law
  apply Integrable.smul_measure _ (ENNReal.inv_ne_top.mpr (mass_pos M hγ).ne')
  apply (integrable_withDensity_iff_integrable_smul' (measurable_weight M γ).ennreal_ofReal
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)).mpr
  simpa only [smul_eq_mul,ENNReal.toReal_ofReal (weight_nonneg M γ _)] using weightPolynomial_integrable hM hγ P

theorem rescaled_pow_integrable {M : ℕ} (hM : 1 ≤ M) {γ : ℝ} (hγ : 0 < γ) (r : ℕ) :
    Integrable (fun p => rescaledObservable M γ p^r) (law M γ) := by
  have hs : integrableExpSet (rescaledObservable M γ) (law M γ) = Set.univ :=
    eq_univ_of_univ_subset (fun {t} _ => rescaledObservable_integrable_exp hM hγ t)
  exact integrable_pow_of_mem_interior_integrableExpSet (by simp [hs]) r

private theorem baseExpectation_densityCorrection {M : ℕ} (hM : 1 ≤ M) (r : ℕ) :
    baseExpectation M (((Finset.univ.expect (fun i : Fin M => (X (Sum.inl i) : MvPolynomial (Fin M ⊕ Fin M) ℝ))))^r*linearDensityPoly M) =
      (M : ℝ)^2*(singleMoment M (r+1)-singleMoment M r) := by
  have hm : 0 < (M : ℝ) := Nat.cast_pos'.mpr hM
  have hZ := (partition_pos M hm).ne'
  have hz (x : Fin M → ℝ) : (∑ i, x i) = (M : ℝ)*(Finset.univ.expect x) := by
    simpa only [Fintype.card_fin] using (Fintype.card_mul_expect x).symm
  let f := fun x : Fin M → ℝ => laguerreWeight M M x*(Finset.univ.expect x)^r
  let f₁ := fun x : Fin M → ℝ => laguerreWeight M M x*(Finset.univ.expect x)^(r+1)
  let g := fun y : Fin M → ℝ => laguerreWeight M M y*(∑ i, y i)
  have hf : Integrable f := laguerreZPower_integrable hM r
  have hf₁ : Integrable f₁ := laguerreZPower_integrable hM (r+1)
  have hw := laguerreWeight_integrable M hm
  have hg : Integrable g := by
    simpa only [map_sum,eval_X] using laguerrePolynomial_integrable hm (∑ i : Fin M, X i)
  have hp1 : (∫ y, g y) = (M : ℝ)*partition M M := by
    have h := laguerre_p1 (M := M) hm
    simp only [laguerreMoment,pow_one] at h
    have hh : (M : ℝ)^2/(M : ℝ) = M := by simpa only [pow_two] using mul_self_div_self (M : ℝ)
    rw [hh] at h
    have he : (fun y : Fin M → ℝ => (∑ i, y i)*laguerreWeight M M y) = g := by funext y; dsimp [g]; ring
    rw [he] at h
    exact (div_eq_iff hZ).mp h
  have he : (fun p => baseWeight M M p*eval (Sum.elim p.1 p.2) (((Finset.univ.expect (fun i : Fin M => (X (Sum.inl i) : MvPolynomial (Fin M ⊕ Fin M) ℝ))))^r*linearDensityPoly M)) =
      (fun p : (Fin M → ℝ) × (Fin M → ℝ) => (M : ℝ)^2*(f₁ p.1*laguerreWeight M M p.2)-
        (M : ℝ)*(f p.1*g p.2)) := by
    funext p
    simp only [map_mul,map_pow,zPoly_eval,linearDensityPoly_eval,baseWeight]
    rw [hz p.1]
    dsimp [f,f₁,g]
    rw [pow_succ]
    ring
  unfold baseExpectation singleMoment
  rw [he,Measure.volume_eq_prod,integral_sub ((hf₁.mul_prod hw).const_mul ((M : ℝ)^2)) ((hf.mul_prod hg).const_mul (M : ℝ)),
    integral_const_mul,integral_const_mul,integral_prod_mul,integral_prod_mul,hp1]
  change _/(partition M M)^2 = _
  dsimp only [f, f₁]
  change (((M : ℝ)^2*((∫ x, laguerreWeight M M x*(Finset.univ.expect x)^(r+1))*partition M M)-
    (M : ℝ)*((∫ x, laguerreWeight M M x*(Finset.univ.expect x)^r)*((M : ℝ)*partition M M)))/(partition M M)^2) = _
  field_simp
  <;> ring

theorem singleWMoment_derivative {M : ℕ} (hM : 1 ≤ M) (r : ℕ) :
    singleWMoment M r = iteratedDeriv r (laguerreHw M) 0 := (laguerreHw_iterated hM r).symm

private theorem rescaledExpansion_of_moments (hm : RescaledMomentExpansion) : RescaledExpansion := by
  intro M hM n hn
  let d := (M : ℝ)^2
  have hd : d ≠ 0 := pow_ne_zero _ (by exact_mod_cast (show M ≠ 0 by omega))
  have hK := gammaCGF_analytic d
  have hB := correctionCGF_analytic d
  have hK0 : gammaCGF d 0 = 0 := by simp [gammaCGF]
  have hB0 : correctionCGF d 0 = 0 := by simp [correctionCGF]
  have hk := cumulant_expansion_of_moments
    (fun r γ => ProbabilityTheory.moment (rescaledObservable M γ) r (law M γ)) (rescaledKappa M)
    (expJet (gammaCGF d)) (correctionJet (gammaCGF d) (correctionCGF d))
    (fun r => iteratedDeriv r (gammaCGF d) 0) (fun r => iteratedDeriv r (correctionCGF d) 0)
    (hm M hM)
    (fun γ hγ r => rescaled_moment_cumulant hM hγ r)
    (exp_jet_recurrence hK hK0) (correction_jet_recurrence hK hB hK0 hB0)
  have h := (hk n (by omega)).eventual_bound
  have he : (n-1)+1 = n := Nat.sub_add_cancel (by omega : 1 ≤ n)
  have hpow : d^(n-1) = (M : ℝ)^(2*n-2) := by
    dsimp [d]
    rw [← pow_mul]
    congr 1
    omega
  have hfact : (n.factorial : ℝ) = (n : ℝ)*(n-1).factorial := by
    exact_mod_cast (Nat.mul_factorial_pred (by omega : n ≠ 0)).symm
  have hc : iteratedDeriv n (gammaCGF d) 0 = (n-1).factorial/(M : ℝ)^(2*n-2) := by
    calc
      _ = iteratedDeriv ((n-1)+1) (gammaCGF d) 0 := by rw [he]
      _ = (n-1).factorial/d^(n-1) := gammaCGF_iterated hd (n-1)
      _ = _ := by rw [hpow]
  have hb : iteratedDeriv n (correctionCGF d) 0 =
      -((2*n-1)*n*(n-1).factorial/(M : ℝ)^(2*n-2)) := by
    rw [correctionCGF_iterated hd (by omega), hpow, hfact]
    ring
  obtain ⟨C,G,hG,hbound⟩ := h
  refine ⟨C,G,hG,?_⟩
  intro γ hγ
  have hh := hbound γ hγ
  rw [hc,hb] at hh
  convert hh using 1 <;> congr 1 <;> ring

private theorem signed_kappa_rescaled {M : ℕ} (hM : 1 ≤ M) {n : ℕ} (hn : 2 ≤ n) {γ : ℝ} (hγ : 0 < γ) :
    (-1 : ℝ)^n*kappa M n γ = γ⁻¹^(2*n)*rescaledKappa M n γ := by
  rw [kappa_rescaled hM hn hγ]
  unfold rescaledKappa
  have hs : (-1 : ℝ)^n*(-γ⁻¹^2)^n = γ⁻¹^(2*n) := by
    rw [← mul_pow]
    simp only [neg_mul_neg, one_mul, ← pow_mul]
  rw [← mul_assoc, hs]

private theorem assemble (h : RescaledExpansion) : claim := by
  intro M hM n hn
  obtain ⟨C, γ₀, hγ₀, hbound⟩ := h M hM n hn
  refine ⟨C, γ₀, hγ₀, ?_⟩
  intro γ hγ
  have hγpos : 0 < γ := lt_of_lt_of_le hγ₀ hγ
  have hΓ := hbound γ hγ
  have hmul := mul_le_mul_of_nonneg_left hΓ (pow_nonneg (inv_nonneg.mpr hγpos.le) (2*n))
  rw [signed_kappa_rescaled hM hn hγpos]
  have he : ((n-1).factorial/((M : ℝ)^(2*n-2)*γ^(2*n))-
      (2*n-1)*n*(n-1).factorial/((M : ℝ)^(2*n-2)*γ^(2*n+1))) =
      γ⁻¹^(2*n)*((n-1).factorial/(M : ℝ)^(2*n-2)-
       (2*n-1)*n*(n-1).factorial/((M : ℝ)^(2*n-2)*γ)) := by
    have hm : (M : ℝ) ≠ 0 := by exact_mod_cast (show M ≠ 0 by omega)
    simp only [pow_add, pow_one, inv_pow]
    field_simp [hm, hγpos.ne']
    <;> ring
  rw [he, ← mul_sub, abs_mul, abs_of_nonneg (pow_nonneg (inv_nonneg.mpr hγpos.le) (2*n))]
  have hr : γ⁻¹^(2*n)*(C/γ^2) = C/γ^(2*n+2) := by simp [pow_add, div_eq_mul_inv]; ring
  rw [hr] at hmul
  exact hmul

private theorem law_remainder_bigO {M : ℕ} (hM : 1 ≤ M)
    (f : ℝ → (Fin M → ℝ) × (Fin M → ℝ) → ℝ)
    (P : MvPolynomial (Fin M ⊕ Fin M) ℝ)
    (hbound : ∀ γ : ℝ, 1 ≤ γ → ∀ p, p ∈ supportSet M γ →
      |f γ p| ≤ γ⁻¹^2*eval (Sum.elim p.1 p.2) P) :
    (fun γ => ∫ p, f γ p ∂law M γ) =O[atTop] (fun γ : ℝ => γ⁻¹^2) := by
  have hE := (law_polynomial_firstOrder hM P).tendsto
  have hEB : (fun γ => ∫ p, eval (Sum.elim p.1 p.2) P ∂law M γ) =O[atTop] (fun _ => (1 : ℝ)) :=
    isBigO_const_of_tendsto hE one_ne_zero
  obtain ⟨C,hC⟩ := hEB.bound
  apply IsBigO.of_bound C
  filter_upwards [hC,eventually_ge_atTop (1 : ℝ)] with γ hc hγ
  have hpos := lt_of_lt_of_le zero_lt_one hγ
  have hb : ∀ᵐ p ∂law M γ, ‖f γ p‖ ≤ γ⁻¹^2*eval (Sum.elim p.1 p.2) P := by
    filter_upwards [law_ae_support M γ] with p hp
    simpa only [Real.norm_eq_abs] using hbound γ hγ p hp
  have hi := norm_integral_le_of_norm_le ((law_polynomial_integrable hM hpos P).const_mul (γ⁻¹^2)) hb
  rw [integral_const_mul] at hi
  have hh := (le_abs_self (∫ p, eval (Sum.elim p.1 p.2) P ∂law M γ)).trans (by simpa only [Real.norm_eq_abs,norm_one,mul_one] using hc)
  have hfinal := hi.trans (mul_le_mul_of_nonneg_left hh (sq_nonneg γ⁻¹))
  simpa only [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg γ⁻¹),mul_comm] using hfinal

private theorem laguerreH_analytic {M : ℕ} (hM : 1 ≤ M) : AnalyticAt ℝ (laguerreH M) 0 :=
  (gammaCGF_analytic ((M : ℝ)^2)).rexp'.congr (laguerreH_near hM).symm

private theorem result_of_moments (hm : RescaledMomentExpansion) : claim :=
  assemble (rescaledExpansion_of_moments hm)

private theorem variable_observable_firstOrder {M : ℕ} (hM : 1 ≤ M)
    (f : ℝ → (Fin M → ℝ) × (Fin M → ℝ) → ℝ)
    (P₀ P₁ G : MvPolynomial (Fin M ⊕ Fin M) ℝ)
    (hf : ∀ γ : ℝ, 0 < γ → Integrable (f γ) (law M γ))
    (hbound : ∀ γ : ℝ, 1 ≤ γ → ∀ p, p ∈ supportSet M γ →
      |f γ p-eval (Sum.elim p.1 p.2) P₀-γ⁻¹*eval (Sum.elim p.1 p.2) P₁| ≤
        γ⁻¹^2*eval (Sum.elim p.1 p.2) G) :
    FirstOrder (fun γ => ∫ p, f γ p ∂law M γ)
      (baseExpectation M P₀) (baseExpectation M (P₀*linearDensityPoly M)+baseExpectation M P₁) := by
  let R := fun γ p => f γ p-eval (Sum.elim p.1 p.2) P₀-γ⁻¹*eval (Sum.elim p.1 p.2) P₁
  have hR : FirstOrder (fun γ => ∫ p, R γ p ∂law M γ) 0 0 := by
    simpa only [FirstOrder,sub_zero,zero_mul] using law_remainder_bigO hM R G hbound
  have h0 := law_polynomial_firstOrder hM P₀
  have h1 := (FirstOrder.affine (0 : ℝ) 1).mul (law_polynomial_firstOrder hM P₁)
  simp only [zero_add,one_mul,zero_mul,add_zero] at h1
  have h := hR.add (h0.add h1)
  simp only [zero_add,add_zero] at h
  apply D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.FirstOrder.congr_eventually h
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with γ hγ
  have hpos := lt_of_lt_of_le zero_lt_one hγ
  have hi0 := law_polynomial_integrable hM hpos P₀
  have hi1 := law_polynomial_integrable hM hpos P₁
  dsimp only [R]
  change (∫ p, (f γ-(fun p : (Fin M → ℝ) × (Fin M → ℝ) => eval (Sum.elim p.1 p.2) P₀)) p-
      γ⁻¹*eval (Sum.elim p.1 p.2) P₁ ∂law M γ)+_ = _
  rw [integral_sub ((hf γ hpos).sub hi0) (hi1.const_mul γ⁻¹)]
  simp only [Pi.sub_apply]
  rw [integral_sub (hf γ hpos) hi0,integral_const_mul]
  ring

private theorem rescaled_moment_integral_expansion_high {M : ℕ} (hM : 1 ≤ M) (k : ℕ) :
    FirstOrder ((fun γ => ProbabilityTheory.moment (rescaledObservable M γ) (k+2) (law M γ)))
      (baseExpectation M (((Finset.univ.expect (fun i : Fin M => (X (Sum.inl i) : MvPolynomial (Fin M ⊕ Fin M) ℝ))))^(k+2)))
      (baseExpectation M (((Finset.univ.expect (fun i : Fin M => (X (Sum.inl i) : MvPolynomial (Fin M ⊕ Fin M) ℝ))))^(k+2)*linearDensityPoly M)+
        baseExpectation M (observableCorrectionPoly M (k+2))) := by
  apply variable_observable_firstOrder hM _ _ _ (powerErrorPoly M k)
    (fun γ hγ => rescaled_pow_integrable hM hγ (k+2))
  intro γ hγ p hp
  have hpos := lt_of_lt_of_le zero_lt_one hγ
  have hx := ((supportSet_membership M γ p).mp hp).1
  rw [rescaledObservable_eq_u hM hpos p hx]
  simp only [observableCorrectionPoly,map_mul,map_neg,eval_C,map_pow,zPoly_eval,wPoly_eval,
    powerErrorPoly_eval]
  have he : k+2-1 = k+1 := Nat.add_succ_sub_one k 1
  rw [he]
  convert observable_power_remainder (inv_nonneg.mpr hpos.le) p.1 hx k using 1 <;> congr 1 <;> simp only [Nat.cast_add, Nat.cast_ofNat] <;> ring

private theorem rescaled_moment_integral_expansion_one {M : ℕ} (hM : 1 ≤ M) :
    FirstOrder ((fun γ => ProbabilityTheory.moment (rescaledObservable M γ) 1 (law M γ)))
      (baseExpectation M ((Finset.univ.expect (fun i : Fin M => (X (Sum.inl i) : MvPolynomial (Fin M ⊕ Fin M) ℝ)))))
      (baseExpectation M ((Finset.univ.expect (fun i : Fin M => (X (Sum.inl i) : MvPolynomial (Fin M ⊕ Fin M) ℝ)))*linearDensityPoly M)+baseExpectation M (-(Finset.univ.expect (fun i : Fin M => ((X (Sum.inl i))^2 : MvPolynomial (Fin M ⊕ Fin M) ℝ))))) := by
  apply variable_observable_firstOrder hM _ _ _ ((Finset.univ.expect (fun i : Fin M => ((X (Sum.inl i))^3 : MvPolynomial (Fin M ⊕ Fin M) ℝ))))
    (fun γ hγ => rescaled_pow_integrable hM hγ 1)
  intro γ hγ p hp
  have hpos := lt_of_lt_of_le zero_lt_one hγ
  have hx := ((supportSet_membership M γ p).mp hp).1
  rw [rescaledObservable_eq_u hM hpos p hx]
  simp only [map_neg,zPoly_eval,wPoly_eval,qPoly_eval,pow_one]
  convert observable_power_one (inv_nonneg.mpr hpos.le) p.1 hx using 1 <;> congr 1 <;> ring

private theorem laguerreHw_analytic {M : ℕ} (hM : 1 ≤ M) : AnalyticAt ℝ (laguerreHw M) 0 := by
  have hK := (gammaCGF_analytic ((M : ℝ)^2)).rexp'
  have hS : AnalyticAt ℝ (inverseSlope ((M : ℝ)^2)) 0 := by
    unfold inverseSlope
    fun_prop (disch := simp)
  have h : AnalyticAt ℝ (fun t => 2*Real.exp (gammaCGF ((M : ℝ)^2) t)*(inverseSlope ((M : ℝ)^2) t)^2) 0 := by
    fun_prop
  exact h.congr (laguerreHw_near hM).symm

private theorem modelCorrection_near {M : ℕ} (hM : 1 ≤ M) :
    (fun t => Real.exp (gammaCGF ((M : ℝ)^2) t)*correctionCGF ((M : ℝ)^2) t) =ᶠ[𝓝 0]
      (fun t => (M : ℝ)^2*(deriv (laguerreH M) t-laguerreH M t)-t*laguerreHw M t) := by
  let d := (M : ℝ)^2
  have hd : d ≠ 0 := pow_ne_zero _ (by exact_mod_cast (show M ≠ 0 by omega))
  have hD := ((laguerreH_near hM).deriv).trans (exp_deriv_near (gammaCGF_analytic d))
  have hS : ∀ᶠ t : ℝ in 𝓝 0, 1-t/d ≠ 0 := by
    exact (by fun_prop : ContinuousAt (fun t : ℝ => 1-t/d) 0).eventually_ne (by simp)
  filter_upwards [laguerreH_near hM,laguerreHw_near hM,hD,hS] with t ht hw hdv hs
  rw [ht,hw,hdv,gammaCGF_deriv hd]
  change Real.exp (gammaCGF d t) * correctionCGF d t =
    d * (inverseSlope d t * Real.exp (gammaCGF d t) - Real.exp (gammaCGF d t)) -
      t * (2 * Real.exp (gammaCGF d t) * inverseSlope d t ^ 2)
  have hdt : d-t ≠ 0 := by
    intro h
    have ht : t = d := (sub_eq_zero.mp h).symm
    apply hs
    simp [ht, hd]
  have hsEq : 1-t/d = (d-t)/d := one_sub_div hd
  unfold inverseSlope correctionCGF
  rw [hsEq]
  field_simp [hd, hdt]
  <;> ring

private theorem rescaled_moment_integral_expansion {M : ℕ} (hM : 1 ≤ M) (r : ℕ) :
    FirstOrder ((fun γ => ProbabilityTheory.moment (rescaledObservable M γ) r (law M γ)))
      (baseExpectation M (((Finset.univ.expect (fun i : Fin M => (X (Sum.inl i) : MvPolynomial (Fin M ⊕ Fin M) ℝ))))^r))
      (baseExpectation M (((Finset.univ.expect (fun i : Fin M => (X (Sum.inl i) : MvPolynomial (Fin M ⊕ Fin M) ℝ))))^r*linearDensityPoly M+observableCorrectionPoly M r)) := by
  cases r with
  | zero =>
    have hP : baseExpectation M 1 = 1 := by
      unfold baseExpectation
      simp only [map_one,mul_one,baseWeight_mass]
      exact div_self (pow_ne_zero _ (partition_pos M (by exact_mod_cast (show 0 < M by omega))).ne')
    have hL : baseExpectation M (linearDensityPoly M) = 0 := by
      simp [baseExpectation,linearDensityIntegral_zero]
    have he : (fun γ => ProbabilityTheory.moment (rescaledObservable M γ) 0 (law M γ)) =ᶠ[Filter.atTop] (fun _ => (1 : ℝ)) := by
      filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with γ hγ
      letI := law_isProbability hM (lt_of_lt_of_le zero_lt_one hγ)
      simp [ProbabilityTheory.moment]
    simp only [pow_zero,observableCorrectionPoly,Nat.cast_zero,map_zero,neg_zero,zero_mul,add_zero,one_mul,hP,hL]
    exact D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.FirstOrder.congr_eventually
      (FirstOrder.const (1 : ℝ)) he.symm
  | succ r =>
    cases r with
    | zero =>
      have h := rescaled_moment_integral_expansion_one hM
      simpa [observableCorrectionPoly,baseExpectation_add hM] using h
    | succ k =>
      have h := rescaled_moment_integral_expansion_high hM k
      simpa only [Nat.succ_eq_add_one,Nat.add_assoc, Nat.reduceAdd, baseExpectation_add hM] using h

private theorem correctionJet_moments {M : ℕ} (hM : 1 ≤ M) (r : ℕ) :
    correctionJet (gammaCGF ((M : ℝ)^2)) (correctionCGF ((M : ℝ)^2)) r =
      (M : ℝ)^2*(iteratedDeriv (r+1) (laguerreH M) 0-iteratedDeriv r (laguerreH M) 0)-
      (r : ℝ)*iteratedDeriv (r-1) (laguerreHw M) 0 := by
  unfold correctionJet
  rw [(modelCorrection_near hM).iteratedDeriv_eq]
  have hD : ContDiffAt ℝ r (deriv (laguerreH M)) 0 := (laguerreH_analytic hM).deriv.contDiffAt
  have hH : ContDiffAt ℝ r (laguerreH M) 0 := (laguerreH_analytic hM).contDiffAt
  rw [iteratedDeriv_fun_sub
    (contDiffAt_const.mul (hD.sub hH))
    (by exact (by fun_prop : ContDiffAt ℝ r (fun t : ℝ => t) 0).mul (laguerreHw_analytic hM).contDiffAt)]
  rw [iteratedDeriv_const_mul_field,
    iteratedDeriv_fun_sub (laguerreH_analytic hM).deriv.contDiffAt (laguerreH_analytic hM).contDiffAt,
    ← iteratedDeriv_succ',iteratedDeriv_id_mul (laguerreHw_analytic hM)]

private theorem baseMoment_models {M : ℕ} (hM : 1 ≤ M) (r : ℕ) :
    baseExpectation M (((Finset.univ.expect (fun i : Fin M => (X (Sum.inl i) : MvPolynomial (Fin M ⊕ Fin M) ℝ))))^r) = expJet (gammaCGF ((M : ℝ)^2)) r ∧
    baseExpectation M (((Finset.univ.expect (fun i : Fin M => (X (Sum.inl i) : MvPolynomial (Fin M ⊕ Fin M) ℝ))))^r*linearDensityPoly M+observableCorrectionPoly M r) =
      correctionJet (gammaCGF ((M : ℝ)^2)) (correctionCGF ((M : ℝ)^2)) r := by
  constructor
  · rw [baseExpectation_z hM r]
    exact laguerreH_iterated hM r
  · rw [baseExpectation_add hM,baseExpectation_densityCorrection hM r,
      baseExpectation_observableCorrection hM r,singleMoment_derivative hM,
      singleMoment_derivative hM,singleWMoment_derivative hM,correctionJet_moments hM r]
    ring

theorem rescaledMomentExpansion : RescaledMomentExpansion := by
  intro M hM r
  have h := rescaled_moment_integral_expansion hM r
  obtain ⟨h0,h1⟩ := baseMoment_models hM r
  rw [h0,h1] at h
  exact h

theorem result : claim := result_of_moments rescaledMomentExpansion

end D5.S3.Quantum.Transport.StrongAbsorptionCumulants
