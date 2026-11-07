/- GID: D5/S3/Analytic/Probability/SampleCovarianceLogEnergyRefutation
   generality: I
   mirror-B: D5/B/S3/Analytic/Probability/SampleCovarianceLogEnergyRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Analytic/Probability/SampleCovarianceLogEnergyRefutation.claim; result=D5/S3/Analytic/Probability/SampleCovarianceLogEnergyRefutation.result; claim=D5/S3/Analytic/Probability/SampleCovarianceLogEnergyRefutation.claim
   digest: Failure of covariance logarithmic-energy monotonicity. -/
/-
proof_shape: pending per-declaration verification.
escape_witness: none claimed before the upstream-only tests.
admission_basis: open-problem-resolution (#27294; Refuted)
Direct frozen dependencies: pending compiled-constant extraction.
-/
import D5.S3.Analytic.Probability.GaussianPolynomialLog
import D5.S3.Analytic.Probability.SampleCovarianceSpectralAndSmooth
import D5.S3.Analytic.Probability.SampleCovarianceBernoulliOrders
import D5.S3.StatisticalMechanics.ParticleProcesses.ExclusionMovingParticleOptimality
open D5.S3.Analytic.Probability.SampleCovarianceSpectralAndSmooth
open MeasureTheory Filter Set ProbabilityTheory Matrix Polynomial
open scoped ENNReal NNReal Topology BigOperators Kronecker
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2500000
namespace D5.S3.Analytic.Probability.SampleCovarianceLogEnergyRefutation.Analytic
noncomputable section
private def realNoise {n : ℕ} (x : Fin ((Fintype.card (Bool × Bool × Fin n × Fin n))) → ℝ) (side : Bool) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of (fun i j => (x ((Fintype.equivFin (Bool × Bool × Fin n × Fin n)) (side,false,i,j)) : ℂ) +
    Complex.I * (x ((Fintype.equivFin (Bool × Bool × Fin n × Fin n)) (side,true,i,j)) : ℂ))
private lemma renamed_ne_zero {n : ℕ} {p : (MvPolynomial (Bool × Bool × Fin n × Fin n) ℂ)} (hp : p ≠ 0) : (MvPolynomial.rename (Fintype.equivFin (Bool × Bool × Fin n × Fin n))) p ≠ 0 :=
  (MvPolynomial.rename_eq_zero_iff_of_injective p ((Fintype.equivFin (Bool × Bool × Fin n × Fin n))).injective).not.mpr hp
private lemma eval_renamed {n : ℕ} (p : (MvPolynomial (Bool × Bool × Fin n × Fin n) ℂ)) (x : Fin ((Fintype.card (Bool × Bool × Fin n × Fin n))) → ℝ) :
    (fun {n : ℕ} (p : MvPolynomial (Fin n) ℂ) (x : Fin n → ℝ) => MvPolynomial.eval (fun i => (x i : ℂ)) p) ((MvPolynomial.rename (Fintype.equivFin (Bool × Bool × Fin n × Fin n))) p) x =
      D5.S3.Analytic.Probability.SampleCovarianceBernoulliOrders.Noise.evalNoise (realNoise x false) (realNoise x true) p := by
  dsimp only
  rw [MvPolynomial.eval_rename]
  have he : MvPolynomial.eval (fun i : (Bool × Bool × Fin n × Fin n) => (x ((Fintype.equivFin (Bool × Bool × Fin n × Fin n)) i) : ℂ)) =
      D5.S3.Analytic.Probability.SampleCovarianceBernoulliOrders.Noise.evalNoise (realNoise x false) (realNoise x true) := by
    apply MvPolynomial.ringHom_ext
    · intro z
      simp [D5.S3.Analytic.Probability.SampleCovarianceBernoulliOrders.Noise.evalNoise]
    · intro i
      rcases i with ⟨side,im,i,j⟩
      cases side <;> cases im <;> simp [D5.S3.Analytic.Probability.SampleCovarianceBernoulliOrders.Noise.evalNoise, realNoise]
  exact congrArg (fun f : (MvPolynomial (Bool × Bool × Fin n × Fin n) ℂ) →+* ℂ => f p) he
private lemma gaussian_det_nonzero_integrable {n : ℕ}
    (A C : Matrix (Fin n) (Fin n) ℂ) (ε : ℝ) (hε : ε ≠ 0)
    (m : ℝ) (v : ℝ≥0) (hv : v ≠ 0) :
    (∀ᵐ x ∂(fun n m v => Measure.pi (fun _ : Fin n => gaussianReal m v)) ((Fintype.card (Bool × Bool × Fin n × Fin n))) m v,
      Matrix.det (((A+(ε:ℂ) • realNoise x false)*(A+(ε:ℂ) • realNoise x false)ᴴ) ⊗ₖ
        (1 : Matrix (Fin n) (Fin n) ℂ) - (1 : Matrix (Fin n) (Fin n) ℂ) ⊗ₖ
        ((C+(ε:ℂ) • realNoise x true)*(C+(ε:ℂ) • realNoise x true)ᴴ)) ≠ 0) ∧
    Integrable (fun x => Real.log ‖Matrix.det
      (((A+(ε:ℂ) • realNoise x false)*(A+(ε:ℂ) • realNoise x false)ᴴ) ⊗ₖ
        (1 : Matrix (Fin n) (Fin n) ℂ) - (1 : Matrix (Fin n) (Fin n) ℂ) ⊗ₖ
        ((C+(ε:ℂ) • realNoise x true)*(C+(ε:ℂ) • realNoise x true)ᴴ))‖)
      ((fun n m v => Measure.pi (fun _ : Fin n => gaussianReal m v)) ((Fintype.card (Bool × Bool × Fin n × Fin n))) m v) := by
  have h := D5.S3.Analytic.Probability.SampleCovarianceBernoulliOrders.Gaussian.gaussian_mv_log_integrable m v hv
    ((MvPolynomial.rename (Fintype.equivFin (Bool × Bool × Fin n × Fin n))) (D5.S3.Analytic.Probability.SampleCovarianceBernoulliOrders.Noise.polyAt A C ε)) (renamed_ne_zero (D5.S3.Analytic.Probability.SampleCovarianceBernoulliOrders.Noise.polyAt_ne_zero A C ε hε))
  simpa only [eval_renamed, D5.S3.Analytic.Probability.SampleCovarianceBernoulliOrders.Noise.evalNoise_polyAt, D5.S3.Analytic.Probability.SampleCovarianceBernoulliOrders.Noise.eval_pairDet] using h

private lemma polynomial_log_order {d : ℕ} (m : ℝ) (v : ℝ≥0) (hv : v ≠ 0)
    (P : Polynomial (MvPolynomial (Fin d) ℂ)) (k : ℕ)
    (hlo : ∀ j < k, P.coeff j = 0) (hk : P.coeff k ≠ 0) :
    Tendsto (fun ε : ℝ => -(∫ x, Real.log ‖(fun {n : ℕ} (p : MvPolynomial (Fin n) ℂ) (x : Fin n → ℝ) => MvPolynomial.eval (fun i => (x i : ℂ)) p)
      (P.eval (MvPolynomial.C (ε:ℂ))) x‖ ∂(fun n m v => Measure.pi (fun _ : Fin n => gaussianReal m v)) d m v) /
        Real.log (1/ε)) (𝓝[>] 0) (𝓝 (k:ℝ)) := by
  obtain ⟨Q,hQ⟩ := Polynomial.X_pow_dvd_iff.mpr hlo
  have hq0 : Q.coeff 0 ≠ 0 := by
    intro h
    apply hk
    rw [hQ]
    simpa only [Nat.zero_add] using (Polynomial.coeff_X_pow_mul Q k 0).trans h
  let q : Fin (Q.natDegree+1) → MvPolynomial (Fin d) ℂ := fun j => Q.coeff j
  obtain ⟨a,ha⟩ := MvPolynomial.exists_coeff_ne_zero hq0
  have he (ε : ℝ) : Q.eval (MvPolynomial.C (ε:ℂ)) = (∑ j : Fin (Q.natDegree+1), MvPolynomial.C ((ε : ℂ)^(j : ℕ)) * q j) := by
    rw [Polynomial.eval_eq_sum_range]
    rw [← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro j hj
    simp only [q, ← map_pow, mul_comm]
  have h := D5.S3.Analytic.Probability.SampleCovarianceBernoulliOrders.Gaussian.gaussian_noiseFamily_log_order m v hv q a ha k
  simpa only [hQ, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X, he,
    map_mul, map_pow, MvPolynomial.eval_C] using h
private def finPoly {n : ℕ} (A C : Matrix (Fin n) (Fin n) ℂ) :
    Polynomial (MvPolynomial (Fin ((Fintype.card (Bool × Bool × Fin n × Fin n)))) ℂ) :=
  Polynomial.map (MvPolynomial.rename ((Fintype.equivFin (Bool × Bool × Fin n × Fin n)))).toRingHom (D5.S3.Analytic.Probability.SampleCovarianceBernoulliOrders.Noise.poly A C)
private lemma finPoly_coeff {n : ℕ} (A C : Matrix (Fin n) (Fin n) ℂ) (j : ℕ) :
    (finPoly A C).coeff j = (MvPolynomial.rename (Fintype.equivFin (Bool × Bool × Fin n × Fin n))) ((D5.S3.Analytic.Probability.SampleCovarianceBernoulliOrders.Noise.poly A C).coeff j) := by
  simp [finPoly]
private lemma finPoly_eval {n : ℕ} (A C : Matrix (Fin n) (Fin n) ℂ) (ε : ℝ) :
    (finPoly A C).eval (MvPolynomial.C (ε:ℂ)) = (MvPolynomial.rename (Fintype.equivFin (Bool × Bool × Fin n × Fin n))) (D5.S3.Analytic.Probability.SampleCovarianceBernoulliOrders.Noise.polyAt A C ε) := by
  simpa [finPoly, D5.S3.Analytic.Probability.SampleCovarianceBernoulliOrders.Noise.polyAt] using
    Polynomial.eval_map_apply (f:=(MvPolynomial.rename ((Fintype.equivFin (Bool × Bool × Fin n × Fin n)))).toRingHom)
      (p:=D5.S3.Analytic.Probability.SampleCovarianceBernoulliOrders.Noise.poly A C) (MvPolynomial.C (ε:ℂ))
private lemma gaussian_pairDet_log_order {n : ℕ} (A C : Matrix (Fin n) (Fin n) ℂ)
    (m : ℝ) (v : ℝ≥0) (hv : v ≠ 0) :
    Tendsto (fun ε : ℝ => -(∫ x, Real.log ‖
      (D5.S3.Analytic.Probability.GaussianPolynomialLog.Covariance.pairDet A C (realNoise x false) (realNoise x true)).eval (ε:ℂ)‖
      ∂(fun n m v => Measure.pi (fun _ : Fin n => gaussianReal m v)) ((Fintype.card (Bool × Bool × Fin n × Fin n))) m v) / Real.log (1/ε))
      (𝓝[>] 0) (𝓝 ((D5.S3.Analytic.Probability.SampleCovarianceBernoulliOrders.Noise.poly A C).natTrailingDegree:ℝ)) := by
  have hp := D5.S3.Analytic.Probability.SampleCovarianceBernoulliOrders.Noise.poly_ne_zero A C
  have hlo : ∀ j < (D5.S3.Analytic.Probability.SampleCovarianceBernoulliOrders.Noise.poly A C).natTrailingDegree, (finPoly A C).coeff j = 0 := by
    intro j hj
    rw [finPoly_coeff, Polynomial.coeff_eq_zero_of_lt_natTrailingDegree hj]
    exact map_zero _
  have hk : (finPoly A C).coeff (D5.S3.Analytic.Probability.SampleCovarianceBernoulliOrders.Noise.poly A C).natTrailingDegree ≠ 0 := by
    rw [finPoly_coeff]
    exact renamed_ne_zero (Polynomial.coeff_natTrailingDegree_ne_zero.mpr hp)
  have h := polynomial_log_order m v hv (finPoly A C) (D5.S3.Analytic.Probability.SampleCovarianceBernoulliOrders.Noise.poly A C).natTrailingDegree hlo hk
  simpa only [finPoly_eval, eval_renamed, D5.S3.Analytic.Probability.SampleCovarianceBernoulliOrders.Noise.evalNoise_polyAt] using h
end
end D5.S3.Analytic.Probability.SampleCovarianceLogEnergyRefutation.Analytic
open MeasureTheory Filter Matrix
open scoped ENNReal Topology BigOperators
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2500000
namespace D5.S3.Analytic.Probability.SampleCovarianceLogEnergyRefutation
noncomputable section
private lemma gramEigenvalue_sum (n : ℕ) (A : Matrix (Fin n) (Fin n) ℂ) :
    (∑ i, gramEigenvalue n A i) = ∑ i, ∑ j, ‖A i j‖^2 := by
  have h := congrArg Complex.re (gramHermitian n A).trace_eq_sum_eigenvalues
  simp only [map_sum, Complex.re_sum, Complex.ofReal_re] at h
  change (Matrix.trace ((A * Aᴴ))).re = ∑ i, gramEigenvalue n A i at h
  rw [← h]
  simp only [ Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  simp [Complex.mul_re, Complex.sq_norm, Complex.normSq_apply, Complex.star_def]
private lemma entry_second_integrable (n : ℕ) (μ : Measure ℂ) [IsProbabilityMeasure μ]
    (hμ : EntryLaw μ) (i j : Fin n) :
    Integrable (fun A : Matrix (Fin n) (Fin n) ℂ => ‖A i j‖^2) (matrixLaw n μ) := by
  apply (integrable_map_measure (Matrix.measurable_apply.norm.pow_const 2).aestronglyMeasurable
    (Measurable.of_eval_matrix _ (fun a b => measurable_pi_apply (a,b))).aemeasurable).mpr
  exact integrable_comp_eval (μ:=fun _ : Fin n × Fin n => μ) (i:=(i,j)) hμ.2.2.1
private lemma entry_second_integral (n : ℕ) (μ : Measure ℂ) [IsProbabilityMeasure μ]
    (hμ : EntryLaw μ) (i j : Fin n) :
    (∫ A : Matrix (Fin n) (Fin n) ℂ, ‖A i j‖^2 ∂matrixLaw n μ) = 1 := by
  rw [matrixLaw, integral_map
    (Measurable.of_eval_matrix _ (fun a b => measurable_pi_apply (a,b))).aemeasurable
    (Matrix.measurable_apply.norm.pow_const 2).aestronglyMeasurable]
  exact (integral_comp_eval (μ:=fun _ : Fin n × Fin n => μ) (i:=(i,j))
    hμ.2.2.1.aestronglyMeasurable).trans hμ.2.2.2.2
private lemma gramEigenvalue_integrable (n : ℕ) (μ : Measure ℂ) [IsProbabilityMeasure μ]
    (hμ : EntryLaw μ) (i : Fin n) :
    Integrable (fun A => gramEigenvalue n A i) (matrixLaw n μ) := by
  apply (integrable_finsetSum Finset.univ (fun j _ =>
    integrable_finsetSum Finset.univ (fun k _ => entry_second_integrable n μ hμ j k))).mono'
  · exact (measurable_gramEigenvalue n i).aestronglyMeasurable
  · filter_upwards [] with A
    rw [Real.norm_eq_abs, abs_of_nonneg (gramEigenvalue_nonneg n A i), ← gramEigenvalue_sum]
    exact Finset.single_le_sum (fun j _ => gramEigenvalue_nonneg n A j) (Finset.mem_univ i)
private lemma sum_gramEigenvalue_integrals (n : ℕ) (μ : Measure ℂ) [IsProbabilityMeasure μ]
    (hμ : EntryLaw μ) :
    (∑ i, ∫ A, gramEigenvalue n A i ∂matrixLaw n μ) = (n:ℝ)^2 := by
  rw [← integral_finsetSum _ (fun i _ => gramEigenvalue_integrable n μ hμ i)]
  simp_rw [gramEigenvalue_sum]
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _
    (fun j _ => entry_second_integrable n μ hμ i j))]
  simp_rw [integral_finsetSum _ (fun j _ => entry_second_integrable n μ hμ _ j),
    entry_second_integral n μ hμ]
  simp [pow_two]
private lemma firstMoment_mean_eq_one (n : ℕ) (hn : 0 < n) (μ : Measure ℂ) [IsProbabilityMeasure μ]
    (hμ : EntryLaw μ) : firstMoment (meanSpectralMeasure n hn μ) = 1 := by
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have hmax (A : Matrix (Fin n) (Fin n) ℂ) (i : Fin n) :
      max (gramEigenvalue n A i / n) 0 = gramEigenvalue n A i / n :=
    max_eq_left (div_nonneg (gramEigenvalue_nonneg n A i) hnR.le)
  have hlin (i : Fin n) :
      (∫⁻ A, ENNReal.ofReal (gramEigenvalue n A i / n) ∂matrixLaw n μ) =
        ENNReal.ofReal ((∫ A, gramEigenvalue n A i ∂matrixLaw n μ) / n) := by
    rw [← ofReal_integral_eq_lintegral_ofReal ((gramEigenvalue_integrable n μ hμ i).div_const _)
      (Filter.Eventually.of_forall (fun A => div_nonneg (gramEigenvalue_nonneg n A i) hnR.le)),
      integral_div]
  unfold firstMoment
  rw [lintegral_meanSpectralMeasure n hn μ _ (by fun_prop)]
  simp_rw [hmax]
  rw [lintegral_finsetSum _ (fun i _ => by fun_prop)]
  simp_rw [hlin]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => div_nonneg
    (integral_nonneg (fun A => gramEigenvalue_nonneg n A i)) hnR.le), ← Finset.sum_div,
    sum_gramEigenvalue_integrals n μ hμ]
  have he : (n:ℝ)^2 / n = n := by field_simp [hnR.ne']
  rw [he]
  have hcast : ENNReal.ofReal (n:ℝ) = (n:ℝ≥0∞) := by simp
  rw [hcast, ENNReal.inv_mul_cancel (by exact_mod_cast hn.ne') (by simp)]
  simp
end
end D5.S3.Analytic.Probability.SampleCovarianceLogEnergyRefutation
open MeasureTheory ProbabilityTheory Set Matrix
open scoped ENNReal NNReal BigOperators
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2500000
namespace D5.S3.Analytic.Probability.SampleCovarianceLogEnergyRefutation.Transport
noncomputable section
private lemma pi_mixture {ι X : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace X]
    (ν : ι → Bool → Measure X) [∀ i b, IsProbabilityMeasure (ν i b)]
    (q p : ℝ≥0∞) (hq : q ≠ ∞) (hp : p ≠ ∞) :
    Measure.pi (fun i => q • ν i false + p • ν i true) =
      ∑ b : ι → Bool, (∏ i, if b i then p else q) • Measure.pi (fun i => ν i (b i)) := by
  haveI (i : ι) : IsFiniteMeasure (q • ν i false + p • ν i true) := by
    constructor
    rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply]
    simp only [measure_univ, smul_eq_mul, mul_one]
    exact ENNReal.add_lt_top.mpr ⟨hq.lt_top, hp.lt_top⟩
  apply Measure.pi_eq
  intro s hs
  have hset : MeasurableSet (Set.univ.pi s) := MeasurableSet.univ_pi hs
  simp only [Measure.finsetSum_apply, Measure.smul_apply, Measure.pi_pi,
    Measure.add_apply, hset, smul_eq_mul]
  simp_rw [← Finset.prod_mul_distrib]
  have he := Fintype.prod_sum (fun i (b : Bool) => (if b then p else q) * ν i b (s i))
  simpa [Fintype.sum_bool, add_comm] using he.symm
private lemma pack_preserving (n : ℕ) (v : ℝ≥0) :
    MeasurePreserving (fun x : (Bool × Bool × Fin n × Fin n) → ℝ =>
      fun i : Bool × Fin n × Fin n => (x (i.1,false,i.2), x (i.1,true,i.2))) ((fun n v => Measure.pi (fun _ : Bool × Bool × Fin n × Fin n => gaussianReal 0 v)) n v)
      (Measure.pi (fun _ : (Bool × Fin n × Fin n) => (gaussianReal 0 v).prod (gaussianReal 0 v))) := by
  let e := MeasurableEquiv.sumPiEquivProdPi (fun _ : (Bool × Fin n × Fin n) ⊕ (Bool × Fin n × Fin n) => ℝ)
  have h1 := measurePreserving_piCongrLeft
    (fun _ : (Bool × Fin n × Fin n) ⊕ (Bool × Fin n × Fin n) => gaussianReal 0 v) ((((Equiv.prodAssoc Bool Bool (Fin n × Fin n)).symm.trans ((Equiv.prodComm Bool Bool).prodCongr (Equiv.refl (Fin n × Fin n)))).trans (Equiv.prodAssoc Bool Bool (Fin n × Fin n))).trans (Equiv.boolProdEquivSum (Bool × Fin n × Fin n)))
  have h2 := MeasurePreserving.symm e.symm
    (measurePreserving_sumPiEquivProdPi_symm (fun _ : (Bool × Fin n × Fin n) ⊕ (Bool × Fin n × Fin n) => gaussianReal 0 v))
  let a := MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ ((Bool × Fin n × Fin n))
  have h3 := MeasurePreserving.symm a
    (measurePreserving_arrowProdEquivProdArrow ℝ ℝ ((Bool × Fin n × Fin n))
      (fun _ => gaussianReal 0 v) (fun _ => gaussianReal 0 v))
  convert h3.comp (h2.comp h1) using 1
  · funext x i
    rcases i with ⟨b,i,j⟩
    rfl
private lemma complexGaussian_scaled (m σ : ℝ) (v : ℝ≥0) :
    Measure.map (fun xy : ℝ × ℝ => ((m+σ*xy.1 : ℝ):ℂ) + (σ*xy.2:ℝ)*Complex.I)
      ((gaussianReal 0 v).prod (gaussianReal 0 v)) =
      D5.S3.Analytic.Probability.SampleCovarianceSpectralAndSmooth.Smooth.complexGaussian m (NNReal.mk (σ^2) (sq_nonneg σ)*v) := by
  have hscale : MeasurePreserving (fun x : ℝ => σ*x) (gaussianReal 0 v)
      (gaussianReal 0 (NNReal.mk (σ^2) (sq_nonneg σ)*v)) :=
    ⟨by fun_prop, by simpa using gaussianReal_map_const_mul (μ:=0) (v:=v) σ⟩
  have hshift : MeasurePreserving (fun x : ℝ => m+x)
      (gaussianReal 0 (NNReal.mk (σ^2) (sq_nonneg σ)*v))
      (gaussianReal m (NNReal.mk (σ^2) (sq_nonneg σ)*v)) :=
    ⟨by fun_prop, by simpa using gaussianReal_map_const_add (μ:=0) (v:=NNReal.mk (σ^2) (sq_nonneg σ)*v) m⟩
  have h := (hshift.comp hscale).prod hscale
  unfold D5.S3.Analytic.Probability.SampleCovarianceSpectralAndSmooth.Smooth.complexGaussian
  rw [← h.map_eq, Measure.map_map (by fun_prop) (by fun_prop)]
  rfl
private lemma affine_entries_preserving (n : ℕ) (m : (Bool × Fin n × Fin n) → ℝ) (σ : ℝ) (v : ℝ≥0) :
    MeasurePreserving
      (fun x : (Bool × Bool × Fin n × Fin n) → ℝ => fun i : (Bool × Fin n × Fin n) =>
        ((m i+σ*x (i.1,false,i.2):ℝ):ℂ) + (σ*x (i.1,true,i.2):ℝ)*Complex.I)
      ((fun n v => Measure.pi (fun _ : Bool × Bool × Fin n × Fin n => gaussianReal 0 v)) n v)
      (Measure.pi (fun i : (Bool × Fin n × Fin n) => D5.S3.Analytic.Probability.SampleCovarianceSpectralAndSmooth.Smooth.complexGaussian (m i)
        (NNReal.mk (σ^2) (sq_nonneg σ)*v))) := by
  have h := measurePreserving_pi
    (fun _ : (Bool × Fin n × Fin n) => (gaussianReal 0 v).prod (gaussianReal 0 v))
    (fun i => D5.S3.Analytic.Probability.SampleCovarianceSpectralAndSmooth.Smooth.complexGaussian (m i) (NNReal.mk (σ^2) (sq_nonneg σ)*v))
    (fun i => (show MeasurePreserving
      (fun xy : ℝ × ℝ => ((m i+σ*xy.1:ℝ):ℂ)+(σ*xy.2:ℝ)*Complex.I)
      ((gaussianReal 0 v).prod (gaussianReal 0 v)) _ from
      ⟨by fun_prop, complexGaussian_scaled (m i) σ v⟩))
  exact h.comp (pack_preserving n v)
private def splitEntries {n : ℕ} (f : (Bool × Fin n × Fin n) → ℂ) :
    Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ :=
  (Matrix.of (fun i j => f (false,i,j)), Matrix.of (fun i j => f (true,i,j)))
@[fun_prop] private lemma measurable_splitEntries {n : ℕ} : Measurable (splitEntries (n:=n)) := by
  exact (Measurable.of_eval_matrix _ (fun i j => measurable_pi_apply (false,i,j))).prodMk
    (Measurable.of_eval_matrix _ (fun i j => measurable_pi_apply (true,i,j)))
private lemma entries_pair_preserving (n : ℕ) (μ : Measure ℂ) [IsProbabilityMeasure μ] :
    MeasurePreserving (splitEntries (n:=n)) (Measure.pi (fun _ : (Bool × Fin n × Fin n) => μ))
      ((D5.S3.Analytic.Probability.SampleCovarianceSpectralAndSmooth.matrixLaw n μ).prod (D5.S3.Analytic.Probability.SampleCovarianceSpectralAndSmooth.matrixLaw n μ)) := by
  let e : (Bool × Fin n × Fin n) ≃ (Fin n × Fin n) ⊕ (Fin n × Fin n) := Equiv.boolProdEquivSum _
  let a := MeasurableEquiv.sumPiEquivProdPi (fun _ : (Fin n × Fin n) ⊕ (Fin n × Fin n) => ℂ)
  have h1 := measurePreserving_piCongrLeft
    (fun _ : (Fin n × Fin n) ⊕ (Fin n × Fin n) => μ) e
  have h2 := MeasurePreserving.symm a.symm
    (measurePreserving_sumPiEquivProdPi_symm
      (fun _ : (Fin n × Fin n) ⊕ (Fin n × Fin n) => μ))
  have hmat : MeasurePreserving (fun f : Fin n × Fin n → ℂ => Matrix.of (fun i j => f (i,j)))
      (Measure.pi (fun _ : Fin n × Fin n => μ)) (D5.S3.Analytic.Probability.SampleCovarianceSpectralAndSmooth.matrixLaw n μ) :=
    ⟨Measurable.of_eval_matrix _ (fun i j => measurable_pi_apply (i,j)), rfl⟩
  convert (hmat.prod hmat).comp (h2.comp h1) using 1
  funext f
  rfl
private instance smooth_probability (ε : ℝ) : IsProbabilityMeasure (D5.S3.Analytic.Probability.SampleCovarianceSpectralAndSmooth.Smooth.smoothLaw ε) :=
  ⟨(D5.S3.Analytic.Probability.SampleCovarianceSpectralAndSmooth.Smooth.smoothLaw_EntryLaw ε).1⟩
private def meanB {n : ℕ} (b : ((Bool × Fin n × Fin n) → Bool)) (ε : ℝ) (i : (Bool × Fin n × Fin n)) : ℝ :=
  if b i then Real.sqrt 255/Real.sqrt (1+ε^2) else -1/(Real.sqrt 255*Real.sqrt (1+ε^2))
private def scale (ε : ℝ) : ℝ := ε/Real.sqrt (1+ε^2)
private def affinePair {n : ℕ} (b : ((Bool × Fin n × Fin n) → Bool)) (ε : ℝ) (x : (Bool × Bool × Fin n × Fin n) → ℝ) :=
  splitEntries (fun i : (Bool × Fin n × Fin n) => ((meanB b ε i + scale ε*x (i.1,false,i.2):ℝ):ℂ) +
    (scale ε*x (i.1,true,i.2):ℝ)*Complex.I)
@[fun_prop] private lemma measurable_affinePair {n : ℕ} (b : ((Bool × Fin n × Fin n) → Bool)) (ε : ℝ) :
    Measurable (affinePair b ε) := by
  unfold affinePair
  apply measurable_splitEntries.comp
  apply Measurable.of_eval
  intro i
  fun_prop
private lemma weight_ne_top {n : ℕ} (b : ((Bool × Fin n × Fin n) → Bool)) :
    (∏ i : (Bool × Fin n × Fin n), if b i then (1/256:ℝ≥0∞) else 255/256) ≠ ∞ := by
  apply ENNReal.prod_ne_top
  intro i hi
  split <;> exact ENNReal.div_ne_top (by norm_num) (by norm_num)
private lemma scale_variance (ε : ℝ) :
    (NNReal.mk ((scale ε)^2) (sq_nonneg _):ℝ≥0)*(1/2) = D5.S3.Analytic.Probability.SampleCovarianceSpectralAndSmooth.Smooth.noiseVariance ε := by
  apply NNReal.coe_injective
  change (ε/Real.sqrt (1+ε^2))^2*(1/2) = ε^2/(2*(1+ε^2))
  rw [div_pow, Real.sq_sqrt (by positivity)]
  field_simp
  <;> ring
private lemma affinePair_law (n : ℕ) (b : ((Bool × Fin n × Fin n) → Bool)) (ε : ℝ) :
    Measure.map (affinePair b ε) ((fun n v => Measure.pi (fun _ : Bool × Bool × Fin n × Fin n => gaussianReal 0 v)) n (1/2)) =
      Measure.map splitEntries (Measure.pi (fun i : (Bool × Fin n × Fin n) =>
        D5.S3.Analytic.Probability.SampleCovarianceSpectralAndSmooth.Smooth.complexGaussian (meanB b ε i) (D5.S3.Analytic.Probability.SampleCovarianceSpectralAndSmooth.Smooth.noiseVariance ε))) := by
  have h := affine_entries_preserving n (meanB b ε) (scale ε) (1/2)
  rw [scale_variance] at h
  rw [← h.map_eq, Measure.map_map (by fun_prop) (by fun_prop)]
  rfl
private lemma smooth_pair_law (n : ℕ) (ε : ℝ) :
    (D5.S3.Analytic.Probability.SampleCovarianceSpectralAndSmooth.matrixLaw n (D5.S3.Analytic.Probability.SampleCovarianceSpectralAndSmooth.Smooth.smoothLaw ε)).prod
      (D5.S3.Analytic.Probability.SampleCovarianceSpectralAndSmooth.matrixLaw n (D5.S3.Analytic.Probability.SampleCovarianceSpectralAndSmooth.Smooth.smoothLaw ε)) =
    ∑ b : ((Bool × Fin n × Fin n) → Bool),
      (∏ i : (Bool × Fin n × Fin n), if b i then (1/256:ℝ≥0∞) else 255/256) •
        Measure.map (affinePair b ε) ((fun n v => Measure.pi (fun _ : Bool × Bool × Fin n × Fin n => gaussianReal 0 v)) n (1/2)) := by
  let ν : (Bool × Fin n × Fin n) → Bool → Measure ℂ := fun _ b =>
    D5.S3.Analytic.Probability.SampleCovarianceSpectralAndSmooth.Smooth.complexGaussian
      (if b then Real.sqrt 255/Real.sqrt (1+ε^2) else -1/(Real.sqrt 255*Real.sqrt (1+ε^2)))
      (D5.S3.Analytic.Probability.SampleCovarianceSpectralAndSmooth.Smooth.noiseVariance ε)
  have hp := pi_mixture ν (255/256) (1/256)
    (ENNReal.div_ne_top (by norm_num) (by norm_num))
    (ENNReal.div_ne_top (by norm_num) (by norm_num))
  change Measure.pi (fun _ : (Bool × Fin n × Fin n) => D5.S3.Analytic.Probability.SampleCovarianceSpectralAndSmooth.Smooth.smoothLaw ε) = _ at hp
  rw [← (entries_pair_preserving n (D5.S3.Analytic.Probability.SampleCovarianceSpectralAndSmooth.Smooth.smoothLaw ε)).map_eq, hp,
    Measure.map_finset_sum' (by fun_prop)]
  apply Finset.sum_congr rfl
  intro b hb
  rw [Measure.map_smul _ (by fun_prop), affinePair_law]
  rfl
end
end D5.S3.Analytic.Probability.SampleCovarianceLogEnergyRefutation.Transport
open MeasureTheory Filter Set
open scoped Topology BigOperators NNReal
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2500000
namespace D5.S3.Analytic.Probability.SampleCovarianceLogEnergyRefutation.Energy
noncomputable section
private def negativeLogAverage (n : ℕ) (ε : ℝ) : ℝ :=
  ∑ b : ((Bool × Fin n × Fin n) → Bool), D5.S3.StatisticalMechanics.ParticleProcesses.ExclusionMovingParticleOptimality.bernoulli (1/256) (fun i => finTwoEquiv.symm (b i)) *
    (-(∫ x, Real.log ‖(D5.S3.Analytic.Probability.GaussianPolynomialLog.Covariance.pairDet (D5.S3.Analytic.Probability.SampleCovarianceBernoulliOrders.Events.bmat b false)
      (D5.S3.Analytic.Probability.SampleCovarianceBernoulliOrders.Events.bmat b true) (D5.S3.Analytic.Probability.SampleCovarianceLogEnergyRefutation.Analytic.realNoise x false)
      (D5.S3.Analytic.Probability.SampleCovarianceLogEnergyRefutation.Analytic.realNoise x true)).eval (ε:ℂ)‖
      ∂(fun n m v => Measure.pi (fun _ : Fin n => gaussianReal m v)) ((Fintype.card (Bool × Bool × Fin n × Fin n))) 0 (1/2)))
private def E (n : ℕ) (ε : ℝ) : ℝ :=
  1+Real.log n+Real.log (1+ε^2)+negativeLogAverage n ε/(n:ℝ)^2
private lemma negativeLogAverage_limit (n : ℕ) :
    Tendsto (fun ε : ℝ => negativeLogAverage n ε/Real.log (1/ε))
      (𝓝[>] 0) (𝓝 (∑ b : ((Bool × Fin n × Fin n) → Bool), D5.S3.StatisticalMechanics.ParticleProcesses.ExclusionMovingParticleOptimality.bernoulli (1/256) (fun i => finTwoEquiv.symm (b i))*(D5.S3.Analytic.Probability.SampleCovarianceBernoulliOrders.Events.k b:ℝ))) := by
  have h (b : ((Bool × Fin n × Fin n) → Bool)) :=
    (D5.S3.Analytic.Probability.SampleCovarianceLogEnergyRefutation.Analytic.gaussian_pairDet_log_order (D5.S3.Analytic.Probability.SampleCovarianceBernoulliOrders.Events.bmat b false)
      (D5.S3.Analytic.Probability.SampleCovarianceBernoulliOrders.Events.bmat b true) 0 (1/2) (by norm_num)).const_mul (D5.S3.StatisticalMechanics.ParticleProcesses.ExclusionMovingParticleOptimality.bernoulli (1/256) (fun i => finTwoEquiv.symm (b i)))
  have hs := tendsto_finset_sum Finset.univ (fun b _ => h b)
  convert hs using 1
  · funext ε
    simp only [negativeLogAverage, Finset.sum_div, mul_div_assoc]
  · rfl
private lemma E_limit (n : ℕ) :
    Tendsto (fun ε : ℝ => E n ε/Real.log (1/ε)) (𝓝[>] 0) (𝓝 (D5.S3.Analytic.Probability.SampleCovarianceBernoulliOrders.Events.L n)) := by
  have hden : Tendsto (fun ε : ℝ => Real.log (1/ε)) (𝓝[>] 0) atTop := by
    simpa only [one_div, Real.log_inv, Function.comp_def] using
      tendsto_neg_atBot_atTop.comp Real.tendsto_log_nhdsGT_zero
  have hc : Continuous (fun ε : ℝ => Real.log (1+ε^2)) := by
    apply Continuous.log
    · fun_prop
    · intro ε; positivity
  have hn : Tendsto (fun ε : ℝ => 1+Real.log n+Real.log (1+ε^2))
      (𝓝[>] 0) (𝓝 (1+Real.log n)) := by
    have h : Continuous (fun ε : ℝ => 1+Real.log n+Real.log (1+ε^2)) :=
      (continuous_const.add continuous_const).add hc
    simpa using (h.tendsto 0).mono_left nhdsWithin_le_nhds
  have h := (hn.div_atTop hden).add ((negativeLogAverage_limit n).div_const ((n:ℝ)^2))
  convert h using 1
  · funext ε
    dsimp only [E]
    ring
  · simp [D5.S3.Analytic.Probability.SampleCovarianceBernoulliOrders.Events.L]
private lemma exists_fixed_epsilon : ∃ ε : ℝ, 0 < ε ∧ E 2 ε < E 3 ε := by
  have hg := ((E_limit 3).sub (E_limit 2)).eventually
    (eventually_gt_nhds (sub_pos.mpr D5.S3.Analytic.Probability.SampleCovarianceBernoulliOrders.Events.L_gap))
  have hden : Tendsto (fun ε : ℝ => Real.log (1/ε)) (𝓝[>] 0) atTop := by
    simpa only [one_div, Real.log_inv, Function.comp_def] using
      tendsto_neg_atBot_atTop.comp Real.tendsto_log_nhdsGT_zero
  have hpos : ∀ᶠ ε : ℝ in 𝓝[>] 0, 0 < ε := self_mem_nhdsWithin
  obtain ⟨ε,hε,hden,hgap⟩ := (hpos.and ((hden.eventually (eventually_gt_atTop 0)).and hg)).exists
  refine ⟨ε,hε,?_⟩
  rw [← sub_div] at hgap
  exact sub_pos.mp ((div_pos_iff_of_pos_right hden).mp hgap)
end
end D5.S3.Analytic.Probability.SampleCovarianceLogEnergyRefutation.Energy

open MeasureTheory ProbabilityTheory Filter Matrix Set
open scoped ENNReal NNReal Topology BigOperators Kronecker
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2500000
namespace D5.S3.Analytic.Probability.SampleCovarianceLogEnergyRefutation.Transport
noncomputable section


private lemma toCoords_preserving (n : ℕ) (v : ℝ≥0) :
    MeasurePreserving (MeasurableEquiv.piCongrLeft (fun _ : Bool × Bool × Fin n × Fin n => ℝ) (Fintype.equivFin (Bool × Bool × Fin n × Fin n)).symm) ((fun n m v => Measure.pi (fun _ : Fin n => gaussianReal m v)) ((Fintype.card (Bool × Bool × Fin n × Fin n))) 0 v)
      ((fun n v => Measure.pi (fun _ : Bool × Bool × Fin n × Fin n => gaussianReal 0 v)) n v) := by
  exact measurePreserving_piCongrLeft (fun _ : Bool × Bool × Fin n × Fin n => gaussianReal 0 v)
    (Fintype.equivFin (Bool × Bool × Fin n × Fin n)).symm

private def finitePair {n : ℕ} (b : ((Bool × Fin n × Fin n) → Bool)) (ε : ℝ) (x : Fin ((Fintype.card (Bool × Bool × Fin n × Fin n))) → ℝ) :=
  affinePair b ε ((MeasurableEquiv.piCongrLeft (fun _ : Bool × Bool × Fin n × Fin n => ℝ) (Fintype.equivFin (Bool × Bool × Fin n × Fin n)).symm) x)
@[fun_prop] private lemma measurable_finitePair {n : ℕ} (b : ((Bool × Fin n × Fin n) → Bool)) (ε : ℝ) :
    Measurable (finitePair b ε) := (measurable_affinePair b ε).comp (MeasurableEquiv.piCongrLeft (fun _ : Bool × Bool × Fin n × Fin n => ℝ) (Fintype.equivFin (Bool × Bool × Fin n × Fin n)).symm).measurable
private lemma smooth_pair_law_finite (n : ℕ) (ε : ℝ) :
    (D5.S3.Analytic.Probability.SampleCovarianceSpectralAndSmooth.matrixLaw n (D5.S3.Analytic.Probability.SampleCovarianceSpectralAndSmooth.Smooth.smoothLaw ε)).prod
      (D5.S3.Analytic.Probability.SampleCovarianceSpectralAndSmooth.matrixLaw n (D5.S3.Analytic.Probability.SampleCovarianceSpectralAndSmooth.Smooth.smoothLaw ε)) =
    ∑ b : ((Bool × Fin n × Fin n) → Bool),
      (∏ i : (Bool × Fin n × Fin n), if b i then (1/256:ℝ≥0∞) else 255/256) •
        Measure.map (finitePair b ε) ((fun n m v => Measure.pi (fun _ : Fin n => gaussianReal m v)) ((Fintype.card (Bool × Bool × Fin n × Fin n))) 0 (1/2)) := by
  rw [smooth_pair_law]
  apply Finset.sum_congr rfl
  intro b hb
  congr 1
  rw [← (toCoords_preserving n (1/2)).map_eq, Measure.map_map (by fun_prop) (by fun_prop)]
  rfl
private lemma finitePair_eq {n : ℕ} (b : ((Bool × Fin n × Fin n) → Bool)) (ε : ℝ)
    (x : Fin ((Fintype.card (Bool × Bool × Fin n × Fin n))) → ℝ) (side : Bool) :
    (if side then (finitePair b ε x).2 else (finitePair b ε x).1) =
      ((1/Real.sqrt (1+ε^2):ℝ):ℂ) • D5.S3.Analytic.Probability.SampleCovarianceBernoulliOrders.Events.bmat b side +
        ((scale ε:ℝ):ℂ) • D5.S3.Analytic.Probability.SampleCovarianceLogEnergyRefutation.Analytic.realNoise x side := by
  apply Matrix.ext
  intro i j
  have hs : Real.sqrt (255:ℝ) ≠ 0 := Real.sqrt_ne_zero'.mpr (by norm_num)
  have ht : Real.sqrt (1+ε^2) ≠ 0 := Real.sqrt_ne_zero'.mpr (by positivity)
  have hc (z : Bool × Bool × Fin n × Fin n) :
      (MeasurableEquiv.piCongrLeft (fun _ : Bool × Bool × Fin n × Fin n => ℝ)
        (Fintype.equivFin (Bool × Bool × Fin n × Fin n)).symm x) z =
        x ((Fintype.equivFin (Bool × Bool × Fin n × Fin n)) z) := by
    simpa only [Equiv.symm_apply_apply] using
      (MeasurableEquiv.piCongrLeft_apply_apply
        (β := fun _ : Bool × Bool × Fin n × Fin n => ℝ)
        (Fintype.equivFin (Bool × Bool × Fin n × Fin n)).symm x
        ((Fintype.equivFin (Bool × Bool × Fin n × Fin n)) z))
  cases side <;> simp only [Bool.false_eq_true, ite_false, ite_true, finitePair, affinePair,
    splitEntries, Matrix.of_apply, meanB, scale, D5.S3.Analytic.Probability.SampleCovarianceBernoulliOrders.Events.bmat, D5.S3.Analytic.Probability.SampleCovarianceLogEnergyRefutation.Analytic.realNoise,
    hc, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul] <;>
    split_ifs <;> push_cast <;> field_simp <;> ring

private def detPair {n : ℕ} (AC : Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ) : ℂ :=
  Matrix.det ((AC.1 * AC.1ᴴ) ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ) -
    (1 : Matrix (Fin n) (Fin n) ℂ) ⊗ₖ (AC.2 * AC.2ᴴ))
@[fun_prop] private lemma measurable_detPair {n : ℕ} : Measurable (detPair (n:=n)) := by
  have hf (i j : Fin n) : Measurable
      (fun AC : Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ => AC.1 i j) :=
    measurable_fst.eval_matrix
  have hs (i j : Fin n) : Measurable
      (fun AC : Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ => AC.2 i j) :=
    measurable_snd.eval_matrix
  have h1 (i j : Fin n) : Measurable
      (fun AC : Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ => (AC.1*AC.1ᴴ) i j) := by
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
    exact Finset.measurable_fun_sum _ (fun k hk => (hf i k).mul ((show Measurable (star : ℂ → ℂ) from continuous_star.measurable).comp (hf j k)))
  have h2 (i j : Fin n) : Measurable
      (fun AC : Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ => (AC.2*AC.2ᴴ) i j) := by
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
    exact Finset.measurable_fun_sum _ (fun k hk => (hs i k).mul ((show Measurable (star : ℂ → ℂ) from continuous_star.measurable).comp (hs j k)))
  have hm (i j : Fin n × Fin n) : Measurable
      (fun AC : Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ =>
        (AC.1*AC.1ᴴ) i.1 j.1 * (1 : Matrix (Fin n) (Fin n) ℂ) i.2 j.2 -
          (1 : Matrix (Fin n) (Fin n) ℂ) i.1 j.1 * (AC.2*AC.2ᴴ) i.2 j.2) :=
    ((h1 i.1 j.1).mul_const _).sub ((h2 i.2 j.2).const_mul _)
  unfold detPair
  simp only [Matrix.det_apply]
  apply Finset.measurable_fun_sum
  intro σ hσ
  have hp := Finset.measurable_fun_prod Finset.univ (fun i hi => hm (σ i) i)
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h
  · simpa only [h,one_smul,Matrix.sub_apply,Matrix.kroneckerMap_apply] using hp
  · have hneg := (measurable_neg : Measurable (fun z : ℂ => -z)).comp hp
    simpa only [h,Units.neg_smul,one_smul,Matrix.sub_apply,Matrix.kroneckerMap_apply,
      Function.comp_def] using hneg
private lemma measurable_logdetPair {n : ℕ} : Measurable (fun AC => Real.log ‖detPair (n:=n) AC‖) :=
  Real.measurable_log.comp measurable_detPair.norm
private lemma conditional_det_nonzero_integrable {n : ℕ} (b : ((Bool × Fin n × Fin n) → Bool))
    (ε : ℝ) (hε : ε ≠ 0) :
    (∀ᵐ x ∂(fun n m v => Measure.pi (fun _ : Fin n => gaussianReal m v)) ((Fintype.card (Bool × Bool × Fin n × Fin n))) 0 (1/2),
      detPair (finitePair b ε x) ≠ 0) ∧
    Integrable (fun x => Real.log ‖detPair (finitePair b ε x)‖)
      ((fun n m v => Measure.pi (fun _ : Fin n => gaussianReal m v)) ((Fintype.card (Bool × Bool × Fin n × Fin n))) 0 (1/2)) := by
  have hσ : scale ε ≠ 0 := div_ne_zero hε (Real.sqrt_ne_zero'.mpr (by positivity))
  have h := D5.S3.Analytic.Probability.SampleCovarianceLogEnergyRefutation.Analytic.gaussian_det_nonzero_integrable
    (((1/Real.sqrt (1+ε^2):ℝ):ℂ) • D5.S3.Analytic.Probability.SampleCovarianceBernoulliOrders.Events.bmat b false)
    (((1/Real.sqrt (1+ε^2):ℝ):ℂ) • D5.S3.Analytic.Probability.SampleCovarianceBernoulliOrders.Events.bmat b true)
    (scale ε) hσ 0 (1/2) (by norm_num)
  have hf (x : Fin ((Fintype.card (Bool × Bool × Fin n × Fin n))) → ℝ) : detPair (finitePair b ε x) =
      Matrix.det
      (((((1/Real.sqrt (1+ε^2):ℝ):ℂ) • D5.S3.Analytic.Probability.SampleCovarianceBernoulliOrders.Events.bmat b false +
        (scale ε:ℂ) • D5.S3.Analytic.Probability.SampleCovarianceLogEnergyRefutation.Analytic.realNoise x false) *
       (((1/Real.sqrt (1+ε^2):ℝ):ℂ) • D5.S3.Analytic.Probability.SampleCovarianceBernoulliOrders.Events.bmat b false +
        (scale ε:ℂ) • D5.S3.Analytic.Probability.SampleCovarianceLogEnergyRefutation.Analytic.realNoise x false)ᴴ) ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ) -
       (1 : Matrix (Fin n) (Fin n) ℂ) ⊗ₖ
       ((((1/Real.sqrt (1+ε^2):ℝ):ℂ) • D5.S3.Analytic.Probability.SampleCovarianceBernoulliOrders.Events.bmat b true +
        (scale ε:ℂ) • D5.S3.Analytic.Probability.SampleCovarianceLogEnergyRefutation.Analytic.realNoise x true) *
       (((1/Real.sqrt (1+ε^2):ℝ):ℂ) • D5.S3.Analytic.Probability.SampleCovarianceBernoulliOrders.Events.bmat b true +
        (scale ε:ℂ) • D5.S3.Analytic.Probability.SampleCovarianceLogEnergyRefutation.Analytic.realNoise x true)ᴴ)) := by
    unfold detPair
    rw [← finitePair_eq b ε x false, ← finitePair_eq b ε x true]
    rfl
  simpa only [hf] using h
private lemma smooth_det_nonzero_integrable (n : ℕ) (ε : ℝ) (hε : ε ≠ 0) :
    (∀ᵐ AC ∂(D5.S3.Analytic.Probability.SampleCovarianceSpectralAndSmooth.matrixLaw n (D5.S3.Analytic.Probability.SampleCovarianceSpectralAndSmooth.Smooth.smoothLaw ε)).prod
      (D5.S3.Analytic.Probability.SampleCovarianceSpectralAndSmooth.matrixLaw n (D5.S3.Analytic.Probability.SampleCovarianceSpectralAndSmooth.Smooth.smoothLaw ε)), detPair AC ≠ 0) ∧
    Integrable (fun AC => Real.log ‖detPair AC‖)
      ((D5.S3.Analytic.Probability.SampleCovarianceSpectralAndSmooth.matrixLaw n (D5.S3.Analytic.Probability.SampleCovarianceSpectralAndSmooth.Smooth.smoothLaw ε)).prod
      (D5.S3.Analytic.Probability.SampleCovarianceSpectralAndSmooth.matrixLaw n (D5.S3.Analytic.Probability.SampleCovarianceSpectralAndSmooth.Smooth.smoothLaw ε))) := by
  rw [smooth_pair_law_finite]
  constructor
  · rw [ae_finsetSum_measure_iff]
    intro b hb
    apply Measure.ae_smul_measure
    apply (ae_map_iff (measurable_finitePair b ε).aemeasurable (by measurability)).mpr
    exact (conditional_det_nonzero_integrable b ε hε).1
  · apply integrable_finsetSum_measure.mpr
    intro b hb
    exact ((integrable_map_measure measurable_logdetPair.aestronglyMeasurable
      (measurable_finitePair b ε).aemeasurable).mpr
      (conditional_det_nonzero_integrable b ε hε).2).smul_measure
      (c:=∏ i : (Bool × Fin n × Fin n), if b i then (1/256:ℝ≥0∞) else 255/256)
      (weight_ne_top b)
end
end D5.S3.Analytic.Probability.SampleCovarianceLogEnergyRefutation.Transport
namespace D5.S3.Analytic.Probability.SampleCovarianceLogEnergyRefutation
noncomputable section
private lemma smooth_logarithmicEnergy_identity (n : ℕ) (hn : 0 < n) (ε : ℝ) (hε : ε ≠ 0) :
    logarithmicEnergy (meanSpectralMeasure n hn (D5.S3.Analytic.Probability.SampleCovarianceSpectralAndSmooth.Smooth.smoothLaw ε)) =
      (Real.log n - (n:ℝ)⁻¹^2 * ∫ AC, Real.log ‖D5.S3.Analytic.Probability.SampleCovarianceLogEnergyRefutation.Transport.detPair AC‖
        ∂(matrixLaw n (D5.S3.Analytic.Probability.SampleCovarianceSpectralAndSmooth.Smooth.smoothLaw ε)).prod
          (matrixLaw n (D5.S3.Analytic.Probability.SampleCovarianceSpectralAndSmooth.Smooth.smoothLaw ε)) : ℝ) := by
  obtain ⟨hae,hi⟩ := D5.S3.Analytic.Probability.SampleCovarianceLogEnergyRefutation.Transport.smooth_det_nonzero_integrable n ε hε
  apply logarithmicEnergy_mean_eq_log_det_of_moments n hn _
    (gramEigenvalue_integrable n _ (D5.S3.Analytic.Probability.SampleCovarianceSpectralAndSmooth.Smooth.smoothLaw_EntryLaw ε)) _ hi
  filter_upwards [hae] with AC hAC
  exact (two_copy_gram_det_nonzero_iff n AC.1 AC.2).mp hAC
end
end D5.S3.Analytic.Probability.SampleCovarianceLogEnergyRefutation
open MeasureTheory ProbabilityTheory Filter Matrix Set
open scoped ENNReal NNReal Topology BigOperators Kronecker
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2500000
namespace D5.S3.Analytic.Probability.SampleCovarianceLogEnergyRefutation.Transport
noncomputable section
private lemma detPair_smul {n : ℕ} (a : ℂ) (A C : Matrix (Fin n) (Fin n) ℂ) :
    detPair (a • A,a • C) = (a*star a)^(n*n) * detPair (A,C) := by
  unfold detPair
  simp only [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul, mul_comm (star a) a]
  rw [Matrix.smul_kronecker,
    Matrix.kronecker_smul, ← smul_sub, Matrix.det_smul]
  simp [Fintype.card_prod]
private lemma finitePair_raw {n : ℕ} (b : ((Bool × Fin n × Fin n) → Bool)) (ε : ℝ)
    (x : Fin ((Fintype.card (Bool × Bool × Fin n × Fin n))) → ℝ) :
    finitePair b ε x =
      ((((1/Real.sqrt (1+ε^2):ℝ):ℂ) • (D5.S3.Analytic.Probability.SampleCovarianceBernoulliOrders.Events.bmat b false +
        (ε:ℂ) • D5.S3.Analytic.Probability.SampleCovarianceLogEnergyRefutation.Analytic.realNoise x false)),
       (((1/Real.sqrt (1+ε^2):ℝ):ℂ) • (D5.S3.Analytic.Probability.SampleCovarianceBernoulliOrders.Events.bmat b true +
        (ε:ℂ) • D5.S3.Analytic.Probability.SampleCovarianceLogEnergyRefutation.Analytic.realNoise x true))) := by
  apply Prod.ext
  · have h := finitePair_eq b ε x false
    simp only [Bool.false_eq_true, ite_false] at h
    rw [h]
    ext i j
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, scale,
      Complex.ofReal_div, Complex.ofReal_one, div_eq_mul_inv, Complex.ofReal_mul,
      Complex.ofReal_inv, one_mul]
    ring
  · have h := finitePair_eq b ε x true
    simp only [ite_true] at h
    rw [h]
    ext i j
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, scale,
      Complex.ofReal_div, Complex.ofReal_one, div_eq_mul_inv, Complex.ofReal_mul,
      Complex.ofReal_inv, one_mul]
    ring
private lemma conditional_log_integral {n : ℕ} (b : ((Bool × Fin n × Fin n) → Bool)) (ε : ℝ) (hε : ε ≠ 0) :
    (∫ x, Real.log ‖detPair (finitePair b ε x)‖
      ∂(fun n m v => Measure.pi (fun _ : Fin n => gaussianReal m v)) ((Fintype.card (Bool × Bool × Fin n × Fin n))) 0 (1/2)) =
      -(n:ℝ)^2*Real.log (1+ε^2) +
      ∫ x, Real.log ‖(D5.S3.Analytic.Probability.GaussianPolynomialLog.Covariance.pairDet (D5.S3.Analytic.Probability.SampleCovarianceBernoulliOrders.Events.bmat b false) (D5.S3.Analytic.Probability.SampleCovarianceBernoulliOrders.Events.bmat b true)
        (D5.S3.Analytic.Probability.SampleCovarianceLogEnergyRefutation.Analytic.realNoise x false) (D5.S3.Analytic.Probability.SampleCovarianceLogEnergyRefutation.Analytic.realNoise x true)).eval (ε:ℂ)‖
      ∂(fun n m v => Measure.pi (fun _ : Fin n => gaussianReal m v)) ((Fintype.card (Bool × Bool × Fin n × Fin n))) 0 (1/2) := by
  have hp : 0 < 1+ε^2 := by positivity
  have hs := Real.sq_sqrt hp.le
  have hsne : Real.sqrt (1+ε^2) ≠ 0 := Real.sqrt_ne_zero'.mpr hp
  have hfactor : (((1/Real.sqrt (1+ε^2):ℝ):ℂ) * star ((1/Real.sqrt (1+ε^2):ℝ):ℂ)) =
      ((1/(1+ε^2):ℝ):ℂ) := by
    simp only [Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul]
    congr 1
    rw [← pow_two, div_pow, one_pow, hs]
  have hi := D5.S3.Analytic.Probability.SampleCovarianceLogEnergyRefutation.Analytic.gaussian_det_nonzero_integrable
    (D5.S3.Analytic.Probability.SampleCovarianceBernoulliOrders.Events.bmat b false) (D5.S3.Analytic.Probability.SampleCovarianceBernoulliOrders.Events.bmat b true) ε hε 0 (1/2) (by norm_num)
  have heq : (fun x => Real.log ‖detPair (finitePair b ε x)‖) =ᵐ[
      (fun n m v => Measure.pi (fun _ : Fin n => gaussianReal m v)) ((Fintype.card (Bool × Bool × Fin n × Fin n))) 0 (1/2)]
      (fun x => -(n:ℝ)^2*Real.log (1+ε^2) +
        Real.log ‖(D5.S3.Analytic.Probability.GaussianPolynomialLog.Covariance.pairDet (D5.S3.Analytic.Probability.SampleCovarianceBernoulliOrders.Events.bmat b false) (D5.S3.Analytic.Probability.SampleCovarianceBernoulliOrders.Events.bmat b true)
          (D5.S3.Analytic.Probability.SampleCovarianceLogEnergyRefutation.Analytic.realNoise x false) (D5.S3.Analytic.Probability.SampleCovarianceLogEnergyRefutation.Analytic.realNoise x true)).eval (ε:ℂ)‖) := by
    filter_upwards [hi.1] with x hx
    rw [finitePair_raw, detPair_smul, hfactor]
    have hraw := D5.S3.Analytic.Probability.SampleCovarianceBernoulliOrders.Noise.eval_pairDet ε (D5.S3.Analytic.Probability.SampleCovarianceBernoulliOrders.Events.bmat b false) (D5.S3.Analytic.Probability.SampleCovarianceBernoulliOrders.Events.bmat b true)
      (D5.S3.Analytic.Probability.SampleCovarianceLogEnergyRefutation.Analytic.realNoise x false) (D5.S3.Analytic.Probability.SampleCovarianceLogEnergyRefutation.Analytic.realNoise x true)
    change _ = _ + Real.log ‖(D5.S3.Analytic.Probability.GaussianPolynomialLog.Covariance.pairDet _ _ _ _).eval (ε:ℂ)‖
    change _ ≠ 0 at hx
    rw [← hraw] at hx
    change Real.log ‖(((1/(1+ε^2):ℝ):ℂ))^(n*n) * _‖ = _
    have hd : detPair (D5.S3.Analytic.Probability.SampleCovarianceBernoulliOrders.Events.bmat b false + (ε:ℂ) • D5.S3.Analytic.Probability.SampleCovarianceLogEnergyRefutation.Analytic.realNoise x false,
        D5.S3.Analytic.Probability.SampleCovarianceBernoulliOrders.Events.bmat b true + (ε:ℂ) • D5.S3.Analytic.Probability.SampleCovarianceLogEnergyRefutation.Analytic.realNoise x true) =
        (D5.S3.Analytic.Probability.GaussianPolynomialLog.Covariance.pairDet (D5.S3.Analytic.Probability.SampleCovarianceBernoulliOrders.Events.bmat b false) (D5.S3.Analytic.Probability.SampleCovarianceBernoulliOrders.Events.bmat b true)
          (D5.S3.Analytic.Probability.SampleCovarianceLogEnergyRefutation.Analytic.realNoise x false) (D5.S3.Analytic.Probability.SampleCovarianceLogEnergyRefutation.Analytic.realNoise x true)).eval (ε:ℂ) := hraw.symm
    rw [hd, norm_mul, norm_pow, Real.log_mul (pow_ne_zero _
      (norm_ne_zero_iff.mpr (by exact_mod_cast (one_div_ne_zero hp.ne'))))
      (norm_ne_zero_iff.mpr hx), Real.log_pow, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (one_div_pos.mpr hp), Real.log_div one_ne_zero hp.ne',
      Real.log_one]
    simp only [zero_sub, Nat.cast_mul, pow_two]
    ring
  rw [integral_congr_ae heq, integral_add (integrable_const _)]
  · simp
  · simpa only [D5.S3.Analytic.Probability.SampleCovarianceBernoulliOrders.Noise.eval_pairDet] using hi.2
private lemma weight_toReal {n : ℕ} (b : ((Bool × Fin n × Fin n) → Bool)) :
    (∏ i : (Bool × Fin n × Fin n), if b i then (1/256:ℝ≥0∞) else 255/256).toReal = D5.S3.StatisticalMechanics.ParticleProcesses.ExclusionMovingParticleOptimality.bernoulli (1/256) (fun i => finTwoEquiv.symm (b i)) := by
  rw [ENNReal.toReal_prod]
  unfold D5.S3.StatisticalMechanics.ParticleProcesses.ExclusionMovingParticleOptimality.bernoulli
  apply Finset.prod_congr rfl
  intro i hi
  cases hbi : b i <;> norm_num [hbi, finTwoEquiv]
private lemma smooth_log_integral (n : ℕ) (ε : ℝ) (hε : ε ≠ 0) :
    (∫ AC, Real.log ‖detPair AC‖
      ∂(D5.S3.Analytic.Probability.SampleCovarianceSpectralAndSmooth.matrixLaw n (D5.S3.Analytic.Probability.SampleCovarianceSpectralAndSmooth.Smooth.smoothLaw ε)).prod
        (D5.S3.Analytic.Probability.SampleCovarianceSpectralAndSmooth.matrixLaw n (D5.S3.Analytic.Probability.SampleCovarianceSpectralAndSmooth.Smooth.smoothLaw ε))) =
      -(n:ℝ)^2*Real.log (1+ε^2)-D5.S3.Analytic.Probability.SampleCovarianceLogEnergyRefutation.Energy.negativeLogAverage n ε := by
  have hmap (b : ((Bool × Fin n × Fin n) → Bool)) :
      (∫ AC, Real.log ‖detPair AC‖ ∂Measure.map (finitePair b ε)
        ((fun n m v => Measure.pi (fun _ : Fin n => gaussianReal m v)) ((Fintype.card (Bool × Bool × Fin n × Fin n))) 0 (1/2))) =
      ∫ x, Real.log ‖detPair (finitePair b ε x)‖
        ∂(fun n m v => Measure.pi (fun _ : Fin n => gaussianReal m v)) ((Fintype.card (Bool × Bool × Fin n × Fin n))) 0 (1/2) :=
    integral_map (measurable_finitePair b ε).aemeasurable measurable_logdetPair.aestronglyMeasurable
  rw [smooth_pair_law_finite]
  rw [integral_finsetSum_measure]
  · simp_rw [integral_smul_measure, weight_toReal,
      hmap, conditional_log_integral _ ε hε, smul_eq_mul]
    simp only [D5.S3.Analytic.Probability.SampleCovarianceLogEnergyRefutation.Energy.negativeLogAverage, mul_add, Finset.sum_add_distrib,
      ← Finset.sum_mul, D5.S3.Analytic.Probability.SampleCovarianceBernoulliOrders.Events.w_sum, one_mul, mul_neg, Finset.sum_neg_distrib]
    ring
  · intro b hb
    exact ((integrable_map_measure measurable_logdetPair.aestronglyMeasurable
      (measurable_finitePair b ε).aemeasurable).mpr
      (conditional_det_nonzero_integrable b ε hε).2).smul_measure
      (c:=∏ i : (Bool × Fin n × Fin n), if b i then (1/256:ℝ≥0∞) else 255/256)
      (weight_ne_top b)
end
end D5.S3.Analytic.Probability.SampleCovarianceLogEnergyRefutation.Transport
namespace D5.S3.Analytic.Probability.SampleCovarianceLogEnergyRefutation
noncomputable section
private lemma smooth_penalizedEnergy_identity (n : ℕ) (hn : 0 < n) (ε : ℝ) (hε : ε ≠ 0) :
    penalizedEnergy (meanSpectralMeasure n hn (D5.S3.Analytic.Probability.SampleCovarianceSpectralAndSmooth.Smooth.smoothLaw ε)) =
      (D5.S3.Analytic.Probability.SampleCovarianceLogEnergyRefutation.Energy.E n ε : ℝ) := by
  rw [penalizedEnergy, smooth_logarithmicEnergy_identity n hn ε hε,
    firstMoment_mean_eq_one n hn _ (D5.S3.Analytic.Probability.SampleCovarianceSpectralAndSmooth.Smooth.smoothLaw_EntryLaw ε),
    D5.S3.Analytic.Probability.SampleCovarianceLogEnergyRefutation.Transport.smooth_log_integral n ε hε]
  rw [← EReal.coe_one, ← EReal.coe_add]
  congr 1
  have hnR : (n:ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  unfold D5.S3.Analytic.Probability.SampleCovarianceLogEnergyRefutation.Energy.E
  field_simp [hnR]
  ring

def claim : Prop :=
  ∀ (μ : Measure ℂ), EntryLaw μ →
    (∀ n : ℕ,
      penalizedEnergy (meanSpectralMeasure (n + 2) (by omega) μ) ≤
        penalizedEnergy (meanSpectralMeasure (n + 1) (by omega) μ)) ∧
    Tendsto
      (fun n : ℕ => penalizedEnergy (meanSpectralMeasure (n + 1) (by omega) μ))
      atTop (nhds (penalizedEnergy marchenkoPastur))

theorem result : ¬ claim := by
  obtain ⟨ε,hε,hinc⟩ := D5.S3.Analytic.Probability.SampleCovarianceLogEnergyRefutation.Energy.exists_fixed_epsilon
  intro hclaim
  have h := (hclaim (D5.S3.Analytic.Probability.SampleCovarianceSpectralAndSmooth.Smooth.smoothLaw ε) (D5.S3.Analytic.Probability.SampleCovarianceSpectralAndSmooth.Smooth.smoothLaw_EntryLaw ε)).1 1
  rw [smooth_penalizedEnergy_identity 3 (by norm_num) ε hε.ne',
    smooth_penalizedEnergy_identity 2 (by norm_num) ε hε.ne'] at h
  have hr : D5.S3.Analytic.Probability.SampleCovarianceLogEnergyRefutation.Energy.E 3 ε ≤ D5.S3.Analytic.Probability.SampleCovarianceLogEnergyRefutation.Energy.E 2 ε := by exact_mod_cast h
  exact not_le_of_gt hinc hr
end
end D5.S3.Analytic.Probability.SampleCovarianceLogEnergyRefutation
