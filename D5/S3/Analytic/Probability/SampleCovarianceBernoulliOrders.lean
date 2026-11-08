/- GID: D5/S3/Analytic/Probability/SampleCovarianceBernoulliOrders
   generality: I
   mirror-B: D5/B/S3/Analytic/Probability/SampleCovarianceBernoulliOrders
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Bernoulli matrix determinant orders. -/
/-
admission_basis: escape-witness
escape_witness: D5.S3.Analytic.Probability.SampleCovarianceBernoulliOrders.Gaussian.gaussian_noiseFamily_uniform_log
Declaration proof shapes (names relative to this module):
  Noise.coeffStar; proof_shape: bind-only; escape_witness: none; consumer: Noise.coeffStarRing
  Noise.coeffStarRing; proof_shape: bind-only; escape_witness: none; consumer: Noise.evalNoise_poly
  Noise.star_C; proof_shape: bind-only; escape_witness: none; consumer: Noise.evalNoise_star
  Noise.star_X; proof_shape: bind-only; escape_witness: none; consumer: Noise.evalNoise_star
  Noise.noise; proof_shape: bind-only; escape_witness: none; consumer: Noise.evalNoise_noise
  Noise.poly; proof_shape: bind-only; escape_witness: none; consumer: CommonOrder.poly_common_order
  Noise.evalNoise; proof_shape: bind-only; escape_witness: none; consumer: CommonOrder.poly_common_order
  Noise.evalNoise_C; proof_shape: bind-only; escape_witness: none; consumer: Noise.evalNoise_poly
  Noise.evalNoise_star; proof_shape: bind-only; escape_witness: none; consumer: Noise.evalNoise_poly
  Noise.evalNoise_noise; proof_shape: bind-only; escape_witness: none; consumer: Noise.evalNoise_poly
  Noise.map_affineGram; proof_shape: bind-only; escape_witness: none; consumer: Noise.map_pairDet
  Noise.map_pairDet; proof_shape: bind-only; escape_witness: none; consumer: Noise.evalNoise_poly
  Noise.evalNoise_poly; proof_shape: bind-only; escape_witness: none; consumer: Noise.evalNoise_polyAt
  Noise.poly_ne_zero; proof_shape: bind-only; escape_witness: none; consumer: CommonOrder.poly_common_order
  Noise.poly_degree_le; proof_shape: bind-only; escape_witness: none; consumer: Noise.poly_order_le
  Noise.poly_order_le; proof_shape: bind-only; escape_witness: none; consumer: Events.k_le
  Noise.evalNoise_ext; proof_shape: bind-only; escape_witness: none; consumer: CommonOrder.poly_common_order
  Noise.poly_coeff_map; proof_shape: bind-only; escape_witness: none; consumer: CommonOrder.poly_common_order
  Basis.exists_unitary_common; proof_shape: bind-only; escape_witness: none; consumer: Basis.common_eq_unitary_rankOne
  Basis.common_eq_unitary_rankOne; proof_shape: bind-only; escape_witness: none; consumer: CommonOrder.pairDet_common_lower
  Unitary.transformed_cross; proof_shape: bind-only; escape_witness: none; consumer: Unitary.affineGram_unitary
  Unitary.affineGram_unitary; proof_shape: bind-only; escape_witness: none; consumer: Unitary.pairDet_unitary
  Unitary.tensor_similarity; proof_shape: bind-only; escape_witness: none; consumer: Unitary.pairDet_unitary
  Unitary.pairDet_unitary; proof_shape: bind-only; escape_witness: none; consumer: CommonOrder.pairDet_common_lower
  CommonOrder.pairDet_common_lower; proof_shape: bind-only; escape_witness: none; consumer: CommonOrder.poly_common_order
  CommonOrder.pairDet_common_witness; proof_shape: bind-only; escape_witness: none; consumer: CommonOrder.poly_common_order
  CommonOrder.diagonal_witness_order; proof_shape: bind-only; escape_witness: none; consumer: CommonOrder.poly_common_order
  CommonOrder.poly_common_order; proof_shape: bind-only; escape_witness: none; consumer: Events.k_common
  FiniteBounds.weighted_order_upper; proof_shape: bind-only; escape_witness: none; consumer: Events.L_bounds
  FiniteBounds.weighted_order_lower; proof_shape: bind-only; escape_witness: none; consumer: Events.L_bounds
  FiniteBounds.coarse_bounds_at_one_over_256; proof_shape: bind-only; escape_witness: none; consumer: Events.L_gap
  Events.bmat; proof_shape: bind-only; escape_witness: none; consumer: Events.k
  Events.k; proof_shape: bind-only; escape_witness: none; consumer: Events.L
  Events.L; proof_shape: bind-only; escape_witness: none; consumer: Events.L_bounds
  Events.w_nonneg; proof_shape: bind-only; escape_witness: none; consumer: Events.L_bounds
  Events.w_sum; proof_shape: bind-only; escape_witness: none; consumer: Events.L_bounds
  Events.w_common; proof_shape: bind-only; escape_witness: none; consumer: Events.L_bounds
  Events.k_le; proof_shape: bind-only; escape_witness: none; consumer: Events.L_bounds
  Events.k_common; proof_shape: bind-only; escape_witness: none; consumer: Events.L_bounds
  Events.L_bounds; proof_shape: bind-only; escape_witness: none; consumer: Events.L_gap
  Events.L_gap; proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Analytic.Probability.SampleCovarianceLogEnergyRefutation.Energy.exists_fixed_epsilon
  Noise.eval_affineGram; proof_shape: bind-only; escape_witness: none; consumer: Noise.eval_pairDet
  Noise.eval_pairDet; proof_shape: bind-only; escape_witness: none; consumer: Noise.polyAt_ne_zero
  Noise.polyAt; proof_shape: bind-only; escape_witness: none; consumer: Noise.evalNoise_polyAt
  Noise.evalNoise_polyAt; proof_shape: bind-only; escape_witness: none; consumer: Noise.polyAt_ne_zero
  Noise.polyAt_ne_zero; proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Analytic.Probability.SampleCovarianceLogEnergyRefutation.Analytic.gaussian_det_nonzero_integrable
  Gaussian.gaussian_mv_abs_log_bound; proof_shape: content; escape_witness: D5.S3.Analytic.Probability.SampleCovarianceSpectralAndSmooth.Gaussian.gaussian_mv_log_coeff_lower; consumer: Gaussian.gaussian_mv_uniform_abs_log_bound
  Gaussian.gaussian_mv_uniform_abs_log_bound; proof_shape: content; escape_witness: D5.S3.Analytic.Probability.SampleCovarianceSpectralAndSmooth.Gaussian.gaussian_mv_log_coeff_lower; consumer: Gaussian.gaussian_noiseFamily_uniform_log
  Gaussian.noiseFamily_zero; proof_shape: bind-only; escape_witness: none; consumer: Gaussian.gaussian_noiseFamily_log_order
  Gaussian.noiseFamily_eval; proof_shape: bind-only; escape_witness: none; consumer: Gaussian.noiseFamily_integral_norm_bound
  Gaussian.noiseFamily_coeff_continuous; proof_shape: bind-only; escape_witness: none; consumer: Gaussian.gaussian_noiseFamily_log_order
  Gaussian.noiseFamily_degree_bound; proof_shape: bind-only; escape_witness: none; consumer: Gaussian.gaussian_noiseFamily_uniform_log
  Gaussian.noiseFamily_integral_norm_bound; proof_shape: bind-only; escape_witness: none; consumer: Gaussian.gaussian_noiseFamily_uniform_log
  Gaussian.gaussian_noiseFamily_uniform_log; proof_shape: content; escape_witness: D5.S3.Analytic.Probability.SampleCovarianceBernoulliOrders.Gaussian.gaussian_noiseFamily_uniform_log; consumer: Gaussian.gaussian_noiseFamily_log_remainder_tendsto
  Gaussian.gaussian_mv_log_integrable; proof_shape: content; escape_witness: D5.S3.Analytic.Probability.SampleCovarianceSpectralAndSmooth.Gaussian.gaussian_mv_log_coeff_lower; consumer: Gaussian.gaussian_mv_log_scalar
  Gaussian.gaussian_mv_log_scalar; proof_shape: content; escape_witness: D5.S3.Analytic.Probability.SampleCovarianceSpectralAndSmooth.Gaussian.gaussian_mv_log_coeff_lower; consumer: Gaussian.gaussian_noiseFamily_log_order
  Gaussian.gaussian_noiseFamily_log_remainder_tendsto; proof_shape: content; escape_witness: D5.S3.Analytic.Probability.SampleCovarianceBernoulliOrders.Gaussian.gaussian_noiseFamily_uniform_log; consumer: Gaussian.gaussian_noiseFamily_log_order
  Gaussian.gaussian_noiseFamily_log_order; proof_shape: content; escape_witness: D5.S3.Analytic.Probability.SampleCovarianceBernoulliOrders.Gaussian.gaussian_noiseFamily_uniform_log; consumer: D5.S3.Analytic.Probability.SampleCovarianceLogEnergyRefutation.Analytic.polynomial_log_order
Direct frozen dependencies:
  D5.S3.StatisticalMechanics.ParticleProcesses.ExclusionMovingParticleOptimality.bernoulli: ASSUMED-UNVERIFIED declaration identity; fresh Stage-B report required
  D5.S3.StatisticalMechanics.ParticleProcesses.ExclusionMovingParticleOptimality.bernoulli._proof_1: ASSUMED-UNVERIFIED declaration identity; fresh Stage-B report required
Unfinished escape audit: https://github.com/the-omega-institute/trureturing/issues/27612
-/
import D5.S3.Analytic.Probability.GaussianPolynomialLog
import D5.S3.Analytic.Probability.SampleCovarianceSpectralAndSmooth
import D5.S3.StatisticalMechanics.ParticleProcesses.ExclusionMovingParticleOptimality
import Mathlib.Algebra.MvPolynomial.Funext

set_option maxHeartbeats 2500000
set_option linter.unusedSimpArgs false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Matrix Polynomial
open scoped BigOperators Kronecker
namespace D5.S3.Analytic.Probability.SampleCovarianceBernoulliOrders.Noise
noncomputable section
private instance coeffStar (n : ℕ) : Star ((MvPolynomial (Bool × Bool × Fin n × Fin n) ℂ)) := ⟨MvPolynomial.map (starRingEnd ℂ)⟩
private instance coeffStarRing (n : ℕ) : StarRing ((MvPolynomial (Bool × Bool × Fin n × Fin n) ℂ)) where
  star_involutive p := by
    apply MvPolynomial.ext
    intro d
    change star (star (p.coeff d)) = p.coeff d
    exact star_star _
  star_add p q := by
    exact (MvPolynomial.map (starRingEnd ℂ)).map_add p q
  star_mul p q := by
    change (MvPolynomial.map (starRingEnd ℂ)) (p*q) = _
    rw [map_mul, mul_comm]
    rfl
private lemma star_C {n : ℕ} (z : ℂ) : star (MvPolynomial.C z : (MvPolynomial (Bool × Bool × Fin n × Fin n) ℂ)) = MvPolynomial.C (star z) := by
  simp only [star, MvPolynomial.map_C, starRingEnd_apply]
private lemma star_X {n : ℕ} (i : (Bool × Bool × Fin n × Fin n)) : star (MvPolynomial.X i : (MvPolynomial (Bool × Bool × Fin n × Fin n) ℂ)) = MvPolynomial.X i := by
  simp only [star, MvPolynomial.map_X]
def noise {n : ℕ} (b : Bool) : Matrix (Fin n) (Fin n) ((MvPolynomial (Bool × Bool × Fin n × Fin n) ℂ)) := fun i j =>
  MvPolynomial.X (b,false,i,j) + MvPolynomial.C Complex.I * MvPolynomial.X (b,true,i,j)
def poly {n : ℕ} (A C : Matrix (Fin n) (Fin n) ℂ) : Polynomial ((MvPolynomial (Bool × Bool × Fin n × Fin n) ℂ)) :=
  D5.S3.Analytic.Probability.GaussianPolynomialLog.Covariance.pairDet ((A.map MvPolynomial.C)) ((C.map MvPolynomial.C)) (noise false) (noise true)
def evalNoise {n : ℕ} (G K : Matrix (Fin n) (Fin n) ℂ) : (MvPolynomial (Bool × Bool × Fin n × Fin n) ℂ) →+* ℂ :=
  MvPolynomial.eval₂Hom (RingHom.id ℂ) (fun ⟨b,im,i,j⟩ =>
    if im then ((if b then K i j else G i j).im : ℂ)
    else ((if b then K i j else G i j).re : ℂ))
private lemma evalNoise_C {n : ℕ} (G K : Matrix (Fin n) (Fin n) ℂ) (z : ℂ) :
    evalNoise G K (MvPolynomial.C z) = z := by
  exact MvPolynomial.eval₂Hom_C (RingHom.id ℂ) _ z
private lemma evalNoise_star {n : ℕ} (G K : Matrix (Fin n) (Fin n) ℂ) (p : (MvPolynomial (Bool × Bool × Fin n × Fin n) ℂ)) :
    evalNoise G K (star p) = star (evalNoise G K p) := by
  induction p using MvPolynomial.induction_on with
  | C z => simp [star_C, evalNoise_C]
  | add p q hp hq => simp [star_add, map_add, hp, hq]
  | mul_X p i hp =>
    have hx : star (evalNoise G K (MvPolynomial.X i)) = evalNoise G K (MvPolynomial.X i) := by
      rcases i with ⟨b,im,i,j⟩
      cases b <;> cases im <;> simp [evalNoise, Complex.star_def]
    simp only [star_mul, map_mul, hp, star_X, hx]
private lemma evalNoise_noise {n : ℕ} (G K : Matrix (Fin n) (Fin n) ℂ) (b : Bool) :
    (noise b).map (evalNoise G K) = if b then K else G := by
  apply Matrix.ext
  intro i j
  cases b <;> apply Complex.ext <;> simp [noise, evalNoise]
private lemma map_affineGram {R S : Type*} [CommRing R] [StarRing R] [CommRing S] [StarRing S]
    {n : ℕ} (f : R →+* S) (hf : ∀ r, f (star r) = star (f r))
    (A G : Matrix (Fin n) (Fin n) R) :
    (D5.S3.Analytic.Probability.GaussianPolynomialLog.Covariance.affineGramPoly A G).map (Polynomial.mapRingHom f) =
      D5.S3.Analytic.Probability.GaussianPolynomialLog.Covariance.affineGramPoly (A.map f) (G.map f) := by
  have hc (r : R) : Polynomial.mapRingHom f (Polynomial.C r) = Polynomial.C (f r) :=
    Polynomial.map_C f
  have hx : Polynomial.mapRingHom f Polynomial.X = Polynomial.X := Polynomial.map_X _
  apply Matrix.ext
  intro i j
  change Polynomial.mapRingHom f
    (Polynomial.C ((A*Aᴴ) i j) + Polynomial.X*Polynomial.C ((A*Gᴴ+G*Aᴴ) i j) +
      Polynomial.X^2*Polynomial.C ((G*Gᴴ) i j)) = _
  simp only [map_add, map_mul, map_pow, hc, hx]
  simp only [D5.S3.Analytic.Probability.GaussianPolynomialLog.Covariance.affineGramPoly, Matrix.add_apply, Matrix.map_apply, Matrix.smul_apply,
    smul_eq_mul, Matrix.mul_apply, Matrix.conjTranspose_apply, map_sum, map_mul, map_add, hf]
private lemma map_pairDet {R S : Type*} [CommRing R] [StarRing R] [CommRing S] [StarRing S]
    {n : ℕ} (f : R →+* S) (hf : ∀ r, f (star r) = star (f r))
    (A C G K : Matrix (Fin n) (Fin n) R) :
    Polynomial.map f (D5.S3.Analytic.Probability.GaussianPolynomialLog.Covariance.pairDet A C G K) =
      D5.S3.Analytic.Probability.GaussianPolynomialLog.Covariance.pairDet (A.map f) (C.map f) (G.map f) (K.map f) := by
  unfold D5.S3.Analytic.Probability.GaussianPolynomialLog.Covariance.pairDet
  rw [← Polynomial.coe_mapRingHom, RingHom.map_det]
  congr 1
  let φ := Polynomial.mapRingHom f
  have hsub (B D : Matrix (Fin n × Fin n) (Fin n × Fin n) (Polynomial R)) :
      (B-D).map φ = B.map φ - D.map φ := by
    apply Matrix.ext
    intro i j
    exact φ.map_sub _ _
  have hkr (B D : Matrix (Fin n) (Fin n) (Polynomial R)) :
      (B ⊗ₖ D).map φ = B.map φ ⊗ₖ D.map φ := by
    apply Matrix.ext
    intro i j
    exact φ.map_mul _ _
  have h1 : (1 : Matrix (Fin n) (Fin n) (Polynomial R)).map φ = 1 := by
    apply Matrix.ext
    intro i j
    by_cases hij : i=j <;> simp [Matrix.one_apply, hij]
  change ((D5.S3.Analytic.Probability.GaussianPolynomialLog.Covariance.affineGramPoly A G ⊗ₖ (1 : Matrix (Fin n) (Fin n) (Polynomial R))) -
      (1 : Matrix (Fin n) (Fin n) (Polynomial R)) ⊗ₖ D5.S3.Analytic.Probability.GaussianPolynomialLog.Covariance.affineGramPoly C K).map φ = _
  rw [hsub, hkr, hkr, h1, map_affineGram f hf, map_affineGram f hf]
private lemma evalNoise_poly {n : ℕ} (A C G K : Matrix (Fin n) (Fin n) ℂ) :
    Polynomial.map (evalNoise G K) (poly A C) = D5.S3.Analytic.Probability.GaussianPolynomialLog.Covariance.pairDet A C G K := by
  rw [poly, map_pairDet _ (evalNoise_star G K), evalNoise_noise, evalNoise_noise]
  have he (D : Matrix (Fin n) (Fin n) ℂ) : (D.map MvPolynomial.C).map (evalNoise G K) = D := by
    ext i j
    exact evalNoise_C G K (D i j)
  rw [he, he]
  rfl
lemma poly_ne_zero {n : ℕ} (A C : Matrix (Fin n) (Fin n) ℂ) : poly A C ≠ 0 := by
  intro h
  have he := evalNoise_poly A C 1 0
  rw [h, Polynomial.map_zero] at he
  exact D5.S3.Analytic.Probability.GaussianPolynomialLog.Covariance.pairDet_identity_noise_ne_zero A C he.symm
private lemma poly_degree_le {n : ℕ} (A C : Matrix (Fin n) (Fin n) ℂ) :
    (poly A C).natDegree ≤ 2*n*n := D5.S3.Analytic.Probability.GaussianPolynomialLog.Covariance.pairDet_degree_le _ _ _ _
private lemma poly_order_le {n : ℕ} (A C : Matrix (Fin n) (Fin n) ℂ) :
    (poly A C).natTrailingDegree ≤ 2*n*n :=
  (Polynomial.natTrailingDegree_le_natDegree _).trans (poly_degree_le A C)
end
end D5.S3.Analytic.Probability.SampleCovarianceBernoulliOrders.Noise
namespace D5.S3.Analytic.Probability.SampleCovarianceBernoulliOrders.Noise
noncomputable section
private lemma evalNoise_ext {n : ℕ} (p : (MvPolynomial (Bool × Bool × Fin n × Fin n) ℂ))
    (h : ∀ G K : Matrix (Fin n) (Fin n) ℂ, evalNoise G K p = 0) : p = 0 := by
  classical
  apply MvPolynomial.funext_set (fun _ => Set.range Complex.ofReal)
    (fun _ => Set.infinite_range_of_injective Complex.ofReal_injective)
  intro z hz
  let G : Matrix (Fin n) (Fin n) ℂ := fun i j => z (false,false,i,j) +
    Complex.I * z (false,true,i,j)
  let K : Matrix (Fin n) (Fin n) ℂ := fun i j => z (true,false,i,j) +
    Complex.I * z (true,true,i,j)
  have hzre (i : (Bool × Bool × Fin n × Fin n)) : ((z i).re : ℂ) = z i := by
    obtain ⟨r,hr⟩ := hz i (Set.mem_univ i)
    rw [← hr]
    simp
  have hzim (i : (Bool × Bool × Fin n × Fin n)) : (z i).im = 0 := by
    obtain ⟨r,hr⟩ := hz i (Set.mem_univ i)
    rw [← hr]
    simp
  have he : evalNoise G K = MvPolynomial.eval z := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [evalNoise]
    · intro i
      rcases i with ⟨b,im,i,j⟩
      cases b <;> cases im <;>
        simp [evalNoise, G, K, Complex.mul_re, Complex.mul_im, hzim, hzre]
  rw [← he, h G K]
  simp
private lemma poly_coeff_map {n : ℕ} (A C G K : Matrix (Fin n) (Fin n) ℂ) (j : ℕ) :
    evalNoise G K ((poly A C).coeff j) = (D5.S3.Analytic.Probability.GaussianPolynomialLog.Covariance.pairDet A C G K).coeff j := by
  rw [← evalNoise_poly A C G K, Polynomial.coeff_map]
end
end D5.S3.Analytic.Probability.SampleCovarianceBernoulliOrders.Noise
namespace D5.S3.Analytic.Probability.SampleCovarianceBernoulliOrders.Noise
noncomputable section

end
end D5.S3.Analytic.Probability.SampleCovarianceBernoulliOrders.Noise
namespace D5.S3.Analytic.Probability.SampleCovarianceBernoulliOrders.Basis
noncomputable section
private lemma exists_unitary_common (s : ℕ) :
    ∃ U : Matrix (Fin (s+1)) (Fin (s+1)) ℂ,
      Uᴴ * U = 1 ∧ U * Uᴴ = 1 ∧
      ∀ i, U i 0 = (1 / Real.sqrt (s+1 : ℝ) : ℝ) := by
  let v : EuclideanSpace ℂ (Fin (s+1)) := WithLp.toLp 2
    (fun _ => ((1 / Real.sqrt (s+1 : ℝ) : ℝ) : ℂ))
  have hn : (s+1 : ℝ) ≠ 0 := Nat.cast_add_one_ne_zero s
  have hr : Real.sqrt (s+1 : ℝ) ≠ 0 := Real.sqrt_ne_zero'.mpr (by positivity)
  have hr2 := Real.sq_sqrt (show 0 ≤ (s+1 : ℝ) by positivity)
  have hv : ‖v‖ = 1 := by
    have hsq : ‖v‖^2 = 1 := by
      rw [EuclideanSpace.norm_sq_eq]
      simp only [v, PiLp.toLp_apply, Complex.norm_real, Real.norm_eq_abs, sq_abs,
        Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      simp only [div_pow, one_pow]
      rw [hr2]
      push_cast
      field_simp
    nlinarith [norm_nonneg v]
  have horth : Orthonormal ℂ (({0} : Set (Fin (s+1))).domRestrict (fun _ => v)) := by
    exact orthonormal_subsingleton_iff.mpr (fun _ => hv)
  obtain ⟨b,hb⟩ := Orthonormal.exists_orthonormalBasis_extension_of_card_eq
    (show Module.finrank ℂ (EuclideanSpace ℂ (Fin (s+1))) = Fintype.card (Fin (s+1)) by simp) horth
  let U : Matrix (Fin (s+1)) (Fin (s+1)) ℂ := Matrix.of (fun i j => b j i)
  have hu : Uᴴ * U = 1 := by
    apply Matrix.ext
    intro i j
    have h := (orthonormal_iff_ite.mp b.orthonormal) i j
    simpa [U, Matrix.of_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, PiLp.inner_apply,
      RCLike.inner_apply, mul_comm, Matrix.one_apply] using h
  refine ⟨U, hu, (mul_eq_one_comm.mp hu), ?_⟩
  intro i
  have h := hb 0 (by simp)
  exact congrArg (fun w : EuclideanSpace ℂ (Fin (s+1)) => w i) h
private lemma common_eq_unitary_rankOne (s : ℕ) (c : ℂ) :
    ∃ U : Matrix (Fin (s+1)) (Fin (s+1)) ℂ,
      Uᴴ * U = 1 ∧ U * Uᴴ = 1 ∧
      (Matrix.of (fun _ _ => c)) = U * Matrix.single 0 0 ((s+1 : ℕ)*c) * Uᴴ := by
  obtain ⟨U,hU,hU',hcol⟩ := exists_unitary_common s
  refine ⟨U,hU,hU',?_⟩
  apply Matrix.ext
  intro i j
  have he (a : ℂ) : (U * (Matrix.single 0 0 a : Matrix (Fin (s+1)) (Fin (s+1)) ℂ) * Uᴴ) i j =
      U i 0 * a * star (U j 0) := by
    simp only [← Matrix.diagonal_single, Pi.single_apply, eq_comm, Matrix.mul_apply, Matrix.diagonal_apply,
      Matrix.conjTranspose_apply]
    simp [ite_mul, mul_ite]
  rw [Matrix.of_apply, he, hcol, hcol]
  simp only [Complex.star_def, Complex.conj_ofReal]
  have hr2 := Real.sq_sqrt (show 0 ≤ (s+1 : ℝ) by positivity)
  have hr : Real.sqrt (s+1 : ℝ) ≠ 0 := Real.sqrt_ne_zero'.mpr (by positivity)
  have hc : (Real.sqrt (s+1 : ℝ) : ℂ)^2 = (s+1 : ℕ) := by exact_mod_cast hr2
  have hrc : (Real.sqrt (s+1 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hr
  push_cast
  field_simp
  push_cast at hc
  linear_combination c*hc
end
end D5.S3.Analytic.Probability.SampleCovarianceBernoulliOrders.Basis
namespace D5.S3.Analytic.Probability.SampleCovarianceBernoulliOrders.Unitary
noncomputable section
variable {R : Type*} [CommRing R] [StarRing R] {n : ℕ}
private lemma transformed_cross (U V A G : Matrix (Fin n) (Fin n) R) (hV : V * Vᴴ = 1) :
    (U*A*V)*(U*G*V)ᴴ = U*(A*Gᴴ)*Uᴴ := by
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul]
  calc
    _ = U*A*(V*Vᴴ)*Gᴴ*Uᴴ := by noncomm_ring
    _ = _ := by rw [hV]; simp only [Matrix.mul_one, Matrix.mul_assoc]
private lemma affineGram_unitary (U V A G : Matrix (Fin n) (Fin n) R) (hV : V * Vᴴ = 1) :
    D5.S3.Analytic.Probability.GaussianPolynomialLog.Covariance.affineGramPoly (U*A*V) (U*G*V) =
      U.map Polynomial.C * D5.S3.Analytic.Probability.GaussianPolynomialLog.Covariance.affineGramPoly A G * Uᴴ.map Polynomial.C := by
  unfold D5.S3.Analytic.Probability.GaussianPolynomialLog.Covariance.affineGramPoly
  simp only [transformed_cross U V _ _ hV]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul]
  congr 2
  all_goals
    simp only [← Matrix.map_mul, ← Matrix.map_add, ← Matrix.mul_add,
      ← Matrix.add_mul, Matrix.mul_assoc]
  all_goals simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc]
omit [StarRing R] in
private lemma tensor_similarity (u v H K : Matrix (Fin n) (Fin n) (Polynomial R))
    (hu : u*v=1) :
    (u*H*v) ⊗ₖ (1 : Matrix (Fin n) (Fin n) (Polynomial R)) -
      (1 : Matrix (Fin n) (Fin n) (Polynomial R)) ⊗ₖ (u*K*v) =
      (u ⊗ₖ u) * (H ⊗ₖ (1 : Matrix (Fin n) (Fin n) (Polynomial R)) -
        (1 : Matrix (Fin n) (Fin n) (Polynomial R)) ⊗ₖ K) * (v ⊗ₖ v) := by
  rw [Matrix.mul_sub, Matrix.sub_mul]
  simp only [← Matrix.mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul, hu]
private lemma pairDet_unitary (U V A C G K : Matrix (Fin n) (Fin n) R)
    (hU : U * Uᴴ = 1) (hV : V * Vᴴ = 1) :
    D5.S3.Analytic.Probability.GaussianPolynomialLog.Covariance.pairDet (U*A*V) (U*C*V) (U*G*V) (U*K*V) =
      D5.S3.Analytic.Probability.GaussianPolynomialLog.Covariance.pairDet A C G K := by
  unfold D5.S3.Analytic.Probability.GaussianPolynomialLog.Covariance.pairDet
  rw [affineGram_unitary U V A G hV, affineGram_unitary U V C K hV]
  have hu : U.map Polynomial.C * Uᴴ.map Polynomial.C =
      (1 : Matrix (Fin n) (Fin n) (Polynomial R)) := by
    rw [← Matrix.map_mul, hU]
    apply Matrix.ext
    intro i j
    by_cases hij : i=j <;> simp [Matrix.one_apply, hij]
  rw [tensor_similarity _ _ _ _ hu, Matrix.det_mul, Matrix.det_mul]
  have huv : (U.map Polynomial.C ⊗ₖ U.map Polynomial.C) *
      (Uᴴ.map Polynomial.C ⊗ₖ Uᴴ.map Polynomial.C) = 1 := by
    rw [← Matrix.mul_kronecker_mul, hu, Matrix.one_kronecker_one]
  have hdet := congrArg Matrix.det huv
  rw [Matrix.det_mul, Matrix.det_one] at hdet
  calc
    _ = ((U.map Polynomial.C ⊗ₖ U.map Polynomial.C).det *
        (Uᴴ.map Polynomial.C ⊗ₖ Uᴴ.map Polynomial.C).det) *
        (D5.S3.Analytic.Probability.GaussianPolynomialLog.Covariance.affineGramPoly A G ⊗ₖ (1 : Matrix (Fin n) (Fin n) (Polynomial R)) -
          (1 : Matrix (Fin n) (Fin n) (Polynomial R)) ⊗ₖ D5.S3.Analytic.Probability.GaussianPolynomialLog.Covariance.affineGramPoly C K).det := by ring
    _ = _ := by rw [hdet, one_mul]
end
end D5.S3.Analytic.Probability.SampleCovarianceBernoulliOrders.Unitary
namespace D5.S3.Analytic.Probability.SampleCovarianceBernoulliOrders.CommonOrder
noncomputable section
private lemma pairDet_common_lower (s : ℕ) (c : ℂ)
    (G K : Matrix (Fin (s+1)) (Fin (s+1)) ℂ) :
    (Polynomial.X : Polynomial ℂ)^(2*s*s+1) ∣
      D5.S3.Analytic.Probability.GaussianPolynomialLog.Covariance.pairDet (Matrix.of (fun _ _ => c)) (Matrix.of (fun _ _ => c)) G K := by
  obtain ⟨U,hu,hu',hc⟩ := D5.S3.Analytic.Probability.SampleCovarianceBernoulliOrders.Basis.common_eq_unitary_rankOne s c
  have hinv (B : Matrix (Fin (s+1)) (Fin (s+1)) ℂ) : U*(Uᴴ*B*U)*Uᴴ = B := by
    calc
      _ = (U*Uᴴ)*B*(U*Uᴴ) := by noncomm_ring
      _ = B := by rw [hu']; simp
  have he := D5.S3.Analytic.Probability.SampleCovarianceBernoulliOrders.Unitary.pairDet_unitary U Uᴴ
    (Matrix.single (0 : Fin (s+1)) 0 ((s+1:ℕ)*c)) (Matrix.single (0 : Fin (s+1)) 0 ((s+1:ℕ)*c))
    (Uᴴ*G*U) (Uᴴ*K*U) hu' (by simpa using hu)
  rw [← hc, hinv, hinv] at he
  rw [he]
  exact D5.S3.Analytic.Probability.GaussianPolynomialLog.Covariance.rankOne_order_lower _ _ _
private lemma pairDet_common_witness (s : ℕ) (c : ℂ) :
    D5.S3.Analytic.Probability.GaussianPolynomialLog.Covariance.pairDet (Matrix.of (fun _ _ : Fin (s+1) => c)) (Matrix.of (fun _ _ => c)) 1 0 =
      D5.S3.Analytic.Probability.GaussianPolynomialLog.Covariance.pairDet (Matrix.single (0 : Fin (s+1)) 0 ((s+1:ℕ)*c))
        (Matrix.single (0 : Fin (s+1)) 0 ((s+1:ℕ)*c)) 1 0 := by
  obtain ⟨U,hu,hu',hc⟩ := D5.S3.Analytic.Probability.SampleCovarianceBernoulliOrders.Basis.common_eq_unitary_rankOne s c
  have he := D5.S3.Analytic.Probability.SampleCovarianceBernoulliOrders.Unitary.pairDet_unitary U Uᴴ
    (Matrix.single (0 : Fin (s+1)) 0 ((s+1:ℕ)*c)) (Matrix.single (0 : Fin (s+1)) 0 ((s+1:ℕ)*c)) 1 0 hu'
    (by simpa using hu)
  simpa only [← hc, Matrix.mul_one, hu', Matrix.mul_zero, Matrix.zero_mul] using he
private lemma diagonal_witness_order (s : ℕ) (a : ℝ) (ha : a ≠ 0) :
    (D5.S3.Analytic.Probability.GaussianPolynomialLog.Covariance.pairDet (Matrix.single 0 0 (a : ℂ))
      (Matrix.single 0 0 (a : ℂ)) (1 : Matrix (Fin (s+1)) (Fin (s+1)) ℂ) 0).natTrailingDegree =
      2*s*s+1 := by
  exact D5.S3.Analytic.Probability.GaussianPolynomialLog.Covariance.pairDet_rankOne_witness_order a ha
private lemma poly_common_order (s : ℕ) (c : ℝ) (hc : c ≠ 0) :
    (D5.S3.Analytic.Probability.SampleCovarianceBernoulliOrders.Noise.poly (Matrix.of (fun _ _ : Fin (s+1) => (c:ℂ))) (Matrix.of (fun _ _ => (c:ℂ)))).natTrailingDegree =
      2*s*s+1 := by
  let P := D5.S3.Analytic.Probability.SampleCovarianceBernoulliOrders.Noise.poly (Matrix.of (fun _ _ : Fin (s+1) => (c:ℂ))) (Matrix.of (fun _ _ => (c:ℂ)))
  have hP : P ≠ 0 := D5.S3.Analytic.Probability.SampleCovarianceBernoulliOrders.Noise.poly_ne_zero _ _
  have hlo : 2*s*s+1 ≤ P.natTrailingDegree := by
    apply Polynomial.le_natTrailingDegree hP
    intro j hj
    apply D5.S3.Analytic.Probability.SampleCovarianceBernoulliOrders.Noise.evalNoise_ext
    intro G K
    rw [D5.S3.Analytic.Probability.SampleCovarianceBernoulliOrders.Noise.poly_coeff_map]
    exact Polynomial.X_pow_dvd_iff.mp (pairDet_common_lower s c G K) j hj
  have ha : (s+1:ℝ)*c ≠ 0 := mul_ne_zero (by positivity) hc
  have horder := diagonal_witness_order s ((s+1:ℝ)*c) ha
  have he := pairDet_common_witness s (c:ℂ)
  have hn : (((s+1:ℝ)*c : ℝ):ℂ) = (s+1:ℕ)*(c:ℂ) := by push_cast; ring
  rw [hn] at horder
  rw [← he] at horder
  have hwne := D5.S3.Analytic.Probability.GaussianPolynomialLog.Covariance.pairDet_identity_noise_ne_zero
    (Matrix.of (fun _ _ : Fin (s+1) => (c:ℂ))) (Matrix.of (fun _ _ => (c:ℂ)))
  have hcoeff : P.coeff (2*s*s+1) ≠ 0 := by
    intro h
    have hz := congrArg (D5.S3.Analytic.Probability.SampleCovarianceBernoulliOrders.Noise.evalNoise 1 0) h
    rw [D5.S3.Analytic.Probability.SampleCovarianceBernoulliOrders.Noise.poly_coeff_map, map_zero] at hz
    apply (Polynomial.coeff_natTrailingDegree_ne_zero.mpr hwne)
    rwa [horder]
  exact le_antisymm (Polynomial.natTrailingDegree_le_of_ne_zero hcoeff) hlo
end
end D5.S3.Analytic.Probability.SampleCovarianceBernoulliOrders.CommonOrder
namespace D5.S3.Analytic.Probability.SampleCovarianceBernoulliOrders.CommonOrder
noncomputable section

end
end D5.S3.Analytic.Probability.SampleCovarianceBernoulliOrders.CommonOrder
open MeasureTheory
open scoped ENNReal BigOperators
namespace D5.S3.Analytic.Probability.SampleCovarianceBernoulliOrders.FiniteBounds
noncomputable section

private lemma weighted_order_upper {ι : Type*} [Fintype ι] (w k : ι → ℝ)
    (a : ι) (c M : ℝ) (hw : ∀ i, 0 ≤ w i) (hsum : ∑ i, w i = 1)
    (hk : ∀ i, k i ≤ M) (ha : k a = c) :
    (∑ i, w i * k i) ≤ M - (M-c)*w a := by
  classical
  have hb : ∑ i, w i * (M-k i) ≥ w a * (M-c) := by
    rw [← ha]
    exact Finset.single_le_sum (fun i _ => mul_nonneg (hw i) (sub_nonneg.mpr (hk i)))
      (Finset.mem_univ a)
  have he : (∑ i, w i * (M-k i)) = M - ∑ i, w i * k i := by
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hsum, one_mul]
  rw [he] at hb
  nlinarith
private lemma weighted_order_lower {ι : Type*} [Fintype ι] (w k : ι → ℝ)
    (a : ι) (c : ℝ) (hw : ∀ i, 0 ≤ w i) (hk : ∀ i, 0 ≤ k i)
    (ha : c ≤ k a) :
    c * w a ≤ ∑ i, w i * k i := by
  classical
  calc
    c * w a ≤ w a * k a := by nlinarith [hw a]
    _ ≤ _ := Finset.single_le_sum (fun i _ => mul_nonneg (hw i) (hk i)) (Finset.mem_univ a)
private lemma coarse_bounds_at_one_over_256 (L₂ L₃ : ℝ)
    (h₂ : L₂ ≤ 2 - (5/4 : ℝ)*(1-(1/256 : ℝ))^8)
    (h₃ : (1-(1/256 : ℝ))^18 ≤ L₃) :
    L₂ ≤ 101/128 ∧ 119/128 ≤ L₃ ∧ L₂ < L₃ := by
  have h8 : (31/32 : ℝ) ≤ (1-(1/256 : ℝ))^8 := by
    have h := one_add_mul_sub_le_pow (show (-1:ℝ) ≤ 1-(1/256 : ℝ) by norm_num) 8
    norm_num at h ⊢
  have h18 : (119/128 : ℝ) ≤ (1-(1/256 : ℝ))^18 := by
    have h := one_add_mul_sub_le_pow (show (-1:ℝ) ≤ 1-(1/256 : ℝ) by norm_num) 18
    norm_num at h ⊢
  constructor
  · nlinarith
  constructor
  · linarith
  · nlinarith

end
end D5.S3.Analytic.Probability.SampleCovarianceBernoulliOrders.FiniteBounds

namespace D5.S3.Analytic.Probability.SampleCovarianceBernoulliOrders.Events
open D5.S3.Analytic.Probability.SampleCovarianceBernoulliOrders.Noise
noncomputable section
def bmat {n : ℕ} (b : ((Bool × Fin n × Fin n) → Bool)) (side : Bool) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of (fun i j => if b (side,i,j) then (Real.sqrt 255 : ℂ) else (-1/Real.sqrt 255 : ℝ))
def k {n : ℕ} (b : ((Bool × Fin n × Fin n) → Bool)) : ℕ := (poly (bmat b false) (bmat b true)).natTrailingDegree
def L (n : ℕ) : ℝ := (∑ b : ((Bool × Fin n × Fin n) → Bool), D5.S3.StatisticalMechanics.ParticleProcesses.ExclusionMovingParticleOptimality.bernoulli (1/256) (fun i => finTwoEquiv.symm (b i)) * k b) / (n:ℝ)^2
private lemma w_nonneg {n : ℕ} (b : ((Bool × Fin n × Fin n) → Bool)) : 0 ≤ D5.S3.StatisticalMechanics.ParticleProcesses.ExclusionMovingParticleOptimality.bernoulli (1/256) (fun i => finTwoEquiv.symm (b i)) := by
  unfold D5.S3.StatisticalMechanics.ParticleProcesses.ExclusionMovingParticleOptimality.bernoulli
  apply Finset.prod_nonneg
  intro i hi
  split <;> norm_num
lemma w_sum (n : ℕ) : ∑ b : ((Bool × Fin n × Fin n) → Bool), D5.S3.StatisticalMechanics.ParticleProcesses.ExclusionMovingParticleOptimality.bernoulli (1/256) (fun i => finTwoEquiv.symm (b i)) = 1 := by
  simp only [D5.S3.StatisticalMechanics.ParticleProcesses.ExclusionMovingParticleOptimality.bernoulli]
  have h (b : (Bool × Fin n × Fin n) → Bool) :
      (∏ i, if finTwoEquiv.symm (b i) = 1 then (1/256 : ℝ) else 1-1/256) =
      ∏ i, if b i then (1/256 : ℝ) else 255/256 := by
    apply Finset.prod_congr rfl
    intro i hi
    cases hbi : b i <;> norm_num [hbi, finTwoEquiv]
  simp_rw [h]
  have he := Fintype.prod_sum (fun (_ : (Bool × Fin n × Fin n)) (b : Bool) =>
    if b then (1/256 : ℝ) else 255/256)
  calc
    _ = ∏ i : (Bool × Fin n × Fin n), ∑ b : Bool, if b then (1/256 : ℝ) else 255/256 := he.symm
    _ = 1 := by norm_num [Fintype.sum_bool]
private lemma w_common (n : ℕ) : D5.S3.StatisticalMechanics.ParticleProcesses.ExclusionMovingParticleOptimality.bernoulli (1/256) (fun _ : Bool × Fin n × Fin n => finTwoEquiv.symm false) = (255/256 : ℝ)^(2*n*n) := by
  norm_num [D5.S3.StatisticalMechanics.ParticleProcesses.ExclusionMovingParticleOptimality.bernoulli,
    finTwoEquiv, div_pow] <;> congr 1 <;> ring

private lemma k_le {n : ℕ} (b : ((Bool × Fin n × Fin n) → Bool)) : k b ≤ 2*n*n := poly_order_le _ _
private lemma k_common (s : ℕ) : k (fun _ : (Bool × Fin (s+1) × Fin (s+1)) => false) = 2*s*s+1 := by
  have hc : (-1/Real.sqrt 255 : ℝ) ≠ 0 := by
    apply div_ne_zero (by norm_num)
    exact Real.sqrt_ne_zero'.mpr (by norm_num)
  exact D5.S3.Analytic.Probability.SampleCovarianceBernoulliOrders.CommonOrder.poly_common_order s (-1/Real.sqrt 255) hc
private lemma L_bounds : L 2 ≤ 2-(5/4:ℝ)*(255/256:ℝ)^8 ∧ (255/256:ℝ)^18 ≤ L 3 := by
  have hu := D5.S3.Analytic.Probability.SampleCovarianceBernoulliOrders.FiniteBounds.weighted_order_upper (fun b : (Bool × Fin 2 × Fin 2) → Bool => D5.S3.StatisticalMechanics.ParticleProcesses.ExclusionMovingParticleOptimality.bernoulli (1/256) (fun i => finTwoEquiv.symm (b i))) (fun b => (k b : ℝ))
    (fun _ => false) 3 8 w_nonneg (w_sum 2)
    (fun b => by exact_mod_cast k_le b) (by exact_mod_cast k_common 1)
  have hl := D5.S3.Analytic.Probability.SampleCovarianceBernoulliOrders.FiniteBounds.weighted_order_lower (fun b : (Bool × Fin 3 × Fin 3) → Bool => D5.S3.StatisticalMechanics.ParticleProcesses.ExclusionMovingParticleOptimality.bernoulli (1/256) (fun i => finTwoEquiv.symm (b i))) (fun b => (k b : ℝ))
    (fun _ => false) 9 w_nonneg (fun b => Nat.cast_nonneg _)
    (by exact_mod_cast (k_common 2).ge)
  rw [w_common] at hu hl
  constructor
  · unfold L
    norm_num only [Nat.cast_ofNat, OfNat.ofNat, pow_two]
    change (∑ b : ((Bool × Fin 2 × Fin 2) → Bool), D5.S3.StatisticalMechanics.ParticleProcesses.ExclusionMovingParticleOptimality.bernoulli (1/256) (fun i => finTwoEquiv.symm (b i)) * (k b : ℝ)) ≤ 8 - (8-3)*(255/256:ℝ)^8 at hu
    nlinarith
  · unfold L
    norm_num only [Nat.cast_ofNat, OfNat.ofNat, pow_two]
    change 9*(255/256:ℝ)^18 ≤ (∑ b : ((Bool × Fin 3 × Fin 3) → Bool), D5.S3.StatisticalMechanics.ParticleProcesses.ExclusionMovingParticleOptimality.bernoulli (1/256) (fun i => finTwoEquiv.symm (b i)) * (k b : ℝ)) at hl
    nlinarith
lemma L_gap : L 2 < L 3 := by
  have h := D5.S3.Analytic.Probability.SampleCovarianceBernoulliOrders.FiniteBounds.coarse_bounds_at_one_over_256 (L 2) (L 3)
    (by convert L_bounds.1 using 1 <;> norm_num) (by convert L_bounds.2 using 1 <;> norm_num)
  exact h.2.2
end
end D5.S3.Analytic.Probability.SampleCovarianceBernoulliOrders.Events
namespace D5.S3.Analytic.Probability.SampleCovarianceBernoulliOrders.Noise
noncomputable section
private lemma eval_affineGram {n : ℕ} (ε : ℝ) (A G : Matrix (Fin n) (Fin n) ℂ) :
    (D5.S3.Analytic.Probability.GaussianPolynomialLog.Covariance.affineGramPoly A G).map (Polynomial.evalRingHom (ε:ℂ)) =
      (A+(ε:ℂ) • G)*(A+(ε:ℂ) • G)ᴴ := by
  have hconst (z : ℂ) : (Polynomial.evalRingHom (ε:ℂ)) (Polynomial.C z) = z := Polynomial.eval_C
  have hx : (Polynomial.evalRingHom (ε:ℂ)) Polynomial.X = (ε:ℂ) := Polynomial.eval_X
  apply Matrix.ext
  intro i j
  change (Polynomial.evalRingHom (ε:ℂ))
    (Polynomial.C ((A*Aᴴ) i j) + Polynomial.X * Polynomial.C ((A*Gᴴ+G*Aᴴ) i j) +
      Polynomial.X^2 * Polynomial.C ((G*Gᴴ) i j)) = _
  simp only [map_add, map_mul, map_pow, hconst, hx, Matrix.conjTranspose_add, Matrix.conjTranspose_smul,
    Complex.star_def, Complex.conj_ofReal, Matrix.mul_add, Matrix.add_mul,
    Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.add_apply, Matrix.smul_apply,
    smul_eq_mul]
  ring
lemma eval_pairDet {n : ℕ} (ε : ℝ) (A C G K : Matrix (Fin n) (Fin n) ℂ) :
    (D5.S3.Analytic.Probability.GaussianPolynomialLog.Covariance.pairDet A C G K).eval (ε:ℂ) =
      Matrix.det (((A+(ε:ℂ) • G)*(A+(ε:ℂ) • G)ᴴ) ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ) -
        (1 : Matrix (Fin n) (Fin n) ℂ) ⊗ₖ ((C+(ε:ℂ) • K)*(C+(ε:ℂ) • K)ᴴ)) := by
  change (Polynomial.evalRingHom (ε:ℂ)) (Matrix.det _) = _
  rw [RingHom.map_det]
  congr 1
  let φ := Polynomial.evalRingHom (ε:ℂ)
  have hsub (B D : Matrix (Fin n × Fin n) (Fin n × Fin n) (Polynomial ℂ)) :
      (B-D).map φ = B.map φ - D.map φ := by
    apply Matrix.ext
    intro i j
    exact φ.map_sub _ _
  have hkr (B D : Matrix (Fin n) (Fin n) (Polynomial ℂ)) :
      (B ⊗ₖ D).map φ = B.map φ ⊗ₖ D.map φ := by
    apply Matrix.ext
    intro i j
    exact φ.map_mul _ _
  have h1 : (1 : Matrix (Fin n) (Fin n) (Polynomial ℂ)).map φ = 1 := by
    apply Matrix.ext
    intro i j
    by_cases hij : i=j <;> simp [Matrix.one_apply, hij]
  change ((D5.S3.Analytic.Probability.GaussianPolynomialLog.Covariance.affineGramPoly A G ⊗ₖ (1 : Matrix (Fin n) (Fin n) (Polynomial ℂ))) -
      (1 : Matrix (Fin n) (Fin n) (Polynomial ℂ)) ⊗ₖ D5.S3.Analytic.Probability.GaussianPolynomialLog.Covariance.affineGramPoly C K).map φ = _
  rw [hsub, hkr, hkr, h1, eval_affineGram, eval_affineGram]
def polyAt {n : ℕ} (A C : Matrix (Fin n) (Fin n) ℂ) (ε : ℝ) : (MvPolynomial (Bool × Bool × Fin n × Fin n) ℂ) :=
  (poly A C).eval (MvPolynomial.C (ε:ℂ))
lemma evalNoise_polyAt {n : ℕ} (ε : ℝ) (A C G K : Matrix (Fin n) (Fin n) ℂ) :
    evalNoise G K (polyAt A C ε) = (D5.S3.Analytic.Probability.GaussianPolynomialLog.Covariance.pairDet A C G K).eval (ε:ℂ) := by
  simpa only [evalNoise_C, evalNoise_poly, polyAt] using
    (Polynomial.eval_map_apply (f:=evalNoise G K) (p:=poly A C)
      (MvPolynomial.C (ε:ℂ))).symm
lemma polyAt_ne_zero {n : ℕ} (A C : Matrix (Fin n) (Fin n) ℂ) (ε : ℝ) (hε : ε ≠ 0) :
    polyAt A C ε ≠ 0 := by
  have hεC : (ε:ℂ) ≠ 0 := by exact_mod_cast hε
  let G : Matrix (Fin n) (Fin n) ℂ := (ε:ℂ)⁻¹ • (1-A)
  let K : Matrix (Fin n) (Fin n) ℂ := (ε:ℂ)⁻¹ • (-C)
  have hA : A+(ε:ℂ) • G = 1 := by
    dsimp only [G]
    rw [smul_smul, mul_inv_cancel₀ hεC, one_smul]
    abel
  have hC : C+(ε:ℂ) • K = 0 := by
    dsimp only [K]
    rw [smul_smul, mul_inv_cancel₀ hεC, one_smul]
    abel
  intro h
  have hz := congrArg (evalNoise G K) h
  rw [evalNoise_polyAt, eval_pairDet, hA, hC] at hz
  simpa using hz
end
end D5.S3.Analytic.Probability.SampleCovarianceBernoulliOrders.Noise

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators

open MeasureTheory Filter Set ProbabilityTheory
open scoped ENNReal NNReal Topology BigOperators
namespace D5.S3.Analytic.Probability.SampleCovarianceBernoulliOrders.Gaussian
noncomputable section

private lemma gaussian_mv_abs_log_bound (m : ℝ) (v : ℝ≥0) (hv : v ≠ 0) (n : ℕ)
    (p : MvPolynomial (Fin n) ℂ) (d : Fin n →₀ ℕ) (D : ℕ)
    (hd : p.coeff d ≠ 0) (hD : ∀ i, p.degreeOf i ≤ D) :
    (∫ x, |Real.log ‖(fun {n : ℕ} (p : MvPolynomial (Fin n) ℂ) (x : Fin n → ℝ) => MvPolynomial.eval (fun i => (x i : ℂ)) p) p x‖| ∂(fun n m v => Measure.pi (fun _ : Fin n => gaussianReal m v)) n m v) ≤
      2*(∫ x, ‖(fun {n : ℕ} (p : MvPolynomial (Fin n) ℂ) (x : Fin n → ℝ) => MvPolynomial.eval (fun i => (x i : ℂ)) p) p x‖ ∂(fun n m v => Measure.pi (fun _ : Fin n => gaussianReal m v)) n m v) - Real.log ‖p.coeff d‖ +
        (n : ℝ)*D*(Real.log 2 + D5.S3.Analytic.Probability.GaussianPolynomialLog.rootLogCost m v) := by
  obtain ⟨_, hl, hc⟩ := D5.S3.Analytic.Probability.SampleCovarianceSpectralAndSmooth.Gaussian.gaussian_mv_log_coeff_lower m v hv n p d D hd hD
  have hn := (D5.S3.Analytic.Probability.SampleCovarianceSpectralAndSmooth.Gaussian.gaussian_mv_eval_integrable m v p).norm
  have hb : (∫ x, |Real.log ‖(fun {n : ℕ} (p : MvPolynomial (Fin n) ℂ) (x : Fin n → ℝ) => MvPolynomial.eval (fun i => (x i : ℂ)) p) p x‖| ∂(fun n m v => Measure.pi (fun _ : Fin n => gaussianReal m v)) n m v) ≤
      2*(∫ x, ‖(fun {n : ℕ} (p : MvPolynomial (Fin n) ℂ) (x : Fin n → ℝ) => MvPolynomial.eval (fun i => (x i : ℂ)) p) p x‖ ∂(fun n m v => Measure.pi (fun _ : Fin n => gaussianReal m v)) n m v) -
        ∫ x, Real.log ‖(fun {n : ℕ} (p : MvPolynomial (Fin n) ℂ) (x : Fin n → ℝ) => MvPolynomial.eval (fun i => (x i : ℂ)) p) p x‖ ∂(fun n m v => Measure.pi (fun _ : Fin n => gaussianReal m v)) n m v := by
    rw [← integral_const_mul, ← integral_sub (hn.const_mul 2) hl]
    apply integral_mono_ae hl.abs ((hn.const_mul 2).sub hl)
    filter_upwards [] with x
    rw [← Real.norm_eq_abs, D5.S3.Analytic.Probability.GaussianPolynomialLog.norm_eq_two_pos_sub]
    exact sub_le_sub_right (mul_le_mul_of_nonneg_left (by simpa only [Real.posLog, max_comm, abs_norm] using
      (Real.posLog_le_abs ‖(MvPolynomial.eval (fun i => (x i : ℂ))) p‖)) (by norm_num)) _
  linarith

private lemma gaussian_mv_uniform_abs_log_bound (m : ℝ) (v : ℝ≥0) (hv : v ≠ 0) (n D : ℕ)
    (p : MvPolynomial (Fin n) ℂ) (d : Fin n →₀ ℕ) (c M : ℝ)
    (hc : 0 < c) (hcoeff : c ≤ ‖p.coeff d‖)
    (hD : ∀ i, p.degreeOf i ≤ D)
    (hM : (∫ x, ‖(fun {n : ℕ} (p : MvPolynomial (Fin n) ℂ) (x : Fin n → ℝ) => MvPolynomial.eval (fun i => (x i : ℂ)) p) p x‖ ∂(fun n m v => Measure.pi (fun _ : Fin n => gaussianReal m v)) n m v) ≤ M) :
    Integrable (fun x => Real.log ‖(fun {n : ℕ} (p : MvPolynomial (Fin n) ℂ) (x : Fin n → ℝ) => MvPolynomial.eval (fun i => (x i : ℂ)) p) p x‖) ((fun n m v => Measure.pi (fun _ : Fin n => gaussianReal m v)) n m v) ∧
    (∫ x, |Real.log ‖(fun {n : ℕ} (p : MvPolynomial (Fin n) ℂ) (x : Fin n → ℝ) => MvPolynomial.eval (fun i => (x i : ℂ)) p) p x‖| ∂(fun n m v => Measure.pi (fun _ : Fin n => gaussianReal m v)) n m v) ≤
      2*M - Real.log c + (n : ℝ)*D*(Real.log 2 + D5.S3.Analytic.Probability.GaussianPolynomialLog.rootLogCost m v) := by
  have hd : p.coeff d ≠ 0 := norm_pos_iff.mp (hc.trans_le hcoeff)
  refine ⟨(D5.S3.Analytic.Probability.SampleCovarianceSpectralAndSmooth.Gaussian.gaussian_mv_log_coeff_lower m v hv n p d D hd hD).2.1, ?_⟩
  have hb := gaussian_mv_abs_log_bound m v hv n p d D hd hD
  have hlog := Real.log_le_log hc hcoeff
  linarith

end
end D5.S3.Analytic.Probability.SampleCovarianceBernoulliOrders.Gaussian

namespace D5.S3.Analytic.Probability.SampleCovarianceBernoulliOrders.Gaussian
noncomputable section

private lemma noiseFamily_zero {n N : ℕ} (q : Fin (N+1) → MvPolynomial (Fin n) ℂ) :
    (∑ j : Fin (N+1), MvPolynomial.C ((0 : ℂ)^(j : ℕ)) * q j) = q 0 := by
  simp [Fin.sum_univ_succ]

private lemma noiseFamily_eval {n N : ℕ} (q : Fin (N+1) → MvPolynomial (Fin n) ℂ)
    (ε : ℝ) (x : Fin n → ℝ) :
    (fun {n : ℕ} (p : MvPolynomial (Fin n) ℂ) (x : Fin n → ℝ) => MvPolynomial.eval (fun i => (x i : ℂ)) p) ((∑ j : Fin (N+1), MvPolynomial.C ((ε : ℂ)^(j : ℕ)) * q j)) x = ∑ k : Fin (N+1), (ε : ℂ)^(k : ℕ) * (fun {n : ℕ} (p : MvPolynomial (Fin n) ℂ) (x : Fin n → ℝ) => MvPolynomial.eval (fun i => (x i : ℂ)) p) (q k) x := by
  simp only [map_sum, map_mul, MvPolynomial.eval_C]

private lemma noiseFamily_coeff_continuous {n N : ℕ}
    (q : Fin (N+1) → MvPolynomial (Fin n) ℂ) (d : Fin n →₀ ℕ) :
    Continuous (fun ε : ℝ => ((∑ j : Fin (N+1), MvPolynomial.C ((ε : ℂ)^(j : ℕ)) * q j)).coeff d) := by
  simp only [MvPolynomial.coeff_sum, MvPolynomial.coeff_C_mul]
  fun_prop

private lemma noiseFamily_degree_bound {n N : ℕ}
    (q : Fin (N+1) → MvPolynomial (Fin n) ℂ) (ε : ℝ) (i : Fin n) :
    ((∑ j : Fin (N+1), MvPolynomial.C ((ε : ℂ)^(j : ℕ)) * q j)).degreeOf i ≤ Finset.univ.sup (fun k => (q k).totalDegree) := by
  apply (MvPolynomial.degreeOf_sum_le i _ _).trans
  apply Finset.sup_le
  intro k hk
  exact (MvPolynomial.degreeOf_C_mul_le (q k) i _).trans
    ((MvPolynomial.degreeOf_le_totalDegree _ _).trans (Finset.le_sup (f := fun k : Fin (N+1) => (q k).totalDegree) hk))

private lemma noiseFamily_integral_norm_bound {n N : ℕ} (m : ℝ) (v : ℝ≥0)
    (q : Fin (N+1) → MvPolynomial (Fin n) ℂ) (ε : ℝ) (hε : |ε| ≤ 1) :
    (∫ x, ‖(fun {n : ℕ} (p : MvPolynomial (Fin n) ℂ) (x : Fin n → ℝ) => MvPolynomial.eval (fun i => (x i : ℂ)) p) ((∑ j : Fin (N+1), MvPolynomial.C ((ε : ℂ)^(j : ℕ)) * q j)) x‖ ∂(fun n m v => Measure.pi (fun _ : Fin n => gaussianReal m v)) n m v) ≤
      ∑ k, ∫ x, ‖(fun {n : ℕ} (p : MvPolynomial (Fin n) ℂ) (x : Fin n → ℝ) => MvPolynomial.eval (fun i => (x i : ℂ)) p) (q k) x‖ ∂(fun n m v => Measure.pi (fun _ : Fin n => gaussianReal m v)) n m v := by
  have hi (k : Fin (N+1)) := (D5.S3.Analytic.Probability.SampleCovarianceSpectralAndSmooth.Gaussian.gaussian_mv_eval_integrable m v (q k)).norm
  rw [← integral_finsetSum _ (fun k _ => hi k)]
  apply integral_mono (D5.S3.Analytic.Probability.SampleCovarianceSpectralAndSmooth.Gaussian.gaussian_mv_eval_integrable m v _).norm
    (integrable_finsetSum _ (fun k _ => hi k))
  intro x
  change ‖(fun {n : ℕ} (p : MvPolynomial (Fin n) ℂ) (x : Fin n → ℝ) => MvPolynomial.eval (fun i => (x i : ℂ)) p) ((∑ j : Fin (N+1), MvPolynomial.C ((ε : ℂ)^(j : ℕ)) * q j)) x‖ ≤ ∑ k : Fin (N+1), ‖(fun {n : ℕ} (p : MvPolynomial (Fin n) ℂ) (x : Fin n → ℝ) => MvPolynomial.eval (fun i => (x i : ℂ)) p) (q k) x‖
  rw [noiseFamily_eval]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro k hk
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ (abs_nonneg ε) hε)

private lemma gaussian_noiseFamily_uniform_log {n N : ℕ} (m : ℝ) (v : ℝ≥0) (hv : v ≠ 0)
    (q : Fin (N+1) → MvPolynomial (Fin n) ℂ) (d : Fin n →₀ ℕ)
    (hd : (q 0).coeff d ≠ 0) :
    ∃ δ C : ℝ, 0 < δ ∧ 0 ≤ C ∧ ∀ ε : ℝ, |ε| < δ →
      Integrable (fun x => Real.log ‖(fun {n : ℕ} (p : MvPolynomial (Fin n) ℂ) (x : Fin n → ℝ) => MvPolynomial.eval (fun i => (x i : ℂ)) p) ((∑ j : Fin (N+1), MvPolynomial.C ((ε : ℂ)^(j : ℕ)) * q j)) x‖) ((fun n m v => Measure.pi (fun _ : Fin n => gaussianReal m v)) n m v) ∧
      (∫ x, |Real.log ‖(fun {n : ℕ} (p : MvPolynomial (Fin n) ℂ) (x : Fin n → ℝ) => MvPolynomial.eval (fun i => (x i : ℂ)) p) ((∑ j : Fin (N+1), MvPolynomial.C ((ε : ℂ)^(j : ℕ)) * q j)) x‖| ∂(fun n m v => Measure.pi (fun _ : Fin n => gaussianReal m v)) n m v) ≤ C := by
  let c : ℝ := ‖(q 0).coeff d‖ / 2
  have hc : 0 < c := by dsimp [c]; exact half_pos (norm_pos_iff.mpr hd)
  have ht : Tendsto (fun ε : ℝ => ‖((∑ j : Fin (N+1), MvPolynomial.C ((ε : ℂ)^(j : ℕ)) * q j)).coeff d‖)
      (𝓝 0) (𝓝 ‖(q 0).coeff d‖) := by
    simpa only [Complex.ofReal_zero, noiseFamily_zero] using (noiseFamily_coeff_continuous q d).norm.tendsto 0
  have hev : ∀ᶠ ε : ℝ in 𝓝 0, c < ‖((∑ j : Fin (N+1), MvPolynomial.C ((ε : ℂ)^(j : ℕ)) * q j)).coeff d‖ :=
    ht.eventually (eventually_gt_nhds (by dsimp [c]; linarith [norm_pos_iff.mpr hd]))
  obtain ⟨δ, hδ, hδbound⟩ := Metric.eventually_nhds_iff.mp hev
  let D := Finset.univ.sup (fun k => (q k).totalDegree)
  let M := ∑ k, ∫ x, ‖(fun {n : ℕ} (p : MvPolynomial (Fin n) ℂ) (x : Fin n → ℝ) => MvPolynomial.eval (fun i => (x i : ℂ)) p) (q k) x‖ ∂(fun n m v => Measure.pi (fun _ : Fin n => gaussianReal m v)) n m v
  let C := max (2*M - Real.log c + (n : ℝ)*D*(Real.log 2 + D5.S3.Analytic.Probability.GaussianPolynomialLog.rootLogCost m v)) 0
  refine ⟨min δ 1, C, lt_min hδ (by norm_num), le_max_right _ _, ?_⟩
  intro ε hε
  have hε1 : |ε| ≤ 1 := (hε.trans_le (min_le_right _ _)).le
  have hcoeff : c ≤ ‖((∑ j : Fin (N+1), MvPolynomial.C ((ε : ℂ)^(j : ℕ)) * q j)).coeff d‖ :=
    (hδbound (by simpa [Real.dist_eq] using hε.trans_le (min_le_left _ _))).le
  obtain ⟨hi, hb⟩ := gaussian_mv_uniform_abs_log_bound m v hv n D
    ((∑ j : Fin (N+1), MvPolynomial.C ((ε : ℂ)^(j : ℕ)) * q j)) d c M hc hcoeff (noiseFamily_degree_bound q ε)
    (noiseFamily_integral_norm_bound m v q ε hε1)
  exact ⟨hi, hb.trans (le_max_left _ _)⟩

end
end D5.S3.Analytic.Probability.SampleCovarianceBernoulliOrders.Gaussian

namespace D5.S3.Analytic.Probability.SampleCovarianceBernoulliOrders.Gaussian
noncomputable section

lemma gaussian_mv_log_integrable (m : ℝ) (v : ℝ≥0) (hv : v ≠ 0) {n : ℕ}
    (p : MvPolynomial (Fin n) ℂ) (hp : p ≠ 0) :
    (∀ᵐ x ∂(fun n m v => Measure.pi (fun _ : Fin n => gaussianReal m v)) n m v, (fun {n : ℕ} (p : MvPolynomial (Fin n) ℂ) (x : Fin n → ℝ) => MvPolynomial.eval (fun i => (x i : ℂ)) p) p x ≠ 0) ∧
    Integrable (fun x => Real.log ‖(fun {n : ℕ} (p : MvPolynomial (Fin n) ℂ) (x : Fin n → ℝ) => MvPolynomial.eval (fun i => (x i : ℂ)) p) p x‖) ((fun n m v => Measure.pi (fun _ : Fin n => gaussianReal m v)) n m v) := by
  obtain ⟨d, hd⟩ := MvPolynomial.exists_coeff_ne_zero hp
  obtain ⟨hae, hi, _⟩ := D5.S3.Analytic.Probability.SampleCovarianceSpectralAndSmooth.Gaussian.gaussian_mv_log_coeff_lower m v hv n p d p.totalDegree hd
    (fun i => MvPolynomial.degreeOf_le_totalDegree p i)
  exact ⟨hae, hi⟩

private lemma gaussian_mv_log_scalar (m : ℝ) (v : ℝ≥0) (hv : v ≠ 0) {n : ℕ}
    (p : MvPolynomial (Fin n) ℂ) (hp : p ≠ 0) (c : ℂ) (hc : c ≠ 0) :
    (∫ x, Real.log ‖c * (fun {n : ℕ} (p : MvPolynomial (Fin n) ℂ) (x : Fin n → ℝ) => MvPolynomial.eval (fun i => (x i : ℂ)) p) p x‖ ∂(fun n m v => Measure.pi (fun _ : Fin n => gaussianReal m v)) n m v) =
      Real.log ‖c‖ + ∫ x, Real.log ‖(fun {n : ℕ} (p : MvPolynomial (Fin n) ℂ) (x : Fin n → ℝ) => MvPolynomial.eval (fun i => (x i : ℂ)) p) p x‖ ∂(fun n m v => Measure.pi (fun _ : Fin n => gaussianReal m v)) n m v := by
  have hi := gaussian_mv_log_integrable m v hv p hp
  have heq : (fun x => Real.log ‖c * (fun {n : ℕ} (p : MvPolynomial (Fin n) ℂ) (x : Fin n → ℝ) => MvPolynomial.eval (fun i => (x i : ℂ)) p) p x‖) =ᵐ[(fun n m v => Measure.pi (fun _ : Fin n => gaussianReal m v)) n m v]
      (fun x => Real.log ‖c‖ + Real.log ‖(fun {n : ℕ} (p : MvPolynomial (Fin n) ℂ) (x : Fin n → ℝ) => MvPolynomial.eval (fun i => (x i : ℂ)) p) p x‖) := by
    filter_upwards [hi.1] with x hx
    rw [norm_mul, Real.log_mul (norm_ne_zero_iff.mpr hc) (norm_ne_zero_iff.mpr hx)]
  rw [integral_congr_ae heq, integral_add (integrable_const _) hi.2, integral_const]
  simp only [probReal_univ, one_smul]

private lemma gaussian_noiseFamily_log_remainder_tendsto {n N : ℕ} (m : ℝ) (v : ℝ≥0) (hv : v ≠ 0)
    (q : Fin (N+1) → MvPolynomial (Fin n) ℂ) (d : Fin n →₀ ℕ)
    (hd : (q 0).coeff d ≠ 0) :
    Tendsto (fun ε : ℝ => (∫ x, Real.log ‖(fun {n : ℕ} (p : MvPolynomial (Fin n) ℂ) (x : Fin n → ℝ) => MvPolynomial.eval (fun i => (x i : ℂ)) p) ((∑ j : Fin (N+1), MvPolynomial.C ((ε : ℂ)^(j : ℕ)) * q j)) x‖ ∂(fun n m v => Measure.pi (fun _ : Fin n => gaussianReal m v)) n m v) /
      Real.log (1/ε)) (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨δ, C, hδ, hC, hb⟩ := gaussian_noiseFamily_uniform_log m v hv q d hd
  have hsmall : ∀ᶠ ε : ℝ in 𝓝[>] 0, |ε| < δ := by
    apply Filter.Eventually.filter_mono nhdsWithin_le_nhds
    exact (isOpen_lt continuous_abs continuous_const).mem_nhds (by simpa using hδ)
  have hbound : ∀ᶠ ε : ℝ in 𝓝[>] 0,
      |∫ x, Real.log ‖(fun {n : ℕ} (p : MvPolynomial (Fin n) ℂ) (x : Fin n → ℝ) => MvPolynomial.eval (fun i => (x i : ℂ)) p) ((∑ j : Fin (N+1), MvPolynomial.C ((ε : ℂ)^(j : ℕ)) * q j)) x‖ ∂(fun n m v => Measure.pi (fun _ : Fin n => gaussianReal m v)) n m v| ≤ C := by
    filter_upwards [hsmall] with ε hε
    have hi := hb ε hε
    have hh : |∫ x, Real.log ‖(fun {n : ℕ} (p : MvPolynomial (Fin n) ℂ) (x : Fin n → ℝ) => MvPolynomial.eval (fun i => (x i : ℂ)) p) ((∑ j : Fin (N+1), MvPolynomial.C ((ε : ℂ)^(j : ℕ)) * q j)) x‖ ∂(fun n m v => Measure.pi (fun _ : Fin n => gaussianReal m v)) n m v| ≤
        ∫ x, |Real.log ‖(fun {n : ℕ} (p : MvPolynomial (Fin n) ℂ) (x : Fin n → ℝ) => MvPolynomial.eval (fun i => (x i : ℂ)) p) ((∑ j : Fin (N+1), MvPolynomial.C ((ε : ℂ)^(j : ℕ)) * q j)) x‖| ∂(fun n m v => Measure.pi (fun _ : Fin n => gaussianReal m v)) n m v := by
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm
        (fun x => Real.log ‖(fun {n : ℕ} (p : MvPolynomial (Fin n) ℂ) (x : Fin n → ℝ) => MvPolynomial.eval (fun i => (x i : ℂ)) p) ((∑ j : Fin (N+1), MvPolynomial.C ((ε : ℂ)^(j : ℕ)) * q j)) x‖)
    exact hh.trans hi.2
  have hden : Tendsto (fun ε : ℝ => Real.log (1/ε)) (𝓝[>] 0) atTop := by
    simpa only [one_div, Real.log_inv, Function.comp_def] using tendsto_neg_atBot_atTop.comp Real.tendsto_log_nhdsGT_zero
  exact tendsto_bdd_div_atTop_nhds_zero
    (hbound.mono (fun ε h => (abs_le.mp h).1))
    (hbound.mono (fun ε h => (abs_le.mp h).2)) hden

lemma gaussian_noiseFamily_log_order {n N : ℕ} (m : ℝ) (v : ℝ≥0) (hv : v ≠ 0)
    (q : Fin (N+1) → MvPolynomial (Fin n) ℂ) (d : Fin n →₀ ℕ)
    (hd : (q 0).coeff d ≠ 0) (k : ℕ) :
    Tendsto (fun ε : ℝ => -(∫ x, Real.log ‖(ε : ℂ)^k * (fun {n : ℕ} (p : MvPolynomial (Fin n) ℂ) (x : Fin n → ℝ) => MvPolynomial.eval (fun i => (x i : ℂ)) p) ((∑ j : Fin (N+1), MvPolynomial.C ((ε : ℂ)^(j : ℕ)) * q j)) x‖
      ∂(fun n m v => Measure.pi (fun _ : Fin n => gaussianReal m v)) n m v) / Real.log (1/ε)) (𝓝[>] 0) (𝓝 (k : ℝ)) := by
  have hrem := gaussian_noiseFamily_log_remainder_tendsto m v hv q d hd
  have ht : Tendsto (fun ε : ℝ => ‖((∑ j : Fin (N+1), MvPolynomial.C ((ε : ℂ)^(j : ℕ)) * q j)).coeff d‖)
      (𝓝 0) (𝓝 ‖(q 0).coeff d‖) := by
    simpa only [Complex.ofReal_zero, noiseFamily_zero] using (noiseFamily_coeff_continuous q d).norm.tendsto 0
  have hne : ∀ᶠ ε : ℝ in 𝓝[>] 0, (∑ j : Fin (N+1), MvPolynomial.C ((ε : ℂ)^(j : ℕ)) * q j) ≠ 0 := by
    have hh := ht.eventually (eventually_gt_nhds (norm_pos_iff.mpr hd))
    apply Filter.Eventually.filter_mono nhdsWithin_le_nhds
    filter_upwards [hh] with ε hε
    exact MvPolynomial.ne_zero_iff.mpr ⟨d, norm_pos_iff.mp hε⟩
  have hden : Tendsto (fun ε : ℝ => Real.log (1/ε)) (𝓝[>] 0) atTop := by
    simpa only [one_div, Real.log_inv, Function.comp_def] using tendsto_neg_atBot_atTop.comp Real.tendsto_log_nhdsGT_zero
  have heq : (fun ε : ℝ => -(∫ x, Real.log ‖(ε : ℂ)^k * (fun {n : ℕ} (p : MvPolynomial (Fin n) ℂ) (x : Fin n → ℝ) => MvPolynomial.eval (fun i => (x i : ℂ)) p) ((∑ j : Fin (N+1), MvPolynomial.C ((ε : ℂ)^(j : ℕ)) * q j)) x‖
        ∂(fun n m v => Measure.pi (fun _ : Fin n => gaussianReal m v)) n m v) / Real.log (1/ε)) =ᶠ[𝓝[>] 0]
      (fun ε => (k : ℝ) - (∫ x, Real.log ‖(fun {n : ℕ} (p : MvPolynomial (Fin n) ℂ) (x : Fin n → ℝ) => MvPolynomial.eval (fun i => (x i : ℂ)) p) ((∑ j : Fin (N+1), MvPolynomial.C ((ε : ℂ)^(j : ℕ)) * q j)) x‖
        ∂(fun n m v => Measure.pi (fun _ : Fin n => gaussianReal m v)) n m v) / Real.log (1/ε)) := by
    filter_upwards [hne, self_mem_nhdsWithin, hden.eventually (eventually_gt_atTop 0)]
      with ε hε hεpos hdenpos
    have hεne : (ε : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hεpos)
    rw [gaussian_mv_log_scalar m v hv _ hε _ (pow_ne_zero _ hεne), norm_pow,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hεpos, Real.log_pow]
    have hlog : Real.log ε = -Real.log (1/ε) := by simp
    rw [hlog]
    field_simp
    ring
  apply (tendsto_congr' heq).mpr
  simpa using (tendsto_const_nhds.sub hrem)

end
end D5.S3.Analytic.Probability.SampleCovarianceBernoulliOrders.Gaussian

namespace D5.S3.Analytic.Probability.SampleCovarianceBernoulliOrders.Gaussian
noncomputable section

end
end D5.S3.Analytic.Probability.SampleCovarianceBernoulliOrders.Gaussian
