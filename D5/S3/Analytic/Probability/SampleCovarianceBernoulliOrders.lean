/- GID: D5/S3/Analytic/Probability/SampleCovarianceBernoulliOrders
   generality: I
   mirror-B: D5/B/S3/Analytic/Probability/SampleCovarianceBernoulliOrders
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Bernoulli matrix determinant orders. -/
/-
proof_shape: pending per-declaration verification.
escape_witness: none claimed before the upstream-only tests.
admission_basis: pending escape-witness verification
Direct frozen dependencies: pending compiled-constant extraction.
-/
import D5.S3.Analytic.Probability.GaussianPolynomialLog
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Tactic.Linarith
import Mathlib.LinearAlgebra.Matrix.Polynomial
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Degree.TrailingDegree
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Data.EReal.Operations
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Data.EReal.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.MeasureTheory.Measure.Dirac.Basic
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.Star.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.NoncommRing
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Abel

set_option maxHeartbeats 2500000
set_option linter.unusedSimpArgs false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Matrix Polynomial
open scoped BigOperators Kronecker
namespace D5.S3.Analytic.Probability.SampleCovarianceBernoulliOrders.Noise
noncomputable section
instance coeffStar (n : ℕ) : Star ((MvPolynomial (Bool × Bool × Fin n × Fin n) ℂ)) := ⟨MvPolynomial.map (starRingEnd ℂ)⟩
instance coeffStarRing (n : ℕ) : StarRing ((MvPolynomial (Bool × Bool × Fin n × Fin n) ℂ)) where
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
    evalNoise G K (MvPolynomial.C z) = z := by simp [evalNoise]
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
  have hn : (s+1 : ℝ) ≠ 0 := by positivity
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
    rw [orthonormal_iff_ite]
    intro i j
    have hij : i = j := Subtype.ext (by simpa using i.property.trans j.property.symm)
    simp [hij, inner_self_eq_norm_sq_to_K, hv]
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
      (Matrix.of (fun _ _ => c)) = U * D5.S3.Analytic.Probability.GaussianPolynomialLog.Covariance.rankOneBase ((s+1 : ℕ)*c) * Uᴴ := by
  obtain ⟨U,hU,hU',hcol⟩ := exists_unitary_common s
  refine ⟨U,hU,hU',?_⟩
  apply Matrix.ext
  intro i j
  have he (a : ℂ) : (U * D5.S3.Analytic.Probability.GaussianPolynomialLog.Covariance.rankOneBase (s:=s) a * Uᴴ) i j =
      U i 0 * a * star (U j 0) := by
    simp only [D5.S3.Analytic.Probability.GaussianPolynomialLog.Covariance.rankOneBase, Matrix.mul_apply, Matrix.diagonal_apply,
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
namespace D5.S3.Analytic.Probability.SampleCovarianceBernoulliOrders.Scalar
noncomputable section
variable {R : Type*} [CommRing R] [StarRing R] {n : ℕ}
private lemma cross_smul (a : R) (A G : Matrix (Fin n) (Fin n) R) :
    (a • A)*(a • G)ᴴ = (a*star a) • (A*Gᴴ) := by
  simp only [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_comm (star a) a]
private lemma affineGram_smul (a : R) (A G : Matrix (Fin n) (Fin n) R) :
    D5.S3.Analytic.Probability.GaussianPolynomialLog.Covariance.affineGramPoly (a • A) (a • G) =
      Polynomial.C (a*star a) • D5.S3.Analytic.Probability.GaussianPolynomialLog.Covariance.affineGramPoly A G := by
  unfold D5.S3.Analytic.Probability.GaussianPolynomialLog.Covariance.affineGramPoly
  simp only [cross_smul, ← smul_add]
  apply Matrix.ext
  intro i j
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, map_mul]
  ring
private lemma pairDet_smul (a : R) (A C G K : Matrix (Fin n) (Fin n) R) :
    D5.S3.Analytic.Probability.GaussianPolynomialLog.Covariance.pairDet (a • A) (a • C) (a • G) (a • K) =
      Polynomial.C (a*star a)^(n*n) * D5.S3.Analytic.Probability.GaussianPolynomialLog.Covariance.pairDet A C G K := by
  unfold D5.S3.Analytic.Probability.GaussianPolynomialLog.Covariance.pairDet
  rw [affineGram_smul, affineGram_smul, Matrix.smul_kronecker, Matrix.kronecker_smul,
    ← smul_sub, Matrix.det_smul]
  simp [Fintype.card_prod]
private lemma rankOneBase_smul {s : ℕ} (a : R) :
    (D5.S3.Analytic.Probability.GaussianPolynomialLog.Covariance.rankOneBase a : Matrix (Fin (s+1)) (Fin (s+1)) R) =
      a • D5.S3.Analytic.Probability.GaussianPolynomialLog.Covariance.rankOneBase 1 := by
  apply Matrix.ext
  intro i j
  by_cases hi : i=0 <;> by_cases hj : j=0 <;> by_cases hij : i=j <;>
    simp [D5.S3.Analytic.Probability.GaussianPolynomialLog.Covariance.rankOneBase, Matrix.diagonal_apply, hi,hj,hij]
end
end D5.S3.Analytic.Probability.SampleCovarianceBernoulliOrders.Scalar
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
    (D5.S3.Analytic.Probability.GaussianPolynomialLog.Covariance.rankOneBase (s:=s) ((s+1:ℕ)*c)) (D5.S3.Analytic.Probability.GaussianPolynomialLog.Covariance.rankOneBase (s:=s) ((s+1:ℕ)*c))
    (Uᴴ*G*U) (Uᴴ*K*U) hu' (by simpa using hu)
  rw [← hc, hinv, hinv] at he
  rw [he]
  exact D5.S3.Analytic.Probability.GaussianPolynomialLog.Covariance.rankOne_order_lower _ _ _
private lemma pairDet_common_witness (s : ℕ) (c : ℂ) :
    D5.S3.Analytic.Probability.GaussianPolynomialLog.Covariance.pairDet (Matrix.of (fun _ _ : Fin (s+1) => c)) (Matrix.of (fun _ _ => c)) 1 0 =
      D5.S3.Analytic.Probability.GaussianPolynomialLog.Covariance.pairDet (D5.S3.Analytic.Probability.GaussianPolynomialLog.Covariance.rankOneBase (s:=s) ((s+1:ℕ)*c))
        (D5.S3.Analytic.Probability.GaussianPolynomialLog.Covariance.rankOneBase (s:=s) ((s+1:ℕ)*c)) 1 0 := by
  obtain ⟨U,hu,hu',hc⟩ := D5.S3.Analytic.Probability.SampleCovarianceBernoulliOrders.Basis.common_eq_unitary_rankOne s c
  have he := D5.S3.Analytic.Probability.SampleCovarianceBernoulliOrders.Unitary.pairDet_unitary U Uᴴ
    (D5.S3.Analytic.Probability.GaussianPolynomialLog.Covariance.rankOneBase (s:=s) ((s+1:ℕ)*c)) (D5.S3.Analytic.Probability.GaussianPolynomialLog.Covariance.rankOneBase (s:=s) ((s+1:ℕ)*c)) 1 0 hu'
    (by simpa using hu)
  simpa only [← hc, Matrix.mul_one, hu', Matrix.mul_zero, Matrix.zero_mul] using he
private lemma diagonal_witness_order (s : ℕ) (a : ℝ) (ha : a ≠ 0) :
    (D5.S3.Analytic.Probability.GaussianPolynomialLog.Covariance.pairDet (D5.S3.Analytic.Probability.GaussianPolynomialLog.Covariance.rankOneBase (a : ℂ))
      (D5.S3.Analytic.Probability.GaussianPolynomialLog.Covariance.rankOneBase (a : ℂ)) (1 : Matrix (Fin (s+1)) (Fin (s+1)) ℂ) 0).natTrailingDegree =
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
def w {n : ℕ} (b : ((Bool × Fin n × Fin n) → Bool)) : ℝ := ∏ i, if b i then (1/256 : ℝ) else 255/256
def bmat {n : ℕ} (b : ((Bool × Fin n × Fin n) → Bool)) (side : Bool) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of (fun i j => if b (side,i,j) then (Real.sqrt 255 : ℂ) else (-1/Real.sqrt 255 : ℝ))
def k {n : ℕ} (b : ((Bool × Fin n × Fin n) → Bool)) : ℕ := (poly (bmat b false) (bmat b true)).natTrailingDegree
def L (n : ℕ) : ℝ := (∑ b : ((Bool × Fin n × Fin n) → Bool), w b * k b) / (n:ℝ)^2
private lemma w_nonneg {n : ℕ} (b : ((Bool × Fin n × Fin n) → Bool)) : 0 ≤ w b := by
  apply Finset.prod_nonneg
  intro i hi
  split <;> norm_num
lemma w_sum (n : ℕ) : ∑ b : ((Bool × Fin n × Fin n) → Bool), w b = 1 := by
  unfold w
  have he := Fintype.prod_sum (fun (_ : (Bool × Fin n × Fin n)) (b : Bool) =>
    if b then (1/256 : ℝ) else 255/256)
  calc
    _ = ∏ i : (Bool × Fin n × Fin n), ∑ b : Bool, if b then (1/256 : ℝ) else 255/256 := he.symm
    _ = 1 := by norm_num [Fintype.sum_bool]
private lemma w_common (n : ℕ) : w (fun _ : (Bool × Fin n × Fin n) => false) = (255/256 : ℝ)^(2*n*n) := by
  simp only [w, Bool.false_eq_true, ite_false, Finset.prod_const, Finset.card_univ,
    Fintype.card_prod, Fintype.card_bool, Fintype.card_fin]
  congr 1
  ring
private lemma k_le {n : ℕ} (b : ((Bool × Fin n × Fin n) → Bool)) : k b ≤ 2*n*n := poly_order_le _ _
private lemma k_common (s : ℕ) : k (fun _ : (Bool × Fin (s+1) × Fin (s+1)) => false) = 2*s*s+1 := by
  have hc : (-1/Real.sqrt 255 : ℝ) ≠ 0 := by
    apply div_ne_zero (by norm_num)
    exact Real.sqrt_ne_zero'.mpr (by norm_num)
  exact D5.S3.Analytic.Probability.SampleCovarianceBernoulliOrders.CommonOrder.poly_common_order s (-1/Real.sqrt 255) hc
private lemma L_bounds : L 2 ≤ 2-(5/4:ℝ)*(255/256:ℝ)^8 ∧ (255/256:ℝ)^18 ≤ L 3 := by
  have hu := D5.S3.Analytic.Probability.SampleCovarianceBernoulliOrders.FiniteBounds.weighted_order_upper (w (n:=2)) (fun b => (k b : ℝ))
    (fun _ => false) 3 8 w_nonneg (w_sum 2)
    (fun b => by exact_mod_cast k_le b) (by exact_mod_cast k_common 1)
  have hl := D5.S3.Analytic.Probability.SampleCovarianceBernoulliOrders.FiniteBounds.weighted_order_lower (w (n:=3)) (fun b => (k b : ℝ))
    (fun _ => false) 9 w_nonneg (fun b => Nat.cast_nonneg _)
    (by exact_mod_cast (k_common 2).ge)
  rw [w_common] at hu hl
  constructor
  · unfold L
    norm_num only [Nat.cast_ofNat, OfNat.ofNat, pow_two]
    change (∑ b : ((Bool × Fin 2 × Fin 2) → Bool), w b * (k b : ℝ)) ≤ 8 - (8-3)*(255/256:ℝ)^8 at hu
    nlinarith
  · unfold L
    norm_num only [Nat.cast_ofNat, OfNat.ofNat, pow_two]
    change 9*(255/256:ℝ)^18 ≤ (∑ b : ((Bool × Fin 3 × Fin 3) → Bool), w b * (k b : ℝ)) at hl
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
namespace D5.S3.Analytic.Probability.SampleCovarianceBernoulliOrders.Gaussian
noncomputable section

def gaussianPi (n : ℕ) (m : ℝ) (v : ℝ≥0) : Measure (Fin n → ℝ) :=
  Measure.pi (fun _ => gaussianReal m v)

instance gaussianPi_probability (n : ℕ) (m : ℝ) (v : ℝ≥0) :
    IsProbabilityMeasure (gaussianPi n m v) := by
  unfold gaussianPi
  infer_instance

def realEval {n : ℕ} (p : MvPolynomial (Fin n) ℂ) (x : Fin n → ℝ) : ℂ :=
  MvPolynomial.eval (fun i => (x i : ℂ)) p

private lemma realEval_continuous {n : ℕ} (p : MvPolynomial (Fin n) ℂ) :
    Continuous (realEval p) := by
  unfold realEval
  exact p.continuous_eval.comp (continuous_pi (fun i =>
    Complex.continuous_ofReal.comp (continuous_apply i)))

private lemma gaussian_mv_eval_integrable {n : ℕ} (m : ℝ) (v : ℝ≥0)
    (p : MvPolynomial (Fin n) ℂ) :
    Integrable (realEval p) (gaussianPi n m v) := by
  unfold realEval gaussianPi
  simp_rw [MvPolynomial.eval_eq']
  apply integrable_finsetSum
  intro d hd
  exact (Integrable.fintype_prod (fun i => D5.S3.Analytic.Probability.GaussianPolynomialLog.gaussian_complex_pow_integrable m v (d i))).const_mul _

private lemma gaussian_polynomial_ae_nonzero (m : ℝ) (v : ℝ≥0) (hv : v ≠ 0)
    (p : Polynomial ℂ) (hp : p ≠ 0) :
    ∀ᵐ x : ℝ ∂gaussianReal m v, p.eval (x : ℂ) ≠ 0 := by
  filter_upwards [D5.S3.Analytic.Probability.GaussianPolynomialLog.gaussian_roots_nonzero m v hv p.roots] with x hx
  rw [(IsAlgClosed.splits p).eval_eq_prod_roots (x : ℂ)]
  exact mul_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr hp) hx

private lemma realConsEquiv_apply (n : ℕ) (z : ℝ × (Fin n → ℝ)) :
    ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ) 0).symm) z = Fin.cons z.1 z.2 := by
  simp [ MeasurableEquiv.piFinSuccAbove_symm_apply,
    Fin.insertNthEquiv, Fin.insertNth_zero]

private lemma realConsEquiv_preserving (n : ℕ) (m : ℝ) (v : ℝ≥0) :
    MeasurePreserving (((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ) 0).symm))
      ((gaussianReal m v).prod (gaussianPi n m v)) (gaussianPi (n+1) m v) := by
  simpa only [ gaussianPi, Fin.zero_succAbove] using
    (measurePreserving_piFinSuccAbove (fun _ : Fin (n+1) => gaussianReal m v) 0).symm

private lemma realEval_cons {n : ℕ} (p : MvPolynomial (Fin (n+1)) ℂ)
    (x : ℝ) (y : Fin n → ℝ) :
    realEval p (Fin.cons x y) =
      ((MvPolynomial.finSuccEquiv ℂ n p).map
        (MvPolynomial.eval (fun i => (y i : ℂ)))).eval (x : ℂ) := by
  unfold realEval
  convert MvPolynomial.eval_eq_eval_mv_eval' (fun i => (y i : ℂ)) (x : ℂ) p using 1
  congr 2
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp

private lemma posLog_le_norm (z : ℂ) : max (Real.log ‖z‖) 0 ≤ ‖z‖ := by
  apply max_le _ (norm_nonneg _)
  by_cases hz : z = 0
  · simp [hz]
  · have h := Real.log_le_sub_one_of_pos (norm_pos_iff.mpr hz)
    linarith

private lemma gaussian_mv_log_coeff_lower (m : ℝ) (v : ℝ≥0) (hv : v ≠ 0) (n : ℕ)
    (p : MvPolynomial (Fin n) ℂ) (d : Fin n →₀ ℕ) (D : ℕ)
    (hd : p.coeff d ≠ 0) (hD : ∀ i, p.degreeOf i ≤ D) :
    (∀ᵐ x ∂gaussianPi n m v, realEval p x ≠ 0) ∧
    Integrable (fun x => Real.log ‖realEval p x‖) (gaussianPi n m v) ∧
    Real.log ‖p.coeff d‖ - (n : ℝ)*D*(Real.log 2 + D5.S3.Analytic.Probability.GaussianPolynomialLog.rootLogCost m v) ≤
      ∫ x, Real.log ‖realEval p x‖ ∂gaussianPi n m v := by
  induction n with
  | zero =>
    have hd0 : d = 0 := Subsingleton.elim _ _
    subst d
    have hpe : p = MvPolynomial.C (p.coeff 0) := p.eq_C_of_isEmpty
    have hev (x : Fin 0 → ℝ) : realEval p x = p.coeff 0 := by
      conv_lhs => rw [hpe]
      simp [realEval]
    simp only [hev]
    exact ⟨Filter.Eventually.of_forall (fun _ => hd), integrable_const _, by simp⟩
  | succ n ih =>
    let P := MvPolynomial.finSuccEquiv ℂ n p
    let q := P.coeff (d 0)
    have hqcoeff : q.coeff d.tail = p.coeff d := by
      dsimp only [q, P]
      rw [MvPolynomial.finSuccEquiv_coeff_coeff, Finsupp.cons_tail]
    have hqD : ∀ i, q.degreeOf i ≤ D := fun i =>
      (MvPolynomial.degreeOf_coeff_finSuccEquiv p i (d 0)).trans (hD i.succ)
    obtain ⟨hqae, hqi, hql⟩ := ih q d.tail (by rwa [hqcoeff]) hqD
    let e := ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ) 0).symm)
    have he := realConsEquiv_preserving n m v
    let f : ℝ × (Fin n → ℝ) → ℝ := fun z => Real.log ‖realEval p (e z)‖
    have hfmeas : AEStronglyMeasurable f
        ((gaussianReal m v).prod (gaussianPi n m v)) := by
      exact ((Real.measurable_log.comp ((realEval_continuous p).measurable.comp
        e.measurable).norm)).aestronglyMeasurable
    have hfiPos : Integrable (fun z => max (f z) 0)
        ((gaussianReal m v).prod (gaussianPi n m v)) := by
      have hint := he.integrable_comp_emb e.measurableEmbedding |>.mpr
        (gaussian_mv_eval_integrable m v p).norm
      apply hint.mono' (hfmeas.sup aestronglyMeasurable_const)
      filter_upwards [] with z
      rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
      exact posLog_le_norm _
    let py (y : Fin n → ℝ) := P.map (MvPolynomial.eval (fun i => (y i : ℂ)))
    have hcoeff (y : Fin n → ℝ) : (py y).coeff (d 0) = realEval q y := by
      simp only [py, Polynomial.coeff_map, realEval, q]
    have heval (x : ℝ) (y : Fin n → ℝ) :
        f (x,y) = Real.log ‖(py y).eval (x : ℂ)‖ := by
      dsimp only [f, e]
      rw [realConsEquiv_apply, realEval_cons]
    have hnonzero : ∀ᵐ y ∂gaussianPi n m v, py y ≠ 0 := by
      filter_upwards [hqae] with y hy
      intro hz
      have hc := hcoeff y
      rw [hz, Polynomial.coeff_zero] at hc
      exact hy hc.symm
    have hsections : ∀ᵐ y ∂gaussianPi n m v,
        Integrable (fun x => f (x,y)) (gaussianReal m v) := by
      filter_upwards [hnonzero] with y hy
      simp_rw [heval]
      exact D5.S3.Analytic.Probability.GaussianPolynomialLog.gaussian_polynomial_log_integrable m v hv (py y) hy
    have hcost : 0 ≤ Real.log 2 + D5.S3.Analytic.Probability.GaussianPolynomialLog.rootLogCost m v :=
      add_nonneg (Real.log_nonneg (by norm_num)) (D5.S3.Analytic.Probability.GaussianPolynomialLog.rootLogCost_nonneg m v)
    have hdegrees (y : Fin n → ℝ) : (py y).natDegree ≤ D := by
      apply Polynomial.natDegree_map_le.trans
      rw [MvPolynomial.natDegree_finSuccEquiv]
      exact hD 0
    let g : (Fin n → ℝ) → ℝ := fun y => Real.log ‖realEval q y‖ - D*(Real.log 2 + D5.S3.Analytic.Probability.GaussianPolynomialLog.rootLogCost m v)
    have hgi : Integrable g (gaussianPi n m v) := hqi.sub (integrable_const _)
    have hlower : ∀ᵐ y ∂gaussianPi n m v,
        g y ≤ ∫ x, f (x,y) ∂gaussianReal m v := by
      filter_upwards [hqae] with y hy
      have hc : (py y).coeff (d 0) ≠ 0 := by rwa [hcoeff]
      have hh := D5.S3.Analytic.Probability.GaussianPolynomialLog.gaussian_polynomial_log_coeff_lower m v hv (py y) (d 0) hc
      rw [hcoeff] at hh
      simp_rw [heval]
      exact (sub_le_sub_left (mul_le_mul_of_nonneg_right (by exact_mod_cast hdegrees y) hcost) _).trans hh
    have hfi : Integrable f ((gaussianReal m v).prod (gaussianPi n m v)) :=
      D5.S3.Analytic.Probability.GaussianPolynomialLog.integrable_prod_of_pos_and_fiber_lower _ _ f hfmeas hfiPos hsections g hgi hlower
    have hpi : Integrable (fun x => Real.log ‖realEval p x‖) (gaussianPi (n+1) m v) :=
      (he.integrable_comp_emb e.measurableEmbedding).mp hfi
    have hpnonzero : ∀ᵐ z ∂(gaussianReal m v).prod (gaussianPi n m v),
        realEval p (e z) ≠ 0 := by
      have hset : MeasurableSet {z : ℝ × (Fin n → ℝ) | realEval p (e z) ≠ 0} := by
        exact ((realEval_continuous p).measurable.comp e.measurable)
          (measurableSet_singleton 0).compl
      apply (Measure.ae_prod_iff_ae_ae hset).mpr
      apply (Measure.ae_ae_comm hset).mpr
      filter_upwards [hnonzero] with y hy
      have hh := gaussian_polynomial_ae_nonzero m v hv (py y) hy
      simpa only [e, realConsEquiv_apply, realEval_cons, py, P] using hh
    refine ⟨?_, hpi, ?_⟩
    · rw [← he.map_eq, ← e.map_ae]
      exact hpnonzero
    · have hb := integral_mono_ae hgi hfi.integral_prod_right hlower
      have hei : (∫ x, Real.log ‖realEval p x‖ ∂gaussianPi (n+1) m v) =
          ∫ y, ∫ x, f (x,y) ∂gaussianReal m v ∂gaussianPi n m v := by
        rw [← he.integral_comp' (fun x => Real.log ‖realEval p x‖), integral_prod_symm _ hfi]
      rw [hei]
      have hgint : (∫ y, g y ∂gaussianPi n m v) =
          (∫ y, Real.log ‖realEval q y‖ ∂gaussianPi n m v) - D*(Real.log 2 + D5.S3.Analytic.Probability.GaussianPolynomialLog.rootLogCost m v) := by
        rw [integral_sub hqi (integrable_const _), integral_const]
        simp only [probReal_univ, one_smul]
      rw [hgint] at hb
      rw [hqcoeff] at hql
      push_cast
      nlinarith

end
end D5.S3.Analytic.Probability.SampleCovarianceBernoulliOrders.Gaussian

open MeasureTheory Filter Set ProbabilityTheory
open scoped ENNReal NNReal Topology BigOperators
namespace D5.S3.Analytic.Probability.SampleCovarianceBernoulliOrders.Gaussian
noncomputable section

private lemma gaussian_mv_abs_log_bound (m : ℝ) (v : ℝ≥0) (hv : v ≠ 0) (n : ℕ)
    (p : MvPolynomial (Fin n) ℂ) (d : Fin n →₀ ℕ) (D : ℕ)
    (hd : p.coeff d ≠ 0) (hD : ∀ i, p.degreeOf i ≤ D) :
    (∫ x, |Real.log ‖realEval p x‖| ∂gaussianPi n m v) ≤
      2*(∫ x, ‖realEval p x‖ ∂gaussianPi n m v) - Real.log ‖p.coeff d‖ +
        (n : ℝ)*D*(Real.log 2 + D5.S3.Analytic.Probability.GaussianPolynomialLog.rootLogCost m v) := by
  obtain ⟨_, hl, hc⟩ := gaussian_mv_log_coeff_lower m v hv n p d D hd hD
  have hn := (gaussian_mv_eval_integrable m v p).norm
  have hb : (∫ x, |Real.log ‖realEval p x‖| ∂gaussianPi n m v) ≤
      2*(∫ x, ‖realEval p x‖ ∂gaussianPi n m v) -
        ∫ x, Real.log ‖realEval p x‖ ∂gaussianPi n m v := by
    rw [← integral_const_mul, ← integral_sub (hn.const_mul 2) hl]
    apply integral_mono_ae hl.abs ((hn.const_mul 2).sub hl)
    filter_upwards [] with x
    rw [← Real.norm_eq_abs, D5.S3.Analytic.Probability.GaussianPolynomialLog.norm_eq_two_pos_sub]
    exact sub_le_sub_right (mul_le_mul_of_nonneg_left (posLog_le_norm _) (by norm_num)) _
  linarith

private lemma gaussian_mv_uniform_abs_log_bound (m : ℝ) (v : ℝ≥0) (hv : v ≠ 0) (n D : ℕ)
    (p : MvPolynomial (Fin n) ℂ) (d : Fin n →₀ ℕ) (c M : ℝ)
    (hc : 0 < c) (hcoeff : c ≤ ‖p.coeff d‖)
    (hD : ∀ i, p.degreeOf i ≤ D)
    (hM : (∫ x, ‖realEval p x‖ ∂gaussianPi n m v) ≤ M) :
    Integrable (fun x => Real.log ‖realEval p x‖) (gaussianPi n m v) ∧
    (∫ x, |Real.log ‖realEval p x‖| ∂gaussianPi n m v) ≤
      2*M - Real.log c + (n : ℝ)*D*(Real.log 2 + D5.S3.Analytic.Probability.GaussianPolynomialLog.rootLogCost m v) := by
  have hd : p.coeff d ≠ 0 := norm_pos_iff.mp (hc.trans_le hcoeff)
  refine ⟨(gaussian_mv_log_coeff_lower m v hv n p d D hd hD).2.1, ?_⟩
  have hb := gaussian_mv_abs_log_bound m v hv n p d D hd hD
  have hlog := Real.log_le_log hc hcoeff
  linarith

end
end D5.S3.Analytic.Probability.SampleCovarianceBernoulliOrders.Gaussian

namespace D5.S3.Analytic.Probability.SampleCovarianceBernoulliOrders.Gaussian
noncomputable section

def noiseFamily {n N : ℕ} (q : Fin (N+1) → MvPolynomial (Fin n) ℂ) (ε : ℝ) :
    MvPolynomial (Fin n) ℂ :=
  ∑ k : Fin (N+1), MvPolynomial.C ((ε : ℂ)^(k : ℕ)) * q k

private lemma noiseFamily_zero {n N : ℕ} (q : Fin (N+1) → MvPolynomial (Fin n) ℂ) :
    noiseFamily q 0 = q 0 := by
  simp [noiseFamily, Fin.sum_univ_succ]

private lemma noiseFamily_eval {n N : ℕ} (q : Fin (N+1) → MvPolynomial (Fin n) ℂ)
    (ε : ℝ) (x : Fin n → ℝ) :
    realEval (noiseFamily q ε) x = ∑ k : Fin (N+1), (ε : ℂ)^(k : ℕ) * realEval (q k) x := by
  simp only [noiseFamily, realEval, map_sum, map_mul, MvPolynomial.eval_C]

private lemma noiseFamily_coeff_continuous {n N : ℕ}
    (q : Fin (N+1) → MvPolynomial (Fin n) ℂ) (d : Fin n →₀ ℕ) :
    Continuous (fun ε : ℝ => (noiseFamily q ε).coeff d) := by
  simp only [noiseFamily, MvPolynomial.coeff_sum, MvPolynomial.coeff_C_mul]
  fun_prop

private lemma noiseFamily_degree_bound {n N : ℕ}
    (q : Fin (N+1) → MvPolynomial (Fin n) ℂ) (ε : ℝ) (i : Fin n) :
    (noiseFamily q ε).degreeOf i ≤ Finset.univ.sup (fun k => (q k).totalDegree) := by
  unfold noiseFamily
  apply (MvPolynomial.degreeOf_sum_le i _ _).trans
  apply Finset.sup_le
  intro k hk
  exact (MvPolynomial.degreeOf_C_mul_le (q k) i _).trans
    ((MvPolynomial.degreeOf_le_totalDegree _ _).trans (Finset.le_sup (f := fun k : Fin (N+1) => (q k).totalDegree) hk))

private lemma noiseFamily_integral_norm_bound {n N : ℕ} (m : ℝ) (v : ℝ≥0)
    (q : Fin (N+1) → MvPolynomial (Fin n) ℂ) (ε : ℝ) (hε : |ε| ≤ 1) :
    (∫ x, ‖realEval (noiseFamily q ε) x‖ ∂gaussianPi n m v) ≤
      ∑ k, ∫ x, ‖realEval (q k) x‖ ∂gaussianPi n m v := by
  have hi (k : Fin (N+1)) := (gaussian_mv_eval_integrable m v (q k)).norm
  rw [← integral_finsetSum _ (fun k _ => hi k)]
  apply integral_mono (gaussian_mv_eval_integrable m v _).norm
    (integrable_finsetSum _ (fun k _ => hi k))
  intro x
  change ‖realEval (noiseFamily q ε) x‖ ≤ ∑ k : Fin (N+1), ‖realEval (q k) x‖
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
      Integrable (fun x => Real.log ‖realEval (noiseFamily q ε) x‖) (gaussianPi n m v) ∧
      (∫ x, |Real.log ‖realEval (noiseFamily q ε) x‖| ∂gaussianPi n m v) ≤ C := by
  let c : ℝ := ‖(q 0).coeff d‖ / 2
  have hc : 0 < c := by dsimp [c]; exact half_pos (norm_pos_iff.mpr hd)
  have ht : Tendsto (fun ε : ℝ => ‖(noiseFamily q ε).coeff d‖)
      (𝓝 0) (𝓝 ‖(q 0).coeff d‖) := by
    simpa only [noiseFamily_zero] using (noiseFamily_coeff_continuous q d).norm.tendsto 0
  have hev : ∀ᶠ ε : ℝ in 𝓝 0, c < ‖(noiseFamily q ε).coeff d‖ :=
    ht.eventually (eventually_gt_nhds (by dsimp [c]; linarith [norm_pos_iff.mpr hd]))
  obtain ⟨δ, hδ, hδbound⟩ := Metric.eventually_nhds_iff.mp hev
  let D := Finset.univ.sup (fun k => (q k).totalDegree)
  let M := ∑ k, ∫ x, ‖realEval (q k) x‖ ∂gaussianPi n m v
  let C := max (2*M - Real.log c + (n : ℝ)*D*(Real.log 2 + D5.S3.Analytic.Probability.GaussianPolynomialLog.rootLogCost m v)) 0
  refine ⟨min δ 1, C, lt_min hδ (by norm_num), le_max_right _ _, ?_⟩
  intro ε hε
  have hε1 : |ε| ≤ 1 := (hε.trans_le (min_le_right _ _)).le
  have hcoeff : c ≤ ‖(noiseFamily q ε).coeff d‖ :=
    (hδbound (by simpa [Real.dist_eq] using hε.trans_le (min_le_left _ _))).le
  obtain ⟨hi, hb⟩ := gaussian_mv_uniform_abs_log_bound m v hv n D
    (noiseFamily q ε) d c M hc hcoeff (noiseFamily_degree_bound q ε)
    (noiseFamily_integral_norm_bound m v q ε hε1)
  exact ⟨hi, hb.trans (le_max_left _ _)⟩

end
end D5.S3.Analytic.Probability.SampleCovarianceBernoulliOrders.Gaussian

namespace D5.S3.Analytic.Probability.SampleCovarianceBernoulliOrders.Gaussian
noncomputable section

lemma gaussian_mv_log_integrable (m : ℝ) (v : ℝ≥0) (hv : v ≠ 0) {n : ℕ}
    (p : MvPolynomial (Fin n) ℂ) (hp : p ≠ 0) :
    (∀ᵐ x ∂gaussianPi n m v, realEval p x ≠ 0) ∧
    Integrable (fun x => Real.log ‖realEval p x‖) (gaussianPi n m v) := by
  obtain ⟨d, hd⟩ := MvPolynomial.exists_coeff_ne_zero hp
  obtain ⟨hae, hi, _⟩ := gaussian_mv_log_coeff_lower m v hv n p d p.totalDegree hd
    (fun i => MvPolynomial.degreeOf_le_totalDegree p i)
  exact ⟨hae, hi⟩

private lemma gaussian_mv_log_scalar (m : ℝ) (v : ℝ≥0) (hv : v ≠ 0) {n : ℕ}
    (p : MvPolynomial (Fin n) ℂ) (hp : p ≠ 0) (c : ℂ) (hc : c ≠ 0) :
    (∫ x, Real.log ‖c * realEval p x‖ ∂gaussianPi n m v) =
      Real.log ‖c‖ + ∫ x, Real.log ‖realEval p x‖ ∂gaussianPi n m v := by
  have hi := gaussian_mv_log_integrable m v hv p hp
  have heq : (fun x => Real.log ‖c * realEval p x‖) =ᵐ[gaussianPi n m v]
      (fun x => Real.log ‖c‖ + Real.log ‖realEval p x‖) := by
    filter_upwards [hi.1] with x hx
    rw [norm_mul, Real.log_mul (norm_ne_zero_iff.mpr hc) (norm_ne_zero_iff.mpr hx)]
  rw [integral_congr_ae heq, integral_add (integrable_const _) hi.2, integral_const]
  simp only [probReal_univ, one_smul]

private lemma gaussian_noiseFamily_log_remainder_tendsto {n N : ℕ} (m : ℝ) (v : ℝ≥0) (hv : v ≠ 0)
    (q : Fin (N+1) → MvPolynomial (Fin n) ℂ) (d : Fin n →₀ ℕ)
    (hd : (q 0).coeff d ≠ 0) :
    Tendsto (fun ε : ℝ => (∫ x, Real.log ‖realEval (noiseFamily q ε) x‖ ∂gaussianPi n m v) /
      Real.log (1/ε)) (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨δ, C, hδ, hC, hb⟩ := gaussian_noiseFamily_uniform_log m v hv q d hd
  have hsmall : ∀ᶠ ε : ℝ in 𝓝[>] 0, |ε| < δ := by
    apply Filter.Eventually.filter_mono nhdsWithin_le_nhds
    exact (isOpen_lt continuous_abs continuous_const).mem_nhds (by simpa using hδ)
  have hbound : ∀ᶠ ε : ℝ in 𝓝[>] 0,
      |∫ x, Real.log ‖realEval (noiseFamily q ε) x‖ ∂gaussianPi n m v| ≤ C := by
    filter_upwards [hsmall] with ε hε
    have hi := hb ε hε
    have hh : |∫ x, Real.log ‖realEval (noiseFamily q ε) x‖ ∂gaussianPi n m v| ≤
        ∫ x, |Real.log ‖realEval (noiseFamily q ε) x‖| ∂gaussianPi n m v := by
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm
        (fun x => Real.log ‖realEval (noiseFamily q ε) x‖)
    exact hh.trans hi.2
  have hden : Tendsto (fun ε : ℝ => Real.log (1/ε)) (𝓝[>] 0) atTop := by
    simpa only [one_div, Real.log_inv, Function.comp_def] using tendsto_neg_atBot_atTop.comp Real.tendsto_log_nhdsGT_zero
  exact tendsto_bdd_div_atTop_nhds_zero
    (hbound.mono (fun ε h => (abs_le.mp h).1))
    (hbound.mono (fun ε h => (abs_le.mp h).2)) hden

lemma gaussian_noiseFamily_log_order {n N : ℕ} (m : ℝ) (v : ℝ≥0) (hv : v ≠ 0)
    (q : Fin (N+1) → MvPolynomial (Fin n) ℂ) (d : Fin n →₀ ℕ)
    (hd : (q 0).coeff d ≠ 0) (k : ℕ) :
    Tendsto (fun ε : ℝ => -(∫ x, Real.log ‖(ε : ℂ)^k * realEval (noiseFamily q ε) x‖
      ∂gaussianPi n m v) / Real.log (1/ε)) (𝓝[>] 0) (𝓝 (k : ℝ)) := by
  have hrem := gaussian_noiseFamily_log_remainder_tendsto m v hv q d hd
  have ht : Tendsto (fun ε : ℝ => ‖(noiseFamily q ε).coeff d‖)
      (𝓝 0) (𝓝 ‖(q 0).coeff d‖) := by
    simpa only [noiseFamily_zero] using (noiseFamily_coeff_continuous q d).norm.tendsto 0
  have hne : ∀ᶠ ε : ℝ in 𝓝[>] 0, noiseFamily q ε ≠ 0 := by
    have hh := ht.eventually (eventually_gt_nhds (norm_pos_iff.mpr hd))
    apply Filter.Eventually.filter_mono nhdsWithin_le_nhds
    filter_upwards [hh] with ε hε
    exact MvPolynomial.ne_zero_iff.mpr ⟨d, norm_pos_iff.mp hε⟩
  have hden : Tendsto (fun ε : ℝ => Real.log (1/ε)) (𝓝[>] 0) atTop := by
    simpa only [one_div, Real.log_inv, Function.comp_def] using tendsto_neg_atBot_atTop.comp Real.tendsto_log_nhdsGT_zero
  have heq : (fun ε : ℝ => -(∫ x, Real.log ‖(ε : ℂ)^k * realEval (noiseFamily q ε) x‖
        ∂gaussianPi n m v) / Real.log (1/ε)) =ᶠ[𝓝[>] 0]
      (fun ε => (k : ℝ) - (∫ x, Real.log ‖realEval (noiseFamily q ε) x‖
        ∂gaussianPi n m v) / Real.log (1/ε)) := by
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
