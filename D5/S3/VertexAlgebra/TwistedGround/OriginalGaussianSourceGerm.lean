/- GID: D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianSourceGerm
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/OriginalGaussianSourceGerm
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Fixed-cutoff contraction germs for original source rows and positive comparisons. -/

import D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianSourceMeans
import D5.S3.VertexAlgebra.TwistedGround.FiniteAffineGaussianSewing
import Mathlib.Analysis.Normed.Group.FunctionSeries

/-! The raw left and fully transported right internal matrices vanish at zero.
Their finite positive comparisons therefore admit a common contraction germ
for each fixed cutoff. The radius is allowed to depend on the cutoff. This
does not assert occupation convergence on the unit disk or uniformly in the
cutoff. All colours remain in the right inverse substitution.

The finite-dimensional neighbourhood construction is classical. Its actual-row
application is part of the source coefficient route, not a proof of the final
energy coefficient identity. -/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Topology Kronecker

namespace D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianSourceGerm

open LatticeGeneratingFieldLocality LatticeHalfFock
open OriginalGaussianExternalBlocks OriginalGaussianSourceMeans
open OriginalChargedRowSource FactorialFockMetric
open OriginalGaussianMatrix OriginalGaussianDeterminant OriginalCurrentMetric NativeAffineTransport
open OriginalCorrectedRowRecompositionSource

universe u
variable {X : Type u} [Fintype X] [DecidableEq X]

/-- Positive comparison on all internal colours at all retained frequencies.
The undamped right matrix already includes its complete inverse transport. -/
def positiveInternal (D : LatticeData) (N : ℕ)
    (C : Matrix (Internal D N) (Internal D N) ℂ) (t : ℝ) :
    Matrix (Internal D N) (Internal D N) ℂ :=
  fun i j => (‖C i j‖ : ℂ) * (t : ℂ) ^ (i.2.val + 1) * (t : ℂ) ^ (j.2.val + 1)

private lemma damp_differentiable (D : LatticeData) (N : ℕ)
    (i : Internal D N ⊕ X) : Differentiable ℂ (fun z => damp D N z i) := by
  cases i <;> simp only [damp] <;> fun_prop

lemma left_entry_differentiable (D : LatticeData) (N : ℕ)
    (e : X → External D) (i j : Internal D N ⊕ X) :
    Differentiable ℂ (fun z => leftRow D N e z i j) := by
  exact ((damp_differentiable D N i).mul_const _).mul (damp_differentiable D N j)

lemma right_entry_differentiable (D : LatticeData) (N : ℕ)
    (e : X → External D) (i j : Internal D N ⊕ X) :
    Differentiable ℂ (fun z => rightRow D N e z i j) := by
  exact ((damp_differentiable D N i).mul_const _).mul (damp_differentiable D N j)

private lemma euclidean_norm_continuous {I : Type*} [Fintype I] [DecidableEq I]
    {f : ℂ → Matrix I I ℂ} (hf : Continuous f) :
    Continuous (fun z => ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (f z)‖) := by
  let T : Matrix I I ℂ →ₗ[ℂ] (EuclideanSpace ℂ I →L[ℂ] EuclideanSpace ℂ I) :=
    (Matrix.toEuclideanCLM (n := I) (𝕜 := ℂ)).toAlgEquiv.toLinearMap
  exact (T.continuous_of_finiteDimensional.comp hf).norm

private lemma positive_continuous (D : LatticeData) (N : ℕ)
    (C : Matrix (Internal D N) (Internal D N) ℂ) :
    Continuous (fun z : ℂ => positiveInternal D N C ‖z‖) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  simp only [positiveInternal]
  fun_prop

private lemma positive_zero (D : LatticeData) (N : ℕ)
    (C : Matrix (Internal D N) (Internal D N) ℂ) : positiveInternal D N C 0 = 0 := by
  ext i j
  simp [positiveInternal]

private lemma strict_on_closed_germ {f : ℂ → ℝ} (hf : Continuous f) (h0 : f 0 < 1) :
    ∃ r : ℝ, 0 < r ∧ ∀ z : ℂ, ‖z‖ ≤ r → f z < 1 := by
  have hn : ∀ᶠ z in 𝓝 (0 : ℂ), f z < 1 := hf.continuousAt.eventually (gt_mem_nhds h0)
  obtain ⟨ε, hε, he⟩ := Metric.eventually_nhds_iff.mp hn
  refine ⟨ε / 2, by positivity, fun z hz => he ?_⟩
  simpa only [dist_zero_right] using (hz.trans_lt (half_lt_self hε))

/-- A fixed-cutoff closed disk where both actual raw internal matrices and
both entrywise positive comparison matrices are strict Euclidean contractions.
There is no positive-rank, nonempty-support or positive-cutoff assumption. -/
theorem original_rows_contract_on_germ (D : LatticeData) (N : ℕ)
    (e : X → External D) :
    ∃ r : ℝ, 0 < r ∧ r < 1 ∧ ∀ z : ℂ, ‖z‖ ≤ r →
      ‖Matrix.toEuclideanCLM (𝕜 := ℂ)
        ((leftRow D N e z).submatrix Sum.inl Sum.inl)‖ < 1 ∧
      ‖Matrix.toEuclideanCLM (𝕜 := ℂ)
        ((rightRow D N e z).submatrix Sum.inl Sum.inl)‖ < 1 ∧
      ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (positiveInternal D N
        ((originalRow D N e).submatrix Sum.inl Sum.inl) ‖z‖)‖ < 1 ∧
      ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (positiveInternal D N
        ((transportCovariance (sourceBlock (J := X) (inverseSubstitution D N))
          (originalRow D N e)).submatrix Sum.inl Sum.inl) ‖z‖)‖ < 1 := by
  let A := fun z => (leftRow D N e z).submatrix Sum.inl Sum.inl
  let B := fun z => (rightRow D N e z).submatrix Sum.inl Sum.inl
  have hA : Continuous A := continuous_pi fun i => continuous_pi fun j =>
    (left_entry_differentiable D N e (.inl i) (.inl j)).continuous
  have hB : Continuous B := continuous_pi fun i => continuous_pi fun j =>
    (right_entry_differentiable D N e (.inl i) (.inl j)).continuous
  have hA0 : A 0 = 0 := by ext i j; simp [A, leftRow, damp]
  have hB0 : B 0 = 0 := by ext i j; simp [B, rightRow, damp]
  obtain ⟨rA, hrA, hAr⟩ := strict_on_closed_germ (euclidean_norm_continuous hA)
    (by simp [hA0])
  obtain ⟨rB, hrB, hBr⟩ := strict_on_closed_germ (euclidean_norm_continuous hB)
    (by simp [hB0])
  obtain ⟨rP, hrP, hPr⟩ := strict_on_closed_germ
    (euclidean_norm_continuous (positive_continuous D N
      ((originalRow D N e).submatrix Sum.inl Sum.inl)))
    (by simp [positive_zero])
  obtain ⟨rQ, hrQ, hQr⟩ := strict_on_closed_germ
    (euclidean_norm_continuous (positive_continuous D N
      ((transportCovariance (sourceBlock (J := X) (inverseSubstitution D N))
        (originalRow D N e)).submatrix Sum.inl Sum.inl)))
    (by simp [positive_zero])
  let r := min (1 / 2 : ℝ) (min (min rA rB) (min rP rQ))
  refine ⟨r, lt_min (by norm_num) (lt_min (lt_min hrA hrB) (lt_min hrP hrQ)),
    (min_le_left _ _).trans_lt (by norm_num), ?_⟩
  intro z hz
  have hs : r ≤ min (min rA rB) (min rP rQ) := min_le_right _ _
  exact ⟨hAr z (hz.trans (hs.trans ((min_le_left _ _).trans (min_le_left _ _)))),
    hBr z (hz.trans (hs.trans ((min_le_left _ _).trans (min_le_right _ _)))),
    hPr z (hz.trans (hs.trans ((min_le_right _ _).trans (min_le_left _ _)))),
    hQr z (hz.trans (hs.trans ((min_le_right _ _).trans (min_le_right _ _))))⟩

private lemma conjugate_power {I : Type*} [Fintype I] [DecidableEq I]
    (P Q K : Matrix I I ℂ) (hPQ : P * Q = 1) (hQP : Q * P = 1) (p : ℕ) :
    (P * K * Q) ^ p = P * K ^ p * Q := by
  induction p with
  | zero => simp [hPQ]
  | succ p ih =>
    rw [pow_succ, ih, pow_succ]
    calc
      _ = P * K ^ p * (Q * P) * K * Q := by noncomm_ring
      _ = _ := by rw [hQP, mul_one]; noncomm_ring

private lemma identity_kronecker_power {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] (K : Matrix J J ℂ) (p : ℕ) :
    ((1 : Matrix I I ℂ) ⊗ₖ K) ^ p = (1 : Matrix I I ℂ) ⊗ₖ (K ^ p) := by
  induction p with
  | zero => simp [Matrix.one_kronecker_one]
  | succ p ih => rw [pow_succ, ih, ← Matrix.mul_kronecker_mul, one_mul, ← pow_succ]

/-- Literal finite trace similarity for the raw, fully inverse-transported
rows. The diagonal conjugation uses positive frequencies, never inverse z. -/
theorem original_rows_trace_power (D : LatticeData) (hu : IsUnit D.G.det)
    (N : ℕ) (e : X → External D) (z : ℂ) (p : ℕ) :
    Matrix.trace (((leftRow D N e z).submatrix Sum.inl Sum.inl *
      (rightRow D N e z).submatrix Sum.inl Sum.inl) ^ p) =
      (D.rank : ℂ) * Matrix.trace (finiteSection N z ^ (2 * p)) := by
  have hprod : (leftRow D N e z).submatrix Sum.inl Sum.inl *
      (rightRow D N e z).submatrix Sum.inl Sum.inl =
      (1 : Matrix (Fin D.rank) (Fin D.rank) ℂ) ⊗ₖ
        (frequencyRoot N * finiteSection N z ^ 2 * inverseFrequencyRoot N) := by
    rw [original_source, original_inverse_source D hu, ← Matrix.mul_kronecker_mul,
      Matrix.mul_nonsing_inv _ (SignedOscillatorWick.complex_det_unit D hu)]
    congr 1
    calc
      _ = frequencyRoot N * finiteSection N z *
          (frequencyRoot N * inverseFrequencyRoot N) * finiteSection N z *
            inverseFrequencyRoot N := by noncomm_ring
      _ = _ := by rw [(root_units N).1, mul_one, pow_two]; noncomm_ring
  rw [hprod, identity_kronecker_power,
    conjugate_power _ _ _ (root_units N).1 (root_units N).2, Matrix.trace_kronecker,
    Matrix.trace_mul_cycle, (root_units N).2, one_mul, ← pow_mul]
  simp

/-- The finite affine sewing trace prefactor has exactly the source
normalization exp(-(rank/2)*finiteLog), including rank zero and N=0. -/
theorem original_rows_trace_prefactor (D : LatticeData) (hu : IsUnit D.G.det)
    (N : ℕ) (e : X → External D) (z : ℂ) :
    Complex.exp ((1 / 2 : ℂ) * ∑' k : ℕ,
      Matrix.trace (((leftRow D N e z).submatrix Sum.inl Sum.inl *
        (rightRow D N e z).submatrix Sum.inl Sum.inl) ^ (k + 1)) / (k + 1 : ℂ)) =
      Complex.exp (-(D.rank : ℂ) / 2 * finiteLog N z) := by
  simp_rw [original_rows_trace_power D hu, mul_div_assoc]
  rw [tsum_mul_left, finiteLog]
  congr 1
  ring

section PositiveCoefficients
open MvPolynomial FactorialFockQuadraticEstimate
variable {I : Type*} [Fintype I] [DecidableEq I]

private def dominates (p : MvPolynomial I ℂ) (q : MvPolynomial I ℝ) : Prop :=
  ∀ d, ‖p.coeff d‖ ≤ q.coeff d

private lemma dominates_mul {p p' : MvPolynomial I ℂ} {q q' : MvPolynomial I ℝ}
    (h : dominates p q) (h' : dominates p' q') : dominates (p * p') (q * q') := by
  intro d
  simp only [coeff_mul]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro a ha
  rw [norm_mul]
  exact mul_le_mul (h a.1) (h' a.2) (norm_nonneg _) ((norm_nonneg _).trans (h _))

private lemma dominates_sum {J : Type*} (s : Finset J)
    {p : J → MvPolynomial I ℂ} {q : J → MvPolynomial I ℝ}
    (h : ∀ j ∈ s, dominates (p j) (q j)) : dominates (∑ j ∈ s, p j) (∑ j ∈ s, q j) := by
  intro d
  simp only [coeff_sum]
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun j hj => h j hj d))

private lemma dominates_smul {p : MvPolynomial I ℂ} {q : MvPolynomial I ℝ}
    (h : dominates p q) {c : ℂ} {r : ℝ} (hc : ‖c‖ ≤ r) :
    dominates (c • p) (r • q) := by
  intro d
  simp only [coeff_smul, smul_eq_mul, norm_mul]
  exact mul_le_mul hc (h d) (norm_nonneg _) ((norm_nonneg _).trans hc)

private lemma dominates_pow {p : MvPolynomial I ℂ} {q : MvPolynomial I ℝ}
    (h : dominates p q) (k : ℕ) : dominates (p ^ k) (q ^ k) := by
  induction k with
  | zero => intro d; simp only [pow_zero, coeff_one]; split_ifs <;> simp
  | succ k ih => simpa only [pow_succ] using dominates_mul ih h

private def realQuadratic (P : Matrix I I ℝ) : MvPolynomial I ℝ :=
  (1 / 2 : ℝ) • ∑ i, ∑ j, P i j • (MvPolynomial.X i * MvPolynomial.X j)

private lemma quadratic_domination (A : Matrix I I ℂ) (P : Matrix I I ℝ)
    (h : ∀ i j, ‖A i j‖ ≤ P i j) : dominates (quadratic A) (realQuadratic P) := by
  apply dominates_smul
  · apply dominates_sum
    intro i hi
    apply dominates_sum
    intro j hj
    apply dominates_smul
    · apply dominates_mul <;> intro d <;> simp only [coeff_X] <;> split_ifs <;> simp
    · exact h i j
  · norm_num

private lemma map_realQuadratic (P : Matrix I I ℝ) :
    MvPolynomial.map Complex.ofRealHom (realQuadratic P) =
      quadratic (fun i j => (P i j : ℂ)) := by
  simp only [realQuadratic, quadratic, smul_eq_C_mul, map_mul, map_sum,
    MvPolynomial.map_C, MvPolynomial.map_X, map_div₀, map_ofNat, map_one]
  rfl

private lemma gaussian_norm_le_positive (A : Matrix I I ℂ) (P : Matrix I I ℝ)
    (h : ∀ i j, ‖A i j‖ ≤ P i j) (d : I →₀ ℕ) :
    ‖gaussianCoefficient A d‖ ≤
      ‖gaussianCoefficient (fun i j => (P i j : ℂ)) d‖ := by
  let k := d.degree / 2
  let q : MvPolynomial I ℝ := (k.factorial : ℝ)⁻¹ • realQuadratic P ^ k
  have hb : dominates (gaussianPiece A k) q :=
    dominates_smul (dominates_pow (quadratic_domination A P h) k) (by
      simp only [norm_inv, Complex.norm_natCast]; exact le_rfl)
  have hm : MvPolynomial.map Complex.ofRealHom q =
      gaussianPiece (fun i j => (P i j : ℂ)) k := by
    simp only [q, gaussianPiece, smul_eq_C_mul, map_mul, MvPolynomial.map_C,
      map_inv₀, map_natCast, map_pow, map_realQuadratic]
  calc
    _ ≤ q.coeff d := hb d
    _ ≤ ‖(q.coeff d : ℂ)‖ := by simpa using Complex.re_le_norm (q.coeff d : ℂ)
    _ = _ := by
      have hc := congrArg (fun f : MvPolynomial I ℂ => f.coeff d) hm
      have hc' : (q.coeff d : ℂ) = (gaussianPiece (fun i j => (P i j : ℂ)) k).coeff d := by
        simpa only [coeff_map, Complex.ofRealHom_eq_coe] using hc
      exact congrArg norm hc'

private lemma affine_norm_le_positive (A : Matrix I I ℂ) (mu : I → ℂ)
    (P : Matrix I I ℝ) (m : I → ℝ)
    (hA : ∀ i j, ‖A i j‖ ≤ P i j) (hm : ∀ i, ‖mu i‖ ≤ m i) (d : I →₀ ℕ) :
    ‖affineCoefficient A mu d‖ ≤
      ∑ k ∈ Finset.range (d.degree + 1),
        ‖gaussianCoefficient (affineKernel (fun i j => (P i j : ℂ))
          (fun i => (m i : ℂ))) (d.sumElim (Finsupp.single () k))‖ := by
  let Q : Matrix (I ⊕ Unit) (I ⊕ Unit) ℝ :=
    fun i j => match i, j with
    | .inl i, .inl j => P i j
    | .inl i, .inr _ => m i
    | .inr _, .inl j => m j
    | .inr _, .inr _ => 0
  have hQ : ∀ i j, ‖affineKernel A mu i j‖ ≤ Q i j := by
    intro i j
    cases i <;> cases j <;>
      simp only [affineKernel, ElementaryGaussianContraction.leftKernel,
        Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
        Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂,
        Matrix.transpose_apply, Matrix.zero_apply, Q]
    exacts [hA _ _, hm _, hm _, by change ‖(0 : ℂ)‖ ≤ 0; simp]
  have he : (fun i j => (Q i j : ℂ)) =
      affineKernel (fun i j => (P i j : ℂ)) (fun i => (m i : ℂ)) := by
    ext i j
    cases i <;> cases j <;> first | rfl | simp [Q, affineKernel, ElementaryGaussianContraction.leftKernel, Matrix.fromBlocks, Matrix.transpose]
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun k _ => by
    simpa only [he] using gaussian_norm_le_positive (affineKernel A mu) Q hQ
      (d.sumElim (Finsupp.single () k))))

private def auxiliaryMajorant (P : Matrix I I ℝ) (m : I → ℝ) (d : I →₀ ℕ) : ℝ :=
  ∑ k ∈ Finset.range (d.degree + 1),
    ‖gaussianCoefficient (affineKernel (fun i j => (P i j : ℂ))
      (fun i => (m i : ℂ))) (d.sumElim (Finsupp.single () k))‖

private lemma uniform_pair_majorant {T : Type*} (s : Set T)
    (A B : T → Matrix I I ℂ) (mu nu : T → I → ℂ) (q : T → ℂ)
    (P Q : Matrix I I ℝ) (m l : I → ℝ) (c : ℝ)
    (hP : ∀ i j, P i j = P j i) (hQ : ∀ i j, Q i j = Q j i)
    (hPc : ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (fun i j => (P i j : ℂ))‖ < 1)
    (hQc : ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (fun i j => (Q i j : ℂ))‖ < 1)
    (hA : ∀ t ∈ s, ∀ i j, ‖A t i j‖ ≤ P i j)
    (hB : ∀ t ∈ s, ∀ i j, ‖B t i j‖ ≤ Q i j)
    (hm : ∀ t ∈ s, ∀ i, ‖mu t i‖ ≤ m i)
    (hl : ∀ t ∈ s, ∀ i, ‖nu t i‖ ≤ l i)
    (hq : ∀ t ∈ s, ‖Complex.exp (q t)‖ ≤ Real.exp c) :
    ∃ M : (I →₀ ℕ) → ℝ, Summable M ∧ ∀ t ∈ s, ∀ d,
      ‖Complex.exp (q t) * (FactorialFockMetric.weight d : ℂ) *
        affineCoefficient (A t) (mu t) d * affineCoefficient (B t) (nu t) d‖ ≤ M d := by
  let F := auxiliaryMajorant P m
  let G := auxiliaryMajorant Q l
  have hF := FiniteAffineGaussianSewing.affine_majorant_summable
    (fun i j => (P i j : ℂ)) (fun i => (m i : ℂ))
    (fun i j => congrArg Complex.ofReal (hP i j)) hPc
  have hG := FiniteAffineGaussianSewing.affine_majorant_summable
    (fun i j => (Q i j : ℂ)) (fun i => (l i : ℂ))
    (fun i j => congrArg Complex.ofReal (hQ i j)) hQc
  refine ⟨fun d => Real.exp c * ((FactorialFockMetric.weight d : ℝ) * F d ^ 2 +
    (FactorialFockMetric.weight d : ℝ) * G d ^ 2), (hF.add hG).mul_left _, ?_⟩
  intro t ht d
  have hFd : 0 ≤ F d := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hGd : 0 ≤ G d := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hw : 0 ≤ (FactorialFockMetric.weight d : ℝ) := Nat.cast_nonneg _
  calc
    _ ≤ Real.exp c * (FactorialFockMetric.weight d : ℝ) * F d * G d := by
      simp only [norm_mul, Complex.norm_natCast]
      have h1 := mul_le_mul_of_nonneg_right (hq t ht) hw
      have h2 := mul_le_mul h1 (affine_norm_le_positive _ _ P m (hA t ht) (hm t ht) d)
        (norm_nonneg _) (mul_nonneg (Real.exp_nonneg _) hw)
      exact mul_le_mul h2 (affine_norm_le_positive _ _ Q l (hB t ht) (hl t ht) d)
        (norm_nonneg _) (mul_nonneg (mul_nonneg (Real.exp_nonneg _) hw) hFd)
    _ ≤ _ := by
      have h : (FactorialFockMetric.weight d : ℝ) * F d * G d ≤
          (FactorialFockMetric.weight d : ℝ) * F d ^ 2 +
          (FactorialFockMetric.weight d : ℝ) * G d ^ 2 := by
        nlinarith [mul_nonneg hw (sq_nonneg (F d - G d)), mul_nonneg hw (sq_nonneg (F d)),
          mul_nonneg hw (sq_nonneg (G d))]
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left h (Real.exp_nonneg _)

end PositiveCoefficients

/-- The actual internal affine mean with all external coordinates retained. -/
def mixedMean {I J : Type*} [Fintype J] (C : Matrix (I ⊕ J) (I ⊕ J) ℂ)
    (m : I ⊕ J → ℂ) (x : J → ℂ) : I → ℂ :=
  fun i => m (.inl i) + ∑ j, C (.inl i) (.inr j) * x j

/-- The external part of the original affine exponent, with ordinary products. -/
def externalExponent {I J : Type*} [Fintype J]
    (C : Matrix (I ⊕ J) (I ⊕ J) ℂ) (m : I ⊕ J → ℂ) (x : J → ℂ) : ℂ :=
  (1 / 2 : ℂ) * ∑ i, ∑ j, C (.inr i) (.inr j) * x i * x j +
    ∑ i, m (.inr i) * x i

private def externalBound {I J : Type*} [Fintype J]
    (C : Matrix (I ⊕ J) (I ⊕ J) ℂ) (m : I ⊕ J → ℂ) : ℝ :=
  (1 / 2 : ℝ) * ∑ i, ∑ j, ‖C (.inr i) (.inr j)‖ + ∑ i, ‖m (.inr i)‖

private lemma external_bound {I J : Type*} [Fintype J]
    (C : Matrix (I ⊕ J) (I ⊕ J) ℂ) (m : I ⊕ J → ℂ)
    (x : J → ℂ) (hx : ∀ j, ‖x j‖ ≤ 1) :
    ‖externalExponent C m x‖ ≤ externalBound C m := by
  unfold externalExponent externalBound
  apply (norm_add_le _ _).trans
  apply add_le_add
  · rw [norm_mul]
    have hc : ‖(1 / 2 : ℂ)‖ = (1 / 2 : ℝ) := by norm_num
    rw [hc]
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro i hi
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro j hj
    simp only [norm_mul]
    calc
      _ ≤ ‖C (.inr i) (.inr j)‖ * 1 * 1 := by gcongr <;> apply hx
      _ = _ := by ring
  · apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro i hi
    simpa only [norm_mul, mul_one] using
      mul_le_mul_of_nonneg_left (hx i) (norm_nonneg (m (.inr i)))

private def positiveMean (D : LatticeData) (N : ℕ)
    (C : Matrix (Internal D N ⊕ X) (Internal D N ⊕ X) ℂ)
    (m : Internal D N ⊕ X → ℂ) (t : ℝ) : Internal D N → ℝ :=
  fun i => t ^ (i.2.val + 1) * (‖m (.inl i)‖ + ∑ j, ‖C (.inl i) (.inr j)‖)

private lemma damped_mixed_bound (D : LatticeData) (N : ℕ)
    (C : Matrix (Internal D N ⊕ X) (Internal D N ⊕ X) ℂ)
    (m : Internal D N ⊕ X → ℂ) (t : ℝ) {z : ℂ} (hz : ‖z‖ ≤ t)
    (x : X → ℂ) (hx : ∀ j, ‖x j‖ ≤ 1) (i : Internal D N) :
    ‖mixedMean (fun i j => damp D N z i * C i j * damp D N z j)
      (fun i => damp D N z i * m i) x i‖ ≤ positiveMean D N C m t i := by
  have ht : 0 ≤ t := (norm_nonneg _).trans hz
  change ‖z ^ (i.2.val + 1) * m (.inl i) +
    ∑ j, (z ^ (i.2.val + 1) * C (.inl i) (.inr j) * 1) * x j‖ ≤ _
  simp only [mul_one]
  apply (norm_add_le _ _).trans
  simp only [norm_mul, norm_pow, positiveMean, mul_add]
  apply add_le_add
  · exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hz _) (norm_nonneg _)
  · apply (norm_sum_le _ _).trans
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j hj
    simp only [norm_mul, norm_pow]
    calc
      _ ≤ t ^ (i.2.val + 1) * ‖C (.inl i) (.inr j)‖ * 1 := by
        exact mul_le_mul (mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ (norm_nonneg _) hz _) (norm_nonneg _)) (hx j)
          (norm_nonneg _) (mul_nonneg (pow_nonneg ht _) (norm_nonneg _))
      _ = _ := mul_one _

private lemma damped_covariance_bound (D : LatticeData) (N : ℕ)
    (C : Matrix (Internal D N ⊕ X) (Internal D N ⊕ X) ℂ)
    (t : ℝ) {z : ℂ} (hz : ‖z‖ ≤ t) (i j : Internal D N) :
    ‖damp D N (X := X) z (.inl i) * C (.inl i) (.inl j) * damp D N (X := X) z (.inl j)‖ ≤
      ‖C (.inl i) (.inl j)‖ * t ^ (i.2.val + 1) * t ^ (j.2.val + 1) := by
  simp only [damp, norm_mul, norm_pow]
  calc
    _ ≤ t ^ (i.2.val + 1) * ‖C (.inl i) (.inl j)‖ * t ^ (j.2.val + 1) := by
      exact mul_le_mul (mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (norm_nonneg _) hz _) (norm_nonneg _))
        (pow_le_pow_left₀ (norm_nonneg _) hz _) (pow_nonneg (norm_nonneg _) _)
        (mul_nonneg (pow_nonneg ((norm_nonneg _).trans hz) _) (norm_nonneg _))
    _ = _ := by ring

private lemma corrected_symmetry_on_pair (D : LatticeData)
    (x y : Index D ⊕ (Index D ⊕ Index D)) :
    OriginalCorrectedRowRecompositionSource.correctedMatrix D
      (Function.Embedding.refl (Index D)) x y =
    OriginalCorrectedRowRecompositionSource.correctedMatrix D
      (Function.Embedding.refl (Index D)) y x := by
  let index : Index D ⊕ (Index D ⊕ Index D) → Index D := Sum.elim id (Sum.elim id id)
  let K : Finset (Index D) := {index x, index y}
  let lift (t : Index D ⊕ (Index D ⊕ Index D)) (ht : index t ∈ K) :
      {b // b ∈ K} ⊕ ({b // b ∈ K} ⊕ {b // b ∈ K}) :=
    match t with
    | .inl b => .inl ⟨b, ht⟩
    | .inr (.inl b) => .inr (.inl ⟨b, ht⟩)
    | .inr (.inr b) => .inr (.inr ⟨b, ht⟩)
  have hx : index x ∈ K := by simp [K]
  have hy : index y ∈ K := by simp [K]
  have hh := OriginalSourceInverseCoefficient.correctedMatrix_symm D
    (OriginalNormalRowSource.supportLabel D K) (lift x hx) (lift y hy)
  convert hh using 1 <;> cases x with
  | inl x => cases y with
    | inl y => rfl
    | inr y => cases y <;> rfl
  | inr x => cases x <;> cases y with
    | inl y => rfl
    | inr y => cases y <;> rfl

/-- The literal undamped original mean, with no source-variable evaluation. -/
def originalMean (D : LatticeData) (a : Charge D) (N : ℕ) (e : X → External D) :
    Internal D N ⊕ X → ℂ :=
  correctedMean D a (Function.Embedding.refl (Index D)) ∘
    Sum.elim (fun i => .inl (OriginalSourceInverseCoefficient.boxLabel D N i))
      (fun x => if (e x).1 then .inr (.inr (e x).2) else .inr (.inl (e x).2))

/-- Full inverse colour transport of the original opposite-charge mean. -/
def originalInverseMean (D : LatticeData) (a : Charge D) (N : ℕ)
    (e : X → External D) : Internal D N ⊕ X → ℂ :=
  transportMean (sourceBlock (J := X) (inverseSubstitution D N)) (originalMean D (-a) N e)

private lemma leftMean_raw (D : LatticeData) (a : Charge D) (N : ℕ)
    (e : X → External D) (z : ℂ) :
    leftMean D a N e z = fun i => damp D N z i * originalMean D a N e i := rfl

lemma rightMean_raw (D : LatticeData) (a : Charge D) (N : ℕ)
    (e : X → External D) (z : ℂ) :
    rightMean D a N e z = fun i => damp D N z i * originalInverseMean D a N e i := by
  have h : leftMean D (-a) N e 1 = originalMean D (-a) N e := by
    funext i
    cases i <;> simp [leftMean, originalMean, damp, Function.comp_def]
  unfold OriginalGaussianSourceMeans.rightMean
  rw [h]
  rfl

/-- One native occupation term with the original opposite-charge rows. -/
def occupationTerm (D : LatticeData) (a : Charge D) (N : ℕ) (e : X → External D)
    (d : Internal D N →₀ ℕ) (p : ℂ × (X → ℂ) × (X → ℂ)) : ℂ :=
  Complex.exp (externalExponent (leftRow D N e p.1) (leftMean D a N e p.1) p.2.1 +
    externalExponent (rightRow D N e p.1) (rightMean D a N e p.1) p.2.2) *
    (FactorialFockMetric.weight d : ℂ) *
    affineCoefficient ((leftRow D N e p.1).submatrix Sum.inl Sum.inl)
      (mixedMean (leftRow D N e p.1) (leftMean D a N e p.1) p.2.1) d *
    affineCoefficient ((rightRow D N e p.1).submatrix Sum.inl Sum.inl)
      (mixedMean (rightRow D N e p.1) (rightMean D a N e p.1) p.2.2) d

/-- Closed source disk times the two external unit polydisks. -/
def sourcePolydisk (r : ℝ) : Set (ℂ × (X → ℂ) × (X → ℂ)) :=
  {p | ‖p.1‖ ≤ r ∧ (∀ j, ‖p.2.1 j‖ ≤ 1) ∧ ∀ j, ‖p.2.2 j‖ ≤ 1}

/-- A fixed summable majorant on the actual mixed external source germ.
The radius and majorant may depend on N. No unit-disk occupation convergence
or positive lower bound uniform in the cutoff is asserted. -/
theorem original_occupation_majorant_on_germ (D : LatticeData) (a : Charge D)
    (N : ℕ) (e : X → External D) :
    ∃ r : ℝ, 0 < r ∧ r < 1 ∧ ∃ M : (Internal D N →₀ ℕ) → ℝ,
      Summable M ∧ ∀ p ∈ sourcePolydisk (X := X) r, ∀ d,
        ‖occupationTerm D a N e d p‖ ≤ M d := by
  let C := originalRow D N e
  let R := transportCovariance (sourceBlock (J := X) (inverseSubstitution D N)) C
  let m := originalMean D a N e
  let l := originalInverseMean D a N e
  obtain ⟨r, hr, hr1, hc⟩ := original_rows_contract_on_germ D N e
  have he : ‖(r : ℂ)‖ = r := by simp [abs_of_pos hr]
  have hpos := hc (r : ℂ) he.le
  rw [he] at hpos
  let P : Matrix (Internal D N) (Internal D N) ℝ :=
    fun i j => ‖C (.inl i) (.inl j)‖ * r ^ (i.2.val + 1) * r ^ (j.2.val + 1)
  let Q : Matrix (Internal D N) (Internal D N) ℝ :=
    fun i j => ‖R (.inl i) (.inl j)‖ * r ^ (i.2.val + 1) * r ^ (j.2.val + 1)
  have hC : ∀ i j, C i j = C j i := by
    intro i j
    dsimp only [C, originalRow, Matrix.submatrix_apply]
    exact corrected_symmetry_on_pair D _ _
  have hR : ∀ i j, R i j = R j i := transportCovariance_symm _ _ hC
  have hP : ∀ i j, P i j = P j i := by
    intro i j; dsimp [P]; rw [hC (.inl j) (.inl i)]; ring
  have hQ : ∀ i j, Q i j = Q j i := by
    intro i j; dsimp [Q]; rw [hR (.inl j) (.inl i)]; ring
  have hPc : ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (fun i j => (P i j : ℂ))‖ < 1 := by
    have hh : (fun i j => (P i j : ℂ)) = positiveInternal D N
        (C.submatrix Sum.inl Sum.inl) r := by
      ext i j
      simp only [P, positiveInternal, Matrix.submatrix_apply, Complex.ofReal_mul, Complex.ofReal_pow]
    rw [hh]
    exact hpos.2.2.1
  have hQc : ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (fun i j => (Q i j : ℂ))‖ < 1 := by
    have hh : (fun i j => (Q i j : ℂ)) = positiveInternal D N
        (R.submatrix Sum.inl Sum.inl) r := by
      ext i j
      simp only [Q, positiveInternal, Matrix.submatrix_apply, Complex.ofReal_mul, Complex.ofReal_pow]
    rw [hh]
    exact hpos.2.2.2
  have hm (z : ℂ) : leftMean D a N e z = fun i => damp D N z i * m i := by
    exact leftMean_raw D a N e z
  have hl (z : ℂ) : rightMean D a N e z = fun i => damp D N z i * l i := by
    exact rightMean_raw D a N e z
  have hmajor := uniform_pair_majorant (sourcePolydisk (X := X) r)
    (fun p => (leftRow D N e p.1).submatrix Sum.inl Sum.inl)
    (fun p => (rightRow D N e p.1).submatrix Sum.inl Sum.inl)
    (fun p => mixedMean (leftRow D N e p.1) (leftMean D a N e p.1) p.2.1)
    (fun p => mixedMean (rightRow D N e p.1) (rightMean D a N e p.1) p.2.2)
    (fun p => externalExponent (leftRow D N e p.1) (leftMean D a N e p.1) p.2.1 +
      externalExponent (rightRow D N e p.1) (rightMean D a N e p.1) p.2.2)
    P Q (positiveMean D N C m r) (positiveMean D N R l r)
    (externalBound C m + externalBound R l) hP hQ hPc hQc
    (fun p hp i j => damped_covariance_bound D N C r hp.1 i j)
    (fun p hp i j => damped_covariance_bound D N R r hp.1 i j)
    (by
      intro p hp i
      rw [hm]
      exact damped_mixed_bound D N C m r hp.1 p.2.1 hp.2.1 i)
    (by
      intro p hp i
      rw [hl]
      exact damped_mixed_bound D N R l r hp.1 p.2.2 hp.2.2 i)
    (by
      intro p hp
      have hL : externalExponent (leftRow D N e p.1) (leftMean D a N e p.1) p.2.1 =
          externalExponent C m p.2.1 := by
        rw [hm]; simp [externalExponent, leftRow, damp, C]
      have hR : externalExponent (rightRow D N e p.1) (rightMean D a N e p.1) p.2.2 =
          externalExponent R l p.2.2 := by
        rw [hl]; simp [externalExponent, rightRow, damp, R, C]
      rw [hL, hR]
      apply (Complex.norm_exp_le_exp_norm _).trans
      apply Real.exp_le_exp.mpr
      exact (norm_add_le _ _).trans
        (add_le_add (external_bound C m p.2.1 hp.2.1) (external_bound R l p.2.2 hp.2.2)))
  exact ⟨r, hr, hr1, hmajor⟩

/-- Normal occupation convergence on the same fixed-cutoff closed source
polydisk, before either external or source coefficient extraction. -/
theorem original_occupation_normal_on_germ (D : LatticeData) (a : Charge D)
    (N : ℕ) (e : X → External D) :
    ∃ r : ℝ, 0 < r ∧ r < 1 ∧
      TendstoUniformlyOn
        (fun s : Finset (Internal D N →₀ ℕ) => fun p => ∑ d ∈ s, occupationTerm D a N e d p)
        (fun p => ∑' d, occupationTerm D a N e d p) Filter.atTop (sourcePolydisk (X := X) r) := by
  obtain ⟨r, hr, hr1, M, hM, hb⟩ := original_occupation_majorant_on_germ D a N e
  exact ⟨r, hr, hr1, tendstoUniformlyOn_tsum hM (fun d p hp => hb p hp d)⟩

private lemma affine_diagonal (I : Type*) [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (mu w : I → ℂ) (d : I →₀ ℕ) :
    affineCoefficient (fun i j => w i * A i j * w j) (fun i => w i * mu i) d =
      d.prod (fun i n => w i ^ n) * affineCoefficient A mu d := by
  let v : I ⊕ Unit → ℂ := Sum.elim w (fun _ => 1)
  have he : affineKernel (fun i j => w i * A i j * w j) (fun i => w i * mu i) =
      fun i j => v i * affineKernel A mu i j * v j := by
    ext i j
    cases i <;> cases j <;>
      simp [affineKernel, ElementaryGaussianContraction.leftKernel, Matrix.fromBlocks,
        Matrix.transpose, v, mul_comm]
  simp only [affineCoefficient, he, GaussianCoefficientScaling.finite_diagonal_congruence,
    Finsupp.prod_sumElim]
  simp only [v, Finsupp.prod_single_index, Sum.elim_inl, Sum.elim_inr, one_pow,
    mul_one, Function.comp_def]
  rw [← Finset.mul_sum]

/-- The finite occupation energy uses positive ordinary frequencies. -/
def internalEnergy (D : LatticeData) (N : ℕ) (d : Internal D N →₀ ℕ) : ℕ :=
  d.sum (fun i n => (i.2.val + 1) * n)

private lemma damp_product (D : LatticeData) (N : ℕ) (z : ℂ)
    (d : Internal D N →₀ ℕ) (h : X →₀ ℕ) :
    (d.sumElim h).prod (fun i n => damp D N z i ^ n) = z ^ internalEnergy D N d := by
  rw [Finsupp.prod_sumElim]
  simp only [damp, Sum.elim_inl, Sum.elim_inr, one_pow, mul_one,
    Function.comp_def]
  rw [show h.prod (fun _ _ => (1 : ℂ)) = 1 by simp, mul_one]
  change (∏ i ∈ d.support, (z ^ (i.2.val + 1)) ^ d i) = _
  simp_rw [← pow_mul]
  rw [Finset.prod_pow_eq_pow_sum]
  rfl

/-- Both full row coefficients have their exact internal energy power.
The external occupations remain in the native coefficient's full degree. -/
theorem original_row_coefficients_scale (D : LatticeData) (a : Charge D) (N : ℕ)
    (e : X → External D) (z : ℂ) (d : Internal D N →₀ ℕ) (h k : X →₀ ℕ) :
    affineCoefficient (leftRow D N e z) (leftMean D a N e z) (d.sumElim h) =
      z ^ internalEnergy D N d *
        affineCoefficient (originalRow D N e) (originalMean D a N e) (d.sumElim h) ∧
    affineCoefficient (rightRow D N e z) (rightMean D a N e z) (d.sumElim k) =
      z ^ internalEnergy D N d *
        affineCoefficient
          (transportCovariance (sourceBlock (J := X) (inverseSubstitution D N))
            (originalRow D N e)) (originalInverseMean D a N e) (d.sumElim k) := by
  constructor
  · rw [leftMean_raw]
    exact (affine_diagonal _ _ _ _ _).trans (by rw [damp_product])
  · rw [rightMean_raw]
    exact (affine_diagonal _ _ _ _ _).trans (by rw [damp_product])

/-- Exactly one internal factorial multiplies the two source rows, and their
total damping power is twice the internal energy, also at zero energy. -/
theorem original_row_product_scales (D : LatticeData) (a : Charge D) (N : ℕ)
    (e : X → External D) (z : ℂ) (d : Internal D N →₀ ℕ) (h k : X →₀ ℕ) :
    (FactorialFockMetric.weight d : ℂ) *
      affineCoefficient (leftRow D N e z) (leftMean D a N e z) (d.sumElim h) *
      affineCoefficient (rightRow D N e z) (rightMean D a N e z) (d.sumElim k) =
    z ^ (2 * internalEnergy D N d) * ((FactorialFockMetric.weight d : ℂ) *
      affineCoefficient (originalRow D N e) (originalMean D a N e) (d.sumElim h) *
      affineCoefficient
        (transportCovariance (sourceBlock (J := X) (inverseSubstitution D N))
          (originalRow D N e)) (originalInverseMean D a N e) (d.sumElim k)) := by
  rw [(original_row_coefficients_scale D a N e z d h k).1,
    (original_row_coefficients_scale D a N e z d h k).2]
  rw [show 2 * internalEnergy D N d = internalEnergy D N d + internalEnergy D N d by omega,
    pow_add]
  ring

/-- Literal undamped mixed external term. This is an algebraic source expression. -/
def rawOccupationTerm (D : LatticeData) (a : Charge D) (N : ℕ) (e : X → External D)
    (d : Internal D N →₀ ℕ) (x y : X → ℂ) : ℂ :=
  let C := originalRow D N e
  let R := transportCovariance (sourceBlock (J := X) (inverseSubstitution D N)) C
  let m := originalMean D a N e
  let l := originalInverseMean D a N e
  Complex.exp (externalExponent C m x + externalExponent R l y) *
    (FactorialFockMetric.weight d : ℂ) *
    affineCoefficient (C.submatrix Sum.inl Sum.inl) (mixedMean C m x) d *
    affineCoefficient (R.submatrix Sum.inl Sum.inl) (mixedMean R l y) d

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1000000 in
/-- The full mixed source term has precisely twice its occupation energy as
its ordinary source power; external coordinates and both full means remain literal. -/
theorem original_occupation_scales (D : LatticeData) (a : Charge D) (N : ℕ)
    (e : X → External D) (d : Internal D N →₀ ℕ) (z : ℂ) (x y : X → ℂ) :
    occupationTerm D a N e d (z, x, y) =
      z ^ (2 * internalEnergy D N d) * rawOccupationTerm D a N e d x y := by
  let C := originalRow D N e
  let R := transportCovariance (sourceBlock (J := X) (inverseSubstitution D N)) C
  let m := originalMean D a N e
  let l := originalInverseMean D a N e
  have hm := leftMean_raw D a N e z
  have hl := rightMean_raw D a N e z
  have hmix (K : Matrix (Internal D N ⊕ X) (Internal D N ⊕ X) ℂ)
      (v : Internal D N ⊕ X → ℂ) (t : X → ℂ) :
      mixedMean (fun i j => damp D N z i * K i j * damp D N z j)
        (fun i => damp D N z i * v i) t =
      fun i => z ^ (i.2.val + 1) * mixedMean K v t i := by
    funext i
    simp only [mixedMean, damp, mul_one, mul_add, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hpow : d.prod (fun i n => (z ^ (i.2.val + 1)) ^ n) =
      z ^ internalEnergy D N d := by
    change (∏ i ∈ d.support, (z ^ (i.2.val + 1)) ^ d i) = _
    simp_rw [← pow_mul]
    rw [Finset.prod_pow_eq_pow_sum]
    rfl
  have hq (K : Matrix (Internal D N ⊕ X) (Internal D N ⊕ X) ℂ)
      (v : Internal D N ⊕ X → ℂ) (t : X → ℂ) :
      externalExponent (fun i j => damp D N z i * K i j * damp D N z j)
        (fun i => damp D N z i * v i) t = externalExponent K v t := by
    simp [externalExponent, damp]
  have hleft :
      affineCoefficient ((leftRow D N e z).submatrix Sum.inl Sum.inl)
        (mixedMean (leftRow D N e z) (leftMean D a N e z) x) d =
      z ^ internalEnergy D N d *
        affineCoefficient (C.submatrix Sum.inl Sum.inl) (mixedMean C m x) d := by
    rw [hm]
    unfold leftRow
    rw [hmix]
    have hmat : (Matrix.submatrix
        (fun i j => damp D N z i * C i j * damp D N z j) Sum.inl Sum.inl) =
        fun i j => z ^ (i.2.val + 1) * C (.inl i) (.inl j) * z ^ (j.2.val + 1) := by
      ext i j
      rfl
    rw [hmat]
    exact (affine_diagonal (Internal D N) (C.submatrix Sum.inl Sum.inl)
      (mixedMean C m x) (fun i => z ^ (i.2.val + 1)) d).trans (by rw [hpow])
  have hright :
      affineCoefficient ((rightRow D N e z).submatrix Sum.inl Sum.inl)
        (mixedMean (rightRow D N e z) (rightMean D a N e z) y) d =
      z ^ internalEnergy D N d *
        affineCoefficient (R.submatrix Sum.inl Sum.inl) (mixedMean R l y) d := by
    rw [hl]
    unfold rightRow
    rw [hmix]
    have hmat : (Matrix.submatrix
        (fun i j => damp D N z i * R i j * damp D N z j) Sum.inl Sum.inl) =
        fun i j => z ^ (i.2.val + 1) * R (.inl i) (.inl j) * z ^ (j.2.val + 1) := by
      ext i j
      rfl
    rw [hmat]
    exact (affine_diagonal (Internal D N) (R.submatrix Sum.inl Sum.inl)
      (mixedMean R l y) (fun i => z ^ (i.2.val + 1)) d).trans (by rw [hpow])
  have hqleft : externalExponent (leftRow D N e z) (leftMean D a N e z) x =
      externalExponent C m x := by
    rw [hm]
    exact hq C m x
  have hqright : externalExponent (rightRow D N e z) (rightMean D a N e z) y =
      externalExponent R l y := by
    rw [hl]
    exact hq R l y
  unfold occupationTerm
  rw [hqleft, hqright, hleft, hright]
  change Complex.exp (externalExponent C m x + externalExponent R l y) *
      (FactorialFockMetric.weight d : ℂ) *
      (z ^ internalEnergy D N d *
        affineCoefficient (C.submatrix Sum.inl Sum.inl) (mixedMean C m x) d) *
      (z ^ internalEnergy D N d *
        affineCoefficient (R.submatrix Sum.inl Sum.inl) (mixedMean R l y) d) =
    z ^ (2 * internalEnergy D N d) *
      (Complex.exp (externalExponent C m x + externalExponent R l y) *
        (FactorialFockMetric.weight d : ℂ) *
        affineCoefficient (C.submatrix Sum.inl Sum.inl) (mixedMean C m x) d *
        affineCoefficient (R.submatrix Sum.inl Sum.inl) (mixedMean R l y) d)
  rw [show 2 * internalEnergy D N d = internalEnergy D N d + internalEnergy D N d by omega,
    pow_add]
  ring

lemma original_rows_symm (D : LatticeData) (N : ℕ) (e : X → External D) (z : ℂ) :
    (∀ i j, leftRow D N e z i j = leftRow D N e z j i) ∧
    (∀ i j, rightRow D N e z i j = rightRow D N e z j i) := by
  have hC : ∀ i j, originalRow D N e i j = originalRow D N e j i := by
    intro i j
    dsimp only [originalRow, Matrix.submatrix_apply]
    exact corrected_symmetry_on_pair D _ _
  have hR := transportCovariance_symm
    (sourceBlock (J := X) (inverseSubstitution D N)) (originalRow D N e) hC
  constructor
  · intro i j; unfold leftRow; rw [hC j i]; ring
  · intro i j; unfold rightRow; rw [hR j i]; ring

/-- The exact finite sewn exponent before collecting its external quadratic,
linear and constant parts. Both means are the original actual mixed means. -/
def finiteMixedExponent (D : LatticeData) (a : Charge D) (N : ℕ) (e : X → External D)
    (p : ℂ × (X → ℂ) × (X → ℂ)) : ℂ :=
  let A := (leftRow D N e p.1).submatrix Sum.inl Sum.inl
  let B := (rightRow D N e p.1).submatrix Sum.inl Sum.inl
  let μ := mixedMean (leftRow D N e p.1) (leftMean D a N e p.1) p.2.1
  let ν := mixedMean (rightRow D N e p.1) (rightMean D a N e p.1) p.2.2
  externalExponent (leftRow D N e p.1) (leftMean D a N e p.1) p.2.1 +
    externalExponent (rightRow D N e p.1) (rightMean D a N e p.1) p.2.2 +
    (1 / 2 : ℂ) * ∑ x, ∑ y,
      FiniteGaussianSewing.effectiveKernel (0 : Matrix Unit Unit ℂ) (0 : Matrix Unit Unit ℂ)
        A B (fun _ i => μ i) (fun i _ => ν i) x y

/-- Finite affine sewing and normal convergence hold on one common fixed-N
germ. The equality retains the actual external dependence before extraction. -/
theorem original_occupation_sewing_on_germ (D : LatticeData) (hu : IsUnit D.G.det)
    (a : Charge D) (N : ℕ) (e : X → External D) :
    ∃ r : ℝ, 0 < r ∧ r < 1 ∧
      TendstoUniformlyOn
        (fun s : Finset (Internal D N →₀ ℕ) => fun p => ∑ d ∈ s, occupationTerm D a N e d p)
        (fun p => ∑' d, occupationTerm D a N e d p) Filter.atTop (sourcePolydisk (X := X) r) ∧
      ∀ p ∈ sourcePolydisk (X := X) r,
        (∑' d, occupationTerm D a N e d p) =
          Complex.exp (-(D.rank : ℂ) / 2 * OriginalGaussianDeterminant.finiteLog N p.1) *
            Complex.exp (finiteMixedExponent D a N e p) := by
  obtain ⟨r, hr, hr1, hn⟩ := original_occupation_normal_on_germ D a N e
  obtain ⟨s, hs, hs1, hc⟩ := original_rows_contract_on_germ D N e
  have hsub : sourcePolydisk (X := X) (min r s) ⊆ sourcePolydisk (X := X) r :=
    fun p hp => ⟨hp.1.trans (min_le_left _ _), hp.2⟩
  refine ⟨min r s, lt_min hr hs, (min_le_left _ _).trans_lt hr1, hn.mono hsub, ?_⟩
  intro p hp
  have hc' := hc p.1 (hp.1.trans (min_le_right _ _))
  have hsym := original_rows_symm D N e p.1
  let A := (leftRow D N e p.1).submatrix Sum.inl Sum.inl
  let B := (rightRow D N e p.1).submatrix Sum.inl Sum.inl
  let μ := mixedMean (leftRow D N e p.1) (leftMean D a N e p.1) p.2.1
  let ν := mixedMean (rightRow D N e p.1) (rightMean D a N e p.1) p.2.2
  let q := externalExponent (leftRow D N e p.1) (leftMean D a N e p.1) p.2.1 +
    externalExponent (rightRow D N e p.1) (rightMean D a N e p.1) p.2.2
  have ht := (FiniteAffineGaussianSewing.finite_affine_sewing A B μ ν
    (fun i j => hsym.1 (.inl i) (.inl j)) (fun i j => hsym.2 (.inl i) (.inl j))
    hc'.1 hc'.2.1).2
  have hpref := original_rows_trace_prefactor D hu N e p.1
  change (∑' d, Complex.exp q * (FactorialFockMetric.weight d : ℂ) *
    affineCoefficient A μ d * affineCoefficient B ν d) = _
  simp_rw [show ∀ d, Complex.exp q * (FactorialFockMetric.weight d : ℂ) *
      affineCoefficient A μ d * affineCoefficient B ν d =
      Complex.exp q * ((FactorialFockMetric.weight d : ℂ) *
        affineCoefficient A μ d * affineCoefficient B ν d) by intro d; ring]
  rw [tsum_mul_left, ht]
  change Complex.exp q * (_ * _) = _
  rw [hpref]
  simp only [finiteMixedExponent, q, A, B, μ, ν, Complex.exp_add]
  ring

end D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianSourceGerm
