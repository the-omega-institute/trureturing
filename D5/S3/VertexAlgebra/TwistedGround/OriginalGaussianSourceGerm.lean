/- GID: D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianSourceGerm
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/OriginalGaussianSourceGerm
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Fixed-cutoff contraction germs for original source rows and positive comparisons. -/

import D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianSourceMeans
import D5.S3.VertexAlgebra.TwistedGround.FiniteAffineGaussianSewing

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

end D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianSourceGerm
