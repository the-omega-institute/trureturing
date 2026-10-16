/- GID: D5/S3/Quantum/Entanglement/TavakoliMorelliIncompleteEAM
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/TavakoliMorelliIncompleteEAM
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Incomplete equiangular measurements and Schmidt-number correlation bounds. -/

import D5.S3.Quantum.Foundation.FiniteDensityPurification
import D5.S3.Quantum.Entanglement.ConicalDesignConcurrenceComparability
import D5.S3.Quantum.Analysis.TraceClass.IdealNorm
import D5.S3.Quantum.GNSMatrix
import D5.S3.Quantum.Matrix.CartesianVariance
import D5.S3.Quantum.PureState.PureStateHandshake
import D5.S3.QuadraticForms.GerzonEqualityParameterIdentity
import D5.S3.Quantum.Tomography.PurityPythagorasDecomposition

noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder InnerProductSpace
open Matrix
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000
open D5.S3.Quantum.Foundation.FiniteTraceDistance

namespace D5.S3.Quantum.Entanglement.TavakoliMorelliIncompleteEAM

abbrev Op (d : ℕ) := Matrix (Fin d) (Fin d) ℂ
abbrev BipartiteOp (d : ℕ) := Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ
abbrev proj {ι : Type*} [Fintype ι] [DecidableEq ι] (u : Ket ι) : Matrix ι ι ℂ :=
  (MState.pure u).m

def coeff {d : ℕ} (u : Ket (Fin d × Fin d)) : Op d :=
  Matrix.of fun i j => u.vec (i, j)

def SchmidtNumberLE {d : ℕ} (ρ : BipartiteOp d) (r : ℕ) : Prop :=
  ∃ (N : ℕ) (p : Fin N → ℝ) (u : Fin N → Ket (Fin d × Fin d)),
    (∀ k, 0 ≤ p k) ∧ (∑ k, p k) = 1 ∧
    (∀ k, (coeff (u k)).rank ≤ r) ∧ ρ = ∑ k, (p k : ℂ) • proj (u k)

def correlation {d : ℕ} {κ : Type*} [Fintype κ]
    (ρ : BipartiteOp d) (A B : κ → Op d) : Matrix κ κ ℂ :=
  Matrix.of fun a b => (((ρ * Matrix.kronecker (A a) (B b)).trace).re : ℂ)

def hsSq {ι κ : Type*} [Fintype ι] [Fintype κ] (A : Matrix ι κ ℂ) : ℝ :=
  ∑ i, ∑ j, ‖A i j‖ ^ 2

def moment {d : ℕ} {κ : Type*} [Fintype κ] (A : κ → Op d) (H : Op d) : ℝ :=
  ∑ a, ((H * A a).trace.re) ^ 2

def ScaledPure {d : ℕ} (A : Op d) : Prop :=
  ∃ (c : ℝ) (u : Ket (Fin d)), 0 ≤ c ∧ A = (c : ℂ) • proj u

def MomentBound {d : ℕ} {κ : Type*} [Fintype κ]
    (A : κ → Op d) (α β : ℝ) : Prop :=
  ∀ H : Op d, H.IsHermitian →
    moment A H ≤ α * (H * H).trace.re + β * (H.trace.re) ^ 2

def EAM (d n : ℕ) :=
  {ket : Fin n → Ket (Fin d) // d < n ∧
    (∑ a, proj (ket a)) = ((n : ℂ) / (d : ℂ)) • (1 : Op d) ∧
    ∀ a b, a ≠ b → ‖dotProduct (star (ket a).vec) (ket b).vec‖ ^ 2 =
      ((n : ℝ) - (d : ℝ)) / ((d : ℝ) * ((n : ℝ) - 1))}

def EAM.effect {d n : ℕ} (A : EAM d n) (a : Fin n) : Op d :=
  ((d : ℂ) / (n : ℂ)) • proj (A.val a)

def Pn {d n : ℕ} (ρ : BipartiteOp d) (A B : EAM d n) : Matrix (Fin n) (Fin n) ℂ :=
  correlation ρ A.effect B.effect

theorem trace_toEuclideanCLM {κ : Type*} [Fintype κ] [DecidableEq κ]
    (A : Matrix κ κ ℂ) :
    LinearMap.trace ℂ (EuclideanSpace ℂ κ) (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := κ) A).toLinearMap =
      A.trace := by
  change LinearMap.trace ℂ _ (Matrix.toEuclideanLin A) = _
  rw [Matrix.toEuclideanLin_eq_toLin_orthonormal, Matrix.trace_toLin_eq]

theorem traceNorm_toEuclideanCLM {κ : Type*} [Fintype κ] [DecidableEq κ]
    (A : Matrix κ κ ℂ) :
    D5.S3.Quantum.Foundation.FiniteTraceDistance.traceNorm A =
      _root_.traceNorm (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := κ) A)
        (isTraceClass_of_finiteDimensional _) := by
  let Φ := Matrix.toEuclideanCLM (n := κ) (𝕜 := ℂ)
  have hsqrt : CFC.abs (Φ A) = Φ (CFC.sqrt (Aᴴ * A)) := by
    change CFC.sqrt (star (Φ A) * Φ A) = _
    apply CFC.sqrt_unique
    · rw [← map_mul, CFC.sqrt_mul_sqrt_self _ (Matrix.posSemidef_conjTranspose_mul_self A).nonneg]
      simp only [← Matrix.star_eq_conjTranspose, map_mul, map_star]
    · exact map_nonneg Φ (CFC.sqrt_nonneg _)
  obtain ⟨w, b, _⟩ := exists_hilbertBasis ℂ (EuclideanSpace ℂ κ)
  let : Finite w := b.orthonormal.linearIndependent.finite
  let : Fintype w := Fintype.ofFinite w
  rw [_root_.traceNorm_eq_of_hilbertBasis _ b]
  change (CFC.sqrt (Aᴴ * A)).trace.re = _
  rw [hsqrt, tsum_fintype, ← Complex.re_sum]
  rw [← trace_toEuclideanCLM (CFC.sqrt (Aᴴ * A)),
    trace_eq_sum_inner_hilbertBasis_of_finiteDimensional _ b, tsum_fintype]


theorem hsSq_toEuclideanCLM {κ : Type*} [Fintype κ] [DecidableEq κ]
    (A : Matrix κ κ ℂ) {s : Set (EuclideanSpace ℂ κ)}
    (b : HilbertBasis s ℂ (EuclideanSpace ℂ κ)) :
    (∑' i : s, ‖Matrix.toEuclideanCLM (𝕜 := ℂ) A (b i)‖ ^ 2) = hsSq A := by
  let : Finite s := b.orthonormal.linearIndependent.finite
  let : Fintype s := Fintype.ofFinite s
  let T := Matrix.toEuclideanCLM (𝕜 := ℂ) A
  have hsum : (∑' i : s, ‖T (b i)‖ ^ 2) =
      (LinearMap.trace ℂ _ (star T * T).toLinearMap).re := by
    rw [trace_eq_sum_inner_hilbertBasis_of_finiteDimensional _ b,
      tsum_fintype, tsum_fintype, Complex.re_sum]
    apply Finset.sum_congr rfl
    intro i _
    simpa only [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.mul_def, RCLike.re_eq_complex_re] using
      ContinuousLinearMap.apply_norm_sq_eq_inner_adjoint_right (𝕜 := ℂ) T (b i)
  rw [hsum]
  change (LinearMap.trace ℂ _
    (star (Matrix.toEuclideanCLM (𝕜 := ℂ) A) *
      Matrix.toEuclideanCLM (𝕜 := ℂ) A).toLinearMap).re = _
  rw [← map_star, ← map_mul, trace_toEuclideanCLM]
  open scoped Matrix.Norms.Frobenius in
    have htrace := congrArg Complex.re
      (D5.S3.Quantum.GNSMatrix.frobenius_norm_sq_eq_trace A)
    rw [Complex.ofReal_re] at htrace
    rw [Matrix.star_eq_conjTranspose, ← htrace]
    change ‖WithLp.toLp 2 (fun i => WithLp.toLp 2 (A i))‖ ^ 2 = _
    simp only [PiLp.norm_sq_eq_of_L2, hsSq]

theorem traceNorm_mul_le_hsSq {κ : Type*} [Fintype κ] [DecidableEq κ]
    (R S : Matrix κ κ ℂ) :
    D5.S3.Quantum.Foundation.FiniteTraceDistance.traceNorm (R * S) ≤
      Real.sqrt (hsSq R) * Real.sqrt (hsSq S) := by
  obtain ⟨w, b, _⟩ := exists_hilbertBasis ℂ (EuclideanSpace ℂ κ)
  let : Finite w := b.orthonormal.linearIndependent.finite
  let : Fintype w := Fintype.ofFinite w
  have hR : HilbertSchmidt.IsHilbertSchmidt (Matrix.toEuclideanCLM (𝕜 := ℂ) R) :=
    ⟨w, b, (hasSum_fintype _).summable⟩
  have hS : HilbertSchmidt.IsHilbertSchmidt (Matrix.toEuclideanCLM (𝕜 := ℂ) S) :=
    ⟨w, b, (hasSum_fintype _).summable⟩
  have h := _root_.traceNorm_mul_le_of_isHilbertSchmidt hR hS
    (isTraceClass_of_finiteDimensional _) b
  rw [traceNorm_toEuclideanCLM, map_mul]
  simpa only [hsSq_toEuclideanCLM] using h

theorem traceNorm_gram_le {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (F G : Matrix ι κ ℂ) :
    D5.S3.Quantum.Foundation.FiniteTraceDistance.traceNorm (Fᴴ * G) ≤
      Real.sqrt (hsSq F) * Real.sqrt (hsSq G) := by
  let R : Matrix (κ ⊕ ι) (κ ⊕ ι) ℂ := fromBlocks 0 Fᴴ 0 0
  let S : Matrix (κ ⊕ ι) (κ ⊕ ι) ℂ := fromBlocks 0 0 G 0
  let J : Matrix (κ ⊕ ι) κ ℂ := fromRows 1 0
  have hJ : Jᴴ * J = 1 := by
    simp only [J, conjTranspose_fromRows_eq_fromCols_conjTranspose,
      conjTranspose_one, conjTranspose_zero, fromCols_mul_fromRows,
      Matrix.one_mul, Matrix.zero_mul, add_zero]
  have hprod : R * S = J * (Fᴴ * G) * Jᴴ := by
    simp only [R, S, J, fromBlocks_multiply, Matrix.zero_mul, Matrix.mul_zero,
      zero_add, add_zero, fromRows_mul, Matrix.one_mul,
      conjTranspose_fromRows_eq_fromCols_conjTranspose, conjTranspose_one,
      conjTranspose_zero, mul_fromCols, Matrix.mul_one, Matrix.mul_zero,
      ]
    ext i j <;> cases i <;> cases j <;> rfl
  have hR : hsSq R = hsSq F := by
    simp only [hsSq, R, Fintype.sum_sum_type, fromBlocks_apply₁₁,
      fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂,
      Matrix.zero_apply, norm_zero, zero_pow (by decide : 2 ≠ 0),
      Finset.sum_const_zero, add_zero, zero_add, conjTranspose_apply, norm_star]
    exact Finset.sum_comm
  have hS : hsSq S = hsSq G := by
    simp only [hsSq, S, Fintype.sum_sum_type, fromBlocks_apply₁₁,
      fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂,
      Matrix.zero_apply, norm_zero, zero_pow (by decide : 2 ≠ 0),
      Finset.sum_const_zero, add_zero, zero_add]
  have h := traceNorm_mul_le_hsSq R S
  rw [hprod, ConicalDesignConcurrenceComparability.traceNorm_isometry J hJ,
    hR, hS] at h
  exact h

theorem correlation_sum_smul {d : ℕ} {κ ι : Type*} [Fintype κ] [Fintype ι]
    (p : ι → ℝ) (ρ : ι → BipartiteOp d) (A B : κ → Op d) :
    correlation (∑ i, (p i : ℂ) • ρ i) A B =
      ∑ i, (p i : ℂ) • correlation (ρ i) A B := by
  ext a b
  simp only [correlation, Matrix.of_apply, Matrix.sum_mul, Matrix.trace_sum,
    Matrix.smul_mul, Matrix.trace_smul, Complex.re_sum, Matrix.sum_apply,
    Matrix.smul_apply, smul_eq_mul, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero, Complex.ofReal_sum, Complex.ofReal_mul]

theorem sum_sq_le_of_support_card {d r : ℕ} (sval : Fin d → ℝ)
    (hunit : (∑ i, sval i ^ 2) = 1)
    (hcard : Fintype.card {i : Fin d // sval i ≠ 0} ≤ r) :
    (∑ i, sval i) ^ 2 ≤ (r : ℝ) := by
  classical
  let s := Finset.univ.filter (fun i => sval i ≠ 0)
  have hsum : ∑ i ∈ s, sval i = ∑ i, sval i := by
    exact Finset.sum_filter_ne_zero _
  have hsumSq : ∑ i ∈ s, sval i ^ 2 = 1 := by
    rw [← hunit]
    exact Finset.sum_subset (Finset.filter_subset _ _)
      (fun i _ hi => by
        simp only [s, Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hi
        rw [hi, zero_pow (by decide)])
  have hsize : s.card ≤ r := by
    simpa only [s, Fintype.card_subtype, Finset.card_univ] using hcard
  calc
    (∑ i, sval i) ^ 2 = (∑ i ∈ s, sval i) ^ 2 := by rw [hsum]
    _ ≤ (s.card : ℝ) * ∑ i ∈ s, sval i ^ 2 := sq_sum_le_card_mul_sum_sq
    _ ≤ (r : ℝ) := by rw [hsumSq, mul_one]; exact_mod_cast hsize

theorem eam_effect_scaledPure {d n : ℕ} (A : EAM d n) (a : Fin n) :
    ScaledPure (A.effect a) := by
  refine ⟨(d : ℝ) / n, A.val a, by positivity, ?_⟩
  simp only [EAM.effect, Complex.ofReal_div, Complex.ofReal_natCast]


def claim : Prop :=
  ∀ (d n r : ℕ), 1 ≤ d → 1 ≤ r → r ≤ d →
    ∀ (A B : EAM d n) (ρ : BipartiteOp d), SchmidtNumberLE ρ r →
      D5.S3.Quantum.Foundation.FiniteTraceDistance.traceNorm (Pn ρ A B) ≤
        ((d : ℝ) * ((d : ℝ) - 1) + (r : ℝ) * ((n : ℝ) - (d : ℝ))) /
          ((n : ℝ) * ((n : ℝ) - 1))

end D5.S3.Quantum.Entanglement.TavakoliMorelliIncompleteEAM
