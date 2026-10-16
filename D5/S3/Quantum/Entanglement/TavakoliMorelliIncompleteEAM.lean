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

abbrev EAM (d n : ℕ) :=
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
    LinearMap.trace ℂ (EuclideanSpace ℂ κ)
      (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := κ) A).toLinearMap =
      A.trace := by
  change LinearMap.trace ℂ _ (Matrix.toEuclideanLin A) = _
  rw [Matrix.toEuclideanLin_eq_toLin_orthonormal, Matrix.trace_toLin_eq]

set_option synthInstance.maxHeartbeats 200000 in
-- Functional calculus on endomorphisms uses both real and complex scalar towers.
theorem traceNorm_toEuclideanCLM {κ : Type*} [Fintype κ] [DecidableEq κ]
    (A : Matrix κ κ ℂ) :
    D5.S3.Quantum.Foundation.FiniteTraceDistance.traceNorm A =
      _root_.traceNorm (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := κ) A)
        (isTraceClass_of_finiteDimensional _) := by
  let Φ := Matrix.toEuclideanCLM (n := κ) (𝕜 := ℂ)
  have hsqrt : CFC.abs (Φ A) = Φ (CFC.sqrt (Aᴴ * A)) := by
    change CFC.sqrt (star (Φ A) * Φ A) = _
    apply CFC.sqrt_unique
    · rw [← map_mul,
        CFC.sqrt_mul_sqrt_self _ (Matrix.posSemidef_conjTranspose_mul_self A).nonneg]
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

theorem hsSq_eq_trace {κ : Type*} [Fintype κ] (A : Matrix κ κ ℂ) :
    hsSq A = (Aᴴ * A).trace.re := by
  open scoped Matrix.Norms.Frobenius in
    have htrace := congrArg Complex.re
      (D5.S3.Quantum.GNSMatrix.frobenius_norm_sq_eq_trace A)
    rw [Complex.ofReal_re] at htrace
    rw [← htrace]
    change _ = ‖WithLp.toLp 2 (fun i => WithLp.toLp 2 (A i))‖ ^ 2
    simp only [PiLp.norm_sq_eq_of_L2, hsSq]

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
    simpa only [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.mul_def,
      RCLike.re_eq_complex_re] using
      ContinuousLinearMap.apply_norm_sq_eq_inner_adjoint_right (𝕜 := ℂ) T (b i)
  rw [hsum]
  change (LinearMap.trace ℂ _
    (star (Matrix.toEuclideanCLM (𝕜 := ℂ) A) *
      Matrix.toEuclideanCLM (𝕜 := ℂ) A).toLinearMap).re = _
  rw [← map_star, ← map_mul, trace_toEuclideanCLM]
  rw [Matrix.star_eq_conjTranspose, ← hsSq_eq_trace]

theorem traceNorm_mul_le_hsSq {κ : Type*} [Fintype κ]
    (R S : Matrix κ κ ℂ) :
    D5.S3.Quantum.Foundation.FiniteTraceDistance.traceNorm (R * S) ≤
      Real.sqrt (hsSq R) * Real.sqrt (hsSq S) := by
  classical
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
    [Fintype ι] [Fintype κ]
    (F G : Matrix ι κ ℂ) :
    D5.S3.Quantum.Foundation.FiniteTraceDistance.traceNorm (Fᴴ * G) ≤
      Real.sqrt (hsSq F) * Real.sqrt (hsSq G) := by
  classical
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
      conjTranspose_zero, mul_fromCols, Matrix.mul_one]
    ext i j
    cases i <;> cases j <;> rfl
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

theorem ket_dot_self {ι : Type*} [Fintype ι] (u : Ket ι) :
    star u.vec ⬝ᵥ u.vec = 1 := by
  rw [dotProduct]
  simpa only [Pi.star_apply, Complex.star_def, ← Complex.normSq_eq_conj_mul_self,
    ← Complex.ofReal_sum, Complex.ofReal_one, Ket.apply] using
    congrArg Complex.ofReal (Ket.normalized u)

theorem proj_eq_outer {ι : Type*} [Fintype ι] [DecidableEq ι] (u : Ket ι) :
    proj u = vecMulVec u.vec (star u.vec) := by
  ext i j
  exact MState.pure_apply u

theorem pure_born_coeff {d : ℕ} (u : Ket (Fin d × Fin d)) (A B : Op d) :
    (proj u * Matrix.kronecker A B).trace =
      ((coeff u)ᴴ * A * coeff u * Bᵀ).trace := by
  rw [proj_eq_outer]
  rw [D5.S3.Quantum.BlockNorm.EssentiallyHermitian.outer_pairing_trace
    _ (WithLp.toLp 2 u.vec)]
  rw [EuclideanSpace.inner_eq_star_dotProduct, Matrix.ofLp_toEuclideanCLM]
  rw [dotProduct_comm]
  change star (vec (coeff u)ᵀ) ⬝ᵥ ((Matrix.kronecker A B) *ᵥ vec (coeff u)ᵀ) = _
  simp only [Matrix.kronecker]
  rw [kronecker_mulVec_vec, star_vec_dotProduct_vec]
  rw [← trace_transpose]
  simp only [transpose_mul, transpose_transpose, conjTranspose_transpose]
  rw [trace_mul_comm]
  simp only [Matrix.mul_assoc]
  rfl

theorem coeff_normalized {d : ℕ} (u : Ket (Fin d × Fin d)) :
    ((coeff u)ᴴ * coeff u).trace.re = 1 := by
  rw [← hsSq_eq_trace]
  simpa only [hsSq, coeff, Matrix.of_apply, Fintype.sum_prod_type] using u.normalized'

theorem exists_normalized_svd {d r : ℕ} (u : Ket (Fin d × Fin d))
    (hr : (coeff u).rank ≤ r) :
    ∃ (U V : Matrix.unitaryGroup (Fin d) ℂ) (sval : Fin d → ℝ),
      (∀ i, 0 ≤ sval i) ∧
      coeff u = U.val * Matrix.diagonal (fun i => (sval i : ℂ)) * V.valᴴ ∧
      (∑ i, sval i ^ 2) = 1 ∧
      Fintype.card {i : Fin d // sval i ≠ 0} ≤ r := by
  let hH : ((coeff u)ᴴ * coeff u).IsHermitian :=
    Matrix.isHermitian_conjTranspose_mul_self _
  let sval := fun i => Real.sqrt (hH.eigenvalues i)
  let D : Op d := diagonal (fun i => (sval i : ℂ))
  obtain ⟨U, V, hUV⟩ := exists_svd_sqrt_eigenvalues (coeff u)
  change coeff u = U.val * diagonal (fun i => (sval i : ℂ)) * V.valᴴ at hUV
  refine ⟨U, V, sval, fun i => Real.sqrt_nonneg _, hUV, ?_, ?_⟩
  · have hU : U.valᴴ * U.val = 1 := Unitary.star_mul_self_of_mem U.prop
    have hV : V.valᴴ * V.val = 1 := Unitary.star_mul_self_of_mem V.prop
    have hsquare : ((coeff u)ᴴ * coeff u).trace =
        (Dᴴ * D).trace := by
      change coeff u = U.val * D * V.valᴴ at hUV
      rw [hUV]
      simp only [conjTranspose_mul, conjTranspose_conjTranspose]
      calc
        _ = (V.val * Dᴴ * (U.valᴴ * U.val) * D * V.valᴴ).trace := by
          simp only [Matrix.mul_assoc]
        _ = (V.val * (Dᴴ * D) * V.valᴴ).trace := by
          rw [hU]; simp only [Matrix.mul_one, Matrix.mul_assoc]
        _ = _ := by rw [trace_mul_cycle, hV, Matrix.one_mul]
    have hnorm := coeff_normalized u
    rw [hsquare] at hnorm
    simpa only [D, diagonal_conjTranspose, diagonal_mul_diagonal,
      trace_diagonal, Pi.star_apply, Complex.star_def, Complex.conj_ofReal,
      Complex.re_sum, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, sub_zero, pow_two] using hnorm
  · have hrank : (coeff u).rank =
        Fintype.card {i : Fin d // sval i ≠ 0} := by
      rw [hUV, rank_mul_eq_left_of_isUnit_det V.valᴴ _
        (by rw [det_conjTranspose]; exact (Matrix.UnitaryGroup.det_isUnit V).star),
        rank_mul_eq_right_of_isUnit_det U.val _ (Matrix.UnitaryGroup.det_isUnit U),
        rank_diagonal]
      exact Fintype.card_congr (Equiv.subtypeEquivRight (fun i => by simp))
    rwa [hrank] at hr

theorem scaledPure_hermitian {d : ℕ} {A : Op d} (hA : ScaledPure A) :
    A.IsHermitian := by
  obtain ⟨c, u, _, rfl⟩ := hA
  exact (MState.Hermitian (MState.pure u)).smul (by simp [isSelfAdjoint_iff])

theorem scaledPure_sandwich {d : ℕ} {A : Op d} (hA : ScaledPure A) (M : Op d) :
    A * M * A = (M * A).trace • A := by
  obtain ⟨c, u, _, rfl⟩ := hA
  have h := (D5.S3.Quantum.PureState.PureStateHandshake.pure_state_handshake
    u.vec (ket_dot_self u) M).2
  have hs : proj u * M * proj u = (M * proj u).trace • proj u := by
    simpa only [proj_eq_outer,
      D5.S3.Quantum.PureState.PureStateHandshake.rankOneDensity, h.2] using h.1
  simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_smul, hs, smul_smul,
    smul_eq_mul]
  congr 1
  ring

theorem scaledPure_gram_norm {d : ℕ} {A : Op d} (hA : ScaledPure A) (K : Op d) :
    hsSq (K * A * Kᴴ) = (((Kᴴ * K) * A).trace.re) ^ 2 := by
  have hX : (K * A * Kᴴ).IsHermitian :=
    Matrix.isHermitian_mul_mul_conjTranspose K (scaledPure_hermitian hA)
  have ht : (K * A * Kᴴ).trace = ((Kᴴ * K) * A).trace :=
    Matrix.trace_mul_cycle K A Kᴴ
  have hsquare : ((K * A * Kᴴ) * (K * A * Kᴴ)).trace =
      (((Kᴴ * K) * A).trace) ^ 2 := by
    have heq : (K * A * Kᴴ) * (K * A * Kᴴ) =
        K * (A * (Kᴴ * K) * A) * Kᴴ := by simp only [Matrix.mul_assoc]
    rw [heq, scaledPure_sandwich hA, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.trace_smul, smul_eq_mul, ht, pow_two]
  rw [hsSq_eq_trace, hX.eq, hsquare]
  rw [D5.S3.Quantum.Tomography.PurityPythagorasDecomposition.trace_mul_real_of_hermitian
    _ _ (Matrix.isHermitian_conjTranspose_mul_self K) (scaledPure_hermitian hA)]
  norm_cast

def sandwichFactor {d : ℕ} {κ : Type*} (K : Op d) (A : κ → Op d) :
    Matrix (Fin d × Fin d) κ ℂ := fun p a => Matrix.vec (K * A a * Kᴴ) p

def schmidtSandwich {d : ℕ} (U : Matrix.unitaryGroup (Fin d) ℂ) (sval : Fin d → ℝ) :
    Op d := CFC.sqrt (diagonal (fun i => (sval i : ℂ))) * U.valᴴ

theorem sandwichFactor_hsSq {d : ℕ} {κ : Type*} [Fintype κ]
    (K : Op d) (A : κ → Op d) (hA : ∀ a, ScaledPure (A a)) :
    hsSq (sandwichFactor K A) = moment A (Kᴴ * K) := by
  calc
    hsSq (sandwichFactor K A) = ∑ a, hsSq (K * A a * Kᴴ) := by
      simp only [hsSq, sandwichFactor]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a _
      simp only [Fintype.sum_prod_type, Matrix.vec]
      exact Finset.sum_comm
    _ = moment A (Kᴴ * K) := by
      simp only [scaledPure_gram_norm (hA _), moment]

theorem scaledPure_transpose {d : ℕ} {A : Op d} (hA : ScaledPure A) :
    ScaledPure Aᵀ := by
  obtain ⟨c, u, hc, rfl⟩ := hA
  let v : Ket (Fin d) := ⟨star u.vec, by
    simpa only [Pi.star_apply, norm_star] using u.normalized'⟩
  refine ⟨c, v, hc, ?_⟩
  rw [transpose_smul, proj_eq_outer, proj_eq_outer, transpose_vecMulVec]
  change (c : ℂ) • vecMulVec (star u.vec) u.vec =
    (c : ℂ) • vecMulVec (star u.vec) (star (star u.vec))
  rw [star_star]

theorem schmidtSandwich_weight {d : ℕ} (U : Matrix.unitaryGroup (Fin d) ℂ)
    (sval : Fin d → ℝ) (hs : ∀ i, 0 ≤ sval i) :
    (schmidtSandwich U sval)ᴴ * schmidtSandwich U sval =
      U.val * diagonal (fun i => (sval i : ℂ)) * U.valᴴ := by
  let D : Op d := diagonal (fun i => (sval i : ℂ))
  have hD : D.PosSemidef := PosSemidef.diagonal (fun i => by
    change (0 : ℂ) ≤ (sval i : ℂ)
    exact_mod_cast hs i)
  have hS : (CFC.sqrt D).IsHermitian :=
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg D)).1
  change (CFC.sqrt D * U.valᴴ)ᴴ * (CFC.sqrt D * U.valᴴ) = U.val * D * U.valᴴ
  rw [conjTranspose_mul, conjTranspose_conjTranspose, hS.eq]
  calc
    _ = U.val * (CFC.sqrt D * CFC.sqrt D) * U.valᴴ := by simp only [mul_assoc]
    _ = _ := by rw [CFC.sqrt_mul_sqrt_self D hD.nonneg]

theorem schmidtSandwich_moments {d : ℕ} (U : Matrix.unitaryGroup (Fin d) ℂ)
    (sval : Fin d → ℝ) (hs : ∀ i, 0 ≤ sval i) :
    let H := (schmidtSandwich U sval)ᴴ * schmidtSandwich U sval
    H.trace.re = ∑ i, sval i ∧ (H * H).trace.re = ∑ i, sval i ^ 2 := by
  dsimp only
  rw [schmidtSandwich_weight U sval hs]
  let D : Op d := diagonal (fun i => (sval i : ℂ))
  have hU : U.valᴴ * U.val = 1 := Unitary.star_mul_self_of_mem U.prop
  have htrace : (U.val * D * U.valᴴ).trace = D.trace := by
    rw [trace_mul_cycle, hU, Matrix.one_mul]
  have hsquare : ((U.val * D * U.valᴴ) * (U.val * D * U.valᴴ)).trace =
      (D * D).trace := by
    calc
      _ = (U.val * D * (U.valᴴ * U.val) * D * U.valᴴ).trace := by
        simp only [mul_assoc]
      _ = (U.val * (D * D) * U.valᴴ).trace := by
        rw [hU]; simp only [Matrix.mul_one, mul_assoc]
      _ = _ := by rw [trace_mul_cycle, hU, Matrix.one_mul]
  change (U.val * D * U.valᴴ).trace.re = _ ∧
    ((U.val * D * U.valᴴ) * (U.val * D * U.valᴴ)).trace.re = _
  rw [htrace, hsquare]
  simp only [D, trace_diagonal, diagonal_mul_diagonal, Complex.re_sum,
    Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, mul_zero, sub_zero, pow_two, and_self]

theorem pure_gram_factorization {d : ℕ} {κ : Type*} [Fintype κ]
    (u : Ket (Fin d × Fin d)) (A B : κ → Op d)
    (hA : ∀ a, (A a).IsHermitian) (hB : ∀ b, (B b).IsHermitian)
    (U V : Matrix.unitaryGroup (Fin d) ℂ) (sval : Fin d → ℝ)
    (hs : ∀ i, 0 ≤ sval i)
    (hUV : coeff u = U.val * diagonal (fun i => (sval i : ℂ)) * V.valᴴ) :
    correlation (proj u) A B =
      (sandwichFactor (schmidtSandwich U sval) A)ᴴ *
        sandwichFactor (schmidtSandwich V sval) (fun b => (B b)ᵀ) := by
  let D : Op d := diagonal (fun i => (sval i : ℂ))
  let S := CFC.sqrt D
  have hD : D.PosSemidef := PosSemidef.diagonal (fun i => by
    change (0 : ℂ) ≤ (sval i : ℂ)
    exact_mod_cast hs i)
  have hS : S.IsHermitian := (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg D)).1
  have hSS : S * S = D := CFC.sqrt_mul_sqrt_self D hD.nonneg
  ext a b
  let X := schmidtSandwich U sval * A a * (schmidtSandwich U sval)ᴴ
  let Y := schmidtSandwich V sval * (B b)ᵀ * (schmidtSandwich V sval)ᴴ
  have hX : X.IsHermitian := Matrix.isHermitian_mul_mul_conjTranspose _ (hA a)
  have hY : Y.IsHermitian :=
    Matrix.isHermitian_mul_mul_conjTranspose _ (hB b).transpose
  change ((((proj u * Matrix.kronecker (A a) (B b)).trace).re : ℂ)) =
    star (Matrix.vec X) ⬝ᵥ Matrix.vec Y
  rw [star_vec_dotProduct_vec, hX.eq]
  rw [D5.S3.Quantum.Tomography.PurityPythagorasDecomposition.trace_mul_real_of_hermitian
    X Y hX hY]
  congr 1
  rw [pure_born_coeff]
  let L := U.valᴴ * A a * U.val
  let R := V.valᴴ * (B b)ᵀ * V.val
  have hXY : (X * Y).trace = (D * L * D * R).trace := by
    have hXeq : X = S * L * S := by
      simp only [X, schmidtSandwich, conjTranspose_mul, conjTranspose_conjTranspose]
      change S * U.valᴴ * A a * (U.val * Sᴴ) = S * L * S
      rw [hS.eq]
      simp only [L, mul_assoc]
    have hYeq : Y = S * R * S := by
      simp only [Y, schmidtSandwich, conjTranspose_mul, conjTranspose_conjTranspose]
      change S * V.valᴴ * (B b)ᵀ * (V.val * Sᴴ) = S * R * S
      rw [hS.eq]
      simp only [R, mul_assoc]
    rw [hXeq, hYeq]
    calc
      _ = (S * (L * (S * S) * R) * S).trace := by simp only [mul_assoc]
      _ = (S * (L * D * R) * S).trace := by rw [hSS]
      _ = ((S * S) * (L * D * R)).trace := by
        rw [trace_mul_cycle]
      _ = _ := by rw [hSS]; simp only [mul_assoc]
  rw [hXY]
  apply congrArg Complex.re
  change coeff u = U.val * D * V.valᴴ at hUV
  rw [hUV]
  rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, hD.1.eq]
  calc
    _ = (V.val * (D * U.valᴴ * A a * U.val * D * V.valᴴ * (B b)ᵀ)).trace := by
      simp only [mul_assoc]
    _ = ((D * U.valᴴ * A a * U.val * D * V.valᴴ * (B b)ᵀ) * V.val).trace :=
      trace_mul_comm _ _
    _ = _ := by simp only [L, R, mul_assoc]

def claim : Prop :=
  ∀ (d n r : ℕ), 1 ≤ d → 1 ≤ r → r ≤ d →
    ∀ (A B : EAM d n) (ρ : BipartiteOp d), SchmidtNumberLE ρ r →
      D5.S3.Quantum.Foundation.FiniteTraceDistance.traceNorm (Pn ρ A B) ≤
        ((d : ℝ) * ((d : ℝ) - 1) + (r : ℝ) * ((n : ℝ) - (d : ℝ))) /
          ((n : ℝ) * ((n : ℝ) - 1))

end D5.S3.Quantum.Entanglement.TavakoliMorelliIncompleteEAM
