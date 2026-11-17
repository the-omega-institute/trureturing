/- GID: D5/S3/Quantum/Recovery/QubitCoefficientGeometry
   generality: G
   mirror-B: D5/B/S3/Quantum/Recovery/QubitCoefficientGeometry
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Physical two-column coefficient and isometry geometry. -/

import D5.S3.Quantum.Entanglement.FiniteSectorPhysicalConstruction
import D5.S3.Quantum.Foundation.FiniteDiamondDistance
import D5.S3.Quantum.Foundation.FiniteDensityPurification
import D5.S3.Quantum.Divergence.FaithfulConditionalGap
import D5.S3.Quantum.Information.MarginalCalculus
import D5.S3.Quantum.Information.OrthogonalRecordEntropy
import D5.S3.Quantum.Information.CorrelatedGibbsEnergyIdentity
import D5.S3.Quantum.Information.Pauli.PauliMatrix
import D5.S3.Quantum.Information.ChenKatoBrandaoTraceNormCMIRefutation
import D5.S3.Quantum.Information.PartialTrace.Isometries
import D5.S3.Quantum.Foundation.FiniteHermitianTraceDuality
import D5.S3.Quantum.Reduction.WeightedWordDefect
import D5.S3.Quantum.Matrix.UniformVarianceTraceBound
import D5.S3.Quantum.Foundation.TraceNormTensorProduct
import D5.S3.Quantum.Entanglement.PermutationCriteria.BellBlocks
import D5.S3.Quantum.Matrix.CartesianVariance


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace D5.S3.Quantum.Recovery.QubitResidualRounding

open _root_.Matrix
open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Foundation.FiniteTraceDistance
open D5.S3.Quantum.Foundation.FiniteDiamondDistance
open D5.S3.Quantum.Information.PartialTraceMutualInformation
open D5.S3.Quantum.Information.StrongSubadditivity
open D5.S3.Quantum.Divergence.VonNeumannEntropyPinching
open scoped BigOperators ComplexOrder MatrixOrder InnerProductSpace
open scoped Matrix Matrix.Norms.L2Operator Kronecker

local notation "traceNorm" => D5.S3.Quantum.Foundation.FiniteTraceDistance.traceNorm

variable {Q : Type*} [Fintype Q]

/-- An output-label slice of a column of the physical isometry. -/
def column (W : Matrix (Fin 2 × Q) (Fin 2) ℂ) (j i : Fin 2) :
    EuclideanSpace ℂ Q := WithLp.toLp 2 (fun q => W (j, q) i)

/-- Discard the environment after applying the same isometry to both sides. -/
def reduced (W : Matrix (Fin 2 × Q) (Fin 2) ℂ) (M : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix (Fin 2) (Fin 2) ℂ := partialTraceRight (W * M * Wᴴ)

private theorem reduced_entry (W : Matrix (Fin 2 × Q) (Fin 2) ℂ)
    (M : Matrix (Fin 2) (Fin 2) ℂ) (j k : Fin 2) :
    reduced W M j k =
      ∑ a : Fin 2, ∑ b : Fin 2,
        inner ℂ (column W k b) (column W j a) * M a b := by
  classical
  change (∑ q : Q, ∑ b : Fin 2,
    (∑ a : Fin 2, W (j, q) a * M a b) * star (W (k, q) b)) = _
  calc
    _ = ∑ q : Q, ∑ a : Fin 2, ∑ b : Fin 2,
        W (j, q) a * M a b * star (W (k, q) b) := by
      apply Finset.sum_congr rfl
      intro q hq
      simp_rw [Finset.sum_mul]
      exact Finset.sum_comm
    _ = ∑ a : Fin 2, ∑ b : Fin 2, ∑ q : Q,
        W (j, q) a * M a b * star (W (k, q) b) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a ha
      rw [Finset.sum_comm]
    _ = _ := by
      simp only [column, EuclideanSpace.inner_eq_star_dotProduct, dotProduct]
      simp_rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      apply Finset.sum_congr rfl
      intro q hq
      change W (j, q) a * M a b * star (W (k, q) b) =
        (W (j, q) a * star (W (k, q) b)) * M a b
      ring

private theorem column_gram (W : Matrix (Fin 2 × Q) (Fin 2) ℂ)
    (hW : Wᴴ * W = 1) (i k : Fin 2) :
    inner ℂ (column W 0 i) (column W 0 k) +
      inner ℂ (column W 1 i) (column W 1 k) = if i = k then 1 else 0 := by
  have h := congrFun (congrFun hW i) k
  simpa [Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_prod_type,
    Fin.sum_univ_two, column, EuclideanSpace.inner_eq_star_dotProduct,
    dotProduct, Matrix.one_apply, mul_comm] using h

theorem retained_flip_norms (W : Matrix (Fin 2 × Q) (Fin 2) ℂ)
    (hW : Wᴴ * W = 1) :
    ‖column W 0 0‖ ^ 2 + ‖column W 1 0‖ ^ 2 = 1 ∧
    ‖column W 1 1‖ ^ 2 + ‖column W 0 1‖ ^ 2 = 1 := by
  have h0 := congrArg Complex.re (column_gram W hW 0 0)
  have h1 := congrArg Complex.re (column_gram W hW 1 1)
  simp [inner_self_eq_norm_sq_to_K, ← Complex.ofReal_pow] at h0 h1
  exact ⟨h0, by linarith⟩

private theorem coefficient_cancellation (W : Matrix (Fin 2 × Q) (Fin 2) ℂ)
    (hW : Wᴴ * W = 1) :
    inner ℂ (column W 1 0) (column W 0 0) +
        inner ℂ (column W 1 1) (column W 0 1) =
      inner ℂ (column W 1 0) (column W 0 0 - column W 1 1) +
        inner ℂ (column W 1 1 - column W 0 0) (column W 0 1) := by
  have ho := column_gram W hW 0 1
  norm_num at ho
  simp only [inner_sub_left, inner_sub_right]
  linear_combination ho

theorem retained_gap (W : Matrix (Fin 2 × Q) (Fin 2) ℂ)
    (hW : Wᴴ * W = 1) :
    ‖column W 1 1 - column W 0 0‖ ^ 2 ≤
      2 * ‖1 - inner ℂ (column W 1 1) (column W 0 0)‖ := by
  obtain ⟨h0, h1⟩ := retained_flip_norms W hW
  have hr := Complex.re_le_norm (1 - inner ℂ (column W 1 1) (column W 0 0))
  simp only [Complex.sub_re, Complex.one_re] at hr
  rw [norm_sub_sq (𝕜 := ℂ)]
  change ‖column W 1 1‖ ^ 2 -
      2 * (inner ℂ (column W 1 1) (column W 0 0)).re +
      ‖column W 0 0‖ ^ 2 ≤ _
  nlinarith [sq_nonneg ‖column W 1 0‖, sq_nonneg ‖column W 0 1‖]

/-- The phase-sensitive cancellation estimate follows from orthogonality of
the actual isometry columns. No unitality assumption is imposed. -/
theorem isometry_coefficient_geometry (W : Matrix (Fin 2 × Q) (Fin 2) ℂ)
    (hW : Wᴴ * W = 1) :
    (∀ M : Matrix (Fin 2) (Fin 2) ℂ,
      reduced W M 0 1 =
        inner ℂ (column W 1 1) (column W 0 0) * M 0 1 +
        inner ℂ (column W 1 0) (column W 0 0) * M 0 0 +
        inner ℂ (column W 1 1) (column W 0 1) * M 1 1 +
        inner ℂ (column W 1 0) (column W 0 1) * M 1 0) ∧
    ‖inner ℂ (column W 1 0) (column W 0 1)‖ ≤
      (‖column W 1 0‖ ^ 2 + ‖column W 0 1‖ ^ 2) / 2 ∧
    ‖inner ℂ (column W 1 0) (column W 0 0) +
        inner ℂ (column W 1 1) (column W 0 1)‖ ≤
      2 * Real.sqrt (‖column W 1 0‖ ^ 2 + ‖column W 0 1‖ ^ 2) *
        Real.sqrt ‖1 - inner ℂ (column W 1 1) (column W 0 0)‖ := by
  constructor
  · intro M
    rw [reduced_entry]
    simp only [Fin.sum_univ_two]
    ring
  constructor
  · have h := norm_inner_le_norm (𝕜 := ℂ) (column W 1 0) (column W 0 1)
    nlinarith [sq_nonneg (‖column W 1 0‖ - ‖column W 0 1‖)]
  · let s := Real.sqrt (‖column W 1 0‖ ^ 2 + ‖column W 0 1‖ ^ 2)
    let g := ‖1 - inner ℂ (column W 1 1) (column W 0 0)‖
    have hs : s ^ 2 = ‖column W 1 0‖ ^ 2 + ‖column W 0 1‖ ^ 2 :=
      Real.sq_sqrt (add_nonneg (sq_nonneg _) (sq_nonneg _))
    have hsg : (Real.sqrt g) ^ 2 = g := Real.sq_sqrt (norm_nonneg _)
    have hs0 : 0 ≤ s := Real.sqrt_nonneg _
    have hg0 : 0 ≤ Real.sqrt g := Real.sqrt_nonneg _
    have hdiff := retained_gap W hW
    have hflip : (‖column W 1 0‖ + ‖column W 0 1‖) ^ 2 ≤ 2 * s ^ 2 := by
      nlinarith [sq_nonneg (‖column W 1 0‖ - ‖column W 0 1‖)]
    have hprod :
        ((‖column W 1 0‖ + ‖column W 0 1‖) *
          ‖column W 1 1 - column W 0 0‖) ^ 2 ≤
          (2 * s * Real.sqrt g) ^ 2 := by
      have h := mul_le_mul hflip hdiff (sq_nonneg _)
        (mul_nonneg (by norm_num) (sq_nonneg s))
      dsimp [g] at hsg ⊢
      nlinarith [h]
    have hbound : (‖column W 1 0‖ + ‖column W 0 1‖) *
        ‖column W 1 1 - column W 0 0‖ ≤ 2 * s * Real.sqrt g := by
      nlinarith [mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hs0) hg0]
    rw [coefficient_cancellation W hW]
    calc
      _ ≤ ‖inner ℂ (column W 1 0) (column W 0 0 - column W 1 1)‖ +
          ‖inner ℂ (column W 1 1 - column W 0 0) (column W 0 1)‖ := norm_add_le _ _
      _ ≤ ‖column W 1 0‖ * ‖column W 0 0 - column W 1 1‖ +
          ‖column W 1 1 - column W 0 0‖ * ‖column W 0 1‖ :=
        add_le_add (norm_inner_le_norm _ _) (norm_inner_le_norm _ _)
      _ = (‖column W 1 0‖ + ‖column W 0 1‖) *
          ‖column W 1 1 - column W 0 0‖ := by rw [norm_sub_rev]; ring
      _ ≤ _ := hbound

private theorem reduced_Z_matrix (W : Matrix (Fin 2 × Q) (Fin 2) ℂ)
    (hW : Wᴴ * W = 1) :
    reduced W (Matrix.diagonal ![1, -1]) - Matrix.diagonal ![1, -1] =
      D5.S3.Quantum.Information.ChenKatoBrandaoTraceNormCMIRefutation.qubit
        (-(‖column W 1 0‖ ^ 2 + ‖column W 0 1‖ ^ 2))
        (inner ℂ (column W 1 0) (column W 0 0) -
          inner ℂ (column W 1 1) (column W 0 1)) := by
  classical
  obtain ⟨h0, h1⟩ := retained_flip_norms W hW
  have hc0 := congrArg (fun t : ℝ => (t : ℂ)) h0
  have hc1 := congrArg (fun t : ℝ => (t : ℂ)) h1
  push_cast at hc0 hc1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [reduced_entry, Fin.sum_univ_two, Matrix.diagonal_apply,
      inner_self_eq_norm_sq_to_K, Complex.ofReal_pow,
      D5.S3.Quantum.Information.ChenKatoBrandaoTraceNormCMIRefutation.qubit,
      inner_conj_symm, sub_eq_add_neg]
  · linear_combination hc0
  · linear_combination -hc1

theorem traceless_qubit_entry_bounds
    (M : Matrix (Fin 2) (Fin 2) ℂ) (hM : M.IsHermitian) (ht : Matrix.trace M = 0) :
    2 * ‖M 0 0‖ ≤ traceNorm M ∧ 2 * ‖M 0 1‖ ≤ traceNorm M := by
  have him : (M 0 0).im = 0 := by
    have hh := congrArg Complex.im (congrFun (congrFun hM.eq 0) 0)
    simp only [Matrix.conjTranspose_apply, Complex.star_def, Complex.conj_im] at hh
    linarith
  have h00 : M 0 0 = ((M 0 0).re : ℂ) := by
    apply Complex.ext <;> simp [him]
  have h10 : M 1 0 = star (M 0 1) := by
    have hh := congrArg star (congrFun (congrFun hM.eq 0) 1)
    simpa only [Matrix.conjTranspose_apply, star_star] using hh
  have h11 : M 1 1 = -M 0 0 := by
    simp only [Matrix.trace, Fin.sum_univ_two, Matrix.diag_apply] at ht
    linear_combination ht
  have hm : M =
      D5.S3.Quantum.Information.ChenKatoBrandaoTraceNormCMIRefutation.qubit
        (M 0 0).re (M 0 1) := by
    ext i j
    fin_cases i <;> fin_cases j
    · exact h00
    · rfl
    · exact h10
    · change M 1 1 = -((M 0 0).re : ℂ)
      exact h11.trans (congrArg Neg.neg h00)
  have hn : traceNorm M =
      2 * Real.sqrt ((M 0 0).re ^ 2 + Complex.normSq (M 0 1)) := by
    conv_lhs => rw [hm]
    exact D5.S3.Quantum.Information.ChenKatoBrandaoTraceNormCMIRefutation.qubit_norm _ _
  have hs := Real.sq_sqrt
    (add_nonneg (sq_nonneg (M 0 0).re) (Complex.normSq_nonneg (M 0 1)))
  have hp := Real.sqrt_nonneg ((M 0 0).re ^ 2 + Complex.normSq (M 0 1))
  rw [hn]
  constructor
  · have hn0 : ‖M 0 0‖ = |(M 0 0).re| := by
      conv_lhs => rw [h00]
      exact Complex.norm_real _
    rw [hn0]
    nlinarith [sq_abs (M 0 0).re, abs_nonneg (M 0 0).re,
      Complex.normSq_nonneg (M 0 1)]
  · have hns : Complex.normSq (M 0 1) = ‖M 0 1‖ ^ 2 := Complex.normSq_eq_norm_sq _
    nlinarith [norm_nonneg (M 0 1), sq_nonneg (M 0 0).re]

/-- Approximate preservation of the diagonal qubit direction controls both
the total flip probability and the difference of the two coherence terms. -/
theorem diagonal_residual_controls_coefficients (W : Matrix (Fin 2 × Q) (Fin 2) ℂ)
    (hW : Wᴴ * W = 1) (e : ℝ)
    (he : traceNorm
      (reduced W (Matrix.diagonal ![1, -1]) - Matrix.diagonal ![1, -1]) ≤ e) :
    ‖column W 1 0‖ ^ 2 + ‖column W 0 1‖ ^ 2 ≤ e / 2 ∧
    ‖inner ℂ (column W 1 0) (column W 0 0) -
      inner ℂ (column W 1 1) (column W 0 1)‖ ≤ e / 2 := by
  let t := ‖column W 1 0‖ ^ 2 + ‖column W 0 1‖ ^ 2
  let z := inner ℂ (column W 1 0) (column W 0 0) -
      inner ℂ (column W 1 1) (column W 0 1)
  rw [reduced_Z_matrix W hW,
    D5.S3.Quantum.Information.ChenKatoBrandaoTraceNormCMIRefutation.qubit_norm] at he
  change 2 * Real.sqrt ((-t) ^ 2 + Complex.normSq z) ≤ e at he
  have ht : 0 ≤ t := add_nonneg (sq_nonneg _) (sq_nonneg _)
  have hs := Real.sq_sqrt (add_nonneg (sq_nonneg (-t)) (Complex.normSq_nonneg z))
  have hn : Complex.normSq z = ‖z‖ ^ 2 := Complex.normSq_eq_norm_sq z
  have hp := Real.sqrt_nonneg ((-t) ^ 2 + Complex.normSq z)
  constructor <;> change _ ≤ e / 2
  · nlinarith [Complex.normSq_nonneg z]
  · nlinarith [norm_nonneg z, sq_nonneg t]

theorem reduced_hermitian (W : Matrix (Fin 2 × Q) (Fin 2) ℂ)
    (M : Matrix (Fin 2) (Fin 2) ℂ) (hM : M.IsHermitian) : (reduced W M).IsHermitian := by
  have hd := Matrix.isHermitian_mul_mul_conjTranspose W hM
  ext j k
  change star (∑ q : Q, (W * M * Wᴴ) (k, q) (j, q)) =
    ∑ q : Q, (W * M * Wᴴ) (j, q) (k, q)
  rw [star_sum]
  apply Finset.sum_congr rfl
  intro q _
  exact congrFun (congrFun hd.eq (j, q)) (k, q)

theorem reduced_trace (W : Matrix (Fin 2 × Q) (Fin 2) ℂ)
    (hW : Wᴴ * W = 1) (M : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix.trace (reduced W M) = Matrix.trace M := by
  rw [reduced, trace_partialTraceRight, Matrix.trace_mul_cycle, hW, Matrix.one_mul]

private theorem qubit_entry_operatorNorm (M : Matrix (Fin 2) (Fin 2) ℂ) (i j : Fin 2) :
    ‖M i j‖ ≤ ‖M‖ := by
  let ei := EuclideanSpace.basisFun (Fin 2) ℂ i
  let ej := EuclideanSpace.basisFun (Fin 2) ℂ j
  have hi : ‖ei‖ = 1 := (EuclideanSpace.basisFun (Fin 2) ℂ).orthonormal.1 i
  have hj : ‖ej‖ = 1 := (EuclideanSpace.basisFun (Fin 2) ℂ).orthonormal.1 j
  have he : inner ℂ ei (Matrix.toEuclideanCLM (𝕜 := ℂ) M ej) = M i j := by
    simp [ei, ej, EuclideanSpace.basisFun_apply, Matrix.toEuclideanCLM_toLp,
      EuclideanSpace.inner_eq_star_dotProduct, Matrix.mulVec, dotProduct, Pi.single_apply]
  rw [← he]
  exact (norm_inner_le_norm _ _).trans (by
    simpa [hi, hj, Matrix.l2_opNorm_toEuclideanCLM] using
      (Matrix.toEuclideanCLM (𝕜 := ℂ) M).le_opNorm ej)

/-- The retained-column phase gap controls the complex coherence of every
traceless Hermitian input, using its actual reduced-channel residual. -/
theorem offDiagonal_gap_bound (W : Matrix (Fin 2 × Q) (Fin 2) ℂ)
    (hW : Wᴴ * W = 1) (M : Matrix (Fin 2) (Fin 2) ℂ)
    (hM : M.IsHermitian) (ht : Matrix.trace M = 0)
    (x e f d : ℝ) (hm : ‖M‖ ≤ x)
    (he : traceNorm (reduced W M - M) ≤ e)
    (hf : ‖column W 1 0‖ ^ 2 + ‖column W 0 1‖ ^ 2 ≤ f)
    (hd : ‖inner ℂ (column W 1 0) (column W 0 0) -
      inner ℂ (column W 1 1) (column W 0 1)‖ ≤ d) :
    ‖1 - inner ℂ (column W 1 1) (column W 0 0)‖ * ‖M 0 1‖ ≤
      e / 2 + d * x + (f / 2) * x := by
  have h11 : M 1 1 = -M 0 0 := by
    simp only [Matrix.trace, Fin.sum_univ_two, Matrix.diag_apply] at ht
    linear_combination ht
  have hb := (traceless_qubit_entry_bounds (reduced W M - M)
    ((reduced_hermitian W M hM).sub hM)
    (by rw [Matrix.trace_sub, reduced_trace W hW, sub_self])).2
  have hb' : ‖(reduced W M - M) 0 1‖ ≤ e / 2 := by linarith
  obtain ⟨hentry, hk, _⟩ := isometry_coefficient_geometry W hW
  have heq : (1 - inner ℂ (column W 1 1) (column W 0 0)) * M 0 1 =
      -(reduced W M - M) 0 1 +
        (inner ℂ (column W 1 0) (column W 0 0) -
          inner ℂ (column W 1 1) (column W 0 1)) * M 0 0 +
        inner ℂ (column W 1 0) (column W 0 1) * M 1 0 := by
    have h := hentry M
    rw [h11] at h
    simp only [Matrix.sub_apply]
    linear_combination h
  rw [← norm_mul, heq]
  calc
    _ ≤ ‖-(reduced W M - M) 0 1‖ +
        ‖(inner ℂ (column W 1 0) (column W 0 0) -
          inner ℂ (column W 1 1) (column W 0 1)) * M 0 0‖ +
        ‖inner ℂ (column W 1 0) (column W 0 1) * M 1 0‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ e / 2 + d * x + (f / 2) * x := by
      rw [norm_neg, norm_mul, norm_mul]
      apply add_le_add
      · exact add_le_add hb' (mul_le_mul hd ((qubit_entry_operatorNorm M 0 0).trans hm)
          (norm_nonneg _) (le_trans (norm_nonneg _) hd))
      · exact mul_le_mul (hk.trans (by linarith))
          ((qubit_entry_operatorNorm M 1 0).trans hm) (norm_nonneg _)
          (le_trans (norm_nonneg _) (hk.trans (by linarith)))

theorem rotated_dilation [DecidableEq Q]
    (W : Matrix (Fin 2 × Q) (Fin 2) ℂ) (hW : Wᴴ * W = 1)
    (U : Matrix.unitaryGroup (Fin 2) ℂ) :
    ∃ V : Matrix (Fin 2 × Q) (Fin 2) ℂ, Vᴴ * V = 1 ∧
      ∀ M : Matrix (Fin 2) (Fin 2) ℂ,
        reduced V M = U.valᴴ * reduced W (U.val * M * U.valᴴ) * U.val := by
  let L := U.valᴴ ⊗ₖ (1 : Matrix Q Q ℂ)
  let V := L * W * U.val
  have huU : U.val * U.valᴴ = 1 := Unitary.coe_mul_star_self U
  have hL : Lᴴ * L = 1 := by
    dsimp [L]
    rw [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_conjTranspose,
      Matrix.conjTranspose_one, ← Matrix.mul_kronecker_mul,
      huU, Matrix.one_mul, Matrix.one_kronecker_one]
  refine ⟨V, ?_, ?_⟩
  · change (L * W * U.val)ᴴ * (L * W * U.val) = 1
    calc
      _ = U.valᴴ * Wᴴ * (Lᴴ * L) * W * U.val := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = U.valᴴ * (Wᴴ * W) * U.val := by rw [hL]; simp [Matrix.mul_assoc]
      _ = 1 := by rw [hW, Matrix.mul_one]; exact Unitary.coe_star_mul_self U
  · intro M
    have he : V * M * Vᴴ = L * (W * (U.val * M * U.valᴴ) * Wᴴ) * Lᴴ := by
      simp only [V, Matrix.conjTranspose_mul, Matrix.mul_assoc]
    unfold reduced
    rw [he]
    simpa only [L, Matrix.kronecker, Matrix.conjTranspose_conjTranspose] using
      D5.S3.Quantum.Measurement.AnticoherenceSpinCovariance.partialTrace_isometries
        U.valᴴ (1 : Matrix Q Q ℂ) (by simp)
        (W * (U.val * M * U.valᴴ) * Wᴴ)

private def outputEquiv (C : Type) :
    (Fin 2 × (C × ((Fin 2 × C) × Fin 2))) ≃
      (((Fin 2 × C) × Fin 2) × (Fin 2 × C)) where
  toFun p := (p.2.2, (p.1, p.2.1))
  invFun p := (p.2.1, (p.2.2, p.1))
  left_inv := by rintro ⟨j, c, e⟩; rfl
  right_inv := by rintro ⟨e, j, c⟩; rfl

private theorem actual_dilation_base {C : Type} [Fintype C] [DecidableEq C]
    (T : QuantumChannel (Fin 2) (Fin 2 × C)) :
    ∃ W : Matrix (Fin 2 × (C × ((Fin 2 × C) × Fin 2))) (Fin 2) ℂ,
      Wᴴ * W = 1 ∧
      (∀ (M : Matrix (Fin 2) (Fin 2) ℂ) (j k : Fin 2) (c d : C),
        (∑ e : (Fin 2 × C) × Fin 2,
          (W * M * Wᴴ) (j, (c, e)) (k, (d, e))) =
            CStarMatrix.ofMatrix.symm
              (T.toCompletelyPositiveMap (CStarMatrix.ofMatrix M)) (j, c) (k, d)) ∧
      (∀ M : Matrix (Fin 2) (Fin 2) ℂ,
        reduced W M = partialTraceRight (CStarMatrix.ofMatrix.symm
          (T.toCompletelyPositiveMap (CStarMatrix.ofMatrix M)))) := by
  classical
  obtain ⟨V, hV, hT⟩ :=
    D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.channel_kraus_stinespring.2 T
  let e := outputEquiv C
  let W := V.submatrix e id
  have hw : Wᴴ * W = 1 := by
    dsimp [W]
    rw [Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv Vᴴ V id e id, hV]
    rfl
  have hmatrix (M : Matrix (Fin 2) (Fin 2) ℂ) :
      W * M * Wᴴ = (V * M * Vᴴ).submatrix e e := by
    ext p q
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, W, Matrix.submatrix_apply]
    rfl
  have hout (M : Matrix (Fin 2) (Fin 2) ℂ) (j k : Fin 2) (c d : C) :
      (∑ t : (Fin 2 × C) × Fin 2,
        (W * M * Wᴴ) (j, (c, t)) (k, (d, t))) =
          CStarMatrix.ofMatrix.symm
            (T.toCompletelyPositiveMap (CStarMatrix.ofMatrix M)) (j, c) (k, d) := by
    rw [hmatrix]
    exact congrFun (congrFun (hT M) (j, c)) (k, d)
  refine ⟨W, hw, hout, ?_⟩
  intro M
  ext j k
  change (∑ q : C × ((Fin 2 × C) × Fin 2),
    (W * M * Wᴴ) (j, q) (k, q)) = _
  rw [Fintype.sum_prod_type]
  change (∑ c : C, ∑ t : (Fin 2 × C) × Fin 2,
    (W * M * Wᴴ) (j, (c, t)) (k, (c, t))) = _
  simp_rw [hout]
  rfl

private def reindexChannel {I J : Type*} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] (e : I ≃ J) : QuantumChannel I J where
  toCompletelyPositiveMap :=
    CompletelyPositiveMapClass.toCompletelyPositiveLinearMap (CStarMatrix.reindexₐ ℂ ℂ e)
  trace_preserving X := by
    change (∑ j : J, X (e.symm j) (e.symm j)) = ∑ i : I, X i i
    exact e.symm.sum_comp (fun i => X i i)

theorem actual_dilation {C : Type*} [Fintype C] [DecidableEq C]
    (T : QuantumChannel (Fin 2) (Fin 2 × C)) :
    ∃ W : Matrix (Fin 2 × (C × ((Fin 2 × Fin (Fintype.card C)) × Fin 2))) (Fin 2) ℂ,
      Wᴴ * W = 1 ∧
      (∀ (M : Matrix (Fin 2) (Fin 2) ℂ) (j k : Fin 2) (c d : C),
        (∑ e : (Fin 2 × Fin (Fintype.card C)) × Fin 2,
          (W * M * Wᴴ) (j, (c, e)) (k, (d, e))) =
            CStarMatrix.ofMatrix.symm
              (T.toCompletelyPositiveMap (CStarMatrix.ofMatrix M)) (j, c) (k, d)) ∧
      (∀ M : Matrix (Fin 2) (Fin 2) ℂ,
        reduced W M = partialTraceRight (CStarMatrix.ofMatrix.symm
          (T.toCompletelyPositiveMap (CStarMatrix.ofMatrix M)))) := by
  let e := Fintype.equivFin C
  let f := Equiv.prodCongr (Equiv.refl (Fin 2)) e
  let TC := (reindexChannel f).comp T
  obtain ⟨V,hV,hout,hred⟩ := actual_dilation_base TC
  let q := Equiv.prodCongr (Equiv.refl (Fin 2))
    (Equiv.prodCongr e (Equiv.refl ((Fin 2 × Fin (Fintype.card C)) × Fin 2)))
  let W := V.submatrix q id
  have hW : Wᴴ * W = 1 := by
    dsimp only [W]
    rw [Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv Vᴴ V id q id,hV]
    rfl
  have heq (M : Matrix (Fin 2) (Fin 2) ℂ) :
      W*M*Wᴴ = (V*M*Vᴴ).submatrix q q := by
    ext i j
    simp only [Matrix.mul_apply,Matrix.conjTranspose_apply,W,Matrix.submatrix_apply]
    rfl
  have ho (M : Matrix (Fin 2) (Fin 2) ℂ) (j k : Fin 2) (c d : C) :
      (∑ t : (Fin 2 × Fin (Fintype.card C)) × Fin 2,
        (W*M*Wᴴ) (j,(c,t)) (k,(d,t))) =
      CStarMatrix.ofMatrix.symm
        (T.toCompletelyPositiveMap (CStarMatrix.ofMatrix M)) (j,c) (k,d) := by
    rw [heq]
    have h := hout M j k (e c) (e d)
    change (∑ t, (V*M*Vᴴ) (j,(e c,t)) (k,(e d,t))) =
      T.toCompletelyPositiveMap (CStarMatrix.ofMatrix M)
        (j,e.symm (e c)) (k,e.symm (e d)) at h
    change (∑ t, (V*M*Vᴴ) (j,(e c,t)) (k,(e d,t))) =
      T.toCompletelyPositiveMap (CStarMatrix.ofMatrix M) (j,c) (k,d)
    simpa only [Equiv.symm_apply_apply] using h
  refine ⟨W,hW,ho,?_⟩
  intro M
  ext j k
  change (∑ p : C × ((Fin 2 × Fin (Fintype.card C)) × Fin 2),
    (W*M*Wᴴ) (j,p) (k,p)) = _
  rw [Fintype.sum_prod_type]
  simp_rw [ho]
  rfl

end D5.S3.Quantum.Recovery.QubitResidualRounding
