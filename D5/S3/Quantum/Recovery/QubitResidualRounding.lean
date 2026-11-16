/- GID: D5/S3/Quantum/Recovery/QubitResidualRounding
   generality: G
   mirror-B: D5/B/S3/Quantum/Recovery/QubitResidualRounding
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Physical two-column qubit dilation geometry for residual rounding. -/

import D5.S3.Quantum.Entanglement.FiniteSectorPhysicalConstruction
import D5.S3.Quantum.Foundation.FiniteDiamondDistance
import D5.S3.Quantum.Foundation.FiniteDensityPurification
import D5.S3.Quantum.Divergence.FaithfulConditionalGap
import D5.S3.Quantum.Information.StrongSubadditivity.MarkovConstructors
import D5.S3.Quantum.Information.MarginalCalculus
import D5.S3.Quantum.Information.OrthogonalRecordEntropy
import D5.S3.Quantum.Information.CorrelatedGibbsEnergyIdentity
import D5.S3.Quantum.Information.Pauli.PauliMatrix
import D5.S3.Quantum.Information.ChenKatoBrandaoTraceNormCMIRefutation
import D5.S3.Quantum.Measurement.AnticoherenceSpinCovariance
import D5.S3.Quantum.Foundation.FiniteHermitianTraceDuality
import D5.S3.Quantum.Reduction.WeightedWordDefect
import D5.S3.Quantum.Matrix.UniformVarianceTraceBound
import D5.S3.Quantum.Classicalization.XuImaiGuhneSimultaneousUnboundedness
import D5.S3.Quantum.Entanglement.PermutationCriteria.BellBlocks
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! Two-column geometry of the actual finite physical recovery channel. -/

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

private theorem retained_flip_norms (W : Matrix (Fin 2 × Q) (Fin 2) ℂ)
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

private theorem retained_gap (W : Matrix (Fin 2 × Q) (Fin 2) ℂ)
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

private theorem traceless_qubit_entry_bounds
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

private theorem reduced_hermitian (W : Matrix (Fin 2 × Q) (Fin 2) ℂ)
    (M : Matrix (Fin 2) (Fin 2) ℂ) (hM : M.IsHermitian) : (reduced W M).IsHermitian := by
  have hd := Matrix.isHermitian_mul_mul_conjTranspose W hM
  ext j k
  change star (∑ q : Q, (W * M * Wᴴ) (k, q) (j, q)) =
    ∑ q : Q, (W * M * Wᴴ) (j, q) (k, q)
  rw [star_sum]
  apply Finset.sum_congr rfl
  intro q _
  exact congrFun (congrFun hd.eq (j, q)) (k, q)

private theorem reduced_trace (W : Matrix (Fin 2 × Q) (Fin 2) ℂ)
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

private theorem rotated_dilation [DecidableEq Q]
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

private theorem actual_dilation {C : Type} [Fintype C] [DecidableEq C]
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

section Centered

variable {A : Type*} [Fintype A] [DecidableEq A]

/-- The centered matrix uses the two actual marginals of the input state. -/
def centered (P : DensityState (A × Fin 2)) : Matrix (A × Fin 2) (A × Fin 2) ℂ :=
  CStarMatrix.ofMatrix.symm P.1 -
    CStarMatrix.ofMatrix.symm (productState (marginalRight P) (marginalLeft P)).1

/-- A test on A reads every complex B block by its actual trace pairing. -/
def sliceLinear {B : Type*} (D : Matrix (A × B) (A × B) ℂ) :
    CStarMatrix A A ℂ →ₗ[ℂ] CStarMatrix B B ℂ where
  toFun F := CStarMatrix.ofMatrix (fun j k =>
    Matrix.trace (CStarMatrix.ofMatrix.symm F *
      D.submatrix (fun a => (a, j)) (fun a => (a, k))))
  map_add' F G := by
    apply CStarMatrix.ext
    intro j k
    change Matrix.trace ((CStarMatrix.ofMatrix.symm F + CStarMatrix.ofMatrix.symm G) * _) = _
    rw [Matrix.add_mul, Matrix.trace_add]
    rfl
  map_smul' z F := by
    apply CStarMatrix.ext
    intro j k
    change Matrix.trace ((z • CStarMatrix.ofMatrix.symm F) * _) = _
    rw [Matrix.smul_mul, Matrix.trace_smul]
    rfl

private theorem attained_centered_test (P : DensityState (A × Fin 2)) :
    ∃ F : CStarMatrix A A ℂ, IsSelfAdjoint F ∧ ‖F‖ ≤ 1 ∧
      ∀ G : CStarMatrix A A ℂ, IsSelfAdjoint G → ‖G‖ ≤ 1 →
        ‖sliceLinear (centered P) G‖ ≤ ‖sliceLinear (centered P) F‖ := by
  letI : FiniteDimensional ℂ (CStarMatrix A A ℂ) :=
    Module.Finite.equiv (CStarMatrix.ofMatrixₗ (R := ℂ) (m := A) (n := A))
  let S : Set (CStarMatrix A A ℂ) := {F | IsSelfAdjoint F ∧ ‖F‖ ≤ 1}
  have hc : IsCompact S := by
    have hsa : IsClosed {F : CStarMatrix A A ℂ | IsSelfAdjoint F} :=
      isClosed_eq continuous_star continuous_id
    have he : S = {F : CStarMatrix A A ℂ | IsSelfAdjoint F} ∩ Metric.closedBall 0 1 := by
      ext F
      simp [S, Metric.mem_closedBall, dist_zero_right]
    rw [he]
    exact (isCompact_closedBall (0 : CStarMatrix A A ℂ) 1).inter_left hsa
  have hne : S.Nonempty := ⟨0, by simp [S]⟩
  have hcont : Continuous (fun F => ‖sliceLinear (centered P) F‖) :=
    (sliceLinear (centered P)).continuous_of_finiteDimensional.norm
  obtain ⟨F, hF, hmax⟩ := hc.exists_isMaxOn hne hcont.continuousOn
  exact ⟨F, hF.1, hF.2, fun G hG hn => hmax ⟨hG, hn⟩⟩

private theorem centered_marginals_zero (P : DensityState (A × Fin 2)) :
    partialTraceLeft (centered P) = 0 ∧ partialTraceRight (centered P) = 0 := by
  constructor
  · have he := marginalLeft_productState (marginalRight P) (marginalLeft P)
    have hr := congrArg (fun S : DensityState (Fin 2) => CStarMatrix.ofMatrix.symm S.1) he
    ext j k
    change (∑ a, (CStarMatrix.ofMatrix.symm P.1 (a, j) (a, k) -
      CStarMatrix.ofMatrix.symm (productState (marginalRight P) (marginalLeft P)).1
        (a, j) (a, k))) = 0
    rw [Finset.sum_sub_distrib]
    exact sub_eq_zero.mpr (congrFun (congrFun hr j) k).symm
  · have he := marginalRight_productState (marginalRight P) (marginalLeft P)
    have hr := congrArg (fun S : DensityState A => CStarMatrix.ofMatrix.symm S.1) he
    ext j k
    change (∑ b, (CStarMatrix.ofMatrix.symm P.1 (j, b) (k, b) -
      CStarMatrix.ofMatrix.symm (productState (marginalRight P) (marginalLeft P)).1
        (j, b) (k, b))) = 0
    rw [Finset.sum_sub_distrib]
    exact sub_eq_zero.mpr (congrFun (congrFun hr j) k).symm

private def block {B : Type*} (D : Matrix (A × B) (A × B) ℂ) (j k : B) :
    Matrix A A ℂ := D.submatrix (fun a => (a, j)) (fun a => (a, k))

private def pauliCoefficient (D : Matrix (A × Fin 2) (A × Fin 2) ℂ) :
    Fin 3 → Matrix A A ℂ := ![
      block D 0 1 + block D 1 0,
      Complex.I • (block D 0 1 - block D 1 0),
      block D 0 0 - block D 1 1]

private def pauli : Fin 3 → Matrix (Fin 2) (Fin 2) ℂ :=
  fun i => D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.pauliMatrix
    (![D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.Pauli.X,
      D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.Pauli.Y,
      D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.Pauli.Z] i)

private theorem pauli_reconstruction (D : Matrix (A × Fin 2) (A × Fin 2) ℂ)
    (hz : partialTraceRight D = 0) :
    D = (1 / 2 : ℝ) • ∑ i : Fin 3, (pauliCoefficient D i) ⊗ₖ pauli i := by
  ext ⟨a, j⟩ ⟨b, k⟩
  have hh := congrFun (congrFun hz a) b
  simp only [partialTraceRight, Fin.sum_univ_two, Matrix.zero_apply] at hh
  fin_cases j <;> fin_cases k <;>
    simp [pauliCoefficient, block, pauli,
      D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.pauliMatrix,
      D5.S3.Quantum.FiniteDimensional.qubitX,
      D5.S3.Quantum.FiniteDimensional.qubitZ,
      Fin.sum_univ_three, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.kronecker_apply, Complex.real_smul] <;>
    ring_nf <;> (try simp only [Complex.I_sq]) <;>
    first | ring | linear_combination (1 / 2 : ℂ) * hh

private theorem centered_hermitian (P : DensityState (A × Fin 2)) :
    (centered P).IsHermitian :=
  (density_posSemidef P).isHermitian.sub
    (density_posSemidef (productState (marginalRight P) (marginalLeft P))).isHermitian

private theorem pauliCoefficient_hermitian (D : Matrix (A × Fin 2) (A × Fin 2) ℂ)
    (hD : D.IsHermitian) (i : Fin 3) : (pauliCoefficient D i).IsHermitian := by
  have hb (j k : Fin 2) : (block D j k)ᴴ = block D k j := by
    ext a b
    exact congrFun (congrFun hD.eq (a, k)) (b, j)
  fin_cases i
  · change (block D 0 1 + block D 1 0)ᴴ = block D 0 1 + block D 1 0
    rw [Matrix.conjTranspose_add, hb, hb, add_comm]
  · change (Complex.I • (block D 0 1 - block D 1 0))ᴴ =
      Complex.I • (block D 0 1 - block D 1 0)
    rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, hb, hb]
    simp only [Complex.star_def, Complex.conj_I, neg_smul, ← smul_neg, neg_sub]
  · change (block D 0 0 - block D 1 1)ᴴ = block D 0 0 - block D 1 1
    rw [Matrix.conjTranspose_sub, hb, hb]

private theorem pauliCoefficient_trace (D : Matrix (A × Fin 2) (A × Fin 2) ℂ)
    (F : Matrix A A ℂ) (i : Fin 3) :
    Matrix.trace (F * pauliCoefficient D i) =
      (![sliceLinear D (CStarMatrix.ofMatrix F) 0 1 + sliceLinear D (CStarMatrix.ofMatrix F) 1 0,
        Complex.I * (sliceLinear D (CStarMatrix.ofMatrix F) 0 1 - sliceLinear D (CStarMatrix.ofMatrix F) 1 0),
        sliceLinear D (CStarMatrix.ofMatrix F) 0 0 - sliceLinear D (CStarMatrix.ofMatrix F) 1 1] i) := by
  fin_cases i <;>
    simp [pauliCoefficient, sliceLinear, block, Matrix.mul_add, Matrix.mul_sub,
      Matrix.mul_smul, Matrix.trace_add, Matrix.trace_sub, Matrix.trace_smul]

private theorem pauliCoefficient_traceNorm_le (P : DensityState (A × Fin 2))
    (x : ℝ)
    (hx : ∀ F : CStarMatrix A A ℂ, IsSelfAdjoint F → ‖F‖ ≤ 1 →
      ‖sliceLinear (centered P) F‖ ≤ x) (i : Fin 3) :
    traceNorm (pauliCoefficient (centered P) i) ≤ 2 * x := by
  apply D5.S3.Quantum.Foundation.FiniteHermitianTraceDuality.hermitian_traceNorm_le_tests
    _ (pauliCoefficient_hermitian _ (centered_hermitian P) i)
  intro F hF hfn
  have hfc : IsSelfAdjoint (CStarMatrix.ofMatrix F) :=
    (show IsSelfAdjoint F from hF).map CStarMatrix.ofMatrixStarAlgEquiv
  have hn : ‖CStarMatrix.ofMatrix F‖ ≤ 1 := by
    change ‖CStarMatrix.ofMatrixStarAlgEquiv F‖ ≤ 1
    rw [StarAlgEquiv.norm_map]
    exact hfn
  have hk := hx (CStarMatrix.ofMatrix F) hfc hn
  have he (j k : Fin 2) : ‖sliceLinear (centered P) (CStarMatrix.ofMatrix F) j k‖ ≤ x :=
    (CStarMatrix.norm_entry_le_norm (M := sliceLinear (centered P)
      (CStarMatrix.ofMatrix F)) (i := j) (j := k)).trans hk
  rw [pauliCoefficient_trace]
  fin_cases i <;> simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  · exact (Complex.re_le_norm _).trans ((norm_add_le _ _).trans (by linarith [he 0 1, he 1 0]))
  · change (Complex.I * (sliceLinear (centered P) (CStarMatrix.ofMatrix F) 0 1 -
        sliceLinear (centered P) (CStarMatrix.ofMatrix F) 1 0)).re ≤ 2 * x
    apply (Complex.re_le_norm _).trans
    rw [norm_mul, Complex.norm_I, one_mul]
    exact (norm_sub_le _ _).trans (by linarith [he 0 1, he 1 0])
  · exact (Complex.re_le_norm _).trans ((norm_sub_le _ _).trans (by linarith [he 0 0, he 1 1]))

private theorem pauli_traceNorm (i : Fin 3) : traceNorm (pauli i) = 2 := by
  have hg : (pauli i)ᴴ * pauli i = 1 := by
    fin_cases i <;>
      ext a b <;> fin_cases a <;> fin_cases b <;>
      norm_num [pauli,
        D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.pauliMatrix,
        D5.S3.Quantum.FiniteDimensional.qubitX,
        D5.S3.Quantum.FiniteDimensional.qubitZ,
        Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply]
  simp [D5.S3.Quantum.Foundation.FiniteTraceDistance.traceNorm, hg, Matrix.trace]

private theorem traceNorm_tensor {B : Type*} [Fintype B] [DecidableEq B]
    (X : Matrix A A ℂ) (Y : Matrix B B ℂ) : traceNorm (X ⊗ₖ Y) = traceNorm X * traceNorm Y := by
  let e := (Fintype.equivFin A).symm
  let d := (Fintype.equivFin B).symm
  let f := e.prodCongr d
  have ht := D5.S3.Quantum.Entanglement.PermutationCriteria.NormInvariance.traceNorm_submatrix_equiv
    (X ⊗ₖ Y) f f
  have hx := D5.S3.Quantum.Entanglement.PermutationCriteria.NormInvariance.traceNorm_submatrix_equiv
    X e e
  have hy := D5.S3.Quantum.Entanglement.PermutationCriteria.NormInvariance.traceNorm_submatrix_equiv
    Y d d
  have he : (X ⊗ₖ Y).submatrix f f = X.submatrix e e ⊗ₖ Y.submatrix d d := rfl
  rw [he, D5.S3.Quantum.Classicalization.XuImaiGuhneSimultaneousUnboundedness.Toolkit.traceNorm_kronecker,
    hx, hy] at ht
  exact ht.symm

/-- The maximum over all Hermitian contractions controls the centered state
without an A or C coordinate count. -/
theorem attained_centered_traceNorm_bound (P : DensityState (A × Fin 2)) :
    ∃ F : CStarMatrix A A ℂ, IsSelfAdjoint F ∧ ‖F‖ ≤ 1 ∧
      (∀ G : CStarMatrix A A ℂ, IsSelfAdjoint G → ‖G‖ ≤ 1 →
        ‖sliceLinear (centered P) G‖ ≤ ‖sliceLinear (centered P) F‖) ∧
      traceNorm (centered P) ≤ 6 * ‖sliceLinear (centered P) F‖ := by
  obtain ⟨F, hf, hfn, hmax⟩ := attained_centered_test P
  refine ⟨F, hf, hfn, hmax, ?_⟩
  let x := ‖sliceLinear (centered P) F‖
  have hc (i : Fin 3) : traceNorm (pauliCoefficient (centered P) i) ≤ 2 * x :=
    pauliCoefficient_traceNorm_le P x hmax i
  have hp (i : Fin 3) :
      traceNorm ((pauliCoefficient (centered P) i) ⊗ₖ pauli i) ≤ 4 * x := by
    rw [traceNorm_tensor, pauli_traceNorm]
    linarith [hc i]
  change traceNorm (centered P) ≤ 6 * x
  conv_lhs => rw [pauli_reconstruction _ (centered_marginals_zero P).2]
  change traceNorm (((1 / 2 : ℝ) : ℂ) •
    ∑ i : Fin 3, (pauliCoefficient (centered P) i) ⊗ₖ pauli i) ≤ 6 * x
  rw [D5.S3.Quantum.Entanglement.ConicalDesignConcurrenceComparability.traceNorm_smul_nonneg
    _ (1 / 2 : ℝ) (by norm_num), Fin.sum_univ_three]
  have h := traceNorm_add_le
    ((pauliCoefficient (centered P) 0) ⊗ₖ pauli 0)
    (((pauliCoefficient (centered P) 1) ⊗ₖ pauli 1) +
      ((pauliCoefficient (centered P) 2) ⊗ₖ pauli 2))
  have h' := traceNorm_add_le
    ((pauliCoefficient (centered P) 1) ⊗ₖ pauli 1)
    ((pauliCoefficient (centered P) 2) ⊗ₖ pauli 2)
  change (1 / 2 : ℝ) * traceNorm _ ≤ 6 * x
  rw [add_assoc]
  linarith [hp 0, hp 1, hp 2]

end Centered

section UnitaryTransport

variable {A B C : Type*} [Fintype A] [DecidableEq A]
  [Fintype B] [DecidableEq B] [Fintype C] [DecidableEq C]

private def tensorUnitary (U : Matrix.unitaryGroup A ℂ)
    (V : Matrix.unitaryGroup B ℂ) : Matrix.unitaryGroup (A × B) ℂ :=
  ⟨U.val ⊗ₖ V.val, Matrix.mem_unitaryGroup_iff'.mpr (by
    rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_kronecker,
      ← Matrix.mul_kronecker_mul,
      (show U.valᴴ * U.val = 1 from Unitary.coe_star_mul_self U),
      (show V.valᴴ * V.val = 1 from Unitary.coe_star_mul_self V),
      Matrix.one_kronecker_one])⟩

private def conjugateState (U : Matrix.unitaryGroup A ℂ) (rho : DensityState A) :
    DensityState A :=
  D5.S3.Quantum.Dynamics.EntropyProductionCoherenceDeletionIdentity.unitaryConjugateState
    U.val U.property rho

private theorem conjugateState_value (U : Matrix.unitaryGroup A ℂ) (rho : DensityState A) :
    CStarMatrix.ofMatrix.symm (conjugateState U rho).1 =
      U.val * CStarMatrix.ofMatrix.symm rho.1 * U.valᴴ := rfl

private theorem conjugateState_one (rho : DensityState A) : conjugateState 1 rho = rho := by
  apply Subtype.ext
  apply CStarMatrix.ofMatrix.symm.injective
  rw [conjugateState_value]
  simp

private theorem entropy_conjugateState (U : Matrix.unitaryGroup A ℂ) (rho : DensityState A) :
    vonNeumannEntropy (conjugateState U rho) = vonNeumannEntropy rho :=
  D5.S3.Quantum.Information.CorrelatedGibbsEnergyIdentity.von_neumann_entropy_unitary
    U.val U.property rho

private def conjugateAlg (U : Matrix.unitaryGroup A ℂ) :
    CStarMatrix A A ℂ ≃⋆ₐ[ℂ] CStarMatrix A A ℂ :=
  CStarMatrix.ofMatrixStarAlgEquiv.symm.trans
    ((Unitary.conjStarAlgAut ℂ (Matrix A A ℂ) U).trans CStarMatrix.ofMatrixStarAlgEquiv)

private def conjugateChannel (U : Matrix.unitaryGroup A ℂ) : QuantumChannel A A where
  toCompletelyPositiveMap :=
    CompletelyPositiveMapClass.toCompletelyPositiveLinearMap (conjugateAlg U)
  trace_preserving X := by
    change Matrix.trace (U.val * CStarMatrix.ofMatrix.symm X * U.valᴴ) = Matrix.trace _
    rw [Matrix.trace_mul_cycle, (show U.valᴴ * U.val = 1 from Unitary.coe_star_mul_self U),
      Matrix.one_mul]
    rfl

private theorem conjugateChannel_apply (U : Matrix.unitaryGroup A ℂ)
    (X : CStarMatrix A A ℂ) :
    CStarMatrix.ofMatrix.symm ((conjugateChannel U).toCompletelyPositiveMap X) =
      U.val * CStarMatrix.ofMatrix.symm X * U.valᴴ := rfl

private theorem conjugateChannel_mapState (U : Matrix.unitaryGroup A ℂ)
    (rho : DensityState A) : (conjugateChannel U).mapState rho = conjugateState U rho := by
  apply Subtype.ext
  rfl

private theorem conjugateState_inverse (U : Matrix.unitaryGroup A ℂ)
    (rho : DensityState A) : conjugateState U (conjugateState (star U) rho) = rho := by
  apply Subtype.ext
  apply CStarMatrix.ofMatrix.symm.injective
  rw [conjugateState_value, conjugateState_value]
  simp only [Unitary.coe_star, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_conjTranspose]
  change U.val * (U.valᴴ * CStarMatrix.ofMatrix.symm rho.1 * U.val) * U.valᴴ = _
  calc
    _ = (U.val * U.valᴴ) * CStarMatrix.ofMatrix.symm rho.1 * (U.val * U.valᴴ) := by
      simp only [Matrix.mul_assoc]
    _ = _ := by rw [show U.val * U.valᴴ = 1 from Unitary.coe_mul_star_self U]; simp

private theorem tensor_conjugate_block (U : Matrix C B ℂ)
    (X : Matrix (A × B) (A × B) ℂ) (a b : A) :
    (((1 : Matrix A A ℂ) ⊗ₖ U) * X * ((1 : Matrix A A ℂ) ⊗ₖ U)ᴴ).submatrix
        (fun j => (a, j)) (fun k => (b, k)) =
      U * X.submatrix (fun j => (a, j)) (fun k => (b, k)) * Uᴴ := by
  ext j k
  simp [Matrix.mul_apply, Fintype.sum_prod_type, Matrix.conjTranspose_apply,
    Matrix.one_apply, apply_ite]

private theorem referenceState_conjugate (U : Matrix.unitaryGroup B ℂ)
    (P : DensityState (A × B)) :
    referenceState (conjugateChannel U) P = conjugateState (tensorUnitary 1 U) P := by
  apply Subtype.ext
  apply CStarMatrix.ofMatrix.symm.injective
  ext ⟨a,j⟩ ⟨b,k⟩
  have h := congrFun (congrFun (tensor_conjugate_block U.val
    (CStarMatrix.ofMatrix.symm P.1) a b) j) k
  exact h.symm

private theorem referenceState_comp (T : QuantumChannel B C)
    (S : QuantumChannel A B) {R : Type*} [Fintype R] [DecidableEq R]
    (P : DensityState (R × A)) :
    referenceState (T.comp S) P = referenceState T (referenceState S P) := by
  apply Subtype.ext
  apply CStarMatrix.ext
  rintro ⟨a,j⟩ ⟨b,k⟩
  rfl

/-- Rotate the input and the same output B coordinate of the physical channel. -/
def localBChannel (U : Matrix.unitaryGroup B ℂ) (T : QuantumChannel B (B × C)) :
    QuantumChannel B (B × C) :=
  (conjugateChannel (tensorUnitary (star U) 1)).comp (T.comp (conjugateChannel U))

private theorem localBChannel_reference (U : Matrix.unitaryGroup B ℂ)
    (T : QuantumChannel B (B × C)) (P : DensityState (A × B)) :
    referenceState (localBChannel U T) (conjugateState (tensorUnitary 1 (star U)) P) =
      conjugateState (tensorUnitary 1 (tensorUnitary (star U) 1)) (referenceState T P) := by
  rw [localBChannel, referenceState_comp, referenceState_comp,
    referenceState_conjugate, referenceState_conjugate]
  have ht : tensorUnitary (1 : Matrix.unitaryGroup A ℂ) (star U) =
      star (tensorUnitary (1 : Matrix.unitaryGroup A ℂ) U) := by
    apply Subtype.ext
    simp [tensorUnitary, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_kronecker]
  rw [ht, conjugateState_inverse]

private theorem traceDistance_conjugateState (U : Matrix.unitaryGroup A ℂ)
    (rho sigma : DensityState A) :
    traceDistance (conjugateState U rho) (conjugateState U sigma) =
      traceDistance rho sigma := by
  unfold traceDistance
  rw [conjugateState_value, conjugateState_value]
  rw [← Matrix.sub_mul, ← Matrix.mul_sub]
  rw [D5.S3.Quantum.Entanglement.ConicalDesignConcurrenceComparability.traceNorm_isometry
    U.val (Unitary.coe_star_mul_self U)]

private theorem partialTraceLeft_isometries
    (U : Matrix.unitaryGroup A ℂ) (V : Matrix B B ℂ)
    (D : Matrix (A × B) (A × B) ℂ) :
    partialTraceLeft ((U.val ⊗ₖ V) * D * (U.val ⊗ₖ V)ᴴ) =
      V * partialTraceLeft D * Vᴴ := by
  let e := Equiv.prodComm B A
  have hs (M : Matrix (A × B) (A × B) ℂ) :
      partialTraceLeft M = partialTraceRight (M.submatrix e e) := rfl
  rw [hs]
  have ht : ((U.val ⊗ₖ V) * D * (U.val ⊗ₖ V)ᴴ).submatrix e e =
      (V ⊗ₖ U.val) * D.submatrix e e * (V ⊗ₖ U.val)ᴴ := by
    rw [← Matrix.submatrix_mul_equiv _ _ e e e,
      ← Matrix.submatrix_mul_equiv _ _ e e e]
    have hk : (U.val ⊗ₖ V).submatrix e e = V ⊗ₖ U.val := by
      ext i j
      simp [e, mul_comm]
    rw [hk, ← Matrix.conjTranspose_submatrix, hk]
  rw [ht]
  exact D5.S3.Quantum.Measurement.AnticoherenceSpinCovariance.partialTrace_isometries
    V U.val (Unitary.coe_star_mul_self U) (D.submatrix e e)

private theorem marginalRight_conjugate (U : Matrix.unitaryGroup A ℂ)
    (V : Matrix.unitaryGroup B ℂ) (P : DensityState (A × B)) :
    marginalRight (conjugateState (tensorUnitary U V) P) =
      conjugateState U (marginalRight P) := by
  apply Subtype.ext
  apply CStarMatrix.ofMatrix.symm.injective
  change partialTraceRight (CStarMatrix.ofMatrix.symm
    (conjugateState (tensorUnitary U V) P).1) = _
  rw [conjugateState_value, conjugateState_value]
  exact D5.S3.Quantum.Measurement.AnticoherenceSpinCovariance.partialTrace_isometries
    U.val V.val (Unitary.coe_star_mul_self V) (CStarMatrix.ofMatrix.symm P.1)

private theorem marginalLeft_conjugate (U : Matrix.unitaryGroup A ℂ)
    (V : Matrix.unitaryGroup B ℂ) (P : DensityState (A × B)) :
    marginalLeft (conjugateState (tensorUnitary U V) P) =
      conjugateState V (marginalLeft P) := by
  apply Subtype.ext
  apply CStarMatrix.ofMatrix.symm.injective
  change partialTraceLeft (CStarMatrix.ofMatrix.symm
    (conjugateState (tensorUnitary U V) P).1) = _
  rw [conjugateState_value, conjugateState_value]
  exact partialTraceLeft_isometries U V.val (CStarMatrix.ofMatrix.symm P.1)

private theorem productState_conjugate (U : Matrix.unitaryGroup A ℂ)
    (V : Matrix.unitaryGroup B ℂ) (a : DensityState A) (b : DensityState B) :
    productState (conjugateState U a) (conjugateState V b) =
      conjugateState (tensorUnitary U V) (productState a b) := by
  apply Subtype.ext
  apply CStarMatrix.ofMatrix.symm.injective
  change CStarMatrix.ofMatrix.symm (conjugateState U a).1 ⊗ₖ
    CStarMatrix.ofMatrix.symm (conjugateState V b).1 = _
  rw [conjugateState_value, conjugateState_value, conjugateState_value]
  change (U.val * CStarMatrix.ofMatrix.symm a.1 * U.valᴴ) ⊗ₖ
      (V.val * CStarMatrix.ofMatrix.symm b.1 * V.valᴴ) =
    (U.val ⊗ₖ V.val) * (CStarMatrix.ofMatrix.symm a.1 ⊗ₖ
      CStarMatrix.ofMatrix.symm b.1) * (U.val ⊗ₖ V.val)ᴴ
  rw [Matrix.conjTranspose_kronecker,
    ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]

/-- Change the B coordinate of the same physical ABC density state. -/
def localBState (U : Matrix.unitaryGroup B ℂ) (rho : DensityState (A × (B × C))) :
    DensityState (A × (B × C)) :=
  conjugateState (tensorUnitary 1 (tensorUnitary (star U) 1)) rho

private theorem localBState_assoc (U : Matrix.unitaryGroup B ℂ)
    (rho : DensityState (A × (B × C))) :
    relabelState (Equiv.prodAssoc A B C) (localBState U rho) =
      conjugateState (tensorUnitary (tensorUnitary 1 (star U)) 1)
        (relabelState (Equiv.prodAssoc A B C) rho) := by
  apply Subtype.ext
  apply CStarMatrix.ofMatrix.symm.injective
  change (CStarMatrix.ofMatrix.symm (localBState U rho).1).submatrix
    (Equiv.prodAssoc A B C) (Equiv.prodAssoc A B C) = _
  rw [localBState, conjugateState_value, conjugateState_value]
  rw [← Matrix.submatrix_mul_equiv _ _ _ (Equiv.prodAssoc A B C) _,
    ← Matrix.submatrix_mul_equiv _ _ _ (Equiv.prodAssoc A B C) _]
  have hl : (tensorUnitary 1 (tensorUnitary (star U) (1 : Matrix.unitaryGroup C ℂ))).val.submatrix
      (Equiv.prodAssoc A B C) (Equiv.prodAssoc A B C) =
      (tensorUnitary (tensorUnitary (1 : Matrix.unitaryGroup A ℂ) (star U))
        (1 : Matrix.unitaryGroup C ℂ)).val := by
    ext i j
    simp [tensorUnitary, mul_assoc]
  rw [hl, ← Matrix.conjTranspose_submatrix, hl]
  rfl

private theorem localBState_AB (U : Matrix.unitaryGroup B ℂ)
    (rho : DensityState (A × (B × C))) :
    marginalRight (relabelState (Equiv.prodAssoc A B C) (localBState U rho)) =
      conjugateState (tensorUnitary 1 (star U))
        (marginalRight (relabelState (Equiv.prodAssoc A B C) rho)) := by
  rw [localBState_assoc, marginalRight_conjugate]

private theorem localBState_BC (U : Matrix.unitaryGroup B ℂ)
    (rho : DensityState (A × (B × C))) :
    marginalLeft (localBState U rho) =
      conjugateState (tensorUnitary (star U) 1) (marginalLeft rho) := by
  exact marginalLeft_conjugate 1 (tensorUnitary (star U) 1) rho

private theorem localBState_B (U : Matrix.unitaryGroup B ℂ)
    (rho : DensityState (A × (B × C))) :
    marginalRight (marginalLeft (localBState U rho)) =
      conjugateState (star U) (marginalRight (marginalLeft rho)) := by
  rw [localBState_BC, marginalRight_conjugate]

private theorem localBState_inverse (U : Matrix.unitaryGroup B ℂ)
    (rho : DensityState (A × (B × C))) : localBState (star U) (localBState U rho) = rho := by
  unfold localBState
  have ht : tensorUnitary (1 : Matrix.unitaryGroup A ℂ)
      (tensorUnitary (star U) (1 : Matrix.unitaryGroup C ℂ)) =
      star (tensorUnitary (1 : Matrix.unitaryGroup A ℂ)
        (tensorUnitary (star (star U)) (1 : Matrix.unitaryGroup C ℂ))) := by
    apply Subtype.ext
    simp [tensorUnitary, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_kronecker]
  rw [ht, conjugateState_inverse]

private theorem qcmi_localBState (U : Matrix.unitaryGroup B ℂ)
    (rho : DensityState (A × (B × C))) :
    qcmi (D5.S3.Quantum.Foundation.FiniteDensityPurification.toMState (localBState U rho)) =
      qcmi (D5.S3.Quantum.Foundation.FiniteDensityPurification.toMState rho) := by
  rw [MarkovConstructors.qcmi_eq_four_marginals, MarkovConstructors.qcmi_eq_four_marginals,
    localBState_AB, localBState_B, localBState_BC]
  simp only [localBState, entropy_conjugateState]

end UnitaryTransport

section PhysicalRepair

variable {A B C : Type*} [Fintype A] [DecidableEq A]
  [Fintype B] [DecidableEq B] [Fintype C] [DecidableEq C]

private def referenceRaw (T : QuantumChannel B C) :
    Matrix (A × B) (A × B) ℂ →ₗ[ℂ] Matrix (A × C) (A × C) ℂ :=
  CStarMatrix.ofMatrixₗ.symm.toLinearMap.comp
    ((referenceLinear T).comp CStarMatrix.ofMatrixₗ.toLinearMap)

private theorem referenceRaw_contract (T : QuantumChannel B C)
    (X : Matrix (A × B) (A × B) ℂ) (hX : X.IsHermitian) :
    traceNorm (referenceRaw T X) ≤ traceNorm X := by
  apply D5.S3.Quantum.Divergence.FaithfulConditionalGap.positive_trace_contraction
    (referenceRaw T) _ _ X hX
  · intro Y hY
    exact map_nonneg CStarMatrix.ofMatrixStarAlgEquiv.symm
      (referenceAction_nonneg T (CStarMatrix.ofMatrix Y)
        (map_nonneg CStarMatrix.ofMatrixStarAlgEquiv hY))
  · intro Y
    exact referenceAction_trace T (CStarMatrix.ofMatrix Y)

private theorem referenceState_contract (T : QuantumChannel B C)
    (P Q : DensityState (A × B)) :
    traceDistance (referenceState T P) (referenceState T Q) ≤ traceDistance P Q := by
  have hc := referenceRaw_contract T
    (CStarMatrix.ofMatrix.symm P.1 - CStarMatrix.ofMatrix.symm Q.1)
    ((density_posSemidef P).isHermitian.sub (density_posSemidef Q).isHermitian)
  have he : referenceRaw T
      (CStarMatrix.ofMatrix.symm P.1 - CStarMatrix.ofMatrix.symm Q.1) =
      CStarMatrix.ofMatrix.symm (referenceState T P).1 -
        CStarMatrix.ofMatrix.symm (referenceState T Q).1 := by
    rw [map_sub]
    rfl
  rw [he] at hc
  exact div_le_div_of_nonneg_right hc (by norm_num)

private theorem referenceState_product (T : QuantumChannel B C)
    (a : DensityState A) (b : DensityState B) :
    referenceState T (productState a b) = productState a (T.mapState b) := by
  apply Subtype.ext
  apply CStarMatrix.ext
  rintro ⟨i, u⟩ ⟨j, v⟩
  change T.toCompletelyPositiveMap
    (CStarMatrix.ofMatrix (fun x y => a.1 i j * b.1 x y)) u v =
      a.1 i j * T.toCompletelyPositiveMap b.1 u v
  have he : CStarMatrix.ofMatrix (fun x y => a.1 i j * b.1 x y) =
      a.1 i j • b.1 := rfl
  rw [he, map_smul]
  rfl

private theorem cstar_sum_entry {I : Type*} [Fintype I]
    (f : I → CStarMatrix B B ℂ) (i j : B) :
    (∑ k, f k) i j = ∑ k, f k i j := by
  classical
  suffices h : ∀ s : Finset I, (∑ k ∈ s, f k) i j = ∑ k ∈ s, f k i j by
    simpa only [Finset.mem_univ, Finset.sum_const_zero, if_true] using h Finset.univ
  intro s
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, CStarMatrix.zero_apply]
  | @insert k s hk ih =>
    simp only [Finset.sum_insert hk, CStarMatrix.add_apply, ih]

private theorem slice_sub (D E : Matrix (A × B) (A × B) ℂ)
    (F : CStarMatrix A A ℂ) :
    sliceLinear (D - E) F = sliceLinear D F - sliceLinear E F := by
  apply CStarMatrix.ext
  intro j k
  change Matrix.trace (CStarMatrix.ofMatrix.symm F *
    (block D j k - block E j k)) = _
  rw [Matrix.mul_sub, Matrix.trace_sub]
  rfl

private theorem slice_expansion (D : Matrix (A × B) (A × B) ℂ)
    (F : Matrix A A ℂ) : sliceLinear D (CStarMatrix.ofMatrix F) =
      ∑ a : A, ∑ b : A, F a b •
        CStarMatrix.ofMatrix (D.submatrix (fun j => (b, j)) (fun k => (a, k))) := by
  apply CStarMatrix.ext
  intro j k
  change (∑ a : A, ∑ b : A, F a b * D (b, j) (a, k)) =
    (∑ a : A, ∑ b : A, F a b •
      CStarMatrix.ofMatrix (D.submatrix (fun j => (b, j)) (fun k => (a, k)))) j k
  simp only [cstar_sum_entry, CStarMatrix.smul_apply,
    CStarMatrix.ofMatrix_apply, Matrix.submatrix_apply, smul_eq_mul]

private theorem slice_reference (T : QuantumChannel B C)
    (D : Matrix (A × B) (A × B) ℂ) (F : Matrix A A ℂ) :
    sliceLinear (referenceRaw T D) (CStarMatrix.ofMatrix F) =
      T.toCompletelyPositiveMap (sliceLinear D (CStarMatrix.ofMatrix F)) := by
  rw [slice_expansion D F]
  simp only [map_sum, map_smul]
  apply CStarMatrix.ext
  intro u v
  change (∑ a : A, ∑ b : A, F a b *
    T.toCompletelyPositiveMap
      (CStarMatrix.ofMatrix (D.submatrix (fun j => (b, j)) (fun k => (a, k)))) u v) =
    (∑ a : A, ∑ b : A, F a b • T.toCompletelyPositiveMap
      (CStarMatrix.ofMatrix (D.submatrix (fun j => (b, j)) (fun k => (a, k))))) u v
  simp only [cstar_sum_entry, CStarMatrix.smul_apply, smul_eq_mul]

private theorem referenceRaw_conjugate (U : Matrix.unitaryGroup B ℂ)
    (D : Matrix (A × B) (A × B) ℂ) :
    referenceRaw (conjugateChannel U) D =
      ((1 : Matrix A A ℂ) ⊗ₖ U.val) * D * ((1 : Matrix A A ℂ) ⊗ₖ U.val)ᴴ := by
  ext ⟨a,j⟩ ⟨b,k⟩
  exact (congrFun (congrFun (tensor_conjugate_block U.val D a b) j) k).symm

private theorem centered_conjugate (U : Matrix.unitaryGroup (Fin 2) ℂ)
    (P : DensityState (A × Fin 2)) :
    centered (conjugateState (tensorUnitary 1 (star U)) P) =
      ((1 : Matrix A A ℂ) ⊗ₖ U.valᴴ) * centered P *
        ((1 : Matrix A A ℂ) ⊗ₖ U.valᴴ)ᴴ := by
  unfold centered
  rw [marginalRight_conjugate, marginalLeft_conjugate,
    productState_conjugate, conjugateState_value, conjugateState_value]
  change ((1 : Matrix A A ℂ) ⊗ₖ U.valᴴ) * CStarMatrix.ofMatrix.symm P.1 *
      ((1 : Matrix A A ℂ) ⊗ₖ U.valᴴ)ᴴ -
    ((1 : Matrix A A ℂ) ⊗ₖ U.valᴴ) *
      CStarMatrix.ofMatrix.symm (productState (marginalRight P) (marginalLeft P)).1 *
        ((1 : Matrix A A ℂ) ⊗ₖ U.valᴴ)ᴴ = _
  rw [Matrix.mul_sub, Matrix.sub_mul]

private theorem slice_centered_conjugate (U : Matrix.unitaryGroup (Fin 2) ℂ)
    (P : DensityState (A × Fin 2)) (F : CStarMatrix A A ℂ) :
    sliceLinear (centered (conjugateState (tensorUnitary 1 (star U)) P)) F =
      conjugateAlg (star U) (sliceLinear (centered P) F) := by
  rw [centered_conjugate]
  have hr := referenceRaw_conjugate (A := A) (star U) (centered P)
  simp only [Unitary.coe_star, Matrix.star_eq_conjTranspose] at hr
  rw [← hr]
  exact slice_reference (conjugateChannel (star U)) (centered P) (CStarMatrix.ofMatrix.symm F)

/-- The state, its actual marginals, the channel and its actual recovered state
are transported together. The half trace distance, every centered slice norm,
and the ordinary four-entropy conditional mutual information are preserved. -/
theorem actual_B_unitary_transport (U : Matrix.unitaryGroup (Fin 2) ℂ)
    (rho : DensityState (A × (Fin 2 × C)))
    (T : QuantumChannel (Fin 2) (Fin 2 × C)) :
    let P := marginalRight (relabelState (Equiv.prodAssoc A (Fin 2) C) rho)
    let PU := conjugateState (tensorUnitary 1 (star U)) P
    let rhoU := localBState U rho
    let TU := localBChannel U T
    marginalRight (relabelState (Equiv.prodAssoc A (Fin 2) C) rhoU) = PU ∧
    referenceState TU PU = localBState U (referenceState T P) ∧
    marginalLeft PU = conjugateState (star U) (marginalLeft P) ∧
    (∀ F : CStarMatrix A A ℂ,
      sliceLinear (centered PU) F = conjugateAlg (star U) (sliceLinear (centered P) F) ∧
      ‖sliceLinear (centered PU) F‖ = ‖sliceLinear (centered P) F‖) ∧
    traceDistance rhoU (referenceState TU PU) = traceDistance rho (referenceState T P) ∧
    qcmi (D5.S3.Quantum.Foundation.FiniteDensityPurification.toMState rhoU) =
      qcmi (D5.S3.Quantum.Foundation.FiniteDensityPurification.toMState rho) ∧
    (∀ sigma : DensityState (A × (Fin 2 × C)),
      traceDistance rho (localBState (star U) sigma) = traceDistance rhoU sigma ∧
      qcmi (D5.S3.Quantum.Foundation.FiniteDensityPurification.toMState
        (localBState (star U) sigma)) =
        qcmi (D5.S3.Quantum.Foundation.FiniteDensityPurification.toMState sigma)) := by
  dsimp only
  refine ⟨localBState_AB U rho, localBChannel_reference U T _,
    marginalLeft_conjugate 1 (star U) _, ?_, ?_, qcmi_localBState U rho, ?_⟩
  · intro F
    refine ⟨slice_centered_conjugate U _ F, ?_⟩
    rw [slice_centered_conjugate, StarAlgEquiv.norm_map]
  · rw [localBChannel_reference]
    exact traceDistance_conjugateState _ _ _
  · intro sigma
    refine ⟨?_, qcmi_localBState (star U) sigma⟩
    have h := traceDistance_conjugateState
      (tensorUnitary (1 : Matrix.unitaryGroup A ℂ)
        (tensorUnitary (star U) (1 : Matrix.unitaryGroup C ℂ)))
      rho (localBState (star U) sigma)
    change traceDistance (localBState U rho)
      (localBState U (localBState (star U) sigma)) = _ at h
    rw [show localBState U (localBState (star U) sigma) = sigma from
      by simpa only [star_star] using localBState_inverse (star U) sigma] at h
    exact h.symm

private def partialTraceRightLinear :
    Matrix (A × B) (A × B) ℂ →ₗ[ℂ] Matrix A A ℂ where
  toFun := partialTraceRight
  map_add' := partialTraceRight_add
  map_smul' z D := by ext a b; simp [partialTraceRight, Finset.mul_sum]

private theorem partialTraceRight_contract (D : Matrix (A × B) (A × B) ℂ)
    (hD : D.IsHermitian) : traceNorm (partialTraceRight D) ≤ traceNorm D := by
  apply D5.S3.Quantum.Divergence.FaithfulConditionalGap.positive_trace_contraction
    partialTraceRightLinear _ _ D hD
  · intro X hX
    exact (partialTraceRight_posSemidef (Matrix.nonneg_iff_posSemidef.mp hX)).nonneg
  · exact trace_partialTraceRight

private def partialTraceLeftLinear :
    Matrix (A × B) (A × B) ℂ →ₗ[ℂ] Matrix B B ℂ where
  toFun := partialTraceLeft
  map_add' := partialTraceLeft_add
  map_smul' z D := by ext a b; simp [partialTraceLeft, Finset.mul_sum]

private theorem partialTraceLeft_contract (D : Matrix (A × B) (A × B) ℂ)
    (hD : D.IsHermitian) : traceNorm (partialTraceLeft D) ≤ traceNorm D := by
  apply D5.S3.Quantum.Divergence.FaithfulConditionalGap.positive_trace_contraction
    partialTraceLeftLinear _ _ D hD
  · intro X hX
    exact (partialTraceLeft_posSemidef (Matrix.nonneg_iff_posSemidef.mp hX)).nonneg
  · exact trace_partialTraceLeft

private def tensorLeft : Matrix A A ℂ →⋆ₐ[ℂ] Matrix (A × B) (A × B) ℂ where
  toFun F := F ⊗ₖ (1 : Matrix B B ℂ)
  map_one' := Matrix.one_kronecker_one
  map_mul' F G := by rw [← Matrix.mul_kronecker_mul, Matrix.one_mul]
  map_zero' := Matrix.zero_kronecker _
  map_add' F G := Matrix.add_kronecker _ _ _
  commutes' z := by simp [Algebra.algebraMap_eq_smul_one, Matrix.smul_kronecker]
  map_star' F := by simp only [star, Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one]

private def tensorRight : Matrix B B ℂ →⋆ₐ[ℂ] Matrix (A × B) (A × B) ℂ where
  toFun F := (1 : Matrix A A ℂ) ⊗ₖ F
  map_one' := Matrix.one_kronecker_one
  map_mul' F G := by rw [← Matrix.mul_kronecker_mul, Matrix.one_mul]
  map_zero' := Matrix.kronecker_zero _
  map_add' F G := Matrix.kronecker_add _ _ _
  commutes' z := by simp [Algebra.algebraMap_eq_smul_one, Matrix.kronecker_smul]
  map_star' F := by simp only [star, Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one]

private theorem tensor_operatorNorm_le (F : Matrix A A ℂ) (G : Matrix B B ℂ) :
    ‖F ⊗ₖ G‖ ≤ ‖F‖ * ‖G‖ := by
  have he : F ⊗ₖ G = tensorLeft (B := B) F * tensorRight (A := A) G := by
    change F ⊗ₖ G = (F ⊗ₖ 1) * (1 ⊗ₖ G)
    rw [← Matrix.mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul]
  rw [he]
  exact (norm_mul_le _ _).trans
    (mul_le_mul (NonUnitalStarAlgHom.norm_apply_le tensorLeft F)
      (NonUnitalStarAlgHom.norm_apply_le tensorRight G) (norm_nonneg _) (norm_nonneg _))

private theorem slice_hermitian (D : Matrix (A × B) (A × B) ℂ)
    (hD : D.IsHermitian) (F : Matrix A A ℂ) (hF : F.IsHermitian) :
    (CStarMatrix.ofMatrix.symm (sliceLinear D (CStarMatrix.ofMatrix F))).IsHermitian := by
  have hb (j k : B) : (block D j k)ᴴ = block D k j := by
    ext a b
    exact congrFun (congrFun hD.eq (a, k)) (b, j)
  ext j k
  change star (Matrix.trace (F * block D k j)) = Matrix.trace (F * block D j k)
  rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, hF.eq, hb,
    Matrix.trace_mul_comm]

private theorem slice_trace_zero (P : DensityState (A × Fin 2))
    (F : Matrix A A ℂ) :
    Matrix.trace (CStarMatrix.ofMatrix.symm (sliceLinear (centered P)
      (CStarMatrix.ofMatrix F))) = 0 := by
  have hz := (centered_marginals_zero P).2
  have he : block (centered P) 0 0 + block (centered P) 1 1 = 0 := by
    ext a b
    simpa only [partialTraceRight, Fin.sum_univ_two, block,
      Matrix.add_apply, Matrix.submatrix_apply, Matrix.zero_apply] using
      congrFun (congrFun hz a) b
  rw [Matrix.trace, Fin.sum_univ_two]
  change Matrix.trace (F * block (centered P) 0 0) +
    Matrix.trace (F * block (centered P) 1 1) = 0
  rw [← Matrix.trace_add, ← Matrix.mul_add, he, Matrix.mul_zero, Matrix.trace_zero]

private theorem slice_tensor_pairing (D : Matrix (A × B) (A × B) ℂ)
    (F : Matrix A A ℂ) (G : Matrix B B ℂ) :
    Matrix.trace ((F ⊗ₖ G) * D) =
      Matrix.trace (G * CStarMatrix.ofMatrix.symm (sliceLinear D (CStarMatrix.ofMatrix F))) := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Fintype.sum_prod_type,
    Matrix.kronecker_apply]
  change (∑ a : A, ∑ j : B, ∑ b : A, ∑ k : B,
    F a b * G j k * D (b, k) (a, j)) =
    ∑ j : B, ∑ k : B, G j k *
      ∑ a : A, ∑ b : A, F a b * D (b, k) (a, j)
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.sum_comm]
  calc
    _ = ∑ b : A, ∑ k : B, ∑ a : A,
        G j k * (F a b * D (b, k) (a, j)) := by
      apply Finset.sum_congr rfl
      intro b hb
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k hk
      apply Finset.sum_congr rfl
      intro a ha
      ring
    _ = _ := by rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro k hk; rw [Finset.sum_comm]

private theorem slice_traceNorm_contract (D : Matrix (A × B) (A × B) ℂ)
    (hD : D.IsHermitian) (F : Matrix A A ℂ) (hF : F.IsHermitian) (hn : ‖F‖ ≤ 1) :
    traceNorm (CStarMatrix.ofMatrix.symm (sliceLinear D (CStarMatrix.ofMatrix F))) ≤
      traceNorm D := by
  apply D5.S3.Quantum.Foundation.FiniteHermitianTraceDuality.hermitian_traceNorm_le_tests
    _ (slice_hermitian D hD F hF)
  intro G hG hgn
  rw [← slice_tensor_pairing]
  have hc : ‖F ⊗ₖ G‖ ≤ 1 :=
    (tensor_operatorNorm_le F G).trans (by nlinarith [norm_nonneg F, norm_nonneg G])
  exact (D5.S3.Quantum.Matrix.UniformVarianceTraceBound.re_trace_mul_le _ D).trans
    (mul_le_of_le_one_left (traceNorm_nonneg D) hc)

private def abTrace : Matrix (A × (B × C)) (A × (B × C)) ℂ →ₗ[ℂ]
    Matrix (A × B) (A × B) ℂ where
  toFun D := partialTraceRight (D.submatrix (Equiv.prodAssoc A B C) (Equiv.prodAssoc A B C))
  map_add' D E := by ext a b; simp [partialTraceRight, Finset.sum_add_distrib]
  map_smul' z D := by ext a b; simp [partialTraceRight, Finset.mul_sum]

private theorem abTrace_contract (D : Matrix (A × (B × C)) (A × (B × C)) ℂ)
    (hD : D.IsHermitian) : traceNorm (abTrace D) ≤ traceNorm D := by
  have h := partialTraceRight_contract
    (D.submatrix (Equiv.prodAssoc A B C) (Equiv.prodAssoc A B C))
    (hD.submatrix _)
  rw [D5.S3.Quantum.Entanglement.PermutationCriteria.NormInvariance.traceNorm_submatrix_equiv] at h
  exact h

private theorem slice_abTrace (D : Matrix (A × (B × C)) (A × (B × C)) ℂ)
    (F : Matrix A A ℂ) :
    sliceLinear (abTrace D) (CStarMatrix.ofMatrix F) =
      CStarMatrix.ofMatrix (partialTraceRight
        (CStarMatrix.ofMatrix.symm (sliceLinear D (CStarMatrix.ofMatrix F)))) := by
  apply CStarMatrix.ext
  intro j k
  change (∑ a : A, ∑ b : A, F a b * ∑ c : C, D (b, (j, c)) (a, (k, c))) =
    ∑ c : C, ∑ a : A, ∑ b : A, F a b * D (b, (j, c)) (a, (k, c))
  simp_rw [Finset.mul_sum]
  calc
    _ = ∑ a : A, ∑ c : C, ∑ b : A, F a b * D (b, (j, c)) (a, (k, c)) := by
      apply Finset.sum_congr rfl
      intro a ha
      exact Finset.sum_comm
    _ = _ := Finset.sum_comm

private def reducedAction (T : QuantumChannel B (B × C)) :
    CStarMatrix B B ℂ →ₗ[ℂ] CStarMatrix B B ℂ :=
  CStarMatrix.ofMatrixₗ.toLinearMap.comp
    (partialTraceRightLinear.comp
      (CStarMatrix.ofMatrixₗ.symm.toLinearMap.comp T.toCompletelyPositiveMap.toLinearMap))

private def reducedReference (T : QuantumChannel B (B × C)) :
    Matrix (A × B) (A × B) ℂ →ₗ[ℂ] Matrix (A × B) (A × B) ℂ :=
  abTrace.comp (referenceRaw T)

private theorem slice_reducedReference (T : QuantumChannel B (B × C))
    (D : Matrix (A × B) (A × B) ℂ) (F : Matrix A A ℂ) :
    sliceLinear (reducedReference T D) (CStarMatrix.ofMatrix F) =
      reducedAction T (sliceLinear D (CStarMatrix.ofMatrix F)) := by
  change sliceLinear (abTrace (referenceRaw T D)) (CStarMatrix.ofMatrix F) = _
  rw [slice_abTrace, slice_reference]
  rfl

private theorem actual_AB_residual (rho : DensityState (A × (B × C)))
    (T : QuantumChannel B (B × C)) :
    let P := marginalRight (relabelState (Equiv.prodAssoc A B C) rho)
    traceNorm (CStarMatrix.ofMatrix.symm P.1 -
      reducedReference T (CStarMatrix.ofMatrix.symm P.1)) ≤
      2 * traceDistance rho (referenceState T P) := by
  dsimp only
  let P := marginalRight (relabelState (Equiv.prodAssoc A B C) rho)
  let tau := referenceState T P
  have hc := abTrace_contract
    (CStarMatrix.ofMatrix.symm rho.1 - CStarMatrix.ofMatrix.symm tau.1)
    ((density_posSemidef rho).isHermitian.sub (density_posSemidef tau).isHermitian)
  rw [map_sub] at hc
  change traceNorm (CStarMatrix.ofMatrix.symm P.1 -
    reducedReference T (CStarMatrix.ofMatrix.symm P.1)) ≤ _ at hc
  change traceNorm _ ≤ 2 * (traceNorm _ / 2)
  linarith

private theorem slice_one (D : Matrix (A × B) (A × B) ℂ) :
    sliceLinear D 1 = CStarMatrix.ofMatrix (partialTraceLeft D) := by
  apply CStarMatrix.ext
  intro j k
  change (∑ a : A, ∑ b : A, (1 : Matrix A A ℂ) a b * D (b, j) (a, k)) =
    ∑ a : A, D (a, j) (a, k)
  simp [Matrix.one_apply]

private theorem reducedReference_left (T : QuantumChannel B (B × C))
    (D : Matrix (A × B) (A × B) ℂ) :
    CStarMatrix.ofMatrix (partialTraceLeft (reducedReference T D)) =
      reducedAction T (CStarMatrix.ofMatrix (partialTraceLeft D)) := by
  have h := slice_reducedReference T D (1 : Matrix A A ℂ)
  simpa only [CStarMatrix.ofMatrix_eq_ofMatrixStarAlgEquiv, map_one, slice_one] using h

private theorem actual_B_residual (rho : DensityState (A × (B × C)))
    (T : QuantumChannel B (B × C)) :
    let P := marginalRight (relabelState (Equiv.prodAssoc A B C) rho)
    traceNorm (CStarMatrix.ofMatrix.symm (marginalLeft P).1 -
      CStarMatrix.ofMatrix.symm (reducedAction T (marginalLeft P).1)) ≤
      2 * traceDistance rho (referenceState T P) := by
  dsimp only
  let P := marginalRight (relabelState (Equiv.prodAssoc A B C) rho)
  let tau := referenceState T P
  let Q := marginalRight (relabelState (Equiv.prodAssoc A B C) tau)
  have hab := actual_AB_residual rho T
  have hc := partialTraceLeft_contract
    (CStarMatrix.ofMatrix.symm P.1 - CStarMatrix.ofMatrix.symm Q.1)
    ((density_posSemidef P).isHermitian.sub (density_posSemidef Q).isHermitian)
  have he := reducedReference_left T (CStarMatrix.ofMatrix.symm P.1)
  have hq : CStarMatrix.ofMatrix.symm Q.1 = reducedReference T (CStarMatrix.ofMatrix.symm P.1) := rfl
  have ht : partialTraceLeft
      (CStarMatrix.ofMatrix.symm P.1 - CStarMatrix.ofMatrix.symm Q.1) =
      CStarMatrix.ofMatrix.symm (marginalLeft P).1 -
        CStarMatrix.ofMatrix.symm (reducedAction T (marginalLeft P).1) := by
    change partialTraceLeftLinear (_ - _) = _
    rw [map_sub, hq]
    have he' := congrArg CStarMatrix.ofMatrix.symm he
    change partialTraceLeft _ = _ at he'
    change partialTraceLeft _ - partialTraceLeft _ = _
    rw [he']
    rfl
  rw [ht] at hc
  exact hc.trans hab

private theorem reducedReference_product (T : QuantumChannel B (B × C))
    (a : DensityState A) (b : DensityState B) :
    reducedReference T (CStarMatrix.ofMatrix.symm (productState a b).1) =
      CStarMatrix.ofMatrix.symm a.1 ⊗ₖ CStarMatrix.ofMatrix.symm (reducedAction T b.1) := by
  have h := referenceState_product T a b
  have he := congrArg (fun rho : DensityState (A × (B × C)) =>
    abTrace (CStarMatrix.ofMatrix.symm rho.1)) h
  change reducedReference T (CStarMatrix.ofMatrix.symm (productState a b).1) = _ at he
  rw [he]
  ext ⟨i, j⟩ ⟨k, l⟩
  change (∑ c : C, a.1 i k * T.toCompletelyPositiveMap b.1 (j, c) (l, c)) =
    a.1 i k * ∑ c : C, T.toCompletelyPositiveMap b.1 (j, c) (l, c)
  exact (Finset.mul_sum _ _ _).symm

/-- Every Hermitian contraction on A inherits approximate fixedness under the
actual reduced recovery channel, with the half trace-distance convention. -/
theorem all_centered_tests_residual (rho : DensityState (A × (Fin 2 × C)))
    (T : QuantumChannel (Fin 2) (Fin 2 × C))
    (F : Matrix A A ℂ) (hF : F.IsHermitian) (hn : ‖F‖ ≤ 1) :
    let P := marginalRight (relabelState (Equiv.prodAssoc A (Fin 2) C) rho)
    let K := sliceLinear (centered P) (CStarMatrix.ofMatrix F)
    traceNorm (CStarMatrix.ofMatrix.symm (reducedAction T K - K)) ≤
      4 * traceDistance rho (referenceState T P) := by
  dsimp only
  let P := marginalRight (relabelState (Equiv.prodAssoc A (Fin 2) C) rho)
  let Q := marginalRight (relabelState (Equiv.prodAssoc A (Fin 2) C) (referenceState T P))
  let a := marginalRight P
  let b := marginalLeft P
  let D := CStarMatrix.ofMatrix.symm P.1 - CStarMatrix.ofMatrix.symm Q.1
  let E := CStarMatrix.ofMatrix.symm b.1 - CStarMatrix.ofMatrix.symm (reducedAction T b.1)
  have hD : D.IsHermitian := (density_posSemidef P).isHermitian.sub
    (density_posSemidef Q).isHermitian
  have hE : E.IsHermitian := by
    have he := reducedReference_left T (CStarMatrix.ofMatrix.symm P.1)
    have he' := congrArg CStarMatrix.ofMatrix.symm he
    change CStarMatrix.ofMatrix.symm (marginalLeft Q).1 =
      CStarMatrix.ofMatrix.symm (reducedAction T b.1) at he'
    rw [show E = CStarMatrix.ofMatrix.symm b.1 -
      CStarMatrix.ofMatrix.symm (marginalLeft Q).1 from congrArg
        (fun X => CStarMatrix.ofMatrix.symm b.1 - X) he'.symm]
    exact (density_posSemidef b).isHermitian.sub (density_posSemidef (marginalLeft Q)).isHermitian
  have hd := actual_AB_residual rho T
  have hb := actual_B_residual rho T
  have he : centered P - reducedReference T (centered P) =
      D - (CStarMatrix.ofMatrix.symm a.1 ⊗ₖ E) := by
    unfold centered
    rw [map_sub, reducedReference_product]
    change (_ - _) - (_ - _) = _ - _
    ext ⟨i, j⟩ ⟨k, l⟩
    change (P.1 (i, j) (k, l) - a.1 i k * b.1 j l) -
      (Q.1 (i, j) (k, l) - a.1 i k * reducedAction T b.1 j l) =
      (P.1 (i, j) (k, l) - Q.1 (i, j) (k, l)) -
        a.1 i k * (b.1 j l - reducedAction T b.1 j l)
    ring
  have hs := slice_traceNorm_contract D hD F hF hn
  have ht := slice_traceNorm_contract (CStarMatrix.ofMatrix.symm a.1 ⊗ₖ E)
    (isHermitian_kronecker (density_posSemidef a).isHermitian hE) F hF hn
  have ha : traceNorm (CStarMatrix.ofMatrix.symm a.1) = 1 := by
    have h := traceNorm_of_posSemidef (density_posSemidef a)
    have hr := congrArg Complex.re h
    change traceNorm (CStarMatrix.ofMatrix.symm a.1) =
      (Matrix.trace (CStarMatrix.ofMatrix.symm a.1)).re at hr
    exact hr.trans (congrArg Complex.re a.2.2)
  rw [traceNorm_tensor, ha, one_mul] at ht
  have hpair := traceNorm_add_le
    (CStarMatrix.ofMatrix.symm (sliceLinear D (CStarMatrix.ofMatrix F)))
    (-CStarMatrix.ofMatrix.symm (sliceLinear (CStarMatrix.ofMatrix.symm a.1 ⊗ₖ E)
      (CStarMatrix.ofMatrix F)))
  rw [traceNorm_neg] at hpair
  have hk : CStarMatrix.ofMatrix.symm
      (reducedAction T (sliceLinear (centered P) (CStarMatrix.ofMatrix F)) -
        sliceLinear (centered P) (CStarMatrix.ofMatrix F)) =
      -(CStarMatrix.ofMatrix.symm (sliceLinear D (CStarMatrix.ofMatrix F)) -
        CStarMatrix.ofMatrix.symm (sliceLinear (CStarMatrix.ofMatrix.symm a.1 ⊗ₖ E)
          (CStarMatrix.ofMatrix F))) := by
    rw [← slice_reducedReference]
    have hh := congrArg (fun X => sliceLinear X (CStarMatrix.ofMatrix F)) he
    rw [slice_sub, slice_sub] at hh
    have hh' := congrArg CStarMatrix.ofMatrix.symm hh
    have hhentry := fun j k => congrArg (fun M : CStarMatrix (Fin 2) (Fin 2) ℂ => M j k) hh
    ext j k
    have h := hhentry j k
    change sliceLinear (centered P) (CStarMatrix.ofMatrix F) j k -
      sliceLinear (reducedReference T (centered P)) (CStarMatrix.ofMatrix F) j k =
      sliceLinear D (CStarMatrix.ofMatrix F) j k -
        sliceLinear (CStarMatrix.ofMatrix.symm a.1 ⊗ₖ E) (CStarMatrix.ofMatrix F) j k at h
    change sliceLinear (reducedReference T (centered P)) (CStarMatrix.ofMatrix F) j k -
      sliceLinear (centered P) (CStarMatrix.ofMatrix F) j k =
      -(sliceLinear D (CStarMatrix.ofMatrix F) j k -
        sliceLinear (CStarMatrix.ofMatrix.symm a.1 ⊗ₖ E) (CStarMatrix.ofMatrix F) j k)
    linear_combination -h
  rw [hk, traceNorm_neg, sub_eq_add_neg]
  change traceNorm D ≤ _ at hd
  change traceNorm E ≤ _ at hb
  linarith

private theorem traceless_qubit_diagonalization
    (K : Matrix (Fin 2) (Fin 2) ℂ) (hK : K.IsHermitian) (ht : Matrix.trace K = 0) :
    ∃ U : Matrix.unitaryGroup (Fin 2) ℂ,
      U.valᴴ * K * U.val = Matrix.diagonal ![(‖K‖ : ℂ), -(‖K‖ : ℂ)] := by
  let V := hK.eigenvectorUnitary
  let d := hK.eigenvalues
  have hsum : d 0 + d 1 = 0 := by
    have hh := congrArg RCLike.re hK.trace_eq_sum_eigenvalues
    rw [ht] at hh
    simpa only [Fin.sum_univ_two, map_add, RCLike.ofReal_re,
      map_zero] using hh.symm
  have hd : d 1 = -d 0 := by linarith
  have hv : V.valᴴ * K * V.val = Matrix.diagonal (fun i => (d i : ℂ)) := by
    simpa only [V, d, Function.comp_def, RCLike.ofReal_eq_complex_ofReal,
      Unitary.conjStarAlgAut_star_apply, Matrix.star_eq_conjTranspose] using
      hK.conjStarAlgAut_star_eigenvectorUnitary
  have hnorm : ‖K‖ = |d 0| := by
    have he : ‖K‖ = ‖fun i => (d i : ℂ)‖ := by
      conv_lhs => rw [hK.spectral_theorem]
      simp only [Unitary.conjStarAlgAut_apply, ← Unitary.coe_star,
        CStarRing.norm_mul_coe_unitary, CStarRing.norm_coe_unitary_mul,
        Matrix.l2_opNorm_diagonal]
      rfl
    rw [he]
    apply le_antisymm
    · apply (pi_norm_le_iff_of_nonneg (abs_nonneg (d 0))).mpr
      intro i
      fin_cases i <;> simp [hd, Complex.norm_real, Real.norm_eq_abs]
    · simpa only [Complex.norm_real, Real.norm_eq_abs] using
        (norm_le_pi_norm (fun i => (d i : ℂ)) (0 : Fin 2))
  by_cases hp : 0 ≤ d 0
  · refine ⟨V, hv.trans ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.diagonal_apply, hnorm, abs_of_nonneg hp, hd]
  · have hn : d 0 < 0 := lt_of_not_ge hp
    let S : Matrix.unitaryGroup (Fin 2) ℂ := ⟨pauli 0, by
      apply Matrix.mem_unitaryGroup_iff'.mpr
      ext i j
      fin_cases i <;> fin_cases j <;>
        norm_num [pauli,
          D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.pauliMatrix,
          D5.S3.Quantum.FiniteDimensional.qubitX, Matrix.mul_apply, Fin.sum_univ_two,
          Matrix.conjTranspose_apply]⟩
    refine ⟨V * S, ?_⟩
    change (V.val * S.val)ᴴ * K * (V.val * S.val) = _
    rw [Matrix.conjTranspose_mul]
    have he : S.valᴴ * V.valᴴ * K * (V.val * S.val) =
        S.valᴴ * (V.valᴴ * K * V.val) * S.val := by simp only [Matrix.mul_assoc]
    rw [he, hv]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [S, pauli,
        D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.pauliMatrix,
        D5.S3.Quantum.FiniteDimensional.qubitX, Matrix.mul_apply, Fin.sum_univ_two,
        Matrix.conjTranspose_apply, Matrix.diagonal_apply, hnorm, abs_of_neg hn, hd]

/-- Rotate the same input and output qubit coordinate to the eigenbasis of
its nonzero test, retaining the full actual physical isometry. -/
theorem diagonalized_residual_geometry {E : Type*} [Fintype E] [DecidableEq E]
    (W : Matrix (Fin 2 × E) (Fin 2) ℂ) (hW : Wᴴ * W = 1)
    (K : Matrix (Fin 2) (Fin 2) ℂ) (hK : K.IsHermitian) (ht : Matrix.trace K = 0)
    (hx : 0 < ‖K‖) (e : ℝ) (he : traceNorm (reduced W K - K) ≤ e) :
    ∃ (U : Matrix.unitaryGroup (Fin 2) ℂ)
      (V : Matrix (Fin 2 × E) (Fin 2) ℂ),
      Vᴴ * V = 1 ∧
      U.valᴴ * K * U.val = Matrix.diagonal ![(‖K‖ : ℂ), -(‖K‖ : ℂ)] ∧
      (∀ M : Matrix (Fin 2) (Fin 2) ℂ,
        reduced V M = U.valᴴ * reduced W (U.val * M * U.valᴴ) * U.val) ∧
      ‖column V 1 0‖ ^ 2 + ‖column V 0 1‖ ^ 2 ≤ (e / ‖K‖) / 2 ∧
      ‖inner ℂ (column V 1 0) (column V 0 0) -
        inner ℂ (column V 1 1) (column V 0 1)‖ ≤ (e / ‖K‖) / 2 := by
  obtain ⟨U, hu⟩ := traceless_qubit_diagonalization K hK ht
  obtain ⟨V, hv, hcov⟩ := rotated_dilation W hW U
  have huU : U.val * U.valᴴ = 1 := Unitary.coe_mul_star_self U
  refine ⟨U, V, hv, hu, hcov, ?_⟩
  let Z : Matrix (Fin 2) (Fin 2) ℂ := Matrix.diagonal ![1, -1]
  have hku : U.valᴴ * K * U.val = (‖K‖ : ℂ) • Z := by
    rw [hu]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Z]
  have hk : U.val * ((‖K‖ : ℂ) • Z) * U.valᴴ = K := by
    rw [← hku]
    calc
      _ = (U.val * U.valᴴ) * K * (U.val * U.valᴴ) := by simp [Matrix.mul_assoc]
      _ = K := by rw [huU]; simp
  have hs : (‖K‖ : ℂ) • (reduced V Z - Z) =
      U.valᴴ * (reduced W K - K) * U.val := by
    have hr : reduced V ((‖K‖ : ℂ) • Z) = (‖K‖ : ℂ) • reduced V Z := by
      ext i j
      simp [reduced, partialTraceRight, Matrix.mul_smul, Matrix.smul_mul,
        Finset.mul_sum]
    rw [smul_sub, ← hr, hcov, hk, Matrix.mul_sub, Matrix.sub_mul, hku]
  have htN : ‖K‖ * traceNorm (reduced V Z - Z) ≤ e := by
    rw [← D5.S3.Quantum.Entanglement.ConicalDesignConcurrenceComparability.traceNorm_smul_nonneg
      _ ‖K‖ (norm_nonneg _), hs]
    have hi :=
      D5.S3.Quantum.Entanglement.ConicalDesignConcurrenceComparability.traceNorm_isometry
        U.valᴴ (by simpa only [Matrix.conjTranspose_conjTranspose] using huU) (reduced W K - K)
    simpa only [Matrix.conjTranspose_conjTranspose] using hi.le.trans he
  apply diagonal_residual_controls_coefficients V hv (e / ‖K‖)
  exact (le_div_iff₀ hx).mpr (by simpa [mul_comm] using htN)

/-- Hermitian testing of the complex off-diagonal block retains the factor
of two in complex trace duality. The isometry and all tests refer to the same
centered matrix. -/
theorem complex_block_bound_of_diagonal_geometry
    {E : Type*} [Fintype E]
    (P : DensityState (A × Fin 2))
    (W : Matrix (Fin 2 × E) (Fin 2) ℂ) (hW : Wᴴ * W = 1)
    (x r : ℝ) (hx : 0 < x) (hr : 0 ≤ r)
    (hmax : ∀ F : CStarMatrix A A ℂ, IsSelfAdjoint F → ‖F‖ ≤ 1 →
      ‖sliceLinear (centered P) F‖ ≤ x)
    (hres : ∀ F : Matrix A A ℂ, F.IsHermitian → ‖F‖ ≤ 1 →
      traceNorm (reduced W (CStarMatrix.ofMatrix.symm
        (sliceLinear (centered P) (CStarMatrix.ofMatrix F))) -
        CStarMatrix.ofMatrix.symm (sliceLinear (centered P) (CStarMatrix.ofMatrix F))) ≤ 4 * r)
    (hflip : ‖column W 1 0‖ ^ 2 + ‖column W 0 1‖ ^ 2 ≤ 2 * r / x)
    (hdiff : ‖inner ℂ (column W 1 0) (column W 0 0) -
      inner ℂ (column W 1 1) (column W 0 1)‖ ≤ 2 * r / x)
    (hg : 0 < ‖1 - inner ℂ (column W 1 1) (column W 0 0)‖) :
    traceNorm (block (centered P) 0 1) ≤
      16 * r / ‖1 - inner ℂ (column W 1 1) (column W 0 0)‖ := by
  have hdual : traceNorm (block (centered P) 0 1) ≤
      2 * (8 * r / ‖1 - inner ℂ (column W 1 1) (column W 0 0)‖) := by
    apply D5.S3.Quantum.Foundation.FiniteHermitianTraceDuality.complex_traceNorm_le_twice_tests
    intro F hF hFn
    let K := CStarMatrix.ofMatrix.symm (sliceLinear (centered P) (CStarMatrix.ofMatrix F))
    have hfc : IsSelfAdjoint (CStarMatrix.ofMatrix F) :=
      (show IsSelfAdjoint F from hF).map CStarMatrix.ofMatrixStarAlgEquiv
    have hfn : ‖CStarMatrix.ofMatrix F‖ ≤ 1 := by
      change ‖CStarMatrix.ofMatrixStarAlgEquiv F‖ ≤ 1
      rw [StarAlgEquiv.norm_map]
      exact hFn
    have hkn : ‖K‖ ≤ x := by
      have hn : ‖K‖ = ‖sliceLinear (centered P) (CStarMatrix.ofMatrix F)‖ := by
        change ‖CStarMatrix.ofMatrixStarAlgEquiv.symm _‖ = _
        exact StarAlgEquiv.norm_map _ _
      rw [hn]
      exact hmax _ hfc hfn
    have hk := offDiagonal_gap_bound W hW K
      (slice_hermitian _ (centered_hermitian P) F hF) (slice_trace_zero P F)
      x (4 * r) (2 * r / x) (2 * r / x) hkn (hres F hF hFn) hflip hdiff
    have hs : ‖1 - inner ℂ (column W 1 1) (column W 0 0)‖ * ‖K 0 1‖ ≤ 8 * r := by
      have hd : x ≠ 0 := ne_of_gt hx
      have h1 : (2 * r / x) * x = 2 * r := by field_simp
      have h2 : ((2 * r / x) / 2) * x = r := by field_simp
      rw [h1, h2] at hk
      linarith
    change ‖K 0 1‖ ≤ _
    exact (le_div_iff₀ hg).mpr (by simpa [mul_comm] using hs)
  calc
    _ ≤ _ := hdual
    _ = _ := by ring

/-- The attained centered direction and the diagonal coefficient geometry
belong to one coherently transported physical state and channel. -/
theorem actual_diagonal_geometry {C : Type} [Fintype C] [DecidableEq C]
    (rho : DensityState (A × (Fin 2 × C)))
    (T : QuantumChannel (Fin 2) (Fin 2 × C))
    (F : CStarMatrix A A ℂ) (hF : IsSelfAdjoint F) (hFn : ‖F‖ ≤ 1)
    (hmax : ∀ G : CStarMatrix A A ℂ, IsSelfAdjoint G → ‖G‖ ≤ 1 →
      ‖sliceLinear (centered
        (marginalRight (relabelState (Equiv.prodAssoc A (Fin 2) C) rho))) G‖ ≤
      ‖sliceLinear (centered
        (marginalRight (relabelState (Equiv.prodAssoc A (Fin 2) C) rho))) F‖)
    (hx : 0 < ‖sliceLinear (centered
      (marginalRight (relabelState (Equiv.prodAssoc A (Fin 2) C) rho))) F‖) :
    let P := marginalRight (relabelState (Equiv.prodAssoc A (Fin 2) C) rho)
    let x := ‖sliceLinear (centered P) F‖
    let r := traceDistance rho (referenceState T P)
    ∃ (U : Matrix.unitaryGroup (Fin 2) ℂ)
      (W : Matrix (Fin 2 × (C × ((Fin 2 × C) × Fin 2))) (Fin 2) ℂ),
      Wᴴ * W = 1 ∧
      (∀ (M : Matrix (Fin 2) (Fin 2) ℂ) (j k : Fin 2) (c d : C),
        (∑ e : (Fin 2 × C) × Fin 2,
          (W * M * Wᴴ) (j, (c, e)) (k, (d, e))) =
            CStarMatrix.ofMatrix.symm
              ((localBChannel U T).toCompletelyPositiveMap (CStarMatrix.ofMatrix M))
                (j, c) (k, d)) ∧
      let PU := marginalRight (relabelState (Equiv.prodAssoc A (Fin 2) C) (localBState U rho))
      (∀ G : CStarMatrix A A ℂ, IsSelfAdjoint G → ‖G‖ ≤ 1 →
        ‖sliceLinear (centered PU) G‖ ≤ x) ∧
      (∀ G : Matrix A A ℂ, G.IsHermitian → ‖G‖ ≤ 1 →
        traceNorm (reduced W (CStarMatrix.ofMatrix.symm
          (sliceLinear (centered PU) (CStarMatrix.ofMatrix G))) -
          CStarMatrix.ofMatrix.symm (sliceLinear (centered PU) (CStarMatrix.ofMatrix G))) ≤
            4 * r) ∧
      ‖column W 1 0‖ ^ 2 + ‖column W 0 1‖ ^ 2 ≤ 2 * r / x ∧
      ‖inner ℂ (column W 1 0) (column W 0 0) -
        inner ℂ (column W 1 1) (column W 0 1)‖ ≤ 2 * r / x ∧
      (0 < ‖1 - inner ℂ (column W 1 1) (column W 0 0)‖ →
        traceNorm (block (centered PU) 0 1) ≤
          16 * r / ‖1 - inner ℂ (column W 1 1) (column W 0 0)‖) := by
  dsimp only
  let P := marginalRight (relabelState (Equiv.prodAssoc A (Fin 2) C) rho)
  let K := CStarMatrix.ofMatrix.symm (sliceLinear (centered P) F)
  let x := ‖sliceLinear (centered P) F‖
  let r := traceDistance rho (referenceState T P)
  have hFH : (CStarMatrix.ofMatrix.symm F).IsHermitian := by
    exact hF.map CStarMatrix.ofMatrixStarAlgEquiv.symm
  have hFN : ‖CStarMatrix.ofMatrix.symm F‖ ≤ 1 := by
    change ‖CStarMatrix.ofMatrixStarAlgEquiv.symm F‖ ≤ 1
    rw [StarAlgEquiv.norm_map]
    exact hFn
  have hkn : ‖K‖ = x := StarAlgEquiv.norm_map CStarMatrix.ofMatrixStarAlgEquiv.symm _
  have hkh : K.IsHermitian := slice_hermitian _ (centered_hermitian P)
    (CStarMatrix.ofMatrix.symm F) hFH
  have hkt : Matrix.trace K = 0 := slice_trace_zero P (CStarMatrix.ofMatrix.symm F)
  obtain ⟨W0, hw0, _, hr0⟩ := actual_dilation T
  have hres0 : traceNorm (reduced W0 K - K) ≤ 4 * r := by
    rw [hr0]
    exact all_centered_tests_residual rho T _ hFH hFN
  obtain ⟨U, _, _, hdiag, _, _, _⟩ := diagonalized_residual_geometry W0 hw0 K hkh hkt
    (by simpa only [hkn] using hx) (4 * r) hres0
  obtain ⟨W, hw, hout, hred⟩ := actual_dilation (localBChannel U T)
  let PU := marginalRight (relabelState (Equiv.prodAssoc A (Fin 2) C) (localBState U rho))
  have hp : PU = conjugateState (tensorUnitary 1 (star U)) P := localBState_AB U rho
  have hru : traceDistance (localBState U rho)
      (referenceState (localBChannel U T) PU) = r := by
    rw [hp, localBChannel_reference]
    exact traceDistance_conjugateState _ _ _
  have hm : ∀ G : CStarMatrix A A ℂ, IsSelfAdjoint G → ‖G‖ ≤ 1 →
      ‖sliceLinear (centered PU) G‖ ≤ x := by
    intro G hG hn
    rw [hp, slice_centered_conjugate, StarAlgEquiv.norm_map]
    exact hmax G hG hn
  have hr : ∀ G : Matrix A A ℂ, G.IsHermitian → ‖G‖ ≤ 1 →
      traceNorm (reduced W (CStarMatrix.ofMatrix.symm
        (sliceLinear (centered PU) (CStarMatrix.ofMatrix G))) -
        CStarMatrix.ofMatrix.symm (sliceLinear (centered PU) (CStarMatrix.ofMatrix G))) ≤
          4 * r := by
    intro G hG hn
    rw [hred]
    exact (all_centered_tests_residual (localBState U rho) (localBChannel U T) G hG hn).trans_eq
      (by rw [hru])
  let Z : Matrix (Fin 2) (Fin 2) ℂ := Matrix.diagonal ![1,-1]
  have hku : CStarMatrix.ofMatrix.symm (sliceLinear (centered PU) F) = (x : ℂ) • Z := by
    rw [hp, slice_centered_conjugate]
    simp only [conjugateAlg, StarAlgEquiv.trans_apply, Unitary.conjStarAlgAut_apply,
      Unitary.coe_star, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose]
    change U.valᴴ * K * U.val = _
    rw [hdiag, hkn]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Z]
  have hscale : traceNorm (reduced W Z - Z) ≤ 4 * r / x := by
    have he := hr (CStarMatrix.ofMatrix.symm F) hFH hFN
    change traceNorm (reduced W (CStarMatrix.ofMatrix.symm (sliceLinear (centered PU) F)) -
      CStarMatrix.ofMatrix.symm (sliceLinear (centered PU) F)) ≤ _ at he
    rw [hku] at he
    have heq : reduced W ((x : ℂ) • Z) - (x : ℂ) • Z = (x : ℂ) • (reduced W Z - Z) := by
      ext i j
      simp [reduced, partialTraceRight, Matrix.mul_smul, Matrix.smul_mul,
        Finset.mul_sum, mul_sub]
    rw [heq, D5.S3.Quantum.Entanglement.ConicalDesignConcurrenceComparability.traceNorm_smul_nonneg
      _ x (le_of_lt hx)] at he
    exact (le_div_iff₀ hx).mpr (by simpa only [mul_comm] using he)
  obtain ⟨hflip, hdiff⟩ := diagonal_residual_controls_coefficients W hw (4 * r / x) hscale
  have hf' : ‖column W 1 0‖ ^ 2 + ‖column W 0 1‖ ^ 2 ≤ 2 * r / x := by
    convert hflip using 1 <;> ring
  have hd' : ‖inner ℂ (column W 1 0) (column W 0 0) -
      inner ℂ (column W 1 1) (column W 0 1)‖ ≤ 2 * r / x := by
    convert hdiff using 1 <;> ring
  refine ⟨U, W, hw, hout, hm, hr, hf', hd', ?_⟩
  intro hg
  exact complex_block_bound_of_diagonal_geometry PU W hw x r hx
    (traceDistance_nonneg _ _) hm hr hf' hd' hg

/-- A small centered correlation gives a product state on the actual system. -/
theorem product_repair_of_centered_correlation
    (rho : DensityState (A × (Fin 2 × C)))
    (T : QuantumChannel (Fin 2) (Fin 2 × C)) :
    let P := marginalRight (relabelState (Equiv.prodAssoc A (Fin 2) C) rho)
    ∃ F : CStarMatrix A A ℂ, IsSelfAdjoint F ∧ ‖F‖ ≤ 1 ∧
      (∀ G : CStarMatrix A A ℂ, IsSelfAdjoint G → ‖G‖ ≤ 1 →
        ‖sliceLinear (centered P) G‖ ≤ ‖sliceLinear (centered P) F‖) ∧
      ∃ sigma : DensityState (A × (Fin 2 × C)),
        qcmi (D5.S3.Quantum.Foundation.FiniteDensityPurification.toMState sigma) = 0 ∧
        traceDistance rho sigma ≤ traceDistance rho (referenceState T P) +
          3 * ‖sliceLinear (centered P) F‖ := by
  dsimp only
  let P := marginalRight (relabelState (Equiv.prodAssoc A (Fin 2) C) rho)
  obtain ⟨F, hf, hfn, hmax, hbound⟩ := attained_centered_traceNorm_bound P
  let sigma := productState (marginalRight P) (T.mapState (marginalLeft P))
  refine ⟨F, hf, hfn, hmax, sigma,
    D5.S3.Quantum.Information.StrongSubadditivity.MarkovConstructors.qcmi_product_left _ _, ?_⟩
  have hc := referenceState_contract T P
    (productState (marginalRight P) (marginalLeft P))
  rw [referenceState_product] at hc
  have hp : traceDistance P (productState (marginalRight P) (marginalLeft P)) ≤
      3 * ‖sliceLinear (centered P) F‖ := by
    change traceNorm (centered P) / 2 ≤ _
    linarith
  exact (traceDistance_triangle rho (referenceState T P) sigma).trans
    (add_le_add le_rfl (hc.trans hp))

end PhysicalRepair

section IsometryComparison

variable {I O R : Type*} [Fintype I] [DecidableEq I]
  [Fintype O] [DecidableEq O] [Fintype R] [DecidableEq R]

private theorem isometry_operatorNorm_le (V : Matrix O I ℂ) (hV : Vᴴ * V = 1) :
    ‖V‖ ≤ 1 := by
  have h := Matrix.l2_opNorm_conjTranspose_mul_self V
  rw [hV] at h
  have ho : ‖(1 : Matrix I I ℂ)‖ ≤ 1 := by
    rcases isEmpty_or_nonempty I with hi | hi
    · have hz : (1 : Matrix I I ℂ) = 0 := Subsingleton.elim _ _
      simp [hz]
    · exact (norm_one : ‖(1 : Matrix I I ℂ)‖ = 1).le
  nlinarith [norm_nonneg V]

private def isometryState (V : Matrix O I ℂ) (hV : Vᴴ * V = 1)
    (P : DensityState I) : DensityState O := by
  refine ⟨CStarMatrix.ofMatrix (V * CStarMatrix.ofMatrix.symm P.1 * Vᴴ), ?_, ?_⟩
  · exact map_nonneg CStarMatrix.ofMatrixStarAlgEquiv
      ((density_posSemidef P).mul_mul_conjTranspose_same V).nonneg
  · change Matrix.trace (V * CStarMatrix.ofMatrix.symm P.1 * Vᴴ) = 1
    rw [Matrix.trace_mul_cycle, hV, Matrix.one_mul]
    exact P.2.2

private theorem isometryState_distance (V W : Matrix O I ℂ)
    (hV : Vᴴ * V = 1) (hW : Wᴴ * W = 1) (P : DensityState I) :
    traceDistance (isometryState V hV P) (isometryState W hW P) ≤ ‖V - W‖ := by
  let X := V * CStarMatrix.ofMatrix.symm P.1 * Vᴴ -
    W * CStarMatrix.ofMatrix.symm P.1 * Wᴴ
  obtain ⟨U, hU⟩ := (traceNorm_eq_max_re_tr_U X).1
  let B := Vᴴ * U.val * V - Wᴴ * U.val * W
  have hb : B = (V-W)ᴴ * U.val * V + Wᴴ * U.val * (V-W) := by
    simp only [B, Matrix.conjTranspose_sub, Matrix.sub_mul, Matrix.mul_sub]
    abel
  have hn : ‖B‖ ≤ 2 * ‖V-W‖ := by
    rw [hb]
    have hu : ‖U.val‖ ≤ 1 := isometry_operatorNorm_le U.val (Unitary.coe_star_mul_self U)
    have hv := isometry_operatorNorm_le V hV
    have hw := isometry_operatorNorm_le W hW
    have h1 := (Matrix.l2_opNorm_mul ((V-W)ᴴ * U.val) V).trans
      (mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul (V-W)ᴴ U.val) (norm_nonneg V))
    have h2 := (Matrix.l2_opNorm_mul (Wᴴ * U.val) (V-W)).trans
      (mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul Wᴴ U.val) (norm_nonneg (V-W)))
    rw [Matrix.l2_opNorm_conjTranspose] at h1 h2
    have hp1 : ‖V-W‖ * ‖U.val‖ * ‖V‖ ≤ ‖V-W‖ := by
      calc
        _ ≤ ‖V-W‖ * 1 * 1 :=
          mul_le_mul (mul_le_mul_of_nonneg_left hu (norm_nonneg _)) hv
            (norm_nonneg _) (by positivity)
        _ = _ := by ring
    have hp2 : ‖W‖ * ‖U.val‖ * ‖V-W‖ ≤ ‖V-W‖ := by
      have hh : ‖W‖ * ‖U.val‖ ≤ 1 :=
        (mul_le_mul hw hu (norm_nonneg _) (by norm_num)).trans_eq (one_mul 1)
      nlinarith [norm_nonneg (V-W)]
    exact (norm_add_le _ _).trans (by linarith)
  have ht : Matrix.trace (U.val * X) = Matrix.trace (B * CStarMatrix.ofMatrix.symm P.1) := by
    simp only [X, B, Matrix.mul_sub, Matrix.sub_mul, Matrix.trace_sub]
    congr 1
    · simp only [← Matrix.mul_assoc]
      rw [Matrix.trace_mul_comm _ Vᴴ]
      simp only [Matrix.mul_assoc]
    · simp only [← Matrix.mul_assoc]
      rw [Matrix.trace_mul_comm _ Wᴴ]
      simp only [Matrix.mul_assoc]
  have hp : traceNorm (CStarMatrix.ofMatrix.symm P.1) = 1 := by
    have h := traceNorm_of_posSemidef (density_posSemidef P)
    exact (congrArg Complex.re h).trans (congrArg Complex.re P.2.2)
  have he : traceNorm X ≤ 2 * ‖V-W‖ := by
    rw [← hU, ht]
    exact (D5.S3.Quantum.Matrix.UniformVarianceTraceBound.re_trace_mul_le _ _).trans
      (by rw [hp, mul_one]; exact hn)
  change traceNorm X / 2 ≤ _
  linarith

private theorem reference_isometry_norm_le (V : Matrix O I ℂ) :
    ‖(1 : Matrix R R ℂ) ⊗ₖ V‖ ≤ ‖V‖ := by
  have h := Matrix.l2_opNorm_conjTranspose_mul_self ((1 : Matrix R R ℂ) ⊗ₖ V)
  rw [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
    ← Matrix.mul_kronecker_mul, Matrix.one_mul] at h
  have hb : ‖(1 : Matrix R R ℂ) ⊗ₖ (Vᴴ * V)‖ ≤ ‖Vᴴ * V‖ :=
    NonUnitalStarAlgHom.norm_apply_le tensorRight _
  rw [h, Matrix.l2_opNorm_conjTranspose_mul_self] at hb
  nlinarith [norm_nonneg ((1 : Matrix R R ℂ) ⊗ₖ V), norm_nonneg V]

private theorem reference_isometry (V : Matrix O I ℂ) (hV : Vᴴ * V = 1) :
    (((1 : Matrix R R ℂ) ⊗ₖ V)ᴴ * ((1 : Matrix R R ℂ) ⊗ₖ V)) = 1 := by
  rw [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
    ← Matrix.mul_kronecker_mul, Matrix.one_mul, hV, Matrix.one_kronecker_one]

private theorem reference_isometryState_distance (V W : Matrix O I ℂ)
    (hV : Vᴴ * V = 1) (hW : Wᴴ * W = 1) (P : DensityState (R × I)) :
    traceDistance (isometryState ((1 : Matrix R R ℂ) ⊗ₖ V) (reference_isometry V hV) P)
      (isometryState ((1 : Matrix R R ℂ) ⊗ₖ W) (reference_isometry W hW) P) ≤ ‖V-W‖ := by
  exact (isometryState_distance _ _ _ _ P).trans (by
    have he : (1 : Matrix R R ℂ) ⊗ₖ V - (1 : Matrix R R ℂ) ⊗ₖ W =
        (1 : Matrix R R ℂ) ⊗ₖ (V-W) := by ext i j; simp [mul_sub]
    rw [he]
    exact reference_isometry_norm_le (R := R) (V-W))

end IsometryComparison

section NormalizedColumns

variable [DecidableEq Q]

private theorem qubit_operatorNorm_sq_le_columns
    (D : Matrix (Fin 2 × Q) (Fin 2) ℂ) :
    ‖D‖ ^ 2 ≤ ‖column D 0 0‖ ^ 2 + ‖column D 1 0‖ ^ 2 +
      ‖column D 0 1‖ ^ 2 + ‖column D 1 1‖ ^ 2 := by
  let H := Dᴴ * D
  have hH : H.PosSemidef := Matrix.posSemidef_conjTranspose_mul_self D
  have ht : (Matrix.trace H).re = ‖column D 0 0‖ ^ 2 + ‖column D 1 0‖ ^ 2 +
      ‖column D 0 1‖ ^ 2 + ‖column D 1 1‖ ^ 2 := by
    simp [H, Matrix.trace, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fintype.sum_prod_type, Fin.sum_univ_two, column, EuclideanSpace.norm_sq_eq,
      Complex.mul_re, Complex.sq_norm, Complex.normSq_apply, ← Finset.sum_add_distrib]
    <;> ring
  have hn : ‖H‖ ≤ (Matrix.trace H).re := by
    have hs : (Matrix.trace H).re = ∑ i, hH.isHermitian.eigenvalues i := by
      simpa [Fin.sum_univ_two] using
        congrArg Complex.re hH.isHermitian.trace_eq_sum_eigenvalues
    have hp : 0 ≤ (Matrix.trace H).re := by
      rw [hs]
      exact Finset.sum_nonneg (fun i _ => hH.eigenvalues_nonneg i)
    have he : ‖H‖ = ‖fun i => (hH.isHermitian.eigenvalues i : ℂ)‖ := by
      conv_lhs => rw [hH.isHermitian.spectral_theorem]
      simp only [Unitary.conjStarAlgAut_apply, ← Unitary.coe_star,
        CStarRing.norm_mul_coe_unitary, CStarRing.norm_coe_unitary_mul,
        Matrix.l2_opNorm_diagonal]
      rfl
    rw [he]
    apply (pi_norm_le_iff_of_nonneg hp).mpr
    intro i
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hH.eigenvalues_nonneg i), hs]
    exact Finset.single_le_sum (fun j _ => hH.eigenvalues_nonneg j) (Finset.mem_univ i)
  have he : ‖H‖ = ‖D‖ ^ 2 := by
    dsimp only [H]
    rw [Matrix.l2_opNorm_conjTranspose_mul_self]
    ring
  rw [he, ht] at hn
  exact hn

private theorem normalize_retained_vector (v : EuclideanSpace ℂ Q) (t : ℝ)
    (ht : 0 ≤ t) (hvt : ‖v‖ ^ 2 + t ^ 2 = 1) (ht1 : t ^ 2 < 1) :
    let n := ‖v‖⁻¹ • v
    ‖n‖ = 1 ∧ ‖v-n‖ ^ 2 ≤ t ^ 2 := by
  have hv : 0 < ‖v‖ := by nlinarith [norm_nonneg v]
  have hv1 : ‖v‖ ≤ 1 := by nlinarith [sq_nonneg t, norm_nonneg v]
  dsimp only
  constructor
  · rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hv), inv_mul_cancel₀ (ne_of_gt hv)]
  · have he : v - ‖v‖⁻¹ • v = (1 - ‖v‖⁻¹) • v := by
      rw [sub_smul, one_smul]
    rw [he, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    have hid : (1 - ‖v‖⁻¹) * ‖v‖ = ‖v‖-1 := by
      rw [sub_mul, one_mul, inv_mul_cancel₀ (ne_of_gt hv)]
    nlinarith [sq_nonneg t]

/-- The normalized retained vectors define a physical pointer isometry. -/
def pointerIsometry (v : Fin 2 → EuclideanSpace ℂ Q) :
    Matrix (Fin 2 × Q) (Fin 2) ℂ := fun p i => if p.1 = i then v i p.2 else 0

private theorem pointerIsometry_column (v : Fin 2 → EuclideanSpace ℂ Q) (j i : Fin 2) :
    column (pointerIsometry v) j i = if j = i then v i else 0 := by
  ext q
  by_cases h : j = i <;> simp [column, pointerIsometry, h]

private theorem pointerIsometry_isometry (v : Fin 2 → EuclideanSpace ℂ Q)
    (hv : ∀ i, ‖v i‖ = 1) : (pointerIsometry v)ᴴ * pointerIsometry v = 1 := by
  ext i k
  by_cases hi : i = k
  · subst k
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply, ite_true]
    simp only [Fintype.sum_prod_type, pointerIsometry, apply_ite, star_zero,
      ite_mul, zero_mul, mul_ite, mul_zero, ite_self, Finset.sum_ite_irrel,
      Finset.sum_const_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    have h : inner ℂ (v i) (v i) = 1 := by
      rw [inner_self_eq_norm_sq_to_K, hv]
      norm_num
    simpa only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Pi.star_apply, mul_comm] using h
  · simp [Matrix.mul_apply, Matrix.conjTranspose_apply, pointerIsometry,
      Matrix.one_apply, Fintype.sum_prod_type, hi, Ne.symm hi]

/-- When the total flip probability is below one, normalize both retained
columns and remove the flips, without a rank or spectral-floor premise. -/
theorem normalized_pointer_isometry
    (W : Matrix (Fin 2 × Q) (Fin 2) ℂ) (hW : Wᴴ * W = 1)
    (hs : ‖column W 1 0‖ ^ 2 + ‖column W 0 1‖ ^ 2 < 1) :
    ∃ v : Fin 2 → EuclideanSpace ℂ Q,
      (∀ i, ‖v i‖ = 1) ∧
      (pointerIsometry v)ᴴ * pointerIsometry v = 1 ∧
      ‖W-pointerIsometry v‖ ≤
        2 * Real.sqrt (‖column W 1 0‖ ^ 2 + ‖column W 0 1‖ ^ 2) := by
  obtain ⟨h0,h1⟩ := retained_flip_norms W hW
  let v : Fin 2 → EuclideanSpace ℂ Q :=
    ![‖column W 0 0‖⁻¹ • column W 0 0, ‖column W 1 1‖⁻¹ • column W 1 1]
  have he0 := normalize_retained_vector (column W 0 0) ‖column W 1 0‖
    (norm_nonneg _) h0 (by nlinarith [sq_nonneg ‖column W 0 1‖])
  have he1 := normalize_retained_vector (column W 1 1) ‖column W 0 1‖
    (norm_nonneg _) h1 (by nlinarith [sq_nonneg ‖column W 1 0‖])
  have hv : ∀ i, ‖v i‖ = 1 := by
    intro i
    fin_cases i
    · exact he0.1
    · exact he1.1
  refine ⟨v,hv,pointerIsometry_isometry v hv,?_⟩
  have hd := qubit_operatorNorm_sq_le_columns (W-pointerIsometry v)
  have hc (j i : Fin 2) : column (W-pointerIsometry v) j i =
      column W j i - column (pointerIsometry v) j i := by ext q; rfl
  simp only [hc, pointerIsometry_column] at hd
  simp only [show (1 : Fin 2) ≠ 0 by decide, show (0 : Fin 2) ≠ 1 by decide,
    if_false, sub_zero, ite_true] at hd
  have hs0 : 0 ≤ ‖column W 1 0‖ ^ 2 + ‖column W 0 1‖ ^ 2 := by positivity
  have hsq := Real.sq_sqrt hs0
  have hsum : ‖W-pointerIsometry v‖ ^ 2 ≤
      2 * (‖column W 1 0‖ ^ 2 + ‖column W 0 1‖ ^ 2) := by
    have ha : ‖column W 0 0 - v 0‖ ^ 2 ≤ ‖column W 1 0‖ ^ 2 := he0.2
    have hb : ‖column W 1 1 - v 1‖ ^ 2 ≤ ‖column W 0 1‖ ^ 2 := he1.2
    linarith
  nlinarith [norm_nonneg (W-pointerIsometry v), Real.sqrt_nonneg
    (‖column W 1 0‖ ^ 2 + ‖column W 0 1‖ ^ 2)]

end NormalizedColumns

section PhysicalOutput

variable {A B C E : Type*} [Fintype A] [DecidableEq A]
  [Fintype B] [DecidableEq B] [Fintype C] [DecidableEq C]
  [Fintype E] [DecidableEq E]

private def environmentLast : ((A × (B × C)) × E) ≃ (A × (B × (C × E))) where
  toFun p := (p.1.1,(p.1.2.1,(p.1.2.2,p.2)))
  invFun p := ((p.1,(p.2.1,p.2.2.1)),p.2.2.2)
  left_inv _ := rfl
  right_inv _ := rfl

private def physicalOutput (W : Matrix (B × (C × E)) B ℂ) (hW : Wᴴ * W = 1)
    (P : DensityState (A × B)) : DensityState (A × (B × C)) :=
  D5.S3.Quantum.Information.MarginalCalculus.reduceState environmentLast
    (isometryState ((1 : Matrix A A ℂ) ⊗ₖ W) (reference_isometry W hW) P)

private theorem physicalOutput_entry (W : Matrix (B × (C × E)) B ℂ)
    (hW : Wᴴ * W = 1) (P : DensityState (A × B)) (a b : A) (j k : B) (c d : C) :
    (physicalOutput W hW P).1 (a,(j,c)) (b,(k,d)) =
      ∑ e : E, (W * (CStarMatrix.ofMatrix.symm P.1).submatrix
        (fun l => (a,l)) (fun l => (b,l)) * Wᴴ) (j,(c,e)) (k,(d,e)) := by
  have h := tensor_conjugate_block W (CStarMatrix.ofMatrix.symm P.1) a b
  change (∑ e : E, (((1 : Matrix A A ℂ) ⊗ₖ W) * CStarMatrix.ofMatrix.symm P.1 *
    ((1 : Matrix A A ℂ) ⊗ₖ W)ᴴ) (a,(j,(c,e))) (b,(k,(d,e)))) = _
  apply Finset.sum_congr rfl
  intro e _
  exact congrFun (congrFun h (j,(c,e))) (k,(d,e))

private theorem reduceState_distance {N K R : Type*} [Fintype N] [DecidableEq N]
    [Fintype K] [DecidableEq K] [Fintype R] [DecidableEq R]
    (e : (K × R) ≃ N) (rho sigma : DensityState N) :
    traceDistance (D5.S3.Quantum.Information.MarginalCalculus.reduceState e rho)
      (D5.S3.Quantum.Information.MarginalCalculus.reduceState e sigma) ≤
        traceDistance rho sigma := by
  let D := CStarMatrix.ofMatrix.symm rho.1 - CStarMatrix.ofMatrix.symm sigma.1
  have hh : D.IsHermitian := (density_posSemidef rho).isHermitian.sub
    (density_posSemidef sigma).isHermitian
  have h := partialTraceRight_contract (D.submatrix e e) (hh.submatrix e)
  rw [D5.S3.Quantum.Entanglement.PermutationCriteria.NormInvariance.traceNorm_submatrix_equiv]
    at h
  have he : CStarMatrix.ofMatrix.symm
      (D5.S3.Quantum.Information.MarginalCalculus.reduceState e rho).1 -
      CStarMatrix.ofMatrix.symm
      (D5.S3.Quantum.Information.MarginalCalculus.reduceState e sigma).1 =
        partialTraceRight (D.submatrix e e) := by
    ext i j
    simp only [D5.S3.Quantum.Information.MarginalCalculus.reduceState_entry,
      partialTraceRight, D, Matrix.sub_apply, Matrix.submatrix_apply,
      Finset.sum_sub_distrib]
  unfold traceDistance
  rw [he]
  exact div_le_div_of_nonneg_right h (by norm_num)

/-- Discarding the common physical environment preserves the comparison of
the two normalized isometries, with no reference-dimension factor. -/
theorem physicalOutput_distance
    (V W : Matrix (B × (C × E)) B ℂ) (hV : Vᴴ * V = 1) (hW : Wᴴ * W = 1)
    (P : DensityState (A × B)) :
    traceDistance (physicalOutput V hV P) (physicalOutput W hW P) ≤ ‖V-W‖ :=
  (reduceState_distance environmentLast _ _).trans
    (reference_isometryState_distance V W hV hW P)

private theorem physicalOutput_actual (T : QuantumChannel B (B × C))
    (W : Matrix (B × (C × E)) B ℂ) (hW : Wᴴ * W = 1)
    (hT : ∀ (M : Matrix B B ℂ) (j k : B) (c d : C),
      (∑ e : E, (W * M * Wᴴ) (j,(c,e)) (k,(d,e))) =
        CStarMatrix.ofMatrix.symm (T.toCompletelyPositiveMap (CStarMatrix.ofMatrix M))
          (j,c) (k,d)) (P : DensityState (A × B)) :
    physicalOutput W hW P = referenceState T P := by
  apply Subtype.ext
  apply CStarMatrix.ext
  rintro ⟨a,j,c⟩ ⟨b,k,d⟩
  rw [physicalOutput_entry]
  exact hT _ j k c d

private def normalizedEnvironment (v : EuclideanSpace ℂ (C × E)) (hv : ‖v‖ = 1) :
    DensityState C :=
  marginalRight (pureState v.ofLp (by
    have h : inner ℂ v v = 1 := by rw [inner_self_eq_norm_sq_to_K,hv]; norm_num
    rw [dotProduct_comm]
    simpa only [EuclideanSpace.inner_eq_star_dotProduct] using h))

end PhysicalOutput

section PointerRepair

variable {A B C : Type*} [Fintype A] [DecidableEq A]
  [Fintype B] [DecidableEq B] [Fintype C] [DecidableEq C]

private def blockWeight (P : DensityState (A × B)) (j : B) : ℝ :=
  (Matrix.trace (block (CStarMatrix.ofMatrix.symm P.1) j j)).re

private theorem diagonalBlock_positive (P : DensityState (A × B)) (j : B) :
    (block (CStarMatrix.ofMatrix.symm P.1) j j).PosSemidef :=
  (density_posSemidef P).submatrix _

private theorem blockWeight_nonneg (P : DensityState (A × B)) (j : B) :
    0 ≤ blockWeight P j :=
  (Complex.nonneg_iff.mp (diagonalBlock_positive P j).trace_nonneg).1

private theorem blockWeight_trace (P : DensityState (A × B)) (j : B) :
    Matrix.trace (block (CStarMatrix.ofMatrix.symm P.1) j j) = (blockWeight P j : ℂ) := by
  have hi := (Complex.nonneg_iff.mp (diagonalBlock_positive P j).trace_nonneg).2
  apply Complex.ext <;> simp [blockWeight, hi]

private theorem blockWeight_sum (P : DensityState (A × B)) : ∑ j, blockWeight P j = 1 := by
  have ht := congrArg Complex.re P.2.2
  change (∑ p : A × B, P.1 p p).re = 1 at ht
  rw [Fintype.sum_prod_type_right] at ht
  simpa only [Complex.re_sum, blockWeight, Matrix.trace, Matrix.diag_apply,
    block, Matrix.submatrix_apply, CStarMatrix.ofMatrix_symm_apply] using ht

private def conditionalBlock (P : DensityState (A × B)) (j : B) : DensityState A := by
  classical
  by_cases hp : 0 < blockWeight P j
  · refine ⟨CStarMatrix.ofMatrix ((blockWeight P j)⁻¹ •
      block (CStarMatrix.ofMatrix.symm P.1) j j), ?_, ?_⟩
    · exact map_nonneg CStarMatrix.ofMatrixStarAlgEquiv
        ((diagonalBlock_positive P j).smul (inv_nonneg.mpr (le_of_lt hp))).nonneg
    · change Matrix.trace ((blockWeight P j)⁻¹ •
        block (CStarMatrix.ofMatrix.symm P.1) j j) = 1
      rw [Matrix.trace_smul, blockWeight_trace]
      simp [Complex.real_smul, ne_of_gt hp]
  · exact marginalRight P

private theorem conditionalBlock_weighted (P : DensityState (A × B)) (j : B) :
    blockWeight P j • CStarMatrix.ofMatrix.symm (conditionalBlock P j).1 =
      block (CStarMatrix.ofMatrix.symm P.1) j j := by
  classical
  by_cases hp : 0 < blockWeight P j
  · simp only [conditionalBlock, dif_pos hp]
    change blockWeight P j • ((blockWeight P j)⁻¹ •
      block (CStarMatrix.ofMatrix.symm P.1) j j) = _
    rw [smul_smul, mul_inv_cancel₀ (ne_of_gt hp), one_smul]
  · have hz : blockWeight P j = 0 := le_antisymm (le_of_not_gt hp) (blockWeight_nonneg P j)
    have hb : block (CStarMatrix.ofMatrix.symm P.1) j j = 0 :=
      (diagonalBlock_positive P j).trace_eq_zero_iff.mp (by rw [blockWeight_trace,hz]; simp)
    rw [hz, zero_smul, hb]

private def pointerInput (P : DensityState (A × B)) : DensityState (A × B) :=
  D5.S3.Quantum.Information.OrthogonalRecordEntropy.mixtureState
    (blockWeight P) (blockWeight_nonneg P) (blockWeight_sum P)
    (fun j => productState (conditionalBlock P j)
      (D5.S3.Quantum.Information.OrthogonalRecordEntropy.pointerState j))

private theorem pointerInput_entry (P : DensityState (A × B)) (a b : A) (j k : B) :
    (pointerInput P).1 (a,j) (b,k) = if j = k then P.1 (a,j) (b,j) else 0 := by
  unfold pointerInput D5.S3.Quantum.Information.OrthogonalRecordEntropy.mixtureState
  simp only [cstar_sum_entry, CStarMatrix.smul_apply]
  simp only [productState, CStarMatrix.ofMatrix_apply,
    D5.S3.Quantum.Information.OrthogonalRecordEntropy.pointerState,
    Matrix.kronecker_apply,Matrix.diagonal_apply]
  change (∑ l : B, (blockWeight P l : ℂ) *
    ((conditionalBlock P l).1 a b *
      (if j = k then if j = l then (1 : ℂ) else 0 else 0))) = _
  by_cases h : j = k
  · subst k
    simp only [ite_true, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
      Finset.mem_univ, if_true]
    exact congrFun (congrFun (conditionalBlock_weighted P j) a) b
  · simp [h]

private theorem qubit_single_traceNorm (j k : Fin 2) :
    traceNorm (Matrix.single j k (1 : ℂ)) = 1 := by
  let M : Matrix (Fin 2) (Fin 2) ℂ := Matrix.single j k 1
  let D : Matrix (Fin 2) (Fin 2) ℂ := Matrix.diagonal (fun i => if i = k then 1 else 0)
  have hg : Mᴴ * M = D := by
    ext a b
    fin_cases j <;> fin_cases k <;> fin_cases a <;> fin_cases b <;>
      norm_num [M,D,Matrix.single,Matrix.mul_apply,Matrix.conjTranspose_apply,Fin.sum_univ_two]
  have hp : 0 ≤ D := (Matrix.posSemidef_diagonal_iff.mpr (fun i => by
    split_ifs <;> norm_num)).nonneg
  have hs : D * D = D := by
    dsimp only [D]
    rw [Matrix.diagonal_mul_diagonal]
    congr 1
    ext i
    split_ifs <;> norm_num
  have hr : CFC.sqrt D = D := CFC.sqrt_unique hs hp
  change (CFC.sqrt (Mᴴ * M)).trace.re = 1
  rw [hg,hr]
  simp [D,Matrix.trace]

/-- Pinching the actual AB state in the pointer basis costs at most the
trace norm of its complex off-diagonal block in half trace distance. -/
theorem pointerInput_distance (P : DensityState (A × Fin 2)) :
    traceDistance P (pointerInput P) ≤ traceNorm (block (CStarMatrix.ofMatrix.symm P.1) 0 1) := by
  let X := block (CStarMatrix.ofMatrix.symm P.1) 0 1
  have hx : Xᴴ = block (CStarMatrix.ofMatrix.symm P.1) 1 0 := by
    ext a b
    exact congrFun (congrFun (density_posSemidef P).isHermitian.eq (a,1)) (b,0)
  have he : CStarMatrix.ofMatrix.symm P.1 - CStarMatrix.ofMatrix.symm (pointerInput P).1 =
      X ⊗ₖ Matrix.single 0 1 1 + Xᴴ ⊗ₖ Matrix.single 1 0 1 := by
    ext ⟨a,j⟩ ⟨b,k⟩
    simp only [Matrix.sub_apply, CStarMatrix.ofMatrix_symm_apply, pointerInput_entry, hx]
    fin_cases j <;> fin_cases k <;>
      simp [X,block,Matrix.single,Matrix.kronecker_apply]
  have h := traceNorm_add_le (X ⊗ₖ Matrix.single (0 : Fin 2) 1 (1 : ℂ))
    (Xᴴ ⊗ₖ Matrix.single (1 : Fin 2) 0 (1 : ℂ))
  rw [traceNorm_tensor,traceNorm_tensor,qubit_single_traceNorm,qubit_single_traceNorm,
    D5.S3.Quantum.Entanglement.PermutationCriteria.NormInvariance.traceNorm_conjTranspose,
    mul_one] at h
  unfold traceDistance
  rw [he]
  dsimp only [X] at h
  linarith

private def pointerRepair (P : DensityState (A × B)) (gamma : B → DensityState C) :
    DensityState (A × (B × C)) :=
  MarkovConstructors.classicalMarkovState (blockWeight P) (blockWeight_nonneg P)
    (blockWeight_sum P) (conditionalBlock P) gamma

private theorem pointerRepair_entry (P : DensityState (A × B)) (gamma : B → DensityState C)
    (a b : A) (j k : B) (c d : C) :
    (pointerRepair P gamma).1 (a,(j,c)) (b,(k,d)) =
      if j = k then P.1 (a,j) (b,j) * (gamma j).1 c d else 0 := by
  unfold pointerRepair MarkovConstructors.classicalMarkovState
    D5.S3.Quantum.Information.OrthogonalRecordEntropy.mixtureState
  simp only [cstar_sum_entry, CStarMatrix.smul_apply]
  simp only [productState, CStarMatrix.ofMatrix_apply,
    D5.S3.Quantum.Information.OrthogonalRecordEntropy.pointerState,
    Matrix.kronecker_apply,Matrix.diagonal_apply]
  change (∑ l : B, (blockWeight P l : ℂ) * ((conditionalBlock P l).1 a b *
    ((if j = k then if j = l then (1 : ℂ) else 0 else 0) * (gamma l).1 c d))) = _
  by_cases h : j = k
  · subst k
    simp only [ite_true, ite_mul, one_mul, zero_mul, mul_ite, mul_zero,
      Finset.sum_ite_eq,Finset.mem_univ,if_true]
    have h := congrFun (congrFun (conditionalBlock_weighted P j) a) b
    change (blockWeight P j : ℂ) * (conditionalBlock P j).1 a b = P.1 (a,j) (b,j) at h
    rw [← mul_assoc,h]
  · simp [h]

private theorem pointerRepair_qcmi (P : DensityState (A × B)) (gamma : B → DensityState C) :
    qcmi (D5.S3.Quantum.Foundation.FiniteDensityPurification.toMState
      (pointerRepair P gamma)) = 0 :=
  MarkovConstructors.qcmi_classicalMarkovState _ _ _ _ _

private theorem physicalOutput_pointer {E : Type*} [Fintype E] [DecidableEq E]
    (v : Fin 2 → EuclideanSpace ℂ (C × E)) (hv : ∀ j, ‖v j‖ = 1)
    (P : DensityState (A × Fin 2)) :
    physicalOutput (pointerIsometry v) (pointerIsometry_isometry v hv) (pointerInput P) =
      pointerRepair P (fun j => normalizedEnvironment (v j) (hv j)) := by
  apply Subtype.ext
  apply CStarMatrix.ext
  rintro ⟨a,j,c⟩ ⟨b,k,d⟩
  rw [physicalOutput_entry,pointerRepair_entry]
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, pointerIsometry,
    Matrix.submatrix_apply, CStarMatrix.ofMatrix_symm_apply, pointerInput_entry]
  by_cases h : j = k
  · subst k
    simp only [ite_true,apply_ite,star_zero,mul_ite,mul_zero,
      Finset.sum_ite_eq,Finset.mem_univ,if_true,ite_mul,zero_mul,ite_self]
    change (∑ e : E, v j (c,e) * (P.1 (a,j) (b,j)) * star (v j (d,e))) =
      P.1 (a,j) (b,j) * ∑ e : E, v j (c,e) * star (v j (d,e))
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e _
    ring
  · simp [h, Ne.symm h,apply_ite]

/-- Normalizing the actual retained columns and pinching the actual AB input
gives a same-system classical Markov repair, including zero block weights. -/
theorem classical_pointer_repair {E : Type*} [Fintype E] [DecidableEq E]
    (rho : DensityState (A × (Fin 2 × C)))
    (T : QuantumChannel (Fin 2) (Fin 2 × C))
    (W : Matrix (Fin 2 × (C × E)) (Fin 2) ℂ) (hW : Wᴴ * W = 1)
    (hT : ∀ (M : Matrix (Fin 2) (Fin 2) ℂ) (j k : Fin 2) (c d : C),
      (∑ e : E, (W * M * Wᴴ) (j,(c,e)) (k,(d,e))) =
        CStarMatrix.ofMatrix.symm (T.toCompletelyPositiveMap (CStarMatrix.ofMatrix M))
          (j,c) (k,d))
    (hs : ‖column W 1 0‖ ^ 2 + ‖column W 0 1‖ ^ 2 < 1) :
    let P := marginalRight (relabelState (Equiv.prodAssoc A (Fin 2) C) rho)
    ∃ sigma : DensityState (A × (Fin 2 × C)),
      qcmi (D5.S3.Quantum.Foundation.FiniteDensityPurification.toMState sigma) = 0 ∧
      traceDistance rho sigma ≤ traceDistance rho (referenceState T P) +
        traceNorm (block (CStarMatrix.ofMatrix.symm P.1) 0 1) +
        2 * Real.sqrt (‖column W 1 0‖ ^ 2 + ‖column W 0 1‖ ^ 2) := by
  dsimp only
  let P := marginalRight (relabelState (Equiv.prodAssoc A (Fin 2) C) rho)
  obtain ⟨v,hv,hvi,hd⟩ := normalized_pointer_isometry W hW hs
  let gamma := fun j => normalizedEnvironment (v j) (hv j)
  let sigma := pointerRepair P gamma
  refine ⟨sigma,pointerRepair_qcmi P gamma,?_⟩
  have hpin : traceDistance (referenceState T P) (referenceState T (pointerInput P)) ≤
      traceNorm (block (CStarMatrix.ofMatrix.symm P.1) 0 1) :=
    (referenceState_contract T P (pointerInput P)).trans (pointerInput_distance P)
  have hiso : traceDistance (referenceState T (pointerInput P)) sigma ≤
      2 * Real.sqrt (‖column W 1 0‖ ^ 2 + ‖column W 0 1‖ ^ 2) := by
    rw [← physicalOutput_actual T W hW hT]
    change traceDistance (physicalOutput W hW (pointerInput P))
      (pointerRepair P (fun j => normalizedEnvironment (v j) (hv j))) ≤ _
    rw [← physicalOutput_pointer v hv P]
    exact (physicalOutput_distance W (pointerIsometry v) hW hvi (pointerInput P)).trans hd
  have ht := traceDistance_triangle rho (referenceState T P) sigma
  have ht' := traceDistance_triangle (referenceState T P)
    (referenceState T (pointerInput P)) sigma
  linarith

end PointerRepair

end D5.S3.Quantum.Recovery.QubitResidualRounding
