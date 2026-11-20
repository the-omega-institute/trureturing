import D5.S3.Quantum.Recovery.PetzToricDesignMoment
import D5.S3.Quantum.Foundation.FiniteKrausRepresentation
import D5.S3.Quantum.Foundation.FiniteTraceDistance
import D5.S3.Quantum.Information.PartialTraceMutualInformation
import D5.S3.QuantumChannels.CoPRelativeQuantumnessRefutation
import D5.S3.Weil.ZetaLinear.RankTrace

/-!
# Common CPTP recovery after transposition for a finite weighted design

Section 3 of `toric-design-transpose-recovery.txt`. The Choi matrix here is
unnormalized and has the output index first. The second moment uses the
identity and swap from the verified toric moment.
-/

set_option autoImplicit false

noncomputable section

namespace PetzDesignRecovery

open Matrix
open scoped BigOperators ComplexOrder Kronecker Matrix MatrixOrder
open D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf
open D5.S3.Quantum.Foundation.FiniteTraceDistance (traceNorm traceNorm_eq_max_re_tr_U)
open D5.S3.Quantum.Information.PartialTraceMutualInformation
  (partialTraceLeft partialTraceRight partialTraceRight_add partialTraceRight_kronecker
    trace_partialTraceLeft)
open D5.S3.QuantumChannels.CoPRelativeQuantumnessRefutation (IsCPTP)
open PetzToricDesignMoment (PairMatrix swapMatrix haarMoment)

abbrev Mat (d : ℕ) := Matrix (Fin d) (Fin d) ℂ

section Choi

variable {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B]

/-- The bilinear trace pairing in the output-first Choi convention. -/
theorem choi_trace_pairing (R : MatrixMap A B ℂ) (X : Matrix A A ℂ) (Y : Matrix B B ℂ) :
    (R.choi_matrix * (Y ⊗ₖ Xᵀ)).trace = (Y * R X).trace := by
  classical
  have apply_from_choi (b c : B) :
      ∑ i, ∑ j, X i j * R.choi_matrix (b, i) (c, j) = R X b c :=
    congrArg (fun F : MatrixMap A B ℂ => F X b c) (MatrixMap.choi_map_inv R)
  rw [Matrix.trace_mul_comm Y (R X)]
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Fintype.sum_prod_type,
    Matrix.kronecker_apply, Matrix.transpose_apply, ← apply_from_choi]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_comm]
  simp only [Finset.sum_mul]
  refine Finset.sum_congr rfl fun c _ =>
    Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/-- Trace preservation gives identity after tracing out the output Choi index. -/
theorem choi_input_marginal (R : MatrixMap A B ℂ) (hR : R.IsTracePreserving) :
    partialTraceLeft R.choi_matrix = (1 : Matrix A A ℂ) := by
  ext i j
  change (R (Matrix.single i j 1)).trace = (1 : Matrix A A ℂ) i j
  rw [hR]
  by_cases hij : i = j
  · subst j
    simp [Matrix.trace_single_eq_same]
  · rw [Matrix.trace_single_eq_of_ne i j 1 hij, Matrix.one_apply_ne hij]

end Choi

variable {d : ℕ}

private theorem trace_one_dim : (1 : Mat d).trace = (d : ℂ) := by
  simp [Matrix.trace_one]

private theorem mul_swap (M : PairMatrix d) (a b : Fin d × Fin d) :
    (M * swapMatrix d) a b = M a b.swap := by
  rw [Matrix.mul_apply]
  rw [Finset.sum_eq_single b.swap]
  · simp [swapMatrix]
  · intro c _ hc
    simp [swapMatrix, hc]
  · simp

private theorem swap_square : swapMatrix d * swapMatrix d = 1 := by
  ext a b
  rw [mul_swap]
  simp [swapMatrix, Matrix.one_apply]

private theorem swap_adjoint : (swapMatrix d)ᴴ = swapMatrix d := by
  ext a b
  have hab : b = a.swap ↔ a = b.swap := by
    constructor <;> intro h <;> simpa using (congrArg Prod.swap h).symm
  by_cases h : a = b.swap <;> simp [swapMatrix, Matrix.conjTranspose_apply, hab, h]

private theorem hermitian_idempotent_psd {n : Type*} [Fintype n]
    {P : Matrix n n ℂ} (hP : P.IsHermitian) (hPP : P * P = P) : P.PosSemidef := by
  simpa only [hP.eq, hPP] using Matrix.posSemidef_conjTranspose_mul_self P

theorem one_add_swap_psd (d : ℕ) : ((1 : PairMatrix d) + swapMatrix d).PosSemidef := by
  let M : PairMatrix d := 1 + swapMatrix d
  have hM : Mᴴ * M = (2 : ℝ) • M := by
    simp only [M, Matrix.conjTranspose_add, Matrix.conjTranspose_one, swap_adjoint,
      add_mul, mul_add, one_mul, mul_one, swap_square, two_smul]
    abel
  have hp := Matrix.posSemidef_conjTranspose_mul_self M
  rw [hM] at hp
  have h := hp.smul (a := (1 / 2 : ℝ)) (by norm_num)
  rwa [smul_smul, show (1 / 2 : ℝ) * 2 = 1 by norm_num, one_smul] at h

theorem one_sub_swap_psd (d : ℕ) : ((1 : PairMatrix d) - swapMatrix d).PosSemidef := by
  let M : PairMatrix d := 1 - swapMatrix d
  have hM : Mᴴ * M = (2 : ℝ) • M := by
    simp only [M, Matrix.conjTranspose_sub, Matrix.conjTranspose_one, swap_adjoint,
      sub_mul, mul_sub, one_mul, mul_one, swap_square, two_smul]
    abel
  have hp := Matrix.posSemidef_conjTranspose_mul_self M
  rw [hM] at hp
  have h := hp.smul (a := (1 / 2 : ℝ)) (by norm_num)
  rwa [smul_smul, show (1 / 2 : ℝ) * 2 = 1 by norm_num, one_smul] at h

theorem choi_psd_and_trace (R : MatrixMap (Fin d) (Fin d) ℂ) (hR : IsCPTP R) :
    R.choi_matrix.PosSemidef ∧ R.choi_matrix.trace = (d : ℂ) := by
  refine ⟨(MatrixMap.choi_PSD_iff_CP_map R).mp hR.1, ?_⟩
  rw [← trace_partialTraceLeft R.choi_matrix, choi_input_marginal R hR.2, trace_one_dim]

theorem choi_swap_bounds (R : MatrixMap (Fin d) (Fin d) ℂ) (hR : IsCPTP R) :
    0 ≤ (R.choi_matrix * (1 + swapMatrix d)).trace.re ∧
      (R.choi_matrix * (1 + swapMatrix d)).trace.re ≤ 2 * (d : ℝ) := by
  obtain ⟨hpos, htr⟩ := choi_psd_and_trace R hR
  refine ⟨RHLinalg.trace_mul_nonneg_of_posSemidef hpos (one_add_swap_psd d), ?_⟩
  have h : 0 ≤ (R.choi_matrix * (1 - swapMatrix d)).trace.re :=
    RHLinalg.trace_mul_nonneg_of_posSemidef hpos (one_sub_swap_psd d)
  simp only [mul_sub, mul_one, Matrix.trace_sub, Complex.sub_re, htr, Complex.natCast_re] at h
  simp only [mul_add, mul_one, Matrix.trace_add, Complex.add_re, htr, Complex.natCast_re]
  linarith

def reference (d : ℕ) : Mat d := (d : ℂ)⁻¹ • 1

private theorem reference_trace (hd : 0 < d) : (reference d).trace = 1 := by
  have hdC : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hd.ne'
  simp [reference, Matrix.trace_smul, hdC]

private theorem reference_transpose (d : ℕ) : (reference d)ᵀ = reference d := by
  simp [reference]

private theorem partialTraceRight_smul (c : ℂ) (M : PairMatrix d) :
    partialTraceRight (c • M) = c • partialTraceRight M := by
  ext a b
  simp [partialTraceRight, Finset.mul_sum]

private theorem partialTraceRight_swap : partialTraceRight (swapMatrix d) = (1 : Mat d) := by
  ext a b
  change (∑ j : Fin d, (swapMatrix d) (a, j) (b, j)) = (1 : Mat d) a b
  rw [Finset.sum_eq_single a]
  · by_cases hab : a = b <;> simp [swapMatrix, Matrix.one_apply, hab]
  · intro j _ hja
    simp [swapMatrix, Ne.symm hja]
  · simp

theorem haar_first_marginal (hd : 0 < d) :
    partialTraceRight (haarMoment d) = reference d := by
  have hdC : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hd.ne'
  have hd1 : (d : ℂ) + 1 ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero d)
  have hone : partialTraceRight (1 : PairMatrix d) = (d : ℂ) • (1 : Mat d) := by
    rw [← Matrix.one_kronecker_one]
    exact (partialTraceRight_kronecker (1 : Mat d) (1 : Mat d)).trans
      (congrArg (fun c : ℂ => c • (1 : Mat d)) trace_one_dim)
  have hadd : (d : ℂ) • (1 : Mat d) + 1 = ((d : ℂ) + 1) • (1 : Mat d) := by
    rw [add_smul, one_smul]
  have hscalar : ((d : ℂ) * ((d : ℂ) + 1))⁻¹ * ((d : ℂ) + 1) = (d : ℂ)⁻¹ := by
    field_simp
  rw [haarMoment, partialTraceRight_smul, partialTraceRight_add, hone, partialTraceRight_swap,
    hadd, smul_smul, hscalar, reference]

variable {ι : Type*} [Fintype ι]

theorem design_first_marginal (hd : 0 < d) (P : ι → Mat d) (w : ι → ℝ)
    (htr : ∀ i, (P i).trace = 1)
    (hm : (∑ i, (w i : ℂ) • (P i ⊗ₖ P i)) = haarMoment d) :
    (∑ i, (w i : ℂ) • P i) = reference d := by
  calc
    _ = partialTraceRight (∑ i, (w i : ℂ) • (P i ⊗ₖ P i)) := by
      ext a b
      simp only [partialTraceRight, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
        Matrix.kronecker_apply]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [← mul_assoc, ← Finset.mul_sum]
      change (w i : ℂ) * P i a b = ((w i : ℂ) * P i a b) * (P i).trace
      rw [htr, mul_one]
    _ = reference d := by rw [hm, haar_first_marginal hd]

private theorem re_trace_smul (r : ℝ) {n : Type*} [Fintype n] (M : Matrix n n ℂ) :
    ((r : ℂ) • M).trace.re = r * M.trace.re := by
  simp [Matrix.trace_smul]

theorem design_mean_overlap_le (hd : 0 < d) (P : ι → Mat d) (w : ι → ℝ)
    (hm : (∑ i, (w i : ℂ) • (P i ⊗ₖ P i)) = haarMoment d)
    (R : MatrixMap (Fin d) (Fin d) ℂ) (hR : IsCPTP R) :
    (∑ i, w i * (P i * R (P i)ᵀ).trace.re) ≤ 2 / ((d : ℝ) + 1) := by
  have hmean : (∑ i, w i * (P i * R (P i)ᵀ).trace.re) =
      (R.choi_matrix * haarMoment d).trace.re := by
    rw [← hm, Matrix.mul_sum, Matrix.trace_sum, Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.mul_smul, re_trace_smul, ← choi_trace_pairing, Matrix.transpose_transpose]
  have hdR : 0 < (d : ℝ) := Nat.cast_pos.mpr hd
  have hd1 : 0 < (d : ℝ) + 1 := by positivity
  rw [hmean, haarMoment, Matrix.mul_smul]
  have hcast : ((d : ℂ) * ((d : ℂ) + 1))⁻¹ =
      (((d : ℝ) * ((d : ℝ) + 1))⁻¹ : ℝ) := by push_cast; rfl
  rw [hcast, re_trace_smul]
  calc
    _ ≤ ((d : ℝ) * ((d : ℝ) + 1))⁻¹ * (2 * (d : ℝ)) :=
      mul_le_mul_of_nonneg_left (choi_swap_bounds R hR).2 (by positivity)
    _ = _ := by field_simp

/-- A self-adjoint idempotent with trace one is a rank-one orthogonal projection. -/
def IsRankOneProjection (P : Mat d) : Prop :=
  P.IsHermitian ∧ P * P = P ∧ P.trace = 1

private theorem projection_trace_eq_rank {P : Mat d} (hP : P.IsHermitian) (hPP : P * P = P) :
    P.trace = (P.rank : ℂ) := by
  classical
  rw [hP.trace_eq_sum_eigenvalues, hP.rank_eq_card_non_zero_eigs, Fintype.card_subtype,
    Finset.natCast_card_filter]
  refine Finset.sum_congr rfl fun i _ => ?_
  let eigenvalue := hP.eigenvalues i
  let v : Fin d → ℂ := ⇑(hP.eigenvectorBasis i)
  have hv : v ≠ 0 := (WithLp.ofLp_eq_zero 2).ne.2 (hP.eigenvectorBasis.orthonormal.ne_zero i)
  have he : P *ᵥ v = eigenvalue • v := hP.mulVec_eigenvectorBasis i
  have hsquare : eigenvalue * eigenvalue = eigenvalue := by
    apply smul_left_injective ℝ hv
    change (eigenvalue * eigenvalue) • v = eigenvalue • v
    calc
      _ = eigenvalue • (P *ᵥ v) := by rw [he, mul_smul]
      _ = P *ᵥ (eigenvalue • v) := (Matrix.mulVec_smul P eigenvalue v).symm
      _ = P *ᵥ (P *ᵥ v) := congrArg (fun u => P *ᵥ u) he.symm
      _ = eigenvalue • v := by rw [Matrix.mulVec_mulVec, hPP, he]
  have h01 : eigenvalue = 0 ∨ eigenvalue = 1 := by
    have hz : eigenvalue * (eigenvalue - 1) = 0 := by
      rw [mul_sub, mul_one, hsquare, sub_self]
    exact (mul_eq_zero.mp hz).imp id sub_eq_zero.mp
  change (eigenvalue : ℂ) = if eigenvalue ≠ 0 then 1 else 0
  rcases h01 with h | h <;> simp [h]

theorem isRankOneProjection_iff_rank {P : Mat d} :
    IsRankOneProjection P ↔ P.IsHermitian ∧ P * P = P ∧ P.rank = 1 := by
  constructor
  · rintro ⟨hP, hPP, htr⟩
    refine ⟨hP, hPP, ?_⟩
    exact_mod_cast (projection_trace_eq_rank hP hPP).symm.trans htr
  · rintro ⟨hP, hPP, hrank⟩
    exact ⟨hP, hPP, by simp [projection_trace_eq_rank hP hPP, hrank]⟩

def probe (ε : ℝ) (P : Mat d) : Mat d :=
  ((1 - ε : ℝ) : ℂ) • reference d + (ε : ℂ) • P

def residual (R : MatrixMap (Fin d) (Fin d) ℂ) (ε : ℝ) (P : Mat d) : Mat d :=
  probe ε P - R (probe ε P)ᵀ

theorem probe_trace (hd : 0 < d) (ε : ℝ) {P : Mat d} (hP : IsRankOneProjection P) :
    (probe ε P).trace = 1 := by
  simp [probe, Matrix.trace_add, Matrix.trace_smul, reference_trace hd, hP.2.2]

/-- Below unit mixing the trace-one probe is positive definite. -/
theorem probe_posDef (hd : 0 < d) {ε : ℝ} (hε : 0 ≤ ε) (hε₁ : ε < 1)
    {P : Mat d} (hP : IsRankOneProjection P) : (probe ε P).PosDef := by
  have hscale : 0 < ((1 - ε : ℝ) : ℂ) * (d : ℂ)⁻¹ := by
    simpa only [Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_natCast] using
      (Complex.zero_lt_real.mpr (mul_pos (sub_pos.mpr hε₁) (inv_pos.mpr (Nat.cast_pos.mpr hd))))
  rw [probe, reference, smul_smul]
  exact (Matrix.PosDef.one.smul hscale).add_posSemidef
    ((hermitian_idempotent_psd hP.1 hP.2.1).smul (Complex.zero_le_real.mpr hε))

theorem residual_trace_zero (R : MatrixMap (Fin d) (Fin d) ℂ) (hR : IsCPTP R)
    (ε : ℝ) (P : Mat d) : (residual R ε P).trace = 0 := by
  rw [residual, Matrix.trace_sub, hR.2, Matrix.trace_transpose, sub_self]

private def reflection (P : Mat d) : Mat d := (2 : ℂ) • P - 1

private theorem reflection_unitary {P : Mat d} (hP : IsRankOneProjection P) :
    reflection P ∈ Matrix.unitaryGroup (Fin d) ℂ := by
  apply Matrix.mem_unitaryGroup_iff.mpr
  change reflection P * (reflection P)ᴴ = 1
  simp only [reflection, Matrix.conjTranspose_sub, Matrix.conjTranspose_one,
    Matrix.conjTranspose_smul, Complex.star_def, map_ofNat, hP.1.eq,
    sub_mul, mul_sub, Matrix.smul_mul, Matrix.mul_smul, hP.2.1, one_mul, mul_one,
    smul_smul]
  rw [show (2 : ℂ) * 2 = 2 + 2 by norm_num, add_smul]
  abel

private theorem reflection_test {P D : Mat d} (hP : IsRankOneProjection P)
    (htr : D.trace = 0) : 2 * (P * D).trace.re ≤ traceNorm D := by
  have h := (traceNorm_eq_max_re_tr_U D).2 ⟨⟨reflection P, reflection_unitary hP⟩, rfl⟩
  simpa [reflection, sub_mul, Matrix.smul_mul, Matrix.trace_sub, Matrix.trace_smul, htr,
    Complex.mul_re] using h

private theorem residual_expansion (R : MatrixMap (Fin d) (Fin d) ℂ) (ε : ℝ) (P : Mat d) :
    residual R ε P = ((1 - ε : ℝ) : ℂ) • (reference d - R (reference d)) +
      (ε : ℂ) • (P - R Pᵀ) := by
  simp only [residual, probe, Matrix.transpose_add, Matrix.transpose_smul,
    reference_transpose, map_add, map_smul, smul_sub]
  abel

private theorem design_mean_probe_test (hd : 0 < d) (P : ι → Mat d) (w : ι → ℝ)
    (hP : ∀ i, IsRankOneProjection (P i)) (hw : ∑ i, w i = 1)
    (hm : (∑ i, (w i : ℂ) • (P i ⊗ₖ P i)) = haarMoment d)
    (R : MatrixMap (Fin d) (Fin d) ℂ) (hR : IsCPTP R) (ε : ℝ) :
    (∑ i, w i * (P i * residual R ε (P i)).trace.re) =
      ε * (1 - ∑ i, w i * (P i * R (P i)ᵀ).trace.re) := by
  let Δ := reference d - R (reference d)
  have hΔ : Δ.trace = 0 := by simp [Δ, Matrix.trace_sub, hR.2]
  have hcancel : (∑ i, w i * (P i * Δ).trace.re) = 0 := by
    calc
      _ = (((∑ i, (w i : ℂ) • P i) * Δ).trace).re := by
        simp only [Matrix.sum_mul, Matrix.trace_sum, Complex.re_sum, Matrix.smul_mul,
          re_trace_smul]
      _ = 0 := by
        rw [design_first_marginal hd P w (fun i => (hP i).2.2) hm, reference,
          Matrix.smul_mul, one_mul, Matrix.trace_smul, hΔ]
        simp
  calc
    _ = (1 - ε) * (∑ i, w i * (P i * Δ).trace.re) +
        ε * ((∑ i, w i) - ∑ i, w i * (P i * R (P i)ᵀ).trace.re) := by
      simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [residual_expansion, ← show Δ = reference d - R (reference d) from rfl,
        mul_add, Matrix.mul_smul, Matrix.trace_add, Complex.add_re, re_trace_smul,
        mul_sub, Matrix.trace_sub, Complex.sub_re, (hP i).2.1, (hP i).2.2, Complex.one_re]
      ring
    _ = _ := by simp [hcancel, hw]

/-- A single recovery channel incurs the full trace-norm lower bound on some design probe. -/
theorem exists_large_residual (hd : 2 ≤ d) {ε : ℝ} (hε : 0 < ε)
    (P : ι → Mat d) (w : ι → ℝ) (hP : ∀ i, IsRankOneProjection (P i))
    (hw₀ : ∀ i, 0 ≤ w i) (hw : ∑ i, w i = 1)
    (hm : (∑ i, (w i : ℂ) • (P i ⊗ₖ P i)) = haarMoment d)
    (R : MatrixMap (Fin d) (Fin d) ℂ) (hR : IsCPTP R) :
    ∃ i, 2 * ε * ((d : ℝ) - 1) / ((d : ℝ) + 1) ≤ traceNorm (residual R ε (P i)) := by
  classical
  have hd₀ : 0 < d := by omega
  have hdR : 0 < (d : ℝ) := Nat.cast_pos.mpr hd₀
  let bound := 2 * ε * ((d : ℝ) - 1) / ((d : ℝ) + 1)
  have htest (i : ι) :
      2 * (P i * residual R ε (P i)).trace.re ≤ traceNorm (residual R ε (P i)) :=
    reflection_test (hP i) (residual_trace_zero R hR ε (P i))
  have hmean : bound ≤ ∑ i, w i * (2 * (P i * residual R ε (P i)).trace.re) := by
    have hdouble : (∑ i, w i * (2 * (P i * residual R ε (P i)).trace.re)) =
        2 * ∑ i, w i * (P i * residual R ε (P i)).trace.re := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [hdouble, design_mean_probe_test hd₀ P w hP hw hm R hR]
    calc
      bound = 2 * (ε * (1 - 2 / ((d : ℝ) + 1))) := by
        dsimp [bound]
        field_simp
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (sub_le_sub_left (design_mean_overlap_le hd₀ P w hm R hR) 1)
          hε.le) (by norm_num)
  change ∃ i, bound ≤ traceNorm (residual R ε (P i))
  by_contra! h
  obtain ⟨j, hj⟩ : ∃ j, 0 < w j := by
    by_contra! hnone
    have hs : (∑ i, w i) ≤ 0 := Finset.sum_nonpos fun i _ => hnone i
    linarith
  have hs : (∑ i, w i * (2 * (P i * residual R ε (P i)).trace.re)) < ∑ i, w i * bound := by
    apply Finset.sum_lt_sum
    · intro i _
      exact mul_le_mul_of_nonneg_left ((htest i).trans (h i).le) (hw₀ i)
    · exact ⟨j, Finset.mem_univ j, mul_lt_mul_of_pos_left ((htest j).trans_lt (h j)) hj⟩
  rw [← Finset.sum_mul, hw, one_mul] at hs
  exact (not_lt_of_ge hmean) hs

end PetzDesignRecovery
