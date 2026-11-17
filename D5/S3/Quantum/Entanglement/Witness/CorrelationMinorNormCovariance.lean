/- GID: D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormCovariance
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/Witness/CorrelationMinorNormCovariance
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual normalized covariance bounds and the corrected correlation tail. -/

import D5.S3.Quantum.Entanglement.Witness.CorrelationMinorNormSpectral
import D5.S3.Quantum.Entanglement.Witness.CorrelationMinorNormTetrahedron

/-! The covariance inequality is prior work: Zhang et al. (2008), Theorem 1,
and Gittsovich et al. (2008), Proposition IV.2. This is its trace-product-normalized
application in the Peled return note by Haobo Ma (Chrono AI, Singapore) and
Wenlin Zhang (NUS and Chrono AI, Singapore), CC BY 4.0. It does not validate
Appendix D.5's additional assumptions or remove FNF from the original theorems. -/
set_option autoImplicit false
set_option linter.style.longLine false
noncomputable section
open Matrix Module
open scoped BigOperators InnerProductSpace MatrixOrder ComplexOrder Kronecker Matrix.Norms.L2Operator
open D5.S3.Quantum.Entanglement.Witness.CorrelationMinorNormFNFRefutation
open D5.S3.Quantum.Entanglement.Witness.CorrelationMinorNormGeometry
open D5.S3.Quantum.Entanglement.Witness.CorrelationMinorNormSpectral
open D5.S3.Quantum.Foundation.FiniteTraceDistance
open D5.S3.Quantum.QuantumChannels.NuclearNormAdditivity
open D5.S3.Quantum.Information.SLDSpectralEnergy (IsDensity)
open D5.S3.Quantum.QuantumChannels.IptPptSquaredEquivalence (IsSeparable)
open D5.S3.Quantum.Information.PartialTraceMutualInformation
namespace D5.S3.Quantum.Entanglement.Witness.CorrelationMinorNormCovariance
private lemma weighted_variance {v n : ℕ} (x : Fin v → EuclideanSpace ℝ (Fin n))
    (w : Fin v → ℝ) (hs : ∑ j, w j = 1) :
    let a := ∑ j, w j • x j
    ∑ j, w j * ‖x j - a‖^2 = ∑ j, w j * ‖x j‖^2 - ‖a‖^2 := by
  intro a
  have hi : ∑ j, w j * ⟪x j,a⟫_ℝ = ‖a‖^2 := by
    rw [← real_inner_self_eq_norm_sq]
    change _ = ⟪∑ j, w j • x j, a⟫_ℝ
    simp only [sum_inner, real_inner_smul_left]
  calc
    _ = ∑ j, (w j*‖x j‖^2 - 2*(w j*⟪x j,a⟫_ℝ) + w j*‖a‖^2) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [norm_sub_sq_real]
      ring
    _ = _ := by
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
        hi, ← Finset.sum_mul, hs]
      ring

/-- The covariance nuclear bound for arbitrary finite Euclidean families,
including zero weights and zero centered vectors. -/
theorem weighted_centered_nuclear {v m n : ℕ}
    (x : Fin v → EuclideanSpace ℝ (Fin m)) (y : Fin v → EuclideanSpace ℝ (Fin n))
    (w : Fin v → ℝ) (hw : ∀ j, 0 ≤ w j) (hs : ∑ j, w j = 1)
    (hx : ∀ j, ‖x j‖^2 ≤ 1) (hy : ∀ j, ‖y j‖^2 ≤ 1) :
    let a := ∑ j, w j • x j
    let b := ∑ j, w j • y j
    traceNorm (weightedOuter (fun j => x j-a) (fun j => y j-b) w) ≤
      Real.sqrt ((1-‖a‖^2)*(1-‖b‖^2)) := by
  intro a b
  have hvx := weighted_variance x w hs
  have hvy := weighted_variance y w hs
  have hxsum : ∑ j, w j * ‖x j‖^2 ≤ 1 := by
    calc
      _ ≤ ∑ j, w j * 1 := Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (hx j) (hw j))
      _ = 1 := by simpa using hs
  have hysum : ∑ j, w j * ‖y j‖^2 ≤ 1 := by
    calc
      _ ≤ ∑ j, w j * 1 := Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (hy j) (hw j))
      _ = 1 := by simpa using hs
  have hvx0 : 0 ≤ ∑ j, w j * ‖x j-a‖^2 := Finset.sum_nonneg (fun j _ => mul_nonneg (hw j) (sq_nonneg _))
  have hvy0 : 0 ≤ ∑ j, w j * ‖y j-b‖^2 := Finset.sum_nonneg (fun j _ => mul_nonneg (hw j) (sq_nonneg _))
  have hc := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ
    (fun j => Real.sqrt (w j)*‖x j-a‖) (fun j => Real.sqrt (w j)*‖y j-b‖)
  have hleft : (∑ j, (Real.sqrt (w j)*‖x j-a‖)*(Real.sqrt (w j)*‖y j-b‖)) =
      ∑ j, w j*‖x j-a‖*‖y j-b‖ := by
    apply Finset.sum_congr rfl
    intro j _
    calc
      _ = Real.sqrt (w j)^2 * ‖x j-a‖ * ‖y j-b‖ := by ring
      _ = _ := by rw [Real.sq_sqrt (hw j)]
  have hxs : (∑ j, (Real.sqrt (w j)*‖x j-a‖)^2) = ∑ j, w j*‖x j-a‖^2 := by
    apply Finset.sum_congr rfl
    intro j _; rw [mul_pow, Real.sq_sqrt (hw j)]
  have hys : (∑ j, (Real.sqrt (w j)*‖y j-b‖)^2) = ∑ j, w j*‖y j-b‖^2 := by
    apply Finset.sum_congr rfl
    intro j _; rw [mul_pow, Real.sq_sqrt (hw j)]
  rw [hleft, hxs, hys] at hc
  calc
    _ ≤ ∑ j, w j*‖x j-a‖*‖y j-b‖ := traceNorm_weightedOuter_le _ _ _ hw
    _ ≤ _ := hc
    _ ≤ Real.sqrt (1-‖a‖^2)*Real.sqrt (1-‖b‖^2) := by
      apply mul_le_mul (Real.sqrt_le_sqrt (by linarith [hvx]))
        (Real.sqrt_le_sqrt (by linarith [hvy])) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    _ = _ := (Real.sqrt_mul (by linarith [hvx] : 0 ≤ 1-‖a‖^2) _).symm

private lemma centered_outer_identity {v m n : ℕ}
    (x : Fin v → EuclideanSpace ℝ (Fin m)) (y : Fin v → EuclideanSpace ℝ (Fin n))
    (w : Fin v → ℝ) (hs : ∑ j, w j = 1) :
    let a := ∑ j, w j • x j
    let b := ∑ j, w j • y j
    weightedOuter (fun j => x j-a) (fun j => y j-b) w =
      weightedOuter x y w - Matrix.vecMulVec a.ofLp b.ofLp := by
  intro a b
  ext i k
  have ha : ∑ j, w j * x j i = a i := by simp [a]
  have hb : ∑ j, w j * y j k = b k := by simp [b]
  simp only [weightedOuter, Matrix.sum_apply, Matrix.smul_apply,
    Matrix.sub_apply, Matrix.vecMulVec_apply, smul_eq_mul]
  change (∑ j, w j * ((x j i-a i)*(y j k-b k))) = _
  calc
    _ = ∑ j, (w j*x j i*y j k - b k*(w j*x j i) -
        a i*(w j*y j k) + (a i*b k)*w j) := by
      apply Finset.sum_congr rfl
      intro j _; ring
    _ = _ := by
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
        ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, hs, ha, hb]
      ring

private lemma coordinates_weighted_sum {v n m : ℕ}
    (a : Fin m → Matrix (Fin n) (Fin n) ℂ) (w : Fin v → ℝ)
    (A : Fin v → Matrix (Fin n) (Fin n) ℂ) :
    coordinates a (∑ j, ((w j : ℝ) : ℂ) • A j) = ∑ j, w j • coordinates a (A j) := by
  ext i
  simp [coordinates, Matrix.sum_mul, Matrix.smul_mul, Matrix.trace_sum, Matrix.trace_smul,
    Complex.re_sum]

private lemma actual_marginal_means {da db v : ℕ}
    (w : Fin v → ℝ) (A : Fin v → Matrix (Fin da) (Fin da) ℂ)
    (B : Fin v → Matrix (Fin db) (Fin db) ℂ)
    (hA : ∀ j, IsDensity (A j)) (hB : ∀ j, IsDensity (B j)) :
    partialTraceRight (∑ j, ((w j : ℝ) : ℂ) • (A j ⊗ₖ B j)) =
      ∑ j, ((w j : ℝ) : ℂ) • A j ∧
    partialTraceLeft (∑ j, ((w j : ℝ) : ℂ) • (A j ⊗ₖ B j)) =
      ∑ j, ((w j : ℝ) : ℂ) • B j := by
  constructor
  · ext i k
    simp only [partialTraceRight, Matrix.sum_apply, Matrix.smul_apply,
      Matrix.kroneckerMap_apply, smul_eq_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    rw [← Finset.mul_sum]
    simp only [← mul_assoc, ← Finset.mul_sum]
    change (w j : ℂ) * A j i k * (B j).trace = _
    rw [(hB j).2, mul_one]
  · ext i k
    simp only [partialTraceLeft, Matrix.sum_apply, Matrix.smul_apply,
      Matrix.kroneckerMap_apply, smul_eq_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    rw [← Finset.mul_sum]
    simp only [← Finset.sum_mul]
    change (w j : ℂ) * ((A j).trace * B j i k) = _
    rw [(hA j).2, one_mul]

/-- The actual centered covariance matrix in arbitrary positive local dimensions.
The means are the coefficients of the actual marginals, with Left retaining Bob. -/
theorem actual_covariance_nuclear {da db : ℕ}
    (ρ : Matrix (Fin da × Fin db) (Fin da × Fin db) ℂ) (hρ : IsSeparable ρ)
    (a : Fin (da ^ 2) → Matrix (Fin da) (Fin da) ℂ) (ha : IsHermBasis a)
    (b : Fin (db ^ 2) → Matrix (Fin db) (Fin db) ℂ) (hb : IsHermBasis b) :
    traceNorm (corr ρ a b - Matrix.vecMulVec
      (coordinates a (partialTraceRight ρ)).ofLp (coordinates b (partialTraceLeft ρ)).ofLp) ≤
    Real.sqrt ((1-‖coordinates a (partialTraceRight ρ)‖^2)*
      (1-‖coordinates b (partialTraceLeft ρ)‖^2)) := by
  classical
  obtain ⟨v, w, A, B, hw, hs, hab, heq⟩ := hρ
  have hm := actual_marginal_means w A B (fun j => (hab j).1) (fun j => (hab j).2)
  have hc := correlation_finite_decomposition w A B a b
    (fun j => (hab j).1.1.isHermitian) (fun j => (hab j).2.1.isHermitian) ha.1 hb.1
  have hx (j : Fin v) : ‖coordinates a (A j)‖^2 ≤ 1 := by
    rw [coordinates_purity a ha (A j) (hab j).1.1.isHermitian]
    exact (density_purity_bounds (A j) (hab j).1).2
  have hy (j : Fin v) : ‖coordinates b (B j)‖^2 ≤ 1 := by
    rw [coordinates_purity b hb (B j) (hab j).2.1.isHermitian]
    exact (density_purity_bounds (B j) (hab j).2).2
  have hn := weighted_centered_nuclear (fun j => coordinates a (A j))
    (fun j => coordinates b (B j)) w hw hs hx hy
  dsimp only at hn
  rw [centered_outer_identity _ _ w hs] at hn
  rw [heq, hc, hm.1, hm.2, coordinates_weighted_sum, coordinates_weighted_sum]
  exact hn

private lemma separable_marginal_densities {da db : ℕ}
    (ρ : Matrix (Fin da × Fin db) (Fin da × Fin db) ℂ) (hρ : IsSeparable ρ) :
    IsDensity (partialTraceRight ρ) ∧ IsDensity (partialTraceLeft ρ) := by
  have hd := separable_density ρ hρ
  exact ⟨⟨partialTraceRight_posSemidef hd.1, (trace_partialTraceRight ρ).trans hd.2⟩,
    ⟨partialTraceLeft_posSemidef hd.1, (trace_partialTraceLeft ρ).trans hd.2⟩⟩

/-- The actual descending singular-value tail, from the source's second value
through the full smaller-side squared dimension, with the actual marginal
purities. Positive one-dimensional factors and empty tails are included. -/
theorem correlation_tail_purity {da db : ℕ} (hda : 0 < da) (hdb : 0 < db)
    (ρ : Matrix (Fin da × Fin db) (Fin da × Fin db) ℂ) (hρ : IsSeparable ρ)
    (a : Fin (da ^ 2) → Matrix (Fin da) (Fin da) ℂ) (ha : IsHermBasis a)
    (b : Fin (db ^ 2) → Matrix (Fin db) (Fin db) ℂ) (hb : IsHermBasis b) :
    (∑ i ∈ Finset.Ico 1 ((min da db)^2), (corr ρ a b).toEuclideanLin.singularValues i) ≤
      Real.sqrt ((1-((partialTraceRight ρ)*(partialTraceRight ρ)).trace.re)*
        (1-((partialTraceLeft ρ)*(partialTraceLeft ρ)).trace.re)) := by
  have hd := separable_marginal_densities ρ hρ
  have hc := actual_covariance_nuclear ρ hρ a ha b hb
  rw [coordinates_purity a ha _ hd.1.1.isHermitian,
    coordinates_purity b hb _ hd.2.1.isHermitian] at hc
  exact (native_tail_le_centered (corr ρ a b)
    (coordinates a (partialTraceRight ρ)) (coordinates b (partialTraceLeft ρ))
    ((min da db)^2) (by have : 0 < min da db := lt_min hda hdb; nlinarith)
    (Nat.pow_le_pow_left (min_le_right da db) 2)).trans hc

/-- Purity-sensitive correction of printed D31 in all positive finite local
dimensions. This is the normalized application of the prior covariance bounds,
not a proof of Appendix D.5's additional maximization assumptions. -/
theorem correlation_tail_corrected {da db : ℕ} (hda : 0 < da) (hdb : 0 < db)
    (ρ : Matrix (Fin da × Fin db) (Fin da × Fin db) ℂ) (hρ : IsSeparable ρ)
    (a : Fin (da ^ 2) → Matrix (Fin da) (Fin da) ℂ) (ha : IsHermBasis a)
    (b : Fin (db ^ 2) → Matrix (Fin db) (Fin db) ℂ) (hb : IsHermBasis b) :
    (∑ i ∈ Finset.Ico 1 ((min da db)^2), (corr ρ a b).toEuclideanLin.singularValues i) ≤
      Real.sqrt ((1-((partialTraceRight ρ)*(partialTraceRight ρ)).trace.re)*
        (1-((partialTraceLeft ρ)*(partialTraceLeft ρ)).trace.re)) ∧
    Real.sqrt ((1-((partialTraceRight ρ)*(partialTraceRight ρ)).trace.re)*
        (1-((partialTraceLeft ρ)*(partialTraceLeft ρ)).trace.re)) ≤
      Real.sqrt ((((min da db : ℕ) : ℝ)-1)/((min da db : ℕ) : ℝ) *
        ((((max da db : ℕ) : ℝ)-1)/((max da db : ℕ) : ℝ))) := by
  refine ⟨correlation_tail_purity hda hdb ρ hρ a ha b hb, ?_⟩
  have hd := separable_marginal_densities ρ hρ
  have hA := density_purity_bounds _ hd.1
  have hB := density_purity_bounds _ hd.2
  have hlA := density_purity_dimension_lower hda _ hd.1
  have hlB := density_purity_dimension_lower hdb _ hd.2
  have hda' : (0:ℝ) < da := by exact_mod_cast hda
  have hdb' : (0:ℝ) < db := by exact_mod_cast hdb
  have heA : 1-1/(da:ℝ) = ((da:ℝ)-1)/da := by field_simp
  have heB : 1-1/(db:ℝ) = ((db:ℝ)-1)/db := by field_simp
  have hp : (1-((partialTraceRight ρ)*(partialTraceRight ρ)).trace.re)*
      (1-((partialTraceLeft ρ)*(partialTraceLeft ρ)).trace.re) ≤
      (((da:ℝ)-1)/da)*(((db:ℝ)-1)/db) := by
    rw [← heA, ← heB]
    exact mul_le_mul (by linarith) (by linarith) (by linarith) (by linarith)
  apply Real.sqrt_le_sqrt
  rcases le_total da db with h | h
  · simpa only [min_eq_left h, max_eq_right h] using hp
  · simpa only [min_eq_right h, max_eq_left h, mul_comm] using hp

open D5.S3.Quantum.Entanglement.Witness.CorrelationMinorNormTetrahedron

private lemma tetra_zero_gram
    (b : Fin 16 → Matrix (Fin 4) (Fin 4) ℂ) (hb : IsHermBasis b) :
    corr (omega 4 (by omega) 0) alice b * (corr (omega 4 (by omega) 0) alice b).transpose =
      Matrix.diagonal ![(1/8:ℝ),1/24,1/24,1/24] := by
  simpa [q0,q1] using omega_gram 4 (by omega) 0 b hb

private lemma tetra_zero_traceNorm
    (b : Fin 16 → Matrix (Fin 4) (Fin 4) ℂ) (hb : IsHermBasis b) :
    traceNorm (corr (omega 4 (by omega) 0) alice b) =
      Real.sqrt (1/8) + 3*Real.sqrt (1/24) := by
  rw [← traceNorm_transpose]
  unfold traceNorm
  rw [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.transpose_transpose,
    tetra_zero_gram b hb]
  have hs : CFC.sqrt (Matrix.diagonal ![(1/8:ℝ),1/24,1/24,1/24]) =
      Matrix.diagonal ![Real.sqrt (1/8),Real.sqrt (1/24),Real.sqrt (1/24),Real.sqrt (1/24)] := by
    apply CFC.sqrt_unique
    · rw [Matrix.diagonal_mul_diagonal]
      congr 1
      ext i
      fin_cases i <;> norm_num [Real.sq_sqrt, ← pow_two]
    · apply Matrix.PosSemidef.nonneg
      exact Matrix.PosSemidef.diagonal (by intro i; fin_cases i <;> exact Real.sqrt_nonneg _)
  rw [hs]
  simp [Matrix.trace_diagonal, Fin.sum_univ_succ]
  ring

private lemma tetra_zero_opNorm
    (b : Fin 16 → Matrix (Fin 4) (Fin 4) ℂ) (hb : IsHermBasis b) :
    ‖corr (omega 4 (by omega) 0) alice b‖ = Real.sqrt (1/8) := by
  let C := corr (omega 4 (by omega) 0) alice b
  have hh := Matrix.l2_opNorm_conjTranspose_mul_self C.transpose
  have ht : ‖C.transpose‖ = ‖C‖ := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.l2_opNorm_conjTranspose C
  simp only [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.transpose_transpose, ht] at hh
  rw [tetra_zero_gram b hb, Matrix.l2_opNorm_diagonal] at hh
  have hn : ‖(![(1/8:ℝ),1/24,1/24,1/24] : Fin 4 → ℝ)‖ = 1/8 := by
    apply le_antisymm
    · apply (pi_norm_le_iff_of_nonneg (by norm_num)).mpr
      intro i
      fin_cases i <;> norm_num
    · simpa using norm_le_pi_norm (![(1/8:ℝ),1/24,1/24,1/24] : Fin 4 → ℝ) 0
  rw [hn] at hh
  have hs := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 1/8)
  change ‖C‖ = _
  nlinarith [norm_nonneg C, Real.sqrt_nonneg (1/8)]

/-- The actual FNF tetrahedral state refutes printed D31 and attains both the
purity-sensitive and dimension-only corrected bounds. The covariance credit
remains Zhang2008/Gittsovich2008. No additional D.5 assumptions are concluded. -/
theorem d31_counterexample_and_equality
    (b : Fin 16 → Matrix (Fin 4) (Fin 4) ℂ) (hb : IsHermBasis b) :
    IsSeparable (omega 4 (by omega) 0) ∧ IsDensity (omega 4 (by omega) 0) ∧
    partialTraceRight (omega 4 (by omega) 0) = (1/2:ℂ) • 1 ∧
    partialTraceLeft (omega 4 (by omega) 0) = (1/4:ℂ) • 1 ∧
    (∑ i ∈ Finset.Ico 1 4, (corr (omega 4 (by omega) 0) alice b).toEuclideanLin.singularValues i) =
      Real.sqrt (3/8) ∧
    Real.sqrt ((1-((partialTraceRight (omega 4 (by omega) 0))^2).trace.re)*
      (1-((partialTraceLeft (omega 4 (by omega) 0))^2).trace.re)) = Real.sqrt (3/8) ∧
    (3/8:ℝ) < Real.sqrt (3/8) := by
  have hm := omega_marginals 4 (by omega) 0
  have hB : partialTraceLeft (omega 4 (by omega) 0) = (1/4:ℂ) • 1 := by
    rw [hm.2]
    have hf : ∑ j : Fin 4, tetraFlag 4 (by omega) j = 1 := by
      ext i k
      fin_cases i <;> fin_cases k <;> norm_num [tetraFlag, Fin.sum_univ_succ, Matrix.single_apply, Matrix.one_apply]
    simp [hf]
  have ht := native_tail_eq_traceNorm_sub
    (corr (omega 4 (by omega) 0) alice b) (by decide) (by decide)
  have hmin : min (4:ℕ) 16 = 4 := by decide
  rw [hmin] at ht
  rw [tetra_zero_traceNorm b hb, tetra_zero_opNorm b hb] at ht
  have hs24 : 0 ≤ Real.sqrt (1/24) := Real.sqrt_nonneg _
  have hs : 3*Real.sqrt (1/24) = Real.sqrt (3/8) := by
    have h24 := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 1/24)
    have h38 := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3/8)
    nlinarith [Real.sqrt_nonneg (3/8)]
  refine ⟨omega_separable 4 (by omega) 0 (by norm_num) (by norm_num),
    omega_density 4 (by omega) 0 (by norm_num) (by norm_num), hm.1, hB, ?_, ?_, ?_⟩
  · linarith
  · rw [hm.1,hB]
    norm_num [smul_pow, Matrix.trace_smul, Matrix.trace_one]
  · have h38 := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3/8)
    nlinarith [Real.sqrt_nonneg (3/8)]

end D5.S3.Quantum.Entanglement.Witness.CorrelationMinorNormCovariance
