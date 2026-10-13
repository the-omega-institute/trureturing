/- GID: D5/S3/Quantum/Foundation/TwoRoundRankOneReduction
   generality: G
   mirror-B: D5/B/S3/Quantum/Foundation/TwoRoundRankOneReduction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Same-marginal rank-one tester reduction with attained original global extrema.
-/
import D5.S3.Quantum.Foundation.TwoRoundRankOneReductionSpectral
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.Normed.Module.FiniteDimension
noncomputable section
open Matrix Unitary
open scoped BigOperators ComplexOrder MatrixOrder
open scoped Kronecker Classical
namespace D5.S3.Quantum.Foundation.TwoRoundPhaseAverage
open D5.S3.Quantum.Information.PartialTraceMutualInformation
abbrev AB := Fin 2 × Fin 2
abbrev Wire := AB × Fin 3
abbrev Phase := Fin 2 × Fin 2
def bitSign (g i : Fin 2) : ℂ := if g = 1 ∧ i = 1 then -1 else 1
def phaseAB (g : Phase) (i : AB) : ℂ := bitSign g.1 i.1 * bitSign g.2 i.2
def phaseD (g : Phase) (d : Fin 3) : ℂ :=
  if d = 0 then 1 else if d = 1 then bitSign g.1 1
  else bitSign g.1 1 * bitSign g.2 1
def phaseWire (g : Phase) (i : Wire) : ℂ := phaseAB g i.1 * phaseD g i.2
def signConjugate {n : Type*} (u : n → ℂ) (M : Matrix n n ℂ) : Matrix n n ℂ :=
  fun i j => u i * M i j * u j
def phaseAverage {n : Type*} (u : Phase → n → ℂ) (M : Matrix n n ℂ) : Matrix n n ℂ :=
  (1 / 4 : ℝ) • ∑ g : Phase, signConjugate (u g) M
def averageWire := phaseAverage phaseWire
def averageAB := phaseAverage phaseAB
def Causal (S : Matrix Wire Wire ℂ) (sigma : Matrix (Fin 2) (Fin 2) ℂ) : Prop :=
  S.PosSemidef ∧ sigma.PosSemidef ∧ Matrix.trace sigma = 1 ∧
    partialTraceRight S = Matrix.kronecker (1 : Matrix (Fin 2) (Fin 2) ℂ) sigma
def Tester (C : Matrix AB AB ℂ) (E : Matrix Wire Wire ℂ) : Prop :=
  C.PosSemidef ∧ partialTraceLeft C = (1 : Matrix (Fin 2) (Fin 2) ℂ) ∧
    E.PosSemidef ∧ (Matrix.kronecker C (1 : Matrix (Fin 3) (Fin 3) ℂ) - E).PosSemidef
def response (X E : Matrix Wire Wire ℂ) : ℝ := (Matrix.trace (X * E)).re
def ErrorBound (X : Matrix Wire Wire ℂ) (b : ℝ) : Prop :=
  ∀ C E, Tester C E → |response X E| ≤ b
def candidateVector (eps : ℝ) (i : Wire) : ℂ :=
  if i = ((0, 0), 0) then 1
  else if i = ((1, 0), 1) then (Real.sqrt (1 - eps) : ℂ)
  else if i = ((1, 1), 2) then (Real.sqrt eps : ℂ) else 0
def candidate (eps : ℝ) : Matrix Wire Wire ℂ :=
  Matrix.vecMulVec (candidateVector eps) (star (candidateVector eps))
def MainSupport (i : Wire) : Prop :=
  i = ((0, 0), 0) ∨ i = ((1, 0), 1) ∨ i = ((1, 1), 2)
private theorem bitSign_star (g i : Fin 2) : star (bitSign g i) = bitSign g i := by
  unfold bitSign
  split_ifs <;> simp
private theorem bitSign_sq (g i : Fin 2) : bitSign g i * bitSign g i = 1 := by
  unfold bitSign
  split_ifs <;> norm_num
private theorem phaseAB_star (g : Phase) (i : AB) : star (phaseAB g i) = phaseAB g i := by
  simp only [phaseAB, star_mul, bitSign_star]; ring
private theorem phaseD_star (g : Phase) (d : Fin 3) : star (phaseD g d) = phaseD g d := by
  unfold phaseD
  split_ifs <;> simp [bitSign_star]
private theorem phaseD_sq (g : Phase) (d : Fin 3) : phaseD g d * phaseD g d = 1 := by
  rcases g with ⟨a, b⟩
  fin_cases a <;> fin_cases b <;> fin_cases d <;> norm_num [phaseD, bitSign]
private theorem phaseWire_star (g : Phase) (i : Wire) : star (phaseWire g i) = phaseWire g i := by
  simp only [phaseWire, star_mul, phaseAB_star, phaseD_star]; ring
private theorem signConjugate_pos {n : Type*} [Finite n] (u : n → ℂ) (hu : ∀ i, star (u i) = u i) {M
    : Matrix n n ℂ} (hM : M.PosSemidef) : (signConjugate u M).PosSemidef := by
  classical
  letI := Fintype.ofFinite n
  have heq : signConjugate u M = (Matrix.diagonal u)ᴴ * M * Matrix.diagonal u := by
    ext i j; simp [signConjugate, Matrix.diagonal_conjTranspose, hu]
  rw [heq]; exact hM.conjTranspose_mul_mul_same _
private theorem phaseAverage_pos {n : Type*} [Finite n] (u : Phase → n → ℂ) (hu : ∀ g i, star (u g
    i) = u g i) {M : Matrix n n ℂ} (hM : M.PosSemidef) : (phaseAverage u M).PosSemidef := by
  classical
  letI := Fintype.ofFinite n
  exact (Matrix.posSemidef_sum _ (fun g _ => signConjugate_pos _ (hu g) hM)).smul
    (by norm_num : (0 : ℝ) ≤ 1 / 4)
private theorem average_apply {n : Type*} (u : Phase → n → ℂ) (M : Matrix n n ℂ) (i j : n) :
    phaseAverage u M i j = (1 / 4 : ℂ) * ∑ g : Phase, u g i * M i j * u g j := by
  simp [phaseAverage, signConjugate, Matrix.sum_apply, Matrix.smul_apply,
    Complex.real_smul]
private theorem signConjugate_sub {n : Type*} (u : n → ℂ) (M N : Matrix n n ℂ) : signConjugate u (M
    - N) = signConjugate u M - signConjugate u N := by
  ext i j; simp [signConjugate, mul_sub, sub_mul]
private theorem average_sub {n : Type*} (u : Phase → n → ℂ) (M N : Matrix n n ℂ) : phaseAverage u (M
    - N) = phaseAverage u M - phaseAverage u N := by
  simp [phaseAverage, signConjugate_sub, Finset.sum_sub_distrib, smul_sub]
private theorem conjugate_tester_rhs (g : Phase) (C : Matrix AB AB ℂ) : signConjugate (phaseWire g)
    (Matrix.kronecker C (1 : Matrix (Fin 3) (Fin 3) ℂ)) = Matrix.kronecker (signConjugate (phaseAB
    g) C) (1 : Matrix (Fin 3) (Fin 3) ℂ) := by
  ext i j; rcases i with ⟨ab, d⟩; rcases j with ⟨ab', d'⟩
  by_cases h : d = d'
  · subst d'
    simp only [signConjugate, Matrix.kronecker, Matrix.kronecker_apply, Matrix.one_apply_eq, mul_one,
      phaseWire]
    calc
      _ = phaseAB g ab * C ab ab' * phaseAB g ab' * (phaseD g d * phaseD g d) := by ring
      _ = _ := by rw [phaseD_sq]; ring
  · simp [signConjugate, Matrix.kronecker, h]
private theorem average_tester_rhs (C : Matrix AB AB ℂ) : averageWire (Matrix.kronecker C (1 :
    Matrix (Fin 3) (Fin 3) ℂ)) = Matrix.kronecker (averageAB C) (1 : Matrix (Fin 3) (Fin 3) ℂ) := by
  ext i j; rcases i with ⟨ab, d⟩; rcases j with ⟨ab', d'⟩
  simp only [averageWire, averageAB, average_apply, Matrix.kronecker, Matrix.kronecker_apply,
    Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl; intro g _
  have h := congrArg (fun M : Matrix Wire Wire ℂ => M (ab, d) (ab', d'))
    (conjugate_tester_rhs g C)
  simp only [signConjugate, Matrix.kronecker, Matrix.kronecker_apply] at h
  linear_combination (1 / 4 : ℂ) * h
private theorem averageAB_entry (C : Matrix AB AB ℂ) (i j : AB) : averageAB C i j = if i = j then C
    i i else 0 := by
  rcases i with ⟨a, b⟩; rcases j with ⟨a', b'⟩
  fin_cases a <;> fin_cases b <;> fin_cases a' <;> fin_cases b' <;>
    simp [averageAB, average_apply, Fintype.sum_prod_type, Fin.sum_univ_two, phaseAB, bitSign] <;> ring
private theorem average_tester {C : Matrix AB AB ℂ} {E : Matrix Wire Wire ℂ} (h : Tester C E) :
    Tester (averageAB C) (averageWire E) := by
  refine ⟨phaseAverage_pos _ phaseAB_star h.1, ?_,
    phaseAverage_pos _ phaseWire_star h.2.2.1, ?_⟩
  · ext i j
    by_cases hij : i = j
    · subst j
      simpa [partialTraceLeft, averageAB_entry] using
        congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M i i) h.2.1
    · simp [partialTraceLeft, averageAB_entry, hij, Matrix.one_apply]
  · rw [← average_tester_rhs]
    change (phaseAverage phaseWire (Matrix.kronecker C (1 : Matrix (Fin 3) (Fin 3) ℂ)) -
      phaseAverage phaseWire E).PosSemidef
    rw [← average_sub]; exact phaseAverage_pos _ phaseWire_star h.2.2.2
private theorem averageAB_diagonal (C : Matrix AB AB ℂ) : (averageAB C).IsDiag :=
  fun i j hij => by simp [averageAB_entry, hij]
private theorem candidateVector_fixed (eps : ℝ) (g : Phase) (i : Wire) : phaseWire g i *
    candidateVector eps i = candidateVector eps i := by
  rcases g with ⟨a, b⟩; rcases i with ⟨⟨i, j⟩, d⟩
  fin_cases a <;> fin_cases b <;> fin_cases i <;> fin_cases j <;> fin_cases d <;>
    norm_num [candidateVector, phaseWire, phaseAB, phaseD, bitSign, Fin.ext_iff]
private theorem candidate_fixed (eps : ℝ) (g : Phase) : signConjugate (phaseWire g) (candidate eps)
    = candidate eps := by
  ext i j; change phaseWire g i * (candidateVector eps i * star (candidateVector eps j)) *
      phaseWire g j = candidateVector eps i * star (candidateVector eps j)
  have hj : star (candidateVector eps j) * phaseWire g j = star (candidateVector eps j) := by
    have h := congrArg star (candidateVector_fixed eps g j)
    simpa only [star_mul, phaseWire_star] using h
  calc
    _ = (phaseWire g i * candidateVector eps i) *
      (star (candidateVector eps j) * phaseWire g j) := by ring
    _ = _ := by rw [candidateVector_fixed, hj]
private theorem trace_conjugate_swap {n : Type*} [Fintype n] (u : n → ℂ) (X E : Matrix n n ℂ) :
    Matrix.trace (X * signConjugate u E) = Matrix.trace (signConjugate u X * E) := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, signConjugate]
  apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro j _; ring
private theorem average_invariant_response (X E : Matrix Wire Wire ℂ)
    (hX : ∀ g, signConjugate (phaseWire g) X = X) :
    response X (averageWire E) = response X E := by
  simp [response, averageWire, phaseAverage, Matrix.mul_sum, Matrix.trace_smul,
    Matrix.trace_sum, Complex.real_smul, trace_conjugate_swap, hX]
def mainAddress (k : Fin 3) : Wire :=
  if k = 0 then ((0, 0), 0) else if k = 1 then ((1, 0), 1) else ((1, 1), 2)
def blockEmbedding : Matrix Wire (Fin 3) ℂ :=
  fun i k => if MainSupport i then if i.2 = k then 1 else 0 else 0
def embedBlock (P : Matrix (Fin 3) (Fin 3) ℂ) : Matrix Wire Wire ℂ :=
  blockEmbedding * P * blockEmbeddingᴴ
def complementWeight (p : ℝ) (P : Matrix (Fin 3) (Fin 3) ℂ) (i : Wire) : ℝ :=
  if i = ((0, 0), 1) then 1 - p - (P 0 0).re
  else if i = ((1, 0), 0) then 1 - p - (P 1 1).re
  else if i = ((0, 1), 0) then p
  else if i = ((1, 1), 0) then p - (P 2 2).re else 0
def causalCompletion (p : ℝ) (P : Matrix (Fin 3) (Fin 3) ℂ) : Matrix Wire Wire ℂ :=
  embedBlock P + Matrix.diagonal (fun i => (complementWeight p P i : ℂ))
def diagonalMarginal (p : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.diagonal (fun b => if b = 0 then (1 - p : ℝ) else p : Fin 2 → ℝ) |>.map
    (fun r : ℝ => (r : ℂ))
private theorem embedBlock_entry (P : Matrix (Fin 3) (Fin 3) ℂ) (i j : Wire) : embedBlock P i j = if
    MainSupport i then if MainSupport j then P i.2 j.2 else 0 else 0 := by
  classical
  by_cases hi : MainSupport i <;> by_cases hj : MainSupport j <;>
    simp [embedBlock, Matrix.mul_apply, blockEmbedding, Matrix.conjTranspose_apply,
      hi, hj, eq_comm]
private theorem complementWeight_nonneg (p : ℝ) (P : Matrix (Fin 3) (Fin 3) ℂ) (hp : 0 ≤ p) (h0 : (P
    0 0).re ≤ 1 - p) (h1 : (P 1 1).re ≤ 1 - p) (h2 : (P 2 2).re ≤ p) (i : Wire) : 0 ≤
    complementWeight p P i := by
  unfold complementWeight
  split_ifs <;> linarith
private theorem diagonalMarginal_pos (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) : (diagonalMarginal
    p).PosSemidef := by
  rw [diagonalMarginal, Matrix.diagonal_map (f := Complex.ofReal) (by simp)]
  apply Matrix.PosSemidef.diagonal; intro b
  apply Complex.nonneg_iff.mpr
  exact ⟨by dsimp; split_ifs <;> linarith, by simp⟩
private theorem completion_partialTrace (p : ℝ) (P : Matrix (Fin 3) (Fin 3) ℂ) (hP : P.PosSemidef) :
    partialTraceRight (causalCompletion p P) = Matrix.kronecker (1 : Matrix (Fin 2) (Fin 2) ℂ)
    (diagonalMarginal p) := by
  have hr (k : Fin 3) : P k k = ((P k k).re : ℂ) :=
    Complex.eq_re_of_ofReal_le (r := 0) hP.diag_nonneg
  have h0 := hr 0; have h1 := hr 1; have h2 := hr 2; ext i j; rcases i with ⟨a, b⟩; rcases j with ⟨a', b'⟩
  fin_cases a <;> fin_cases b <;> fin_cases a' <;> fin_cases b' <;>
    simp [partialTraceRight, causalCompletion, embedBlock_entry, complementWeight,
      MainSupport, diagonalMarginal, Matrix.kronecker, Matrix.kronecker_apply,
      Matrix.diagonal, Fin.sum_univ_three] <;>
      first | (solve | linear_combination h0) | (solve | linear_combination h1) |
        (solve | linear_combination h2)
private theorem completion_compression (p : ℝ) (P : Matrix (Fin 3) (Fin 3) ℂ) : (causalCompletion p
    P).submatrix mainAddress mainAddress = P := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.submatrix_apply, causalCompletion, embedBlock_entry, complementWeight,
      MainSupport, mainAddress, Matrix.diagonal]
private theorem compressed_block_causal_lift (p : ℝ) (P : Matrix (Fin 3) (Fin 3) ℂ) (hp : 0 ≤ p)
    (hp1 : p ≤ 1) (hP : P.PosSemidef) (h0 : (P 0 0).re ≤ 1 - p) (h1 : (P 1 1).re ≤ 1 - p) (h2 : (P 2
    2).re ≤ p) : Causal (causalCompletion p P) (diagonalMarginal p) ∧ (causalCompletion p
    P).submatrix mainAddress mainAddress = P ∧ diagonalMarginal p 1 1 = (p : ℂ) := by
  refine ⟨⟨?_, diagonalMarginal_pos p hp hp1, ?_, completion_partialTrace p P hP⟩,
    completion_compression p P, ?_⟩
  · exact (hP.mul_mul_conjTranspose_same blockEmbedding).add
      (Matrix.PosSemidef.diagonal (fun i => Complex.nonneg_iff.mpr
        ⟨by simpa using complementWeight_nonneg p P hp h0 h1 h2 i, by simp⟩))
  · simp [diagonalMarginal, Matrix.trace, Fin.sum_univ_two]
  · simp [diagonalMarginal]
private theorem causal_principal_block_budgets (S : Matrix Wire Wire ℂ) (sigma : Matrix (Fin 2) (Fin
    2) ℂ) (hS : Causal S sigma) : let p := (sigma 1 1).re
    let P := S.submatrix mainAddress mainAddress
    0 ≤ p ∧ p ≤ 1 ∧ P.PosSemidef ∧
      (P 0 0).re ≤ 1 - p ∧ (P 1 1).re ≤ 1 - p ∧ (P 2 2).re ≤ p := by
  intro p P; have hsig0 : 0 ≤ (sigma 0 0).re := (Complex.nonneg_iff.mp hS.2.1.diag_nonneg).1
  have hsig1 : 0 ≤ (sigma 1 1).re := (Complex.nonneg_iff.mp hS.2.1.diag_nonneg).1
  have hst := congrArg Complex.re hS.2.2.1; simp [Matrix.trace, Fin.sum_univ_two] at hst
  have hb (ab : AB) (d : Fin 3) :
      (S (ab, d) (ab, d)).re ≤ (sigma ab.2 ab.2).re := by
    have h := congrArg (fun M : Matrix AB AB ℂ => (M ab ab).re) hS.2.2.2
    simp [partialTraceRight, Matrix.kronecker, Matrix.kroneckerMap_apply] at h
    calc
      _ ≤ ∑ k : Fin 3, (S (ab, k) (ab, k)).re :=
        Finset.single_le_sum (fun k _ =>
          (Complex.nonneg_iff.mp (hS.1.diag_nonneg (i := (ab, k)))).1) (Finset.mem_univ d)
      _ = _ := h
  have hp1 : p ≤ 1 := by dsimp [p]; linarith
  refine ⟨hsig1, hp1, hS.1.submatrix mainAddress, ?_, ?_, ?_⟩
  · change (S ((0, 0), 0) ((0, 0), 0)).re ≤ 1 - p
    dsimp [p]; linarith [hb (0, 0) 0]
  · change (S ((1, 0), 1) ((1, 0), 1)).re ≤ 1 - p
    dsimp [p]; linarith [hb (1, 0) 1]
  · change (S ((1, 1), 2) ((1, 1), 2)).re ≤ p
    exact hb (1, 1) 2
end D5.S3.Quantum.Foundation.TwoRoundPhaseAverage
namespace D5.S3.Quantum.Foundation.TwoRoundSpectralEvents
open D5.S3.Quantum.Foundation.TwoRoundPhaseAverage
open D5.S3.Quantum.Information.PartialTraceMutualInformation
open scoped Kronecker
def testerWeight (q t : ℝ) (ab : AB) : ℝ :=
  if ab.1 = 0 then if ab.2 = 0 then q else 1 - t
  else if ab.2 = 0 then 1 - q else t
def diagonalTester (q t : ℝ) : Matrix AB AB ℂ :=
  diagonal (fun ab => (testerWeight q t ab : ℂ))
def testerNormalization (q t : ℝ) : Matrix Wire Wire ℂ :=
  diagonalTester q t ⊗ₖ (1 : Matrix (Fin 3) (Fin 3) ℂ)
def compressedNormalization (q t : ℝ) : Matrix (Fin 3) (Fin 3) ℂ :=
  diagonal (fun k => if k = 0 then (q : ℂ) else if k = 1 then (1 - q : ℝ) else t)
def compressedDifference (eps : ℝ) (P : Matrix (Fin 3) (Fin 3) ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  (candidate eps).submatrix mainAddress mainAddress - P
private theorem compressed_difference_hermitian (eps : ℝ) {P : Matrix (Fin 3) (Fin 3) ℂ} (hP :
    P.PosSemidef) : (compressedDifference eps P).IsHermitian :=
  ((posSemidef_vecMulVec_self_star (candidateVector eps)).isHermitian.submatrix mainAddress).sub
    hP.isHermitian
def compressedPositiveMass (eps q t : ℝ) {P : Matrix (Fin 3) (Fin 3) ℂ} (hP : P.PosSemidef) : ℝ :=
  weightedPositiveMass (compressedNormalization q t) (compressed_difference_hermitian eps hP)
private theorem mainAddress_of_support {i : Wire} (hi : MainSupport i) : mainAddress i.2 = i := by
  rcases hi with rfl | rfl | rfl <;> decide
private theorem blockEmbedding_gram : blockEmbeddingᴴ * blockEmbedding = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, blockEmbedding, Matrix.conjTranspose_apply, MainSupport,
      Fintype.sum_prod_type, Fin.sum_univ_three]
private theorem block_compression (E : Matrix Wire Wire ℂ) : blockEmbeddingᴴ * E * blockEmbedding =
    E.submatrix mainAddress mainAddress := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, blockEmbedding, Matrix.conjTranspose_apply, MainSupport,
      mainAddress, Fintype.sum_prod_type, Fin.sum_univ_three]
private theorem compress_embed (F : Matrix (Fin 3) (Fin 3) ℂ) : blockEmbeddingᴴ * embedBlock F *
    blockEmbedding = F := by
  calc
    _ = (blockEmbeddingᴴ * blockEmbedding) * F * (blockEmbeddingᴴ * blockEmbedding) := by
      simp only [embedBlock, Matrix.mul_assoc]
    _ = F := by rw [blockEmbedding_gram, Matrix.one_mul, Matrix.mul_one]
private theorem candidate_embed (eps : ℝ) : candidate eps = embedBlock ((candidate eps).submatrix
    mainAddress mainAddress) := by
  have hz (i : Wire) (hi : ¬ MainSupport i) : candidateVector eps i = 0 := by
    simp_all [MainSupport, candidateVector]
  ext i j; rw [embedBlock_entry]
  by_cases hi : MainSupport i
  · by_cases hj : MainSupport j
    · simp only [hi, hj, if_true, Matrix.submatrix_apply,
        mainAddress_of_support hi, mainAddress_of_support hj]
    · simp [hi, hj, candidate, Matrix.vecMulVec_apply, hz j hj, Pi.star_apply]
  · simp [hi, candidate, Matrix.vecMulVec_apply, hz i hi, Pi.star_apply]
private theorem testerWeight_nonneg (q t : ℝ) (hq : 0 ≤ q) (hq1 : q ≤ 1) (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (ab : AB) : 0 ≤ testerWeight q t ab := by
  unfold testerWeight
  split_ifs <;> linarith
private theorem diagonalTester_pos (q t : ℝ) (hq : 0 ≤ q) (hq1 : q ≤ 1) (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    (diagonalTester q t).PosSemidef := by
  apply PosSemidef.diagonal; intro ab; change (0 : ℂ) ≤ (testerWeight q t ab : ℂ)
  exact_mod_cast testerWeight_nonneg q t hq hq1 ht ht1 ab
private theorem diagonalTester_normalized (q t : ℝ) : partialTraceLeft (diagonalTester q t) = (1 :
    Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [partialTraceLeft, diagonalTester, testerWeight, diagonal, Fin.sum_univ_two]
private theorem testerNormalization_diagonal (q t : ℝ) : testerNormalization q t = diagonal (fun i
    => (testerWeight q t i.1 : ℂ)) := by
  unfold testerNormalization diagonalTester; rw [← diagonal_one, diagonal_kronecker_diagonal]
  simp only [mul_one]
private theorem testerNormalization_compression (q t : ℝ) : blockEmbeddingᴴ * testerNormalization q
    t * blockEmbedding = compressedNormalization q t := by
  rw [block_compression, testerNormalization_diagonal]; ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.submatrix_apply, mainAddress, testerWeight, compressedNormalization, diagonal]
private def outsideDiagonal (w : Wire → ℂ) : Matrix Wire Wire ℂ :=
  diagonal (fun i => if MainSupport i then 0 else w i)
private theorem diagonal_embedding_split (w : Wire → ℂ) : diagonal w = embedBlock (diagonal (fun k
    => w (mainAddress k))) + outsideDiagonal w := by
  ext i j; rw [Matrix.add_apply, embedBlock_entry]
  by_cases hi : MainSupport i <;> by_cases hj : MainSupport j
  · have heq : i.2 = j.2 ↔ i = j := ⟨fun h => by
      rw [← mainAddress_of_support hi, ← mainAddress_of_support hj, h], congrArg Prod.snd⟩
    simp [hi, hj, outsideDiagonal, diagonal, heq, mainAddress_of_support hi]
  · simp [hi, hj, outsideDiagonal, diagonal, show i ≠ j from fun h => hj (h ▸ hi)]
  · simp [hi, outsideDiagonal, diagonal]
  · simp [hi, outsideDiagonal, diagonal]
private theorem testerNormalization_split (q t : ℝ) : testerNormalization q t = embedBlock
    (compressedNormalization q t) + outsideDiagonal (fun i => (testerWeight q t i.1 : ℂ)) := by
  rw [testerNormalization_diagonal, diagonal_embedding_split]; congr 2; ext i j
  fin_cases i <;> fin_cases j <;>
    simp [mainAddress, testerWeight, compressedNormalization, diagonal]
private theorem compressedNormalization_pos (q t : ℝ) (hq : 0 ≤ q) (hq1 : q ≤ 1) (ht : 0 ≤ t) (ht1 :
    t ≤ 1) : (compressedNormalization q t).PosSemidef := by
  have hM := (diagonalTester_pos q t hq hq1 ht ht1).kronecker
    (PosSemidef.one : (1 : Matrix (Fin 3) (Fin 3) ℂ).PosSemidef)
  change (testerNormalization q t).PosSemidef at hM
  simpa only [testerNormalization_compression] using
    hM.conjTranspose_mul_mul_same blockEmbedding
private theorem lift_compressed_event (q t : ℝ) (hq : 0 ≤ q) (hq1 : q ≤ 1) (ht : 0 ≤ t) (ht1 : t ≤
    1) {F : Matrix (Fin 3) (Fin 3) ℂ} (hF : EventInterval (compressedNormalization q t) F) :
    EventInterval (testerNormalization q t) (embedBlock F) := by
  classical
  refine ⟨hF.1.mul_mul_conjTranspose_same _, ?_⟩
  rw [testerNormalization_split]
  have ho : (outsideDiagonal (fun i => (testerWeight q t i.1 : ℂ))).PosSemidef := by
    apply PosSemidef.diagonal; intro i; dsimp [outsideDiagonal]
    split_ifs
    · exact le_rfl
    · exact_mod_cast testerWeight_nonneg q t hq hq1 ht ht1 i.1
  have h := (hF.2.mul_mul_conjTranspose_same blockEmbedding).add ho
  convert h using 1
  simp only [embedBlock, Matrix.mul_sub, Matrix.sub_mul]; abel
private theorem compress_full_event (q t : ℝ) {E : Matrix Wire Wire ℂ} (hE : EventInterval
    (testerNormalization q t) E) : EventInterval (compressedNormalization q t) (blockEmbeddingᴴ * E
    * blockEmbedding) := by
  refine ⟨hE.1.conjTranspose_mul_mul_same _, ?_⟩
  have h := hE.2.conjTranspose_mul_mul_same blockEmbedding
  simpa only [Matrix.mul_sub, Matrix.sub_mul, testerNormalization_compression] using h
private theorem response_embed (F : Matrix (Fin 3) (Fin 3) ℂ) (E : Matrix Wire Wire ℂ) :
    eventResponse (embedBlock F) E = eventResponse F (blockEmbeddingᴴ * E * blockEmbedding) := by
  unfold eventResponse embedBlock; congr 1
  calc
    _ = trace ((blockEmbedding * F) * (blockEmbeddingᴴ * E)) := by simp only [Matrix.mul_assoc]
    _ = trace ((blockEmbeddingᴴ * E) * (blockEmbedding * F)) := trace_mul_comm _ _
    _ = trace ((blockEmbeddingᴴ * E * blockEmbedding) * F) := by simp only [Matrix.mul_assoc]
    _ = _ := trace_mul_comm _ _
private theorem diagonal_response (w : Wire → ℝ) (E : Matrix Wire Wire ℂ) : eventResponse (diagonal
    (fun i => (w i : ℂ))) E = ∑ i, w i * (E i i).re := by
  simp [eventResponse, Matrix.trace, Matrix.diagonal_mul, Complex.mul_re]
private theorem completion_response (eps p : ℝ) (P : Matrix (Fin 3) (Fin 3) ℂ) (E : Matrix Wire Wire
    ℂ) : eventResponse (candidate eps - causalCompletion p P) E = eventResponse
    (compressedDifference eps P) (blockEmbeddingᴴ * E * blockEmbedding) - ∑ i, complementWeight p P
    i * (E i i).re := by
  rw [candidate_embed eps]
  simp only [causalCompletion, eventResponse, Matrix.sub_mul, Matrix.add_mul,
    Matrix.trace_sub, Matrix.trace_add, Complex.sub_re, Complex.add_re]
  change eventResponse (embedBlock ((candidate eps).submatrix mainAddress mainAddress)) E -
    (eventResponse (embedBlock P) E + eventResponse (diagonal _) E) = _
  rw [response_embed, response_embed, diagonal_response]
  simp only [compressedDifference, eventResponse, Matrix.sub_mul, Matrix.trace_sub, Complex.sub_re]
  ring
private theorem completion_lifted_response (eps p : ℝ) (P F : Matrix (Fin 3) (Fin 3) ℂ) :
    eventResponse (candidate eps - causalCompletion p P) (embedBlock F) = eventResponse
    (compressedDifference eps P) F := by
  rw [completion_response, compress_embed]
  have hz : ∑ i : Wire, complementWeight p P i * (embedBlock F i i).re = 0 := by
    apply Finset.sum_eq_zero; intro i _
    by_cases hi : MainSupport i
    · have hw : complementWeight p P i = 0 := by
        rcases hi with rfl | rfl | rfl <;> simp [complementWeight]
      simp [hw]
    · simp [embedBlock_entry, hi]
  rw [hz, sub_zero]
private theorem normalization_trace (S : Matrix Wire Wire ℂ) (sigma : Matrix (Fin 2) (Fin 2) ℂ) (C :
    Matrix AB AB ℂ) (hSn : partialTraceRight S = Matrix.kronecker (1 : Matrix (Fin 2) (Fin 2) ℂ)
    sigma) (hst : trace sigma = 1) (hCn : partialTraceLeft C = 1) : trace (S * (C ⊗ₖ (1 : Matrix
    (Fin 3) (Fin 3) ℂ))) = 1 := by
  have hR : trace (S * (C ⊗ₖ (1 : Matrix (Fin 3) (Fin 3) ℂ))) =
      trace (partialTraceRight S * C) := by
    simp [Matrix.trace, Matrix.mul_apply, Matrix.kroneckerMap_apply, partialTraceRight,
      Matrix.one_apply, Fintype.sum_prod_type, Finset.sum_mul, Fin.sum_univ_three]
    ring
  have hL : trace (C * ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ sigma)) =
      trace (partialTraceLeft C * sigma) := by
    simp [Matrix.trace, Matrix.mul_apply, Matrix.kroneckerMap_apply, partialTraceLeft,
      Matrix.one_apply, Fintype.sum_prod_type, Finset.sum_mul, Fin.sum_univ_three]
    ring
  rw [hR, hSn, Matrix.kronecker, trace_mul_comm, hL, hCn, Matrix.one_mul, hst]
private theorem candidate_normalization_response (eps q t : ℝ) (he : 0 ≤ eps) (he1 : eps ≤ 1) :
    eventResponse (candidate eps) (testerNormalization q t) = 1 - eps * (1 - q - t) := by
  rw [testerNormalization_diagonal]
  simp [eventResponse, candidate, candidateVector, testerWeight, Matrix.trace,
    Matrix.mul_diagonal, Matrix.vecMulVec_apply, Pi.star_apply,
    Fintype.sum_prod_type, Fin.sum_univ_two, Fin.sum_univ_three, Complex.mul_re,
    Real.mul_self_sqrt he, Real.mul_self_sqrt (sub_nonneg.mpr he1)]
  ring
theorem compressed_completion_tester_value (eps p q t : ℝ)
    (P : Matrix (Fin 3) (Fin 3) ℂ) (he : 0 ≤ eps) (he1 : eps ≤ 1)
    (hp : 0 ≤ p) (hp1 : p ≤ 1) (hq : 0 ≤ q) (hq1 : q ≤ 1) (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (hP : P.PosSemidef) (h0 : (P 0 0).re ≤ 1 - p) (h1 : (P 1 1).re ≤ 1 - p)
    (h2 : (P 2 2).re ≤ p) :
    Causal (causalCompletion p P) (diagonalMarginal p) ∧
    ∃ Ep En : Matrix Wire Wire ℂ,
      Tester (diagonalTester q t) Ep ∧ Tester (diagonalTester q t) En ∧
      response (candidate eps - causalCompletion p P) Ep = compressedPositiveMass eps q t hP ∧
      response (causalCompletion p P - candidate eps) En =
        compressedPositiveMass eps q t hP + eps * (1 - q - t) ∧
      (∀ E, Tester (diagonalTester q t) E →
        response (candidate eps - causalCompletion p P) E ≤ compressedPositiveMass eps q t hP ∧
        response (causalCompletion p P - candidate eps) E ≤
          compressedPositiveMass eps q t hP + eps * (1 - q - t)) ∧
      IsGreatest {r : ℝ | ∃ E, Tester (diagonalTester q t) E ∧
        |response (candidate eps - causalCompletion p P) E| = r}
        (compressedPositiveMass eps q t hP + max (eps * (1 - q - t)) 0) := by
  let S := causalCompletion p P; let X := candidate eps - S; let M := testerNormalization q t
  have hS := (compressed_block_causal_lift p P hp hp1 hP h0 h1 h2).1
  have hC := diagonalTester_pos q t hq hq1 ht ht1; have hCn := diagonalTester_normalized q t
  have hM : M.PosSemidef := hC.kronecker PosSemidef.one
  have hX : X.IsHermitian := (posSemidef_vecMulVec_self_star (candidateVector eps)).isHermitian.sub
    hS.1.isHermitian
  have hB := compressedNormalization_pos q t hq hq1 ht ht1
  obtain ⟨F, _, hF, _, hvF, _, hbF, _⟩ :=
    attained_two_direction_spectral_events hB (compressed_difference_hermitian eps hP)
  have hupper (E : Matrix Wire Wire ℂ) (hE : EventInterval M E) :
      eventResponse X E ≤ compressedPositiveMass eps q t hP := by
    have hb := (hbF _ (compress_full_event q t hE)).1
    have hc : 0 ≤ ∑ i, complementWeight p P i * (E i i).re := by
      apply Finset.sum_nonneg; intro i _
      exact mul_nonneg (complementWeight_nonneg p P hp h0 h1 h2 i)
        (RCLike.nonneg_iff.mp (hE.1.diag_nonneg (i := i))).1
    change eventResponse (candidate eps - causalCompletion p P) E ≤ _; rw [completion_response]
    dsimp [compressedPositiveMass]; linarith
  obtain ⟨Ep, En, hEp, hEn, hv, hnv, hb, hgreat⟩ :=
    attained_two_direction_spectral_events hM hX
  have hmass : weightedPositiveMass M hX = compressedPositiveMass eps q t hP := by
    apply le_antisymm
    · have := hupper Ep hEp
      rw [hv] at this; exact this
    · have hLift := lift_compressed_event q t hq hq1 ht ht1 hF
      have h := (hb (embedBlock F) hLift).1
      change eventResponse (candidate eps - causalCompletion p P) (embedBlock F) ≤ _ at h
      rw [completion_lifted_response, hvF] at h; exact h
  have htrace : eventResponse X M = -eps * (1 - q - t) := by
    have hst := normalization_trace S (diagonalMarginal p) (diagonalTester q t)
      hS.2.2.2 hS.2.2.1 hCn
    have hR := candidate_normalization_response eps q t he he1
    have h : eventResponse X M = eventResponse (candidate eps) M - 1 := by
      simp [X, eventResponse, Matrix.sub_mul, Matrix.trace_sub, M, testerNormalization, hst]
    rw [h, hR]; ring
  have hrev (E : Matrix Wire Wire ℂ) :
      response (S - candidate eps) E = -eventResponse X E := by
    simp [X, response, eventResponse, Matrix.sub_mul, trace_sub]
  refine ⟨hS, Ep, En, ⟨hC, hCn, hEp⟩, ⟨hC, hCn, hEn⟩, ?_, ?_, ?_, ?_⟩
  · exact hv.trans hmass
  · rw [hrev, hnv, hmass, htrace]
    ring
  · intro E hE
    have h := hb E ⟨hE.2.2.1, hE.2.2.2⟩
    refine ⟨h.1.trans_eq hmass, ?_⟩
    rw [hrev]; rw [hmass, htrace] at h; linarith [h.2]
  · have ht : -eventResponse X M = eps * (1 - q - t) := by rw [htrace]; ring
    rw [hmass, ht] at hgreat
    simpa only [Tester, hC, hCn, true_and, EventInterval, M, testerNormalization,
      Matrix.kronecker, X, S, response, eventResponse] using hgreat
private theorem completion_phase_fixed (p : ℝ) (P : Matrix (Fin 3) (Fin 3) ℂ) (g : Phase) :
    signConjugate (phaseWire g) (causalCompletion p P) = causalCompletion p P := by
  have hm (i : Wire) (hi : MainSupport i) : phaseWire g i = 1 := by
    rcases hi with rfl | rfl | rfl <;> rcases g with ⟨a, b⟩ <;>
      fin_cases a <;> fin_cases b <;> norm_num [phaseWire, phaseAB, phaseD, bitSign, Fin.ext_iff]
  have hs (i : Wire) : phaseWire g i * phaseWire g i = 1 := by
    dsimp [phaseWire, phaseAB]
    calc
      _ = (bitSign g.1 i.1.1 * bitSign g.1 i.1.1) *
        (bitSign g.2 i.1.2 * bitSign g.2 i.1.2) * (phaseD g i.2 * phaseD g i.2) := by ring
      _ = 1 := by rw [bitSign_sq, bitSign_sq, phaseD_sq]; ring
  ext i j
  by_cases hij : i = j
  · subst j
    change phaseWire g i * causalCompletion p P i i * phaseWire g i = _
    calc
      _ = (phaseWire g i * phaseWire g i) * causalCompletion p P i i := by ring
      _ = _ := by rw [hs, one_mul]
  · by_cases hi : MainSupport i <;> by_cases hj : MainSupport j <;>
      simp [signConjugate, causalCompletion, Matrix.diagonal, hij, embedBlock_entry, hi, hj, hm]
private theorem diagonal_tester_parameters {C : Matrix AB AB ℂ} (hC : C.PosSemidef) (hCn :
    partialTraceLeft C = 1) (hCd : C.IsDiag) : ∃ q t : ℝ, 0 ≤ q ∧ q ≤ 1 ∧ 0 ≤ t ∧ t ≤ 1 ∧ C =
    diagonalTester q t := by
  let q := (C (0, 0) (0, 0)).re; let t := (C (1, 1) (1, 1)).re
  have hq : 0 ≤ q := (RCLike.nonneg_iff.mp (hC.diag_nonneg (i := (0, 0)))).1
  have ht : 0 ≤ t := (RCLike.nonneg_iff.mp (hC.diag_nonneg (i := (1, 1)))).1
  have h01 : 0 ≤ (C (0, 1) (0, 1)).re :=
    (RCLike.nonneg_iff.mp (hC.diag_nonneg (i := (0, 1)))).1
  have h10 : 0 ≤ (C (1, 0) (1, 0)).re :=
    (RCLike.nonneg_iff.mp (hC.diag_nonneg (i := (1, 0)))).1
  have hb0 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => (M 0 0).re) hCn
  have hb1 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => (M 1 1).re) hCn
  simp [partialTraceLeft, Fin.sum_univ_two] at hb0 hb1
  have hq1 : q ≤ 1 := by dsimp [q]; linarith
  have ht1 : t ≤ 1 := by dsimp [t]; linarith
  have hr (ab : AB) : C ab ab = ((C ab ab).re : ℂ) :=
    Complex.eq_re_of_ofReal_le (r := 0) hC.diag_nonneg
  have hd (ab : AB) : C ab ab = (testerWeight q t ab : ℂ) := by
    rcases ab with ⟨a, b⟩
    fin_cases a <;> fin_cases b
    · change C (0, 0) (0, 0) = (q : ℂ)
      exact hr _
    · change C (0, 1) (0, 1) = ((1 - t : ℝ) : ℂ)
      rw [hr]; congr 1; dsimp [t]; linarith
    · change C (1, 0) (1, 0) = ((1 - q : ℝ) : ℂ)
      rw [hr]; congr 1; dsimp [q]; linarith
    · change C (1, 1) (1, 1) = (t : ℂ)
      exact hr _
  refine ⟨q, t, hq, hq1, ht, ht1, ?_⟩
  calc
    C = diagonal (fun ab => C ab ab) := hCd.diagonal_diag.symm
    _ = diagonalTester q t := congrArg diagonal (funext hd)
theorem full_tester_compressed_objective (eps p : ℝ) (P : Matrix (Fin 3) (Fin 3) ℂ)
    (he : 0 ≤ eps) (he1 : eps ≤ 1) (hp : 0 ≤ p) (hp1 : p ≤ 1) (hP : P.PosSemidef)
    (h0 : (P 0 0).re ≤ 1 - p) (h1 : (P 1 1).re ≤ 1 - p) (h2 : (P 2 2).re ≤ p) (b : ℝ) :
    ErrorBound (candidate eps - causalCompletion p P) b ↔
      ∀ q t : ℝ, 0 ≤ q → q ≤ 1 → 0 ≤ t → t ≤ 1 →
        compressedPositiveMass eps q t hP + max (eps * (1 - q - t)) 0 ≤ b := by
  let S := causalCompletion p P; have hS := (compressed_block_causal_lift p P hp hp1 hP h0 h1 h2).1
  constructor
  · intro hError q t hq hq1 ht ht1
    obtain ⟨_, _, _, _, _, _, _, hgreat⟩ :=
      (compressed_completion_tester_value eps p q t P he he1 hp hp1 hq hq1 ht ht1
        hP h0 h1 h2).2
    obtain ⟨E, hE, hv⟩ := hgreat.1
    calc
      _ = |response (candidate eps - causalCompletion p P) E| := hv.symm
      _ ≤ b := hError _ _ hE
  · intro hBound C E hCE
    have hAvg := average_tester hCE
    have hresp := average_invariant_response (candidate eps - S) E (fun g => by
      rw [signConjugate_sub, candidate_fixed, completion_phase_fixed])
    obtain ⟨q, t, hq, hq1, ht, ht1, hQt⟩ :=
      diagonal_tester_parameters hAvg.1 hAvg.2.1 (averageAB_diagonal C)
    rw [hQt] at hAvg
    obtain ⟨_, _, _, _, _, _, _, hgreat⟩ :=
      (compressed_completion_tester_value eps p q t P he he1 hp hp1 hq hq1 ht ht1
        hP h0 h1 h2).2
    have h := hgreat.2 ⟨averageWire E, hAvg, rfl⟩
    change |response (candidate eps - S) E| ≤ b; rw [← hresp]
    exact h.trans (hBound q t hq hq1 ht ht1)
private theorem response_compressed_event (X : Matrix Wire Wire ℂ) (F : Matrix (Fin 3) (Fin 3) ℂ) :
    eventResponse X (embedBlock F) = eventResponse (X.submatrix mainAddress mainAddress) F := by
  calc
    _ = eventResponse (embedBlock F) X := congrArg Complex.re (trace_mul_comm X (embedBlock F))
    _ = eventResponse F (blockEmbeddingᴴ * X * blockEmbedding) := response_embed F X
    _ = _ := by rw [block_compression]; exact congrArg Complex.re (trace_mul_comm F _)
theorem causal_compressed_repair_domination (eps : ℝ) (S : Matrix Wire Wire ℂ)
    (sigma : Matrix (Fin 2) (Fin 2) ℂ) (he : 0 ≤ eps) (he1 : eps ≤ 1) (hS : Causal S sigma) :
    let p := (sigma 1 1).re
    let P := S.submatrix mainAddress mainAddress
    Causal (causalCompletion p P) (diagonalMarginal p) ∧
      (causalCompletion p P).submatrix mainAddress mainAddress = P ∧
      diagonalMarginal p 1 1 = sigma 1 1 ∧
      (∀ b : ℝ, ErrorBound (candidate eps - S) b →
        ErrorBound (candidate eps - causalCompletion p P) b) := by
  intro p P
  obtain ⟨hp, hp1, hP, h0, h1, h2⟩ := causal_principal_block_budgets S sigma hS
  have hLift := compressed_block_causal_lift p P hp hp1 hP h0 h1 h2
  refine ⟨hLift.1, hLift.2.1, ?_, ?_⟩
  · rw [hLift.2.2]
    exact (Complex.eq_re_of_ofReal_le (r := 0) hS.2.1.diag_nonneg).symm
  · intro b hError
    apply (full_tester_compressed_objective eps p P he he1 hp hp1 hP h0 h1 h2 b).mpr
    intro q t hq hq1 ht ht1; let C := diagonalTester q t; let M := testerNormalization q t
    let X := candidate eps - S; have hC := diagonalTester_pos q t hq hq1 ht ht1
    have hCn := diagonalTester_normalized q t
    have hB := compressedNormalization_pos q t hq hq1 ht ht1
    obtain ⟨F, _, hF, _, hvF, _, _, _⟩ :=
      attained_two_direction_spectral_events hB (compressed_difference_hermitian eps hP)
    have hE := lift_compressed_event q t hq hq1 ht ht1 hF
    have hCE : Tester C (embedBlock F) := ⟨hC, hCn, hE⟩
    have hCM : Tester C (M - embedBlock F) :=
      ⟨hC, hCn, hE.2, by
        change (M - (M - embedBlock F)).PosSemidef; simpa only [sub_sub_cancel] using hE.1⟩
    have hval : eventResponse X (embedBlock F) = compressedPositiveMass eps q t hP := by
      rw [response_compressed_event]; change eventResponse (compressedDifference eps P) F = _
      exact hvF
    have htr : eventResponse X M = -eps * (1 - q - t) := by
      have hst := normalization_trace S sigma C hS.2.2.2 hS.2.2.1 hCn
      have hR := candidate_normalization_response eps q t he he1
      have h : eventResponse X M = eventResponse (candidate eps) M - 1 := by
        simp [X, eventResponse, Matrix.sub_mul, Matrix.trace_sub, M, C, testerNormalization, hst]
      rw [h, hR]; ring
    have hcomp : eventResponse X (M - embedBlock F) =
        -eps * (1 - q - t) - compressedPositiveMass eps q t hP := by
      simp only [eventResponse, Matrix.mul_sub, trace_sub, Complex.sub_re]
      change eventResponse X M - eventResponse X (embedBlock F) = _
      rw [htr, hval]
    have hpos : compressedPositiveMass eps q t hP ≤ b := by
      have h := (le_abs_self (eventResponse X (embedBlock F))).trans (hError C (embedBlock F) hCE)
      rwa [hval] at h
    have hneg : compressedPositiveMass eps q t hP + eps * (1 - q - t) ≤ b := by
      have h := (neg_le_abs (eventResponse X (M - embedBlock F))).trans
        (hError C (M - embedBlock F) hCM)
      rw [hcomp] at h; linarith
    by_cases hc : 0 ≤ eps * (1 - q - t)
    · rw [max_eq_left hc]
      exact hneg
    · rw [max_eq_right (le_of_not_ge hc), add_zero]
      exact hpos
end D5.S3.Quantum.Foundation.TwoRoundSpectralEvents
namespace D5.S3.Quantum.Foundation.TwoRoundRankOneReduction
open D5.S3.Quantum.Foundation.TwoRoundPhaseAverage
open D5.S3.Quantum.Foundation.TwoRoundSpectralEvents
/-- The saturated principal-block amplitudes at the original marginal parameter. -/
def repairVector (p : ℝ) (i : Fin 3) : ℝ :=
  if i = 2 then Real.sqrt p else Real.sqrt (1 - p)
def rankOneBlock (p : ℝ) : Matrix (Fin 3) (Fin 3) ℂ :=
  vecMulVec (fun i => (repairVector p i : ℂ)) (star (fun i => (repairVector p i : ℂ)))
/-- The complementary mass is part of the causal repair. -/
def rankOneRepair (p : ℝ) : Matrix Wire Wire ℂ := causalCompletion p (rankOneBlock p)
def scalarU (eps q t : ℝ) : ℝ := q + (1 - eps) * (1 - q) + eps * t
def scalarV (p t : ℝ) : ℝ := 1 - p + p * t
def scalarW (eps p q t : ℝ) : ℝ :=
  Real.sqrt (1 - p) * (q + Real.sqrt (1 - eps) * (1 - q)) + Real.sqrt (eps * p) * t
/-- The exact positive spectral root, including collinear and zero vectors. -/
def scalarLambda (eps p q t : ℝ) : ℝ :=
  (scalarU eps q t - scalarV p t +
    Real.sqrt ((scalarU eps q t + scalarV p t) ^ 2 - 4 * scalarW eps p q t ^ 2)) / 2
private def inputVector (eps : ℝ) (i : Fin 3) : ℝ :=
  if i = 0 then 1 else if i = 1 then Real.sqrt (1 - eps) else Real.sqrt eps
private def weightVector (q t : ℝ) (i : Fin 3) : ℝ :=
  if i = 0 then Real.sqrt q else if i = 1 then Real.sqrt (1 - q) else Real.sqrt t
private def weightedInput (eps q t : ℝ) (i : Fin 3) : ℝ :=
  weightVector q t i * inputVector eps i
private def weightedRepair (p q t : ℝ) (i : Fin 3) : ℝ :=
  weightVector q t i * repairVector p i
private theorem rankOneBlock_pos (p : ℝ) : (rankOneBlock p).PosSemidef :=
  posSemidef_vecMulVec_self_star _
private theorem rankOneBlock_budgets (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) : (rankOneBlock p 0 0).re =
    1 - p ∧ (rankOneBlock p 1 1).re = 1 - p ∧ (rankOneBlock p 2 2).re = p := by
  simp [rankOneBlock, repairVector, vecMulVec_apply, Real.mul_self_sqrt hp,
    Real.mul_self_sqrt (sub_nonneg.mpr hp1)]
private theorem normalization_sqrt (q t : ℝ) (hq : 0 ≤ q) (hq1 : q ≤ 1) (ht : 0 ≤ t) : CFC.sqrt
    (compressedNormalization q t) = diagonal (fun i => (weightVector q t i : ℂ)) := by
  let D : Matrix (Fin 3) (Fin 3) ℂ := diagonal (fun i => (weightVector q t i : ℂ))
  have hD : D.PosSemidef := PosSemidef.diagonal (fun i =>
    Complex.nonneg_iff.mpr ⟨by dsimp [weightVector]; split_ifs <;> positivity, by simp⟩)
  have hs : D * D = compressedNormalization q t := by
    rw [diagonal_mul_diagonal]; ext i j
    fin_cases i <;> fin_cases j <;>
      simp [compressedNormalization, weightVector, diagonal,
        ← Complex.ofReal_mul, Real.mul_self_sqrt hq,
        Real.mul_self_sqrt (sub_nonneg.mpr hq1), Real.mul_self_sqrt ht]
  exact CFC.sqrt_unique hs hD.nonneg
private theorem input_compression (eps : ℝ) : (candidate eps).submatrix mainAddress mainAddress =
    realOuter (inputVector eps) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [candidate, candidateVector, mainAddress, realOuter, inputVector, vecMulVec_apply]
private theorem weighted_difference (eps q t : ℝ) (P : Matrix (Fin 3) (Fin 3) ℂ) (hq : 0 ≤ q) (hq1 :
    q ≤ 1) (ht : 0 ≤ t) : weightedOperator (compressedNormalization q t) (compressedDifference eps
    P) = diagonal (fun i => (weightVector q t i : ℂ)) * (realOuter (inputVector eps) - P) * diagonal
    (fun i => (weightVector q t i : ℂ)) := by
  rw [weightedOperator, normalization_sqrt q t hq hq1 ht]
  have hD : (diagonal (fun i => (weightVector q t i : ℂ)))ᴴ =
      diagonal (fun i => (weightVector q t i : ℂ)) := by simp [diagonal_conjTranspose]
  rw [hD, compressedDifference, input_compression]
private theorem weighted_rank_one_difference (eps p q t : ℝ) (hq : 0 ≤ q) (hq1 : q ≤ 1) (ht : 0 ≤ t)
    : weightedOperator (compressedNormalization q t) (compressedDifference eps (rankOneBlock p)) =
    realOuter (weightedInput eps q t) - realOuter (weightedRepair p q t) := by
  rw [weighted_difference eps q t _ hq hq1 ht]; ext i j
  simp [Matrix.diagonal_mul, Matrix.mul_diagonal, realOuter, rankOneBlock,
    weightedInput, weightedRepair, vecMulVec_apply, Complex.ofReal_mul]
  ring
private theorem weighted_grams (eps p q t : ℝ) (he : 0 ≤ eps) (he1 : eps ≤ 1) (hp : 0 ≤ p) (hp1 : p
    ≤ 1) (hq : 0 ≤ q) (hq1 : q ≤ 1) (ht : 0 ≤ t) : gramU (weightedInput eps q t) = scalarU eps q t ∧
    gramU (weightedRepair p q t) = scalarV p t ∧ gramW (weightedInput eps q t) (weightedRepair p q
    t) = scalarW eps p q t := by
  constructor
  · simp [gramU, weightedInput, weightVector, inputVector, Fin.sum_univ_three, mul_pow,
      Real.sq_sqrt hq, Real.sq_sqrt (sub_nonneg.mpr hq1), Real.sq_sqrt ht,
      Real.sq_sqrt he, Real.sq_sqrt (sub_nonneg.mpr he1), scalarU]
    ring
  constructor
  · simp [gramU, weightedRepair, weightVector, repairVector, Fin.sum_univ_three, mul_pow,
      Real.sq_sqrt hq, Real.sq_sqrt (sub_nonneg.mpr hq1), Real.sq_sqrt ht,
      Real.sq_sqrt hp, Real.sq_sqrt (sub_nonneg.mpr hp1), scalarV]
    ring
  · simp [gramW, weightedInput, weightedRepair, weightVector, inputVector, repairVector,
      scalarW, Fin.sum_univ_three, Real.sqrt_mul he]
    ring_nf
    simp [Real.sq_sqrt hq, Real.sq_sqrt (sub_nonneg.mpr hq1), Real.sq_sqrt ht]; ring
private theorem mass_congr {A B : Matrix (Fin 3) (Fin 3) ℂ} (hA : A.IsHermitian) (hB :
    B.IsHermitian) (h : A = B) : positiveSpectralMass hA = positiveSpectralMass hB := by
  subst B; rfl
private theorem compressed_rank_one_mass (eps p q t : ℝ) (he : 0 ≤ eps) (he1 : eps ≤ 1) (hp : 0 ≤ p)
    (hp1 : p ≤ 1) (hq : 0 ≤ q) (hq1 : q ≤ 1) (ht : 0 ≤ t) : compressedPositiveMass eps q t
    (rankOneBlock_pos p) = scalarLambda eps p q t := by
  have hB := weighted_rank_one_difference eps p q t hq hq1 ht
  unfold compressedPositiveMass weightedPositiveMass
  have hmass := rank_one_positive_mass (weightedInput eps q t) (weightedRepair p q t)
  let hRight : (realOuter (weightedInput eps q t) - realOuter (weightedRepair p q t)).IsHermitian :=
    (posSemidef_vecMulVec_self_star _).isHermitian.sub
      (posSemidef_vecMulVec_self_star _).isHermitian
  obtain ⟨hU, hV, hW⟩ := weighted_grams eps p q t he he1 hp hp1 hq hq1 ht
  calc
    _ = positiveSpectralMass hRight := mass_congr _ hRight hB
    _ = positiveRoot (weightedInput eps q t) (weightedRepair p q t) := hmass
    _ = scalarLambda eps p q t := by simp only [positiveRoot, scalarLambda, hU, hV, hW]
private theorem budget_entry_bound {P : Matrix (Fin 3) (Fin 3) ℂ} (hP : P.PosSemidef) (v : Fin 3 →
    ℝ) (hv : ∀ i, 0 ≤ v i) (hd : ∀ i, (P i i).re ≤ v i ^ 2) (i j : Fin 3) : (P i j).re ≤ v i * v j
    := by
  have h := D5.S3.Quantum.QuantumChannels.QubitWassersteinCouplings.psd_entry_bound hP i j
  have hb := mul_le_mul (hd i) (hd j)
    (Complex.nonneg_iff.mp (hP.diag_nonneg (i := j))).1 (sq_nonneg (v i))
  have hsq : (P i j).re ^ 2 ≤ (v i * v j) ^ 2 := by
    simp only [Complex.normSq_apply] at h; nlinarith [sq_nonneg (P i j).im]
  nlinarith [mul_nonneg (hv i) (hv j)]
private theorem repair_offdiagonal (eps p : ℝ) (he : 0 ≤ eps) (hehalf : eps ≤ 1 / 2) (hp : 0 ≤ p)
    (hplo : 1 - Real.sqrt (1 - eps) ≤ p) (hphi : p ≤ eps) : ∀ i j : Fin 3, i ≠ j → 0 ≤ inputVector
    eps i * inputVector eps j - repairVector p i * repairVector p j := by
  have he1 : eps ≤ 1 := by linarith
  have hp1 : p ≤ 1 := by linarith
  have hc := Real.sqrt_nonneg (1 - eps); have hs := Real.sqrt_nonneg eps
  have ha := Real.sqrt_nonneg (1 - p); have hb := Real.sqrt_nonneg p
  have hcs := Real.sq_sqrt (sub_nonneg.mpr he1); have hss := Real.sq_sqrt he
  have has := Real.sq_sqrt (sub_nonneg.mpr hp1); have hbs := Real.sq_sqrt hp
  have hab : (Real.sqrt p * Real.sqrt (1 - p)) ^ 2 = p * (1 - p) := by rw [mul_pow, hbs, has]
  have hcsprod : (Real.sqrt (1 - eps) * Real.sqrt eps) ^ 2 = (1 - eps) * eps := by
    rw [mul_pow, hcs, hss]
  have hmon : p * (1 - p) ≤ eps * (1 - eps) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hphi) (show 0 ≤ 1 - eps - p by linarith)]
  have hxy : 0 ≤ Real.sqrt (1 - eps) - Real.sqrt (1 - p) * Real.sqrt (1 - p) := by nlinarith
  have hxz : 0 ≤ Real.sqrt eps - Real.sqrt p * Real.sqrt (1 - p) := by nlinarith [mul_nonneg hb ha]
  have hyz : 0 ≤ Real.sqrt (1 - eps) * Real.sqrt eps -
      Real.sqrt p * Real.sqrt (1 - p) := by nlinarith [mul_nonneg hc hs, mul_nonneg hb ha]
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    first | exact (hij rfl).elim |
      (simp [inputVector, repairVector, Fin.ext_iff]; nlinarith)
private def realWeightedDifference (eps p q t : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  vecMulVec (weightedInput eps q t) (weightedInput eps q t) -
    vecMulVec (weightedRepair p q t) (weightedRepair p q t)
private theorem realWeightedDifference_map (eps p q t : ℝ) : (realWeightedDifference eps p q t).map
    Complex.ofRealHom = realOuter (weightedInput eps q t) - realOuter (weightedRepair p q t) := by
  ext i j; simp [realWeightedDifference, realOuter, vecMulVec_apply]
private theorem positiveRoot_mem_spectrum (eps p q t : ℝ) : positiveRoot (weightedInput eps q t)
    (weightedRepair p q t) ∈ spectrum ℝ (realWeightedDifference eps p q t) := by
  let lam := positiveRoot (weightedInput eps q t) (weightedRepair p q t)
  have hz : (realOuter (weightedInput eps q t) - realOuter (weightedRepair p q t)).charpoly.eval
      (lam : ℂ) = 0 := by rw [difference_charpoly]; simp [lam]
  rw [← realWeightedDifference_map, Matrix.charpoly_map] at hz
  change ((realWeightedDifference eps p q t).charpoly.map Complex.ofRealHom).eval
    (Complex.ofRealHom lam) = 0 at hz
  rw [Polynomial.eval_map_apply] at hz; apply Matrix.mem_spectrum_of_isRoot_charpoly
  apply Complex.ofReal_injective; exact hz
/-- All original full testers are controlled exactly by the two scalar normalization parameters. -/
theorem rank_one_full_objective (eps p b : ℝ) (he : 0 ≤ eps) (he1 : eps ≤ 1) (hp : 0 ≤ p) (hp1 : p ≤
    1) : ErrorBound (candidate eps - rankOneRepair p) b ↔ ∀ q t : ℝ, 0 ≤ q → q ≤ 1 → 0 ≤ t → t ≤ 1 →
    scalarLambda eps p q t + max (eps * (1 - q - t)) 0 ≤ b := by
  obtain ⟨h0, h1, h2⟩ := rankOneBlock_budgets p hp hp1
  refine (full_tester_compressed_objective eps p (rankOneBlock p) he he1 hp hp1
    (rankOneBlock_pos p) h0.le h1.le h2.le b).trans ?_
  refine forall_congr' fun q => forall_congr' fun t => forall_congr' fun hq =>
    forall_congr' fun hq1 => forall_congr' fun ht => forall_congr' fun _ht1 => ?_
  rw [compressed_rank_one_mass eps p q t he he1 hp hp1 hq hq1 ht]
private theorem compressed_rank_one_domination (eps p q t : ℝ) (P : Matrix (Fin 3) (Fin 3) ℂ) (he :
    0 ≤ eps) (hehalf : eps ≤ 1 / 2) (hp : 0 ≤ p) (hplo : 1 - Real.sqrt (1 - eps) ≤ p) (hphi : p ≤
    eps) (hP : P.PosSemidef) (h0 : (P 0 0).re ≤ 1 - p) (h1 : (P 1 1).re ≤ 1 - p) (h2 : (P 2 2).re ≤
    p) (hq : 0 ≤ q) (hq1 : q ≤ 1) (ht : 0 ≤ t) : scalarLambda eps p q t ≤ compressedPositiveMass eps
    q t hP := by
  have he1 : eps ≤ 1 := by linarith
  have hp1 : p ≤ 1 := by linarith
  have hv (i : Fin 3) : 0 ≤ repairVector p i := by
    dsimp [repairVector]
    split_ifs <;> positivity
  have hd (i : Fin 3) : (P i i).re ≤ repairVector p i ^ 2 := by
    fin_cases i
    · simpa [repairVector, Real.sq_sqrt (sub_nonneg.mpr hp1)] using h0
    · simpa [repairVector, Real.sq_sqrt (sub_nonneg.mpr hp1)] using h1
    · simpa [repairVector, Real.sq_sqrt hp] using h2
  have hw (i : Fin 3) : 0 ≤ weightVector q t i := by
    dsimp [weightVector]
    split_ifs <;> positivity
  let H := realWeightedDifference eps p q t
  let A := weightedOperator (compressedNormalization q t) (compressedDifference eps P)
  have hH : H.IsHermitian := by
    apply isHermitian_iff_isSymm.mpr; ext i j
    dsimp [H, realWeightedDifference, Matrix.transpose, vecMulVec]; ring
  have hA : A.IsHermitian := isHermitian_conjTranspose_mul_mul _
    (((posSemidef_vecMulVec_self_star (candidateVector eps)).isHermitian.submatrix
      mainAddress).sub hP.isHermitian)
  have hHentry (i j : Fin 3) : H i j = weightVector q t i *
      (inputVector eps i * inputVector eps j - repairVector p i * repairVector p j) *
        weightVector q t j := by
    dsimp [H, realWeightedDifference, vecMulVec, weightedInput, weightedRepair]; ring
  have hAentry (i j : Fin 3) : (A i j).re = weightVector q t i *
      (inputVector eps i * inputVector eps j - (P i j).re) * weightVector q t j := by
    dsimp [A]; rw [weighted_difference eps q t P hq hq1 ht]
    simp [Matrix.diagonal_mul, Matrix.mul_diagonal, realOuter, vecMulVec_apply,
      Complex.mul_re]
  have hoff (i j : Fin 3) (hij : i ≠ j) : 0 ≤ H i j := by
    rw [hHentry]
    exact mul_nonneg (mul_nonneg (hw i)
      (repair_offdiagonal eps p he hehalf hp hplo hphi i j hij)) (hw j)
  have hentry (i j : Fin 3) : H i j ≤ (A i j).re := by
    rw [hHentry, hAentry]; exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (sub_le_sub_left (budget_entry_bound hP _ hv hd i j) _)
        (hw i)) (hw j)
  have hbound := real_eigenvalue_le_mass hH hA hoff hentry (positiveRoot_mem_spectrum eps p q t)
  obtain ⟨hU, hV, hW⟩ := weighted_grams eps p q t he he1 hp hp1 hq hq1 ht
  have hroot : positiveRoot (weightedInput eps q t) (weightedRepair p q t) =
      scalarLambda eps p q t := by simp only [positiveRoot, scalarLambda, hU, hV, hW]
  rw [hroot] at hbound; exact hbound
/-- Every original complex causal repair with marginal in the comparison interval is dominated
by the explicit repair at exactly that marginal, for the complete original tester set. -/
theorem same_p_error_domination (eps : ℝ) (S : Matrix Wire Wire ℂ)
    (sigma : Matrix (Fin 2) (Fin 2) ℂ) (he : 0 ≤ eps) (hehalf : eps ≤ 1 / 2)
    (hS : Causal S sigma) (hplo : 1 - Real.sqrt (1 - eps) ≤ (sigma 1 1).re)
    (hphi : (sigma 1 1).re ≤ eps) :
    let p := (sigma 1 1).re
    Causal (rankOneRepair p) (diagonalMarginal p) ∧
      diagonalMarginal p 1 1 = sigma 1 1 ∧
      ∀ b : ℝ, ErrorBound (candidate eps - S) b →
        ErrorBound (candidate eps - rankOneRepair p) b ∧
        ∀ q t : ℝ, 0 ≤ q → q ≤ 1 → 0 ≤ t → t ≤ 1 →
          scalarLambda eps p q t + max (eps * (1 - q - t)) 0 ≤ b := by
  intro p
  have he1 : eps ≤ 1 := by linarith
  obtain ⟨hp, hp1, hP, h0, h1, h2⟩ := causal_principal_block_budgets S sigma hS
  obtain ⟨hb0, hb1, hb2⟩ := rankOneBlock_budgets p hp hp1
  have hLift := compressed_block_causal_lift p (rankOneBlock p) hp hp1 (rankOneBlock_pos p)
    hb0.le hb1.le hb2.le
  refine ⟨hLift.1, ?_, ?_⟩
  · rw [hLift.2.2]
    exact (Complex.eq_re_of_ofReal_le (r := 0) hS.2.1.diag_nonneg).symm
  · intro b hError
    have hComp := (causal_compressed_repair_domination eps S sigma he he1 hS).2.2.2 b hError
    have hScalar := (full_tester_compressed_objective eps p
      (S.submatrix mainAddress mainAddress) he he1 hp hp1 hP h0 h1 h2 b).mp hComp
    have hRepair : ErrorBound (candidate eps - rankOneRepair p) b := by
      apply (rank_one_full_objective eps p b he he1 hp hp1).mpr; intro q t hq hq1 ht ht1
      have hdom := compressed_rank_one_domination eps p q t
        (S.submatrix mainAddress mainAddress) he hehalf hp hplo hphi hP h0 h1 h2 hq hq1 ht
      linarith [hScalar q t hq hq1 ht ht1]
    exact ⟨hRepair, (rank_one_full_objective eps p b he he1 hp hp1).mp hRepair⟩
open D5.S3.Quantum.Information.PartialTraceMutualInformation
open scoped Matrix.Norms.L2Operator
private theorem psd_closed {n : Type*} [Finite n] [Nonempty n] : IsClosed {M : Matrix n n ℂ |
    M.PosSemidef} := by
  classical
  let := Fintype.ofFinite n
  have heq : {M : Matrix n n ℂ | M.PosSemidef} = Set.Ici 0 := by
    ext M; exact Matrix.nonneg_iff_posSemidef.symm
  rw [heq]; exact isClosed_Ici
private theorem psd_trace_entry {n : Type*} [Fintype n] {M : Matrix n n ℂ} (hM : M.PosSemidef) {r :
    ℝ} (hr : 0 ≤ r) (htr : M.trace.re ≤ r) (i j : n) : ‖M i j‖ ≤ r := by
  classical
  have hd (k : n) : (M k k).re ≤ r := by
    apply le_trans _ htr; simpa only [Matrix.trace, Matrix.diag_apply, Complex.re_sum] using
      (Finset.single_le_sum (fun l _ => (Complex.nonneg_iff.mp (hM.diag_nonneg (i := l))).1)
        (Finset.mem_univ k))
  have hn (k : n) : 0 ≤ (M k k).re := (Complex.nonneg_iff.mp (hM.diag_nonneg (i := k))).1
  have h := D5.S3.Quantum.QuantumChannels.QubitWassersteinCouplings.psd_entry_bound hM i j
  rw [Complex.normSq_eq_norm_sq] at h; have hm := mul_le_mul (hd i) (hd j) (hn j) hr
  nlinarith [norm_nonneg (M i j)]
private theorem bounded_psd_compact {n : Type*} [Fintype n] [Nonempty n] (r : ℝ) (hr : 0 ≤ r) :
    IsCompact {M : Matrix n n ℂ | M.PosSemidef ∧ M.trace.re ≤ r} := by
  classical
  have hc : IsClosed {M : Matrix n n ℂ | M.PosSemidef ∧ M.trace.re ≤ r} :=
    psd_closed.inter (isClosed_le
      (show Continuous (fun M : Matrix n n ℂ => M.trace.re) from by
        simp only [Matrix.trace, Matrix.diag_apply]
        fun_prop) continuous_const)
  have hb : IsCompact {M : Matrix n n ℂ | ∀ i j, M i j ∈ Metric.closedBall 0 r} :=
    isCompact_pi_infinite (fun _ => isCompact_pi_infinite (fun _ => isCompact_closedBall 0 r))
  apply hb.of_isClosed_subset hc; intro M hM i j; rw [Metric.mem_closedBall, dist_zero_right]
  exact psd_trace_entry hM.1 hr hM.2 i j
private def causalPairs : Set (Matrix Wire Wire ℂ × Matrix (Fin 2) (Fin 2) ℂ) :=
  {z | Causal z.1 z.2}
private def testerPairs : Set (Matrix AB AB ℂ × Matrix Wire Wire ℂ) :=
  {z | Tester z.1 z.2}
private theorem causal_trace {S : Matrix Wire Wire ℂ} {sigma : Matrix (Fin 2) (Fin 2) ℂ} (hS :
    Causal S sigma) : S.trace = 2 := by
  rw [← trace_partialTraceRight, hS.2.2.2, Matrix.kronecker, Matrix.trace_kronecker, hS.2.2.1]; simp
private theorem tester_trace {C : Matrix AB AB ℂ} {E : Matrix Wire Wire ℂ} (hT : Tester C E) :
    C.trace = 2 ∧ E.trace.re ≤ 6 := by
  have hc : C.trace = 2 := by rw [← trace_partialTraceLeft, hT.2.1]; simp
  refine ⟨hc, ?_⟩
  have h := (Complex.nonneg_iff.mp hT.2.2.2.trace_nonneg).1
  rw [Matrix.trace_sub, Matrix.kronecker, Matrix.trace_kronecker, hc] at h; norm_num at h; linarith
private theorem causal_pairs_compact : IsCompact causalPairs := by
  have hclosed : IsClosed causalPairs :=
    (psd_closed.preimage continuous_fst).inter ((psd_closed.preimage continuous_snd).inter
      ((isClosed_eq (by unfold Matrix.trace; fun_prop) continuous_const).inter
        (isClosed_eq (by unfold partialTraceRight; fun_prop) (by
          apply continuous_pi; intro i; apply continuous_pi; intro j
          simp only [Matrix.kronecker, Matrix.kroneckerMap_apply]; fun_prop))))
  apply ((bounded_psd_compact (n := Wire) 2 (by norm_num)).prod
    (bounded_psd_compact (n := Fin 2) 1 (by norm_num))).of_isClosed_subset hclosed
  intro z hz; exact ⟨⟨hz.1, by rw [causal_trace hz]; norm_num⟩,
    ⟨hz.2.1, by rw [hz.2.2.1]; norm_num⟩⟩
private theorem tester_pairs_compact : IsCompact testerPairs := by
  have hclosed : IsClosed testerPairs :=
    (psd_closed.preimage continuous_fst).inter
      ((isClosed_eq (by unfold partialTraceLeft; fun_prop) continuous_const).inter
        ((psd_closed.preimage continuous_snd).inter (psd_closed.preimage (by
          apply continuous_pi; intro i; apply continuous_pi; intro j
          simp only [Matrix.sub_apply, Matrix.kronecker, Matrix.kroneckerMap_apply]; fun_prop))))
  apply ((bounded_psd_compact (n := AB) 2 (by norm_num)).prod
    (bounded_psd_compact (n := Wire) 6 (by norm_num))).of_isClosed_subset hclosed
  intro z hz
  obtain ⟨hc, he⟩ := tester_trace hz
  exact ⟨⟨hz.1, by rw [hc]; norm_num⟩, ⟨hz.2.2.1, he⟩⟩
private theorem original_pairs_nonempty : causalPairs.Nonempty ∧ testerPairs.Nonempty := by
  obtain ⟨h0, h1, h2⟩ := rankOneBlock_budgets 0 (by norm_num) (by norm_num)
  have h := compressed_completion_tester_value 0 0 0 0 (rankOneBlock 0) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (rankOneBlock_pos 0) h0.le h1.le h2.le
  obtain ⟨Ep, En, hEp, _, _⟩ := h.2
  exact ⟨⟨(rankOneRepair 0, diagonalMarginal 0), h.1⟩, ⟨(diagonalTester 0 0, Ep), hEp⟩⟩
/-- The supremum is over the original full normalization and event pair. -/
def testerNorm (X : Matrix Wire Wire ℂ) : ℝ :=
  sSup ((fun z => |response X z.2|) '' testerPairs)
/-- The infimum is over the original causal pair, including all complex repairs. -/
def optimalError (eps : ℝ) : ℝ :=
  sInf ((fun z => testerNorm (candidate eps - z.1)) '' causalPairs)
private theorem response_continuous : Continuous (fun z : Matrix Wire Wire ℂ × (Matrix AB AB ℂ ×
    Matrix Wire Wire ℂ) => |response z.1 z.2.2|) := by
  simp only [response, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]; fun_prop
theorem tester_norm_continuous : Continuous testerNorm :=
  tester_pairs_compact.continuous_sSup response_continuous
theorem tester_norm_attained (X : Matrix Wire Wire ℂ) : ∃ C E, Tester C E ∧ |response X E| =
    testerNorm X ∧ ErrorBound X (testerNorm X) := by
  let f : Matrix AB AB ℂ × Matrix Wire Wire ℂ → ℝ := fun z => |response X z.2|
  have hg : Continuous (fun z : Matrix AB AB ℂ × Matrix Wire Wire ℂ => (X, z)) :=
    continuous_const.prodMk continuous_id
  have hf0 := response_continuous.comp hg; have hf : Continuous f := hf0
  obtain ⟨z, hz, hn, hm⟩ := tester_pairs_compact.exists_sSup_image_eq_and_ge
    original_pairs_nonempty.2 hf.continuousOn
  exact ⟨z.1, z.2, hz, hn.symm, fun C E hT => (hm (C, E) hT).trans_eq hn.symm⟩
private theorem tester_norm_le {X : Matrix Wire Wire ℂ} {b : ℝ} (hb : ErrorBound X b) : testerNorm X
    ≤ b := by
  obtain ⟨C, E, hT, hn, _⟩ := tester_norm_attained X
  rw [← hn]; exact hb C E hT
theorem original_minimum_attained (eps : ℝ) : ∃ S sigma, Causal S sigma ∧ testerNorm (candidate eps
    - S) = optimalError eps ∧ ∀ T tau, Causal T tau → optimalError eps ≤ testerNorm (candidate eps -
    T) := by
  let f : Matrix Wire Wire ℂ × Matrix (Fin 2) (Fin 2) ℂ → ℝ :=
    fun z => testerNorm (candidate eps - z.1)
  have hg : Continuous (fun z : Matrix Wire Wire ℂ × Matrix (Fin 2) (Fin 2) ℂ =>
      candidate eps - z.1) := continuous_const.sub continuous_fst
  have hf0 := tester_norm_continuous.comp hg; have hf : Continuous f := hf0
  obtain ⟨z, hz, hn, hm⟩ := causal_pairs_compact.exists_sInf_image_eq_and_le
    original_pairs_nonempty.1 hf.continuousOn
  exact ⟨z.1, z.2, hz, hn.symm, fun T tau hT => hn.trans_le (hm (T, tau) hT)⟩
/-- Original global extrema exist. Every original optimum in the comparison interval has
an actual same-marginal rank-one optimum and the complete scalar objective at that value. -/
theorem attained_original_minimum_and_same_p_reduction (eps : ℝ)
    (he : 0 ≤ eps) (hehalf : eps ≤ 1 / 2) :
    (∃ S sigma, Causal S sigma ∧ testerNorm (candidate eps - S) = optimalError eps) ∧
    (∀ X : Matrix Wire Wire ℂ, ∃ C E, Tester C E ∧
      |response X E| = testerNorm X ∧ ErrorBound X (testerNorm X)) ∧
    ∀ S sigma, Causal S sigma → testerNorm (candidate eps - S) = optimalError eps →
      1 - Real.sqrt (1 - eps) ≤ (sigma 1 1).re → (sigma 1 1).re ≤ eps →
      let p := (sigma 1 1).re
      Causal (rankOneRepair p) (diagonalMarginal p) ∧
        diagonalMarginal p 1 1 = sigma 1 1 ∧
        testerNorm (candidate eps - rankOneRepair p) = optimalError eps ∧
        ∀ q t : ℝ, 0 ≤ q → q ≤ 1 → 0 ≤ t → t ≤ 1 →
          scalarLambda eps p q t + max (eps * (1 - q - t)) 0 ≤ optimalError eps := by
  obtain ⟨S0, sigma0, hS0, hn0, hmin⟩ := original_minimum_attained eps
  refine ⟨⟨S0, sigma0, hS0, hn0⟩, tester_norm_attained, ?_⟩
  intro S sigma hS hn hlo hhi p
  obtain ⟨C, E, hT, hval, hbound⟩ := tester_norm_attained (candidate eps - S)
  rw [hn] at hbound
  obtain ⟨hR, hsig, hdom⟩ := same_p_error_domination eps S sigma he hehalf hS hlo hhi
  obtain ⟨hb, hs⟩ := hdom _ hbound
  exact ⟨hR, hsig, le_antisymm (tester_norm_le hb) (hmin _ _ hR), hs⟩
end D5.S3.Quantum.Foundation.TwoRoundRankOneReduction
