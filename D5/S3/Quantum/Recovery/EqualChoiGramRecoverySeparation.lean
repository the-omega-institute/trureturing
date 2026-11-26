/- GID: D5/S3/Quantum/Recovery/EqualChoiGramRecoverySeparation
   generality: I
   mirror-B: D5/B/S3/Quantum/Recovery/EqualChoiGramRecoverySeparation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Two explicit four-dimensional channels share an exact Choi Gram and have unequal optimal recovery fidelity. -/

import D5.S3.Quantum.Recovery.BinaryRandomUnitaryChannel
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-! Two four-dimensional binary channels with the same branch Choi Gram. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators ComplexConjugate InnerProductSpace Matrix
open Matrix Finset Complex
open D5.S3.QuantumBounds.PeritoTsirelson (maxEntangledVector)

noncomputable section

open D5.S3.Quantum.Recovery.BinaryUnitaryOptimization
open D5.S3.Quantum.Recovery.BinaryRandomUnitaryChannel

namespace D5.S3.Quantum.Recovery.EqualChoiGramRecoverySeparation

private def aPlus : ℂ := Complex.exp ((↑(Real.pi / 3) : ℂ) * I)
private def aMinus : ℂ := Complex.exp ((↑(-(Real.pi / 3)) : ℂ) * I)

def entriesA : Fin 4 → ℂ := ![aPlus, aPlus, aMinus, aMinus]
def entriesB : Fin 4 → ℂ := ![1, 1, I, -I]

theorem entriesA_norm (j : Fin 4) : ‖entriesA j‖ = 1 := by
  have hp : ‖aPlus‖ = 1 := norm_exp_ofReal_mul_I _
  have hm : ‖aMinus‖ = 1 := norm_exp_ofReal_mul_I _
  fin_cases j <;> simp [entriesA, hp, hm]

theorem entriesB_norm (j : Fin 4) : ‖entriesB j‖ = 1 := by
  fin_cases j <;> simp [entriesB]

def W_A : unitaryGroup (Fin 4) ℂ := diagonalUnitary entriesA entriesA_norm
def W_B : unitaryGroup (Fin 4) ℂ := diagonalUnitary entriesB entriesB_norm

private theorem re_aPlus : aPlus.re = 1 / 2 := by
  rw [aPlus, exp_ofReal_mul_I_re, Real.cos_pi_div_three]

private theorem re_aMinus : aMinus.re = 1 / 2 := by
  rw [aMinus, exp_ofReal_mul_I_re, Real.cos_neg, Real.cos_pi_div_three]

private theorem sum_a : aPlus + aMinus = 1 := by
  apply Complex.ext
  · norm_num [re_aPlus, re_aMinus]
  · rw [Complex.add_im, aPlus, aMinus, exp_ofReal_mul_I_im, exp_ofReal_mul_I_im, Real.sin_neg]
    simp

private abbrev w : ℝ := 1 / 2
private def r : ℝ := Real.sqrt w
private theorem r_sq : r ^ 2 = w := Real.sq_sqrt (by norm_num)
private theorem r_nonneg : 0 ≤ r := Real.sqrt_nonneg _
private theorem w_nonneg : 0 ≤ w := by norm_num
private theorem weights : w + w = 1 := by norm_num

def channelA : CodeChannel 4 := binaryChannel w_nonneg w_nonneg weights 1 W_A
def channelB : CodeChannel 4 := binaryChannel w_nonneg w_nonneg weights 1 W_B

private def halfForm {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (x y : H) (z : ℂ) : H := (r : ℂ) • x + ((r : ℂ) * conj z) • y

private theorem halfForm_sq {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (x y : H) (hn : ‖x‖ ^ 2 + ‖y‖ ^ 2 = 1) (z : ℂ) (hz : ‖z‖ = 1) :
    ‖halfForm x y z‖ ^ 2 = w + (conj z * ⟪x, y⟫_ℂ).re := by
  rw [halfForm, sq_form, norm_mul, Complex.norm_of_nonneg r_nonneg,
    Complex.norm_conj, hz, mul_one, r_sq, Complex.conj_ofReal]
  have h : (r : ℂ) * ((r : ℂ) * conj z) * ⟪x, y⟫_ℂ =
      (w : ℂ) * (conj z * ⟪x, y⟫_ℂ) := by
    rw [← r_sq, Complex.ofReal_pow]
    ring
  rw [h, ← mul_add, hn]
  simp [Complex.mul_re]

private theorem inner_bound {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (x y : H) (hn : ‖x‖ ^ 2 + ‖y‖ ^ 2 = 1) :
    ‖⟪x, y⟫_ℂ‖ ≤ w := by
  refine (norm_inner_le_norm x y).trans ?_
  nlinarith [sq_nonneg (‖x‖ - ‖y‖), weights]

private theorem sum_le_sqrt {a b c : ℝ} (hc : 0 ≤ c) (h : 2 * (a ^ 2 + b ^ 2) ≤ c) :
    a + b ≤ Real.sqrt c := by
  apply le_of_pow_le_pow_left₀ (n := 2) (by decide) (Real.sqrt_nonneg _)
  rw [Real.sq_sqrt hc]
  nlinarith [sq_nonneg (a - b)]

private theorem dual_A {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (x y : H) (hn : ‖x‖ ^ 2 + ‖y‖ ^ 2 = 1) :
    (∑ j, ‖halfForm x y (entriesA j)‖) ≤ 2 * Real.sqrt 3 := by
  have hp : ‖aPlus‖ = 1 := entriesA_norm 0
  have hm : ‖aMinus‖ = 1 := entriesA_norm 2
  have hsq : ‖halfForm x y aPlus‖ ^ 2 + ‖halfForm x y aMinus‖ ^ 2 =
      1 + (⟪x, y⟫_ℂ : ℂ).re := by
    rw [halfForm_sq x y hn _ hp, halfForm_sq x y hn _ hm]
    have h : (conj aPlus * ⟪x, y⟫_ℂ).re + (conj aMinus * ⟪x, y⟫_ℂ).re =
        (⟪x, y⟫_ℂ : ℂ).re := by
      rw [← Complex.add_re, ← add_mul, ← map_add, sum_a, map_one, one_mul]
    linarith [weights]
  have h := (Complex.re_le_norm ⟪x, y⟫_ℂ).trans (inner_bound x y hn)
  have hpair : ‖halfForm x y aPlus‖ + ‖halfForm x y aMinus‖ ≤ Real.sqrt 3 :=
    sum_le_sqrt (by norm_num) (by linarith [weights])
  simp [Fin.sum_univ_four, entriesA]
  linarith

private theorem dual_B {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (x y : H) (hn : ‖x‖ ^ 2 + ‖y‖ ^ 2 = 1) :
    (∑ j, ‖halfForm x y (entriesB j)‖) ≤ 2 + Real.sqrt 2 := by
  have h := (Complex.re_le_norm ⟪x, y⟫_ℂ).trans (inner_bound x y hn)
  have h1 : ‖halfForm x y 1‖ ≤ 1 := by
    apply le_of_pow_le_pow_left₀ (n := 2) (by decide) zero_le_one
    rw [halfForm_sq x y hn _ norm_one]
    simp only [map_one, one_mul, one_pow]
    linarith [weights]
  have hsq : ‖halfForm x y I‖ ^ 2 + ‖halfForm x y (-I)‖ ^ 2 = 1 := by
    rw [halfForm_sq x y hn _ norm_I, halfForm_sq x y hn _ (by simp)]
    simp [map_neg, neg_mul, Complex.neg_re]
    ring
  have hi : ‖halfForm x y I‖ + ‖halfForm x y (-I)‖ ≤ Real.sqrt 2 :=
    sum_le_sqrt (by norm_num) (by linarith)
  simp [Fin.sum_univ_four, entriesB]
  linarith

private theorem column_bound {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (z : Fin 4 → ℂ) (v : Fin 4 → H) (hv : ∀ j, ‖v j‖ ≤ 1) (k : ℝ) (hk : 0 ≤ k)
    (hdual : ∀ x y : H, ‖x‖ ^ 2 + ‖y‖ ^ 2 = 1 →
      (∑ j, ‖halfForm x y (z j)‖) ≤ k) : columnLength r r z v ≤ k := by
  by_cases h0 : columnLength r r z v = 0
  · rwa [h0]
  · obtain ⟨x, y, hn, hbound⟩ := columnLength_le_dual r r z v hv h0
    exact hbound.trans (hdual x y hn)

private def decoderPhase (z : ℂ) : ℂ := aligningPhase (halfForm (r : ℂ) (r : ℂ) z)

private theorem decoderPhase_norm (z : ℂ) : ‖decoderPhase z‖ = 1 := norm_aligningPhase _

private theorem halfForm_scalar_sq (z : ℂ) (hz : ‖z‖ = 1) :
    ‖halfForm (r : ℂ) (r : ℂ) z‖ ^ 2 = w + w * z.re := by
  have hn : ‖(r : ℂ)‖ ^ 2 + ‖(r : ℂ)‖ ^ 2 = 1 := by
    rw [Complex.norm_of_nonneg r_nonneg, r_sq, weights]
  rw [halfForm_sq _ _ hn z hz, RCLike.inner_apply', Complex.conj_ofReal,
    ← pow_two, ← Complex.ofReal_pow, r_sq]
  simp [Complex.mul_re, mul_comm]

private theorem norm_halfForm_scalar (z : ℂ) (hz : ‖z‖ = 1) (k : ℝ) (hk : 0 ≤ k)
    (heq : w + w * z.re = k ^ 2) : ‖halfForm (r : ℂ) (r : ℂ) z‖ = k := by
  have h := halfForm_scalar_sq z hz
  rw [heq] at h
  nlinarith [norm_nonneg (halfForm (r : ℂ) (r : ℂ) z)]

private theorem scalar_dual_A :
    (∑ j, ‖halfForm (r : ℂ) (r : ℂ) (entriesA j)‖) = 2 * Real.sqrt 3 := by
  have hs := Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num)
  have hp := norm_halfForm_scalar aPlus (entriesA_norm 0) (Real.sqrt 3 / 2) (by positivity)
    (by rw [re_aPlus, div_pow, hs]; norm_num)
  have hm := norm_halfForm_scalar aMinus (entriesA_norm 2) (Real.sqrt 3 / 2) (by positivity)
    (by rw [re_aMinus, div_pow, hs]; norm_num)
  simp [Fin.sum_univ_four, entriesA, hp, hm]
  ring

private theorem scalar_dual_B :
    (∑ j, ‖halfForm (r : ℂ) (r : ℂ) (entriesB j)‖) = 2 + Real.sqrt 2 := by
  have hs := Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num)
  have h1 := norm_halfForm_scalar 1 norm_one 1 (by norm_num) (by norm_num)
  have hi := norm_halfForm_scalar I norm_I (Real.sqrt 2 / 2) (by positivity)
    (by rw [div_pow, hs]; norm_num)
  have hm := norm_halfForm_scalar (-I) (by simp) (Real.sqrt 2 / 2) (by positivity)
    (by rw [div_pow, hs]; norm_num)
  simp [Fin.sum_univ_four, entriesB, h1, hi, hm]
  ring

private theorem scalar_dual_attains (z : Fin 4 → ℂ) :
    (∑ j, ‖halfForm (r : ℂ) (r : ℂ) (z j)‖) ≤ columnLength r r z (decoderPhase ∘ z) := by
  have hn : ‖(r : ℂ)‖ ^ 2 + ‖(r : ℂ)‖ ^ 2 = 1 := by
    rw [Complex.norm_of_nonneg r_nonneg, r_sq, weights]
  exact scalar_dual_le_phase r r z (r : ℂ) (r : ℂ) hn

def decoderA : unitaryGroup (Fin 4) ℂ :=
  diagonalUnitary (decoderPhase ∘ entriesA) (fun j => decoderPhase_norm (entriesA j))

def decoderB : unitaryGroup (Fin 4) ℂ :=
  diagonalUnitary (decoderPhase ∘ entriesB) (fun j => decoderPhase_norm (entriesB j))

/-- The first four-dimensional channel has score at most (3/4) over all
    canonical CPTP decoders. The displayed unitary attains this bound. -/
theorem exampleA_exact :
    (∀ D : CodeChannel 4, recoveryScore channelA D ≤ 3 / 4) ∧
    recoveryScore channelA (unitaryChannel decoderA) = 3 / 4 := by
  have hpos : 0 ≤ 2 * Real.sqrt 3 := by positivity
  have hscale : (4 : ℝ)⁻¹ ^ 2 * (2 * Real.sqrt 3) ^ 2 = 3 / 4 := by
    rw [mul_pow, Real.sq_sqrt (by norm_num)]
    norm_num
  constructor
  · intro D
    obtain ⟨v, hv, hs⟩ := diagonal_score_vectors (d := 4) (by decide)
      w_nonneg w_nonneg weights entriesA entriesA_norm D
    change recoveryScore channelA D = _ at hs
    rw [hs, ← hscale]
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (Real.sqrt_nonneg _)
        (column_bound entriesA v hv _ hpos dual_A) 2) (sq_nonneg _)
  · change recoveryScore (binaryChannel w_nonneg w_nonneg weights 1
      (diagonalUnitary entriesA entriesA_norm))
      (unitaryChannel (diagonalUnitary _ _)) = _
    rw [diagonal_phase_score (by decide), ← hscale]
    change (4 : ℝ)⁻¹ ^ 2 * columnLength r r entriesA (decoderPhase ∘ entriesA) ^ 2 = _
    have hl := scalar_dual_attains entriesA
    rw [scalar_dual_A] at hl
    rw [le_antisymm (column_bound entriesA (decoderPhase ∘ entriesA) (fun j => (decoderPhase_norm _).le)
      _ hpos dual_A) hl]

/-- The second four-dimensional channel has score at most (3/8+sqrt{2}/4)
    over all canonical CPTP decoders. The displayed unitary attains it. -/
theorem exampleB_exact :
    (∀ D : CodeChannel 4, recoveryScore channelB D ≤ 3 / 8 + Real.sqrt 2 / 4) ∧
    recoveryScore channelB (unitaryChannel decoderB) = 3 / 8 + Real.sqrt 2 / 4 := by
  have hpos : 0 ≤ 2 + Real.sqrt 2 := by positivity
  have hscale : (4 : ℝ)⁻¹ ^ 2 * (2 + Real.sqrt 2) ^ 2 = 3 / 8 + Real.sqrt 2 / 4 := by
    nlinarith [Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num)]
  constructor
  · intro D
    obtain ⟨v, hv, hs⟩ := diagonal_score_vectors (d := 4) (by decide)
      w_nonneg w_nonneg weights entriesB entriesB_norm D
    change recoveryScore channelB D = _ at hs
    rw [hs, ← hscale]
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (Real.sqrt_nonneg _)
        (column_bound entriesB v hv _ hpos dual_B) 2) (sq_nonneg _)
  · change recoveryScore (binaryChannel w_nonneg w_nonneg weights 1
      (diagonalUnitary entriesB entriesB_norm))
      (unitaryChannel (diagonalUnitary _ _)) = _
    rw [diagonal_phase_score (by decide), ← hscale]
    change (4 : ℝ)⁻¹ ^ 2 * columnLength r r entriesB (decoderPhase ∘ entriesB) ^ 2 = _
    have hl := scalar_dual_attains entriesB
    rw [scalar_dual_B] at hl
    rw [le_antisymm (column_bound entriesB (decoderPhase ∘ entriesB) (fun j => (decoderPhase_norm _).le)
      _ hpos dual_B) hl]

/-- The unitary Choi branch vector is the actual normalized maximally
    entangled vector with the unitary acting on its first factor. -/
def branchChoiVector {d : ℕ} (U : CodeMatrix d) : Fin d × Fin d → ℂ :=
  Matrix.kronecker U (1 : CodeMatrix d) *ᵥ maxEntangledVector (Fin d)

theorem branchChoiVector_apply {d : ℕ} (U : CodeMatrix d) (i j : Fin d) :
    branchChoiVector U (i, j) = ((Real.sqrt (d : ℝ))⁻¹ : ℂ) * U i j := by
  simp [branchChoiVector, Matrix.mulVec, dotProduct, Matrix.kroneckerMap_apply,
    maxEntangledVector, Matrix.one_apply, Fintype.sum_prod_type, mul_comm]

private def gramEntries (z : Fin 4 → ℂ) : Bool → Fin 4 → ℂ
  | false => fun _ => 1
  | true => z

/-- Gram of the normalized branch Choi vectors for (I) and the given diagonal. -/
def branchChoiGram (z : Fin 4 → ℂ) : Matrix Bool Bool ℂ :=
  Matrix.of fun a b =>
    star (branchChoiVector (diagonal (gramEntries z a))) ⬝ᵥ
      branchChoiVector (diagonal (gramEntries z b))

private theorem gram_apply (z : Fin 4 → ℂ) (a b : Bool) :
    branchChoiGram z a b = (1 / 4 : ℂ) * ∑ j, conj (gramEntries z a j) * gramEntries z b j := by
  have hs : Real.sqrt ((4 : ℕ) : ℝ) = 2 := by
    rw [show ((4 : ℕ) : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  unfold branchChoiGram
  simp only [Matrix.of_apply, dotProduct, Fintype.sum_prod_type, Pi.star_apply,
    branchChoiVector_apply]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Matrix.diagonal_apply, mul_zero, apply_ite, star_zero, ite_mul,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  rw [hs]
  change conj (((2 : ℝ) : ℂ)⁻¹ * gramEntries z a i) *
    (((2 : ℝ) : ℂ)⁻¹ * gramEntries z b i) = _
  rw [map_mul, map_inv₀, Complex.conj_ofReal]
  norm_num
  ring

private theorem gram_of_sum_two (z : Fin 4 → ℂ) (hz : ∀ j, ‖z j‖ = 1)
    (h : ∑ j, z j = 2) :
    branchChoiGram z = Matrix.of (fun a b => if a = b then 1 else 1 / 2) := by
  ext a b
  have hnorm (j) : conj (z j) * z j = 1 := by
    rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, hz j]
    norm_num
  have hc : ∑ j, conj (z j) = 2 := by
    rw [← map_sum, h]
    exact map_natCast (starRingEnd ℂ) 2
  rw [gram_apply]
  cases a <;> cases b <;> norm_num [gramEntries, h, hc, hnorm]

/-- The two unweighted normalized branch Choi Grams coincide, with off-diagonal (1/2). -/
theorem equal_branch_choi_gram :
    branchChoiGram entriesA = branchChoiGram entriesB ∧
    branchChoiGram entriesA = Matrix.of (fun a b => if a = b then 1 else 1 / 2) := by
  have ha : ∑ j, entriesA j = 2 := by
    simp [Fin.sum_univ_four, entriesA]
    linear_combination 2 * sum_a
  have hb : ∑ j, entriesB j = 2 := by simp [Fin.sum_univ_four, entriesB]; ring
  have hA := gram_of_sum_two entriesA entriesA_norm ha
  have hB := gram_of_sum_two entriesB entriesB_norm hb
  exact ⟨hA.trans hB.symm, hA⟩

theorem equal_gram_strict_recovery_separation :
    branchChoiGram entriesA = branchChoiGram entriesB ∧
    (∀ D : CodeChannel 4, recoveryScore channelB D <
      recoveryScore channelA (unitaryChannel decoderA)) := by
  refine ⟨equal_branch_choi_gram.1, fun D => ?_⟩
  rw [exampleA_exact.2]
  apply (exampleB_exact.1 D).trans_lt
  have h := Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num)
  nlinarith [sq_nonneg (Real.sqrt 2 - 3 / 2)]

#print axioms exampleA_exact
#print axioms exampleB_exact
#print axioms equal_branch_choi_gram
#print axioms equal_gram_strict_recovery_separation

end D5.S3.Quantum.Recovery.EqualChoiGramRecoverySeparation
