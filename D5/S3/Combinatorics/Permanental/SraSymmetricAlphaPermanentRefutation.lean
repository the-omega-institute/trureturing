/- GID: D5/S3/Combinatorics/Permanental/SraSymmetricAlphaPermanentRefutation
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Permanental/SraSymmetricAlphaPermanentRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Combinatorics/Permanental/SraSymmetricAlphaPermanentRefutation.claim; result=D5/S3/Combinatorics/Permanental/SraSymmetricAlphaPermanentRefutation.result; claim=D5/S3/Combinatorics/Permanental/SraSymmetricAlphaPermanentRefutation.claim
   digest: A symmetric inverse M matrix refutes alpha-permanent log-supermodularity. -/

/-
proof_shape: bind-only (same-delivery helpers expanded).
escape_witness: none.
admission_basis: open-problem-resolution (#21689; Refuted).
The public result is the designated refutation result (`basis=refutes`) and is exempt
from four-slot escape registration (CLAUDE.md §3.9).
The cycle-count expression is inlined rather than introducing an alias for an existing count.
Direct frozen dependencies (declaration statement_id):
none.
Declarations (all are on a settling result value path):
Symmetrizable: proof_shape: bind-only; escape_witness: none; consumer: claim.
alphaPermanent: proof_shape: bind-only; escape_witness: none; consumer: expand, principalAlphaPermanent.
principalAlphaPermanent: proof_shape: bind-only; escape_witness: none; consumer: claim, difference, expand, interval_failure, result.
claim: proof_shape: bind-only; escape_witness: none; consumer: result.
B: proof_shape: bind-only; escape_witness: none; consumer: B_mul_MB, difference, expand, interval_failure, inverseM, result, symmetric, witness_positive.
MB: proof_shape: bind-only; escape_witness: none; consumer: B_mul_MB, inverseM.
BQ: proof_shape: bind-only; escape_witness: none; consumer: cc, expand.
B_mul_MB: proof_shape: bind-only; escape_witness: none; consumer: inverseM.
witness_positive: proof_shape: bind-only; escape_witness: none; consumer: inverseM.
inverseM: proof_shape: bind-only; escape_witness: none; consumer: result.
symmetric: proof_shape: bind-only; escape_witness: none; consumer: result.
cc: proof_shape: bind-only; escape_witness: none; consumer: ccR, ccS, ccT, ccU, difference, expand.
expand: proof_shape: bind-only; escape_witness: none; consumer: difference.
countR: proof_shape: bind-only; escape_witness: none; consumer: difference.
countS: proof_shape: bind-only; escape_witness: none; consumer: difference.
countT: proof_shape: bind-only; escape_witness: none; consumer: difference.
countU: proof_shape: bind-only; escape_witness: none; consumer: difference.
ccR: proof_shape: bind-only; escape_witness: none; consumer: difference.
ccS: proof_shape: bind-only; escape_witness: none; consumer: difference.
ccT: proof_shape: bind-only; escape_witness: none; consumer: difference.
ccU: proof_shape: bind-only; escape_witness: none; consumer: difference.
difference: proof_shape: bind-only; escape_witness: none; consumer: interval_failure.
interval_failure: proof_shape: bind-only; escape_witness: none; consumer: result.
result: proof_shape: bind-only; escape_witness: none; consumer: settling conclusion.
-/


import D5.S3.Combinatorics.Permanental.SraReciprocalPermanentLorentzianRefutation


/-! The source assertion and its explicit inverse-M-matrix refutation. -/

noncomputable section
open scoped BigOperators
open Matrix Finset

namespace D5.S3.Combinatorics.Permanental.SraSymmetricAlphaPermanentRefutation
open D5.S3.Combinatorics.Permanental.SraReciprocalPermanentLorentzianRefutation

/-- Positive diagonal similarity to a symmetric matrix, exactly as in Sra's introduction. -/
def Symmetrizable {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∃ δ : Fin n → ℝ, (∀ i : Fin n, 0 < δ i) ∧
    (Matrix.diagonal δ * A * Matrix.diagonal (fun i => (δ i)⁻¹)).IsSymm

/-- Sra equation (3.1), with the empty permutation giving the empty α-permanent 1. -/
def alphaPermanent {ι : Type*} [Fintype ι] [DecidableEq ι]
    (α : ℝ) (H : Matrix ι ι ℝ) : ℝ :=
  ∑ π : Equiv.Perm ι, α ^ (π.cycleType.card + (Finset.univ.filter (fun i => π i = i)).card) * ∏ i : ι, H i (π i)

def principalAlphaPermanent {n : ℕ} (α : ℝ) (A : Matrix (Fin n) (Fin n) ℝ)
    (S : Finset (Fin n)) : ℝ :=
  alphaPermanent α (A.submatrix (fun i : S => (i : Fin n)) (fun i : S => (i : Fin n)))

/-- The universal affirmative extension asked about in Sra, Section 4(b). -/
def claim : Prop :=
  ∀ n : ℕ, 0 < n → ∀ A : Matrix (Fin n) (Fin n) ℝ,
    InverseMMatrix A → Symmetrizable A →
    ∀ α : ℝ, 0 < α → α ≠ (1 / 2 : ℝ) → α ≠ 1 →
    ∀ S T : Finset (Fin n),
      principalAlphaPermanent α A S * principalAlphaPermanent α A T ≤
        principalAlphaPermanent α A (S ∪ T) * principalAlphaPermanent α A (S ∩ T)


open D5.S3.Combinatorics.Permanental.SraReciprocalPermanentLorentzianRefutation
set_option maxRecDepth 10000
set_option maxHeartbeats 0

private def B : Matrix (Fin 4) (Fin 4) ℝ :=
  !![7,2,1,2; 2,7,2,1; 1,2,7,2; 2,1,2,7]
private def MB : Matrix (Fin 4) (Fin 4) ℝ :=
  !![1/6,-1/24,0,-1/24; -1/24,1/6,-1/24,0;
     0,-1/24,1/6,-1/24; -1/24,0,-1/24,1/6]
private def BQ : Matrix (Fin 4) (Fin 4) ℚ :=
  !![7,2,1,2; 2,7,2,1; 1,2,7,2; 2,1,2,7]

private theorem B_mul_MB : B * MB = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [B, MB, Matrix.mul_apply, Fin.sum_univ_succ]

private theorem witness_positive : ∀ i j : Fin 4, 0 < B i j := by
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [B]

private theorem inverseM : InverseMMatrix B := by
  refine ⟨?_, Matrix.isUnit_det_of_right_inverse B_mul_MB, ?_⟩
  · exact fun i j => (witness_positive i j).le
  · rw [Matrix.inv_eq_right_inv B_mul_MB]
    intro i j hij
    fin_cases i <;> fin_cases j <;> norm_num [MB] at *

private theorem symmetric : Symmetrizable B := by
  refine ⟨fun _ => 1, by simp, ?_⟩
  simp only [inv_one, Matrix.diagonal_one, Matrix.one_mul, Matrix.mul_one]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [B, Matrix.transpose_apply]


private def cc (S : Finset (Fin 4)) (k : ℕ) : ℚ :=
  ∑ π : Equiv.Perm S, if (π.cycleType.card + (Finset.univ.filter (fun i => π i = i)).card) = k then ∏ i : S, BQ i (π i) else 0

private theorem expand (α : ℝ) (S : Finset (Fin 4))
    (hb : ∀ π : Equiv.Perm S, (π.cycleType.card + (Finset.univ.filter (fun i => π i = i)).card) < 5) :
    principalAlphaPermanent α B S = ∑ k : Fin 5, (cc S k : ℝ) * α ^ (k : ℕ) := by
  simp only [cc, Rat.cast_sum, apply_ite, Rat.cast_prod, Rat.cast_zero,
    Finset.sum_mul, ite_mul, zero_mul]
  rw [Finset.sum_comm]
  unfold principalAlphaPermanent alphaPermanent
  apply Finset.sum_congr rfl
  intro π hπ
  rw [Finset.sum_eq_single (⟨(π.cycleType.card + (Finset.univ.filter (fun i => π i = i)).card), hb π⟩ : Fin 5)]
  · simp only [↓reduceIte, Matrix.submatrix_apply]
    rw [mul_comm]
    congr 1
    apply Finset.prod_congr rfl
    intro i hi
    change B i (π i) = (BQ i (π i) : ℝ)
    generalize (i : Fin 4) = j
    generalize (π i : Fin 4) = k
    fin_cases j <;> fin_cases k <;> norm_num [B, BQ]
  · intro k hk hne
    have hh : (π.cycleType.card + (Finset.univ.filter (fun i => π i = i)).card) ≠ (k : ℕ) := by
      intro h
      apply hne
      exact Fin.ext h.symm
    change (if (π.cycleType.card + (Finset.univ.filter (fun i => π i = i)).card) =
      (k : ℕ) then _ else 0) = 0
    rw [if_neg hh]
  · simp

private theorem countR : ∀ π : Equiv.Perm (↥({0,2} : Finset (Fin 4))), (π.cycleType.card + (Finset.univ.filter (fun i => π i = i)).card) < 5 := by decide +kernel
private theorem countS : ∀ π : Equiv.Perm (↥({0,1,2} : Finset (Fin 4))), (π.cycleType.card + (Finset.univ.filter (fun i => π i = i)).card) < 5 := by decide +kernel
private theorem countT : ∀ π : Equiv.Perm (↥({0,2,3} : Finset (Fin 4))), (π.cycleType.card + (Finset.univ.filter (fun i => π i = i)).card) < 5 := by decide +kernel
private theorem countU : ∀ π : Equiv.Perm (↥(univ : Finset (Fin 4))), (π.cycleType.card + (Finset.univ.filter (fun i => π i = i)).card) < 5 := by decide +kernel
private theorem ccR : ∀ k : Fin 5, cc {0,2} k = (![0,1,49,0,0] : Fin 5 → ℚ) k := by decide +kernel
private theorem ccS : ∀ k : Fin 5, cc {0,1,2} k = (![0,8,63,343,0] : Fin 5 → ℚ) k := by decide +kernel
private theorem ccT : ∀ k : Fin 5, cc {0,2,3} k = (![0,8,63,343,0] : Fin 5 → ℚ) k := by decide +kernel
private theorem ccU : ∀ k : Fin 5, cc univ k = (![0,48,257,882,2401] : Fin 5 → ℚ) k := by decide +kernel

private theorem difference (α : ℝ) :
    principalAlphaPermanent α B univ * principalAlphaPermanent α B {0,2} -
      principalAlphaPermanent α B {0,1,2} * principalAlphaPermanent α B {0,2,3} =
    α^2*(α+1)*(2401*α^2+1617*α-16) := by
  rw [expand α univ countU, expand α {0,2} countR,
    expand α {0,1,2} countS, expand α {0,2,3} countT]
  simp only [ccR, ccS, ccT, ccU]
  norm_num [Fin.sum_univ_succ]
  ring

private theorem interval_failure (α : ℝ) (ha : 0 < α) (hb : α ≤ 1/200) :
    principalAlphaPermanent α B univ * principalAlphaPermanent α B {0,2} <
      principalAlphaPermanent α B {0,1,2} * principalAlphaPermanent α B {0,2,3} := by
  have hbr : 2401*α^2+1617*α-16 < 0 := by
    nlinarith [mul_nonneg ha.le (show 0 ≤ 1/200-α by linarith)]
  have hneg := mul_neg_of_pos_of_neg (mul_pos (sq_pos_of_pos ha) (by linarith : 0 < α+1)) hbr
  rw [← difference] at hneg
  linarith

theorem result : ¬ claim := by
  intro h
  have hh := h 4 (by norm_num) B inverseM symmetric (1/200) (by norm_num)
    (by norm_num) (by norm_num) {0,1,2} {0,2,3}
  have hu : ({0,1,2} ∪ {0,2,3} : Finset (Fin 4)) = univ := by
    exact (compl_eq_empty_iff ({0,1,2} ∪ {0,2,3} : Finset (Fin 4))).mp rfl
  have hi : ({0,1,2} ∩ {0,2,3} : Finset (Fin 4)) = {0,2} := by decide
  rw [hu, hi] at hh
  exact (not_le_of_gt (interval_failure (1/200) (by norm_num) (by norm_num))) hh
end D5.S3.Combinatorics.Permanental.SraSymmetricAlphaPermanentRefutation
