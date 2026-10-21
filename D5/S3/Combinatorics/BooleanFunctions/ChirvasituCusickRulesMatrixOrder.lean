/- GID: D5/S3/Combinatorics/BooleanFunctions/ChirvasituCusickRulesMatrixOrder
   generality: I
   mirror-B: D5/B/S3/Combinatorics/BooleanFunctions/ChirvasituCusickRulesMatrixOrder
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Combinatorics/BooleanFunctions/ChirvasituCusickRulesMatrixOrder.claim; result=D5/S3/Combinatorics/BooleanFunctions/ChirvasituCusickRulesMatrixOrder.result; claim=D5/S3/Combinatorics/BooleanFunctions/ChirvasituCusickRulesMatrixOrder.claim
   digest: The rules-matrix order conjecture fails at (8,4) by a zero-trace obstruction. -/

/-
The public result is the designated refutation result (`basis=refutes`) and is exempt from four-slot escape registration (CLAUDE.md §3.9).
The source-facing definitions H0, H1, pad, rot, blockH, R, Rsq and claim retain the stated conventions literally; the finite witness definitions are private implementation carriers.
result — proof_shape: bind-only; escape_witness: none (settling result under open-problem-resolution).
admission_basis: open-problem-resolution (#19397; Refuted).
Direct frozen dependencies: none; the proof uses pinned Mathlib matrix, finite arithmetic and order facts.
All escape_witness fields are none; the module uses only the external open-problem-resolution basis.
The finite signed-transport certificates support the refutation through the consumers listed below.
row_lower — proof_shape: bind-only; consumer: row_formula.
row_upper — proof_shape: bind-only; consumer: row_formula.
row_other — proof_shape: bind-only; consumer: row_formula.
row_formula — proof_shape: bind-only; consumer: mulVec_eq_step.
mulVec_eq_step — proof_shape: bind-only; consumer: pauli_power.
intertwining_data — proof_shape: bind-only; consumer: pauli_step.
pauli_step — proof_shape: bind-only; consumer: pauli_power.
pauli_power — proof_shape: bind-only; consumer: power_diag_zero.
perm_endpoints — proof_shape: bind-only; consumers: pauli_zero_single, power_diag_zero.
phase_endpoints — proof_shape: bind-only; consumer: power_diag_zero.
pauli_zero_single — proof_shape: bind-only; consumer: power_diag_zero.
power_diag_zero — proof_shape: bind-only; consumer: trace_power.
trace_power — proof_shape: bind-only; consumer: order_ne.
sqrt_pow — proof_shape: bind-only; consumer: order_ne.
order_ne — proof_shape: bind-only; consumer: result.
H0 — definition; proof_shape: bind-only; escape_witness: none; consumer: blockH.
H1 — definition; proof_shape: bind-only; escape_witness: none; consumer: blockH.
pad — definition; proof_shape: bind-only; escape_witness: none; consumer: R.
rot — definition; proof_shape: bind-only; escape_witness: none; consumer: R.
blockH — definition; proof_shape: bind-only; escape_witness: none; consumer: R.
R — definition; proof_shape: bind-only; escape_witness: none; consumer: Rsq, A.
Rsq — definition; proof_shape: bind-only; escape_witness: none; consumer: claim, order_ne.
claim — definition; proof_shape: bind-only; escape_witness: none; consumer: result.
A — definition; proof_shape: bind-only; escape_witness: none; consumer: row_lower.
sgn — definition; proof_shape: bind-only; escape_witness: none; consumer: row_lower.
sparse — definition; proof_shape: bind-only; escape_witness: none; consumer: row_formula.
upperSign — definition; proof_shape: bind-only; escape_witness: none; consumer: mulVec_eq_step.
step — definition; proof_shape: bind-only; escape_witness: none; consumer: mulVec_eq_step.
pauliData — definition; proof_shape: bind-only; escape_witness: none; consumer: intertwining_data.
perm — definition; proof_shape: bind-only; escape_witness: none; consumer: intertwining_data.
phase — definition; proof_shape: bind-only; escape_witness: none; consumer: intertwining_data.
pauli — definition; proof_shape: bind-only; escape_witness: none; consumer: pauli_step.
-/

import Mathlib.Algebra.Algebra.Spectrum.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Basic.Complex.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Data.Fin.Init

/-! Binding conventions for A. Chirvasitu and T. W. Cusick, "Quadratic rotation symmetric Boolean functions",
arXiv:2304.12734v1 (Discrete Appl. Math. 343 (2024) 91–105), Section 6: the Hadamard matrices H0, H1, the padding
π_k and rotation ρ_k, the binomial rules matrix R(i, j) of Eq. (6-3), and Conjecture 6.1. -/

namespace D5.S3.Combinatorics.BooleanFunctions.ChirvasituCusickRulesMatrixOrder

open Matrix

/-- `H0 := [[1, 1], [1, −1]]`. -/
def H0 : Matrix (Fin 2) (Fin 2) ℤ := !![1, 1; 1, -1]

/-- `H1 := [[1, 1], [−1, 1]]`. -/
def H1 : Matrix (Fin 2) (Fin 2) ℤ := !![1, 1; -1, 1]

/-- `π_k(M)`: append `k` all-zero columns after each column of `M`. Column `b` of the result is column `b/(k+1)` of
`M` when `k + 1 ∣ b`, and zero otherwise. -/
def pad {r c : ℕ} (k : ℕ) (M : Matrix (Fin r) (Fin c) ℤ) : Matrix (Fin r) (Fin (c * (k + 1))) ℤ :=
  fun a b => if h : b.val % (k + 1) = 0 then M a ⟨b.val / (k + 1), by
    exact Nat.div_lt_of_lt_mul (by simp [Nat.mul_comm])⟩ else 0

/-- `ρ_k(M)`: rotate all rows of `M` simultaneously rightward `k` times, so entry `(a, b)` of the result is entry
`(a, b − k)` of `M`, indices modulo the number of columns. -/
def rot {r n : ℕ} [NeZero n] (k : ℕ) (M : Matrix (Fin r) (Fin n) ℤ) : Matrix (Fin r) (Fin n) ℤ :=
  fun a b => M a ⟨(b.val + n - k % n) % n, Nat.mod_lt _ (Nat.pos_of_neZero n)⟩

/-- The `H`-choice of block `k` in Eq. (6-3): the rows alternate between `H0` and `H1` in batches of `2^{j−1}`
blocks, starting with `H0`. -/
def blockH (j k : ℕ) : Matrix (Fin 2) (Fin 2) ℤ :=
  if (k / 2 ^ (j - 1)) % 2 = 0 then H0 else H1

/-- `R(i, j)` of Eq. (6-3): the `2^{i−1}` blocks `ρ_k π_{2^{i−1}−1} H_{ε(k)}` (`k = 0, …, 2^{i−1} − 1`), each a
`2 × (2 * 2^{i−1})` matrix (width `2^i` for `1 ≤ i`), stacked from top to bottom (row `2k + c` is row `c` of block `k`). -/
def R (i j : ℕ) : Matrix (Fin (2 ^ (i - 1) * 2)) (Fin (2 * 2 ^ (i - 1))) ℤ :=
  fun a b =>
    let p := finProdFinEquiv.symm a
    rot p.1.val (pad (2 ^ (i - 1) - 1) (blockH j p.1.val)) p.2
      (Fin.cast (by rw [Nat.sub_add_cancel (Nat.one_le_two_pow)]) b)

/-- `R(i, j)` as a real square matrix, rows and columns indexed in the same order; its size is `2^i` for `1 ≤ i`. -/
noncomputable def Rsq (i j : ℕ) : Matrix (Fin (2 * 2 ^ (i - 1))) (Fin (2 * 2 ^ (i - 1))) ℝ :=
  (R i j).submatrix (Fin.cast (Nat.mul_comm _ _)) id |>.map (Int.cast : ℤ → ℝ)

/-- Conjecture 6.1: "For i > j ≥ 1 the eigenvalues of the matrix R(i, j) of (6-3) are all √2-scaled roots of unity.
Moreover, the multiplicative order of R(i, j)/√2 is precisely 2 · lcm(4, i − j, i + j)." -/
def claim : Prop :=
  ∀ i j : ℕ, 1 ≤ j → j < i →
    (∀ μ ∈ spectrum ℂ ((Rsq i j).map (Complex.ofReal)), ∃ n : ℕ, 0 < n ∧ (μ / (Real.sqrt 2 : ℂ)) ^ n = 1) ∧
    orderOf ((Real.sqrt 2)⁻¹ • Rsq i j) = 2 * Nat.lcm 4 (Nat.lcm (i - j) (i + j))

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

private def A : Matrix (Fin 256) (Fin 256) ℤ :=
  (R 8 4).submatrix (Fin.cast (by norm_num)) id

private def sgn (a : Fin 256) : ℤ := if a.val % 2 = 0 ∨ (a.val / 16) % 2 = 0 then 1 else -1

private def sparse (a b : Fin 256) : ℤ :=
  Function.update (Pi.single (a / (2 : Fin 256) + 128)
    (if a.val % 2 = 0 then 1 else -(sgn a)) : Fin 256 → ℤ) (a / (2 : Fin 256)) (sgn a) b

private theorem row_lower : ∀ a : Fin 256, A a (a / (2 : Fin 256)) = sgn a := by
  decide +kernel

private theorem row_upper : ∀ a : Fin 256, A a ((a / (2 : Fin 256) + 128)) = if a.val % 2 = 0 then 1 else -(sgn a) := by
  decide +kernel

private theorem row_other (a b : Fin 256) (hl : b ≠ (a / (2 : Fin 256))) (hh : b ≠ (a / (2 : Fin 256) + 128)) : A a b = 0 := by
  have hl' : b.val ≠ a.val / 2 := Fin.val_ne_iff.mpr hl
  have hh' : b.val ≠ a.val / 2 + 128 := by
    have hv := Fin.val_ne_iff.mpr hh
    change b.val ≠ (a.val / 2 + 128) % 256 at hv
    have := a.isLt
    omega
  have hn : ((b.val + 256 - (a.val / 2) % 256) % 256) % 128 ≠ 0 := by
    have ha := a.isLt
    have hb := b.isLt
    omega
  change (if h : ((b.val + 256 - (a.val / 2) % 256) % 256) % 128 = 0 then _ else (0 : ℤ)) = 0
  simp only [hn, dite_false]

private theorem row_formula (a b : Fin 256) : A a b = sparse a b := by
  by_cases hl : b = (a / (2 : Fin 256))
  · subst b
    simpa [sparse] using row_lower a
  · by_cases hh : b = (a / (2 : Fin 256) + 128)
    · subst b
      simpa [sparse, hl] using row_upper a
    · simpa [sparse, hl, hh] using row_other a b hl hh


private def upperSign (a : Fin 256) : ℤ := if a.val % 2 = 0 then 1 else -(sgn a)
private def step (v : Fin 256 → ℤ) (a : Fin 256) : ℤ :=
  sgn a * v (a / (2 : Fin 256)) + upperSign a * v ((a / (2 : Fin 256) + 128))

private theorem mulVec_eq_step (v : Fin 256 → ℤ) : A *ᵥ v = step v := by
  funext a
  have hne : (a / (2 : Fin 256)) ≠ (a / (2 : Fin 256) + 128) := by
    exact left_ne_add.mpr (by decide : (128 : Fin 256) ≠ 0)
  simp only [Matrix.mulVec, dotProduct]
  rw [Finset.sum_eq_add_of_mem (a / (2 : Fin 256)) ((a / (2 : Fin 256) + 128)) (Finset.mem_univ _) (Finset.mem_univ _) hne]
  · simp [row_formula, sparse, hne.symm, step, upperSign]
  · intro b _ hb
    rw [row_formula]
    simp [sparse, hb.1, hb.2]

private def pauliData : ℕ → ℕ × ℕ × ℤ
  | 0 => (0, 1, 1)
  | 1 => (0, 2, 1)
  | 2 => (0, 4, 1)
  | 3 => (0, 8, 1)
  | 4 => (0, 16, 1)
  | 5 => (0, 32, 1)
  | 6 => (0, 64, 1)
  | 7 => (0, 128, 1)
  | 8 => (1, 16, 1)
  | 9 => (2, 32, 1)
  | 10 => (4, 64, 1)
  | 11 => (8, 128, 1)
  | 12 => (17, 17, -1)
  | 13 => (34, 34, -1)
  | 14 => (68, 68, -1)
  | 15 => (136, 136, -1)
  | 16 => (17, 0, -1)
  | 17 => (34, 0, -1)
  | 18 => (68, 0, -1)
  | 19 => (136, 0, -1)
  | 20 => (16, 0, -1)
  | 21 => (32, 0, -1)
  | 22 => (64, 0, -1)
  | 23 => (128, 0, -1)
  | 24 => (0, 1, -1)
  | _ => (0, 0, 1)

private def perm (n : ℕ) (a : Fin 256) : Fin 256 :=
  a ^^^ Fin.ofNat 256 (pauliData n).1
private def phase (n : ℕ) (a : Fin 256) : ℤ :=
  (pauliData n).2.2 * (-1) ^ (BitVec.ofNat 8 (a.val &&& (pauliData n).2.1)).cpop.toNat
private def pauli (n : ℕ) (v : Fin 256 → ℤ) : Fin 256 → ℤ :=
  phase n * (v ∘ perm n)

private theorem intertwining_data : ∀ n : Fin 24, ∀ a : Fin 256,
    (perm n.val (a / (2 : Fin 256)) = (perm (n.val+1) a / (2 : Fin 256)) ∧
     perm n.val ((a / (2 : Fin 256) + 128)) = (perm (n.val+1) a / (2 : Fin 256) + 128) ∧
     sgn a * phase n.val (a / (2 : Fin 256)) = phase (n.val+1) a * sgn (perm (n.val+1) a) ∧
     upperSign a * phase n.val ((a / (2 : Fin 256) + 128)) = phase (n.val+1) a * upperSign (perm (n.val+1) a)) ∨
    (perm n.val (a / (2 : Fin 256)) = (perm (n.val+1) a / (2 : Fin 256) + 128) ∧
     perm n.val ((a / (2 : Fin 256) + 128)) = (perm (n.val+1) a / (2 : Fin 256)) ∧
     sgn a * phase n.val (a / (2 : Fin 256)) = phase (n.val+1) a * upperSign (perm (n.val+1) a) ∧
     upperSign a * phase n.val ((a / (2 : Fin 256) + 128)) = phase (n.val+1) a * sgn (perm (n.val+1) a)) := by
  decide +kernel

private theorem pauli_step (n : ℕ) (hn : n < 24) (v : Fin 256 → ℤ) :
    step (pauli n v) = pauli (n+1) (step v) := by
  funext a
  rcases intertwining_data ⟨n, hn⟩ a with ⟨h1,h2,h3,h4⟩ | ⟨h1,h2,h3,h4⟩
  all_goals
    simp only [step, pauli, Pi.mul_apply, Function.comp_apply, mul_add, ← mul_assoc]
    rw [h1,h2,h3,h4]
    try exact add_comm _ _

private theorem pauli_power (n : ℕ) (hn : n ≤ 24) (v : Fin 256 → ℤ) :
    A ^ n *ᵥ pauli 0 v = pauli n (A ^ n *ᵥ v) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', ← Matrix.mulVec_mulVec, ih (by omega), mulVec_eq_step,
      pauli_step n (by omega)]
    congr 1
    rw [← mulVec_eq_step, Matrix.mulVec_mulVec]

private theorem perm_endpoints (n : ℕ) (hn : n = 0 ∨ n = 24) (a : Fin 256) : perm n a = a := by
  rcases hn with rfl | rfl <;> exact Fin.xor_zero a

private theorem phase_endpoints (a : Fin 256) : phase 24 a = -phase 0 a := by
  exact neg_mul (1 : ℤ) ((-1 : ℤ) ^ (BitVec.ofNat 8 (a.val &&& 1)).cpop.toNat)

private theorem pauli_zero_single (a : Fin 256) :
    pauli 0 (Pi.single a 1) = phase 0 a • Pi.single a 1 := by
  funext b
  simp only [pauli, Pi.mul_apply, Function.comp_apply, perm_endpoints 0 (Or.inl rfl), Pi.smul_apply, smul_eq_mul]
  rw [← Pi.single_mul_right_apply a b (phase 0) (1 : ℤ)]
  simpa only [mul_one, one_mul, mul_comm] using
    Pi.single_mul_left_apply a b (1 : ℤ) (fun _ => phase 0 a)

private theorem power_diag_zero (a : Fin 256) : (A ^ 24) a a = 0 := by
  have h := congrFun (pauli_power 24 (by omega) (Pi.single a 1)) a
  rw [pauli_zero_single, Matrix.mulVec_smul, Matrix.mulVec_single_one] at h
  simp only [pauli, Pi.mul_apply, Function.comp_apply, perm_endpoints 24 (Or.inr rfl), phase_endpoints, Pi.smul_apply,
    smul_eq_mul, Matrix.col, Matrix.transpose_apply] at h
  have hp : phase 0 a = 1 ∨ phase 0 a = -1 := by
    simp only [phase, pauliData, one_mul]
    exact neg_one_pow_eq_or ℤ _
  rcases hp with hp | hp <;> rw [hp] at h <;> linarith

private theorem trace_power : Matrix.trace (A ^ 24) = 0 := by
  simp [Matrix.trace, Matrix.diag, power_diag_zero]

private theorem sqrt_pow : (Real.sqrt 2) ^ 24 = (4096 : ℝ) := by
  calc
    (Real.sqrt 2) ^ 24 = ((Real.sqrt 2) ^ 2) ^ 12 := by rw [← pow_mul]
    _ = 4096 := by rw [Real.sq_sqrt (by norm_num)]; norm_num

private theorem order_ne : orderOf ((Real.sqrt 2)⁻¹ • Rsq 8 4) ≠ 24 := by
  intro h
  have hp : ((Real.sqrt 2)⁻¹ • Rsq 8 4) ^ 24 = 1 := by
    simpa only [h] using pow_orderOf_eq_one ((Real.sqrt 2)⁻¹ • Rsq 8 4)
  rw [smul_pow, inv_pow, sqrt_pow] at hp
  have hr := congrArg (fun M : Matrix (Fin 256) (Fin 256) ℝ => (4096 : ℝ) • M) hp
  simp only [smul_smul, mul_inv_cancel₀ (by norm_num : (4096 : ℝ) ≠ 0), one_smul] at hr
  have hm : (Rsq 8 4) ^ 24 = (A ^ 24).map (Int.castRingHom ℝ) := by
    have hm0 : Rsq 8 4 = A.map (Int.castRingHom ℝ) := by rfl
    rw [hm0, Matrix.map_pow]
  rw [hm] at hr
  have he := congrArg Matrix.trace hr
  have ht : Matrix.trace ((A ^ 24).map (Int.castRingHom ℝ)) = 0 := by
    rw [← AddMonoidHom.map_trace (Int.castRingHom ℝ), trace_power]
    simp
  rw [ht] at he
  norm_num [Matrix.trace_smul] at he

theorem result : ¬ claim := by
  intro h
  have ho := (h 8 4 (by omega) (by omega)).2
  norm_num at ho
  exact order_ne ho

end ChirvasituCusickRulesMatrixOrder
