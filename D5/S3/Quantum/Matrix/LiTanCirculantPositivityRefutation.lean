/- GID: D5/S3/Quantum/Matrix/LiTanCirculantPositivityRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/Matrix/LiTanCirculantPositivityRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Matrix/LiTanCirculantPositivityRefutation.claim; result=D5/S3/Quantum/Matrix/LiTanCirculantPositivityRefutation.result; claim=D5/S3/Quantum/Matrix/LiTanCirculantPositivityRefutation.claim
   digest: The Li–Tan circulant positivity conjecture fails at order four. -/

/-
admission_basis: open-problem-resolution (#19081; Refuted)
escape_witness: none
Direct frozen dependencies: none (every declaration; only pinned Mathlib is imported).
Definitions z, CH, claim, H, B, d, K, v: proof_shape: not-applicable (definitions).
h_gram: proof_shape: bind-only; consumer: h_psd.
h_psd: proof_shape: bind-only; consumer: result.
h_diag: proof_shape: bind-only; consumer: result.
z_values: proof_shape: bind-only; consumer: ch_eq.
shift_eq: proof_shape: bind-only; consumer: ch_eq.
ch_eq: proof_shape: bind-only; consumer: quadratic.
quadratic: proof_shape: bind-only; consumer: result.
result: proof_shape: bind-only; consumer: none (settling result).
The cyclic shift's prescribed entries are inlined through Matrix.of in CH;
shift_eq identifies it with Matrix.circulant (Pi.single (-1) 1) for use in the proof.
The public result is the designated refutation result (`basis=refutes`) and is
exempt from four-slot escape registration (CLAUDE.md §3.9).
-/

import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Circulant
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! Binding conventions for M.-S. Li and Y.-X. Tan, "On the Bargmann invariants for quantum imaginarity",
arXiv:2412.08022v1 (Phys. Rev. A 111 (2025) 022409), Sections II–III. Indices `1, …, n` of the source are
`Fin n`, so `k ⊕ l` (addition mod `n` on `{1, …, n}`) is addition in `Fin n`. -/

noncomputable section
open Matrix
namespace D5.S3.Quantum.Matrix.LiTanCirculantPositivityRefutation

open scoped ComplexOrder

/-- Section III: `z_k = (∏_{l=1}^n r_{l(l⊕k)})^{1/n} e^{iθ_k}` with `θ_k = (Σ_{l=1}^n θ_{l(l⊕k)})/n`, where
`h_{kl} = r_{kl} e^{iθ_{kl}}`, `r_{kl} ≥ 0` and `θ_{kl} ∈ (−π, π]` (so `r = ‖h‖` and `θ = arg h`). -/
def z (n : ℕ) [NeZero n] (H : Matrix (Fin n) (Fin n) ℂ) (k : ℕ) : ℂ :=
  (((∏ l : Fin n, ‖H l (l + Fin.ofNat n k)‖) ^ ((1 : ℝ) / n) : ℝ) : ℂ) *
    Complex.exp (Complex.I * (((∑ l : Fin n, Complex.arg (H l (l + Fin.ofNat n k))) / n : ℝ) : ℂ))

/-- Section III: the associated circulant matrix `C_H = Σ_{k=0}^{n−1} z_k C_n^k`. -/
def CH (n : ℕ) [NeZero n] (H : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  ∑ k ∈ Finset.range n, z n H k •
    (Matrix.of (fun i j : Fin n => if j = i + 1 then (1 : ℂ) else 0)) ^ k

/-- Section III: "the conjecture that the positive semidefiniteness of `H` implies the positive
semidefiniteness of `C_H` … for general `n`", for `H` in `𝐇_n` (positive semidefinite with `h_{ii} = 1`). -/
def claim : Prop :=
  ∀ (n : ℕ) [NeZero n] (H : Matrix (Fin n) (Fin n) ℂ), H.PosSemidef → (∀ i, H i i = 1) →
    (CH n H).PosSemidef

end D5.S3.Quantum.Matrix.LiTanCirculantPositivityRefutation

namespace D5.S3.Quantum.Matrix.LiTanCirculantPositivityRefutation
open scoped ComplexOrder
set_option maxRecDepth 2000
set_option maxHeartbeats 800000

private def H : Matrix (Fin 4) (Fin 4) ℂ :=
  !![1, 5/8, 1/9, 5/8; 5/8, 1, 5/8, 4/9;
     1/9, 5/8, 1, 5/8; 5/8, 4/9, 5/8, 1]
private def B : Matrix (Fin 4) (Fin 4) ℂ :=
  !![1, 5/8, 1/9, 5/8; 0, 1, 320/351, 31/351;
     0, 0, 1, 20/19; 0, 0, 0, 1]
private def d : Fin 4 → ℂ := ![1, 39/64, 1520/3159, 110/1539]

private theorem h_gram : H = Bᴴ * diagonal d * B := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [H, B, d, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fin.sum_univ_succ, map_ofNat]

private theorem h_psd : H.PosSemidef := by
  rw [h_gram]
  apply Matrix.PosSemidef.conjTranspose_mul_mul_same
  apply Matrix.PosSemidef.diagonal
  intro i
  fin_cases i <;> norm_num [d, Complex.le_def]

private theorem h_diag : ∀ i, H i i = 1 := by
  intro i
  fin_cases i <;> norm_num [H]

private theorem z_values :
    z 4 H 0 = 1 ∧ z 4 H 1 = 5/8 ∧ z 4 H 2 = 2/9 ∧ z 4 H 3 = 5/8 := by
  have ha (i j : Fin 4) : Complex.arg (H i j) = 0 := by
    fin_cases i <;> fin_cases j <;>
      apply Complex.arg_eq_zero_iff.mpr <;> norm_num [H]
  have hn (i j : Fin 4) : ‖H i j‖ = (H i j).re := by
    fin_cases i <;> fin_cases j <;>
      norm_num [H, norm_div, Complex.norm_natCast]
  simp only [z, ha, hn]
  norm_num [H, Fin.prod_univ_succ, Fin.sum_univ_succ, Fin.ofNat, Fin.add_def]

private def K : Matrix (Fin 4) (Fin 4) ℂ :=
  !![1, 5/8, 2/9, 5/8; 5/8, 1, 5/8, 2/9;
     2/9, 5/8, 1, 5/8; 5/8, 2/9, 5/8, 1]

private theorem shift_eq (n : ℕ) [NeZero n] :
    Matrix.of (fun i j : Fin n => if j = i + 1 then (1 : ℂ) else 0) =
      Matrix.circulant (Pi.single (-1 : Fin n) (1 : ℂ)) := by
  ext i j
  simp only [Matrix.of_apply, Matrix.circulant_apply, Pi.single_apply]
  congr 1
  simp only [sub_eq_iff_eq_add]
  apply propext
  constructor <;> intro h <;> rw [h] <;> abel

private theorem ch_eq : CH 4 H = K := by
  unfold CH
  rw [shift_eq]
  rw [show (-1 : Fin 4) = 3 from rfl]
  obtain ⟨h0,h1,h2,h3⟩ := z_values
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    h0, h1, h2, h3]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [K, Matrix.circulant_apply, Pi.single_apply, pow_succ, Matrix.mul_apply, Matrix.one_apply,
      Fin.sum_univ_succ, Fin.neg_def] <;> decide

private def v : Fin 4 → ℂ := ![1,-1,1,-1]

private theorem quadratic : star v ⬝ᵥ (CH 4 H *ᵥ v) = -1/9 := by
  rw [ch_eq]
  norm_num [v, K, dotProduct, Matrix.mulVec, Fin.sum_univ_succ,
    Pi.star_apply, map_neg, map_one]

theorem result : ¬ claim := by
  intro hc
  have hp := hc 4 H h_psd h_diag
  have hn := hp.dotProduct_mulVec_nonneg v
  rw [quadratic] at hn
  norm_num [Complex.le_def] at hn

end D5.S3.Quantum.Matrix.LiTanCirculantPositivityRefutation
