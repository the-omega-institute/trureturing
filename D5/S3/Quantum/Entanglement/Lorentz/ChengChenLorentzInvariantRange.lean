/- GID: D5/S3/Quantum/Entanglement/Lorentz/ChengChenLorentzInvariantRange
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/Lorentz/ChengChenLorentzInvariantRange
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Odd-qubit Lorentz invariant values are exactly the complex image of [-1/2, 0]. -/

/-
proof_shape: result: bind-only; escape_witness: none
  admission_basis: open-problem-resolution (#18697; Proved)
  Direct frozen dependencies:
    RHLinalg.trace_mul_nonneg_of_posSemidef (GID D5/S3/Weil/ZetaLinear/RankTrace; statement_id sha256:d0be9623184a0aa6b2753f04a89d828122fe7292de10124c81506a795f6decf6)
    D5.S3.Quantum.Tomography.PurityPythagorasDecomposition.trace_mul_real_of_hermitian (GID D5/S3/Quantum/Tomography/PurityPythagorasDecomposition; statement_id sha256:1e1324fa199db4b069a84d9ade1af6c9de0e6a6e58122daaec95a759df7104f8)
  Escape audit: unfinished for result; reuse issue #19827 pending CI DTR reading.
  The claim keeps the preregistered convention bodies literally inlined; proofs reuse imported owners through consumed private helpers.
-/

import Mathlib.Analysis.Matrix.PosDef
import D5.S3.Weil.ZetaLinear.RankTrace
import D5.S3.Quantum.Tomography.PurityPythagorasDecomposition
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Complex.Order

set_option autoImplicit false

namespace D5.S3.Quantum.Entanglement.Lorentz.ChengChenLorentzInvariantRange

open Matrix
open scoped ComplexOrder

/-- The two-dimensional Levi-Civita symbol `ε = [[0, 1], [-1, 0]]`. -/
def eps : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; -1, 0]

/-- `ε_n = ε^{⊗n}`, the `n`-fold tensor (Kronecker) power, on the computational basis indexed by
`n`-bit strings. -/
def epsN (n : ℕ) : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ := fun i j => ∏ k, eps (i k) (j k)

/-- An `n`-qubit state: a positive semidefinite matrix of trace one. -/
def IsState {n : ℕ} (ρ : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ) : Prop :=
  ρ.PosSemidef ∧ ρ.trace = 1

/-- The Lorentz invariant `I_ρ = Tr(ρ^T ε_n ρ ε_n)` (Eq. (54)). -/
def lorentz {n : ℕ} (ρ : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ) : ℂ :=
  (ρᵀ * epsN n * ρ * epsN n).trace

/-- Cheng–Chen, arXiv:2605.19530v2, Conjecture 24 ("Suppose ρ is an arbitrary n-qubit state with odd n,
then the range of Lorentz invariant I_ρ is [−1/2, 0]."). -/
def claim : Prop :=
  ∀ n : ℕ, Odd n →
    {z : ℂ | ∃ ρ : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ, IsState ρ ∧ lorentz ρ = z} =
      (fun x : ℝ => (x : ℂ)) '' Set.Icc (-1 / 2) 0

end D5.S3.Quantum.Entanglement.Lorentz.ChengChenLorentzInvariantRange

namespace D5.S3.Quantum.Entanglement.Lorentz.ChengChenLorentzInvariantRange
open Matrix
open scoped ComplexOrder

private lemma eps_transpose : epsᵀ = -eps := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [eps]

private lemma eps_square : eps * eps = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [eps, Matrix.mul_apply, Fin.sum_univ_two]

private lemma epsN_transpose (n : ℕ) : (epsN n)ᵀ = (-1 : ℂ)^n • epsN n := by
  ext i j
  change (∏ k, eps (j k) (i k)) = (-1 : ℂ)^n * ∏ k, eps (i k) (j k)
  have h (k : Fin n) : eps (j k) (i k) = -eps (i k) (j k) := congrFun (congrFun eps_transpose (i k)) (j k)
  simp_rw [h]
  simp [Finset.prod_neg]

private lemma epsN_square (n : ℕ) : epsN n * epsN n = (-1 : ℂ)^n • (1 : Matrix (Fin n → Fin 2) _ ℂ) := by
  classical
  ext i j
  change (∑ x : Fin n → Fin 2, (∏ k, eps (i k) (x k)) * ∏ k, eps (x k) (j k)) = _
  simp_rw [← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun (k : Fin n) (a : Fin 2) => eps (i k) a * eps a (j k))]
  have h (k : Fin n) : (∑ a, eps (i k) a * eps a (j k)) = -(1 : Matrix (Fin 2) _ ℂ) (i k) (j k) :=
    congrFun (congrFun eps_square (i k)) (j k)
  simp_rw [h]
  by_cases hij : i = j
  · subst j
    simp [Matrix.one_apply, Finset.prod_neg]
  · have hex : ∃ k, i k ≠ j k := Function.ne_iff.mp hij
    obtain ⟨k, hk⟩ := hex
    have hp : (∏ a, -(1 : Matrix (Fin 2) _ ℂ) (i a) (j a)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ k) (by simp [Matrix.one_apply, hk])
    rw [hp]
    change (0 : ℂ) = (-1 : ℂ)^n * (1 : Matrix (Fin n → Fin 2) _ ℂ) i j
    simp [hij]

private lemma epsN_conjTranspose (n : ℕ) : (epsN n)ᴴ = (epsN n)ᵀ := by
  ext i j
  change star (∏ k, eps (j k) (i k)) = ∏ k, eps (j k) (i k)
  rw [star_prod]
  congr 1
  ext k
  generalize j k = a
  generalize i k = b
  fin_cases a <;> fin_cases b <;> norm_num [eps]

private lemma epsN_odd (n : ℕ) (hn : Odd n) : (epsN n)ᵀ = -epsN n ∧ epsN n * epsN n = -1 := by
  constructor
  · simpa [hn.neg_one_pow] using epsN_transpose n
  · simpa [hn.neg_one_pow] using epsN_square n


open Matrix
open scoped ComplexOrder
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private lemma skew_dot_zero (E : Matrix ι ι ℂ) (hE : Eᵀ = -E) (v : ι → ℂ) :
    v ⬝ᵥ (E *ᵥ v) = 0 := by
  have h := Matrix.dotProduct_transpose_mulVec E v v
  rw [hE, neg_mulVec, dotProduct_neg] at h
  linear_combination -h / 2

private lemma flip_norm (E : Matrix ι ι ℂ) (hE : Eᴴ * E = 1) (v : ι → ℂ)
    (hv : star v ⬝ᵥ v = 1) :
    star (E *ᵥ star v) ⬝ᵥ (E *ᵥ star v) = 1 := by
  rw [star_mulVec, star_star, dotProduct_mulVec, vecMul_vecMul, hE, vecMul_one]
  simpa only [dotProduct_comm] using hv

private lemma pair_complement_psd (v w : ι → ℂ)
    (hv : star v ⬝ᵥ v = 1) (hw : star w ⬝ᵥ w = 1)
    (hvw : star v ⬝ᵥ w = 0) :
    (1 - vecMulVec v (star v) - vecMulVec w (star w)).PosSemidef := by
  have hwv : star w ⬝ᵥ v = 0 := by
    rw [star_dotProduct, hvw, star_zero]
  let P := vecMulVec v (star v)
  let Q := vecMulVec w (star w)
  have hP : Pᴴ = P := (posSemidef_vecMulVec_self_star v).1
  have hQ : Qᴴ = Q := (posSemidef_vecMulVec_self_star w).1
  have hPP : P * P = P := by simp [P, vecMulVec_mul_vecMulVec, hv]
  have hQQ : Q * Q = Q := by simp [Q, vecMulVec_mul_vecMulVec, hw]
  have hPQ : P * Q = 0 := by simp [P, Q, vecMulVec_mul_vecMulVec, hvw]
  have hQP : Q * P = 0 := by simp [P, Q, vecMulVec_mul_vecMulVec, hwv]
  have hstar : (1 - P - Q)ᴴ = 1 - P - Q := by simp [hP, hQ]
  have hsquare : (1 - P - Q) * (1 - P - Q) = 1 - P - Q := by
    noncomm_ring [hPP, hQQ, hPQ, hQP]
  have h := posSemidef_conjTranspose_mul_self (1 - P - Q)
  rwa [hstar, hsquare] at h

private lemma spectral_mixture (A : Matrix ι ι ℂ) (hA : A.PosSemidef) (ht : A.trace = 1) :
    ∃ (p : ι → ℝ) (v : ι → ι → ℂ),
      (∀ i, 0 ≤ p i) ∧ (∑ i, p i) = 1 ∧
      (∀ i, star (v i) ⬝ᵥ v i = 1) ∧
      A = ∑ i, p i • vecMulVec (v i) (star (v i)) := by
  let U : Matrix ι ι ℂ := hA.1.eigenvectorUnitary
  let v : ι → ι → ℂ := fun i j => U j i
  refine ⟨hA.1.eigenvalues, v, hA.eigenvalues_nonneg, ?_, ?_, ?_⟩
  · have he : A.trace = ∑ i, (hA.1.eigenvalues i : ℂ) := hA.1.trace_eq_sum_eigenvalues
    rw [ht] at he
    have h := congrArg Complex.re he
    simpa only [Complex.one_re, Complex.re_sum, Complex.ofReal_re] using h.symm
  · intro i
    have hU : Uᴴ * U = 1 := Unitary.coe_star_mul_self hA.1.eigenvectorUnitary
    simpa only [v, dotProduct, Pi.star_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Matrix.one_apply_eq] using congrArg (fun M : Matrix ι ι ℂ => M i i) hU
  · conv_lhs => rw [hA.1.spectral_theorem, Unitary.conjStarAlgAut_apply]
    ext i j
    rw [Matrix.mul_apply]
    simp only [Matrix.mul_diagonal, Matrix.sum_apply, Matrix.smul_apply,
      Matrix.vecMulVec_apply, Matrix.star_apply, Matrix.conjTranspose_apply, Pi.star_apply, smul_eq_mul,
      Function.comp_apply, Complex.real_smul, v, U]
    apply Finset.sum_congr rfl
    intro k hk
    change U i k * (hA.1.eigenvalues k : ℂ) * star (U j k) =
      (hA.1.eigenvalues k : ℂ) * (U i k * star (U j k))
    ring

private lemma flip_rank_one (E : Matrix ι ι ℂ) (v : ι → ℂ) :
    E * (vecMulVec v (star v))ᵀ * Eᴴ =
      vecMulVec (E *ᵥ star v) (star (E *ᵥ star v)) := by
  rw [transpose_vecMulVec, mul_vecMulVec, vecMulVec_mul, star_mulVec]
  simp

private lemma breuer_psd (E A : Matrix ι ι ℂ) (hEt : Eᵀ = -E) (hEu : Eᴴ * E = 1)
    (hA : A.PosSemidef) (ht : A.trace = 1) :
    (1 - A - E * Aᵀ * Eᴴ).PosSemidef := by
  obtain ⟨p, v, hp, hsum, hv, hAv⟩ := spectral_mixture A hA ht
  have hpair (i : ι) := pair_complement_psd (v i) (E *ᵥ star (v i)) (hv i)
    (flip_norm E hEu (v i) (hv i)) (skew_dot_zero E hEt (star (v i)))
  have h := posSemidef_sum Finset.univ (fun i _ => (hpair i).smul (hp i))
  have hflip : E * Aᵀ * Eᴴ = ∑ i, p i • vecMulVec (E *ᵥ star (v i)) (star (E *ᵥ star (v i))) := by
    rw [hAv]
    simp only [transpose_sum, transpose_smul, Finset.mul_sum, Finset.sum_mul,
      Matrix.mul_smul, Matrix.smul_mul, flip_rank_one]
  have hsum' : (∑ i, p i • (1 : Matrix ι ι ℂ)) = 1 := by rw [← Finset.sum_smul, hsum, one_smul]
  simpa only [smul_sub, Finset.sum_sub_distrib, hsum', Complex.real_smul, ← hAv, ← hflip] using h

private lemma trace_mul_real (A B : Matrix ι ι ℂ) (hA : A.IsHermitian) (hB : B.IsHermitian) :
    ((A * B).trace.re : ℂ) = (A * B).trace := by
  classical
  let e := (Fintype.equivFin ι).symm
  have ht (M : Matrix ι ι ℂ) : (M.submatrix e e).trace = M.trace := by
    exact e.sum_comp (fun i => M i i)
  have h := (D5.S3.Quantum.Tomography.PurityPythagorasDecomposition.trace_mul_real_of_hermitian
    (A.submatrix e e) (B.submatrix e e) (hA.submatrix e) (hB.submatrix e)).symm
  rw [Matrix.submatrix_mul_equiv, ht] at h
  exact h

private lemma overlap_bound (A B : Matrix ι ι ℂ) (hA : A.PosSemidef) (hB : B.PosSemidef)
    (htA : A.trace = 1) (htB : B.trace = 1) (hAB : (1 - A - B).PosSemidef) :
    0 ≤ (A * B).trace.re ∧ (A * B).trace.re ≤ 1 / 2 := by
  have hlow := RHLinalg.trace_mul_nonneg_of_posSemidef hA hB
  have hS := RHLinalg.trace_mul_nonneg_of_posSemidef (hA.add hB) hAB
  change 0 ≤ (A * B).trace.re at hlow
  change 0 ≤ ((A + B) * (1 - A - B)).trace.re at hS
  have hD := posSemidef_conjTranspose_mul_self (A - B)
  rw [(hA.1.sub hB.1).eq] at hD
  have hD' := Complex.nonneg_iff.mp hD.trace_nonneg |>.1
  simp only [sub_mul, mul_sub, add_mul, mul_add, one_mul, mul_one, trace_add, trace_sub,
    Complex.add_re, Complex.sub_re, htA, htB, Complex.one_re] at hS hD'
  rw [trace_mul_comm B A] at hS hD'
  exact ⟨hlow, by linarith⟩


open Matrix
open scoped ComplexOrder

private lemma basis_pair_entries (n : ℕ) (hn : Odd n) :
    epsN n (fun _ => 0) (fun _ => 0) = 0 ∧
    epsN n (fun _ => 1) (fun _ => 1) = 0 ∧
    epsN n (fun _ => 0) (fun _ => 1) = 1 ∧
    epsN n (fun _ => 1) (fun _ => 0) = -1 := by
  have hn0 : n ≠ 0 := ne_of_gt hn.pos
  simp [epsN, eps, hn0, hn.neg_one_pow]

private lemma single_psd {ι : Type*} [Fintype ι] [DecidableEq ι] (a : ι) (p : ℝ) (hp : 0 ≤ p) :
    (Matrix.single a a (p : ℂ)).PosSemidef := by
  rw [← Matrix.diagonal_single]
  apply Matrix.PosSemidef.diagonal
  intro i
  by_cases hi : i = a
  · subst i
    simpa using Complex.zero_le_real.mpr hp
  · simp [Pi.single_apply, hi]

private lemma pair_state (n : ℕ) (a b : Fin n → Fin 2) (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    IsState (Matrix.single a a (p : ℂ) + Matrix.single b b ((1 - p : ℝ) : ℂ)) := by
  refine ⟨(single_psd a p hp).add (single_psd b (1-p) (by linarith)), ?_⟩
  simp

private lemma pair_lorentz (n : ℕ) (hn : Odd n) (p : ℝ) :
    lorentz (Matrix.single (fun _ : Fin n => (0 : Fin 2)) (fun _ => 0) (p : ℂ) +
      Matrix.single (fun _ => (1 : Fin 2)) (fun _ => 1) ((1 - p : ℝ) : ℂ)) =
        ((-2 * p * (1 - p) : ℝ) : ℂ) := by
  obtain ⟨h00, h11, h01, h10⟩ := basis_pair_entries n hn
  simp only [lorentz, transpose_add, transpose_single, add_mul, mul_add, trace_add,
    single_mul_mul_single, trace_single_mul, smul_eq_mul]
  rw [h00, h11, h01, h10]
  push_cast
  ring

private lemma attained (n : ℕ) (hn : Odd n) (x : ℝ) (hx : x ∈ Set.Icc (-1 / 2 : ℝ) 0) :
    ∃ ρ : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ, IsState ρ ∧ lorentz ρ = (x : ℂ) := by
  let p : ℝ := (1 - Real.sqrt (1 + 2*x)) / 2
  have hs : 0 ≤ Real.sqrt (1 + 2*x) := Real.sqrt_nonneg _
  have hsq : (Real.sqrt (1 + 2*x))^2 = 1 + 2*x := Real.sq_sqrt (by linarith [hx.1])
  have hs1 : Real.sqrt (1 + 2*x) ≤ 1 := Real.sqrt_le_one.mpr (by linarith [hx.2])
  have hp : 0 ≤ p := by dsimp [p]; linarith
  have hp1 : p ≤ 1 := by dsimp [p]; linarith
  refine ⟨Matrix.single (fun _ : Fin n => (0 : Fin 2)) (fun _ => 0) (p : ℂ) +
    Matrix.single (fun _ => (1 : Fin 2)) (fun _ => 1) ((1 - p : ℝ) : ℂ),
    pair_state n _ _ p hp hp1, ?_⟩
  rw [pair_lorentz n hn p]
  apply congrArg (fun t : ℝ => (t : ℂ))
  dsimp [p]
  nlinarith



private lemma state_range_bound (n : ℕ) (hn : Odd n)
    (A : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ) (hA : IsState A) :
    ∃ x : ℝ, x ∈ Set.Icc (-1 / 2 : ℝ) 0 ∧ lorentz A = (x : ℂ) := by
  let E := epsN n
  have hEt : Eᵀ = -E := (epsN_odd n hn).1
  have hEE : E * E = -1 := (epsN_odd n hn).2
  have hEh : Eᴴ = -E := (epsN_conjTranspose n).trans hEt
  have hEu : Eᴴ * E = 1 := by rw [hEh, neg_mul, hEE, neg_neg]
  let B := E * Aᵀ * Eᴴ
  have hB : B.PosSemidef := hA.1.transpose.mul_mul_conjTranspose_same E
  have htB : B.trace = 1 := by
    dsimp [B]
    rw [trace_mul_cycle, hEu, one_mul, trace_transpose, hA.2]
  have hAB : (1 - A - B).PosSemidef := breuer_psd E A hEt hEu hA.1 hA.2
  have hb := overlap_bound A B hA.1 hB hA.2 htB hAB
  have hc := trace_mul_real A B hA.1.1 hB.1
  have hcyc : lorentz A = (A * E * Aᵀ * E).trace := by
    unfold lorentz
    change (Aᵀ * E * A * E).trace = _
    calc
      _ = ((Aᵀ * E) * (A * E)).trace := by simp only [Matrix.mul_assoc]
      _ = ((A * E) * (Aᵀ * E)).trace := trace_mul_comm _ _
      _ = _ := by simp only [Matrix.mul_assoc]
  have hlor : lorentz A = -(A * B).trace := by
    rw [hcyc]
    simp only [B, hEh, Matrix.mul_neg, trace_neg, neg_neg, Matrix.mul_assoc]
  refine ⟨-(A * B).trace.re, ⟨by linarith [hb.2], by linarith [hb.1]⟩, ?_⟩
  rw [hlor, Complex.ofReal_neg, hc]

theorem result : claim := by
  intro n hn
  ext z
  constructor
  · rintro ⟨A, hA, rfl⟩
    obtain ⟨x, hx, heq⟩ := state_range_bound n hn A hA
    exact ⟨x, hx, heq.symm⟩
  · rintro ⟨x, hx, rfl⟩
    exact attained n hn x hx


end D5.S3.Quantum.Entanglement.Lorentz.ChengChenLorentzInvariantRange
