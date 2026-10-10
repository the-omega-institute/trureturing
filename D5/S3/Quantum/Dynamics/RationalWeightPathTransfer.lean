/- GID: D5/S3/Quantum/Dynamics/RationalWeightPathTransfer
   generality: G
   mirror-B: D5/B/S3/Quantum/Dynamics/RationalWeightPathTransfer
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Rational positive weights forbid perfect state transfer at time pi on paths with 2^k + 1 vertices. -/

/-
proof_shape: result: content; escape_witness:
D5/S3/Quantum/Dynamics/ParityNodeDividedDifference.evenOdd_dividedDifference_twoAdicUnit (the
preregistered 2-adic unit lemma), together with pst_parity_classes (integer spectral classes
with P * Σ_{i ∈ A} 1 / ∏_{j ≠ i} (z i - z j) = 1 / 2) and reversal_columns (reversal form of
the transfer unitary, whose second component persymmetric_weights is the mirror symmetry of the
weights); all three lie on the live path, through the private step no_transfer_last_first, to
the valuation contradiction 2 v_2(Q) = -1.
proof_shape: reversal_columns: content (column induction for a unitary commuting with the path
Hamiltonian); consumer: persymmetric_weights and
D5/S3/Quantum/Dynamics/PathMiddleVertexMoments (private step propagator_eq_reversal).
proof_shape: persymmetric_weights: bind-only (second component of reversal_columns); consumer:
no_transfer_last_first.
proof_shape: pst_parity_classes: content (moment identity, phase alignment, sign classes);
consumer: no_transfer_last_first.
Public helpers; PathMiddleVertexMoments and OddPathRationalWeightTransfer abbreviate the modules
D5/S3/Quantum/Dynamics/PathMiddleVertexMoments and
D5/S3/Quantum/Dynamics/OddPathRationalWeightTransfer:
proof_shape: mul_prod_sub_eq_of_moments: content (nodal polynomial evaluated against the
moments); consumer: pst_parity_classes, PathMiddleVertexMoments.middle_vertex_weights.
proof_shape: pathHamiltonian_pow_apply_column: content (induction on the power); consumer:
no_transfer_last_first, PathMiddleVertexMoments.middle_vertex_weights,
OddPathRationalWeightTransfer.middle_moment_gram_det.
proof_shape: prod_eq_sq_of_rev: content (mirror pairing of a product); consumer:
no_transfer_last_first, PathMiddleVertexMoments.middle_vertex_weights.
proof_shape: hamiltonianPropagator_neg: bind-only; consumer: pst_phase, pst_parity_classes,
no_transfer_last_first, result, PathMiddleVertexMoments (propagator_eq_reversal),
OddPathRationalWeightTransfer (propagator_shift, result).
proof_shape: pathHamiltonian_transpose: bind-only; consumer: pathHamiltonian_isHermitian,
result, OddPathRationalWeightTransfer (middle_moment_gram_det, result).
proof_shape: pathHamiltonian_isHermitian: bind-only; consumer: no_transfer_last_first,
PathMiddleVertexMoments (propagator_eq_reversal, middle_vertex_moments).
proof_shape: spectral_pow_apply: bind-only; consumer: pst_parity_classes,
PathMiddleVertexMoments (middle_vertex_weights, middle_vertex_moments).
proof_shape: spectral_exp: bind-only; consumer: pst_phase, pst_column,
PathMiddleVertexMoments (eigenvector_rev, sum_phase_eq_trace).
proof_shape: exists_int_of_exp_eq_one: bind-only; consumer: exists_int_of_exp_eq_neg_one,
pst_parity_classes, PathMiddleVertexMoments.middle_vertex_weights.
proof_shape: exists_int_of_exp_eq_neg_one: bind-only; consumer: pst_parity_classes,
PathMiddleVertexMoments.middle_vertex_weights.
proof_shape: pst_column: bind-only; consumer: no_transfer_last_first,
PathMiddleVertexMoments (propagator_eq_reversal).
proof_shape: propagator_star_mul_self: bind-only; consumer: no_transfer_last_first,
PathMiddleVertexMoments (propagator_eq_reversal).
Private helpers:
proof_shape: no_transfer_last_first: content (escape witnesses as for result); consumer:
result.
proof_shape: pst_phase: content (equality case of the unit-vector pairing); consumer:
pst_parity_classes, pst_column.
proof_shape: choose_two_pow_sub_one_odd: content (Frobenius identity in (ZMod 2)[X]);
consumer: no_transfer_last_first.
proof_shape: pathHamiltonian_far: bind-only; consumer: pathHamiltonian_transpose,
pathHamiltonian_pow_apply_column, reversal_columns.
proof_shape: pathHamiltonian_up: bind-only; consumer: pathHamiltonian_transpose,
reversal_columns.
proof_shape: pathHamiltonian_down: bind-only; consumer: pathHamiltonian_transpose,
pathHamiltonian_pow_apply_column, reversal_columns.
proof_shape: eigenvector_row_sum: bind-only; consumer: pst_phase, pst_parity_classes,
pst_column.
proof_shape: normSq_exp_pi_mul_I: bind-only; consumer: pst_phase.
admission_basis: escape-witness (partial progress on the rational weights conjecture of
arXiv:1708.03283, research line #14293; the sizes other than 2^k + 1 are not settled by the
source's proposition or by this module).
Direct frozen dependencies:
  D5/S3/Quantum/Dynamics/ProjectionProbabilityFlow.hamiltonianPropagator
  statement_id sha256:cda9b54324a60c3d19d82ae43fd312bec7fd42bc7d2748ad663e34115d863ceb.
  D5/S3/Quantum/Dynamics/ProjectionProbabilityFlow.hamiltonianGenerator
  statement_id sha256:4c0ebd78b0aa0a551d6207706ae2d39b87a3d18687dc8dcb29e00bd4e58a735a.
  (module pin sha256:63542644e2162329887997e930a818684048961f5b1728a2394256c633e8e084 in
  Golden/Frozen/state.)
  D5/S3/Quantum/Dynamics/ParityNodeDividedDifference.evenOdd_dividedDifference_twoAdicUnit
  statement_id sha256:d9f99e39b10db5978f5d3f2ed162aff7c7d97af3f4381b1950ab467b7dbf5cf0.
utility: none; no declaration is a bounded enumeration, checker, numeric reduction or
certified instance: the claim quantifies over every k >= 1 and all real weights and potentials.
-/

import D5.S3.Quantum.Dynamics.ParityNodeDividedDifference
import D5.S3.Quantum.Dynamics.ProjectionProbabilityFlow
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Exponential

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Quantum.Dynamics.RationalWeightPathTransfer

open Matrix Polynomial Finset Complex
open D5.S3.Quantum.Dynamics.ProjectionProbabilityFlow

/-- The Hamiltonian of a weighted path on the vertices `0, …, m`: the potential `q i` on the
diagonal and the weight `r t` on the edge `{t, t + 1}`. -/
def pathHamiltonian {m : ℕ} (r : Fin m → ℝ) (q : Fin (m + 1) → ℝ) :
    Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ :=
  Matrix.of fun i j =>
    if i = j then (q i : ℂ)
    else if h : (i : ℕ) + 1 = j then (r ⟨i, by have := j.isLt; omega⟩ : ℂ)
    else if h' : (j : ℕ) + 1 = i then (r ⟨j, by have := i.isLt; omega⟩ : ℂ)
    else 0

/-- Perfect state transfer from vertex `a` to vertex `b` at time `t`:
`|e_a^T e^{i t H} e_b|^2 = 1`, where `e^{i t H} = hamiltonianPropagator H (-t)`. -/
def HasPST {V : Type*} [Fintype V] [DecidableEq V] (H : Matrix V V ℂ) (t : ℝ) (a b : V) :
    Prop :=
  Complex.normSq (hamiltonianPropagator H (-t) a b) = 1

/-- The repository propagator `exp (-i s H)` at `s = -t` is the matrix exponential
`exp ((t * i) • H)`. -/
theorem hamiltonianPropagator_neg {V : Type*} [Fintype V] [DecidableEq V]
    (H : Matrix V V ℂ) (t : ℝ) :
    hamiltonianPropagator H (-t) = NormedSpace.exp (((t : ℂ) * I) • H) := by
  unfold hamiltonianPropagator hamiltonianGenerator
  congr 1
  ext i j
  simp [Matrix.smul_apply, Complex.real_smul]
  ring

section Path

variable {m : ℕ} (r : Fin m → ℝ) (q : Fin (m + 1) → ℝ)

private theorem pathHamiltonian_far (i j : Fin (m + 1)) (h1 : (i : ℕ) ≠ j) (h2 : (i : ℕ) + 1 ≠ j)
    (h3 : (j : ℕ) + 1 ≠ i) : pathHamiltonian r q i j = 0 := by
  simp only [pathHamiltonian, of_apply, if_neg (fun h : i = j => h1 (congrArg Fin.val h)),
    dif_neg h2, dif_neg h3]

private theorem pathHamiltonian_up (i j : Fin (m + 1)) (t : Fin m) (hi : (i : ℕ) = t)
    (hj : (j : ℕ) = t + 1) : pathHamiltonian r q i j = r t := by
  have hij : i ≠ j := fun h => by rw [h] at hi; omega
  simp only [pathHamiltonian, of_apply, if_neg hij, dif_pos (show (i : ℕ) + 1 = j by omega)]
  congr 2
  exact Fin.ext hi

private theorem pathHamiltonian_down (i j : Fin (m + 1)) (t : Fin m) (hj : (j : ℕ) = t)
    (hi : (i : ℕ) = t + 1) : pathHamiltonian r q i j = r t := by
  have hij : i ≠ j := fun h => by rw [h] at hi; omega
  simp only [pathHamiltonian, of_apply, if_neg hij, dif_neg (show (i : ℕ) + 1 ≠ j by omega),
    dif_pos (show (j : ℕ) + 1 = i by omega)]
  congr 2
  exact Fin.ext hj

theorem pathHamiltonian_transpose : (pathHamiltonian r q)ᵀ = pathHamiltonian r q := by
  ext i j
  rw [transpose_apply]
  by_cases h1 : i = j
  · rw [h1]
  by_cases h2 : (i : ℕ) + 1 = j
  · rw [pathHamiltonian_up r q i j ⟨i, by have := j.isLt; omega⟩ rfl (by simp [h2]),
      pathHamiltonian_down r q j i ⟨i, by have := j.isLt; omega⟩ rfl (by simp [h2])]
  by_cases h3 : (j : ℕ) + 1 = i
  · rw [pathHamiltonian_down r q i j ⟨j, by have := i.isLt; omega⟩ rfl (by simp [h3]),
      pathHamiltonian_up r q j i ⟨j, by have := i.isLt; omega⟩ rfl (by simp [h3])]
  have h1' : (i : ℕ) ≠ j := fun h => h1 (Fin.ext h)
  rw [pathHamiltonian_far r q i j h1' h2 h3, pathHamiltonian_far r q j i (Ne.symm h1') h3 h2]

theorem pathHamiltonian_isHermitian : (pathHamiltonian r q).IsHermitian := by
  have hreal : (pathHamiltonian r q).map star = pathHamiltonian r q := by
    ext i j
    simp only [map_apply, pathHamiltonian, of_apply]
    split_ifs <;> simp
  change (pathHamiltonian r q)ᴴ = pathHamiltonian r q
  rw [conjTranspose, pathHamiltonian_transpose, hreal]

/-- The column of `H ^ p` at the vertex `v` vanishes beyond distance `p` from `v`, and at the
vertex `v + p` it is the product of the `p` edge weights between `v` and `v + p`. -/
theorem pathHamiltonian_pow_apply_column (v : Fin (m + 1)) (p : ℕ) :
    ∀ i : Fin (m + 1),
      ((v : ℕ) + p < i ∨ (i : ℕ) + p < v → (pathHamiltonian r q ^ p) i v = 0) ∧
        ((i : ℕ) = v + p → (pathHamiltonian r q ^ p) i v =
          ∏ t ∈ range p, (if h : (v : ℕ) + t < m then (r ⟨v + t, h⟩ : ℂ) else 0)) := by
  induction p with
  | zero =>
    intro i
    refine ⟨fun h => ?_, fun h => ?_⟩
    · rw [pow_zero, one_apply_ne (fun h' => by rw [h'] at h; omega)]
    · have : i = v := Fin.ext h
      subst this
      simp
  | succ p ih =>
    intro i
    refine ⟨fun h => ?_, fun h => ?_⟩
    · rw [pow_succ', mul_apply]
      refine Finset.sum_eq_zero fun l _ => ?_
      by_cases hl : (v : ℕ) + p < l ∨ (l : ℕ) + p < v
      · rw [(ih l).1 hl, mul_zero]
      · rw [pathHamiltonian_far r q i l (by omega) (by omega) (by omega), zero_mul]
    · have hp : (v : ℕ) + p < m := by have := i.isLt; omega
      rw [pow_succ', mul_apply, Finset.sum_eq_single ⟨v + p, by omega⟩]
      · rw [(ih ⟨v + p, by omega⟩).2 rfl, prod_range_succ, dif_pos hp,
          pathHamiltonian_down r q i ⟨v + p, by omega⟩ ⟨v + p, hp⟩ rfl h]
        ring
      · intro l _ hl
        by_cases hlp : (v : ℕ) + p < l ∨ (l : ℕ) + p < v
        · rw [(ih l).1 hlp, mul_zero]
        · have hlp' : (l : ℕ) ≠ v + p := fun h' => hl (Fin.ext h')
          rw [pathHamiltonian_far r q i l (by omega) (by omega) (by omega), zero_mul]
      · simp

end Path

section Spectral

variable {V : Type*} [Fintype V] [DecidableEq V] {H : Matrix V V ℂ} (hH : H.IsHermitian)

/-- Entries of the powers of a Hermitian matrix in its orthonormal eigenbasis. -/
theorem spectral_pow_apply (p : ℕ) (a b : V) :
    (H ^ p) a b = ∑ k, (hH.eigenvectorUnitary : Matrix V V ℂ) a k *
      ((hH.eigenvalues k : ℂ) ^ p *
        starRingEnd ℂ ((hH.eigenvectorUnitary : Matrix V V ℂ) b k)) := by
  have h : H ^ p = (hH.eigenvectorUnitary : Matrix V V ℂ) *
      diagonal (fun k => (hH.eigenvalues k : ℂ) ^ p) *
        star (hH.eigenvectorUnitary : Matrix V V ℂ) := by
    conv_lhs => rw [hH.spectral_theorem]
    rw [← map_pow, Unitary.conjStarAlgAut_apply, diagonal_pow]
    congr 2
  rw [h, mul_apply]
  simp only [mul_diagonal, star_apply, mul_assoc, Complex.star_def]

/-- The propagator `exp (s • H)` of a Hermitian matrix in its orthonormal eigenbasis. -/
theorem spectral_exp (s : ℂ) :
    NormedSpace.exp (s • H) = (hH.eigenvectorUnitary : Matrix V V ℂ) *
      diagonal (fun k => Complex.exp (s * hH.eigenvalues k)) *
        star (hH.eigenvectorUnitary : Matrix V V ℂ) := by
  set W : Matrix V V ℂ := ↑hH.eigenvectorUnitary with hW
  have hWinv : W⁻¹ = star W := Matrix.inv_eq_left_inv (Unitary.coe_star_mul_self _)
  have hs : s • H = W * diagonal (s • fun k => (hH.eigenvalues k : ℂ)) * W⁻¹ := by
    conv_lhs => rw [hH.spectral_theorem]
    rw [Unitary.conjStarAlgAut_apply, hWinv, diagonal_smul, Matrix.mul_smul, Matrix.smul_mul]
    rfl
  have hexp : NormedSpace.exp (s • fun k => (hH.eigenvalues k : ℂ)) =
      fun k => Complex.exp (s * hH.eigenvalues k) := by
    funext k
    rw [Pi.coe_exp, Pi.smul_apply, smul_eq_mul, ← Complex.exp_eq_exp_ℂ]
  rw [hs, Matrix.exp_conj _ _ Unitary.isUnit_coe, Matrix.exp_diagonal, hWinv, hexp]

/-- The rows of the eigenvector matrix are orthonormal. -/
private theorem eigenvector_row_sum (a b : V) :
    ∑ k, (hH.eigenvectorUnitary : Matrix V V ℂ) a k *
      starRingEnd ℂ ((hH.eigenvectorUnitary : Matrix V V ℂ) b k) = if a = b then 1 else 0 := by
  have h := congrFun (congrFun (Unitary.coe_mul_star_self hH.eigenvectorUnitary) a) b
  rw [Unitary.coe_star, mul_apply, one_apply] at h
  simpa [star_apply, Complex.star_def] using h

private theorem normSq_exp_pi_mul_I (x : ℝ) : Complex.normSq (Complex.exp ((Real.pi : ℂ) * I * x)) = 1 := by
  rw [show (Real.pi : ℂ) * I * x = ((Real.pi * x : ℝ) : ℂ) * I by push_cast; ring,
    Complex.normSq_eq_norm_sq, Complex.norm_exp_ofReal_mul_I, one_pow]

/-- Perfect state transfer at time `π` from `a` to `b` aligns, eigenvector by eigenvector, the
phase-rotated `b`-entries with the `a`-entries. -/
private theorem pst_phase (a b : V) (hpst : HasPST H Real.pi a b) (k : V) :
    Complex.exp ((Real.pi : ℂ) * I * hH.eigenvalues k) *
        starRingEnd ℂ ((hH.eigenvectorUnitary : Matrix V V ℂ) b k) =
      NormedSpace.exp (((Real.pi : ℂ) * I) • H) a b *
        starRingEnd ℂ ((hH.eigenvectorUnitary : Matrix V V ℂ) a k) := by
  set W : Matrix V V ℂ := ↑hH.eigenvectorUnitary with hW
  set γ := NormedSpace.exp (((Real.pi : ℂ) * I) • H) a b with hγdef
  have hγ : Complex.normSq γ = 1 := by
    rw [hγdef, ← hamiltonianPropagator_neg]
    exact hpst
  let E : V → ℂ := fun k => Complex.exp ((Real.pi : ℂ) * I * hH.eigenvalues k)
  let x : V → ℂ := fun k => starRingEnd ℂ (W a k)
  let y : V → ℂ := fun k => E k * starRingEnd ℂ (W b k)
  have hγsum : γ = ∑ k, W a k * (E k * starRingEnd ℂ (W b k)) := by
    rw [hγdef, spectral_exp hH, mul_apply]
    simp only [mul_diagonal, star_apply, mul_assoc, Complex.star_def, E]
    rfl
  have hrow : ∀ c : V, ∑ k, Complex.normSq (W c k) = 1 := by
    intro c
    have h := eigenvector_row_sum hH c c
    rw [if_pos rfl] at h
    simp only [Complex.mul_conj] at h
    exact_mod_cast h
  have hx : ∑ k, Complex.normSq (x k) = 1 := by
    simp only [x, Complex.normSq_conj]
    exact hrow a
  have hy : ∑ k, Complex.normSq (y k) = 1 := by
    simp only [y, E, Complex.normSq_mul, Complex.normSq_conj, normSq_exp_pi_mul_I, one_mul]
    exact hrow b
  have hcross : ∑ k, y k * starRingEnd ℂ (x k) = γ := by
    rw [hγsum]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [x, y, Complex.conj_conj]
    ring
  have hzero : ∑ k, Complex.normSq (y k - γ * x k) = 0 := by
    have hgen : ∀ u v g : ℂ, Complex.normSq (u - g * v) =
        Complex.normSq u + Complex.normSq g * Complex.normSq v -
          2 * (starRingEnd ℂ g * (u * starRingEnd ℂ v)).re := by
      intro u v g
      rw [Complex.normSq_sub, Complex.normSq_mul, map_mul,
        show u * (starRingEnd ℂ g * starRingEnd ℂ v) = starRingEnd ℂ g * (u * starRingEnd ℂ v) by
          ring]
    rw [Finset.sum_congr rfl fun k _ => hgen (y k) (x k) γ, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      ← Complex.re_sum, ← Finset.mul_sum, hcross, hx, hy, ← Complex.normSq_eq_conj_mul_self,
      Complex.ofReal_re, hγ]
    norm_num
  have hk := (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => Complex.normSq_nonneg _)).mp
    hzero k (mem_univ k)
  rw [Complex.normSq_eq_zero, sub_eq_zero] at hk
  exact hk

end Spectral

/-- **Nodal extraction from moments.** If the moments `Σ_{j ∈ S} c j * x j ^ p` of a family
indexed by a finite set `S` of `n + 1` points vanish for `p < n` and equal `P` for `p = n`, then
`c k * ∏_{l ∈ S, l ≠ k} (x k - x l) = P` for every `k ∈ S`. -/
theorem mul_prod_sub_eq_of_moments {ι : Type*} [DecidableEq ι] (S : Finset ι) (c x : ι → ℂ)
    (n : ℕ) (hS : S.card = n + 1) (P : ℂ)
    (hmom : ∀ p ≤ n, ∑ j ∈ S, c j * x j ^ p = if p = n then P else 0) (k : ι) (hk : k ∈ S) :
    c k * ∏ l ∈ S.erase k, (x k - x l) = P := by
  set f : ℂ[X] := ∏ l ∈ S.erase k, (X - C (x l)) with hf
  have hfm : f.Monic := monic_prod_of_monic _ _ fun l _ => monic_X_sub_C _
  have hfdeg : f.natDegree = n := by
    rw [hf, natDegree_prod_of_monic _ _ fun l _ => monic_X_sub_C _,
      Finset.sum_congr rfl fun l _ => natDegree_X_sub_C _]
    simp [Finset.card_erase_of_mem hk, hS]
  have hsum : ∑ j ∈ S, c j * f.eval (x j) = P := by
    have h1 : ∀ j, c j * f.eval (x j) = ∑ p ∈ range (n + 1), f.coeff p * (c j * x j ^ p) := by
      intro j
      rw [eval_eq_sum_range' (by omega : f.natDegree < n + 1), Finset.mul_sum]
      exact Finset.sum_congr rfl fun p _ => by ring
    simp_rw [h1]
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum]
    have h2 : ∀ p ∈ range (n + 1), f.coeff p * ∑ j ∈ S, c j * x j ^ p =
        if p = n then f.coeff p * P else 0 := by
      intro p hp
      rw [hmom p (by have := Finset.mem_range.mp hp; omega)]
      split_ifs <;> simp
    rw [Finset.sum_congr rfl h2, Finset.sum_ite_eq', if_pos (Finset.mem_range.mpr (by omega)),
      show f.coeff n = 1 by rw [← hfdeg]; exact hfm.coeff_natDegree, one_mul]
  have hsingle : ∑ j ∈ S, c j * f.eval (x j) = c k * ∏ l ∈ S.erase k, (x k - x l) := by
    rw [Finset.sum_eq_single_of_mem k hk]
    · rw [hf, eval_prod]
      simp only [eval_sub, eval_X, eval_C]
    · intro j hj hjk
      rw [hf, eval_prod, Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hjk, hj⟩) (by simp),
        mul_zero]
  rw [← hsingle, hsum]

section Classes

variable {V : Type*} [Fintype V] [DecidableEq V] {H : Matrix V V ℂ} (hH : H.IsHermitian)

theorem exists_int_of_exp_eq_one {θ : ℝ} (h : Complex.exp ((Real.pi : ℂ) * I * θ) = 1) :
    ∃ n : ℤ, θ = 2 * n := by
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp h
  refine ⟨n, ?_⟩
  have hpi : (Real.pi : ℂ) * I ≠ 0 :=
    mul_ne_zero (ofReal_ne_zero.mpr Real.pi_ne_zero) I_ne_zero
  have h2 : (θ : ℂ) = 2 * n := mul_left_cancel₀ hpi (by rw [hn]; ring)
  exact_mod_cast h2

theorem exists_int_of_exp_eq_neg_one {θ : ℝ} (h : Complex.exp ((Real.pi : ℂ) * I * θ) = -1) :
    ∃ n : ℤ, θ = 2 * n + 1 := by
  have h1 : Complex.exp ((Real.pi : ℂ) * I * ((θ - 1 : ℝ) : ℂ)) = 1 := by
    rw [show (Real.pi : ℂ) * I * ((θ - 1 : ℝ) : ℂ) = (Real.pi : ℂ) * I * θ - Real.pi * I by
        push_cast; ring, Complex.exp_sub, h, Complex.exp_pi_mul_I]
    norm_num
  obtain ⟨n, hn⟩ := exists_int_of_exp_eq_one h1
  exact ⟨n, by linarith⟩

include hH in
/-- **Spectral parity classes.** Let `H` be Hermitian on `m + 1` sites whose `(a, b)` entries of
`H ^ p` vanish for `p < m` and equal `P ≠ 0` for `p = m`. If `H` has perfect state transfer from
`a` to `b` at time `π`, then its eigenvalues are integers up to a common shift, split into an even
class `A` and an odd class, and `P · Σ_{i ∈ A} 1 / ∏_{j ≠ i} (z i - z j) = 1 / 2`. -/
theorem pst_parity_classes (a b : V) (hab : a ≠ b) (m : ℕ) (hm : Fintype.card V = m + 1)
    (P : ℝ) (hP : P ≠ 0) (hmom : ∀ p ≤ m, (H ^ p) a b = if p = m then (P : ℂ) else 0)
    (hpst : HasPST H Real.pi a b) :
    ∃ (z : V → ℤ) (A : Finset V), Function.Injective z ∧ A.Nonempty ∧ A ≠ univ ∧
      (∀ i ∈ A, Even (z i)) ∧ (∀ i, i ∉ A → Odd (z i)) ∧
      P * ∑ i ∈ A, (∏ j ∈ univ.erase i, ((z i - z j : ℤ) : ℝ))⁻¹ = 1 / 2 := by
  set W : Matrix V V ℂ := ↑hH.eigenvectorUnitary with hW
  set Λ := hH.eigenvalues with hΛ
  set γ := NormedSpace.exp (((Real.pi : ℂ) * I) • H) a b with hγdef
  have hγ : Complex.normSq γ = 1 := by
    rw [hγdef, ← hamiltonianPropagator_neg]
    exact hpst
  have hγ0 : γ ≠ 0 := fun h => by rw [h, map_zero] at hγ; exact zero_ne_one hγ
  have hm1 : 1 ≤ m := by
    by_contra h0
    exact hab (Fintype.card_le_one_iff.mp (by omega) a b)
  let c : V → ℂ := fun k => W a k * starRingEnd ℂ (W b k)
  have hmomc : ∀ p ≤ m, ∑ k, c k * (Λ k : ℂ) ^ p = if p = m then (P : ℂ) else 0 := by
    intro p hp
    rw [← hmom p hp, spectral_pow_apply hH]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [c]
    ring
  have hcD : ∀ k, c k * ∏ l ∈ univ.erase k, ((Λ k : ℂ) - Λ l) = P := fun k =>
    mul_prod_sub_eq_of_moments univ c (fun l => (Λ l : ℂ)) m (by rw [Finset.card_univ, hm]) P
      (fun p hp => hmomc p hp) k (mem_univ k)
  have hDcast : ∀ k, ∏ l ∈ univ.erase k, ((Λ k : ℂ) - Λ l) =
      ((∏ l ∈ univ.erase k, (Λ k - Λ l) : ℝ) : ℂ) := by
    intro k
    push_cast
    rfl
  have hDne : ∀ k, ∏ l ∈ univ.erase k, (Λ k - Λ l) ≠ 0 := by
    intro k h0
    have h := hcD k
    rw [hDcast, h0, ofReal_zero, mul_zero] at h
    exact hP (by exact_mod_cast h.symm)
  have hΛinj : Function.Injective Λ := by
    intro k l hkl
    by_contra hne
    exact hDne k (Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨Ne.symm hne, mem_univ l⟩)
      (by rw [hkl, sub_self]))
  let ρ : V → ℝ := fun k => P / ∏ l ∈ univ.erase k, (Λ k - Λ l)
  have hcρ : ∀ k, c k = (ρ k : ℂ) := by
    intro k
    have hD' : ((∏ l ∈ univ.erase k, (Λ k - Λ l) : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr (hDne k)
    simp only [ρ]
    rw [ofReal_div, eq_div_iff hD', ← hDcast]
    exact hcD k
  have hρ0 : ∀ k, ρ k ≠ 0 := fun k => div_ne_zero hP (hDne k)
  have hphase := pst_phase hH a b hpst
  let w : V → ℝ := fun k => Complex.normSq (W a k)
  have hEρ : ∀ k, Complex.exp ((Real.pi : ℂ) * I * Λ k) * (ρ k : ℂ) = γ * (w k : ℂ) := by
    intro k
    rw [← hcρ k]
    simp only [c, w]
    calc Complex.exp ((Real.pi : ℂ) * I * Λ k) * (W a k * starRingEnd ℂ (W b k))
        = W a k * (Complex.exp ((Real.pi : ℂ) * I * Λ k) * starRingEnd ℂ (W b k)) := by ring
      _ = W a k * (γ * starRingEnd ℂ (W a k)) := by rw [hphase k]
      _ = γ * (W a k * starRingEnd ℂ (W a k)) := by ring
      _ = γ * (Complex.normSq (W a k) : ℂ) := by rw [Complex.mul_conj]
  have hnormE : ∀ k, ‖Complex.exp ((Real.pi : ℂ) * I * Λ k)‖ = 1 := by
    intro k
    rw [show (Real.pi : ℂ) * I * Λ k = ((Real.pi * Λ k : ℝ) : ℂ) * I by push_cast; ring]
    exact Complex.norm_exp_ofReal_mul_I _
  have hnormγ : ‖γ‖ = 1 := by
    have h2 : ‖γ‖ ^ 2 = 1 := by rw [← Complex.normSq_eq_norm_sq]; exact hγ
    nlinarith [norm_nonneg γ]
  have habsρ : ∀ k, |ρ k| = w k := by
    intro k
    have h := congrArg norm (hEρ k)
    rw [norm_mul, norm_mul, hnormE, hnormγ, one_mul, one_mul, Complex.norm_real,
      Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (Complex.normSq_nonneg _)] at h
    exact h
  have hw1 : ∑ k, w k = 1 := by
    have h := eigenvector_row_sum hH a a
    rw [if_pos rfl] at h
    simp only [Complex.mul_conj] at h
    exact_mod_cast h
  have hρsum : ∑ k, ρ k = 0 := by
    have h := hmomc 0 (Nat.zero_le _)
    rw [if_neg (by omega)] at h
    simp only [pow_zero, mul_one, hcρ] at h
    exact_mod_cast h
  set A : Finset V := univ.filter (fun k => 0 < ρ k) with hA
  have hAsum : ∑ k ∈ A, ρ k = 1 / 2 := by
    have h1 : ∑ k, (ρ k + |ρ k|) = 2 * ∑ k ∈ A, ρ k := by
      rw [hA, Finset.sum_filter, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      split_ifs with h
      · rw [abs_of_pos h]; ring
      · rw [abs_of_nonpos (not_lt.mp h)]; ring
    have h2 : ∑ k, (ρ k + |ρ k|) = 1 := by
      rw [Finset.sum_add_distrib, hρsum, zero_add]
      simp only [habsρ]
      exact hw1
    linarith
  have hEA : ∀ k ∈ A, Complex.exp ((Real.pi : ℂ) * I * Λ k) = γ := by
    intro k hk
    have hpos : 0 < ρ k := (Finset.mem_filter.mp hk).2
    have h := hEρ k
    rw [← habsρ k, abs_of_pos hpos] at h
    exact mul_right_cancel₀ (ofReal_ne_zero.mpr (hρ0 k)) h
  have hEB : ∀ k, k ∉ A → Complex.exp ((Real.pi : ℂ) * I * Λ k) = -γ := by
    intro k hk
    have hneg : ρ k < 0 := lt_of_le_of_ne
      (not_lt.mp fun h => hk (Finset.mem_filter.mpr ⟨mem_univ k, h⟩)) (hρ0 k)
    have h := hEρ k
    rw [← habsρ k, abs_of_neg hneg] at h
    refine mul_right_cancel₀ (ofReal_ne_zero.mpr (hρ0 k)) ?_
    rw [h]
    push_cast
    ring
  have hAne : A.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h
    rw [h, Finset.sum_empty] at hAsum
    norm_num at hAsum
  have hAuniv : A ≠ univ := by
    intro h
    rw [h, hρsum] at hAsum
    norm_num at hAsum
  obtain ⟨k0, hk0⟩ := hAne
  have hz : ∀ k, ∃ n : ℤ, Λ k - Λ k0 = n ∧ (k ∈ A → Even n) ∧ (k ∉ A → Odd n) := by
    intro k
    have hdiff : Complex.exp ((Real.pi : ℂ) * I * ((Λ k - Λ k0 : ℝ) : ℂ)) =
        Complex.exp ((Real.pi : ℂ) * I * Λ k) / Complex.exp ((Real.pi : ℂ) * I * Λ k0) := by
      rw [← Complex.exp_sub]
      congr 1
      push_cast
      ring
    by_cases hk : k ∈ A
    · rw [hEA k hk, hEA k0 hk0, div_self hγ0] at hdiff
      obtain ⟨n, hn⟩ := exists_int_of_exp_eq_one hdiff
      exact ⟨2 * n, by rw [hn]; push_cast; ring, fun _ => even_two_mul n, fun h => absurd hk h⟩
    · rw [hEB k hk, hEA k0 hk0, neg_div, div_self hγ0] at hdiff
      obtain ⟨n, hn⟩ := exists_int_of_exp_eq_neg_one hdiff
      exact ⟨2 * n + 1, by rw [hn]; push_cast; ring, fun h => absurd h hk,
        fun _ => odd_two_mul_add_one n⟩
  choose z hzΛ hzA hzB using hz
  refine ⟨z, A, ?_, ⟨k0, hk0⟩, hAuniv, hzA, hzB, ?_⟩
  · intro k l hkl
    apply hΛinj
    have h1 := hzΛ k
    have h2 := hzΛ l
    rw [hkl] at h1
    linarith
  · rw [← hAsum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [ρ]
    rw [div_eq_mul_inv]
    congr 2
    refine Finset.prod_congr rfl fun l _ => ?_
    push_cast
    rw [← hzΛ k, ← hzΛ l]
    ring

include hH in
/-- After perfect state transfer from `a` to `b` at time `π`, the `b`-th column of the
propagator is a multiple of the `a`-th basis vector. -/
theorem pst_column (a b : V) (hpst : HasPST H Real.pi a b) (x : V) :
    NormedSpace.exp (((Real.pi : ℂ) * I) • H) x b =
      if x = a then NormedSpace.exp (((Real.pi : ℂ) * I) • H) a b else 0 := by
  set γ := NormedSpace.exp (((Real.pi : ℂ) * I) • H) a b with hγdef
  have hphase := pst_phase hH a b hpst
  rw [spectral_exp hH, mul_apply]
  simp only [mul_diagonal, star_apply, Complex.star_def]
  calc ∑ k, (hH.eigenvectorUnitary : Matrix V V ℂ) x k *
        Complex.exp ((Real.pi : ℂ) * I * hH.eigenvalues k) *
          starRingEnd ℂ ((hH.eigenvectorUnitary : Matrix V V ℂ) b k)
      = ∑ k, γ * ((hH.eigenvectorUnitary : Matrix V V ℂ) x k *
          starRingEnd ℂ ((hH.eigenvectorUnitary : Matrix V V ℂ) a k)) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [mul_assoc, hphase k]
        ring
    _ = γ * (if x = a then 1 else 0) := by rw [← Finset.mul_sum, eigenvector_row_sum hH]
    _ = if x = a then γ else 0 := by split_ifs <;> simp

include hH in
/-- The propagator at time `π` is unitary. -/
theorem propagator_star_mul_self :
    star (NormedSpace.exp (((Real.pi : ℂ) * I) • H)) *
      NormedSpace.exp (((Real.pi : ℂ) * I) • H) = 1 := by
  have hs : star (((Real.pi : ℂ) * I) • H) = -(((Real.pi : ℂ) * I) • H) := by
    rw [star_eq_conjTranspose, conjTranspose_smul, hH.eq]
    simp [Complex.conj_ofReal]
  rw [star_eq_conjTranspose, ← Matrix.exp_conjTranspose, ← star_eq_conjTranspose, hs,
    Matrix.exp_neg]
  exact Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp (Matrix.isUnit_exp _))

end Classes

section Persymmetry

variable {m : ℕ} (r : Fin m → ℝ) (q : Fin (m + 1) → ℝ)

/-- **Reversal form of the transfer unitary.** If a unitary matrix commuting with the path
Hamiltonian sends the first basis vector to a unimodular multiple `γ` of the last one, then it
sends every basis vector to `γ` times its mirror image, and the edge weights are mirror
symmetric. -/
theorem reversal_columns (hr : ∀ t, 0 < r t) (U : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ)
    (hU : star U * U = 1) (hcomm : U * pathHamiltonian r q = pathHamiltonian r q * U) (γ : ℂ)
    (hγ : Complex.normSq γ = 1) (hcol : ∀ x, U x 0 = if x = Fin.last m then γ else 0) :
    (∀ i x : Fin (m + 1), U x i = if x = i.rev then γ else 0) ∧ ∀ t : Fin m, r t = r t.rev := by
  have hγ0 : γ ≠ 0 := fun h => by rw [h, map_zero] at hγ; exact zero_ne_one hγ
  have hUcol : ∀ i j : Fin (m + 1),
      ∑ x, starRingEnd ℂ (U x i) * U x j = if i = j then 1 else 0 := by
    intro i j
    have h := congrFun (congrFun hU i) j
    rw [mul_apply, one_apply] at h
    simpa [star_apply, Complex.star_def] using h
  have key : ∀ j ≤ m,
      (∀ i : Fin (m + 1), (i : ℕ) ≤ j → ∀ x, U x i = if x = i.rev then γ else 0) ∧
        (∀ t : Fin m, (t : ℕ) < j → r t = r t.rev) := by
    intro j
    induction j with
    | zero =>
      intro _
      refine ⟨fun i hi x => ?_, fun t ht => absurd ht (Nat.not_lt_zero _)⟩
      have hi0 : i = 0 := Fin.ext (by simp only [Fin.val_zero]; omega)
      rw [hi0, hcol, Fin.rev_zero]
    | succ j ih =>
      intro hj
      obtain ⟨ihU, ihr⟩ := ih (by omega)
      set jj : Fin (m + 1) := ⟨j, by omega⟩ with hjj
      set jn : Fin (m + 1) := ⟨j + 1, by omega⟩ with hjn
      set et : Fin m := ⟨j, by omega⟩ with het
      have hcolj : ∀ x, U x jj = if x = jj.rev then γ else 0 := ihU jj le_rfl
      have hret : r et ≠ 0 := (hr et).ne'
      have hretc : (r et : ℂ) ≠ 0 := ofReal_ne_zero.mpr hret
      have hstar : ∀ x : Fin (m + 1),
          (if (x.rev : ℕ) ≤ j then γ * pathHamiltonian r q x.rev jj else 0) + U x jn * (r et : ℂ) =
            pathHamiltonian r q x jj.rev * γ := by
        intro x
        have h := congrFun (congrFun hcomm x) jj
        rw [mul_apply, mul_apply] at h
        have hR : ∑ l, pathHamiltonian r q x l * U l jj = pathHamiltonian r q x jj.rev * γ := by
          rw [Finset.sum_eq_single jj.rev]
          · rw [hcolj, if_pos rfl]
          · intro l _ hl
            rw [hcolj, if_neg hl, mul_zero]
          · simp
        have hL : ∀ l, U x l * pathHamiltonian r q l jj =
            (if l = x.rev then (if (x.rev : ℕ) ≤ j then γ * pathHamiltonian r q x.rev jj else 0) else 0) +
              (if l = jn then U x jn * (r et : ℂ) else 0) := by
          intro l
          by_cases hl : (l : ℕ) ≤ j
          · have hljn : l ≠ jn := fun h => by rw [h] at hl; simp [hjn] at hl
            rw [ihU l hl x, if_neg hljn, add_zero]
            by_cases hxl : l = x.rev
            · subst hxl
              rw [Fin.rev_rev, if_pos rfl, if_pos rfl, if_pos hl]
            · have hxl' : x ≠ l.rev := fun h => hxl (by rw [h, Fin.rev_rev])
              rw [if_neg hxl', if_neg hxl, zero_mul]
          · by_cases hljn : l = jn
            · subst hljn
              rw [pathHamiltonian_down r q jn jj et rfl rfl, if_pos rfl]
              have hno : ¬ ((x.rev : ℕ) ≤ j ∧ jn = x.rev) := fun ⟨h1, h2⟩ => by
                rw [← h2] at h1
                simp [hjn] at h1
              have h0 : (if jn = x.rev then (if (x.rev : ℕ) ≤ j then γ * pathHamiltonian r q x.rev jj else 0)
                  else 0) = 0 := by
                split_ifs with h1 h2
                · exact absurd ⟨h2, h1⟩ hno
                · rfl
                · rfl
              rw [h0, zero_add]
            · have hl2 : j + 2 ≤ (l : ℕ) := by
                have : (l : ℕ) ≠ j + 1 := fun h => hljn (Fin.ext h)
                omega
              rw [pathHamiltonian_far r q l jj (by simp [hjj]; omega) (by simp [hjj]; omega)
                (by simp [hjj]; omega), mul_zero, if_neg hljn, add_zero]
              split_ifs with h1 h2
              · exact absurd (by rw [h1]; exact h2) hl
              · rfl
              · rfl
        rw [Finset.sum_congr rfl fun l _ => hL l, Finset.sum_add_distrib, Finset.sum_ite_eq',
          Finset.sum_ite_eq', if_pos (mem_univ _), if_pos (mem_univ _), hR] at h
        exact h
      have hjm : j < m := by omega
      have hvjj : (jj.rev : ℕ) = m - j := by simp [Fin.val_rev, hjj]
      have hvjn : (jn.rev : ℕ) = m - (j + 1) := by simp [Fin.val_rev, hjn]
      have hvet : (et.rev : ℕ) = m - (j + 1) := by simp [Fin.val_rev, het]
      -- the entry at the mirror vertex
      have ha : U jn.rev jn * (r et : ℂ) = (r et.rev : ℂ) * γ := by
        have h := hstar jn.rev
        rw [Fin.rev_rev, if_neg (by simp [hjn]), zero_add,
          pathHamiltonian_up r q jn.rev jj.rev et.rev (by rw [hvjn, hvet])
            (by rw [hvjj, hvet]; omega)] at h
        exact h
      -- all other entries of column `j + 1` vanish
      have hb : ∀ x, x ≠ jn.rev → x ≠ jj.rev → U x jn = 0 := by
        intro x hx1 hx2
        have hX1 : (x : ℕ) ≠ m - (j + 1) := fun h => hx1 (Fin.ext (by rw [h, hvjn]))
        have hX2 : (x : ℕ) ≠ m - j := fun h => hx2 (Fin.ext (by rw [h, hvjj]))
        have hxr : (x.rev : ℕ) = m - x := by simp [Fin.val_rev]
        have hxm := x.isLt
        have h := hstar x
        have hzero : U x jn * (r et : ℂ) = 0 := by
          rcases lt_or_gt_of_ne hX1 with hlt | hgt
          · rw [if_neg (by omega), zero_add,
              pathHamiltonian_far r q x jj.rev (by omega) (by omega) (by omega), zero_mul] at h
            exact h
          · rcases Nat.lt_or_ge (x : ℕ) (m - j + 2) with hlt2 | hge2
            · -- `x = m - j + 1`
              have hx' : (x : ℕ) = m - j + 1 := by omega
              have hj1 : 1 ≤ j := by omega
              set es : Fin m := ⟨j - 1, by omega⟩ with hes
              have hup : pathHamiltonian r q x.rev jj = r es := pathHamiltonian_up r q x.rev jj es
                (by rw [hxr, hes]; simp; omega) (by simp [hjj, hes]; omega)
              have hdown : pathHamiltonian r q x jj.rev = r es.rev := pathHamiltonian_down r q x jj.rev es.rev
                (by rw [hvjj]; simp [Fin.val_rev, hes]; omega)
                (by simp [Fin.val_rev, hes]; omega)
              have hsym := ihr es (by simp [hes]; omega)
              rw [if_pos (by omega), hup, hdown, ← hsym] at h
              linear_combination h
            · rw [if_pos (by omega),
                pathHamiltonian_far r q x.rev jj (by simp [hjj]; omega) (by simp [hjj]; omega)
                  (by simp [hjj]; omega),
                pathHamiltonian_far r q x jj.rev (by omega) (by omega) (by omega)] at h
              simpa using h
        exact (mul_eq_zero.mp hzero).resolve_right hretc
      -- orthogonality to column `j` kills the entry at `jj.rev`
      have hc : U jj.rev jn = 0 := by
        have h := hUcol jj jn
        rw [if_neg (fun h => by simp [hjj, hjn, Fin.ext_iff] at h)] at h
        rw [Finset.sum_eq_single jj.rev] at h
        · rw [hcolj, if_pos rfl] at h
          exact (mul_eq_zero.mp h).resolve_left ((_root_.map_ne_zero _).mpr hγ0)
        · intro x _ hx
          rw [hcolj, if_neg hx, map_zero, zero_mul]
        · simp
      -- the column has norm one
      have hd : Complex.normSq (U jn.rev jn) = 1 := by
        have h := hUcol jn jn
        rw [if_pos rfl, Finset.sum_eq_single jn.rev] at h
        · rw [← Complex.normSq_eq_conj_mul_self] at h
          exact_mod_cast h
        · intro x _ hx
          by_cases hx2 : x = jj.rev
          · rw [hx2, hc, mul_zero]
          · rw [hb x hx hx2, mul_zero]
        · simp
      have he : r et = r et.rev := by
        have h := congrArg Complex.normSq ha
        rw [Complex.normSq_mul, Complex.normSq_mul, hd, hγ, Complex.normSq_ofReal,
          Complex.normSq_ofReal, one_mul, mul_one] at h
        exact (mul_self_inj (hr et).le (hr et.rev).le).mp h
      have hf : U jn.rev jn = γ := by
        rw [← he, mul_comm (r et : ℂ)] at ha
        exact mul_right_cancel₀ hretc ha
      refine ⟨fun i hi x => ?_, fun t ht => ?_⟩
      · by_cases hij : (i : ℕ) ≤ j
        · exact ihU i hij x
        · have hi' : i = jn := Fin.ext (by simp [hjn]; omega)
          subst hi'
          by_cases hx1 : x = jn.rev
          · rw [hx1, if_pos rfl, hf]
          · rw [if_neg hx1]
            by_cases hx2 : x = jj.rev
            · rw [hx2, hc]
            · exact hb x hx1 hx2
      · by_cases htj : (t : ℕ) < j
        · exact ihr t htj
        · have ht' : t = et := Fin.ext (by simp [het]; omega)
          rw [ht']
          exact he
  exact ⟨fun i x => (key m le_rfl).1 i (Nat.lt_succ_iff.mp i.isLt) x,
    fun t => (key m le_rfl).2 t t.isLt⟩

/-- **Mirror symmetry of the weights.** If a unitary matrix commuting with the path Hamiltonian
sends the first basis vector to a unimodular multiple of the last one, then the edge weights are
mirror symmetric. -/
theorem persymmetric_weights (hr : ∀ t, 0 < r t) (U : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ)
    (hU : star U * U = 1) (hcomm : U * pathHamiltonian r q = pathHamiltonian r q * U) (γ : ℂ)
    (hγ : Complex.normSq γ = 1) (hcol : ∀ x, U x 0 = if x = Fin.last m then γ else 0) :
    ∀ t : Fin m, r t = r t.rev :=
  (reversal_columns r q hr U hU hcomm γ hγ hcol).2

end Persymmetry

/-- `C(2^K - 1, j)` is odd for every `j < 2^K`. -/
private theorem choose_two_pow_sub_one_odd (K j : ℕ) (hj : j < 2 ^ K) : Odd ((2 ^ K - 1).choose j) := by
  have hpos : 1 ≤ 2 ^ K := Nat.one_le_two_pow
  have hX : (X + 1 : (ZMod 2)[X]) ^ (2 ^ K - 1) = ∑ i ∈ range (2 ^ K), (X : (ZMod 2)[X]) ^ i := by
    have hne : (X + 1 : (ZMod 2)[X]) ≠ 0 := by simpa using X_add_C_ne_zero (1 : ZMod 2)
    apply mul_right_cancel₀ hne
    rw [← pow_succ, Nat.sub_add_cancel hpos, add_pow_char_pow, one_pow]
    have h := geom_sum_mul (X : (ZMod 2)[X]) (2 ^ K)
    rw [CharTwo.sub_eq_add, CharTwo.sub_eq_add] at h
    exact h.symm
  have hc := congrArg (fun p => Polynomial.coeff p j) hX
  simp only [coeff_X_add_one_pow, finsetSum_coeff, coeff_X_pow] at hc
  rw [Finset.sum_ite_eq, if_pos (Finset.mem_range.mpr hj)] at hc
  exact (ZMod.natCast_eq_one_iff_odd).mp hc

/-- A product over `Fin (h + h)` of a mirror-symmetric family is a square. -/
theorem prod_eq_sq_of_rev {R : Type*} [CommMonoid R] {n h : ℕ} (hn : n = h + h)
    (f : Fin n → R) (hf : ∀ t, f t = f t.rev) :
    ∏ t, f t = (∏ i : Fin h, f (Fin.cast hn.symm (Fin.castAdd h i))) ^ 2 := by
  subst hn
  have h2 : ∏ i : Fin h, f (Fin.natAdd h i) = ∏ i : Fin h, f (Fin.castAdd h i) := by
    refine Fintype.prod_equiv Fin.revPerm _ _ fun i => ?_
    rw [hf]
    congr 1
    ext
    simp [Fin.val_rev]
    omega
  rw [Fin.prod_univ_add, h2, sq]
  simp

/-- **Rational weights rule out perfect state transfer at time `π` on paths with `2^k + 1`
vertices.** For every `k ≥ 1`, a path on `2^k + 1` vertices with positive rational edge weights
and arbitrary real potentials has no perfect state transfer between its end vertices at time `π`.
-/
def claim : Prop :=
  ∀ k : ℕ, 1 ≤ k → ∀ (r : Fin (2 ^ k) → ℝ) (q : Fin (2 ^ k + 1) → ℝ),
    (∀ j, ∃ x : ℚ, r j = x) → (∀ j, 0 < r j) →
      ¬ HasPST (pathHamiltonian r q) Real.pi 0 (Fin.last (2 ^ k)) ∧
        ¬ HasPST (pathHamiltonian r q) Real.pi (Fin.last (2 ^ k)) 0

/-- No perfect state transfer at time `π` from the last vertex to the first on a path with
`2^K + 1` vertices and positive rational weights. -/
private theorem no_transfer_last_first {m K : ℕ} (hK : 1 ≤ K) (hm : 2 ^ K = m) (r : Fin m → ℝ)
    (q : Fin (m + 1) → ℝ) (hrat : ∀ j, ∃ x : ℚ, r j = x) (hpos : ∀ j, 0 < r j) :
    ¬ HasPST (pathHamiltonian r q) Real.pi (Fin.last m) 0 := by
  have hm2 : 2 ≤ m := by
    rw [← hm]
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ K := Nat.pow_le_pow_right (by norm_num) hK
  set H := pathHamiltonian r q with hHdef
  have hH := pathHamiltonian_isHermitian r q
  set U := NormedSpace.exp (((Real.pi : ℂ) * I) • H) with hUdef
  intro hpst
  set P : ℝ := ∏ t, r t with hP
  have hPpos : 0 < P := Finset.prod_pos fun t _ => hpos t
  have hmom : ∀ p ≤ m, (H ^ p) (Fin.last m) 0 = if p = m then (P : ℂ) else 0 := by
    intro p hp
    split_ifs with hpm
    · rw [hpm, (pathHamiltonian_pow_apply_column r q 0 m (Fin.last m)).2 (by simp), hP]
      push_cast
      rw [Finset.prod_range]
      refine Finset.prod_congr rfl fun t _ => ?_
      simp
    · exact (pathHamiltonian_pow_apply_column r q 0 p (Fin.last m)).1 (Or.inl (by simp; omega))
  have hlast : Fin.last m ≠ 0 := fun h => by
    have := congrArg Fin.val h
    simp at this
    omega
  obtain ⟨z, A, hzinj, hAne, hAuniv, hzA, hzB, hsum⟩ :=
    pst_parity_classes hH (Fin.last m) 0 hlast m (Fintype.card_fin _) P hPpos.ne' hmom hpst
  have hγ : Complex.normSq (U (Fin.last m) 0) = 1 := by
    rw [hUdef, ← hamiltonianPropagator_neg]
    exact hpst
  have hsymr : ∀ t : Fin m, r t = r t.rev :=
    persymmetric_weights r q hpos U (propagator_star_mul_self hH)
      ((Commute.refl H).smul_left ((Real.pi : ℂ) * I)).exp_left.eq
      (U (Fin.last m) 0) hγ (pst_column hH (Fin.last m) 0 hpst)
  choose x hx using hrat
  have hxs : ∀ t : Fin m, x t = x t.rev := fun t => by
    have h := hsymr t
    rw [hx t, hx t.rev] at h
    exact_mod_cast h
  have hh : m = 2 ^ (K - 1) + 2 ^ (K - 1) := by
    rw [← hm, ← two_mul, ← pow_succ']
    congr 1
    omega
  set Qr : ℚ := ∏ i : Fin (2 ^ (K - 1)),
    x (Fin.cast hh.symm (Fin.castAdd (2 ^ (K - 1)) i)) with hQr
  have hPQ : P = ((Qr ^ 2 : ℚ) : ℝ) := by
    rw [hP, hQr, ← prod_eq_sq_of_rev hh x hxs]
    push_cast
    exact Finset.prod_congr rfl fun t _ => hx t
  set Tq : ℚ := ∑ i ∈ A, (∏ j ∈ univ.erase i, ((z i - z j : ℤ) : ℚ))⁻¹ with hTq
  have hQT : Qr ^ 2 * Tq = 1 / 2 := by
    have h : ((Qr ^ 2 * Tq : ℚ) : ℝ) = 1 / 2 := by
      rw [← hsum, hPQ, hTq]
      push_cast
      rfl
    exact Rat.cast_injective (α := ℝ) (h.trans (by norm_num))
  have hAcard : A.card - 1 < 2 ^ K := by
    have h1 : A.card < (univ : Finset (Fin (m + 1))).card :=
      Finset.card_lt_card (Finset.ssubset_univ_iff.mpr hAuniv)
    rw [Finset.card_univ, Fintype.card_fin] at h1
    have h2 : 1 ≤ A.card := Finset.card_pos.mpr hAne
    rw [hm]
    omega
  have hcard : Fintype.card (Fin (m + 1)) - 2 = 2 ^ K - 1 := by
    rw [Fintype.card_fin, hm]
    omega
  obtain ⟨hT0, hTv⟩ := ParityNodeDividedDifference.evenOdd_dividedDifference_twoAdicUnit z hzinj
    A hAne hzA hzB (by rw [hcard]; exact choose_two_pow_sub_one_odd K _ hAcard)
  have hQ0 : Qr ≠ 0 := by
    rintro h0
    rw [h0] at hQT
    norm_num at hQT
  have h2v : padicValRat 2 (2 : ℚ) = 1 := by
    have h := padicValRat.self (p := 2) (by norm_num)
    simpa using h
  have hv := congrArg (padicValRat 2) hQT
  rw [padicValRat.mul (pow_ne_zero 2 hQ0) hT0, padicValRat.pow Qr, ← hTq, hTv, one_div,
    padicValRat.inv, h2v] at hv
  push_cast at hv
  omega

theorem result : claim := by
  intro K hK r q hrat hpos
  have hmain := no_transfer_last_first hK rfl r q hrat hpos
  have hT : (NormedSpace.exp (((Real.pi : ℂ) * I) • pathHamiltonian r q))ᵀ =
      NormedSpace.exp (((Real.pi : ℂ) * I) • pathHamiltonian r q) := by
    rw [← Matrix.exp_transpose, Matrix.transpose_smul, pathHamiltonian_transpose]
  refine ⟨fun h => hmain ?_, hmain⟩
  have he := congrFun (congrFun hT (Fin.last (2 ^ K))) 0
  rw [transpose_apply] at he
  unfold HasPST at h ⊢
  rw [hamiltonianPropagator_neg] at h ⊢
  rwa [← he]

end D5.S3.Quantum.Dynamics.RationalWeightPathTransfer
