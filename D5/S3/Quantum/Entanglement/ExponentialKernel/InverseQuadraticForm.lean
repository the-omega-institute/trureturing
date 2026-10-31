/- GID: D5/S3/Quantum/Entanglement/ExponentialKernel/InverseQuadraticForm
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/ExponentialKernel/InverseQuadraticForm
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Identify the actual inverse quadratic form of every strictly ordered finite exponential kernel. -/

import D5.S3.Quantum.Entanglement.ExponentialSectorKernel
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Entanglement.ExponentialSectorKernel

open Matrix
open scoped BigOperators

noncomputable section

set_option maxHeartbeats 800000 in
/-- The exponential matrix is nonsingular and its actual inverse has the innovation quadratic form.
Only adjacent sites in the finite prefix are required to be strictly ordered. -/
theorem inverse_quadratic_form (n : ℕ) (loss : ℕ → ℝ)
    (horder : ∀ i < n, loss i < loss (i + 1)) :
    let K : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ := fun i j => kernel loss i j
    K.det ≠ 0 ∧ K * K⁻¹ = 1 ∧
      ∀ x : Fin (n + 1) → ℝ,
        x ⬝ᵥ (K⁻¹ *ᵥ x) = x 0 ^ 2 +
          ∑ i : Fin n, (x i.succ - edge loss i * x i.castSucc) ^ 2 /
            (1 - edge loss i ^ 2) := by
  classical
  let K : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ := fun i j => kernel loss i j
  change K.det ≠ 0 ∧ K * K⁻¹ = 1 ∧ _
  let A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ := fun i =>
    Fin.cases (fun j => if j = 0 then 1 else 0)
      (fun r j => (if j = r.succ then 1 else 0) -
        edge loss r * (if j = r.castSucc then 1 else 0)) i
  let d : Fin (n + 1) → ℝ := Fin.cases 1 (fun i => 1 - edge loss i ^ 2)
  have hmono : ∀ j : ℕ, j ≤ n → ∀ i ≤ j, loss i ≤ loss j := by
    intro j
    induction j with
    | zero => intro hj i hi; have : i = 0 := by omega; subst i; rfl
    | succ j ih =>
      intro hj i hi
      by_cases he : i = j + 1
      · subst i; rfl
      · exact (ih (by omega) i (by omega)).trans (horder j (by omega)).le
  have hdiag (i : ℕ) : kernel loss i i = 1 := by simp [kernel]
  have hsymm (i j : ℕ) : kernel loss i j = kernel loss j i := by
    simp only [kernel, abs_sub_comm]
  have hcross (j : Fin n) (i : ℕ) (hi : i ≤ j) :
      kernel loss i (j + 1) = edge loss j * kernel loss i j := by
    have h0 := hmono j (by omega) i hi
    have h1 := hmono (j + 1) (by omega) i (by omega)
    simp only [kernel, edge, abs_of_nonpos (sub_nonpos.mpr h0),
      abs_of_nonpos (sub_nonpos.mpr h1), ← Real.exp_add]
    congr 1
    ring
  have hadj (i : Fin n) : kernel loss i (i + 1) = edge loss i := by
    simpa only [hdiag, mul_one] using hcross i i le_rfl
  have hd (i : Fin (n + 1)) : d i ≠ 0 := by
    refine Fin.cases (by simp [d]) (fun j => ?_) i
    have ha : 0 < edge loss j := Real.exp_pos _
    have hb : edge loss j < 1 := by
      apply Real.exp_lt_one_iff.mpr
      have := horder j j.isLt
      dsimp [edge]
      linarith
    have : 0 < 1 - edge loss j ^ 2 := by nlinarith
    simpa only [d, Fin.cases_succ] using ne_of_gt this
  have hleft0 (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (j) :
      (A * M) 0 j = M 0 j := by
    simp [Matrix.mul_apply, A]
  have hleft (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
      (i : Fin n) (j) :
      (A * M) i.succ j = M i.succ j - edge loss i * M i.castSucc j := by
    simp [Matrix.mul_apply, A, sub_mul, Finset.sum_sub_distrib,
      mul_assoc, ← Finset.mul_sum]
  have hright0 (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (i) :
      (M * Aᵀ) i 0 = M i 0 := by
    simp [Matrix.mul_apply, A]
  have hright (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
      (i) (j : Fin n) :
      (M * Aᵀ) i j.succ = M i j.succ - edge loss j * M i j.castSucc := by
    simp [Matrix.mul_apply, A, mul_sub, Finset.sum_sub_distrib,
      mul_comm, mul_left_comm, mul_assoc, ← Finset.mul_sum]
  have hfactor : A * K * Aᵀ = Matrix.diagonal d := by
    ext i j
    refine Fin.cases ?_ (fun r => ?_) i
    · refine Fin.cases ?_ (fun s => ?_) j
      · simp [hright0, hleft0, K, hdiag, d]
      · rw [hright, hleft0, hleft0]
        have hc := hcross s 0 (Nat.zero_le _)
        simpa [K, d, Matrix.diagonal, hc] using
          sub_self (edge loss s * kernel loss 0 s)
    · refine Fin.cases ?_ (fun s => ?_) j
      · rw [hright0, hleft]
        have hc := hcross r 0 (Nat.zero_le _)
        simpa [K, d, Matrix.diagonal, hsymm (r + 1) 0, hsymm r 0, hc] using
          sub_self (edge loss r * kernel loss 0 r)
      · rw [hright, hleft, hleft]
        by_cases he : r = s
        · subst s
          simp only [K, Fin.val_succ, Fin.val_castSucc, hdiag, hadj,
            hsymm (r + 1) r, Matrix.diagonal_apply_eq, d, Fin.cases_succ]
          ring
        · have hne : r.succ ≠ s.succ := fun h => he (Fin.succ_inj.mp h)
          rw [Matrix.diagonal_apply_ne _ hne]
          rcases lt_or_gt_of_ne he with hrs | hsr
          · have h1 := hcross s (r + 1) (by exact hrs)
            have h2 := hcross s r hrs.le
            simp only [K, Fin.val_succ, Fin.val_castSucc, h1, h2]
            ring
          · have h1 := hcross r (s + 1) (by exact hsr)
            have h2 := hcross r s hsr.le
            simp only [K, Fin.val_succ, Fin.val_castSucc]
            rw [hsymm (r + 1) (s + 1), hsymm (r + 1) s, h1, h2,
              hsymm r (s + 1), hsymm r s]
            ring
  let D : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ := Matrix.diagonal (fun i => (d i)⁻¹)
  have hD : Matrix.diagonal d * D = 1 := by
    rw [D, Matrix.diagonal_mul_diagonal]
    simp only [mul_inv_cancel₀ (hd _), Matrix.diagonal_one]
  have hAK : A * (K * (Aᵀ * D)) = 1 := by
    calc
      A * (K * (Aᵀ * D)) = (A * K * Aᵀ) * D := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hfactor, hD]
  have hKQ : K * (Aᵀ * D * A) = 1 := by
    simpa only [Matrix.mul_assoc] using Matrix.mul_eq_one_comm.mp hAK
  have hinv : K⁻¹ = Aᵀ * D * A := Matrix.inv_eq_right_inv hKQ
  refine ⟨Matrix.det_ne_zero_of_right_inverse hKQ, ?_, ?_⟩
  · rw [hinv]
    exact hKQ
  · intro x
    have hAx0 : (A *ᵥ x) 0 = x 0 := by simp [Matrix.mulVec, dotProduct, A]
    have hAx (i : Fin n) :
        (A *ᵥ x) i.succ = x i.succ - edge loss i * x i.castSucc := by
      simp [Matrix.mulVec, dotProduct, A, sub_mul, Finset.sum_sub_distrib,
        mul_assoc, ← Finset.mul_sum]
    rw [hinv, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      Matrix.dotProduct_transpose_mulVec]
    simp only [D, Matrix.mulVec_diagonal, dotProduct]
    rw [Fin.sum_univ_succ]
    simp only [hAx0, hAx, d, Fin.cases_zero, Fin.cases_succ, inv_one, mul_one]
    congr 1
    · ring
    · apply Finset.sum_congr rfl
      intro i _
      ring

end
end D5.S3.Quantum.Entanglement.ExponentialSectorKernel
