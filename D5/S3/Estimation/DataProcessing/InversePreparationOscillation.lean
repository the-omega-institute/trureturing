/- GID: D5/S3/Estimation/DataProcessing/InversePreparationOscillation
   generality: G
   mirror-B: D5/B/S3/Estimation/DataProcessing/InversePreparationOscillation
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   utility: none
   digest: Inverse column oscillation controls a finite preparation matrix's trace defect. -/

import Mathlib.Analysis.Convex.DoublyStochasticMatrix
import Mathlib.Data.Finset.Max
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic.Linarith

/-!
The two public estimates have proof_shape: content and admission_basis: escape-witness.
The witness is the zero-mass bounded-oscillation pairing estimate, live-consumed by the
inverse preparation theorem and the quantum equality-event consumer. The inverse theorem
is live-consumed by ChoiRecoveryIdentifiability.arbitrary_cptp_choi_bridge.
These are arbitrary finite-type, real-parameter theorems, not bounded certificates.
No mathematical novelty or resolution of a published open problem is asserted.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S3.Estimation.DataProcessing.InversePreparationOscillation
open Matrix Finset
open scoped BigOperators

/-- A zero-mass signed row pairs with a bounded-oscillation observable at half its l1 mass. -/
theorem zero_sum_pairing_bound {n : Type*} [Fintype n] [Nonempty n]
    (v w : n → ℝ) (L : ℝ) (hv : ∑ i, v i = 0)
    (hw : ∀ i j, w i - w j ≤ L) :
    |∑ i, v i * w i| ≤ L / 2 * ∑ i, |v i| := by
  classical
  obtain ⟨j, _, hj⟩ := Finset.exists_min_image univ w univ_nonempty
  let t := w j + L / 2
  have hmid (i : n) : |w i - t| ≤ L / 2 := by
    rw [abs_le]
    constructor
    · have := hj i (mem_univ i)
      dsimp [t]
      linarith
    · have := hw i j
      dsimp [t]
      linarith
  have he : (∑ i, v i * w i) = ∑ i, v i * (w i - t) := by
    simp [mul_sub, sum_sub_distrib, ← sum_mul, hv]
  rw [he]
  calc
    |∑ i, v i * (w i - t)| ≤ ∑ i, |v i * (w i - t)| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, |v i| * (L / 2) := by
      apply sum_le_sum
      intro i _
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hmid i) (abs_nonneg _)
    _ = L / 2 * ∑ i, |v i| := by rw [← sum_mul, mul_comm]

/-- No positivity of `P` or of the inverse `N` is required. Only row mass and inverse-column
oscillation enter the estimate. -/
theorem inverse_preparation_trace_bound {n : Type*} [Fintype n] [DecidableEq n]
    [Nonempty n] (M N P : Matrix n n ℝ) (L : ℝ)
    (hM : M *ᵥ 1 = 1) (hNM : N * M = 1) (hP : P *ᵥ 1 = 1)
    (hL : ∀ a c b, N c a - N b a ≤ L) :
    |P.trace - 1| ≤ L / 2 * ∑ a, ∑ c, |(M * P) a c - 1 / (Fintype.card n : ℝ)| := by
  classical
  let U : Matrix n n ℝ := fun _ _ => 1 / (Fintype.card n : ℝ)
  let Z := M * P - U
  have hc : (Fintype.card n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hrows (a : n) : ∑ c, Z a c = 0 := by
    have hh := congrFun (show (M * P) *ᵥ 1 = 1 by
      rw [← Matrix.mulVec_mulVec, hP, hM]) a
    change (∑ c, ((M * P) a c - 1 / (Fintype.card n : ℝ))) = 0
    simpa [Matrix.mulVec, dotProduct, sum_sub_distrib, hc] using sub_eq_zero.mpr hh
  have hN : N *ᵥ (1 : n → ℝ) = 1 := by
    calc
      N *ᵥ 1 = N *ᵥ (M *ᵥ 1) := by rw [hM]
      _ = 1 := by rw [Matrix.mulVec_mulVec, hNM, Matrix.one_mulVec]
  have hNU : N * U = U := by
    ext i j
    change (∑ k, N i k * (1 / (Fintype.card n : ℝ))) = 1 / (Fintype.card n : ℝ)
    have hi := congrFun hN i
    simpa only [Matrix.mul_apply, Matrix.mulVec, dotProduct, U, ← sum_mul, Pi.one_apply, mul_one, one_mul] using
      congrArg (fun x : ℝ => x * (1 / (Fintype.card n : ℝ))) hi
  have hNZ : N * Z = P - U := by
    simp only [Z, Matrix.mul_sub, ← Matrix.mul_assoc, hNM, Matrix.one_mul, hNU]
  have htr : P.trace - 1 = ∑ a, ∑ c, Z a c * N c a := by
    have ht := congrArg Matrix.trace hNZ
    have hu : U.trace = 1 := by simp [Matrix.trace, Matrix.diag, U, hc]
    rw [Matrix.trace_sub, hu] at ht
    rw [← ht, Matrix.trace_mul_comm]
    simp [Matrix.trace, Matrix.mul_apply]
  rw [htr]
  calc
    |∑ a, ∑ c, Z a c * N c a| ≤ ∑ a, |∑ c, Z a c * N c a| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ a, L / 2 * ∑ c, |Z a c| := by
      exact sum_le_sum fun a _ => zero_sum_pairing_bound (Z a) (fun c => N c a) L
        (hrows a) (fun c b => hL a c b)
    _ = L / 2 * ∑ a, ∑ c, |(M * P) a c - 1 / (Fintype.card n : ℝ)| := by
      rw [← mul_sum]
      rfl

#print axioms zero_sum_pairing_bound
#print axioms inverse_preparation_trace_bound
end D5.S3.Estimation.DataProcessing.InversePreparationOscillation
