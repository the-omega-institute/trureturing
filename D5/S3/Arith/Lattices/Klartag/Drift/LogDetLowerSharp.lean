/- GID: D5/S3/Arith/Lattices/Klartag/Drift/LogDetLowerSharp
   generality: G
   mirror-B: D5/B/S3/Arith/Lattices/Klartag/Drift/LogDetLowerSharp
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Second order log determinant bounds and accumulated drift. -/

/- Copyright 2026 Lean FRO, LLC. Licensed under Apache-2.0.
   Source: mlgraham/lean-eval-klartag-submission, commit
   270b3358a135f64a6688636660c07772e8db0173.
   Attribution and full license: Library/QuadraticForms/klartag2025packing.md. -/

import D5.S3.Arith.Lattices.Klartag.Drift.LogDetVariance

open D5.S3.Arith.Lattices.Klartag.Completion
open D5.S3.Arith.Lattices.Klartag.Construction
open D5.S3.Arith.Lattices.Klartag.Contact
open D5.S3.Arith.Lattices.Klartag.Drift
open D5.S3.Arith.Lattices.Klartag.Drift.Stopped
open D5.S3.Arith.Lattices.Klartag.Gaussian
open D5.S3.Arith.Lattices.Klartag.Lemma43R
open D5.S3.Arith.Lattices.Klartag.Lemma43R2
open D5.S3.Arith.Lattices.Klartag.State
open D5.S3.Arith.Lattices.Klartag.Tail
open D5.S3.Arith.Lattices.Klartag.Walk

namespace D5.S3.Arith.Lattices.Klartag.Drift.LogDetLowerSharp

open MeasureTheory
open Matrix
open Finset
open Module
open scoped RealInnerProductSpace
open D5.S3.Arith.Lattices.Klartag
open D5.S3.Arith.Lattices.Klartag.Walk.Increments

theorem log_one_add_ge_sharp {x : ℝ} (hx : |x| ≤ 1 / 2) :
    x - x ^ 2 / 2 - 2 * |x| ^ 3 ≤ Real.log (1 + x) := by
  have hlt : |(-x)| < 1 := by rw [abs_neg]; linarith
  have h := Real.abs_log_sub_add_sum_range_le hlt 2
  have hsum : (∑ i ∈ Finset.range 2, (-x) ^ (i + 1) / ((i : ℝ) + 1)) = -x + x ^ 2 / 2 := by
    simp [Finset.sum_range_succ]; ring
  have hone : (1 : ℝ) - (-x) = 1 + x := by ring
  rw [hsum, hone, abs_neg] at h
  have hpos : (0 : ℝ) < 1 - |x| := by linarith
  have hnorm : |x| ^ (2 + 1) = |x| ^ 3 := by norm_num
  have h3 : |x| ^ (2 + 1) / (1 - |x|) ≤ 2 * |x| ^ 3 := by
    rw [hnorm, div_le_iff₀ hpos]
    have h0 : (0 : ℝ) ≤ |x| ^ 3 := by positivity
    nlinarith [abs_nonneg x]
  have h4 : |(-x + x ^ 2 / 2) + Real.log (1 + x)| ≤ 2 * |x| ^ 3 := le_trans h h3
  linarith [(abs_le.1 h4).1]

theorem log_one_add_ge_of_abs_le {x r : ℝ} (hr : r ≤ 1 / 2) (hx : |x| ≤ r) :
    x - (1 / 2 + 2 * r) * x ^ 2 ≤ Real.log (1 + x) := by
  have hx2 : |x| ≤ 1 / 2 := le_trans hx hr
  have hmain := log_one_add_ge_sharp hx2
  have hsq : |x| ^ 2 = x ^ 2 := sq_abs x
  have hcube : |x| ^ 3 = |x| * x ^ 2 := by rw [← hsq]; ring
  have hle : |x| * x ^ 2 ≤ r * x ^ 2 :=
    mul_le_mul_of_nonneg_right hx (sq_nonneg x)
  rw [hcube] at hmain
  nlinarith [hmain, hle]

section Spectral

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **`LogDetVariance.log_det_one_add_ge` with the sharp constant.**  The hypothesis is two-sided
(`|λ| ≤ r`) where 94a's was one-sided (`λ ≥ −1/2`); the chain supplies it from the operator norm,
which is what 94a's own proof already derived. -/
theorem log_det_one_add_ge_sharp {B : Matrix n n ℝ} (hB : B.IsHermitian) {r : ℝ}
    (hr : r ≤ 1 / 2) (hbd : ∀ i, |hB.eigenvalues i| ≤ r) :
    B.trace - (1 / 2 + 2 * r) * (∑ i, (hB.eigenvalues i) ^ 2) ≤ Real.log (1 + B).det := by
  have hpos : ∀ i, (0 : ℝ) < 1 + hB.eigenvalues i := fun i => by
    have := (abs_le.1 (le_trans (hbd i) hr)).1; linarith
  rw [D5.S3.Arith.Lattices.Klartag.det_one_add_eq_prod hB,
    Real.log_prod (fun i _ => ne_of_gt (hpos i)),
    D5.S3.Arith.Lattices.Klartag.trace_eq_sum_eigenvalues_real hB, Finset.mul_sum,
    ← Finset.sum_sub_distrib]
  exact Finset.sum_le_sum fun i _ => log_one_add_ge_of_abs_le hr (hbd i)

end Spectral

section Cone

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **`LogDetVariance.log_det_add_ge` with the sharp constant.** -/
theorem log_det_add_ge_sharp {A H S : Matrix n n ℝ} (hA : A.PosDef)
    (hS : S.IsHermitian) (hSA : S * A * S = 1) (hH : H.IsHermitian) {r : ℝ} (hr : r ≤ 1 / 2)
    (hbd : ∀ i, |(D5.S3.Arith.Lattices.Klartag.IsHermitian.conj' hS hH).eigenvalues i| ≤ r) :
    Real.log A.det + (A⁻¹ * H).trace - (1 / 2 + 2 * r) * (∑ i, ∑ j, ((S * H * S) i j) ^ 2)
      ≤ Real.log (A + H).det := by
  have hB := D5.S3.Arith.Lattices.Klartag.IsHermitian.conj' hS hH
  have hpos : ∀ i, (0 : ℝ) < 1 + hB.eigenvalues i := fun i => by
    have := (abs_le.1 (le_trans (hbd i) hr)).1; linarith
  have hSS : S * S * A = 1 := by
    have h1 : (S * A) * S = 1 := hSA
    have h2 : S * (S * A) = 1 := _root_.mul_eq_one_comm.mp h1
    rw [← mul_assoc] at h2
    exact h2
  have hAinv : A⁻¹ = S * S := Matrix.inv_eq_left_inv hSS
  have hcong : S * (A + H) * S = 1 + S * H * S := by
    rw [Matrix.mul_add, Matrix.add_mul, hSA]
  have hdetA : 0 < A.det := hA.det_pos
  have hdetS : S.det * A.det * S.det = 1 := by
    have h := congrArg Matrix.det hSA
    rwa [Matrix.det_mul, Matrix.det_mul, Matrix.det_one] at h
  have hcongdet : S.det * (A + H).det * S.det = (1 + S * H * S).det := by
    have h := congrArg Matrix.det hcong
    rwa [Matrix.det_mul, Matrix.det_mul] at h
  have hdet : (A + H).det = A.det * (1 + S * H * S).det := by
    linear_combination A.det * hcongdet - (A + H).det * hdetS
  have htr : (A⁻¹ * H).trace = (S * H * S).trace := by
    rw [hAinv, Matrix.trace_mul_cycle S H S]
  have hposdet : 0 < (1 + S * H * S).det := by
    rw [D5.S3.Arith.Lattices.Klartag.det_one_add_eq_prod hB]
    exact Finset.prod_pos fun i _ => hpos i
  rw [hdet, Real.log_mul (ne_of_gt hdetA) (ne_of_gt hposdet), htr,
    ← D5.S3.Arith.Lattices.Klartag.sum_sq_eigenvalues_eq_frobenius hB]
  linarith [log_det_one_add_ge_sharp hB hr hbd]

end Cone

section Chain

variable {n : ℕ}

theorem log_det_add_ge_sharp_of_stateBounds {A H : Matrix (Fin n) (Fin n) ℝ} {m M r : ℝ}
    (hSB : Discharge.StateBounds A m M) (hH : H.IsHermitian) (hr0 : 0 ≤ r) (hr : r ≤ 1 / 2)
    (hop : ‖Matrix.toEuclideanCLM (𝕜 := ℝ) H‖ ≤ r * m) :
    Real.log A.det + (A⁻¹ * H).trace
        - ((1 / 2 + 2 * r) / m ^ 2) * (∑ i, ∑ j, (H i j) ^ 2)
      ≤ Real.log (A + H).det := by
  classical
  obtain ⟨S, hSherm, hSA⟩ := hSB.congr
  have hm := hSB.mpos
  have hSsym : S.IsSymm := Matrix.isHermitian_iff_isSymm.1 hSherm
  have hSS : S * S * A = 1 := by
    have h1 : (S * A) * S = 1 := hSA
    have h2 : S * (S * A) = 1 := _root_.mul_eq_one_comm.mp h1
    rw [← mul_assoc] at h2
    exact h2
  have hAinv : A⁻¹ = S * S := Matrix.inv_eq_left_inv hSS
  have hS2 : ‖Matrix.toEuclideanCLM (𝕜 := ℝ) S‖ ^ 2 ≤ 1 / m := by
    refine le_trans (StepInputs2.opNorm_sq_le_of_sq (A := A⁻¹) hSsym ?_)
      (LogDetVariance.opNorm_inv_le hSB)
    exact hAinv.symm
  have hS0 : (0 : ℝ) ≤ ‖Matrix.toEuclideanCLM (𝕜 := ℝ) S‖ := norm_nonneg _
  have hH0 : (0 : ℝ) ≤ ‖Matrix.toEuclideanCLM (𝕜 := ℝ) H‖ := norm_nonneg _
  have hfrob : ∑ i, ∑ j, ((S * H * S) i j) ^ 2
      ≤ (1 / m ^ 2) * ∑ i, ∑ j, (H i j) ^ 2 := by
    have h1 : ∑ i, ∑ j, ((S * H * S) i j) ^ 2
        ≤ ‖Matrix.toEuclideanCLM (𝕜 := ℝ) S‖ ^ 2 * ∑ i, ∑ j, ((S * H) i j) ^ 2 :=
      StepInputs2.frobenius_mul_right_le (S * H) S hSsym
    have h2 : ∑ i, ∑ j, ((S * H) i j) ^ 2
        ≤ ‖Matrix.toEuclideanCLM (𝕜 := ℝ) S‖ ^ 2 * ∑ i, ∑ j, (H i j) ^ 2 :=
      StepInputs2.frobenius_mul_left_le S H
    have hHF0 : (0 : ℝ) ≤ ∑ i, ∑ j, (H i j) ^ 2 := by positivity
    have hS20 : (0 : ℝ) ≤ ‖Matrix.toEuclideanCLM (𝕜 := ℝ) S‖ ^ 2 := by positivity
    have h3 : ‖Matrix.toEuclideanCLM (𝕜 := ℝ) S‖ ^ 2 * ∑ i, ∑ j, ((S * H) i j) ^ 2
        ≤ ‖Matrix.toEuclideanCLM (𝕜 := ℝ) S‖ ^ 2
          * (‖Matrix.toEuclideanCLM (𝕜 := ℝ) S‖ ^ 2 * ∑ i, ∑ j, (H i j) ^ 2) :=
      mul_le_mul_of_nonneg_left h2 hS20
    have h4 : ‖Matrix.toEuclideanCLM (𝕜 := ℝ) S‖ ^ 2
          * (‖Matrix.toEuclideanCLM (𝕜 := ℝ) S‖ ^ 2 * ∑ i, ∑ j, (H i j) ^ 2)
        ≤ (1 / m) * ((1 / m) * ∑ i, ∑ j, (H i j) ^ 2) := by
      have hstep : ‖Matrix.toEuclideanCLM (𝕜 := ℝ) S‖ ^ 2 * ∑ i, ∑ j, (H i j) ^ 2
          ≤ (1 / m) * ∑ i, ∑ j, (H i j) ^ 2 :=
        mul_le_mul_of_nonneg_right hS2 hHF0
      have hrhs0 : (0 : ℝ) ≤ (1 / m) * ∑ i, ∑ j, (H i j) ^ 2 := by positivity
      nlinarith [hS2, hS20, hstep, hHF0]
    have h5 : (1 / m) * ((1 / m) * ∑ i, ∑ j, (H i j) ^ 2)
        = (1 / m ^ 2) * ∑ i, ∑ j, (H i j) ^ 2 := by
      field_simp
    linarith

  have hopSHS : ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (S * H * S)‖ ≤ r := by
    have hmul : Matrix.toEuclideanCLM (𝕜 := ℝ) (S * H * S)
        = Matrix.toEuclideanCLM (𝕜 := ℝ) S * Matrix.toEuclideanCLM (𝕜 := ℝ) H
          * Matrix.toEuclideanCLM (𝕜 := ℝ) S := by
      rw [map_mul, map_mul]
    rw [hmul]
    have hb1 : ‖Matrix.toEuclideanCLM (𝕜 := ℝ) S * Matrix.toEuclideanCLM (𝕜 := ℝ) H
          * Matrix.toEuclideanCLM (𝕜 := ℝ) S‖
        ≤ ‖Matrix.toEuclideanCLM (𝕜 := ℝ) S‖ * ‖Matrix.toEuclideanCLM (𝕜 := ℝ) H‖
          * ‖Matrix.toEuclideanCLM (𝕜 := ℝ) S‖ :=
      le_trans (norm_mul_le _ _) (mul_le_mul_of_nonneg_right (norm_mul_le _ _) hS0)
    have hb2 : ‖Matrix.toEuclideanCLM (𝕜 := ℝ) S‖ * ‖Matrix.toEuclideanCLM (𝕜 := ℝ) H‖
          * ‖Matrix.toEuclideanCLM (𝕜 := ℝ) S‖
        = ‖Matrix.toEuclideanCLM (𝕜 := ℝ) S‖ ^ 2 * ‖Matrix.toEuclideanCLM (𝕜 := ℝ) H‖ := by
      ring
    rw [hb2] at hb1
    have hb3 : ‖Matrix.toEuclideanCLM (𝕜 := ℝ) S‖ ^ 2 * ‖Matrix.toEuclideanCLM (𝕜 := ℝ) H‖
        ≤ (1 / m) * (r * m) := mul_le_mul hS2 hop hH0 (by positivity)
    have hb4 : (1 / m) * (r * m) = r := by field_simp
    linarith
  have hbd : ∀ i, |(D5.S3.Arith.Lattices.Klartag.IsHermitian.conj' hSherm hH).eigenvalues i| ≤ r := fun i =>
    le_trans (GoodEvent.abs_eigenvalues_le_opNorm
      (D5.S3.Arith.Lattices.Klartag.IsHermitian.conj' hSherm hH) i) hopSHS
  have hmain := log_det_add_ge_sharp hSB.posDef hSherm hSA hH hr hbd
  have hcoef0 : (0 : ℝ) ≤ 1 / 2 + 2 * r := by linarith
  have hstep : (1 / 2 + 2 * r) * (∑ i, ∑ j, ((S * H * S) i j) ^ 2)
      ≤ (1 / 2 + 2 * r) * ((1 / m ^ 2) * ∑ i, ∑ j, (H i j) ^ 2) :=
    mul_le_mul_of_nonneg_left hfrob hcoef0
  have hid : ((1 / 2 + 2 * r) / m ^ 2) * (∑ i, ∑ j, (H i j) ^ 2)
      = (1 / 2 + 2 * r) * ((1 / m ^ 2) * ∑ i, ∑ j, (H i j) ^ 2) := by ring
  rw [hid]
  linarith

end Chain

end D5.S3.Arith.Lattices.Klartag.Drift.LogDetLowerSharp
