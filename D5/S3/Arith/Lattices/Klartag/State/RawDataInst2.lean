/- GID: D5/S3/Arith/Lattices/Klartag/State/RawDataInst2
   generality: G
   mirror-B: D5/B/S3/Arith/Lattices/Klartag/State/RawDataInst2
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Symmetric matrix state invariants and padded driving laws. -/

/- Copyright 2026 Lean FRO, LLC. Licensed under Apache-2.0.
   Source: mlgraham/lean-eval-klartag-submission, commit
   270b3358a135f64a6688636660c07772e8db0173.
   Attribution and full license: Library/QuadraticForms/klartag2025packing.md. -/

import Mathlib
import D5.S3.Arith.Lattices.Klartag.State.RawDataInst
import D5.S3.Arith.Lattices.Klartag.Tail.TailSideSetup2
import D5.S3.Arith.Lattices.Klartag.Walk.ChainWiring

set_option linter.unusedSectionVars false

open D5.S3.Arith.Lattices.Klartag.Completion
open D5.S3.Arith.Lattices.Klartag.Construction
open D5.S3.Arith.Lattices.Klartag.Contact
open D5.S3.Arith.Lattices.Klartag.Drift
open D5.S3.Arith.Lattices.Klartag.Gaussian
open D5.S3.Arith.Lattices.Klartag.State
open D5.S3.Arith.Lattices.Klartag.Tail
open D5.S3.Arith.Lattices.Klartag.Walk

namespace D5.S3.Arith.Lattices.Klartag.State.RawDataInst2

open MeasureTheory
open Finset
open scoped RealInnerProductSpace
open D5.S3.Arith.Lattices.Klartag
open D5.S3.Arith.Lattices.Klartag.Construction.Section5
open D5.S3.Arith.Lattices.Klartag.Construction.Tiling
open D5.S3.Arith.Lattices.Klartag.Construction.ConstructionA
open D5.S3.Arith.Lattices.Klartag.State.PaddedLawSetup
open D5.S3.Arith.Lattices.Klartag.Walk.Increments
open D5.S3.Arith.Lattices.Klartag.Walk.ChainWiring
open D5.S3.Arith.Lattices.Klartag.Tail.TailSideSetup2
open D5.S3.Arith.Lattices.Klartag.State.RawDataInst

variable {n : ℕ}

/-- The identity matrix in Frobenius coordinates. -/
noncomputable def idUT (n : ℕ) : EuclideanSpace ℝ (UT n) :=
  WithLp.toLp 2 fun p => if p.1.1 = p.1.2 then 1 else 0

@[simp] theorem idUT_apply (p : UT n) :
    (idUT n) p = if p.1.1 = p.1.2 then 1 else 0 := rfl

theorem up_fst_eq_snd_iff (i j : Fin n) : (up i j).1.1 = (up i j).1.2 ↔ i = j := by
  rcases le_total i j with h | h
  · rw [up_of_le h]
  · rw [up_comm, up_of_le h]; exact eq_comm

theorem symMat_idUT (n : ℕ) : symMat (idUT n) = (1 : Matrix (Fin n) (Fin n) ℝ) := by
  ext i j
  rw [symMat_apply, idUT_apply, Matrix.one_apply]
  by_cases h : i = j
  · rw [if_pos ((up_fst_eq_snd_iff i j).2 h), if_pos h, mul_one, cc_diag ((up_fst_eq_snd_iff i j).2 h)]
  · rw [if_neg (fun hc => h ((up_fst_eq_snd_iff i j).1 hc)), if_neg h, mul_zero]

/-- `⟪Id, q x⟫ = |x|²`. -/
theorem inner_idUT (x : Fin n → ℝ) : ⟪idUT n, qUT x⟫ = x ⬝ᵥ x := by
  rw [inner_qUT_eq_quad, symMat_idUT, Matrix.one_mulVec]

/-- The chain's initial state, Klartag's `a₀·Id` (eq. 61). -/
noncomputable def A0C (n : ℕ) : EuclideanSpace ℝ (UT n) := a0C n • idUT n

/-- The scaled lattice point, as a plain coordinate vector. -/
noncomputable def xOf (α : ℝ) {n : ℕ} (y : Fin n → ℤ) : Fin n → ℝ := fun i => α * (y i : ℝ)

theorem dotProduct_xOf (α : ℝ) {n : ℕ} (y : Fin n → ℤ) :
    xOf α y ⬝ᵥ xOf α y = (α * ‖toE n y‖) ^ 2 := by
  have hnorm : ‖toE n y‖ ^ 2 = ∑ i : Fin n, ((y i : ℝ)) ^ 2 := by
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
    exact Finset.sum_congr rfl (fun i _ => by rw [Tiling.toE_apply, Real.norm_eq_abs, sq_abs])
  rw [dotProduct, mul_pow, hnorm, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun i _ => by rw [xOf]; ring)

/-- The chain's constraint vector at the scaled lattice point. -/
noncomputable def qC (α : ℝ) {n : ℕ} (y : Fin n → ℤ) : EuclideanSpace ℝ (UT n) := qUT (xOf α y)

theorem norm_qC (α : ℝ) {n : ℕ} (y : Fin n → ℤ) : ‖qC α y‖ = (α * ‖toE n y‖) ^ 2 := by
  have h : ‖qC α y‖ ^ 2 = ((α * ‖toE n y‖) ^ 2) ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, qC, inner_qUT, dotProduct_xOf]
  have h2 : (0 : ℝ) ≤ (α * ‖toE n y‖) ^ 2 := sq_nonneg _
  nlinarith [norm_nonneg (qC α y), h, h2]

theorem inner_A0C_qC (α : ℝ) {n : ℕ} (y : Fin n → ℤ) :
    ⟪A0C n, qC α y⟫ = a0C n * (α * ‖toE n y‖) ^ 2 := by
  rw [A0C, qC, real_inner_smul_left, inner_idUT, dotProduct_xOf]

/-- **`NormData` for the chain's own data** — both fields, for any `W`. -/
theorem normData_qC (α : ℝ) {n : ℕ} (W : Finset (Fin n → ℤ)) :
    NormData n α (qC α) W (A0C n) :=
  ⟨fun y _ => norm_qC α y, fun y _ => inner_A0C_qC α y⟩

end D5.S3.Arith.Lattices.Klartag.State.RawDataInst2
