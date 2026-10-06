/- GID: D5/S3/Arith/Lattices/Klartag/Completion/Assembly
   generality: G
   mirror-B: D5/B/S3/Arith/Lattices/Klartag/Completion/Assembly
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Uniform constants and completion of lattice packing. -/

/- Copyright 2026 Lean FRO, LLC. Licensed under Apache-2.0.
   Source: mlgraham/lean-eval-klartag-submission, commit
   270b3358a135f64a6688636660c07772e8db0173.
   Attribution and full license: Library/QuadraticForms/klartag2025packing.md. -/

import D5.S3.Arith.Lattices.Klartag.Walk.ChainWiring
import D5.S3.Arith.Lattices.Klartag.Walk.ChainDataInst
import D5.S3.Arith.Lattices.Klartag.Construction.LatticeTransfer

set_option linter.unusedSectionVars false

open D5.S3.Arith.Lattices.Klartag.Construction
open D5.S3.Arith.Lattices.Klartag.Gaussian
open D5.S3.Arith.Lattices.Klartag.Walk

namespace D5.S3.Arith.Lattices.Klartag.Completion.Assembly

open MeasureTheory
open Matrix
open Metric
open Finset
open scoped ENNReal RealInnerProductSpace
open D5.S3.Arith.Lattices.Klartag
open D5.S3.Arith.Lattices.Klartag.Walk.Increments

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

variable {N : ℕ}

/-- **Klartag eq. (68), with the constant written out.**  `log det A ≤ C' − 4 log n` gives
`Vol(E_A) ≥ e^{−C'/2}·n²·Vol(Bᴺ)`.  With `C'` the universal constant of Lemma 5.2 this is
`c₀ = e^{−C'/2}`: **the `n²` of the theorem statement, produced here and nowhere else.** -/
theorem sqrt_det_le {A : Matrix (Fin N) (Fin N) ℝ} (hApos : 0 < A.det) {C' : ℝ} {n : ℕ}
    (hn : n ≠ 0) (hlog : Real.log A.det ≤ C' - 4 * Real.log n) :
    Real.sqrt A.det ≤ Real.exp (C' / 2) / (n : ℝ) ^ 2 := by
  have hn' : (0 : ℝ) < (n : ℝ) := by positivity
  have hu : 0 < Real.sqrt A.det := Real.sqrt_pos.2 hApos
  have hv : 0 < Real.exp (C' / 2) / (n : ℝ) ^ 2 := by positivity
  refine (Real.log_le_log_iff hu hv).1 ?_
  have hlu : Real.log (Real.sqrt A.det) = Real.log A.det / 2 := Real.log_sqrt hApos.le
  have hlv : Real.log (Real.exp (C' / 2) / (n : ℝ) ^ 2) = C' / 2 - 2 * Real.log n := by
    rw [Real.log_div (by positivity) (by positivity), Real.log_exp, Real.log_pow]
    push_cast
    ring
  rw [hlu, hlv]
  linarith

open D5.S3.Arith.Lattices.Klartag.Construction.ConstructionA
open D5.S3.Arith.Lattices.Klartag.Walk.ChainDataInst
open D5.S3.Arith.Lattices.Klartag.Construction.LatticeTransfer
open D5.S3.Arith.Lattices.Klartag.Construction.Section5
open D5.S3.Arith.Lattices.Klartag.Construction.Tiling

def ChainOutput {p m : ℕ} (α : ℝ) (g : Fin (m + 1) → ZMod p) (c₀ : ℝ) : Prop :=
  ∃ A S : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ, 0 < A.det ∧ Sᵀ * A * S = 1 ∧
    Real.sqrt A.det * (c₀ * (m : ℝ) ^ 2) ≤ 1 ∧
    ∀ x : Fin (m + 1) → ℝ, x ∈ (α • ·) '' (latR p (m + 1) g : Set (Fin (m + 1) → ℝ)) → x ≠ 0 →
      (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin (m + 1))) ∉ ChainEllipsoid.ellipsoid A

theorem mulVec_ne_zero {N : ℕ} {B : Matrix (Fin N) (Fin N) ℝ} (hB : B.det ≠ 0)
    {v : Fin N → ℝ} (hv : v ≠ 0) : B *ᵥ v ≠ 0 := by
  intro h
  refine hv ?_
  have hinv : B⁻¹ *ᵥ (B *ᵥ v) = v := by
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul B (isUnit_iff_ne_zero.2 hB),
      Matrix.one_mulVec]
  rw [h, Matrix.mulVec_zero] at hinv
  exact hinv.symm

end D5.S3.Arith.Lattices.Klartag.Completion.Assembly
