/- GID: D5/S3/Arith/Lattices/Klartag/Drift/Stopped/DriftStopped8
   generality: G
   mirror-B: D5/B/S3/Arith/Lattices/Klartag/Drift/Stopped/DriftStopped8
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Stopped log determinant drift and integrability estimates. -/

/- Copyright 2026 Lean FRO, LLC. Licensed under Apache-2.0.
   Source: mlgraham/lean-eval-klartag-submission, commit
   270b3358a135f64a6688636660c07772e8db0173.
   Attribution and full license: Library/QuadraticForms/klartag2025packing.md. -/

import D5.S3.Arith.Lattices.Klartag.Drift.Stopped.DriftStopped7
import Mathlib
import D5.S3.Arith.Lattices.Klartag.Completion.Theorem2
import D5.S3.Arith.Lattices.Klartag.Construction.LatticeData

set_option linter.unusedSectionVars false

open D5.S3.Arith.Lattices.Klartag.Completion
open D5.S3.Arith.Lattices.Klartag.Construction
open D5.S3.Arith.Lattices.Klartag.Contact
open D5.S3.Arith.Lattices.Klartag.Drift
open D5.S3.Arith.Lattices.Klartag.Drift.Stopped
open D5.S3.Arith.Lattices.Klartag.Gaussian
open D5.S3.Arith.Lattices.Klartag.State
open D5.S3.Arith.Lattices.Klartag.Tail
open D5.S3.Arith.Lattices.Klartag.Walk

namespace D5.S3.Arith.Lattices.Klartag.Drift.Stopped.DriftStopped8

open MeasureTheory
open Matrix
open Finset
open Module
open D5.S3.Arith.Lattices.Klartag
open D5.S3.Arith.Lattices.Klartag.Walk.Increments
open D5.S3.Arith.Lattices.Klartag.Construction.ConstructionA
open D5.S3.Arith.Lattices.Klartag.Construction.Tiling
open D5.S3.Arith.Lattices.Klartag.State.PaddedLawSetup
open D5.S3.Arith.Lattices.Klartag.Tail.TailSideSetup2
open D5.S3.Arith.Lattices.Klartag.State.RawDataInst2
open D5.S3.Arith.Lattices.Klartag.Completion.Theorem2
open D5.S3.Arith.Lattices.Klartag.Drift.Stopped.DriftStopped7
open scoped ENNReal RealInnerProductSpace

section Reach

variable {N : ℕ}

/-- The ellipsoid's quadratic form as an inner product, so `StateBounds.lower` applies to it. -/
theorem quad_eq_inner (A : Matrix (Fin N) (Fin N) ℝ) (v : EuclideanSpace ℝ (Fin N)) :
    (A *ᵥ v.ofLp) ⬝ᵥ v.ofLp = ⟪v, Matrix.toEuclideanCLM (𝕜 := ℝ) A v⟫ := by
  rw [Matrix.inner_toEuclideanCLM]
  exact dotProduct_comm _ _

/-- **The reach.**  `StateBounds A m M` bounds the ellipsoid inside the ball of radius `1/√m`:
`m‖v‖² ≤ ⟪v, Av⟫ < 1`. -/
theorem norm_lt_reach {A : Matrix (Fin N) (Fin N) ℝ} {mLow M : ℝ}
    (hSB : Discharge.StateBounds A mLow M) {v : EuclideanSpace ℝ (Fin N)}
    (hv : v ∈ ChainEllipsoid.ellipsoid A) : ‖v‖ < 1 / Real.sqrt mLow := by
  have hm : 0 < mLow := hSB.mpos
  have hs : 0 < Real.sqrt mLow := Real.sqrt_pos.2 hm
  have hsq : Real.sqrt mLow ^ 2 = mLow := Real.sq_sqrt hm.le
  have hq : (A *ᵥ v.ofLp) ⬝ᵥ v.ofLp < 1 := hv
  rw [quad_eq_inner] at hq
  have h1 : mLow * ‖v‖ ^ 2 < 1 := lt_of_le_of_lt (hSB.lower v) hq
  by_contra hcon
  have hge : 1 / Real.sqrt mLow ≤ ‖v‖ := not_lt.1 hcon
  have hpos : 0 < 1 / Real.sqrt mLow := by positivity
  have hsq2 : (1 / Real.sqrt mLow) ^ 2 ≤ ‖v‖ ^ 2 := by nlinarith [hge, hpos]
  have hval : (1 / Real.sqrt mLow) ^ 2 = 1 / mLow := by rw [div_pow, one_pow, hsq]
  rw [hval] at hsq2
  have hfin : 1 ≤ ‖v‖ ^ 2 * mLow := (div_le_iff₀ hm).1 hsq2
  nlinarith [hfin, h1]

/-- A lattice point at or beyond the reach is outside the ellipsoid, with no counting at all. -/
theorem notMem_ellipsoid_of_reach {A : Matrix (Fin N) (Fin N) ℝ} {mLow M : ℝ}
    (hSB : Discharge.StateBounds A mLow M) {v : EuclideanSpace ℝ (Fin N)}
    (hv : 1 / Real.sqrt mLow ≤ ‖v‖) : v ∉ ChainEllipsoid.ellipsoid A :=
  fun hmem => absurd (norm_lt_reach hSB hmem) (not_lt.2 hv)

end Reach

section Shell

variable {n : ℕ}

theorem toLp_xOf_eq (α : ℝ) (y : Fin n → ℤ) :
    (WithLp.toLp 2 (xOf α y) : EuclideanSpace ℝ (Fin n)) = α • toE n y := rfl

theorem norm_toLp_xOf {α : ℝ} (hα : 0 ≤ α) (y : Fin n → ℤ) :
    ‖(WithLp.toLp 2 (xOf α y) : EuclideanSpace ℝ (Fin n))‖ = α * ‖toE n y‖ := by
  rw [toLp_xOf_eq, norm_smul, Real.norm_eq_abs, abs_of_nonneg hα]

/-- **The shell case, and it needs no probabilistic input.**  `Chain.kSet` is the set of matrices
whose ellipsoid misses the window, and `Chain.chain_fst_mem_kSet` keeps the chain inside it at every
step and on every path. -/
theorem notMem_ellipsoid_of_mem_kSet {α : ℝ} {W : Finset (Fin n → ℤ)}
    {A : EuclideanSpace ℝ (UT n)} (hA : A ∈ Chain.kSet (qC α) W) {y : Fin n → ℤ} (hy : y ∈ W) :
    (WithLp.toLp 2 (xOf α y) : EuclideanSpace ℝ (Fin n))
      ∉ ChainEllipsoid.ellipsoid (symMat A) := by
  intro hmem
  have h1 : (1 : ℝ) ≤ ⟪A, qC α y⟫ := hA y hy
  have h2 : ⟪A, qC α y⟫ = (symMat A *ᵥ xOf α y) ⬝ᵥ xOf α y :=
    ChainWiring.inner_qUT_eq_quad A (xOf α y)
  have h3 : (symMat A *ᵥ xOf α y) ⬝ᵥ xOf α y < 1 := hmem
  rw [h2] at h1
  linarith

end Shell

section Assembly

variable {m p : ℕ}

theorem chainOutput_of_state (hm0 : m ≠ 0) {α : ℝ} {g : Fin (m + 1) → ZMod p}
    {A : EuclideanSpace ℝ (UT (m + 1))} {mLow M C' : ℝ}
    (hSB : Discharge.StateBounds (symMat A) mLow M)
    (hlog : ChainWiring.logDet A ≤ C' - 4 * Real.log ((m + 1 : ℕ) : ℝ))
    (havoid : ∀ y : Fin (m + 1) → ℤ, y ≠ 0 → y ∈ latZ p (m + 1) g →
      (WithLp.toLp 2 (xOf α y) : EuclideanSpace ℝ (Fin (m + 1)))
        ∉ ChainEllipsoid.ellipsoid (symMat A)) :
    Assembly.ChainOutput α g (Real.exp (-C' / 2)) := by
  obtain ⟨S, hSherm, hSA⟩ := hSB.congr
  have hST : Sᵀ = S := GoodEvent.isSymm_of_isHermitian hSherm
  have hdet : 0 < (symMat A).det := hSB.posDef.det_pos
  have hmR : (0 : ℝ) < (m : ℝ) := by
    have : 0 < m := Nat.pos_of_ne_zero hm0
    exact_mod_cast this
  have hmono : Real.log ((m : ℝ)) ≤ Real.log (((m + 1 : ℕ) : ℝ)) := by
    refine Real.log_le_log hmR ?_
    exact_mod_cast Nat.le_succ m
  have hlog' : Real.log ((symMat A).det) ≤ C' - 4 * Real.log ((m : ℕ) : ℝ) := by
    rw [ChainWiring.logDet] at hlog
    linarith
  have hsd : Real.sqrt ((symMat A).det) ≤ Real.exp (C' / 2) / (m : ℝ) ^ 2 :=
    Assembly.sqrt_det_le hdet hm0 hlog'
  refine ⟨symMat A, S, hdet, by rw [hST]; exact hSA, ?_, ?_⟩
  · have hexp : Real.exp (C' / 2) * Real.exp (-C' / 2) = 1 := by
      rw [← Real.exp_add, show C' / 2 + -C' / 2 = 0 by ring, Real.exp_zero]
    have hnn : (0 : ℝ) ≤ Real.exp (-C' / 2) * (m : ℝ) ^ 2 := by positivity
    have hstep : Real.sqrt ((symMat A).det) * (Real.exp (-C' / 2) * (m : ℝ) ^ 2)
        ≤ (Real.exp (C' / 2) / (m : ℝ) ^ 2) * (Real.exp (-C' / 2) * (m : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_right hsd hnn
    have hval : (Real.exp (C' / 2) / (m : ℝ) ^ 2) * (Real.exp (-C' / 2) * (m : ℝ) ^ 2)
        = Real.exp (C' / 2) * Real.exp (-C' / 2) := by field_simp
    rw [hval, hexp] at hstep
    exact hstep
  · rintro x ⟨v, hv, rfl⟩ hx0
    obtain ⟨y, hy, rfl⟩ := hv
    have hxeq : α • (toReal (m + 1) y) = xOf α y := by
      funext i
      simp only [xOf, Pi.smul_apply, smul_eq_mul, toReal_apply]
    have hy0 : y ≠ 0 := by
      rintro rfl
      exact hx0 (by simp)
    show (WithLp.toLp 2 (α • (toReal (m + 1) y)) : EuclideanSpace ℝ (Fin (m + 1)))
        ∉ ChainEllipsoid.ellipsoid (symMat A)
    rw [hxeq]
    exact havoid y hy0 hy

end Assembly

section Side

end Side

section Adopted

end Adopted

end D5.S3.Arith.Lattices.Klartag.Drift.Stopped.DriftStopped8
