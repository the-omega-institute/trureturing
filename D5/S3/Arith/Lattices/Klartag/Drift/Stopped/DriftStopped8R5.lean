/- GID: D5/S3/Arith/Lattices/Klartag/Drift/Stopped/DriftStopped8R5
   generality: G
   mirror-B: D5/B/S3/Arith/Lattices/Klartag/Drift/Stopped/DriftStopped8R5
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Stopped log determinant drift and integrability estimates. -/

/- Copyright 2026 Lean FRO, LLC. Licensed under Apache-2.0.
   Source: mlgraham/lean-eval-klartag-submission, commit
   270b3358a135f64a6688636660c07772e8db0173.
   Attribution and full license: Library/QuadraticForms/klartag2025packing.md. -/

import D5.S3.Arith.Lattices.Klartag.Completion.WindowR2
import D5.S3.Arith.Lattices.Klartag.Drift.Stopped.DriftStopped8
import Mathlib
import D5.S3.Arith.Lattices.Klartag.Completion.Theorem2
import D5.S3.Arith.Lattices.Klartag.Construction.LatticeData
import D5.S3.Arith.Lattices.Klartag.Construction.LatticeDataR
import D5.S3.Arith.Lattices.Klartag.Tail.TailSideSetup3
import D5.S3.Arith.Lattices.Klartag.Construction.LatticeDataRW2

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

namespace D5.S3.Arith.Lattices.Klartag.Drift.Stopped.DriftStopped8R5

open MeasureTheory
open Matrix
open Finset
open Module
open D5.S3.Arith.Lattices.Klartag
open D5.S3.Arith.Lattices.Klartag.Walk.Increments
open D5.S3.Arith.Lattices.Klartag.Construction.ConstructionA
open D5.S3.Arith.Lattices.Klartag.Construction.Tiling
open D5.S3.Arith.Lattices.Klartag.Completion.WindowR2
open D5.S3.Arith.Lattices.Klartag.Completion.GoodPathBounds
open D5.S3.Arith.Lattices.Klartag.State.RawDataInst2
open scoped ENNReal RealInnerProductSpace

variable {m p : ℕ}

/-- **`DriftStopped8R.BandHypR` at the generic reach window.** -/
def BandHypR2 (p m : ℕ) (α mLow : ℝ) (g : Fin (m + 1) → ZMod p) : Prop :=
  ∀ y : Fin (m + 1) → ℤ, y ≠ 0 → y ∈ latZ p (m + 1) g →
    windowR2 α (m + 1) - Real.sqrt ((m + 1 : ℕ) : ℝ) / 2 < ‖toE (m + 1) y‖ →
    1 / Real.sqrt mLow ≤ α * ‖toE (m + 1) y‖

/-- The outer radius of the generic reach window. -/
theorem windowR2_sub (α : ℝ) (n : ℕ) :
    windowR2 α n - Real.sqrt n / 2 = reachNum2 n / α := by
  rw [windowR2_eq]; ring

/-- **The band at `windowR2`, for every admissible `c₃`.**  `mAt n c₃ ≥ mR2 n` (85a's
`mAt_ge_mR2`) and `reachNum2 n = 1/√(mR2 n)`, so a lattice point beyond the window is beyond the
reach of *any* state with lower bound `mAt n c₃`. -/
theorem bandHypR2_of_pos {α : ℝ} (hα : 0 < α) (hm : 2073600 ≤ m + 1) {c₃ : ℝ}
    (hc₃0 : 0 ≤ c₃) (hc₃ : c₃ * DriftStopped6.etaAdopted (m + 1) ≤ 1 / 4)
    (g : Fin (m + 1) → ZMod p) : BandHypR2 p m α (mAt (m + 1) c₃) g := by
  intro y _hy0 _hylat hfar
  rw [windowR2_sub] at hfar
  have hlt : reachNum2 (m + 1) < α * ‖toE (m + 1) y‖ := by
    rw [div_lt_iff₀ hα] at hfar; linarith
  have hmR2 : 0 < mR2 (m + 1) := mR2_pos hm
  have hge : mR2 (m + 1) ≤ mAt (m + 1) c₃ := mAt_ge_mR2 hm hc₃0 hc₃
  have hs : Real.sqrt (mR2 (m + 1)) ≤ Real.sqrt (mAt (m + 1) c₃) := Real.sqrt_le_sqrt hge
  have hs0 : 0 < Real.sqrt (mR2 (m + 1)) := Real.sqrt_pos.2 hmR2
  have hinv : 1 / Real.sqrt (mAt (m + 1) c₃) ≤ 1 / Real.sqrt (mR2 (m + 1)) :=
    one_div_le_one_div_of_le hs0 hs
  rw [reachNum2_eq hm] at hlt
  linarith

def BandSideAdoptedR2 (c₃ : ℕ → ℝ) : Prop :=
  ∀ m : ℕ, Threshold2.n₁ ≤ m → ∀ (p : ℕ) (α : ℝ), 0 < α → ∀ (g : Fin (m + 1) → ZMod p),
    BandHypR2 p m α (mAt (m + 1) (c₃ (m + 1))) g

/-- **`BandSideAdoptedR2` is a theorem** for every admissible threshold family. -/
theorem bandSideAdoptedR2 {c₃ : ℕ → ℝ} (hc₃0 : ∀ n, 0 ≤ c₃ n)
    (hc₃ : ∀ n, c₃ n * DriftStopped6.etaAdopted n ≤ 1 / 4) : BandSideAdoptedR2 c₃ := by
  intro m hm p α hα g
  have hm' : 2073600 ≤ m := by simpa [Threshold2.n₁] using hm
  exact bandHypR2_of_pos hα (by omega) (hc₃0 (m + 1)) (hc₃ (m + 1)) g

open Classical in
/-- `W_g` at the generic reach window, over 85b's `RawDataInst2RW2.shellR`. -/
noncomputable def windowOfR2 (α : ℝ) (p m : ℕ) (g : Fin (m + 1) → ZMod p) :
    Finset (Fin (m + 1) → ℤ) :=
  (RawDataInst2RW2.shellR α (m + 1)).filter (fun y => y ∈ latZ p (m + 1) g)

theorem mem_windowOfR2 {p m : ℕ} {α : ℝ} {g : Fin (m + 1) → ZMod p} {y : Fin (m + 1) → ℤ} :
    y ∈ windowOfR2 α p m g ↔
      y ∈ RawDataInst2RW2.shellR α (m + 1) ∧ y ∈ latZ p (m + 1) g := by
  classical
  rw [windowOfR2, Finset.mem_filter]

theorem windowOfR2_subset {p m : ℕ} {α : ℝ} {g : Fin (m + 1) → ZMod p} :
    windowOfR2 α p m g ⊆ RawDataInst2RW2.shellR α (m + 1) :=
  fun _y hy => (mem_windowOfR2.1 hy).1

open Classical in
/-- Rule 16: any other `open Classical` filter of the same predicate is this `Finset`. -/
theorem filter_eq_windowOfR2 {p m : ℕ} {α : ℝ} {g : Fin (m + 1) → ZMod p}
    [DecidablePred (fun y : Fin (m + 1) → ℤ => y ∈ latZ p (m + 1) g)] :
    (RawDataInst2RW2.shellR α (m + 1)).filter (fun y => y ∈ latZ p (m + 1) g)
      = windowOfR2 α p m g := by
  ext y
  rw [Finset.mem_filter, mem_windowOfR2]

/-- **`DriftStopped8.avoid_of_cases` at `windowR2`.** -/
theorem avoid_of_casesR2 {α : ℝ} (hα : 0 < α) {g : Fin (m + 1) → ZMod p}
    {A : EuclideanSpace ℝ (UT (m + 1))} {mLow M : ℝ}
    (hSB : Discharge.StateBounds (symMat A) mLow M)
    (hkSet : A ∈ Chain.kSet (qC α) (windowOfR2 α p m g))
    (hcov : ∀ y : Fin (m + 1) → ℤ, y ≠ 0 →
      (1 - 1 / ((m + 1 : ℕ) : ℝ)) / α < ‖toE (m + 1) y‖ →
      ‖toE (m + 1) y‖ + Real.sqrt ((m + 1 : ℕ) : ℝ) / 2 ≤ windowR2 α (m + 1) →
        y ∈ RawDataInst2RW2.shellR α (m + 1))
    (hfree : ∀ y : Fin (m + 1) → ℤ, y ≠ 0 →
      ‖toE (m + 1) y‖ ≤ (1 - 1 / ((m + 1 : ℕ) : ℝ)) / α → y ∉ latZ p (m + 1) g)
    (hband : BandHypR2 p m α mLow g) :
    ∀ y : Fin (m + 1) → ℤ, y ≠ 0 → y ∈ latZ p (m + 1) g →
      (WithLp.toLp 2 (xOf α y) : EuclideanSpace ℝ (Fin (m + 1)))
        ∉ ChainEllipsoid.ellipsoid (symMat A) := by
  intro y hy0 hylat
  by_cases hshort : ‖toE (m + 1) y‖ ≤ (1 - 1 / ((m + 1 : ℕ) : ℝ)) / α
  · exact absurd hylat (hfree y hy0 hshort)
  have hlong : (1 - 1 / ((m + 1 : ℕ) : ℝ)) / α < ‖toE (m + 1) y‖ := not_le.1 hshort
  by_cases hin : ‖toE (m + 1) y‖ + Real.sqrt ((m + 1 : ℕ) : ℝ) / 2 ≤ windowR2 α (m + 1)
  · exact DriftStopped8.notMem_ellipsoid_of_mem_kSet hkSet
      (mem_windowOfR2.2 ⟨hcov y hy0 hlong hin, hylat⟩)
  · have hfar : windowR2 α (m + 1) - Real.sqrt ((m + 1 : ℕ) : ℝ) / 2 < ‖toE (m + 1) y‖ := by
      have hgt := not_le.1 hin
      linarith
    have hreach := hband y hy0 hylat hfar
    rw [← DriftStopped8.norm_toLp_xOf hα.le y] at hreach
    exact DriftStopped8.notMem_ellipsoid_of_reach hSB hreach

end D5.S3.Arith.Lattices.Klartag.Drift.Stopped.DriftStopped8R5
