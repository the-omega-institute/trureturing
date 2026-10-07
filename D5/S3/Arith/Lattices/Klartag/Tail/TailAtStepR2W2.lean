/- GID: D5/S3/Arith/Lattices/Klartag/Tail/TailAtStepR2W2
   generality: G
   mirror-B: D5/B/S3/Arith/Lattices/Klartag/Tail/TailAtStepR2W2
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Lattice tail bounds along the matrix walk. -/

/- Copyright 2026 Lean FRO, LLC. Licensed under Apache-2.0.
   Source: mlgraham/lean-eval-klartag-submission, commit
   270b3358a135f64a6688636660c07772e8db0173.
   Attribution and full license: Library/QuadraticForms/klartag2025packing.md. -/

import D5.S3.Arith.Lattices.Klartag.Tail.TailAtStepRW2
import D5.S3.Arith.Lattices.Klartag.Contact.ThetaTight
import D5.S3.Arith.Lattices.Klartag.Drift.Stopped.DriftStopped8
import Mathlib
import D5.S3.Arith.Lattices.Klartag.Completion.Theorem2
import D5.S3.Arith.Lattices.Klartag.Construction.LatticeData
import D5.S3.Arith.Lattices.Klartag.Construction.LatticeDataR
import D5.S3.Arith.Lattices.Klartag.Tail.TailSideSetup3

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

namespace D5.S3.Arith.Lattices.Klartag.Tail.TailAtStepR2W2

open MeasureTheory
open Set
open Real
open Finset
open scoped ENNReal NNReal
open D5.S3.Arith.Lattices.Klartag
open D5.S3.Arith.Lattices.Klartag.Walk.Increments
open D5.S3.Arith.Lattices.Klartag.Walk.ChainDataInst
open D5.S3.Arith.Lattices.Klartag.Construction.Tiling
open D5.S3.Arith.Lattices.Klartag.Construction.Section5
open D5.S3.Arith.Lattices.Klartag.Construction.ConstructionA
open D5.S3.Arith.Lattices.Klartag.Completion.WindowR2

noncomputable section

theorem markov_tight {p n : ℕ} (hn : 0 < n) (hp : 1 < p) {C : ℝ} (hC : 0 < C) :
    2 * (((p - 1 : ℕ) : ℝ≥0∞) * ENNReal.ofReal ((n : ℝ) * kappa n * C))
      < ENNReal.ofReal (ThetaTight.thetaTight p n C) * ((p ^ n - 1 : ℕ) : ℝ≥0∞) := by
  have hpR : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have hpnN : 1 < p ^ n := Nat.one_lt_pow (by omega) hp
  have hpnR : (1 : ℝ) < (p : ℝ) ^ n := by exact_mod_cast hpnN
  have hκ : 0 < kappa n := kappa_pos hn
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  have hd : (0 : ℝ) < (p : ℝ) ^ n - 1 := by linarith
  have hprod : 0 < ((p : ℝ) - 1) * (n : ℝ) * kappa n * C := by positivity
  have hkey := ThetaTight.two_mul_lt_thetaTight_mul (n := n) hpnR hprod
  have hθ0 : 0 ≤ ThetaTight.thetaTight p n C := by
    rw [ThetaTight.thetaTight]
    exact div_nonneg (by positivity) (by linarith)
  have e1 : (((p - 1 : ℕ) : ℝ≥0∞)) = ENNReal.ofReal ((p : ℝ) - 1) := by
    have hr : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by
      rw [Nat.cast_sub (le_of_lt hp), Nat.cast_one]
    rw [← ENNReal.ofReal_natCast, hr]
  have e2 : (((p ^ n - 1 : ℕ) : ℝ≥0∞)) = ENNReal.ofReal ((p : ℝ) ^ n - 1) := by
    have hr : ((p ^ n - 1 : ℕ) : ℝ) = (p : ℝ) ^ n - 1 := by
      rw [Nat.cast_sub (le_of_lt hpnN), Nat.cast_pow, Nat.cast_one]
    rw [← ENNReal.ofReal_natCast, hr]
  have hL : (2 : ℝ≥0∞) * (ENNReal.ofReal ((p : ℝ) - 1)
        * ENNReal.ofReal ((n : ℝ) * kappa n * C))
      = ENNReal.ofReal (2 * (((p : ℝ) - 1) * ((n : ℝ) * kappa n * C))) := by
    rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
      ENNReal.ofReal_mul (le_of_lt hp1)]
    norm_num
  have hR : ENNReal.ofReal (ThetaTight.thetaTight p n C) * ENNReal.ofReal ((p : ℝ) ^ n - 1)
      = ENNReal.ofReal (ThetaTight.thetaTight p n C * ((p : ℝ) ^ n - 1)) :=
    (ENNReal.ofReal_mul hθ0).symm
  rw [e1, e2, hL, hR]
  refine (ENNReal.ofReal_lt_ofReal_iff (by linarith [hkey, hprod])).2 ?_
  have hassoc : ((p : ℝ) - 1) * ((n : ℝ) * kappa n * C)
      = ((p : ℝ) - 1) * (n : ℝ) * kappa n * C := by ring
  rw [hassoc]
  exact hkey

end

end D5.S3.Arith.Lattices.Klartag.Tail.TailAtStepR2W2
