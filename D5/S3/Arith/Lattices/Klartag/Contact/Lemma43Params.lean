/- GID: D5/S3/Arith/Lattices/Klartag/Contact/Lemma43Params
   generality: G
   mirror-B: D5/B/S3/Arith/Lattices/Klartag/Contact/Lemma43Params
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Contact profile counts and accumulated projection dimension. -/

/- Copyright 2026 Lean FRO, LLC. Licensed under Apache-2.0.
   Source: mlgraham/lean-eval-klartag-submission, commit
   270b3358a135f64a6688636660c07772e8db0173.
   Attribution and full license: Library/QuadraticForms/klartag2025packing.md. -/

import D5.S3.Arith.Lattices.Klartag.Completion.HJ
import D5.S3.Arith.Lattices.Klartag.Walk.ChainDataInst

open D5.S3.Arith.Lattices.Klartag.Construction
open D5.S3.Arith.Lattices.Klartag.Walk

namespace D5.S3.Arith.Lattices.Klartag

open MeasureTheory
open Set
open Real
open D5.S3.Arith.Lattices.Klartag.Walk.ChainDataInst
open scoped ENNReal NNReal

/-- `a₀ = (1 − 1/n)⁻¹² ≥ 1` for `n ≥ 2`.  `ha₀` of `hgbound_chained`. -/
theorem params_a0_ge_one {p n : ℕ} (P : Params p n) (hn : 2 ≤ n) : 1 ≤ P.a0 := by
  have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  have h1 : (0 : ℝ) < 1 - 1 / (n : ℝ) := by
    have : 1 / (n : ℝ) ≤ 1 / 2 := by
      rw [div_le_div_iff₀ hn0 (by norm_num)]
      linarith
    linarith
  have h2 : 1 - 1 / (n : ℝ) ≤ 1 := by
    have : (0 : ℝ) ≤ 1 / (n : ℝ) := by positivity
    linarith
  have hinv : (1 : ℝ) ≤ (1 - 1 / (n : ℝ))⁻¹ := by
    rw [le_inv_comm₀ (by norm_num) h1]
    simp
  rw [P.a0_eq]
  nlinarith [hinv]

/-- **`Params` with Lemma 4.3's window pinned.**  Six fields, and nothing else. -/
structure Params' (p n : ℕ) extends Params p n where
  /-- The `y`-window's right endpoint (Klartag's `C₀√n`). -/
  Y : ℝ
  Y_nonneg : 0 ≤ Y
  /-- `hgbound_chained`'s `hWdef`: the window radius is *defined* by the substitution, not bounded. -/
  windowRadius_eq : windowRadius = radiusOf a0 alpha (Real.sqrt n / 2) T Y

  window_small : Y * Real.sqrt T ≤ 1 / 2

  n_large : 2073600 ≤ n
  /-- Lemma 4.3's profile is `Profile.profile` at these parameters. -/
  f_eq : f = profile a0 alpha windowRadius n T

/-- `Params'` inherits `a₀ ≥ 1`. -/
theorem Params'.a0_ge_one {p n : ℕ} (P : Params' p n) : 1 ≤ P.a0 :=
  params_a0_ge_one P.toParams (by have := P.n_large; omega)

theorem Params'.window_sub_pos {p n : ℕ} (P : Params' p n) {y : ℝ} (hyY : y ≤ P.Y) :
    0 < P.a0 - Real.sqrt P.T * y :=
  _root_.D5.S3.Arith.Lattices.Klartag.window_sub_pos P.a0_ge_one hyY P.window_small

theorem Params'.window_one_sub_pos {p n : ℕ} (P : Params' p n) {y : ℝ} (hyY : y ≤ P.Y) :
    0 < 1 - Real.sqrt P.T * y :=
  _root_.D5.S3.Arith.Lattices.Klartag.window_one_sub_pos hyY P.window_small

end D5.S3.Arith.Lattices.Klartag
