/- GID: D5/S3/Arith/Lattices/Klartag/Walk/ChainInputDom
   generality: G
   mirror-B: D5/B/S3/Arith/Lattices/Klartag/Walk/ChainInputDom
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Gaussian matrix walk, filtration and stopped increments. -/

/- Copyright 2026 Lean FRO, LLC. Licensed under Apache-2.0.
   Source: mlgraham/lean-eval-klartag-submission, commit
   270b3358a135f64a6688636660c07772e8db0173.
   Attribution and full license: Library/QuadraticForms/klartag2025packing.md. -/

import D5.S3.Arith.Lattices.Klartag.Contact.Lemma43Uniform
import D5.S3.Arith.Lattices.Klartag.State.Padding

open D5.S3.Arith.Lattices.Klartag.Completion
open D5.S3.Arith.Lattices.Klartag.Construction
open D5.S3.Arith.Lattices.Klartag.Gaussian
open D5.S3.Arith.Lattices.Klartag.Walk

namespace D5.S3.Arith.Lattices.Klartag

open MeasureTheory
open Set
open Real
open D5.S3.Arith.Lattices.Klartag.Walk.ChainDataInst
open D5.S3.Arith.Lattices.Klartag.Construction.Tiling
open D5.S3.Arith.Lattices.Klartag.Construction.Section5
open D5.S3.Arith.Lattices.Klartag.Construction.ConstructionA
open scoped ENNReal NNReal

/-- The un-widened profile: `profile` evaluated at the lattice point's own radius.  `profile`'s
argument is already shifted inward by `√n/2`, so undoing that shift is adding `√n/2`. -/
noncomputable def profileAt (a₀ α W : ℝ) (n : ℕ) (t r : ℝ) : ℝ :=
  profile a₀ α W n t (r + Real.sqrt n / 2)

theorem profileAt_antitone {a₀ α W : ℝ} {n : ℕ} {t : ℝ} (hα : 0 < α) (ht : 0 < t) :
    Antitone (profileAt a₀ α W n t) := by
  intro r₁ r₂ h
  show profile a₀ α W n t (r₂ + Real.sqrt n / 2) ≤ profile a₀ α W n t (r₁ + Real.sqrt n / 2)
  exact profile_antitone hα ht (by linarith)

theorem profileAt_eq_Phi {a₀ α W : ℝ} {n : ℕ} {t r : ℝ}
    (hW : r + Real.sqrt n / 2 ≤ W) (hr : 0 < α * r)
    (hy : 0 < yOf a₀ t (α * r)) :
    profileAt a₀ α W n t r = Phi (yOf a₀ t (α * r)) := by
  have hadd : r + Real.sqrt n / 2 - Real.sqrt n / 2 = r := by ring
  unfold profileAt profile
  rw [if_neg (not_lt.2 hW), hadd, if_neg (not_le.2 hr), PhiC_of_pos hy]

end D5.S3.Arith.Lattices.Klartag
