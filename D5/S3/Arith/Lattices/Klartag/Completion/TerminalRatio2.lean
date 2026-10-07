/- GID: D5/S3/Arith/Lattices/Klartag/Completion/TerminalRatio2
   generality: G
   mirror-B: D5/B/S3/Arith/Lattices/Klartag/Completion/TerminalRatio2
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Uniform constants and completion of lattice packing. -/

/- Copyright 2026 Lean FRO, LLC. Licensed under Apache-2.0.
   Source: mlgraham/lean-eval-klartag-submission, commit
   270b3358a135f64a6688636660c07772e8db0173.
   Attribution and full license: Library/QuadraticForms/klartag2025packing.md. -/

import D5.S3.Arith.Lattices.Klartag.Completion.TerminalRatio
import D5.S3.Arith.Lattices.Klartag.Completion.ExpBounds
import D5.S3.Arith.Lattices.Klartag.Drift.Stopped.DriftStopped6d

set_option linter.unusedSectionVars false

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

namespace D5.S3.Arith.Lattices.Klartag.Completion.TerminalRatio2

open D5.S3.Arith.Lattices.Klartag
open D5.S3.Arith.Lattices.Klartag.Walk.Increments
open D5.S3.Arith.Lattices.Klartag.Construction.Section5

variable {a₀ α : ℝ} {n : ℕ}

/-- **`TerminalRatio.thetaTight_terminal_le`, unconditional.** -/
theorem theta_tight_terminal_bound {p : ℕ} {b : ℝ} (hn : 2073600 ≤ n) (hα : 0 < α) (hb : 0 ≤ b)
    (hdef : (n : ℝ) * (α * Real.sqrt n / 2) ≤ 1 / 4)
    (halpha : α ^ n * ((p ^ (n - 1) : ℕ) : ℝ) = kappa n)
    (hp : 1 ≤ (p : ℝ)) (hpn : 1 ≤ ((p ^ (n - 1) : ℕ) : ℝ)) (hppos : 1 < (p : ℝ) ^ n) :
    ThetaTight.thetaTight p n (b * (Lemma43R.C1cR (a0C n) α n * (n : ℝ) ^ 2))
      ≤ 4 * b * 827 * (n : ℝ) ^ 2 :=
  TerminalRatio.thetaTight_terminal_le hn hα hb hdef halpha hp hpn hppos
    ExpBounds.exp_half_mul_KcR_le

end D5.S3.Arith.Lattices.Klartag.Completion.TerminalRatio2
