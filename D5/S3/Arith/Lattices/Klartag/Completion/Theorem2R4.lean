/- GID: D5/S3/Arith/Lattices/Klartag/Completion/Theorem2R4
   generality: G
   mirror-B: D5/B/S3/Arith/Lattices/Klartag/Completion/Theorem2R4
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Uniform constants and completion of lattice packing. -/

/- Copyright 2026 Lean FRO, LLC. Licensed under Apache-2.0.
   Source: mlgraham/lean-eval-klartag-submission, commit
   270b3358a135f64a6688636660c07772e8db0173.
   Attribution and full license: Library/QuadraticForms/klartag2025packing.md. -/

import D5.S3.Arith.Lattices.Klartag.Drift.Stopped.DriftStopped8R5
import D5.S3.Arith.Lattices.Klartag.Tail.TailAtStepR2W2
import D5.S3.Arith.Lattices.Klartag.Tail.TailSideSetup3W2
import D5.S3.Arith.Lattices.Klartag.Drift.Stopped.DriftStopped8
import Mathlib
import D5.S3.Arith.Lattices.Klartag.Completion.Theorem2
import D5.S3.Arith.Lattices.Klartag.Construction.LatticeData
import D5.S3.Arith.Lattices.Klartag.Construction.LatticeDataR
import D5.S3.Arith.Lattices.Klartag.Tail.TailSideSetup3
import D5.S3.Arith.Lattices.Klartag.Tail.TailAtStep
import D5.S3.Arith.Lattices.Klartag.Walk.ChainInputDom
import D5.S3.Arith.Lattices.Klartag.Completion.WindowR
import D5.S3.Arith.Lattices.Klartag.Contact.ThetaTight
import D5.S3.Arith.Lattices.Klartag.Completion.GoodPathLight
import D5.S3.Arith.Lattices.Klartag.Tail.TailAtStepR5W2
import D5.S3.Arith.Lattices.Klartag.Drift.Stopped.DriftStopped6c

set_option linter.unusedSectionVars false

open MeasureTheory
open Finset

open D5.S3.Arith.Lattices.Klartag.Completion
open D5.S3.Arith.Lattices.Klartag.Construction
open D5.S3.Arith.Lattices.Klartag.Contact
open D5.S3.Arith.Lattices.Klartag.Drift
open D5.S3.Arith.Lattices.Klartag.Drift.Stopped
open D5.S3.Arith.Lattices.Klartag.Gaussian
open D5.S3.Arith.Lattices.Klartag.Lemma43R
open D5.S3.Arith.Lattices.Klartag.Lemma43R2
open D5.S3.Arith.Lattices.Klartag.Lemma43R3
open D5.S3.Arith.Lattices.Klartag.State
open D5.S3.Arith.Lattices.Klartag.Tail
open D5.S3.Arith.Lattices.Klartag.Walk

namespace D5.S3.Arith.Lattices.Klartag.Completion.Theorem2R4

open scoped ENNReal RealInnerProductSpace
open D5.S3.Arith.Lattices.Klartag
open D5.S3.Arith.Lattices.Klartag.Walk.Increments
open D5.S3.Arith.Lattices.Klartag.Construction.Tiling
open D5.S3.Arith.Lattices.Klartag.Completion.Assembly
open D5.S3.Arith.Lattices.Klartag.Walk.ChainDataInst
open D5.S3.Arith.Lattices.Klartag.Construction.ConstructionA
open D5.S3.Arith.Lattices.Klartag.State.RawDataInst2
open D5.S3.Arith.Lattices.Klartag.Completion.WindowR2
open D5.S3.Arith.Lattices.Klartag.Walk.ChainSetup
open D5.S3.Arith.Lattices.Klartag.Drift.Stopped.DriftStopped8R5
open D5.S3.Arith.Lattices.Klartag.Tail.TailAtStepR5W2

/-- **The combined `profileAt` weight.**  No chain, no `g`, no record: a function of `(A, B, α, m)`
alone.  This is the weight the light-contact hypothesis is stated at. -/
noncomputable def wComb (A B : ℝ) (_p m : ℕ) (α : ℝ) : (Fin (m + 1) → ℤ) → ℝ≥0∞ :=
  fun y => ENNReal.ofReal A * wProf α (m + 1) y + ENNReal.ofReal B * wProfT α (m + 1) y

/-- The canonical `ChainRaw3` at the adopted data: the reach-2 chain record, weights swapped. -/
noncomputable def QOf {p m : ℕ} {α : ℝ} (hn : 3 ≤ m + 1)
    (hraw : PaddedLawSetupRW2.RawDataR p (m + 1) α ((1 - 1 / ((m + 1 : ℕ) : ℝ)) / α)
      (qC α) (RawDataInst2RW2.shellR α (m + 1)) (A0C (m + 1)))
    (hnd : TailSideSetup2.NormData (m + 1) α (qC α)
      (RawDataInst2RW2.shellR α (m + 1)) (A0C (m + 1))) : ChainRaw3 p (m + 1) :=
  chainRaw3_of_raw2 (PaddedLawSetupRW2.chainRaw2_on_setupR hn hraw
    (TailSideSetup3W2.tailSideHyp_of_rawDataR hraw hnd hn))

/-- The combined threshold family, in the shape `paramsProducer3` returns. -/
noncomputable def θ3 (A B : ℝ) (p m : ℕ) (α : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (ThetaTight.thetaTight p (m + 1) (C3 (m + 1) A B α))

/-- `c3Adopted''` clamped below the threshold, so the unrestricted admissibility facts hold. -/
noncomputable def c3clamp (n : ℕ) : ℝ :=
  if 2073600 ≤ n then DriftStopped6c.c3Adopted'' n else 0

theorem c3clamp_nonneg (n : ℕ) : 0 ≤ c3clamp n := by
  rw [c3clamp]; split
  · exact DriftStopped6c.c3_adopted_nonnegative n
  · exact le_refl 0

theorem c3clamp_eta_le (n : ℕ) :
    c3clamp n * DriftStopped6.etaAdopted n ≤ 1 / 4 := by
  rw [c3clamp]; split
  · rename_i h; exact DriftStopped6c.c3Adopted''_eta_le h
  · rw [zero_mul]; norm_num

theorem c3clamp_eq {n : ℕ} (hn : 2073600 ≤ n) : c3clamp n = DriftStopped6c.c3Adopted'' n := by
  rw [c3clamp, if_pos hn]

end D5.S3.Arith.Lattices.Klartag.Completion.Theorem2R4
