/- GID: D5/S3/Arith/Lattices/Klartag/Construction/LatticeDataRW2
   generality: G
   mirror-B: D5/B/S3/Arith/Lattices/Klartag/Construction/LatticeDataRW2
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Construction A lattices, covolumes and ellipsoid transfer. -/

/- Copyright 2026 Lean FRO, LLC. Licensed under Apache-2.0.
   Source: mlgraham/lean-eval-klartag-submission, commit
   270b3358a135f64a6688636660c07772e8db0173.
   Attribution and full license: Library/QuadraticForms/klartag2025packing.md. -/

import Mathlib
import D5.S3.Arith.Lattices.Klartag.Construction.LatticeData
import D5.S3.Arith.Lattices.Klartag.State.RawDataInst2RW2

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

namespace D5.S3.Arith.Lattices.Klartag.Construction.LatticeDataRW2

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
open D5.S3.Arith.Lattices.Klartag.State.RawDataInst2
open D5.S3.Arith.Lattices.Klartag.State.PaddedLawSetupRW2
open D5.S3.Arith.Lattices.Klartag.State.RawDataInstRW2
open D5.S3.Arith.Lattices.Klartag.State.RawDataInst2RW2
open D5.S3.Arith.Lattices.Klartag.Completion.WindowR2

noncomputable section

section Restrict

variable {n p : ℕ} {α R : ℝ} {q : (Fin n → ℤ) → EuclideanSpace ℝ (UT n)}
  {W W' : Finset (Fin n → ℤ)} {A₀ : EuclideanSpace ℝ (UT n)}

theorem rawData_monoR (h : RawDataR p n α R q W A₀) (hsub : W' ⊆ W) :
    RawDataR p n α R q W' A₀ := rawDataR_mono h hsub

/-- **`TailSideHyp` on a restricted window**, given a producer at the full window.  The producer
is a hypothesis because `TailSideSetup2.tailSideHyp_of_rawData` demands a `windowC`-shaped
`RawData`; everything else is `LatticeData.tailSideHyp_filter`'s content. -/
theorem tailSideHyp_filterR {c : ℝ} (h : RawDataR p n α R q W A₀) (hnd : NormData n α q W A₀)
    (_hn : 3 ≤ n)
    (hprod : ∀ W₁ : Finset (Fin n → ℤ), RawDataR p n α R q W₁ A₀ → NormData n α q W₁ A₀ →
      TailSideHypR n c α q W₁ A₀)
    (P : (Fin n → ℤ) → Prop) [DecidablePred P] :
    TailSideHypR n c α q (W.filter P) A₀ :=
  hprod _ (rawData_monoR h (Finset.filter_subset _ _))
    (LatticeData.normData_mono hnd (Finset.filter_subset _ _))

open Classical in
/-- The same at the lattice filter the drift side uses. -/
theorem tailSideHyp_latZR {c : ℝ} (h : RawDataR p n α R q W A₀) (hnd : NormData n α q W A₀)
    (hn : 3 ≤ n)
    (hprod : ∀ W₁ : Finset (Fin n → ℤ), RawDataR p n α R q W₁ A₀ → NormData n α q W₁ A₀ →
      TailSideHypR n c α q W₁ A₀)
    (g : Fin n → ZMod p) :
    TailSideHypR n c α q (W.filter (fun y => y ∈ latZ p n g)) A₀ :=
  tailSideHyp_filterR h hnd hn hprod _

end Restrict

section Coverage

variable {n : ℕ} {α : ℝ}

/-- **Coverage at the reach window**, with the outer radius written additively. -/
theorem mem_shellR_of_shell {y : Fin n → ℤ} (_h0 : y ≠ 0)
    (hin : (1 - 1 / (n : ℝ)) / α < ‖toE n y‖)
    (hout : ‖toE n y‖ + Real.sqrt n / 2 ≤ windowR2 α n) : y ∈ shellR α n :=
  mem_shellR.2 ⟨by linarith, hin⟩

end Coverage

section Exists

/-- **`RawDataR`, `NormData` and coverage at every dimension above the threshold**, with no
hypothesis and with `q`, `W`, `A₀` and `R` named. -/
theorem rawData_exists'R (m : ℕ) (hm : Threshold2.n₁ ≤ m) :
    ∃ (p : ℕ) (_ : Fact (Nat.Prime p)) (_ : NeZero p) (α : ℝ), 0 < α ∧ 3 ≤ m + 1 ∧
      RawDataR p (m + 1) α ((1 - 1 / ((m + 1 : ℕ) : ℝ)) / α)
          (qC α) (shellR α (m + 1)) (A0C (m + 1)) ∧
      NormData (m + 1) α (qC α) (shellR α (m + 1)) (A0C (m + 1)) ∧
      (∀ y : Fin (m + 1) → ℤ, y ≠ 0 →
        (1 - 1 / ((m + 1 : ℕ) : ℝ)) / α < ‖toE (m + 1) y‖ →
        ‖toE (m + 1) y‖ + Real.sqrt ((m + 1 : ℕ) : ℝ) / 2 ≤ windowR2 α (m + 1) →
          y ∈ shellR α (m + 1)) := by
  have hm' : 2073600 ≤ m := by simpa [Threshold2.n₁] using hm
  have h3 : 3 ≤ m + 1 := by omega
  obtain ⟨p, hp, α, hαpos, hαnorm, hαsmall, hM⟩ :=
    exists_prime_alpha_mul (by omega : 2 ≤ m + 1)
      (max (2 * reachNum2 (m + 1)) (max 1 (Real.sqrt ((m + 1 : ℕ) : ℝ))))
      (le_trans (le_max_left _ _) (le_max_right _ _))
  obtain ⟨hq, hA₀, hne0, hrad, hwin, hr, hy⟩ := lattice_fieldsR hαpos h3
  exact ⟨p, ⟨hp⟩, ⟨hp.ne_zero⟩, α, hαpos, h3,
    rawData_of_latticeR (by omega) hαpos hp.two_le hαnorm hαsmall hM hq hA₀ hne0 hrad hwin hr hy,
    normData_qC α (shellR α (m + 1)),
    fun y h0 hin hout => mem_shellR_of_shell h0 hin hout⟩

end Exists

end

end D5.S3.Arith.Lattices.Klartag.Construction.LatticeDataRW2
