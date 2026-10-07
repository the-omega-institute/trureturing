/- GID: D5/S3/Arith/Lattices/Klartag/Walk/ChainWalkRW2
   generality: G
   mirror-B: D5/B/S3/Arith/Lattices/Klartag/Walk/ChainWalkRW2
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Gaussian matrix walk, filtration and stopped increments. -/

/- Copyright 2026 Lean FRO, LLC. Licensed under Apache-2.0.
   Source: mlgraham/lean-eval-klartag-submission, commit
   270b3358a135f64a6688636660c07772e8db0173.
   Attribution and full license: Library/QuadraticForms/klartag2025packing.md. -/

import D5.S3.Arith.Lattices.Klartag.Walk.ChainWalk
import D5.S3.Arith.Lattices.Klartag.State.PaddingMap
import D5.S3.Arith.Lattices.Klartag.Tail.TailTransportRW2

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

namespace D5.S3.Arith.Lattices.Klartag

open MeasureTheory
open Set
open Real
open D5.S3.Arith.Lattices.Klartag.Walk.Chain
open D5.S3.Arith.Lattices.Klartag.Construction.Tiling
open D5.S3.Arith.Lattices.Klartag.Construction.Section5
open D5.S3.Arith.Lattices.Klartag.Construction.ConstructionA
open D5.S3.Arith.Lattices.Klartag.Walk.ChainDataInst
open D5.S3.Arith.Lattices.Klartag.Completion.WindowR2
open scoped ENNReal RealInnerProductSpace

variable {n : ℕ} {Ωc : Type*} [MeasurableSpace Ωc] {P : Measure Ωc} [IsProbabilityMeasure P]
variable {Ec : Type*} [NormedAddCommGroup Ec] [InnerProductSpace ℝ Ec] [FiniteDimensional ℝ Ec]
variable {q : (Fin n → ℤ) → Ec} {W : Finset (Fin n → ℤ)} {A₀ : Ec} {ξ : ℕ → Ωc → Ec} {α : ℝ}

theorem hsteps_of_walkRW2
    (hq : ∀ j : (Fin n → ℤ), ∀ i ∈ W, (0 : ℝ) ≤ ⟪q i, q j⟫)
    (hA₀ : ∀ y ∈ W, (1 : ℝ) < ⟪A₀, q y⟫)
    (hwin : ∀ y ∈ W, ‖toE n y‖ + Real.sqrt n / 2 ≤ windowR2 α n)
    (hr : ∀ y ∈ W, 0 < α * ‖toE n y‖)
    (hy : ∀ k, k < ParamsAdopted2.numStepsAdopted2 n → k ≠ 0 → ∀ y ∈ W,
      0 < yOf (a0C n) ((k : ℝ) * ParamsAdopted2.stepSizeAdopted2 n) (α * ‖toE n y‖))
    (hprop : ∀ k, k < ParamsAdopted2.numStepsAdopted2 n → k ≠ 0 → ∀ y ∈ W,
      P {ω | ∃ i ≤ k, constraintM q W A₀ ξ y i ω ≤ 0}
        ≤ ENNReal.ofReal (4 * Phi (yOf (a0C n)
            ((k : ℝ) * ParamsAdopted2.stepSizeAdopted2 n) (α * ‖toE n y‖)))) :
    ∀ k, k < ParamsAdopted2.numStepsAdopted2 n → ∀ y ∈ W,
      P.real {ω | y ∈ contactSet q W A₀ ξ k ω}
        ≤ 4 * profStepRW2 α n (ParamsAdopted2.stepSizeAdopted2 n) y k :=
  tail_at_step_mu_rw2 (contactSet q W A₀ ξ) W (constraintM q W A₀ ξ) hwin hr hy
    (fun k _ y _ => chain_hhit hq k y) hprop
    (contact_zero_of_gap (contactSet q W A₀ ξ) W (constraintM q W A₀ ξ)
      (fun y _ => chain_hhit hq 0 y)
      (fun y hy' ω => chain_hgap (hA₀ y hy') ω))

/-- **`ChainRaw2RW2` from the chain**, with `w = intWeight` and `tail` discharged.  The thirteen
remaining arguments are §5 arithmetic and the chain's own lattice data. -/
noncomputable def chainRaw2_of_walkRW2 {p : ℕ} (hn : 3 ≤ n)
    (hq : ∀ j : (Fin n → ℤ), ∀ i ∈ W, (0 : ℝ) ≤ ⟪q i, q j⟫)
    (hA₀ : ∀ y ∈ W, (1 : ℝ) < ⟪A₀, q y⟫)
    (alpha_pos : 0 < α)
    (alpha_norm : α ^ n * ((p ^ (n - 1) : ℕ) : ℝ) = kappa n)
    (R : ℝ) (R_nonneg : 0 ≤ R) (R_scaled : α * R ≤ 1 - 1 / (n : ℝ)) (R_lt_p : R < (p : ℝ))
    (tiling_defect : (n : ℝ) * (α * Real.sqrt n / 2) ≤ 1 / 4)
    (window_lt_p : windowR2 α n < (p : ℝ))
    (supp_ne_zero : ∀ y ∈ W, y ≠ 0)
    (supp_radius : ∀ y ∈ W, ‖toE n y‖ ≤ windowR2 α n)
    (hwin : ∀ y ∈ W, ‖toE n y‖ + Real.sqrt n / 2 ≤ windowR2 α n)
    (hr : ∀ y ∈ W, 0 < α * ‖toE n y‖)
    (hy : ∀ k, k < ParamsAdopted2.numStepsAdopted2 n → k ≠ 0 → ∀ y ∈ W,
      0 < yOf (a0C n) ((k : ℝ) * ParamsAdopted2.stepSizeAdopted2 n) (α * ‖toE n y‖))
    (hprop : ∀ k, k < ParamsAdopted2.numStepsAdopted2 n → k ≠ 0 → ∀ y ∈ W,
      P {ω | ∃ i ≤ k, constraintM q W A₀ ξ y i ω ≤ 0}
        ≤ ENNReal.ofReal (4 * Phi (yOf (a0C n)
            ((k : ℝ) * ParamsAdopted2.stepSizeAdopted2 n) (α * ‖toE n y‖))))
    (arith : (n : ℝ) * kappa n * ((p : ℝ) - 1) * (8 - 8 / (n : ℝ) ^ 2)
      < 8 * ((p : ℝ) ^ n - 1)) :
    ChainRaw2RW2 p n :=
  chainRaw2_of_chainRW2 (μ := P) hn (contactSet q W A₀ ξ) α alpha_pos alpha_norm R R_nonneg
    R_scaled R_lt_p tiling_defect window_lt_p W supp_ne_zero supp_radius
    (fun y hy' k hk => hsteps_of_walkRW2 hq hA₀ hwin hr hy hprop k hk y hy') arith

end D5.S3.Arith.Lattices.Klartag
