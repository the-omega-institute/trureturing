/- GID: D5/S3/Analytic/Interpolation/ArtificialSourceIncrementContract
   generality: G
   mirror-B: D5/B/S3/Analytic/Interpolation/ArtificialSourceIncrementContract
   mirror-E: none(waiver:analytic-inequality)
   anchors: []
   utility: none
   digest: Quartic cell perturbations of the Robin price coordinate generate positive integer pulse sources. -/

import D5.S3.Arith.Robin.MellinWeightedVariation
import D5.S1.Words.Mechanical.FloorFractShift
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open Set Filter MeasureTheory
open scoped Topology
open D5.S3.Arith.Robin.MellinWeightedVariation

namespace D5.S3.Analytic.Interpolation.ArtificialSourceIncrementContract

local notation "c" => (1 / 128 : ℝ)
local notation "q" => (fun x : ℝ => (x * Real.log x)⁻¹)
local notation "k" => weight

/-- The quartic bump has a double zero at either endpoint. -/
def eta (s : ℝ) : ℝ := s ^ 2 * (1 - s) ^ 2

/-- The local increment budget. -/
def epsilon (a : ℝ) : ℝ := Real.log a * Real.exp (-(Real.log a) ^ (1 / 4 : ℝ))

/-- The cell width for a fixed positive logarithmic excess. -/
def width (δ a : ℝ) : ℝ :=
  a ^ (3 / 4 : ℝ) * Real.exp ((Real.log a) ^ (1 / 4 : ℝ) / 2) /
    Real.sqrt (Real.log a) * (Real.log a) ^ δ

/-- The height of the cell's negative bump. -/
def amplitude (δ a : ℝ) : ℝ := c * (Real.log a) ^ (2 * δ - 1) / Real.sqrt a

/-- Conditions on the start of the half-line. -/
def Admissible (δ A : ℝ) : Prop :=
  (∀ a ∈ Ici A, 1 ≤ Real.log a ∧ epsilon a ≤ 1 ∧ 1 ≤ width δ a ∧ width δ a ≤ a) ∧
    AntitoneOn epsilon (Ici A)

/-- Consecutive cells in the adaptive grid. -/
def grid (δ A : ℝ) : ℕ → ℝ
  | 0 => A
  | j + 1 => grid δ A j + width δ (grid δ A j)

/-- The last grid point not exceeding x, with a finite search bound. -/
def cellIndex (δ A x : ℝ) : ℕ :=
  Nat.findGreatest (fun j => grid δ A j ≤ x) ⌊x - A⌋₊

/-- Polynomial continuation of the bump in one cell. -/
def cellBump (δ a x : ℝ) : ℝ :=
  -amplitude δ a * eta ((x - a) / width δ a)

/-- The assembled negative bump, extended by zero below the initial point. -/
def bump (δ A x : ℝ) : ℝ :=
  if A ≤ x then cellBump δ (grid δ A (cellIndex δ A x)) x else 0

/-- The perturbed price coordinate. -/
def coordinate (δ A x : ℝ) : ℝ := x - deriv (bump δ A) x / k x

/-- The integer-valued pulse source. -/
def source (δ A x : ℝ) : ℤ := ⌊coordinate δ A x⌋

/-- Its tail in the same Robin price coordinate. -/
def tail (δ A x : ℝ) : ℝ :=
  ∫ v in Ioi x, ((source δ A v : ℝ) - v) * k v

end D5.S3.Analytic.Interpolation.ArtificialSourceIncrementContract
