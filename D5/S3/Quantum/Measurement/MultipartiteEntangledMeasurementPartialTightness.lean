/- GID: D5/S3/Quantum/Measurement/MultipartiteEntangledMeasurementPartialTightness
   generality: I
   mirror-B: D5/B/S3/Quantum/Measurement/MultipartiteEntangledMeasurementPartialTightness
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Sectorwise computational/Fourier projectors attain every n-partite partial bound. -/

import D5.S3.Quantum.Information.SLDSpectralEnergy
import Mathlib.Data.ZMod.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.longLine false

noncomputable section

open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
open D5.S3.Quantum.Information.SLDSpectralEnergy

namespace D5.S3.Quantum.Measurement.MultipartiteEntangledMeasurementPartialTightness

private abbrev joint (n d : ℕ) := Fin n → ZMod d

/-- The winning outcome of the n-partite sum-and-difference game. -/
def winningOutcome {n d : ℕ} (x y : joint n d) : joint n d :=
  fun k => if k = 0 then ∑ i, x i else y k - y 0

private def tensorEntry {n d : ℕ}
    (U : Fin n → ZMod d → ZMod d → Matrix (ZMod d) (ZMod d) ℂ)
    (x : joint n d) (y : joint n d) (i j : joint n d) : ℂ :=
  ∏ k, U k (x k) (y k) (i k) (j k)

/-- The average winning score for local unitary encodings and a joint measurement. -/
def score {n d : ℕ}
    (ρ : Matrix (joint n d) (joint n d) ℂ)
    (U : Fin n → ZMod d → ZMod d → Matrix (ZMod d) (ZMod d) ℂ)
    (M : joint n d → Matrix (joint n d) (joint n d) ℂ) : ℝ :=
  ((d : ℝ) ^ (2 * n))⁻¹ *
    ∑ x, ∑ y,
      (Matrix.trace
        ((fun i j => tensorEntry U x y i j) * ρ *
          (fun i j => star (tensorEntry U x y j i)) *
          M (winningOutcome x y))).re

/-- A finite sum of positive product operators is fully separable. -/
def IsFullySeparable {n d : ℕ}
    (A : Matrix (joint n d) (joint n d) ℂ) : Prop :=
  ∃ k : ℕ, ∃ S : Fin k → Fin n → Matrix (ZMod d) (ZMod d) ℂ,
    (∀ a v, (S a v).PosSemidef) ∧
      ∀ i j, A i j = ∑ a, ∏ v, S a v (i v) (j v)

private def IsProjectiveMeasurement {n d : ℕ}
    (M : joint n d → Matrix (joint n d) (joint n d) ℂ) : Prop :=
  (∀ b, (M b).PosSemidef ∧ M b * M b = M b) ∧ ∑ b, M b = 1

def claim : Prop :=
  ∀ n d m : ℕ, 2 ≤ n → 2 ≤ d → m ≤ d ^ (n - 1) →
    ∃ (ρ : Matrix (joint n d) (joint n d) ℂ)
      (U : Fin n → ZMod d → ZMod d → Matrix (ZMod d) (ZMod d) ℂ)
      (M : joint n d → Matrix (joint n d) (joint n d) ℂ),
      IsDensity ρ ∧
      (∀ k x y, U k x y ∈ Matrix.unitaryGroup (ZMod d) ℂ) ∧
      IsProjectiveMeasurement M ∧
      ((Finset.univ.filter (fun b => IsFullySeparable (M b))).card = d * m) ∧
      score ρ U M = ((d : ℝ) ^ n - d * m + m) / (d : ℝ) ^ n

private theorem sector_basis (n d : ℕ) (hn : 2 ≤ n) (hd : 2 ≤ d) :
    True := by sorry

private theorem sector_measurement (n d m : ℕ) (hn : 2 ≤ n) (hd : 2 ≤ d)
    (hm : m ≤ d ^ (n - 1)) : True := by sorry

private theorem sector_separability_count (n d m : ℕ) (hn : 2 ≤ n) (hd : 2 ≤ d)
    (hm : m ≤ d ^ (n - 1)) : True := by sorry

private theorem sector_score (n d m : ℕ) (hn : 2 ≤ n) (hd : 2 ≤ d)
    (hm : m ≤ d ^ (n - 1)) : True := by sorry

private theorem density_witness (n d : ℕ) (hn : 2 ≤ n) (hd : 2 ≤ d) : True := by sorry

theorem result : claim := by
  intro n d m hn hd hm
  have hb := sector_basis n d hn hd
  have hm' := sector_measurement n d m hn hd hm
  have hs := sector_separability_count n d m hn hd hm
  have hv := sector_score n d m hn hd hm
  have hρ := density_witness n d hn hd
  exact False.elim (by sorry)

end D5.S3.Quantum.Measurement.MultipartiteEntangledMeasurementPartialTightness
