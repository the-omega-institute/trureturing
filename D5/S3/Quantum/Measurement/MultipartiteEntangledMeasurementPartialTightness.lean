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

abbrev jointIndex (n d : ℕ) := Fin n → ZMod d

/-- The winning outcome of the n-partite sum-and-difference game. -/
def winningOutcome {n d : ℕ} [NeZero n] (x y : jointIndex n d) : jointIndex n d :=
  fun k => if k = 0 then ∑ i, x i else y k - y 0

private def tensorEntry {n d : ℕ}
    (U : Fin n → ZMod d → ZMod d → Matrix (ZMod d) (ZMod d) ℂ)
    (x : jointIndex n d) (y : jointIndex n d) (i j : jointIndex n d) : ℂ :=
  ∏ k, U k (x k) (y k) (i k) (j k)

private def tensorMatrix {n d : ℕ}
    (U : Fin n → ZMod d → ZMod d → Matrix (ZMod d) (ZMod d) ℂ)
    (x : jointIndex n d) (y : jointIndex n d) :
    Matrix (jointIndex n d) (jointIndex n d) ℂ :=
  fun i j => tensorEntry U x y i j

private def tensorAdjointMatrix {n d : ℕ}
    (U : Fin n → ZMod d → ZMod d → Matrix (ZMod d) (ZMod d) ℂ)
    (x : jointIndex n d) (y : jointIndex n d) :
    Matrix (jointIndex n d) (jointIndex n d) ℂ :=
  fun i j => star (tensorEntry U x y j i)

/-- The average winning score for local unitary encodings and a joint measurement. -/
def score {n d : ℕ}
    [NeZero n] [NeZero d] [Fintype (jointIndex n d)] [DecidableEq (jointIndex n d)]
    (ρ : Matrix (jointIndex n d) (jointIndex n d) ℂ)
    (U : Fin n → ZMod d → ZMod d → Matrix (ZMod d) (ZMod d) ℂ)
    (M : jointIndex n d → Matrix (jointIndex n d) (jointIndex n d) ℂ) : ℝ :=
  ((d : ℝ) ^ (2 * n))⁻¹ *
    ∑ x, ∑ y,
      (Matrix.trace
        (tensorMatrix U x y * ρ * tensorAdjointMatrix U x y *
          M (winningOutcome x y))).re

/-- A finite sum of positive product operators is fully separable. -/
def IsFullySeparable {n d : ℕ}
    (A : Matrix (jointIndex n d) (jointIndex n d) ℂ) : Prop :=
  ∃ k : ℕ, ∃ S : Fin k → Fin n → Matrix (ZMod d) (ZMod d) ℂ,
    (∀ a v, (S a v).PosSemidef) ∧
      ∀ i j, A i j = ∑ a, ∏ v, S a v (i v) (j v)

def IsProjectiveMeasurement {n d : ℕ} [NeZero n] [NeZero d]
    [Fintype (jointIndex n d)] [DecidableEq (jointIndex n d)]
    (M : jointIndex n d → Matrix (jointIndex n d) (jointIndex n d) ℂ) : Prop :=
  (∀ b, (M b).PosSemidef ∧ M b * M b = M b) ∧ ∑ b, M b = 1

private theorem neZeroOfTwo (n : ℕ) (h : 2 ≤ n) : NeZero n :=
  ⟨by omega⟩

private def sectorBasisSpec {n d : ℕ} [NeZero n] [NeZero d]
    [Fintype (jointIndex n d)] [DecidableEq (jointIndex n d)]
    (e : ZMod d → jointIndex n d → jointIndex n d → ℂ)
    (g : ZMod d → jointIndex n d → jointIndex n d → ℂ) : Prop :=
  (∀ t r (hr : r 0 = 0) i,
      e t r i = if i = (fun k => t + r k) then 1 else 0) ∧
    (∀ a r (hr : r 0 = 0), ∑ i, Complex.normSq (g a r i) = 1)

def claim : Prop := by
  classical
  exact ∀ n d m : ℕ, 2 ≤ n → 2 ≤ d → m ≤ d ^ (n - 1) →
    letI : NeZero n := neZeroOfTwo n (by omega)
    letI : NeZero d := neZeroOfTwo d (by omega)
    letI : Fintype (ZMod d) := Fintype.ofFinite _
    letI : DecidableEq (ZMod d) := Classical.decEq _
    letI : Fintype (jointIndex n d) := Fintype.ofFinite _
    letI : DecidableEq (jointIndex n d) := Classical.decEq _
    ∃ (ρ : Matrix (jointIndex n d) (jointIndex n d) ℂ)
      (U : Fin n → ZMod d → ZMod d → Matrix (ZMod d) (ZMod d) ℂ)
      (M : jointIndex n d → Matrix (jointIndex n d) (jointIndex n d) ℂ),
      IsDensity ρ ∧
      (∀ k x y, U k x y ∈ Matrix.unitaryGroup (ZMod d) ℂ) ∧
      IsProjectiveMeasurement M ∧
      ((Finset.univ.filter (fun b => IsFullySeparable (M b))).card = d * m) ∧
      score ρ U M = ((d : ℝ) ^ n - d * m + m) / (d : ℝ) ^ n

private theorem sector_basis (n d : ℕ) [NeZero n] [NeZero d]
    [Fintype (jointIndex n d)] [DecidableEq (jointIndex n d)]
    (hn : 2 ≤ n) (hd : 2 ≤ d) :
    ∃ (e : ZMod d → jointIndex n d → jointIndex n d → ℂ)
      (g : ZMod d → jointIndex n d → jointIndex n d → ℂ),
      sectorBasisSpec e g := by sorry

private theorem sector_measurement (n d m : ℕ) [NeZero n] [NeZero d]
    [Fintype (jointIndex n d)] [DecidableEq (jointIndex n d)]
    (hb : ∃ (e : ZMod d → jointIndex n d → jointIndex n d → ℂ)
      (g : ZMod d → jointIndex n d → jointIndex n d → ℂ), sectorBasisSpec e g)
    (hn : 2 ≤ n) (hd : 2 ≤ d) (hm : m ≤ d ^ (n - 1)) :
    ∃ (R : Finset (jointIndex n d))
      (M : jointIndex n d → Matrix (jointIndex n d) (jointIndex n d) ℂ),
      R.card = m ∧ (∀ r ∈ R, r 0 = 0) ∧ IsProjectiveMeasurement M := by sorry

private theorem sector_separability_count (n d m : ℕ) [NeZero n] [NeZero d]
    [Fintype (jointIndex n d)] [DecidableEq (jointIndex n d)]
    (R : Finset (jointIndex n d))
    (M : jointIndex n d → Matrix (jointIndex n d) (jointIndex n d) ℂ)
    (hR : R.card = m) (hR0 : ∀ r ∈ R, r 0 = 0)
    (hn : 2 ≤ n) (hd : 2 ≤ d) :
    (letI : DecidablePred (fun b => IsFullySeparable (M b)) := Classical.decPred _;
      (Finset.univ.filter (fun b => IsFullySeparable (M b))).card = d * m) := by sorry

private theorem sector_score (n d m : ℕ) [NeZero n] [NeZero d]
    [Fintype (jointIndex n d)] [DecidableEq (jointIndex n d)]
    (ρ : Matrix (jointIndex n d) (jointIndex n d) ℂ)
    (U : Fin n → ZMod d → ZMod d → Matrix (ZMod d) (ZMod d) ℂ)
    (M : jointIndex n d → Matrix (jointIndex n d) (jointIndex n d) ℂ)
    (R : Finset (jointIndex n d)) (hR : R.card = m)
    (hR0 : ∀ r ∈ R, r 0 = 0)
    (hn : 2 ≤ n) (hd : 2 ≤ d) (hm : m ≤ d ^ (n - 1)) :
    score ρ U M = ((d : ℝ) ^ n - d * m + m) / (d : ℝ) ^ n := by sorry

private theorem density_witness (n d : ℕ) [NeZero n] [NeZero d]
    [Fintype (jointIndex n d)] [DecidableEq (jointIndex n d)]
    (hn : 2 ≤ n) (hd : 2 ≤ d) :
    ∃ (ρ : Matrix (jointIndex n d) (jointIndex n d) ℂ)
      (U : Fin n → ZMod d → ZMod d → Matrix (ZMod d) (ZMod d) ℂ),
      IsDensity ρ ∧ ∀ k x y, U k x y ∈ Matrix.unitaryGroup (ZMod d) ℂ := by sorry

theorem result : claim := by
  intro n d m hn hd hm
  letI : NeZero n :=
    neZeroOfTwo n (by omega)
  letI : NeZero d :=
    neZeroOfTwo d (by omega)
  letI : Fintype (ZMod d) := Fintype.ofFinite _
  letI : DecidableEq (ZMod d) := Classical.decEq _
  letI : Fintype (jointIndex n d) := Fintype.ofFinite _
  letI : DecidableEq (jointIndex n d) := Classical.decEq _
  have hb := sector_basis n d hn hd
  obtain ⟨R, M, hR, hR0, hM⟩ :=
    sector_measurement n d m hb hn hd hm
  obtain ⟨ρ, U, hρ, hU⟩ := density_witness n d hn hd
  refine ⟨ρ, U, M, hρ, hU, hM, ?_, ?_⟩
  · exact sector_separability_count n d m R M hR hR0 hn hd
  · exact sector_score n d m ρ U M R hR hR0 hn hd hm

end D5.S3.Quantum.Measurement.MultipartiteEntangledMeasurementPartialTightness
