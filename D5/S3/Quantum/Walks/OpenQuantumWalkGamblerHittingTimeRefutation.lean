/- GID: D5/S3/Quantum/Walks/OpenQuantumWalkGamblerHittingTimeRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/Walks/OpenQuantumWalkGamblerHittingTimeRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Walks/OpenQuantumWalkGamblerHittingTimeRefutation.claim; result=D5/S3/Quantum/Walks/OpenQuantumWalkGamblerHittingTimeRefutation.result; claim=D5/S3/Quantum/Walks/OpenQuantumWalkGamblerHittingTimeRefutation.claim
   digest: A complex reset pair separates states invisible to the proposed mean hitting time. -/

import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Data.Complex.Basic
import Mathlib.Data.List.Sections
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Tactic

set_option autoImplicit false

noncomputable section

namespace D5.S3.Quantum.Walks.OpenQuantumWalkGamblerHittingTimeRefutation

open scoped BigOperators ComplexOrder Matrix

/-- Time-ordered branch operator; `true` is a right step and the last step acts first. -/
def wordOperator (l r : Matrix (Fin 2) (Fin 2) ℂ) (w : List Bool) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  (w.map (fun b => if b then r else l)).reverse.prod

/-- Position after the first `t` letters, using integer positions to retain left steps. -/
def position (k : ℕ) (w : List Bool) (t : ℕ) : ℤ :=
  (k : ℤ) + ((w.take t).map (fun b => if b then (1 : ℤ) else -1)).sum

/-- The path is interior before its final step and reaches a boundary on that step. -/
def firstAbsorbs (m k : ℕ) (w : List Bool) : Prop :=
  (∀ t, t < w.length → 0 < position k w t ∧ position k w t < (m : ℤ)) ∧
    (position k w w.length = 0 ∨ position k w w.length = (m : ℤ))

/-- Sum of unnormalized branch probabilities over all words first absorbed at time `n`. -/
def absorbedMass (l r : Matrix (Fin 2) (Fin 2) ℂ) (m k : ℕ)
    (ρ : Matrix (Fin 2) (Fin 2) ℂ) (n : ℕ) : ℝ := by
  classical
  exact (((List.replicate n [false, true]).sections).map (fun w =>
    if firstAbsorbs m k w then
      (Matrix.trace (wordOperator l r w * ρ * (wordOperator l r w)ᴴ)).re else 0)).sum

/-- Extended nonnegative expectation of the first absorption time. -/
def meanHittingTime (l r : Matrix (Fin 2) (Fin 2) ℂ) (m k : ℕ)
    (ρ : Matrix (Fin 2) (Fin 2) ℂ) : ℝ≥0∞ :=
  ∑' n : ℕ, (n : ℝ≥0∞) * ENNReal.ofReal (absorbedMass l r m k ρ n)

/-- The Jacq–Lardizabal mean-hitting-time conjecture for complex two-dimensional OQWs. -/
def claim : Prop :=
  ∀ l r : Matrix (Fin 2) (Fin 2) ℂ, lᴴ * l + rᴴ * r = 1 →
    ∀ m : ℕ, 3 ≤ m → ∃ h j : ℕ → ℕ → ℝ,
      (∀ k, 1 ≤ k → k ≤ m - 1 → j m k = -j m (m - k)) ∧
      ∀ k, 1 ≤ k → k ≤ m - 1 → ∀ ρ : Matrix (Fin 2) (Fin 2) ℂ,
        ρ.PosSemidef → ρ.trace = 1 →
        meanHittingTime l r m k ρ ≠ ⊤ ∧
        (meanHittingTime l r m k ρ).toReal =
          1 + h m (m - k) * (ρ 0 0).re + h m k * (ρ 1 1).re + j m k * (ρ 0 1).re

private lemma word_operator_append (l r : Matrix (Fin 2) (Fin 2) ℂ)
    (a b : List Bool) :
    wordOperator l r (a ++ b) = wordOperator l r b * wordOperator l r a := by
  sorry

private lemma stopped_word_zero (l r : Matrix (Fin 2) (Fin 2) ℂ)
    (hz : l * r = 0) (w : List Bool) (hn : 3 ≤ w.length)
    (hw : firstAbsorbs 3 1 w) : wordOperator l r w = 0 := by
  sorry

private lemma absorbed_mass_tail (l r ρ : Matrix (Fin 2) (Fin 2) ℂ)
    (hz : l * r = 0) (n : ℕ) (hn : 3 ≤ n) : absorbedMass l r 3 1 ρ n = 0 := by
  sorry

private lemma absorbed_mass_one (l r ρ : Matrix (Fin 2) (Fin 2) ℂ) :
    absorbedMass l r 3 1 ρ 1 = (Matrix.trace (l * ρ * lᴴ)).re := by
  sorry

private lemma absorbed_mass_two (l r ρ : Matrix (Fin 2) (Fin 2) ℂ) :
    absorbedMass l r 3 1 ρ 2 = (Matrix.trace ((r * r) * ρ * (r * r)ᴴ)).re := by
  sorry

private lemma mean_two_step (l r ρ : Matrix (Fin 2) (Fin 2) ℂ) (hz : l * r = 0) :
    meanHittingTime l r 3 1 ρ = ENNReal.ofReal (Matrix.trace (l * ρ * lᴴ)).re +
      2 * ENNReal.ofReal (Matrix.trace ((r * r) * ρ * (r * r)ᴴ)).re := by
  sorry

/-- The complex reset pair refutes the conjectured dependence on three real matrix entries. -/
theorem result : ¬ claim := by
  classical
  let u : Fin 2 → ℂ := ![1, Complex.I]
  let v : Fin 2 → ℂ := ![1, -Complex.I]
  let l : Matrix (Fin 2) (Fin 2) ℂ := (1 / 2 : ℂ) • Matrix.vecMulVec v (star u)
  let r : Matrix (Fin 2) (Fin 2) ℂ := (1 / 2 : ℂ) • Matrix.vecMulVec v (star v)
  let ρ : Matrix (Fin 2) (Fin 2) ℂ := (1 / 2 : ℂ) • Matrix.vecMulVec u (star u)
  let σ : Matrix (Fin 2) (Fin 2) ℂ := (1 / 2 : ℂ) • Matrix.vecMulVec v (star v)
  have hnorm : lᴴ * l + rᴴ * r = 1 := by sorry
  have hzero : l * r = 0 := by sorry
  have hρ : ρ.PosSemidef ∧ ρ.trace = 1 := by sorry
  have hσ : σ.PosSemidef ∧ σ.trace = 1 := by sorry
  have hentries : (ρ 0 0).re = (σ 0 0).re ∧ (ρ 1 1).re = (σ 1 1).re ∧
      (ρ 0 1).re = (σ 0 1).re := by sorry
  have htimes : meanHittingTime l r 3 1 ρ = 1 ∧ meanHittingTime l r 3 1 σ = 2 := by
    rw [mean_two_step l r ρ hzero, mean_two_step l r σ hzero]
    sorry
  intro hc
  obtain ⟨h, j, _, he⟩ := hc l r hnorm 3 (by omega)
  have hp := (he 1 (by omega) (by omega) ρ hρ.1 hρ.2).2
  have hm := (he 1 (by omega) (by omega) σ hσ.1 hσ.2).2
  rw [htimes.1] at hp
  rw [htimes.2] at hm
  rw [hentries.1, hentries.2.1, hentries.2.2] at hp
  norm_num at hp hm
  linarith

end D5.S3.Quantum.Walks.OpenQuantumWalkGamblerHittingTimeRefutation
