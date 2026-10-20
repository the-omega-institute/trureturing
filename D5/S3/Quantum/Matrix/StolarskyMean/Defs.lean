/- GID: D5/S3/Quantum/Matrix/StolarskyMean/Defs
   generality: G
   mirror-B: D5/B/S3/Quantum/Matrix/StolarskyMean/Defs
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.Matrix.Spectrum, mathlib/module/Mathlib.Analysis.SpecialFunctions.Pow.Real]
   utility: none
   digest: Stolarsky means, their finite matrices, and the positive eigenvalue class. -/

import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.SpecialFunctions.Pow.Real

noncomputable section

namespace D5.S3.Quantum.Matrix.StolarskyMean.Defs

noncomputable def stolarsky (γ a b : ℝ) : ℝ :=
  if a = b then a
  else if γ = 0 then (a - b) / (Real.log a - Real.log b)
  else if γ = 1 then Real.exp ((a * Real.log a - b * Real.log b) / (a - b) - 1)
  else ((a ^ γ - b ^ γ) / (γ * (a - b))) ^ (1 / (γ - 1))

noncomputable def stolarskyMatrix (γ : ℝ) {n : ℕ} (l : Fin n → ℝ) :
    _root_.Matrix (Fin n) (Fin n) ℝ := fun i j => stolarsky γ (l i) (l j)

noncomputable def numPosEig {n : ℕ} (M : _root_.Matrix (Fin n) (Fin n) ℝ) : ℕ :=
  if h : M.IsHermitian then
    (Finset.univ.filter fun i => 0 < h.eigenvalues i).card else 0

def InClassA {n : ℕ} (M : _root_.Matrix (Fin n) (Fin n) ℝ) : Prop :=
  (∀ i j, 0 < M i j) ∧ numPosEig M = 1

def claim : Prop :=
  (∀ γ : ℝ, 2 ≤ γ → ∀ (n : ℕ) (l : Fin (n + 1) → ℝ),
    (∀ i, 0 < l i) → InClassA (stolarskyMatrix γ l)) ∧
  (∀ γ : ℝ, 0 ≤ γ → γ < 2 → ∃ (n : ℕ) (l : Fin n → ℝ),
    (∀ i, 0 < l i) ∧ ¬ InClassA (stolarskyMatrix γ l))

end D5.S3.Quantum.Matrix.StolarskyMean.Defs
