/- GID: D5/S3/Quantum/Matrix/JainAbsCosine/Defs
   generality: G
   mirror-B: D5/B/S3/Quantum/Matrix/JainAbsCosine/Defs
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.SpecialFunctions.Pow.Real, mathlib/module/Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic, mathlib/module/Mathlib.LinearAlgebra.Matrix.Charpoly.Basic, mathlib/module/Mathlib.Algebra.Polynomial.Div]
   utility: none
   digest: Absolute cosine powers, their real Fourier modes, and the multiplicity claim. -/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.Algebra.Polynomial.Div

open scoped BigOperators

namespace D5.S3.Quantum.Matrix.JainAbsCosine.Defs

noncomputable def angle (m : ℕ) : ℝ := Real.pi / (2 * (m : ℝ) + 1)

noncomputable def absCosPow (m : ℕ) (r : ℝ) :
    Matrix (Fin (2 * m + 1)) (Fin (2 * m + 1)) ℝ :=
  fun a b => |Real.cos ((((a : ℕ) : ℝ) - ((b : ℕ) : ℝ)) * angle m)| ^ r

noncomputable def modeValue (m j : ℕ) (r : ℝ) : ℝ :=
  1 + 2 * ∑ l ∈ Finset.Icc 1 m,
    Real.cos (2 * (j : ℝ) * (l : ℝ) * angle m) * Real.cos ((l : ℝ) * angle m) ^ r

noncomputable def rootProduct (j : ℕ) (r : ℝ) : ℝ :=
  ∏ s ∈ Finset.range j, (r - 2 * (s : ℝ))

def claim : Prop :=
  ∀ (m : ℕ) (r μ : ℝ), 1 ≤ m → 0 ≤ r → (absCosPow m r).charpoly.IsRoot μ → μ ≠ 0 →
    μ ≠ modeValue m 0 r → (absCosPow m r).charpoly.rootMultiplicity μ = 2

end D5.S3.Quantum.Matrix.JainAbsCosine.Defs
