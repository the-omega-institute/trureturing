/- GID: D5/S3/Combinatorics/MinimalForts/BlockParameters
   generality: I
   mirror-B: D5/B/S3/Combinatorics/MinimalForts/BlockParameters
   mirror-E: none(waiver:logarithmic-parameter-proof)
   anchors: [mathlib/module/Mathlib.Analysis.SpecialFunctions.Log.Basic]
   utility: none
   digest: The actual block logarithms have an interior target slope and feasible multiplicities in every residue. -/

import D5.S3.Combinatorics.MinimalForts.LogRotation
import D5.S3.Combinatorics.MinimalForts.SimplexApproximation

/-! Logarithmic parameters for all six vertex-order residues. -/

noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.MinimalForts.BlockParameters

open Filter Topology

/-- The exponential growth base. -/
def rate : ℝ := 3 / 2

/-- The logarithmic increment of replacing two triangles by a complete six-block. -/
def negativeIncrement : ℝ := Real.log (2 / 3 : ℝ)

/-- The logarithmic increment of replacing two triangles by an octahedron. -/
def positiveIncrement : ℝ := Real.log (4 / 3 : ℝ)

/-- The required increment per six vertices. -/
def slope : ℝ := 6 * Real.log rate - Real.log 9

/-- The correction for the final complete block and universal root. -/
def offset (r : Fin 6) : ℝ := ((r.val : ℝ) + 3) * Real.log rate -
  Real.log ((r.val : ℝ) + 2)

private theorem slope_bounds : 0 < slope ∧ slope < positiveIncrement := by
  have h9 : Real.log (9 : ℝ) < Real.log (rate ^ 6) :=
    Real.log_lt_log (by norm_num) (by norm_num [rate])
  have h12 : Real.log (rate ^ 6) < Real.log (12 : ℝ) :=
    Real.log_lt_log (by norm_num [rate]) (by norm_num [rate])
  have hlog : Real.log (12 : ℝ) - Real.log 9 = positiveIncrement := by
    rw [← Real.log_div (by norm_num) (by norm_num)]
    norm_num [positiveIncrement]
  rw [Real.log_pow] at h9 h12
  norm_num only [Nat.cast_ofNat] at h9 h12
  dsimp [slope]
  constructor <;> linarith

/-- One feasible sequence for each of the six order residues, with its actual log error. -/
theorem residue_sequences :
    ∃ x y z : Fin 6 → ℕ → ℕ,
      (∀ r k, x r k + y r k + z r k = k) ∧
      ∀ r, Tendsto (fun k => (x r k : ℝ) * negativeIncrement +
        (z r k : ℝ) * positiveIncrement - ((k : ℝ) * slope + offset r))
        atTop (𝓝 0) := by
  have H (r : Fin 6) := SimplexApproximation.simplex_approximation_sequence
    positiveIncrement negativeIncrement slope (offset r)
    (Real.log_pos (by norm_num)) (Real.log_neg (by norm_num) (by norm_num))
    slope_bounds.1 slope_bounds.2 LogRotation.ratio_irrational
  choose x y z hsum hlim using H
  exact ⟨x, y, z, hsum, hlim⟩

end D5.S3.Combinatorics.MinimalForts.BlockParameters
