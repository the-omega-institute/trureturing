/- GID: D5/S3/Analytic/BesselRedheffer/Result
   generality: G
   mirror-B: D5/B/S3/Analytic/BesselRedheffer/Result
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The universal Redheffer lower bound fails for every normalized Bessel order at least thirty. -/

import D5.S3.Analytic.BesselRedheffer.Expansion
import D5.S3.Analytic.BesselRedheffer.FirstZero

open D5.S3.Analytic.BesselRedheffer.Defs
open D5.S3.Analytic.BesselRedheffer.Expansion
open D5.S3.Analytic.BesselRedheffer.FirstZero

namespace D5.S3.Analytic.BesselRedheffer.Result

/-- Every real order at least thirty has a strict counterexample below its first zero. -/
theorem failure_family : ∀ ν : ℝ, 30 ≤ ν → ∃ x : ℝ,
    0 < x ∧ x < firstZero ν ∧ nbessel (ν + 1) x / nbessel ν x <
      (firstZero ν ^ 2 / (firstZero ν ^ 2 - x ^ 2)) ^
        (firstZero ν ^ 2 / (4 * (ν + 1) * (ν + 2))) := by
  intro ν hν
  obtain ⟨ε, hε, H⟩ := failure_of_energy_bound hν (firstZero_pos hν) (firstZero_sq_le hν)
  have hx0 : 0 < ε / 2 := by linarith
  obtain ⟨hxj, hgap⟩ := H (ε / 2) hx0 (by linarith)
  exact ⟨ε / 2, hx0, hxj, hgap⟩

/-- The conjectured universal Redheffer lower bound is false. -/
theorem result : ¬ claim := by
  obtain ⟨x, hx0, hxj, hgap⟩ := failure_family 30 (by norm_num)
  intro h
  have hc := h 30 (by norm_num) x (by rwa [abs_of_pos hx0])
  exact (not_lt_of_ge hc) hgap

end D5.S3.Analytic.BesselRedheffer.Result
