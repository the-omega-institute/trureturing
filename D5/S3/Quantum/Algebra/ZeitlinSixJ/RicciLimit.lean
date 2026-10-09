/- GID: D5/S3/Quantum/Algebra/ZeitlinSixJ/RicciLimit
   generality: G
   mirror-B: D5/B/S3/Quantum/Algebra/ZeitlinSixJ/RicciLimit
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Averaged Ricci curvature of the Zeitlin metric. -/

import D5.S3.Quantum.Algebra.ZeitlinSixJ.SumRules
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Polynomial.Basic

set_option maxRecDepth 4096
set_option maxHeartbeats 800000

namespace D5.S3.Quantum.Algebra.ZeitlinSixJ.RicciLimit

open Finset Filter
open D5.S3.Quantum.Algebra.ZeitlinSixJ.Racah

noncomputable def rPlus (l N : ℕ) : ℝ :=
  (N : ℝ) / (4 / ((N : ℝ)^2 - 1)) *
    ∑ i ∈ range (N-1), ∑ j ∈ range (N-1),
      if Odd (i+1+(j+1)+l) then
        casimir l * (2*((i+1 : ℕ) : ℝ)+1) * (2*((j+1 : ℕ) : ℝ)+1) /
          (casimir (i+1) * casimir (j+1)) * W N l (i+1) (j+1)^2
      else 0

noncomputable def rMinus (l N : ℕ) : ℝ :=
  (N : ℝ) / (4 / ((N : ℝ)^2 - 1)) *
    ∑ i ∈ range (N-1), ∑ j ∈ range (N-1),
      if Odd (i+1+(j+1)+l) then
        (casimir (i+1) - casimir (j+1))^2 *
          (2*((i+1 : ℕ) : ℝ)+1) * (2*((j+1 : ℕ) : ℝ)+1) /
          (casimir (i+1) * casimir (j+1) * casimir l) * W N l (i+1) (j+1)^2
      else 0

noncomputable def rTilde (l N : ℕ) : ℝ :=
  (rPlus l N - rMinus l N) / ((N : ℝ)^2 - 1)

def claim : Prop := ∀ l : ℕ, 2 ≤ l →
  Tendsto (fun N : ℕ => rTilde l N) atTop (nhds (-((harmonic l : ℝ) - 1) / 2)) ∧
  ∃ N0 : ℕ, ∀ N ≥ N0, rTilde l N < 0

end D5.S3.Quantum.Algebra.ZeitlinSixJ.RicciLimit
