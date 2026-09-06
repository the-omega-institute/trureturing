/- GID: D5/S0/Certificates/CheckedLinearImageExamples
   generality: G
   mirror-B: D5/B/S0/Certificates/CheckedLinearImageExamples
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Capped four-cell payloads exercise real image certification and mutation rejection. -/

import D5.S0.Certificates.CheckedLinearImage

/-!
# Concrete replay and mutation checks

The paper's positive capped-coupling fixture and its inconsistent fixture are
checked from raw rational data. Real image soundness and real infeasibility
consume the checker, while four mutations test its authoritative-input boundary.
The coordinate order is 00, 01, 10, 11. Rows are four nonnegativity rows,
normalization in both directions, both marginals in both directions, and cap.
These fixtures test certificate replay; structural semantics is a separate task.

Library search: no CheckedLinearImageExamples or matching numeric payload was
found in D5. Finite rational decisions use Lean kernel reduction, not native_decide.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S0.Certificates.CheckedLinearImageExamples

open scoped BigOperators Matrix
open D5.S0.Certificates.CheckedLinearImage

/-- The four-cell inequality matrix, independent of the data parameters. -/
def cappedMatrix : Fin 11 → Fin 4 → ℚ :=
  ![![-1, 0, 0, 0], ![0, -1, 0, 0], ![0, 0, -1, 0], ![0, 0, 0, -1],
    ![1, 1, 1, 1], ![-1, -1, -1, -1],
    ![0, 0, 1, 1], ![0, 0, -1, -1],
    ![0, 1, 0, 1], ![0, -1, 0, -1], ![0, 1, 1, 0]]

/-- Data for the normalization, marginal, and disagreement rows. -/
def cappedRhs (p q delta : ℚ) : Fin 11 → ℚ :=
  ![0, 0, 0, 0, 1, -1, p, -p, q, -q, delta]

/-- The query is the true-true cell. -/
def jointObjective : Fin 4 → ℚ := ![0, 0, 0, 1]

/-- All numerical data for the interval [5/12,1/2] at p=1/2,q=2/3,delta=1/3. -/
def cappedPayload : RawSharpPayload (Fin 11) (Fin 4) where
  lower := 5 / 12
  upper := 1 / 2
  xLower := ![1 / 4, 1 / 4, 1 / 12, 5 / 12]
  xUpper := ![1 / 3, 1 / 6, 0, 1 / 2]
  yLower := ![0, 0, 0, 0, 0, 0, 0, 1 / 2, 0, 1 / 2, 1 / 2]
  yUpper := ![0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0]

/-- The complete positive numerical payload passes executable replay. -/
theorem capped_payload_accepted :
    checkSharp cappedMatrix (cappedRhs (1 / 2) (2 / 3) (1 / 3))
      jointObjective cappedPayload = true := by
  decide +kernel

/-- The checked fixture certifies its complete real image, including interior targets. -/
theorem capped_fixture_real_image :
    (fun x : Fin 4 → ℝ => ∑ j, (jointObjective j : ℝ) * x j) ''
      {x | ∀ i, (∑ j, (cappedMatrix i j : ℝ) * x j) ≤
        (cappedRhs (1 / 2) (2 / 3) (1 / 3) i : ℝ)} =
      Set.Icc (5 / 12 : ℝ) (1 / 2 : ℝ) := by
  simpa [cappedPayload] using checked_real_query_image cappedMatrix
    (cappedRhs (1 / 2) (2 / 3) (1 / 3)) jointObjective cappedPayload
    capped_payload_accepted

/-- The negative fixture uses P-minus + Q-plus + D + twice N01. -/
def inconsistentWeights : Fin 11 → ℚ := ![0, 2, 0, 0, 0, 0, 0, 1, 1, 0, 1]

/-- Inconsistent marginal and cap data have an accepted raw Farkas certificate. -/
theorem inconsistent_payload_accepted :
    checkFarkas cappedMatrix (cappedRhs (3 / 4) (1 / 4) (1 / 4))
      inconsistentWeights = true := by
  decide +kernel

/-- The negative fixture excludes every real vector, not only rational ones. -/
theorem inconsistent_fixture_real_infeasible :
    ¬∃ x : Fin 4 → ℝ, ∀ i, (∑ j, (cappedMatrix i j : ℝ) * x j) ≤
      (cappedRhs (3 / 4) (1 / 4) (1 / 4) i : ℝ) :=
  checked_infeasible cappedMatrix (cappedRhs (3 / 4) (1 / 4) (1 / 4))
    inconsistentWeights inconsistent_payload_accepted

/-- Negating a valid upper multiplier vector is rejected. -/
theorem rejects_negative_multiplier :
    checkSharp cappedMatrix (cappedRhs (1 / 2) (2 / 3) (1 / 3)) jointObjective
      { cappedPayload with yUpper := fun i => -cappedPayload.yUpper i } = false := by
  decide +kernel

/-- Changing an endpoint coordinate without changing the claims is rejected. -/
theorem rejects_changed_endpoint :
    checkSharp cappedMatrix (cappedRhs (1 / 2) (2 / 3) (1 / 3)) jointObjective
      { cappedPayload with xLower := ![0, 1 / 4, 1 / 12, 5 / 12] } = false := by
  decide +kernel

/-- The same payload cannot certify a different authoritative objective. -/
theorem rejects_changed_objective :
    checkSharp cappedMatrix (cappedRhs (1 / 2) (2 / 3) (1 / 3))
      ![0, 0, 0, 2] cappedPayload = false := by
  decide +kernel

/-- Tightening the authoritative disagreement row invalidates the old payload. -/
theorem rejects_changed_problem :
    checkSharp cappedMatrix (cappedRhs (1 / 2) (2 / 3) 0)
      jointObjective cappedPayload = false := by
  decide +kernel

end D5.S0.Certificates.CheckedLinearImageExamples
