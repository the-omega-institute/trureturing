/- GID: D5/S0/Tower/DBonacciGeneral/ChampionBoundary
   generality: I
   mirror-B: D5/B/S0/Tower/DBonacciGeneral/ChampionBoundary
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: D-bonacci champion values converge to one third at the binary boundary. -/

import D5.S0.Tower.DBonacciGeneral.ChampionValue

namespace D5.S0.Tower.DBonacciGeneral.ChampionBoundary

open D5.S0.Tower.DBonacci.PerronRoot
open D5.S0.Tower.DBonacciGeneral.ChampionValue
open Filter

/- Library-search audit trail (2026-08-17):
   * Repository search found the frozen d-bonacci Perron-root limit and the
     exact endpoint evaluation `championValue_two` in the imported module.
   * Pinned mathlib supplies `ContinuousAt.div` and `Tendsto.comp`; continuity
     of the polynomial numerator and denominator is discharged by `fun_prop`.
     No third-party asymptotic theorem is needed. -/

/-- The corrected rational champion expression is continuous at the limiting
endpoint because its denominator evaluates to three there. -/
theorem continuousAt_championValue_two : ContinuousAt championValue 2 := by
  unfold championValue
  apply ContinuousAt.div
  · fun_prop
  · fun_prop
  · norm_num

/-- As recurrence order tends to infinity, the d-bonacci champion values tend
to the binary champion value one third. -/
theorem championValue_dbonacciPerronRoot_tendsto_one_third :
    Tendsto (fun d => championValue (dbonacciPerronRoot d)) atTop
      (nhds ((1 : Real) / 3)) := by
  have hlimit :=
    continuousAt_championValue_two.tendsto.comp dbonacciPerronRoot_tendsto_two
  change Tendsto (fun d => championValue (dbonacciPerronRoot d)) atTop
    (nhds (championValue 2)) at hlimit
  rw [championValue_two] at hlimit
  exact hlimit

end D5.S0.Tower.DBonacciGeneral.ChampionBoundary
