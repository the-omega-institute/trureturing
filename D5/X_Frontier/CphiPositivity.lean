/- GID: D5/X_Frontier/CphiPositivity
   generality: I
   mirror-B: none(waiver:frontier-open-statement)
   mirror-E: D5/E/values--json
   anchors: []
   digest: Ask whether the twisted cotangent summand can tend to zero. -/

import D5.S3.Constants.Values

namespace D5.X_Frontier.CphiPositivity

/- THEORIST_FRONTIER_CONTRACT_V1
{
  "schema": "trureturing-theorist-frontier-v1",
  "exact_statement": {
    "gid": "D5/X_Frontier/CphiPositivity.cPhiSummand_not_tendsto_zero",
    "statement_sha256": "sha256:50b2f295236ec28b6eb0573675c047d45819f19f948b8dbc52e7726addcb8477"
  },
  "motivation_gids": ["D5/S3/Constants/Values"],
  "falsifier": "The ordinary cPhi summand tends to zero along the natural numbers.",
  "search_receipt_gids": ["D5/L/koshy2001fibonacci"],
  "computation_receipt_gids": ["D5/E/values--json"],
  "triage_class": "theorem"
}
-/

/-- The ordinary summand used by `Values.cPhi` does not tend to zero. The
Fibonacci-window computation exposes the obstruction but is not a proof. -/
theorem cPhiSummand_not_tendsto_zero :
    ¬ Filter.Tendsto
      (fun k : ℕ =>
        let n : ℝ := k + 1
        Real.cos (4 * Real.pi * n * D5.S3.Constants.Values.goldenRatio) *
          (Real.cos (Real.pi * n * D5.S3.Constants.Values.goldenRatio) /
            Real.sin (Real.pi * n * D5.S3.Constants.Values.goldenRatio)) / n)
      Filter.atTop (nhds 0) := by
  sorry

end D5.X_Frontier.CphiPositivity
