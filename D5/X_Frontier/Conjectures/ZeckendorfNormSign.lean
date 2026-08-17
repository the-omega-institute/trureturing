/- GID: D5/X_Frontier/Conjectures/ZeckendorfNormSign
   generality: I
   mirror-B: none(waiver:open-frontier-conjecture)
   mirror-E: D5/E/S1/Deficit/ZeckendorfNormSign.result--json
   anchors: [mathlib/module/Mathlib.Data.Nat.Fib.Zeckendorf]
   digest: The least occupied Zeckendorf index determines the sign of the associated golden norm. -/

import D5.S0.Conventions.WDigits
import D5.S1.Deficit.DoubleFaceLength

namespace D5.X_Frontier.Conjectures.ZeckendorfNormSign

open D5.S0.Carrier
open D5.S0.Conventions
open D5.S1.Deficit

/-!
The machine-selected `GoldenUnitsUFD` frontier ticket is stale as a theorem
target: its signed-power classification, PID, and UFD conclusions already
exist in the frozen graph. This module records a nonduplicate norm question
exposed while binding that candidate to its existing delivery.

The conjecture connects canonical Zeckendorf gaps to the two real faces of
`betaGolden`. On the contraction face, the least occupied term should dominate
the remaining nonadjacent tail, fixing its sign by parity. The expansion face
is positive, while `embedding_mul_conj` identifies the product of both faces
with the integer norm. The finite computation receipt tests this consequence;
it does not prove it.
-/

/- TASK D5-T0045
   Prove or refute that the least occupied canonical Zeckendorf index fixes the
   sign of the golden norm of `betaGolden`; a zero norm is also a falsifier. -/

/- THEORIST_FRONTIER_CONTRACT_V1
{
  "schema": "trureturing-theorist-frontier-v1",
  "exact_statement": {
    "gid": "D5/X_Frontier/Conjectures/ZeckendorfNormSign.betaGolden_norm_sign_of_least_zeckendorf_index",
    "statement_sha256": "sha256:4456d98bab5d30f02251fdb9fe6d2256263c566c7cafade256960c114817559c"
  },
  "motivation_gids": [
    "D5/S0/Carrier/Norm",
    "D5/S0/Conventions/WDigits",
    "D5/S1/Deficit/DeficitInteger",
    "D5/S1/Digit/Admissibility/LeastDigitDecomposition",
    "D5/S1/Scale/Embedding"
  ],
  "falsifier": "A positive v with wrong least-index parity for its norm sign, or zero norm.",
  "search_receipt_gids": [
    "D5/L/koshy2001fibonacci"
  ],
  "computation_receipt_gids": [
    "D5/E/S1/Deficit/ZeckendorfNormSign.result--json"
  ],
  "triage_class": "theorem"
}
-/

/-- For a positive natural number, parity of its least occupied Zeckendorf
index determines the sign of the norm of its golden-integer realization. -/
theorem betaGolden_norm_sign_of_least_zeckendorf_index
    {v k : ℕ}
    (hv : 0 < v)
    (hk : k ∈ wdigits v)
    (hmin : ∀ j ∈ wdigits v, k ≤ j) :
    (0 < norm (betaGolden v) ↔ Even k) ∧
      (norm (betaGolden v) < 0 ↔ Odd k) := by
  sorry

end D5.X_Frontier.Conjectures.ZeckendorfNormSign
