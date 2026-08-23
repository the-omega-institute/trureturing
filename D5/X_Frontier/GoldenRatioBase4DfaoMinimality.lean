/- GID: D5/X_Frontier/GoldenRatioBase4DfaoMinimality
   generality: I
   mirror-B: none(waiver:open-frontier-conjecture)
   mirror-E: D5/E/S1/Words/Automata/GoldenRatioBase4DfaoMinimality.result--json
   anchors: [mathlib/module/Mathlib.Data.Nat.Fib.Zeckendorf]
   digest: A 21-state DFAO refutes the paper's 22-state claim on valid words. -/

import D5.S1.Words.Automata.GoldenRatioBase4DfaoMinimality

namespace D5.X_Frontier.GoldenRatioBase4DfaoMinimality

open D5.S1.Words.Automata.GoldenRatioBase4DfaoMinimality

/-!
The literature question asks whether the paper's 22-state base-4 golden-ratio
DFAO can be replaced by a smaller DFAO when only Zeckendorf encodings of
powers `4^i` matter. The target below gives a stronger counterexample: one
21-state total DFAO agrees with the paper machine on every valid Zeckendorf
word and ignores leading zeroes.

Attack plan:

1. Check the finite state embedding which skips old state 3, including output
   compatibility and every transition allowed by the no-adjacent-ones rule.
2. Induct over valid words while carrying the invariant that seven explicit
   reduced states are exactly those reached after a terminal one; then package
   the reduced table and its leading-zero loop as the existential witness.

The finite checks are decidable; the only proof-theoretic step beyond them is
the structural induction over arbitrary valid words. The expected difficulty
is low once the dead-state observation has been made.
-/

/- THEORIST_FRONTIER_CONTRACT_V2
{
  "schema": "trureturing-theorist-frontier-v2",
  "exact_statement": {
    "gid": "D5/X_Frontier/GoldenRatioBase4DfaoMinimality.paper_base4_golden_ratio_dfao_is_not_minimal",
    "statement_sha256": "sha256:c3b64c8898de86769dad3d525acb15abd51c7adf8f2040b5844a5ca0c6d644c4"
  },
  "motivation_gids": ["D5/S0/Conventions/WDigits"],
  "falsifier": "No 21-state DFAO agrees with the paper machine on every valid Zeckendorf word while ignoring leading zeroes.",
  "search_receipt_gids": ["D5/L/Words/barnoffbrightshallit2024using"],
  "computation_receipt_gids": ["D5/E/S1/Words/Automata/GoldenRatioBase4DfaoMinimality.result--json"],
  "triage_class": "theorem"
}
-/

/- TASK D5-T0049
   Prove or refute 22-state minimality for the base-4 golden-ratio DFAO on the
   valid Zeckendorf encodings of powers of four. -/

/-- The 22-state base-4 golden-ratio DFAO is not minimal even on the larger
domain of all valid Zeckendorf words. -/
theorem paper_base4_golden_ratio_dfao_is_not_minimal :
    ∃ machine : DFAO 21,
      (∀ word : List Bool, ValidZeckendorf word ->
        machine.evaluate word = paperBase4DFAO.evaluate word) ∧
      (∀ word : List Bool,
        machine.evaluate (false :: word) = machine.evaluate word) := by
  sorry

end D5.X_Frontier.GoldenRatioBase4DfaoMinimality
