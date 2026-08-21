# Byzantine Majority Recovery

## Abstract

A strict majority recovers a common binary truth when fewer than half the reports are Byzantine.

**Theorem 1.1 (Strict majority recovers the common truth).**

$$\forall n, f: Nat, truth: Bool, reports: \operatorname{Fin}(n) \to Bool,\\{}n > 2 \times f \land \operatorname{byzantineCount}\left(reports, truth\right) \leq f \Rightarrow \operatorname{strictMajority}\left(reports\right) = \operatorname{some}(truth).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InstitutionalCapture/ByzantineMajorityRecovery.strict_majority_recovers` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The report population is the finite identity type `Fin n`, each report is binary, and `byzantineCount` counts reports differing from the common honest value `truth`. The bound `byzantineCount reports truth <= f` is the formal reading of at most `f` Byzantine reporters.

The threshold `n > 2 * f` makes the matching reports strictly more numerous than the mismatching reports. The named `strictMajority` rule therefore returns `some truth`, including the two possible truth values.

The proof uses the pinned finite-filter partition theorem and natural-number arithmetic. A concrete three-report, one-fault-free witness is checked in the Lean module.

Repository searches found no accepted Byzantine-majority threshold theorem; the pinned library supplied only the finite cardinal partition used in the proof.

## References

- Truth anchor: `D5/S3/ConceptDynamics/InstitutionalCapture/ByzantineMajorityRecovery.strict_majority_recovers`
