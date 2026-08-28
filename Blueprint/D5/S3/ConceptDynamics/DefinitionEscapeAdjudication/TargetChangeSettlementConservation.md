# Target-Change Settlement Conservation

## Abstract

Appending only later target versions preserves every old pure settlement.

**Theorem 1.1 (Old-round settlement is unchanged by an append-only extension).**

$$\forall Target \in Type, Commitment \in Type, Evidence \in Type, Verdict \in Type, evaluate \in Commitment \to \left(Evidence \to Verdict\right), old \in \operatorname{List}(\operatorname{RoundRecord}(Target, Commitment, Evidence)), new \in \operatorname{List}(\operatorname{RoundRecord}(Target, Commitment, Evidence)), round \in Nat,\; \left(\operatorname{AppendOnly}(old, new) \land round < \operatorname{length}(old)\right) \Rightarrow \operatorname{settleAt}(evaluate, new, round) = \operatorname{settleAt}(evaluate, old, round)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/DefinitionEscapeAdjudication/TargetChangeSettlementConservation.append_only_old_settlement_unchanged` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A target change records the old and new target versions together with reason, author, time, and affected rounds, so the version edge is explicit rather than an in-place mutation.

RoundRecord stores the target version, immutable commitment, and evidence. AppendOnly means that a later ledger is the old ledger followed by a tail, and settleAt is a pure lookup and evaluation of one indexed record.

For an old index that exists in the old ledger, List.get?_append returns the same record after any tail. Mapping the pure evaluator over that equal lookup proves the displayed settlement equality; mutable external state is not part of this evaluator interface.

## References

- Truth anchor: `D5/S3/ConceptDynamics/DefinitionEscapeAdjudication/TargetChangeSettlementConservation.append_only_old_settlement_unchanged`
