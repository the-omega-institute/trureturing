# Research Promotion Loop

## Abstract

Ledgers prune; walls persist; release forces escape; promotion receipts are typed.

**Theorem 1.1 (A released anchor projects its typed proof receipt and link chain).**

$$\forall chain: \operatorname{PromotionChain}\left(Candidate, Statement, Proof, Node, Anchor, Seed\right), \exists receipt: \operatorname{ProofReceipt}\left(\operatorname{certifies}\left(chain\right), \operatorname{exactStatement}\left(chain\right)\right), \operatorname{verdict}\left(chain\right) = \operatorname{PromotionVerdictProved}\left(receipt\right) \land \operatorname{exactStatement}\left(chain\right) = \operatorname{statementOfProposal}\left(chain\right) \land \operatorname{frozenNode}\left(chain\right) = \operatorname{nodeOfVerdict}\left(chain\right) \land \operatorname{releasedAnchor}\left(chain\right) = \operatorname{anchorOfFrozenNode}\left(chain\right) \land \operatorname{researchSeed}\left(chain\right) = \operatorname{seedOfReleasedAnchor}\left(chain\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Promotion/ResearchPromotionLoop.released_anchor_has_receipt` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

PromotionChain is typed bookkeeping from proposal through verdict, frozen node, released anchor, and research seed.

The proved verdict branch supplies the ProofReceipt and all faithfulness equalities; the refuted branch is excluded by IsReleased.

This is typed bookkeeping, not an empirical validity or promotion-policy theorem.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Promotion/ResearchPromotionLoop.released_anchor_has_receipt`
