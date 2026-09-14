# UniqueChoice

## Abstract

Unique existence determines a chosen value and its defining predicate.

**Theorem 1.1 (Every satisfying value is the chosen value).**

$$\forall x, \operatorname{p}\left(x\right)\implies x= \operatorname{choose}!(h)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/ZfcSupport/UniqueChoice.choose_uniq` (`✓ std3`). ∎

*Citation.* FormalizedFormalLogic contributors (2026). *Foundation first-order logic and set theory, revision 30a16ffa*. URL: <https://github.com/FormalizedFormalLogic/Foundation/tree/30a16ffa93d79d73ab4d02427fa00f50e039bf29>.

*Commentary.*

Let p be a predicate on any sort and h a proof that exactly one value satisfies p. Every value satisfying p equals Classical.choose! applied to h.

For a predicate p on any sort and h witnessing unique existence, Classical.choose!_spec states that the chosen value satisfies p:

$\operatorname{p}\left(\operatorname{choose}!(h)\right)$

Classical.choose!_eq_iff_right characterizes equality with that value:

$\forall x, x= \operatorname{choose}!(h)\iff \operatorname{p}\left(x\right)$

Classical.choose! is noncomputable and requires a proof of unique existence. Its specification supports retained set definitions and function interpretation; it supplies no new existence axiom or full CSA definition-elimination theorem.

Retained mathematical commands: upstream lines 11-18. The selected definitions and proofs retain Foundation revision 30a16ffa93d79d73ab4d02427fa00f50e039bf29. Attribution, the complete Apache-2.0 license and the replacement condition are in Library/ConceptDynamics/foundation2026firstorder.md.

## References

- Truth anchor: `D5/S3/ConceptDynamics/ZfcSupport/UniqueChoice.choose_uniq`
