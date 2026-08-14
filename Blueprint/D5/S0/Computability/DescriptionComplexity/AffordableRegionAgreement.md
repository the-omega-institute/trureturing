# Affordable Region Agreement

## Abstract

An affordable finite-region patch forces agreement for a loss-minimal candidate.

**Theorem 1.1 (Affordable regions contain no remaining disagreement).**

$$\operatorname{price}(P) \leq budget - \operatorname{complexity}(g) - overhead \Rightarrow \forall n \in P,\ g(n) = \operatorname{truth}(n).$$

*Proof.* Machine-checked in Lean as `D5/S0/Computability/DescriptionComplexity/AffordableRegionAgreement.affordable_region_agreement` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The candidate and truth are total functions on the natural numbers. A finite record fixes their observed values, while a finite region P specifies the values replaced by the truth function.

The patch-cost premise bounds the corrected function by the candidate complexity plus price(P) and a fixed overhead. The accounting premise makes the natural-number subtraction explicit, so an affordable patch remains within the stated budget and stays consistent with the record.

Loss is valued in an arbitrary preorder. Correcting a genuine disagreement on a nonempty region, while changing nothing outside it, is assumed to strictly lower loss. This contradicts candidate minimality among all record-consistent functions within budget, forcing pointwise agreement.

Pinned Mathlib has no universal-machine or description-complexity theorem with these semantics. The proof therefore exposes cost and loss behavior as hypotheses and reuses only finite-set patching, natural arithmetic, and preorder contradiction.

## References

- Truth anchor: `D5/S0/Computability/DescriptionComplexity/AffordableRegionAgreement.affordable_region_agreement`
