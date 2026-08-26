# Affordable Region Agreement

## Abstract

An affordable finite-region patch forces agreement for a loss-minimal candidate.

**Theorem 1.1 (Affordable regions contain no remaining disagreement).**

$$\begin{gathered}\forall Output, Loss: \operatorname{Type},\\{}[\operatorname{Preorder}(Loss)],\\{}\forall truth, g: \mathbb{N} \to Output,\\{}\forall record, P: \operatorname{Finset}\left(\mathbb{N}\right),\\{}\forall complexity: (\mathbb{N} \to Output) \to \mathbb{N}, \forall price: \operatorname{Finset}\left(\mathbb{N}\right) \to \mathbb{N},\\{}\forall budget, overhead: \mathbb{N}, \forall loss: (\mathbb{N} \to Output) \to Loss,\\{}(\forall n: \mathbb{N}, n \in record \Rightarrow g(n) = \operatorname{truth}(n)),\\{}\operatorname{complexity}((n: \mathbb{N} \mapsto \operatorname{ite}\left(n \in P, \operatorname{truth}(n), g(n)\right))) \leq \operatorname{complexity}(g) + \operatorname{price}(P) + overhead,\\{}\operatorname{complexity}(g) + overhead \leq budget,\\{}(\forall h: \mathbb{N} \to Output, \operatorname{Nonempty}\left(P\right) \Rightarrow (\forall n: \mathbb{N}, \neg (n \in P) \Rightarrow h(n) = g(n)) \Rightarrow (\forall n: \mathbb{N}, n \in P \Rightarrow h(n) = \operatorname{truth}(n)) \Rightarrow (\exists n: \mathbb{N}, n \in P \land g(n) \neq \operatorname{truth}(n)) \Rightarrow \operatorname{loss}(h) < \operatorname{loss}(g)),\\{}(\forall h: \mathbb{N} \to Output, (\forall n: \mathbb{N}, n \in record \Rightarrow h(n) = \operatorname{truth}(n)) \Rightarrow \operatorname{complexity}(h) \leq budget \Rightarrow \operatorname{loss}(g) \leq \operatorname{loss}(h)),\\{}\operatorname{price}(P) \leq budget - \operatorname{complexity}(g) - overhead \Rightarrow \forall n \in P,\ g(n) = \operatorname{truth}(n).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S0/Computability/DescriptionComplexity/AffordableRegionAgreement.affordable_region_agreement` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The candidate and truth are total functions on the natural numbers. A finite record fixes their observed values, while a finite region P specifies the values replaced by the truth function.

The patch-cost premise bounds the corrected function by the candidate complexity plus price(P) and a fixed overhead. The accounting premise makes the natural-number subtraction explicit, so an affordable patch remains within the stated budget and stays consistent with the record.

Loss is valued in an arbitrary preorder. Correcting a genuine disagreement on a nonempty region, while changing nothing outside it, is assumed to strictly lower loss. This contradicts candidate minimality among all record-consistent functions within budget, forcing pointwise agreement.

Pinned Mathlib has no universal-machine or description-complexity theorem with these semantics. The proof therefore exposes cost and loss behavior as hypotheses and reuses only finite-set patching, natural arithmetic, and preorder contradiction.

## References

- Truth anchor: `D5/S0/Computability/DescriptionComplexity/AffordableRegionAgreement.affordable_region_agreement`
