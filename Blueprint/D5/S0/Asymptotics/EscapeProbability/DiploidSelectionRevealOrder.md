# Diploid Selection Reveal Order

## Abstract

Nonzero heterozygote effect changes the rare-allele signal from second to first order.

**Theorem 1.1 (Complete recessivity is quadratic and nonzero dominance is linear).**

$$\forall s, h\in \mathbb{R}, s \neq 0 \Rightarrow\\{}\operatorname{let}(\operatorname{meanFitness}(h: \mathbb{R}, x: \mathbb{R}) := (1 - x)^{{2}} + 2 \cdot {1 - x} \cdot x \cdot {1 - h \cdot s} + x^{{2}} \cdot {1 - s},\\{}\operatorname{selectedAlleleMass}(h: \mathbb{R}, x: \mathbb{R}) := x^{{2}} \cdot {1 - s} + {1 - x} \cdot x \cdot {1 - h \cdot s},\\{}\operatorname{updatedFrequency}(h: \mathbb{R}, x: \mathbb{R}) := \frac{\operatorname{selectedAlleleMass}(h, x)}{\operatorname{meanFitness}(h, x)},\\{}\operatorname{selectionChange}(h: \mathbb{R}, x: \mathbb{R}) := \operatorname{updatedFrequency}(h, x) - x)\;\\{}(\forall x\in \mathbb{R}, \operatorname{meanFitness}(0, x) \neq 0 \Rightarrow \operatorname{selectionChange}(0, x) = \frac{-{s \cdot {1 - x} \cdot x^{{2}}}}{1 - s \cdot x^{{2}}}) \land\\{}\operatorname{IsBigOAtZero}(x, \operatorname{selectionChange}(0, x) - -{s \cdot x^{{2}}}, x^{{3}}) \land\\{}\operatorname{analyticOrderAt}(\operatorname{selectionChange}(0), 0) = 2 \land\\{}(0 < h \Rightarrow \operatorname{IsBigOAtZero}(x, \operatorname{selectionChange}(h, x) - -{h \cdot s \cdot x}, x^{{2}})) \land\\{}(h \cdot s \neq 0 \Rightarrow \operatorname{analyticOrderAt}(\operatorname{selectionChange}(h), 0) = 1).$$

*Proof.* Machine-checked in Lean as `D5/S0/Asymptotics/EscapeProbability/DiploidSelectionRevealOrder.diploid_selection_reveal_order` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Mean fitness, selected allele mass, updated frequency, and selection change are the source's diploid genotype formulas with fitnesses 1, 1-hs, and 1-s.

For nonzero s, complete recessivity has the displayed exact change, a cubic remainder after its quadratic leading term, and analytic order two. Under h greater than zero, the exposed change has a quadratic remainder after its linear leading term. Whenever hs is nonzero, the selection reveal order is one.

## References

- Truth anchor: `D5/S0/Asymptotics/EscapeProbability/DiploidSelectionRevealOrder.diploid_selection_reveal_order`
- Dependency: [D5/S0/Asymptotics/EscapeProbability/DiploidDominanceSelectionOrder](DiploidDominanceSelectionOrder.md)
