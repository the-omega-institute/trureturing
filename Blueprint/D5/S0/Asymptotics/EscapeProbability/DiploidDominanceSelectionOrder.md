# Diploid Dominance Selection Order

## Abstract

Diploid dominance changes the rare-allele selection signal from second to first order.

**Theorem 1.1 (Recessive selection is quadratic and exposed selection is linear).**

$$\forall s, h\in \mathbb{R}, s \neq 0 \Rightarrow\\{}\operatorname{let}(\operatorname{meanFitness}(h: \mathbb{R}, x: \mathbb{R}) := (1 - x)^{{2}} + 2 \cdot {1 - x} \cdot x \cdot {1 - h \cdot s} + x^{{2}} \cdot {1 - s},\\{}\operatorname{selectedAlleleMass}(h: \mathbb{R}, x: \mathbb{R}) := x^{{2}} \cdot {1 - s} + {1 - x} \cdot x \cdot {1 - h \cdot s},\\{}\operatorname{updatedFrequency}(h: \mathbb{R}, x: \mathbb{R}) := \frac{\operatorname{selectedAlleleMass}(h, x)}{\operatorname{meanFitness}(h, x)},\\{}\operatorname{selectionChange}(h: \mathbb{R}, x: \mathbb{R}) := \operatorname{updatedFrequency}(h, x) - x)\;\\{}(\forall x\in \mathbb{R}, \operatorname{meanFitness}(0, x) \neq 0 \Rightarrow \operatorname{selectionChange}(0, x) = \frac{-{s \cdot {1 - x} \cdot x^{{2}}}}{1 - s \cdot x^{{2}}}) \land\\{}\operatorname{IsBigOAtZero}(x, \operatorname{selectionChange}(0, x) - -{s \cdot x^{{2}}}, x^{{3}}) \land\\{}\operatorname{analyticOrderAt}(\operatorname{selectionChange}(0), 0) = 2 \land\\{}\operatorname{IsBigOAtZero}(x, \operatorname{selectionChange}(h, x) - -{h \cdot s \cdot x}, x^{{2}}) \land\\{}(h \cdot s \neq 0 \Rightarrow \operatorname{analyticOrderAt}(\operatorname{selectionChange}(h), 0) = 1).$$

*Proof.* Machine-checked in Lean as `D5/S0/Asymptotics/EscapeProbability/DiploidDominanceSelectionOrder.diploid_dominance_selection_order` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Mean fitness and selected allele mass are constructed from the aa, ab, and bb genotype frequencies with fitnesses 1, 1-hs, and 1-s.

At h=0 the exact frequency change has a quadratic leading term and a cubic remainder. A nonzero product hs supplies a nonzero linear leading term, so the analytic order drops from two to one.

## References

- Truth anchor: `D5/S0/Asymptotics/EscapeProbability/DiploidDominanceSelectionOrder.diploid_dominance_selection_order`
- Dependency: [D5/S0/Asymptotics/EscapeProbability/CompletelyRecessiveSelectionOrder](CompletelyRecessiveSelectionOrder.md)
