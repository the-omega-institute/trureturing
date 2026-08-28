# Completely Recessive Selection Order

## Abstract

Completely recessive selection first appears at the ploidy order.

**Theorem 1.1 (The selection signal has exact ploidy order).**

$$\forall p\in \mathbb{N}, s, x\in \mathbb{R},\\{}1 \leq p \land 0 < s \land s \leq 1 \land 0 \leq x \land x \leq 1 \land (s < 1 \lor x < 1) \Rightarrow\\{}\operatorname{let}(\operatorname{allRecessiveFrequency}(k: \mathbb{N}, y: \mathbb{R}) := y^{{k}},\\{}\operatorname{meanFitness}(k: \mathbb{N}, y: \mathbb{R}) := {1 - \operatorname{allRecessiveFrequency}(k, y)} \cdot 1 + \operatorname{allRecessiveFrequency}(k, y) \cdot {1 - s},\\{}\operatorname{selectedAlleleMass}(k: \mathbb{N}, y: \mathbb{R}) := {y - \operatorname{allRecessiveFrequency}(k, y)} \cdot 1 + \operatorname{allRecessiveFrequency}(k, y) \cdot {1 - s},\\{}\operatorname{updatedFrequency}(k: \mathbb{N}, y: \mathbb{R}) := \frac{\operatorname{selectedAlleleMass}(k, y)}{\operatorname{meanFitness}(k, y)},\\{}\operatorname{selectionChange}(k: \mathbb{N}, y: \mathbb{R}) := \operatorname{updatedFrequency}(k, y) - y)\;\\{}\operatorname{meanFitness}(p, x) = 1 - s \cdot x^{{p}} \land\\{}\operatorname{updatedFrequency}(p, x) = \frac{x - s \cdot x^{{p}}}{1 - s \cdot x^{{p}}} \land\\{}\operatorname{selectionChange}(p, x) = \frac{-{s \cdot x^{{p}} \cdot {1 - x}}}{1 - s \cdot x^{{p}}} \land\\{}\operatorname{IsBigOAtZero}(y, \operatorname{selectionChange}(p, y) - -{s \cdot y^{{p}}}, y^{{p + 1}}) \land\\{}\operatorname{analyticOrderAt}(\operatorname{selectionChange}(p), 0) = p \land\\{}\forall q\in \mathbb{N}, p < q \Rightarrow \operatorname{analyticOrderAt}(\operatorname{selectionChange}(p), 0) < \operatorname{analyticOrderAt}(\operatorname{selectionChange}(q), 0).$$

*Proof.* Machine-checked in Lean as `D5/S0/Asymptotics/EscapeProbability/CompletelyRecessiveSelectionOrder.completely_recessive_selection_order` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The all-recessive class has frequency x^p and fitness 1-s; the remaining class has fitness one. Mean fitness and selected allele mass are constructed from those two classes before normalization.

Positive selection is required for the exact-order clause: at s=0 the change vanishes identically. The frequency lies in [0,1], and the single endpoint s=x=1 is excluded because mean fitness is zero there.

The local remainder is big-O of x^(p+1). Mathlib's analytic vanishing order records the nonzero degree-p leading factor, and the final clause makes the increase with ploidy explicit.

## References

- Truth anchor: `D5/S0/Asymptotics/EscapeProbability/CompletelyRecessiveSelectionOrder.completely_recessive_selection_order`
