# Uniform Finite-Pattern Recurrence Across the Golden Subshift

## Abstract

Every observer in the golden word subshift sees each admissible finite factor inside one recurrence window whose bound is independent of the observer and the starting position.

**Theorem 1.1 (Every golden-subshift observer shares the same factor recurrence bound).**

$$\forall n\in \mathbb{N}, w\in \operatorname{List}(Bool),\\{}w \in \operatorname{goldenFactorSet}(n) \Rightarrow \exists R\in \mathbb{N},\\{}\forall y : \mathbb{N} \to Bool, y \in \operatorname{wordSubshift}(goldenWord) \Rightarrow\\{}\forall i\in \mathbb{N}, \exists j\in \mathbb{N},\\{}i \leq j \land j + n \leq i + R \land w = \operatorname{ofFn}(\operatorname{wordFactor}(y, n, j))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Complexity/GoldenSubshiftUniformRecurrence.golden_subshift_factor_uniformly_recurrent` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The public carrier is the existing prefix-language subshift of the golden word. Admissibility is membership in the existing finite golden factor set; neither object is redefined for this theorem.

Use the existing explicit recurrence bound for the distinguished golden word. A sufficiently long prefix of an arbitrary subshift member is itself a golden factor, so an occurrence in the corresponding golden-word window transports back to the observer.

The transported start lies at or after the requested index, and its end lies within the same bound. Thus the witness is uniform in both the observer and the orbit-segment start.

## References

- Truth anchor: `D5/S1/Words/Complexity/GoldenSubshiftUniformRecurrence.golden_subshift_factor_uniformly_recurrent`
- Dependency: [D5/S1/Words/Complexity/GoldenSubshiftMinimality](GoldenSubshiftMinimality.md)
