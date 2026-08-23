# Budget Set Scale Invariance

## Abstract

Simultaneous positive scaling of prices and wealth preserves the budget set.

**Theorem 1.1 (Positive price and wealth scaling preserves affordable bundles).**

$$\forall L\in \mathbb{N}, p\in \mathbb{R}_{++}^{L}, w, \lambda\in \mathbb{R},\ 0< w \land 0< \lambda \Rightarrow \{x\in \mathbb{R}_{+}^{L} \mid \lambda p \cdot x \leq \lambda w\} = \{x\in \mathbb{R}_{+}^{L} \mid p \cdot x \leq w\}.$$

*Proof.* Machine-checked in Lean as `D5/S3/ResourceOrder/PriceCoordinates/BudgetSetScaleInvariance.budget_set_scale_invariance` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For L goods, prices are a strictly positive real vector and nominal wealth is positive. Each budget set is constructed directly as the nonnegative bundles whose finite price dot product does not exceed wealth.

Scaling the price vector pulls the positive scalar through the dot product. Multiplication by a positive scalar preserves and reflects the affordability inequality, giving equality of the two sets.

Repository search found only the distinct fixed-nominal-debt inverse scaling result. Pinned Mathlib has no exact budget-set theorem; the proof directly applies smul_dotProduct and mul_le_mul_iff_of_pos_left.

The module compiles a two-good instance with unit prices, unit wealth, and scale two as simultaneous witnesses for the hypotheses and the set equality.

## References

- Truth anchor: `D5/S3/ResourceOrder/PriceCoordinates/BudgetSetScaleInvariance.budget_set_scale_invariance`
