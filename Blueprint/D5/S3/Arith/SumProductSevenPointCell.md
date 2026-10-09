# The Seven-Point Sum-Product Cell (23, 13) Is Absent

## Abstract

A seven-element set of positive reals with thirteen products has at least twenty-four sums.

**Theorem 1.1 (Sums of seven geometric terms).**

$$\forall b \in \mathrm{Real},\; \forall r \in \mathrm{Real},\; 0 < b \Rightarrow \left(1 < r \Rightarrow 24 \le \operatorname{card}\left(\left\{b \cdot r^{i} \mid i \in \operatorname{range}\left(7\right)\right\} + \left\{b \cdot r^{i} \mid i \in \operatorname{range}\left(7\right)\right\}\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/SumProductSevenPointCell.geometric_sum_card_lower_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For b positive and r greater than one, the seven terms b, br, through br to the sixth power have at least twenty-four distinct sums. Every equality of two unordered pair sums reduces to one of thirteen polynomial equations. Their twelve remaining factors have no common positive root, so removing at most four outer index pairs leaves an injective sum map.

**Theorem 1.2 (Thirteen products force twenty-four sums).**

$$\forall A \in \operatorname{Finset}\left(\mathrm{Real}\right),\; \left(\forall x \in \mathrm{Real},\; x \in A \Rightarrow 0 < x\right) \Rightarrow \left(\operatorname{card}\left(A\right) = 7 \Rightarrow \left(\operatorname{card}\left(A \cdot A\right) = 13 \Rightarrow 24 \le \operatorname{card}\left(A + A\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/SumProductSevenPointCell.stronger_result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The minimum product cardinality of a seven-element positive-real set is thirteen. Equality forces a geometric progression. Applying the geometric sum bound gives at least twenty-four sums.

**Definition 1.3 (The cell (23, 13) is absent).**

$$claim \Leftrightarrow \left(\forall A \in \operatorname{Finset}\left(\mathrm{Real}\right),\; \left(\forall x \in \mathrm{Real},\; x \in A \Rightarrow 0 < x\right) \Rightarrow \left(\operatorname{card}\left(A\right) = 7 \Rightarrow \left(\neg \left(\operatorname{card}\left(A + A\right) = 23 \land \operatorname{card}\left(A \cdot A\right) = 13\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Arith/SumProductSevenPointCell.claim` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every finite set A of positive reals with seven elements, the sumset cannot have twenty-three elements while the product set has thirteen elements. Both sets use pointwise operations.

**Theorem 1.4 (Exclusion of the cell (23, 13)).**

$$claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/SumProductSevenPointCell.result` (`✓ std3`). ∎

*Resolves.* `Problems/obryant-2024-sum-product-seven-point-cell` (proved) by `D5/S3/Arith/SumProductSevenPointCell.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"obryant-2024-sum-product-seven-point-cell","declaration_gid":"D5/S3/Arith/SumProductSevenPointCell.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Commentary.*

The stronger bound contradicts the proposed sum cardinality whenever the product cardinality is thirteen.

## References

- Truth anchor: `D5/S3/Arith/SumProductSevenPointCell.claim`
- Truth anchor: `D5/S3/Arith/SumProductSevenPointCell.geometric_sum_card_lower_bound`
- Truth anchor: `D5/S3/Arith/SumProductSevenPointCell.result`
- Truth anchor: `D5/S3/Arith/SumProductSevenPointCell.stronger_result`
- Dependency: [D5/S3/Arith/GeometricProductSetMinimum](GeometricProductSetMinimum.md)
