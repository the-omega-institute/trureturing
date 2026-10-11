# Minimum Product Sets of Positive Reals

## Abstract

A finite set of positive real numbers with the least possible number of products is a geometric progression.

**Theorem 1.1 (The ordered-product lower bound).**

$$\forall A \in \operatorname{Finset}\left(\mathrm{Real}\right),\; \left(\forall a \in \mathrm{Real},\; \operatorname{Member}\left(a, A\right) \Rightarrow 0 < a\right) \Rightarrow \left(\operatorname{Nonempty}\left(A\right) \Rightarrow 2 \cdot \operatorname{card}\left(A\right) - 1 \le \operatorname{card}\left(A \cdot A\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/GeometricProductSetMinimum.product_card_lower_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let A be a nonempty finite set of positive real numbers, of size m. Then AA has at least 2m-1 elements. In increasing coordinates x_0<...<x_(m-1), the products along an increasing grid path from (0,0) to (m-1,m-1) are strictly increasing. Such a path has 2m-1 vertices.

**Theorem 1.2 (Equality forces constant consecutive ratios).**

$$\forall A \in \operatorname{Finset}\left(\mathrm{Real}\right),\; \left(\forall a \in \mathrm{Real},\; \operatorname{Member}\left(a, A\right) \Rightarrow 0 < a\right) \Rightarrow \left(2 \le \operatorname{card}\left(A\right) \Rightarrow \left(\operatorname{card}\left(A \cdot A\right) \le 2 \cdot \operatorname{card}\left(A\right) - 1 \Rightarrow \left(\exists b \in \mathrm{Real},\; \exists r \in \mathrm{Real},\; 0 < b \land \left(1 < r \land A = \left\{b \cdot r^{i} \mid i \in \operatorname{range}\left(\operatorname{card}\left(A\right)\right)\right\}\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/GeometricProductSetMinimum.eq_geometric_of_product_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Suppose A contains at least two positive real numbers and AA has at most 2|A|-1 elements. The lower bound gives equality. Every increasing product-grid path therefore enumerates AA in increasing order. Compare the path that first follows row zero with the path that changes from row zero to row one at column j-1. Their entries at position j agree, giving x_0 x_j=x_1 x_(j-1). Thus x_j=x_0(x_1/x_0)^j for every index j, and x_1/x_0>1.

## References

- Truth anchor: `D5/S3/Arith/GeometricProductSetMinimum.eq_geometric_of_product_card`
- Truth anchor: `D5/S3/Arith/GeometricProductSetMinimum.product_card_lower_bound`
