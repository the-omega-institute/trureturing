# Transport of the unaffected boundary product

## Abstract

Transport of the unaffected boundary product.

**Theorem 1.1 (Transport of the unaffected boundary product).**

$$\forall L \in \mathit{Type},\; \forall m \in \mathit{Natural},\; \forall M \in \operatorname{NCMatching}\left(m + 2\right),\; \forall j \in \operatorname{Fin}\left(m + 1\right),\; \forall q \in \operatorname{Function}\left(L, \mathit{Real}\right),\; \forall y \in \operatorname{Function}\left(\operatorname{Fin}\left(m + 1\right), L\right),\; \forall b \in L,\; \operatorname{UnchangedOpeningProduct}\left(q, M, j, \operatorname{DetourLabels}\left(j, y, b\right)\right) = \operatorname{ShortUnchangedOpeningProduct}\left(q, M, j, y\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PerfectMatchings/BoundaryProductTransport.unaffected_opening_product` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

OpeningProduct is the product over all endpoints of the opening factor, which is q(x(a+1))/q(x(a)) when a is smaller than its partner and is 1 otherwise. UnchangedOpeningProduct restricts this product to the original Unchanged predicate; ShortUnchangedOpeningProduct restricts the shorter product to ShortUnchanged. ChangedOpeningProduct and ShortChangedOpeningProduct use the respective complementary predicates. Every arc whose endpoints survive without rewiring has the same opening factor before and after insertion. The increasing survivor equivalence transports the full product over these unaffected arcs.

**Theorem 1.2 (Transport of the unaffected boundary product).**

$$\forall L \in \mathit{Type},\; \forall m \in \mathit{Natural},\; \forall M \in \operatorname{NCMatching}\left(m + 2\right),\; \forall j \in \operatorname{Fin}\left(m + 1\right),\; \forall q \in \operatorname{Function}\left(L, \mathit{Real}\right),\; \forall y \in \operatorname{Function}\left(\operatorname{Fin}\left(m + 1\right), L\right),\; \forall b \in L,\; \operatorname{OpeningProduct}\left(q, M, \operatorname{DetourLabels}\left(j, y, b\right)\right) = \operatorname{ChangedOpeningProduct}\left(q, M, j, \operatorname{DetourLabels}\left(j, y, b\right)\right) \cdot \operatorname{ShortUnchangedOpeningProduct}\left(q, M, j, y\right) \land \operatorname{OpeningProduct}\left(q, \operatorname{CapSurgery}\left(M, j\right), y\right) = \operatorname{ShortChangedOpeningProduct}\left(q, M, j, y\right) \cdot \operatorname{ShortUnchangedOpeningProduct}\left(q, M, j, y\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PerfectMatchings/BoundaryProductTransport.opening_products_split` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The original and shorter boundary products split into their affected factors and the common unaffected product. This keeps all other components and imposes no relation on their weights.

## References

- Truth anchor: `D5/S3/Combinatorics/PerfectMatchings/BoundaryProductTransport.opening_products_split`
- Truth anchor: `D5/S3/Combinatorics/PerfectMatchings/BoundaryProductTransport.unaffected_opening_product`
- Dependency: [D5/S3/Combinatorics/PerfectMatchings/DetourLabels](DetourLabels.md)
