# Multipartite coefficient extrema

## Abstract

Strict extrema of multipartite reciprocal coefficients at fixed order and size.

**Theorem 1.1 (Elementary symmetric sums after adjoining one entry).**

$$\forall x: \mathbb{N}, \forall s: \operatorname{Multiset}\left(\mathbb{N}\right), \forall k: \mathbb{N}, \operatorname{Multiset.esymm}\left(\operatorname{Multiset.cons}\left(x, s\right), k + 1\right) = \operatorname{Multiset.esymm}\left(s, k + 1\right) + x \cdot \operatorname{Multiset.esymm}\left(s, k\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/MultipartiteCHS/Extremal.esymm_cons` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Adjoining a natural-number entry to a multiset splits the next elementary symmetric sum into the old next sum and the new entry times the old preceding sum. The identity gives the two-entry coefficient expansion and the arithmetic of a positive integer family satisfying σ₃ = σₙ.

**Theorem 1.2 (Unique extremal part multisets).**

Lean statement: `D5/S3/Combinatorics/Graph/MultipartiteCHS/Extremal.recH_extremal`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/MultipartiteCHS/Extremal.recH_extremal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix r at least two, n at least r, and a positive even degree 2m. Among all positive integer part sizes with sum n, the reciprocal coefficient is minimized by one part of size n minus r plus one and r minus one singleton parts. It is maximized by the balanced partition, whose part sizes differ by at most one. Equality at either endpoint forces the same part multiset, expressed by a permutation of the indices.

Strong induction in the coefficient recurrence propagates elementary symmetric coefficient inequalities. A strict increase in the quadratic elementary coefficient forces a strict increase at every positive even degree, using positivity of the preceding even coefficient.

For two selected part sizes x and y and remaining multiset c, the degree k plus two elementary coefficient is e[k+2](c) plus (x+y)e[k+1](c) plus xy e[k](c). A transfer preserving x+y and increasing xy weakly increases every elementary coefficient of degree at least two and strictly increases the quadratic coefficient.

The admissible positive integer vectors form a finite set. Any maximizing vector must be equitable: otherwise a balancing transfer gives a strictly larger coefficient. The equitable-function characterization puts every part at the quotient n/r or one more; counting the larger parts produces a permutation of balancedParts. Any minimizing vector has at most one part larger than one: otherwise an unbalancing transfer gives a strictly smaller coefficient. Its remaining part is determined by the total sum.

The recurrence comparison reuses recH_eq, recH_nonneg and recH_two_mul_pos. The multiset representation uses Finset.esymm_map_val, and the balanced classification uses Finset.equitableOn_iff and extension of an equivalence between the larger-part fibers. This theorem concerns recH; the separately proved spectral identity transfers it to CHS values.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/MultipartiteCHS/Extremal.esymm_cons`
- Truth anchor: `D5/S3/Combinatorics/Graph/MultipartiteCHS/Extremal.recH_extremal`
- Dependency: [D5/S3/Combinatorics/Graph/MultipartiteCHS/Recurrence](Recurrence.md)
