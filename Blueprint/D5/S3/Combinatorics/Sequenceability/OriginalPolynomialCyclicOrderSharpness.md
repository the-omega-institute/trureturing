# Polynomial-size cyclic extremal labels

## Abstract

A cyclic carrier of quadratic size attains the original all-support component bound.

**Theorem 1.1 (A polynomial carrier bound for the extremal support family).**

Lean statement: `D5/S3/Combinatorics/Sequenceability/OriginalPolynomialCyclicOrderSharpness.sharpness`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Sequenceability/OriginalPolynomialCyclicOrderSharpness.sharpness` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural m at least two, set r = m-1, L = 6*r-1, and N = m*L. The finite cyclic label group G = ZMod N has exactly m*(6*m-7) elements. Retain the original coordinates J = Fin(m-1), Coordinate = Option J summed with Option J, q = inl none, p = inr none, a_j = inl (some j), and b_j = inr (some j); Y contains all coordinates. Use natural representatives q = N-L, p = 4*r, a_j = 2*r+2*j, and b_j = L-2*r-2*j. The label of q has additive order exactly m.

The a labels are distinct even numbers from 2*r through 4*r-2, the sentinel p = 4*r is even, and the b labels are distinct odd numbers from 2*r+1 through 4*r-1. The q label is larger than 4*r and below N. These intervals and parities imply that every label is nonzero and the labeling is injective.

All non-q labels are positive, and each pair a_j,b_j has natural sum L. Their complete natural sum, including p, is r*L+4*r, strictly below N. Consequently a nonempty coefficient-one zero support must contain q. Since q has representative N-L, the other labels in that support have natural sum exactly L.

Because L is odd, each b label is odd, and all a labels and p are even, the number of selected b labels is odd. Each b label is at least 2*r+1, so three of them already exceed L = 6*r-1. Thus exactly one b label, b_j, occurs. The selected small labels then sum to a_j, a number between 2*r and 4*r-2. The sentinel is too large, two a labels already sum to at least 4*r, and the empty sum is zero. Thus there is exactly one a label, and injectivity forces its index to be j. Every nonempty zero support is precisely {q,a_j,b_j}; conversely each such triple sums to N.

Let E consist of all proper original inclusion-minimal nonempty zero supports in Y. The complete zero-support classification identifies E with the full family of OriginalFiniteOrderSharpness. It has m-1 elements, every support contains q, and distinct supports have disjoint punctures after deleting q. The sentinel keeps every triple proper, including m = 2. Equality of the complete support families transports the existing graph lower bound. Applying OriginalFiniteOrderComponentBound.q_containing_component_card_lt directly to these labels gives the matching strict upper bound. Therefore the image of the canonical supportIntersectionGraph E q connected-component map on all q-containing vertices has exactly m-1 elements.

This gives an explicit quadratic upper bound on the size of a cyclic carrier attaining the original finite-order component bound. The proof reuses OriginalFiniteOrderSharpness for the original coordinates and the actual support graph. It applies to composite m and retains all original supports. No assertion of minimum carrier size, literature priority, good-ordering, or infinite order is made.

## References

- Truth anchor: `D5/S3/Combinatorics/Sequenceability/OriginalPolynomialCyclicOrderSharpness.sharpness`
- Dependency: [D5/S3/Combinatorics/Sequenceability/OriginalFiniteOrderSharpness](OriginalFiniteOrderSharpness.md)
