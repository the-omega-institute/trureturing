# Terminating Larger Atoms of Optimal Laws

## Abstract

Every atom above the minimum in an optimal real probability law is a terminating binary rational.

**Theorem 1.1 (Larger atoms terminate).**

$$(\forall m: \mathbb{N}, (\forall p: \operatorname{Fin}\left(m\right) \to \mathbb{R}, ((2 \le m \land (\forall i: \operatorname{Fin}\left(m\right), 0 < \operatorname{p}\left(i\right)) \land \sum_{i \in \operatorname{Fin}\left(m\right)}\operatorname{p}\left(i\right) = 1 \land \operatorname{cost}\left(p\right) = \operatorname{alpha}\left(m\right) \cdot \operatorname{inf}\left(\operatorname{range}\left(p\right)\right)) \to (\forall j: \operatorname{Fin}\left(m\right), (\operatorname{inf}\left(\operatorname{range}\left(p\right)\right) < \operatorname{p}\left(j\right) \to (\exists D: \mathbb{N}, (\exists N: \mathbb{N}, \operatorname{p}\left(j\right) = \frac{N}{2^{D}})))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/OptimalLawLargerAtomsTerminate.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The law p is strictly positive and normalized on m labels, with m at least two. Its minimum mass is the infimum of its finite range. The function alpha is the infimum of the dyadic floor-tail cost divided by the minimum mass over all such real laws. Attainment means that cost(p) equals alpha(m) times that minimum.

Let I contain the labels of minimum mass t, and let e be its cardinality. A larger atom has a label outside I, so e is smaller than m. Choose an attaining e-label law q of minimum mass u. When e is one, q is the single-label law and has zero cost.

A nonterminating larger atom has binary digits equal to one at arbitrarily large depths. Choose such a depth d with delta=2^(-d) smaller than the gap above t divided by 1+u. Remove delta from that atom and distribute it over I according to q. The resulting actual law is positive and normalized, with minimum mass exactly t+delta*u.

The donor's shallower floor counts remain unchanged, and the recipients' floor counts do not decrease. At later depths, the donor loses an integral dyadic count and the recipients gain at least the corresponding counts of q. Summing the resulting convergent floor-tail inequalities bounds the new cost by cost(p)+delta*cost(q). Since alpha(e) is strictly smaller than alpha(m), this cost is below alpha(m) times the new minimum mass. That contradicts the defining optimal lower bound and forces every larger atom to have a terminating binary expansion.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/OptimalLawLargerAtomsTerminate.result`
- Dependency: [D5/S3/Arith/FibonacciAtomic/OptimalLawStrictSlope](OptimalLawStrictSlope.md)
