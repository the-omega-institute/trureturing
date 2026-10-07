# Exact Stream of a Marked Prefix

## Abstract

Literal marked prefixes determine the ordered signed stream.

**Theorem 1.1 (Padded stream and exact lower tail).**

$$\forall n \in \mathbb{N},\; \forall m \in \mathbb{N},\; \forall p \in \mathbb{N},\; \forall T \in \mathbb{Z},\; \forall ds \in \operatorname{List}\left(\mathbb{Z}\right),\; \left(\left(\left(\left(\operatorname{markedPrefix}\left(n, m, p, T\right) \land \left(\forall z \in \mathbb{Z},\; z \in ds \Rightarrow \left(z = \operatorname{neg}\left(1\right) \lor \left(z = 0 \lor z = 1\right)\right)\right)\right) \land \operatorname{IsChain}\left(ds, \lambda a:\mathbb{Z} b:\mathbb{Z} \mapsto a = 0 \lor b = 0\right)\right) \land \operatorname{foldr}\left(\lambda z:\mathbb{Z} x:\mathbb{Z} \mapsto z + 2 \cdot x, 0, ds\right) = 2 \cdot \operatorname{cast}\left(\operatorname{div}\left(n + 1, 2\right), \mathbb{Z}\right)\right) \land p + 3 \cdot m + 2 \le \operatorname{length}\left(ds\right)\right) \Rightarrow \left(\exists lower \in \operatorname{List}\left(\mathbb{Z}\right),\; \exists k \in \mathbb{N},\; \left(\left(\left(\left(\operatorname{length}\left(lower\right) = p + 1 \land \operatorname{foldr}\left(\lambda z:\mathbb{Z} x:\mathbb{Z} \mapsto z + 2 \cdot x, 0, lower\right) = 2 \cdot T\right) \land \left(\forall i \in \mathbb{N},\; \operatorname{getD}\left(\operatorname{ite}\left(i < \operatorname{List.length}\left(lower\right), \operatorname{some}\left(\operatorname{GetElem.getElem}\left(lower, i\right)\right), \operatorname{none}\left(\right)\right), 0\right) \ne 0 \Rightarrow i + 2 \le p\right)\right) \land ds = \operatorname{append}\left(\operatorname{append}\left(lower, \operatorname{flatten}\left(\operatorname{replicate}\left(m, [1, 0, 0]\right)\right)\right), \operatorname{replicate}\left(k + 1, 0\right)\right)\right) \land \operatorname{getD}\left(\operatorname{ite}\left(0 < \operatorname{List.length}\left(\operatorname{reverse}\left(\operatorname{append}\left([0, 0], lower\right)\right)\right), \operatorname{some}\left(\operatorname{GetElem.getElem}\left(\operatorname{reverse}\left(\operatorname{append}\left([0, 0], lower\right)\right), 0\right)\right), \operatorname{none}\left(\right)\right), 0\right) = 0\right) \land \operatorname{getD}\left(\operatorname{ite}\left(1 < \operatorname{List.length}\left(\operatorname{reverse}\left(\operatorname{append}\left([0, 0], lower\right)\right)\right), \operatorname{some}\left(\operatorname{GetElem.getElem}\left(\operatorname{reverse}\left(\operatorname{append}\left([0, 0], lower\right)\right), 1\right)\right), \operatorname{none}\left(\right)\right), 0\right) = 0\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Palindromes/PeriodDoubling/MarkedPrefixExpansion.marked_prefix_expansion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Any nonadjacent signed expansion of twice the rounded half-endpoint, of length at least p+3m+2, consists of a lower tail of length p+1, then m blocks [1,0,0], then at least one leading zero. The lower tail evaluates to twice T and its nonzero positions i satisfy i+2 at most p. Adding the two initial zero memories gives two zero digits immediately before the selected marker, including p=0. The proof constructs the literal expansion, evaluates the geometric block, and applies nonadjacent digit uniqueness. div is natural integer quotient; option lookups have default zero.

## References

- Truth anchor: `D5/S1/Words/Palindromes/PeriodDoubling/MarkedPrefixExpansion.marked_prefix_expansion`
- Dependency: [D5/S1/Words/Palindromes/PeriodDoubling/CanonicalSignedDigits](CanonicalSignedDigits.md)
- Dependency: [D5/S1/Words/Palindromes/PeriodDoubling/MarkedPrefixArithmetic](MarkedPrefixArithmetic.md)
