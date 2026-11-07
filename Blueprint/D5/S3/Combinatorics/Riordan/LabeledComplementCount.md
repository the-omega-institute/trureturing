# LabeledComplementCount

## Abstract

Finite binary Riordan complements: LabeledComplementCount

**Theorem 1.1 (result).**

$$(\operatorname{a}\left(1\right) = 1) \land ((\operatorname{a}\left(2\right) = 2) \land (((\forall (n: \operatorname{Nat}), \left(3 \le n\right) \to \left((\operatorname{a}\left(n\right) : \operatorname{Int}) = 8 \cdot (\operatorname{a}\left((n - 2)\right) : \operatorname{Int}) - 4\right))) \land (((\forall (n: \operatorname{Nat}), \left(1 \le n\right) \to \left((\operatorname{a}\left((n + 1)\right) : \operatorname{Int}) - (\operatorname{a}\left(n\right) : \operatorname{Int}) = (2 : \operatorname{Int})^{(\operatorname{Nat}.\operatorname{div}\left(3 \cdot (n - 1), 2\right))}\right))) \land (((\forall (n: \operatorname{Nat}), \left(1 \le n\right) \to \left(\operatorname{a}\left(n\right) = 1 + \sum_{k \in \operatorname{Finset}.\operatorname{range}\left((n - 1)\right)} 2^{(\operatorname{Nat}.\operatorname{div}\left(3 \cdot k, 2\right))}\right))) \land (((\forall (n: \operatorname{Nat}), \left(2 \le n\right) \to \left(\operatorname{a}\left(n\right) = \operatorname{a113836}\left((n - 1)\right) + 1\right))) \land (((\forall (k: \operatorname{Nat}), \left(1 \le k\right) \to \left((\operatorname{a}\left((2 \cdot k)\right) : \operatorname{Rat}) = \frac{(10 \cdot (8 : \operatorname{Rat})^{(k - 1)} + 4)}{7}\right))) \land (((\forall (k: \operatorname{Nat}), (\operatorname{a}\left((2 \cdot k + 1)\right) : \operatorname{Rat}) = \frac{(3 \cdot (8 : \operatorname{Rat})^{k} + 4)}{7})) \land (\operatorname{ogf} = \operatorname{conjecturedOGF}))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Riordan/LabeledComplementCount.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Arnauld Mesinga Mwafise (2026). *OEIS A401496: labeled Riordan graphs with labeled Riordan complements*. URL: <https://oeis.org/A401496>.

*Commentary.*

The formula gives all five expressions for the count of fixed-label graphs, at every order in their stated domains. The finite quotient condition is r times delta squared equal to zero. First nonzero coefficients and their attainable tails give a bijective classification of the graphs. The expressions 108 and 38 in the source are read as the products 10 times 8 and 3 times 8; no author confirmation of the typography is asserted. The unlabeled problem in Section 5, Problem 3 of arXiv:1710.04604v2 is outside this statement.

Nat.div denotes floor division on natural numbers.

## References

- Truth anchor: `D5/S3/Combinatorics/Riordan/LabeledComplementCount.result`
- Dependency: [D5/S1/Recurrence/SquareRows/SquareExponentDyadicSupport](../../../S1/Recurrence/SquareRows/SquareExponentDyadicSupport.md)
- Dependency: [D5/S3/Combinatorics/Riordan/LabeledComplementAlgebra](LabeledComplementAlgebra.md)
- Dependency: [D5/S3/Combinatorics/Riordan/LabeledComplementClassification](LabeledComplementClassification.md)
