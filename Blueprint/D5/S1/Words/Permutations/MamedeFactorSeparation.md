# Separated Source Factors

## Abstract

Equal-product source shapes are unique when their interior endpoints satisfy j<i.

**Theorem 1.1 (Conditional uniqueness for j<i).**

$$1 \le m < j < i < M \le n \land \operatorname {ReducedConsecutive}\left(n, a\right) \land \operatorname {ReducedConsecutive}\left(n, b\right) \land \operatorname {WordProduct}\left(n, a\right) = \operatorname {WordProduct}\left(n, b\right) \land \operatorname {SourceShape}\left(m, M, i, j, a, p, q\right) \land \operatorname {SourceShape}\left(m, M, i, j, b, r, s\right) \implies a = b$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Permutations/MamedeFactorSeparation.source_shape_unique_of_j_lt_i` (`✓ std3`). ∎

*Citation.* Ricardo Mamede, Jose Luis Santos, Diogo Soares (2026). *Maximum number of one-element commutation classes of a permutation*. DOI: [10.48550/arXiv.2601.09395](https://doi.org/10.48550/arXiv.2601.09395).

*Commentary.*

For arbitrary n,m,M,i,j with 1<=m<j<i<M<=n, let a and b be reduced consecutive adjacent-swap words with the same permutation product. Assume a=p++fullExcursion(m,M,i,j)++q and b=r++fullExcursion(m,M,i,j)++s, with every prefix generator strictly between m and j and every suffix generator strictly between i and M. Then a=b. The central product fixes the prefix positions [m+1,j] and suffix positions [i+1,M]. An extra descent relates it to the existing deleted-excursion action formula; this descent is empty when i=j+1. Commuting the central product past the suffixes and cancelling it leaves equal products on disjoint supports. Pointwise evaluation recovers the prefix products; cancellation recovers the suffix products. Reducedness and consecutiveness pass to each subword. Nonempty prefixes end at their common maximum j-1 and nonempty suffixes start at their common minimum i+1, so extremal endpoint uniqueness identifies them. Empty subwords are handled by minimality against the empty representative. This formalizes the factor-separation argument in Proposition 3.7, conditional on both source shapes. It assumes no oscillation or endpoint equations. This theorem takes both shapes as inputs. The order-free fiber theorem derives them under j<i endpoint data, and the nonoscillating source-endpoint theorem derives those data in the first orientation. No global Conjecture 5.1 resolution or KPI change follows.

## References

- Truth anchor: `D5/S1/Words/Permutations/MamedeFactorSeparation.source_shape_unique_of_j_lt_i`
- Dependency: [D5/S1/Words/Permutations/MamedeEndpointUniqueness](MamedeEndpointUniqueness.md)
- Dependency: [D5/S1/Words/Permutations/MamedeSourceAction](MamedeSourceAction.md)
