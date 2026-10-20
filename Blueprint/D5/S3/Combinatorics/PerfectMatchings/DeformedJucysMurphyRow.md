# Native Components and the Exact Occurrence Row

## Abstract

The native operator sum has the exact occurrence row on complete coset types, with charges evaluated on the output matching.

Let k be a natural number, K the rational function field over the complex numbers, and b an arbitrary element of K. A native matching p is a fixed-point-free involutive partner map on Fin(2k). The identity matching pairs 2h with 2h+1. Connectivity uses both its edges and p's edges. The complete partition ct(p) contains, once for every component, the number of its identity edges. A doubled identity and matching edge contributes the part one. The indicator of a partition lambda is one precisely when ct(p)=lambda and zero otherwise.

Write v(q)=2q. For h in Fin(q), the earlier identity edge has endpoints 2h and 2h+1. Let aEq(p,q,h) be its unique endpoint with the same charge as v(q), and aOpp(p,q,h) its other endpoint. These are charges of the output p, computed by the alternating walk with its component maximum positive. Conjugation act(a,c,p) swaps the labels a and c in p. The literal operator sum is S(b,k)=sum over q in Fin(k) of J(b,k,q+1), using the native J.

**Theorem 1.1 (Exact Expansion over Identity Edge Pairs).**

$$\forall b \in K,\; \forall k \in Nat,\; \forall f \in \operatorname{Function}\left(\operatorname{P}\left(k\right), K\right),\; \forall p \in \operatorname{P}\left(k\right),\; \operatorname{apply}\left(\operatorname{S}\left(b, k\right), f, p\right) = \sum_{q\in\operatorname{Fin}\left(k\right)}{\sum_{h\in\operatorname{Fin}\left(q\right)}{\operatorname{apply}\left(f, \operatorname{act}\left(\operatorname{aEq}\left(p, q, h\right), \operatorname{v}\left(q\right), p\right)\right)+b\cdot\operatorname{apply}\left(f, \operatorname{act}\left(\operatorname{aOpp}\left(p, q, h\right), \operatorname{v}\left(q\right), p\right)\right)}}$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PerfectMatchings/DeformedJucysMurphyComponents.native_pair_expansion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Coulter, Xavier; Do, Norman (2025). *From Weingarten calculus for real Grassmannians to deformations of monotone Hurwitz numbers and Jucys–Murphy elements*. DOI: [10.48550/arXiv.2506.04002](https://doi.org/10.48550/arXiv.2506.04002). URL: <https://arxiv.org/abs/2506.04002v1>.

*Commentary.*

Reindex the 2q summands of J at q+1 by Fin(q) times Fin(2). Charge reverses on every identity edge, so exactly one earlier endpoint has the same output charge as v(q). Its weight is one; the other's weight is b. The two terms can therefore be placed in the displayed order for every function f. The empty sums cover q=0 and k=0. Taking b equal to the rational function variable and f equal to a complete-partition indicator gives the corresponding literal indicator expansion.

For source partition rho and target partition lambda, define B_b(rho,lambda) as follows. For every occurrence r in rho, the cut contribution is r/2 times the sum over 0<d<r of the indicator that lambda is rho with that occurrence r replaced by d and r-d. For every ordered pair of distinct occurrences r,s, the join contribution is (1+b)rs/2 times the indicator that lambda is obtained by replacing those occurrences by r+s. The diagonal contribution is b times the sum of binomial(r,2) over the occurrences of rho, times the indicator that lambda=rho. Multiset erasure removes one occurrence, so repeated parts and equal splits retain their multiplicities. This is rowCoefficient(b,rho,lambda).

**Theorem 1.2 (Exact Native Row and C1).**

$$\forall b \in K,\; \forall k \in Nat,\; \forall lambda \in \operatorname{Partition}\left(k\right),\; \forall p \in \operatorname{P}\left(k\right),\; \operatorname{apply}\left(\operatorname{S}\left(b, k\right), \operatorname{indicator}\left(lambda\right), p\right) = \operatorname{rowCoefficient}\left(b, \operatorname{ct}\left(p\right), lambda\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PerfectMatchings/DeformedJucysMurphyRow.native_row` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Coulter, Xavier; Do, Norman (2025). *From Weingarten calculus for real Grassmannians to deformations of monotone Hurwitz numbers and Jucys–Murphy elements*. DOI: [10.48550/arXiv.2506.04002](https://doi.org/10.48550/arXiv.2506.04002). URL: <https://arxiv.org/abs/2506.04002v1>.

*Commentary.*

The equal-charge transposition cuts a component at its exact rotation displacement d into d and r-d identity edges. The proof identifies literal edge occurrences with rotation powers, proves the reverse orientation has the same complete type, and counts the two orientations of each native edge pair. Distinct components join with both charge choices and coefficient 1+b; an internal opposite-charge choice preserves the complete type. The empty displacement range handles singleton components, and partner transpositions are included in the diagonal count. No surgery or correspondence hypothesis is assumed.

Setting b=X gives C1 with the concrete coefficient function c_lambda(rho)=B_X(rho,lambda), for every k and every native output p. The occurrence bridge identifies this exact coefficient with the literal differential operator coefficient. The companion integration proves same-coefficient C2, every-partition matching realization. The Components narrative records the full singleton-inclusive product-orbit multiset as a consequence of the reused frozen split.

## References

- Truth anchor: `D5/S3/Combinatorics/PerfectMatchings/DeformedJucysMurphyComponents.native_pair_expansion`
- Truth anchor: `D5/S3/Combinatorics/PerfectMatchings/DeformedJucysMurphyRow.native_row`
- Dependency: [D5/S3/Combinatorics/PerfectMatchings/DeformedJucysMurphyCuts](DeformedJucysMurphyCuts.md)
