# The counted point-to-edge bridge

## Abstract

Shifting every upper coordinate by one gives an exact counted equivalence between the literal triangular family and bounded ordered-edge closure.

**Definition 1.1 (The strict edge triangle).**

$$\forall n \in \operatorname{Nat}\left(\right),\; \operatorname{edgeTriangle}\left(n\right) = \{p \in \operatorname{Prod}\left(\operatorname{Nat}\left(\right), \operatorname{Nat}\left(\right)\right)| (\operatorname{fst}\left(p\right) < \operatorname{snd}\left(p\right)) \land (\operatorname{snd}\left(p\right) \le n + 1)\}$$

*Formalization.* `D5/S3/Combinatorics/BinomialBases/MazorchukXuFamilies.edgeTriangle` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Volodymyr Mazorchuk, Shuoyang Xu (2026). *On the number of cokernel-closed additive subcategories for uniformly oriented A_n quivers*. DOI: [10.48550/arXiv.2610.07999](https://doi.org/10.48550/arXiv.2610.07999). URL: <https://arxiv.org/html/2610.07999v2>.

*Commentary.*

The vertex set is zero through n+1, and every selected edge has strictly increasing endpoints.

**Definition 1.2 (Points become edges).**

$$\forall Y \in \operatorname{Finset}\left(\operatorname{Prod}\left(\operatorname{Nat}\left(\right), \operatorname{Nat}\left(\right)\right)\right),\; \operatorname{edgeSet}\left(Y\right) = \{q \in \operatorname{Prod}\left(\operatorname{Nat}\left(\right), \operatorname{Nat}\left(\right)\right)| \exists p \in Y,\; q = (\operatorname{fst}\left(p\right), \operatorname{snd}\left(p\right) + 1)\}$$

*Formalization.* `D5/S3/Combinatorics/BinomialBases/MazorchukXuFamilies.edgeSet` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Volodymyr Mazorchuk, Shuoyang Xu (2026). *On the number of cokernel-closed additive subcategories for uniformly oriented A_n quivers*. DOI: [10.48550/arXiv.2610.07999](https://doi.org/10.48550/arXiv.2610.07999). URL: <https://arxiv.org/html/2610.07999v2>.

*Commentary.*

Shift the second coordinate up by one. This map is injective on all natural pairs and preserves the zero first coordinate.

**Definition 1.3 (Edges become points).**

$$\forall A \in \operatorname{Finset}\left(\operatorname{Prod}\left(\operatorname{Nat}\left(\right), \operatorname{Nat}\left(\right)\right)\right),\; \operatorname{pointSet}\left(A\right) = \{q \in \operatorname{Prod}\left(\operatorname{Nat}\left(\right), \operatorname{Nat}\left(\right)\right)| \exists p \in A,\; q = (\operatorname{fst}\left(p\right), \operatorname{snd}\left(p\right) - 1)\}$$

*Formalization.* `D5/S3/Combinatorics/BinomialBases/MazorchukXuFamilies.pointSet` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Volodymyr Mazorchuk, Shuoyang Xu (2026). *On the number of cokernel-closed additive subcategories for uniformly oriented A_n quivers*. DOI: [10.48550/arXiv.2610.07999](https://doi.org/10.48550/arXiv.2610.07999). URL: <https://arxiv.org/html/2610.07999v2>.

*Commentary.*

Shift the second coordinate down by one. On strict natural edges this is inverse to edgeSet.

**Definition 1.4 (The bounded ordered-edge family).**

$$\forall n \in \operatorname{Nat}\left(\right),\; \forall k \in \operatorname{Nat}\left(\right),\; \operatorname{edgeFamily}\left(n, k\right) = \{A \in \operatorname{Finset}\left(\operatorname{Prod}\left(\operatorname{Nat}\left(\right), \operatorname{Nat}\left(\right)\right)\right)| ((A \subseteq \operatorname{edgeTriangle}\left(n\right)) \land (\operatorname{Rules}\left(\operatorname{pairMembership}\left(A\right)\right))) \land (\operatorname{firstColumnCard}\left(A\right) = k)\}$$

*Formalization.* `D5/S3/Combinatorics/BinomialBases/MazorchukXuFamilies.edgeFamily` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Volodymyr Mazorchuk, Shuoyang Xu (2026). *On the number of cokernel-closed additive subcategories for uniformly oriented A_n quivers*. DOI: [10.48550/arXiv.2610.07999](https://doi.org/10.48550/arXiv.2610.07999). URL: <https://arxiv.org/html/2610.07999v2>.

*Commentary.*

The notation pairMembership(A)(a,b) means (a,b) belongs to A. Every subset of the strict edge triangle is tested against both rules and the exact first-column statistic.

**Theorem 1.5 (Equality of the finite counts).**

$$\forall n \in \operatorname{Nat}\left(\right),\; \forall k \in \operatorname{Nat}\left(\right),\; \operatorname{count}\left(n, k\right) = \operatorname{card}\left(\operatorname{edgeFamily}\left(n, k\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/BinomialBases/MazorchukXuFamilies.count_eq_edgeFamily_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Volodymyr Mazorchuk, Shuoyang Xu (2026). *On the number of cokernel-closed additive subcategories for uniformly oriented A_n quivers*. DOI: [10.48550/arXiv.2610.07999](https://doi.org/10.48550/arXiv.2610.07999). URL: <https://arxiv.org/html/2610.07999v2>.

*Commentary.*

The two coordinate shifts are inverse on their bounded domains, preserve closure in both directions and preserve the first-column count. A finite-set bijection therefore gives the equality for all natural n and k. This includes empty subsets, zero first-column counts, n=0 and every valid deficit. It introduces no representation-theoretic assumption.

## References

- Truth anchor: `D5/S3/Combinatorics/BinomialBases/MazorchukXuFamilies.count_eq_edgeFamily_card`
- Truth anchor: `D5/S3/Combinatorics/BinomialBases/MazorchukXuFamilies.edgeFamily`
- Truth anchor: `D5/S3/Combinatorics/BinomialBases/MazorchukXuFamilies.edgeSet`
- Truth anchor: `D5/S3/Combinatorics/BinomialBases/MazorchukXuFamilies.edgeTriangle`
- Truth anchor: `D5/S3/Combinatorics/BinomialBases/MazorchukXuFamilies.pointSet`
- Dependency: [D5/S3/Combinatorics/BinomialBases/MazorchukXuClosure](MazorchukXuClosure.md)
