# Characterizing well-covered Cayley squares

## Abstract

A connected finite abelian Cayley graph has a well-covered Cartesian square exactly when it is complete, and exactly when every positive distance power of that square is well-covered.

**Theorem 1.1 (All finite abelian groups and all positive powers).**

$$\forall A \in \mathrm{Type},\; [\operatorname{Finite}\left(A\right)] [\operatorname{AddCommGroup}\left(A\right)] \forall S \in \operatorname{Set}\left(A\right),\; \left(\left(\neg \operatorname{Mem}\left(0, S\right)\right) \land \left(\forall z \in A,\; \operatorname{Mem}\left(z, S\right) \Rightarrow \operatorname{Mem}\left(\operatorname{neg}\left(z\right), S\right)\right)\right) \Rightarrow \left(\operatorname{Connected}\left(\operatorname{addCayley}\left(S\right)\right) \Rightarrow \left(\left(\operatorname{addCayley}\left(S\right) = \operatorname{completeGraph}\left(A\right) \Leftrightarrow \operatorname{WellCovered}\left(\operatorname{boxProd}\left(\operatorname{addCayley}\left(S\right), \operatorname{addCayley}\left(S\right)\right)\right)\right) \land \left(\operatorname{WellCovered}\left(\operatorname{boxProd}\left(\operatorname{addCayley}\left(S\right), \operatorname{addCayley}\left(S\right)\right)\right) \Leftrightarrow \left(\forall d \in \mathrm{Nat},\; 1 \le d \Rightarrow \operatorname{WellCovered}\left(\operatorname{power}\left(\operatorname{boxProd}\left(\operatorname{addCayley}\left(S\right), \operatorname{addCayley}\left(S\right)\right), d\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Products/CayleyCharacterization.cayley_square_characterization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* My Hanh Pham, Thanh Vu (2026). *On graphs whose powers are well-covered*. URL: <https://arxiv.org/abs/2610.09300v1>.

*Acknowledgement.* Bert L. Hartnell, Douglas F. Rall, Kirsti Wash (2017). *On well-covered Cartesian products*. URL: <https://arxiv.org/abs/1703.08716v1>.

*Commentary.*

The group is arbitrary finite additive abelian; its connection set avoids zero and is closed under negation. Well-covered means that every pair of inclusion-maximal independent vertex sets has equal cardinality. If the graph is not complete, its independence number is at least two. The nearly-empty-layer construction produces a maximal square-independent set of size at most (n-1) alpha+1, strictly below the maximum n alpha supplied by the Cayley difference construction. For a complete graph, independent square-sets are matchings between rows and columns. Maximality saturates all rows and columns, giving cardinality n. The square has diameter at most two, so every power from two onward is complete. The first-power identity supplies the reverse implication. The trivial group and complete graphs of every positive order are included. The natural-distance power is used only after establishing actual connectedness of the square, so it agrees with the reachability-based distance-power definition.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Products/CayleyCharacterization.cayley_square_characterization`
- Dependency: [D5/S3/Combinatorics/Graph/Products/NearEmptyLayer](NearEmptyLayer.md)
- Dependency: [D5/S3/Combinatorics/Graph/WellCoveredPowerCliqueProduct](../WellCoveredPowerCliqueProduct.md)
