# The universal sharp upper bound

## Abstract

Every positive-dimensional perfect complex evolution algebra has a finite full automorphism group bounded by the partition maximum.

The multiplication is a complex bilinear map on an arbitrary finite-dimensional complex vector space. A natural basis has zero products between distinct basis vectors. Perfection is the equality between the span of all pair products and the entire space. The group Aut contains every multiplication-preserving complex LinearEquiv; no associativity or unit is assumed.

**Theorem 1.1 (The entire successor partition).**

$$\forall Q \in Type,\; \operatorname{Fintype}\left(Q\right) \Rightarrow \left(\operatorname{DecidableEq}\left(Q\right) \Rightarrow \left(\forall beta \in \operatorname{Perm}\left(Q\right),\; \operatorname{cycleWeight}\left(beta\right) \cdot \operatorname{NatCard}\left(\operatorname{centralizer}\left(beta\right)\right) = \operatorname{weight}\left(\operatorname{parts}\left(\operatorname{partition}\left(beta\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/QuadraticForms/EvolutionAlgebras/EvolutionSharpBound.cycle_weight_centralizer` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A permutation beta on Q has the full partition consisting of its nontrivial cycle lengths and one singleton for every fixed point. The existing independent root count contributes product_l (2^l-1)^(m_l). The full centralizer contributes product_l l^(m_l) m_l!, including m_1!. Their product is exactly weight(partition(beta)). The centralizer normalization reuses the Tau Ceti multiplicity formula and Mathlib's cardinality theorem.

**Theorem 1.2 (The arbitrary-carrier bound).**

$$\forall A \in Type,\; \operatorname{FiniteDimensionalComplexVectorSpace}\left(A\right) \Rightarrow \left(\forall I \in Type,\; \operatorname{Fintype}\left(I\right) \Rightarrow \left(\forall n \in \mathbb{N},\; 1 \le n \Rightarrow \left(\operatorname{finrank}\left(A\right) = n \Rightarrow \left(\forall mu \in \operatorname{BilinearProduct}\left(A\right),\; \forall b \in \operatorname{Basis}\left(I, \mathbb{C}, A\right),\; \operatorname{NaturalBasisAt}\left(mu, b\right) \Rightarrow \left(\operatorname{productSpan}\left(mu\right) = Top \Rightarrow \left(\operatorname{Finite}\left(\operatorname{Aut}\left(mu\right)\right) \land \operatorname{NatCard}\left(\operatorname{Aut}\left(mu\right)\right) \le \operatorname{maximumWeight}\left(n\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/QuadraticForms/EvolutionAlgebras/EvolutionSharpBound.finite_and_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite natural basis indexed by an arbitrary finite type I, finrank(A)=n and n>=1, the whole group is finite and its natural cardinality is at most maximumWeight(n). Transport first gives the actual joint bound on the least support quotient P. Every original fiber has size k(B)>=1, their sizes sum to n, and s=card(P) lies between one and n. Ascending-factorial monotonicity bounds the product of the actual fiber factorials by (n-s+1)!. The successor cycles partition s, not n. Their root and centralizer factors form the weight of a full partition of s, bounded by maximumWeight(s). The existing shifted absorption estimate yields maximumWeight(n). The internal block-action kernel is retained throughout; neither a faithful quotient action nor surjectivity onto graph automorphisms is required.

The upper bound is the universal inequality in Kaygorodov, Martín González and Viruel, arXiv:2610.22248v1, section 2.3, Conjecture 3, pages 27-28. The published statement is conjectural. EvolutionAutomorphismMaximum combines this inequality with actual attaining algebras.

## References

- Truth anchor: `D5/S3/QuadraticForms/EvolutionAlgebras/EvolutionSharpBound.cycle_weight_centralizer`
- Truth anchor: `D5/S3/QuadraticForms/EvolutionAlgebras/EvolutionSharpBound.finite_and_bound`
- Dependency: [D5/S0/Asymptotics/WeightedProbability/PermutationMultiplicity](../../../S0/Asymptotics/WeightedProbability/PermutationMultiplicity.md)
- Dependency: [D5/S3/Combinatorics/Partitions/EvolutionAutomorphismWeight](../../Combinatorics/Partitions/EvolutionAutomorphismWeight.md)
- Dependency: [D5/S3/QuadraticForms/EvolutionAlgebras/EvolutionBasisTransport](EvolutionBasisTransport.md)
