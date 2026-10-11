# Intrinsic nilpotent block counts

## Abstract

Intrinsic nilpotent block counts are determined by all iterate ranks.

**Definition 1.1 (Finite nilpotent chain bases).**

$$\forall K \in \operatorname{Type},\; \forall V \in \operatorname{Type},\; [\operatorname{Field}\left(K\right)] [\operatorname{AddCommGroup}\left(V\right)] [\operatorname{Module}\left(K, V\right)] \forall N \in \operatorname{End}\left(K, V\right),\; \operatorname{ChainBasis}\left(N\right)$$

*Formalization.* `D5/S3/Quantum/SpinChains/NilpotentBlockCounts.ChainBasis` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a field K, a vector space V, and an endomorphism N, ChainBasis N stores a finite index type ι, a length function len : ι to the natural numbers with 1 <= len i, and a basis v of V indexed by the dependent sum of Fin (len i). Its shift field sends each nonterminal basis vector to the next position in the same chain, and its terminal field sends the position len i minus one to zero.

**Definition 1.2 (Kernel intersections with preceding power ranges).**

$$\forall K \in \operatorname{Type},\; \forall V \in \operatorname{Type},\; [\operatorname{Field}\left(K\right)] [\operatorname{AddCommGroup}\left(V\right)] [\operatorname{Module}\left(K, V\right)] \forall N \in \operatorname{End}\left(K, V\right),\; \forall j \in \mathbb{N},\; \operatorname{C}\left(N, j\right) = \operatorname{inf}\left(\operatorname{ker}\left(N\right), \operatorname{range}\left((N)^{j - 1}\right)\right)$$

*Formalization.* `D5/S3/Quantum/SpinChains/NilpotentBlockCounts.C` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a field K, a finite-dimensional K-vector space V, an endomorphism N, and a natural index j, C N j is the intersection of ker N with the range of N raised to j minus one. At j equal to one this is ker N. The successor spaces form a descending sequence.

**Definition 1.3 (Successive quotient dimensions).**

$$\forall K \in \operatorname{Type},\; \forall V \in \operatorname{Type},\; [\operatorname{Field}\left(K\right)] [\operatorname{AddCommGroup}\left(V\right)] [\operatorname{Module}\left(K, V\right)] [\operatorname{FiniteDimensional}\left(K, V\right)] \forall N \in \operatorname{End}\left(K, V\right),\; \forall j \in \mathbb{N},\; \operatorname{blockCount}\left(N, j\right) = \operatorname{finrank}\left(K, \operatorname{quotient}\left(\operatorname{C}\left(N, j\right), \operatorname{comap}\left(\operatorname{subtype}\left(\operatorname{C}\left(N, j\right)\right), \operatorname{C}\left(N, j + 1\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/SpinChains/NilpotentBlockCounts.blockCount` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The block count at j is the K-dimension of C N j modulo the copy of C N (j plus one) inside C N j. This quotient records the new kernel vectors that first occur at that level.

**Theorem 1.4 (The rank formula for intrinsic block counts).**

$$\forall K \in \operatorname{Type},\; \forall V \in \operatorname{Type},\; [\operatorname{Field}\left(K\right)] [\operatorname{AddCommGroup}\left(V\right)] [\operatorname{Module}\left(K, V\right)] [\operatorname{FiniteDimensional}\left(K, V\right)] \forall N \in \operatorname{End}\left(K, V\right),\; \forall j \in \mathbb{N},\; (1 \le j) \Rightarrow (\operatorname{IntCast}\left(\operatorname{blockCount}\left(N, j\right)\right) = \operatorname{IntCast}\left(\operatorname{finrank}\left(K, \operatorname{range}\left((N)^{j - 1}\right)\right)\right) - 2 \times \operatorname{IntCast}\left(\operatorname{finrank}\left(K, \operatorname{range}\left((N)^{j}\right)\right)\right) + \operatorname{IntCast}\left(\operatorname{finrank}\left(K, \operatorname{range}\left((N)^{j + 1}\right)\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/SpinChains/NilpotentBlockCounts.blockCount_rank_formula` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For j at least one, the map N restricted to range N raised to j minus one has image range N raised to j and kernel C N j. Rank-nullity therefore gives the additive identity dim C N j plus rho(j) equals rho(j minus one). Applying this identity at j and at j plus one, together with the quotient dimension identity for C N j modulo C N (j plus one), yields the displayed integer formula. The calculation stays in integer casts of additive equalities and does not use truncated natural subtraction.

**Theorem 1.5 (Iterate ranks determine every block count).**

$$\forall K \in \operatorname{Type},\; \forall V \in \operatorname{Type},\; \forall W \in \operatorname{Type},\; [\operatorname{Field}\left(K\right)] [\operatorname{AddCommGroup}\left(V\right)] [\operatorname{Module}\left(K, V\right)] [\operatorname{FiniteDimensional}\left(K, V\right)] [\operatorname{AddCommGroup}\left(W\right)] [\operatorname{Module}\left(K, W\right)] [\operatorname{FiniteDimensional}\left(K, W\right)] \forall N \in \operatorname{End}\left(K, V\right),\; \forall Nprime \in \operatorname{End}\left(K, W\right),\; (\forall r \in \mathbb{N},\; \operatorname{finrank}\left(K, \operatorname{range}\left((N)^{r}\right)\right) = \operatorname{finrank}\left(K, \operatorname{range}\left((Nprime)^{r}\right)\right)) \Rightarrow (\forall j \in \mathbb{N},\; \operatorname{blockCount}\left(N, j\right) = \operatorname{blockCount}\left(Nprime, j\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/SpinChains/NilpotentBlockCounts.blockCount_eq_of_range_finrank_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If two endomorphisms over the same field have equal finite-dimensional ranks for every natural power, the rank formula gives equal block counts at every index. The index zero quotient is zero on both sides, and positive indices use the formula.

## References

- Truth anchor: `D5/S3/Quantum/SpinChains/NilpotentBlockCounts.C`
- Truth anchor: `D5/S3/Quantum/SpinChains/NilpotentBlockCounts.ChainBasis`
- Truth anchor: `D5/S3/Quantum/SpinChains/NilpotentBlockCounts.blockCount`
- Truth anchor: `D5/S3/Quantum/SpinChains/NilpotentBlockCounts.blockCount_eq_of_range_finrank_eq`
- Truth anchor: `D5/S3/Quantum/SpinChains/NilpotentBlockCounts.blockCount_rank_formula`
