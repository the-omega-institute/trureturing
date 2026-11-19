# Products of ternary comparison structures

## Abstract

Products of ternary comparison structures, with multiplied feature ranks.

**Definition 1.1 (The product structure).**

Lean statement: `D5/S3/Quantum/AURICOmega/TernaryComparisonProduct.prod`

*Formalization.* `D5/S3/Quantum/AURICOmega/TernaryComparisonProduct.prod` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Issai Schur (1911). *Bemerkungen zur Theorie der beschränkten Bilinearformen mit unendlich vielen Veränderlichen*. DOI: [10.1515/crll.1911.140.1](https://doi.org/10.1515/crll.1911.140.1). URL: <https://doi.org/10.1515/crll.1911.140.1>.

*Commentary.*

For ternary comparison structures C on M and D on N, prod C D is the ternary comparison structure on M x N defined componentwise. Its transfer sends p, q, r to the pair whose first component is the transfer of C applied to the first components, tri of C at p.1, q.1, r.1, and whose second component is the transfer of D applied to the second components, tri of D at p.2, q.2, r.2. Its reading at p, q is the reading of C at p.1, q.1 times the reading of D at p.2, q.2. The transfer identities and the invariance of the reading hold in each coordinate. The product reading equals one exactly on the diagonal because the readings of C and of D both lie in the interval from 0 to 1, so a product equal to one forces both factors to be one. The upper bound one for the reading of C at x, y holds because the Gram form of C for the pair x, y with coefficients 1 and -1 equals 2 minus twice that reading and is nonnegative; the same holds for D. Every finite Gram matrix of the product reading is the entrywise product of the corresponding Gram matrices of the readings of C and of D, and the entrywise product of two positive semidefinite matrices is positive semidefinite by the Schur product theorem.

**Theorem 1.2 (Feature ranks multiply).**

$$\forall M \in \operatorname{Type}*, N \in \operatorname{Type}*,\; \forall C \in \operatorname{TernaryComparison}\left(M\right),\; \forall D \in \operatorname{TernaryComparison}\left(N\right),\; \forall r \in \mathbb{N}, s \in \mathbb{N},\; \operatorname{HasFeatureRank}\left(C, r\right) \Rightarrow \left(\operatorname{HasFeatureRank}\left(D, s\right) \Rightarrow \operatorname{HasFeatureRank}\left(\operatorname{prod}\left(C, D\right), r \cdot s\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/AURICOmega/TernaryComparisonProduct.prod_hasFeatureRank` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If the reading of C at x, y is the inner product of f x and f y for a map f from M into Euclidean r-space, and the reading of D at u, v is the inner product of g u and g v for a map g from N into Euclidean s-space, then the map sending p to the vector with coordinates (f p.1)_i * (g p.2)_j, indexed by the pairs (i, j) enumerated as Fin (r * s), lands in Euclidean (r * s)-space. Its inner products are the double sums over i and j of (f p.1)_i (f q.1)_i (g p.2)_j (g q.2)_j, which factor as the product of the two inner products, that is the product reading.

**Proposition 1.3 (Chain connectivity of the product).**

$$\forall M \in \operatorname{Type}*, N \in \operatorname{Type}*,\; \forall C \in \operatorname{TernaryComparison}\left(M\right),\; \forall D \in \operatorname{TernaryComparison}\left(N\right),\; \operatorname{ChainConnected}\left(C\right) \Rightarrow \left(\operatorname{ChainConnected}\left(D\right) \Rightarrow \operatorname{ChainConnected}\left(\operatorname{prod}\left(C, D\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/AURICOmega/TernaryComparisonProduct.prod_chainConnected` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Given e > 0 and points (u1, u2) and (v1, v2), a chain from u1 to v1 in M with consecutive readings above 1 - e becomes a chain from (u1, u2) to (v1, u2) in the product, because the second coordinate stays at u2 and the reading of u2 with itself is one. Likewise a chain from u2 to v2 in N becomes a chain from (v1, u2) to (v1, v2). Concatenating the two chains joins the given points.

**Proposition 1.4 (Order sensitivity from the left factor).**

$$\forall M \in \operatorname{Type}*, N \in \operatorname{Type}*,\; \forall C \in \operatorname{TernaryComparison}\left(M\right),\; \forall D \in \operatorname{TernaryComparison}\left(N\right),\; [\operatorname{Nonempty}\left(N\right)] \operatorname{Noncommutative}\left(C\right) \Rightarrow \operatorname{Noncommutative}\left(\operatorname{prod}\left(C, D\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/AURICOmega/TernaryComparisonProduct.prod_noncommutative_left` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If tri x y z differs from tri z y x in M and w is any point of the nonempty carrier N, then the triple (x, w), (y, w), (z, w) is order sensitive in the product, since the first coordinates of the two transfers already differ.

**Proposition 1.5 (Small readings from the left factor).**

$$\forall M \in \operatorname{Type}*, N \in \operatorname{Type}*,\; \forall C \in \operatorname{TernaryComparison}\left(M\right),\; \forall D \in \operatorname{TernaryComparison}\left(N\right),\; [\operatorname{Nonempty}\left(N\right)] \operatorname{TouchesZero}\left(C\right) \Rightarrow \operatorname{TouchesZero}\left(\operatorname{prod}\left(C, D\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/AURICOmega/TernaryComparisonProduct.prod_touchesZero_left` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Given e > 0, choose x and y in M with reading below e and any point w of the nonempty carrier N. The product reading of (x, w) and (y, w) is the reading of x and y times the reading of w with itself, which is one, so it is below e.

## References

- Truth anchor: `D5/S3/Quantum/AURICOmega/TernaryComparisonProduct.prod`
- Truth anchor: `D5/S3/Quantum/AURICOmega/TernaryComparisonProduct.prod_chainConnected`
- Truth anchor: `D5/S3/Quantum/AURICOmega/TernaryComparisonProduct.prod_hasFeatureRank`
- Truth anchor: `D5/S3/Quantum/AURICOmega/TernaryComparisonProduct.prod_noncommutative_left`
- Truth anchor: `D5/S3/Quantum/AURICOmega/TernaryComparisonProduct.prod_touchesZero_left`
- Dependency: [D5/S3/Quantum/AURICOmega/TernaryComparisonGroup](TernaryComparisonGroup.md)
