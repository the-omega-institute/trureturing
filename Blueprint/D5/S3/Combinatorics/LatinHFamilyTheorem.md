# Three transversals of the H family

## Abstract

For every integer k at least nine, the literal H square has the three displayed transversals. Every two transversals meet, although no entry belongs to all transversals.

**Theorem 1.1 (Uniform coordinate permutations).**

$$\forall k \in \mathrm{Nat},\; 9 \le k \Rightarrow \left(\forall j \in \operatorname{Fin}\left(3\right),\; \operatorname{Bijective}\left(\operatorname{column}\left(k, j\right)\right) \land \operatorname{Bijective}\left(\operatorname{symbol}\left(k, j\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/LatinHFamilyTheorem.coordinate_permutations` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Afsane Ghafari, Ian M. Wanless (2026). *Latin Squares whose transversals intersect in unusual ways*. DOI: [10.48550/arXiv.2607.17547](https://doi.org/10.48550/arXiv.2607.17547). URL: <https://arxiv.org/abs/2607.17547v1>.

*Commentary.*

For each of the three profiles, the six cap complement certificates exclude every column and symbol of the four bulk classes. The head, bulk and tail rows exhaust the square. Internal injectivity and this exclusion make each complete coordinate map a bijection, including the empty bulk when k equals nine.

**Theorem 1.2 (The distinguished-entry obstruction).**

$$\forall k \in \mathrm{Nat},\; 9 \le k \Rightarrow \left(\forall S \in \operatorname{Set}\left(\operatorname{Prod}\left(\operatorname{Fin}\left(\operatorname{order}\left(k\right)\right), \operatorname{Prod}\left(\operatorname{Fin}\left(\operatorname{order}\left(k\right)\right), \operatorname{Fin}\left(\operatorname{order}\left(k\right)\right)\right)\right)\right),\; \operatorname{IsTransversal}\left(k, S\right) \Rightarrow 2 \le \operatorname{ncard}\left(\operatorname{inter}\left(\operatorname{D}\left(k\right), S\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/LatinHFamilyTheorem.transversal_obstruction` (`✓ std3`). ∎

*Citation.* Afsane Ghafari, Ian M. Wanless (2026). *Latin Squares whose transversals intersect in unusual ways*. DOI: [10.48550/arXiv.2607.17547](https://doi.org/10.48550/arXiv.2607.17547). URL: <https://arxiv.org/abs/2607.17547v1>.

*Commentary.*

Choosing the unique entry in each row of an arbitrary transversal gives column and symbol permutations. Their sums force the total priority increment to be congruent to two k modulo four k. The row lower bounds sum to minus two k plus three. If at most one distinguished entry is selected, the upper bound is two k minus three, which contradicts that congruence.

**Theorem 1.3 (The complete H-family theorem).**

$$\forall K \in \mathrm{Int},\; 9 \le K \Rightarrow \left(\operatorname{IsLatin}\left(\operatorname{order}\left(\operatorname{toNat}\left(K\right)\right), \operatorname{square}\left(\operatorname{toNat}\left(K\right)\right)\right) \Rightarrow \left(\operatorname{intCast}\left(\operatorname{order}\left(\operatorname{toNat}\left(K\right)\right)\right) = 4 \cdot K \land \left(\left(\forall j \in \operatorname{Fin}\left(3\right),\; \left(\operatorname{Bijective}\left(\operatorname{column}\left(\operatorname{toNat}\left(K\right), j\right)\right) \land \operatorname{Bijective}\left(\operatorname{symbol}\left(\operatorname{toNat}\left(K\right), j\right)\right)\right) \land \left(\left(\forall a \in \operatorname{Fin}\left(\operatorname{order}\left(\operatorname{toNat}\left(K\right)\right)\right),\; \operatorname{symbol}\left(\operatorname{toNat}\left(K\right), j, a\right) = \operatorname{square}\left(\operatorname{toNat}\left(K\right), a, \operatorname{column}\left(\operatorname{toNat}\left(K\right), j, a\right)\right)\right) \land \left(\operatorname{IsTransversal}\left(\operatorname{toNat}\left(K\right), \operatorname{T}\left(\operatorname{toNat}\left(K\right), j\right)\right) \land \operatorname{inter}\left(\operatorname{T}\left(\operatorname{toNat}\left(K\right), j\right), \operatorname{D}\left(\operatorname{toNat}\left(K\right)\right)\right) = \operatorname{diff}\left(\operatorname{D}\left(\operatorname{toNat}\left(K\right)\right), \left\{\operatorname{distinguished}\left(\operatorname{toNat}\left(K\right), j\right)\right\}\right)\right)\right)\right) \land \left(\operatorname{inter}\left(\operatorname{T}\left(\operatorname{toNat}\left(K\right), 0\right), \operatorname{T}\left(\operatorname{toNat}\left(K\right), 1\right)\right) = \left\{\operatorname{d2}\left(\operatorname{toNat}\left(K\right)\right)\right\} \land \left(\operatorname{inter}\left(\operatorname{inter}\left(\operatorname{T}\left(\operatorname{toNat}\left(K\right), 0\right), \operatorname{T}\left(\operatorname{toNat}\left(K\right), 1\right)\right), \operatorname{T}\left(\operatorname{toNat}\left(K\right), 2\right)\right) = \left\{\right\} \land \left(\left(\forall S \in \operatorname{Set}\left(\operatorname{Prod}\left(\operatorname{Fin}\left(\operatorname{order}\left(\operatorname{toNat}\left(K\right)\right)\right), \operatorname{Prod}\left(\operatorname{Fin}\left(\operatorname{order}\left(\operatorname{toNat}\left(K\right)\right)\right), \operatorname{Fin}\left(\operatorname{order}\left(\operatorname{toNat}\left(K\right)\right)\right)\right)\right)\right),\; \forall U \in \operatorname{Set}\left(\operatorname{Prod}\left(\operatorname{Fin}\left(\operatorname{order}\left(\operatorname{toNat}\left(K\right)\right)\right), \operatorname{Prod}\left(\operatorname{Fin}\left(\operatorname{order}\left(\operatorname{toNat}\left(K\right)\right)\right), \operatorname{Fin}\left(\operatorname{order}\left(\operatorname{toNat}\left(K\right)\right)\right)\right)\right)\right),\; \operatorname{IsTransversal}\left(\operatorname{toNat}\left(K\right), S\right) \Rightarrow \left(\operatorname{IsTransversal}\left(\operatorname{toNat}\left(K\right), U\right) \Rightarrow \left(\exists e \in \operatorname{Prod}\left(\operatorname{Fin}\left(\operatorname{order}\left(\operatorname{toNat}\left(K\right)\right)\right), \operatorname{Prod}\left(\operatorname{Fin}\left(\operatorname{order}\left(\operatorname{toNat}\left(K\right)\right)\right), \operatorname{Fin}\left(\operatorname{order}\left(\operatorname{toNat}\left(K\right)\right)\right)\right)\right),\; e \in S \land e \in U\right)\right)\right) \land \left(\forall e \in \operatorname{Prod}\left(\operatorname{Fin}\left(\operatorname{order}\left(\operatorname{toNat}\left(K\right)\right)\right), \operatorname{Prod}\left(\operatorname{Fin}\left(\operatorname{order}\left(\operatorname{toNat}\left(K\right)\right)\right), \operatorname{Fin}\left(\operatorname{order}\left(\operatorname{toNat}\left(K\right)\right)\right)\right)\right),\; \neg \operatorname{IsPinned}\left(\operatorname{toNat}\left(K\right), e\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/LatinHFamilyTheorem.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Afsane Ghafari, Ian M. Wanless (2026). *Latin Squares whose transversals intersect in unusual ways*. DOI: [10.48550/arXiv.2607.17547](https://doi.org/10.48550/arXiv.2607.17547). URL: <https://arxiv.org/abs/2607.17547v1>.

*Commentary.*

The parameter is an integer at least nine; its natural representative has exactly the same value and gives order four k. Latinness of the actual square is the explicit cited premise. Each literal profile gives one source entry in every row, column and symbol, contains precisely the two distinguished entries indexed by the other profiles, and the first two profiles meet exactly at the third distinguished entry. Their triple intersection is empty. Every arbitrary transversal contains at least two of the three distinguished entries, so any two transversals meet. The three explicit witnesses rule out every pinned entry.

## References

- Truth anchor: `D5/S3/Combinatorics/LatinHFamilyTheorem.coordinate_permutations`
- Truth anchor: `D5/S3/Combinatorics/LatinHFamilyTheorem.result`
- Truth anchor: `D5/S3/Combinatorics/LatinHFamilyTheorem.transversal_obstruction`
- Dependency: [D5/S3/Combinatorics/LatinHTransversals](LatinHTransversals.md)
