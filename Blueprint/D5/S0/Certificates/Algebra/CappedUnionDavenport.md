# Relative Davenport constants of the capped union monoid

## Abstract

Every relative Davenport constant of the capped union monoid P_fin(U) x {0,1,2} equals |A|+k.

**Definition 1.1 (Elements of S_U).**

$$\operatorname{Capped}\left(U\right) = \operatorname{Prod}\left(\operatorname{Finset}\left(U\right), \operatorname{Fin}\left(3\right)\right)$$

*Formalization.* `D5/S0/Certificates/Algebra/CappedUnionDavenport.Capped` (`✓ std3`).

*Citation.* Haobo Ma; Wenlin Zhang (2026). *Counterexamples to Wang's Conjectures 3.26 and 5.3 on semigroup algebras*. DOI: [10.5281/zenodo.23884901](https://doi.org/10.5281/zenodo.23884901).

*Commentary.*

An element of S_U is a pair (A,i) of a finite subset A of U and a level i in {0,1,2}. With decidable equality on U, addition is (A,i)+(B,j)=(A union B, min(2,i+j)) and the identity is (empty,0); these make S_U a commutative monoid, and a finite sum has the union of the supports and the capped total level.

**Definition 1.2 (Minimal sequences).**

$$(\operatorname{MinimalFor}\left(f, t\right)) \Leftrightarrow ((\operatorname{sum}\left(f\right) = t) \land (\forall I \in \operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right),\; (I \ne univ) \Rightarrow (\operatorname{sum}\left(I, f\right) \ne t)))$$

*Formalization.* `D5/S0/Certificates/Algebra/CappedUnionDavenport.MinimalFor` (`✓ std3`).

*Citation.* Haobo Ma; Wenlin Zhang (2026). *Counterexamples to Wang's Conjectures 3.26 and 5.3 on semigroup algebras*. DOI: [10.5281/zenodo.23884901](https://doi.org/10.5281/zenodo.23884901).

*Commentary.*

In any commutative monoid M, a sequence f of length n sums to t and no proper subsequence, indexed by a proper subset of the positions and including the empty one, sums to t.

**Definition 1.3 (Lengths of minimal sequences).**

$$\operatorname{minimalLengths}\left(t\right) = (n: \exists f \in \operatorname{Fin}\left(n\right) \to M,\; \operatorname{MinimalFor}\left(f, t\right))$$

*Formalization.* `D5/S0/Certificates/Algebra/CappedUnionDavenport.minimalLengths` (`✓ std3`).

*Citation.* Haobo Ma; Wenlin Zhang (2026). *Counterexamples to Wang's Conjectures 3.26 and 5.3 on semigroup algebras*. DOI: [10.5281/zenodo.23884901](https://doi.org/10.5281/zenodo.23884901).

*Commentary.*

For a commutative monoid M and t in M, the relative Davenport constant D_t(M) is the supremum of this set of lengths.

**Theorem 1.4 (D_(A,k)(S_U)=|A|+k).**

$$\forall A \in \operatorname{Finset}\left(U\right),\; \forall k \in \operatorname{Fin}\left(3\right),\; \operatorname{IsGreatest}\left(\operatorname{minimalLengths}\left(\operatorname{pair}\left(A, k\right)\right), \operatorname{card}\left(A\right) + k\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/Algebra/CappedUnionDavenport.result` (`✓ std3`). ∎

*Citation.* Haobo Ma; Wenlin Zhang (2026). *Counterexamples to Wang's Conjectures 3.26 and 5.3 on semigroup algebras*. DOI: [10.5281/zenodo.23884901](https://doi.org/10.5281/zenodo.23884901).

*Commentary.*

For every type U, finite A and k in {0,1,2}, the set of lengths of minimal sequences with sum (A,k) has greatest element |A|+k; in particular D_(empty,0)=0. Lower bound: the singletons ({a},0) for a in A followed by k copies of (empty,1) sum to (A,k), and a proper subfamily either omits a singleton, losing its point, or omits a copy of (empty,1), dropping the capped level below k. Upper bound: in a minimal sequence each single deletion changes the sum. A term whose deletion keeps the capped level must be the only term containing some point of A, and distinct such terms give distinct points, so there are at most |A| of them. A term whose deletion lowers the capped level has level at least 1 and at least L-1 for the total level L, and at most min(2,L)=k terms can satisfy this. This is Lemma 4 of Ma and Zhang, Zenodo 10.5281/zenodo.23884901.

## References

- Truth anchor: `D5/S0/Certificates/Algebra/CappedUnionDavenport.Capped`
- Truth anchor: `D5/S0/Certificates/Algebra/CappedUnionDavenport.MinimalFor`
- Truth anchor: `D5/S0/Certificates/Algebra/CappedUnionDavenport.minimalLengths`
- Truth anchor: `D5/S0/Certificates/Algebra/CappedUnionDavenport.result`
