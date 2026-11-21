# Structure of the capped union monoid

## Abstract

The capped union monoid is periodic, its positive cyclic semigroups are groups exactly off level one, and its algebraic and relative Davenport constants, Green relation and Schutzenberger groups are explicit.

**Theorem 1.1 (Theorem 1).**

$$(\operatorname{Periodic}\left(\operatorname{Capped}\left(U\right)\right)) \land ((\forall a \in \operatorname{Capped}\left(U\right),\; (\operatorname{CyclicIsGroup}\left(a\right)) \Leftrightarrow (\operatorname{level}\left(a\right) \ne 1)) \land ((\operatorname{algebraicD}\left(\operatorname{Capped}\left(U\right), R\right) = 1) \land ((\forall a \in \operatorname{Capped}\left(U\right),\; \forall b \in \operatorname{Capped}\left(U\right),\; (\operatorname{greenCon}\left(a, b\right)) \Leftrightarrow (a = b)) \land ((\forall A \in \operatorname{Finset}\left(U\right),\; \forall k \in \operatorname{Fin}\left(3\right),\; \operatorname{IsGreatest}\left(\operatorname{minimalLengths}\left(\operatorname{pair}\left(A, k\right)\right), \operatorname{card}\left(A\right) + k\right)) \land (\forall a \in \operatorname{Capped}\left(U\right),\; \operatorname{Unique}\left(\operatorname{Gamma}\left(a\right)\right))))))$$

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/Algebra/CappedUnionStructure.result` (`✓ std3`). ∎

*Citation.* Haobo Ma; Wenlin Zhang (2026). *Counterexamples to Wang's Conjectures 3.26 and 5.3 on semigroup algebras*. DOI: [10.5281/zenodo.23884901](https://doi.org/10.5281/zenodo.23884901).

*Commentary.*

For every set U and every nonzero commutative ring R: S_U is periodic in the sense of WangConjecture326Refutation.Periodic, since CappedUnionAlgebraicDavenport.cyclic_le places the positive cyclic subsemigroup of a inside the finite set {a, a+a}. The positive cyclic semigroup of a=(A,k) is a group (WangConjecture326Refutation.CyclicIsGroup) exactly when k is not 1: off level one a+a=a, so the cyclic semigroup is {a} with identity a; at level one an identity e in {a, a+a} would satisfy e+a=a, but a+a and (a+a)+a both have level 2. The remaining clauses are the algebraic Davenport constant algebraicD(S_U,R)=1 (CappedUnionAlgebraicDavenport.result), the Green congruence being equality and the trivial translation groups (CappedUnionGreen.result), and the relative constants D_(A,k)(S_U)=|A|+k (CappedUnionDavenport.result). This is Theorem 1 of Ma and Zhang, Zenodo 10.5281/zenodo.23884901, for arbitrary U; the source's further consequence for U=N, refuting Wang's Conjecture 3.26, is WangConjecture326Refutation.result.

## References

- Truth anchor: `D5/S0/Certificates/Algebra/CappedUnionStructure.result`
- Dependency: [D5/S0/Certificates/Algebra/CappedUnionAlgebraicDavenport](CappedUnionAlgebraicDavenport.md)
- Dependency: [D5/S0/Certificates/Algebra/CappedUnionGreen](CappedUnionGreen.md)
