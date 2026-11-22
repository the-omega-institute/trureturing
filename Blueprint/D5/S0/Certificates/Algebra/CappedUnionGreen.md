# Principal ideals and Green classes of the capped union monoid

## Abstract

In the capped union monoid every principal ideal is a coordinate up-set, so Green H is equality and every Schutzenberger group is trivial.

**Theorem 1.1 (Lemma 3).**

$$\forall a \in \operatorname{Capped}\left(U\right),\; (\operatorname{principalIdeal}\left(a\right) = (x: (\operatorname{subset}\left(\operatorname{support}\left(a\right), \operatorname{support}\left(x\right)\right)) \land (\operatorname{level}\left(a\right) \le \operatorname{level}\left(x\right)))) \land ((\forall b \in \operatorname{Capped}\left(U\right),\; (\operatorname{Green}\left(a, b\right)) \Leftrightarrow (a = b)) \land ((\forall b \in \operatorname{Capped}\left(U\right),\; (\operatorname{greenCon}\left(a, b\right)) \Leftrightarrow (a = b)) \land (\operatorname{Unique}\left(\operatorname{Gamma}\left(a\right)\right))))$$

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/Algebra/CappedUnionGreen.result` (`✓ std3`). ∎

*Citation.* Haobo Ma; Wenlin Zhang (2026). *Counterexamples to Wang's Conjectures 3.26 and 5.3 on semigroup algebras*. DOI: [10.5281/zenodo.23884901](https://doi.org/10.5281/zenodo.23884901).

*Commentary.*

For every a=(A,k) in S_U: the principal ideal {a} union (a+S_U) of WangConjecture326Refutation.principalIdeal is {(B,j) : A subset of B, k<=j}; Green H in the sense of WangConjecture53Refutation.Green, and the Green congruence WangConjecture326Refutation.greenCon, relate a only to itself; and the translation group Gamma(H_a) of WangConjecture53Refutation, the maps of H_a realized by adding an element of S_U, has exactly one element. Proof: addition only enlarges the support and raises the capped level, and if A is contained in B and k<=j then (A,k)+(B,j-k)=(B,j). Equal ideals therefore force mutual inclusion of supports and mutual inequality of levels, so every H-class is the singleton {a}; the only self-map of a singleton is realized by adding (empty,0). This is Lemma 3 of Ma and Zhang, Zenodo 10.5281/zenodo.23884901, for every set U including the empty one, every k and the identity (empty,0).

## References

- Truth anchor: `D5/S0/Certificates/Algebra/CappedUnionGreen.result`
- Dependency: [D5/S0/Certificates/Algebra/CappedUnionDavenport](CappedUnionDavenport.md)
- Dependency: [D5/S0/Certificates/Algebra/WangConjecture326Refutation](WangConjecture326Refutation.md)
- Dependency: [D5/S0/Certificates/Algebra/WangConjecture53Refutation](WangConjecture53Refutation.md)
