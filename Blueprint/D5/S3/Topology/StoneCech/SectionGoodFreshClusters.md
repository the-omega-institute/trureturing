# Fresh projected accumulation on actual sections

## Abstract

Actual sections and disjoint supports encode index ultrafilters in distinct projected accumulation values.

A and B are arbitrary types in Type, with their canonical ultrafilter Stone topologies; q : A -> B is arbitrary. SectionGood(q) is exactly {u : Ultrafilter A | (u : Filter A) <= cofinite and there exists S in u with InjOn q S}. Thus u is free and contains an actual set on which q is injective, a partial section of q. In the formula, map(q) denotes Ultrafilter.map q, apply denotes function evaluation, Card is Cardinal.mk, c is the continuum, Embedding(Nat,Ultrafilter A) is Nat embedded injectively in Ultrafilter A, and principal(range(e)) is the principal filter of that range. AccPt is Mathlib's punctured accumulation predicate: each neighborhood meets the range away from the proposed accumulation point.

**Theorem 1.1 (A section-good accumulation point outside prescribed projected values).**

$$\forall A: Type, \forall B: Type, \forall q: A \to B, \forall e: \operatorname{Embedding}\left(Nat, \operatorname{Ultrafilter}\left(A\right)\right), \forall F: \operatorname{Set}\left(\operatorname{Ultrafilter}\left(B\right)\right), {{\operatorname{range}\left(e\right) \subseteq \operatorname{SectionGood}\left(q\right)} \land {\operatorname{Injective}\left(\operatorname{compose}\left(\operatorname{map}\left(q\right), e\right)\right)} \land {\operatorname{Card}\left(F\right) \le c}} \Rightarrow {\exists u: \operatorname{Ultrafilter}\left(A\right), {u \in \operatorname{SectionGood}\left(q\right)} \land {\operatorname{AccPt}\left(u, \operatorname{principal}\left(\operatorname{range}\left(e\right)\right)\right)} \land {\neg{\operatorname{apply}\left(\operatorname{map}\left(q\right), u\right) \in F}}}$$

*Proof.* Machine-checked in Lean as `D5/S3/Topology/StoneCech/SectionGoodFreshClusters.exists_sectionGood_fresh_accPt` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Zdeněk Frolík (1960). *The topological product of countably compact spaces*. DOI: [10.21136/cmj.1960.100417](https://doi.org/10.21136/cmj.1960.100417). URL: <https://dml.cz/handle/10338.dmlcz/100417>.

*Acknowledgement.* David V. Feldman and Alexander Wilce (2026). *A Note on Compactness and Clique Size*. URL: <https://arxiv.org/abs/2608.13320>.

*Commentary.*

The hypotheses are an embedding e with section-good range, injectivity of n |-> Ultrafilter.map q (e n), and an arbitrary forbidden set F of ultrafilters on B with cardinal at most c. The conclusion is one u in SectionGood(q), an AccPt of the original range(e), whose projected value is outside F. Neither A nor B is assumed countable; no fibre of q is assumed finite and no selector or section-dense seed is assumed.

The support construction takes P to be the actual image subspace range(n |-> map q (e n)). Its injective parametrization makes P infinite. The topological disjoint-open-set lemma is applied to P, producing pairwise disjoint relative open sets and chosen points p(n) in them. Lift these opens to ambient opens O(n) of Ultrafilter B, then choose basic membership clopens C(n)-hat inside O(n), with C(n) in p(n). Relative disjointness implies C(m) is absent from p(n) for m unequal to n; it does not by itself make the ambient C(n) disjoint. Define D(n) = C(n) minus the union of C(m) for m < n. Only finitely many complements are intersected, so D(n) still belongs to p(n), and these literal subsets of B are pairwise disjoint. An injective index map k realizes p(n) as map q (e(k(n))).

Write v(n)=e(k(n)) and choose its given section witness T(n) in v(n). Splice them by S = union over n of T(n) intersect q-inverse(D(n)). Each piece belongs to v(n), so S belongs to every v(n). If two points of S have the same q-value, disjoint supports force their pieces to have the same index; injectivity on that T(n) then makes the points equal. This constructs the actual common injectivity set S.

For every index ultrafilter r on Nat, including principal r, define L(r)=joinM(map v r). The membership law of this actual ultrafilter monad is H in L(r) iff {n | H in v(n)} in r. Every v(n) is free and contains S, so L(r) is free and contains the same injectivity set. For every index subset J, disjointness gives union(i in J) D(i) in map q (v(n)) iff n in J. Consequently union(i in J) D(i) in map q (L(r)) iff J in r. This readout for all J recovers r from the projected limit, so r |-> map q (L(r)) is injective. Distinct ultrafilters on A alone would not justify this projected injectivity.

Restrict now to free index ultrafilters. The join is their topological ultrafilter limit of v. Since v is injective, the pushforward of a free index ultrafilter contains cofinite sets of Ultrafilter A; in particular its neighborhood witnesses can omit L(r). This gives the punctured AccPt of range(v), and monotonicity transfers it to range(e). FreeUltrafilterCardinality.continuum_power_le_mk_freeUltrafilter_nat supplies at least 2^c free index ultrafilters. If every projected limit lay in F, the readout would inject this supply into F, giving 2^c <= c, contrary to Cantor. Thus one free r gives the required fresh projected accumulation value.

The cited Frolik note attributes classical abundance and cardinal avoidance precisely: Lemma 2.8 assumes a separable metrizable P and an infinite subset of beta P with no accumulation point in P; Lemma 2.9 constructs a small countably compact extension avoiding a remainder set of cardinal below 2^c. Its Pospisil and Katetov credits do not attribute this arbitrary-q section-splicing and projected readout theorem to those authors. The exact statement and proof composition here are repository-derived. The Feldman-Wilce note identifies the finite-block motivation; this source exposition makes no original-question resolution, literature exclusion or priority claim.

## References

- Truth anchor: `D5/S3/Topology/StoneCech/SectionGoodFreshClusters.exists_sectionGood_fresh_accPt`
- Dependency: [D5/S3/Topology/StoneCech/FreeUltrafilterCardinality](FreeUltrafilterCardinality.md)
