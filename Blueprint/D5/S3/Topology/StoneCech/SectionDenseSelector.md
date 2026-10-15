# Section-dense ultrafilter selectors

## Abstract

A countable source permits simultaneous fresh section witnesses and countably compact injective closing-off.

Here q : A -> B is arbitrary and only the source A is countable. The codomain B has no countability assumption. SectionGood(q) means free ultrafilters on A containing an actual injectivity set of q. In the formula Card is Cardinal.mk, c is the continuum, and map(q) is Ultrafilter.map q. Infinite(S) means Set.Infinite S. Membership S in u is ultrafilter membership; IsCountablyCompact Y is the native ambient predicate on the subset Y of Ultrafilter A.

**Theorem 1.1 (Constructing the selector and its section density).**

$$\forall A: Type, \forall B: Type, \forall q: A \to B, {\operatorname{Countable}\left(A\right)} \Rightarrow {\exists Y: \operatorname{Set}\left(\operatorname{Ultrafilter}\left(A\right)\right), {Y \subseteq \operatorname{SectionGood}\left(q\right)} \land {\operatorname{Card}\left(Y\right) \le c} \land {\operatorname{InjOn}\left(\operatorname{map}\left(q\right), Y\right)} \land {\operatorname{IsCountablyCompact}\left(Y\right)} \land {\forall S: \operatorname{Set}\left(A\right), {{\operatorname{Infinite}\left(S\right)} \land {\operatorname{InjOn}\left(q, S\right)}} \Rightarrow {\exists u: \operatorname{Ultrafilter}\left(A\right), {u \in Y} \land {S \in u}}}}$$

*Proof.* Machine-checked in Lean as `D5/S3/Topology/StoneCech/SectionDenseSelector.exists_countablyCompact_sectionDense_selector` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Zdeněk Frolík (1960). *The topological product of countably compact spaces*. DOI: [10.21136/cmj.1960.100417](https://doi.org/10.21136/cmj.1960.100417). URL: <https://dml.cz/handle/10338.dmlcz/100417>.

*Acknowledgement.* John Ginsburg and Victor Saks (1975). *Some applications of ultrafilters in topology*. DOI: [10.2140/pjm.1975.57.403](https://doi.org/10.2140/pjm.1975.57.403). URL: <https://doi.org/10.2140/pjm.1975.57.403>.

*Acknowledgement.* David V. Feldman and Alexander Wilce (2026). *A Note on Compactness and Clique Size*. URL: <https://arxiv.org/abs/2608.13320>.

*Commentary.*

The conclusion constructs a set Y of section-good ultrafilters, of cardinal at most c, on which Ultrafilter.map q is injective, and which is countably compact. For every infinite S contained in A on which q is injective, some u in Y contains S. There is no assumed section-dense seed or pre-existing selector, no finite-fibre assumption, and no assumed supply of fresh projected values.

Index the seed tasks by I = {S : Set A // S.Infinite and InjOn q S}. Countability of A bounds Card(I) by Card(Set A)=2^Card(A) <= 2^aleph0=c. This is a bound on subsets of the source, not on subsets of B. A task asks for a free ultrafilter u containing its actual section S, with projected value outside a supplied forbidden set F of cardinal at most c.

For each task choose an actual embedding e : Nat -> S -> A. Injectivity of q on S makes q composed with e injective. Push each free ultrafilter r on Nat forward by e. The resulting u=map e r is free, contains S and belongs to SectionGood(q). The map identity map q (map e r)=map(q composed with e) r and injectivity of filter pushforward along an embedding prove that these projected values are pairwise distinct. The free-ultrafilter cardinal supplier and Cantor's theorem therefore give a witness outside every such F. This proves the task supply rather than assuming it.

Apply InjectiveSelectorClosure.exists_fresh_choice to Q=Ultrafilter.map q, these section tasks, and the empty old set. Its well-founded choice forbids all earlier projected values and chooses one witness per task with globally distinct projected values. The range is a seed of cardinal at most c, contained in SectionGood(q), Q-injective and already section-dense. Empty or finite source cases require no invented infinite section: the corresponding task family may be empty.

The actual theorem SectionGoodFreshClusters.exists_sectionGood_fresh_accPt supplies FreshClusterSupply(SectionGood(q),Q). Feed this and the constructed seed to InjectiveSelectorClosure.exists_countablyCompact_injOn_extension. That existing omega1 closing-off adds fresh ambient punctured accumulation points while preserving section-goodness, Q-injectivity and the continuum bound. Every countable collection appears in a bounded stage and is processed later. The extension contains the seed, so its section-density witnesses survive. The outcome is native countable compactness, with no sequential compactness assertion.

Frolik's Lemma 2.8 has the essential no-accumulation-in-P premise for an infinite subset of beta P, with P separable metrizable; Lemma 2.9 provides cardinal avoidance and omega1 closing-off. Ginsburg-Saks Theorem 2.12 closes a completely regular X inside beta X under sequence limits for one fixed free ultrafilter D. The canonical notes preserve those exact scopes. They attest classical methods, not this exact arbitrary-q selector with a constructed section-dense seed and distinct projected values. The finite-block candidate in Feldman-Wilce supplies the application target, as recorded in its canonical note. The present statement is repository-derived; this exposition makes no novelty, diversity or original-question completion claim.

## References

- Truth anchor: `D5/S3/Topology/StoneCech/SectionDenseSelector.exists_countablyCompact_sectionDense_selector`
- Dependency: [D5/S3/Topology/CountablyCompact/InjectiveSelectorClosure](../CountablyCompact/InjectiveSelectorClosure.md)
- Dependency: [D5/S3/Topology/StoneCech/SectionGoodFreshClusters](SectionGoodFreshClusters.md)
