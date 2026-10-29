# Independent-fibre substitution on actual subsets

## Abstract

Independent fibres retain actual total-domination subsets and give the known polynomial substitution.

V and W are actual finite vertex types, with Fintype instances. G is an arbitrary SimpleGraph on V. For the total-domination identity W is nonempty. Each v is replaced by the independent fibre consisting of all (v,i) with i in W. Vertices in two fibres are adjacent exactly when their original vertices are adjacent. An occupied fibre contributes a nonempty actual subset, not one selected representative.

**Definition 1.1 (The actual independent-fibre graph).**

$$\forall (V:\operatorname{Type}\left(\right)), \forall (G:\operatorname{SimpleGraph}\left(V\right)), \forall (W:\operatorname{Type}\left(\right)), \forall (a:V\times W), \forall (b:V\times W), (\operatorname{Adj}\left(\operatorname{blowupGraph}\left(G, W\right), a, b\right)) \Leftrightarrow (\operatorname{Adj}\left(G, \operatorname{fst}\left(a\right), \operatorname{fst}\left(b\right)\right))$$

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/TotalDominationBlowup.blowupGraph` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The result has vertex type V times W and adjacency G.Adj(a.fst,b.fst). There are no internal edges in a fibre. This is SimpleGraph.comap Prod.fst, so symmetry and looplessness are inherited. It is the edgeless-fibre lexicographic blowup, not a clique blowup.

**Definition 1.2 (Actual subset-to-fibre equivalence).**

$$\forall (V:\operatorname{Type}\left(\right)), \forall (W:\operatorname{Type}\left(\right)), [\operatorname{Fintype}\left(V\right)], [\operatorname{Fintype}\left(W\right)], (\forall (S:\operatorname{Finset}\left(V\times W\right)), \forall (v:V), \forall (i:W), (i \in \operatorname{subsetFamilyEquiv}\left(S, v\right)) \Leftrightarrow ((v,i) \in S)) \land (\forall (f:V\to \operatorname{Finset}\left(W\right)), \forall (v:V), \forall (i:W), ((v,i) \in \operatorname{symm}\left(\operatorname{subsetFamilyEquiv}\left(\right), f\right)) \Leftrightarrow (i \in \operatorname{f}\left(v\right)))$$

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/TotalDominationBlowup.subsetFamilyEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For finite V and W this is an equivalence between Finset(V times W) and V -> Finset W. A global subset S maps at v to all i in W with (v,i) in S. The inverse maps f to all (v,i) with i in f(v). Extensional membership proves the inverse laws. The private cardinal theorem says the inverse subset cardinality equals sum_v card(f(v)).

**Definition 1.3 (Occupied fibres).**

$$\forall (V:\operatorname{Type}\left(\right)), \forall (W:\operatorname{Type}\left(\right)), [\operatorname{Fintype}\left(V\right)], [\operatorname{Fintype}\left(W\right)], \forall (f:V\to \operatorname{Finset}\left(W\right)), \forall (v:V), (v \in \operatorname{support}\left(f\right)) \Leftrightarrow (\operatorname{Nonempty}\left(\operatorname{f}\left(v\right)\right))$$

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/TotalDominationBlowup.support` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

support(f) is the finite subset of all v in V for which f(v) is nonempty. For nonempty W, the private total_family theorem proves that the actual inverse subset totally dominates blowupGraph G W if and only if this support totally dominates G. The forward direction tests any vertex in each fibre; the reverse direction uses a selected neighbour in an occupied adjacent fibre. Selected vertices obey exactly the same condition.

**Theorem 1.4 (The known actual-subset substitution identity).**

$$\forall (V:\operatorname{Type}\left(\right)), \forall (W:\operatorname{Type}\left(\right)), [\operatorname{Fintype}\left(V\right)], [\operatorname{Fintype}\left(W\right)], [\operatorname{Nonempty}\left(W\right)], \forall (G:\operatorname{SimpleGraph}\left(V\right)), \operatorname{complexPolynomial}\left(\operatorname{blowupGraph}\left(G, W\right)\right) = \operatorname{comp}\left(\operatorname{complexPolynomial}\left(G\right), (1 + (X:\mathbb{C}[X]))^{\operatorname{card}\left(W\right)} - 1\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Domination/TotalDominationBlowup.blowup_polynomial` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite V,W, nonempty W, and SimpleGraph G on V, T_blowup(x)=T_G((1+x)^card(W)-1) in C[X]. Both polynomials are the literal subset sums defined in TotalDominationSeeds.complexPolynomial. The fibre equivalence, cardinal sum and occupied-support equivalence reduce the left side to a sum over families. For a fixed support A, product-of-sums and the sum of all nonempty fibre subsets give ((1+x)^card(W)-1)^card(A). Summing the supports gives polynomial composition. The displayed independent-fibre formula is proved here from actual subsets. It is retained as a mathematical ingredient, with no assertion of original discovery. No attribution to an unread H-join theorem is used.

**Theorem 1.5 (A common labelled pullback for every actual root).**

$$\forall (n:\mathbb{N}), \forall (G:\operatorname{SimpleGraph}\left(\operatorname{Fin}\left(n\right)\right)), (2 \le n) \Rightarrow ((\forall (v:\operatorname{Fin}\left(n\right)), \exists (u:\operatorname{Fin}\left(n\right)), \operatorname{Adj}\left(G, v, u\right)) \Rightarrow (\forall (eta:\mathbb{C}), (\operatorname{IsRoot}\left(\operatorname{complexPolynomial}\left(G\right), eta\right)) \Rightarrow (\forall (k:\mathbb{N}), (0 < k) \Rightarrow (\exists (m:\mathbb{N}), \exists (H:\operatorname{SimpleGraph}\left(\operatorname{Fin}\left(m\right)\right)), (2 \le m) \land ((\operatorname{complexPolynomial}\left(H\right) \ne 0) \land ((\forall (v:\operatorname{Fin}\left(m\right)), \exists (u:\operatorname{Fin}\left(m\right)), \operatorname{Adj}\left(H, v, u\right)) \land (\forall (w:\mathbb{C}), ((1 + w)^{k} = 1 + eta) \Rightarrow (\operatorname{IsRoot}\left(\operatorname{complexPolynomial}\left(H\right), w\right)))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Domination/TotalDominationBlowup.labelled_root_blowup` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every n>=2, actual graph G : SimpleGraph (Fin n) without isolates, complex root eta of complexPolynomial G, and positive natural k, there exist m>=2 and an actual isolate-free H : SimpleGraph (Fin m) with nonzero complexPolynomial H. Every complex w satisfying (1+w)^k=1+eta is a root of that same H. The graph is the independent-fibre blowup of G by Fin k, reindexed once to Fin m. Its leading coefficient is one; thus no nonzero assumption on the seed is needed beyond the actual no-isolate graph. This generalizes the live seed pullback to the negative family without a conditional density premise.

The independent-fibre identity supplies the common pullback used in the complex approximation argument. It differs from clique substitution because a selected vertex has no neighbour inside its own fibre.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/TotalDominationBlowup.blowupGraph`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/TotalDominationBlowup.blowup_polynomial`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/TotalDominationBlowup.labelled_root_blowup`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/TotalDominationBlowup.subsetFamilyEquiv`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/TotalDominationBlowup.support`
- Dependency: [D5/S3/Combinatorics/Graph/Domination/TotalDominationSeeds](TotalDominationSeeds.md)
