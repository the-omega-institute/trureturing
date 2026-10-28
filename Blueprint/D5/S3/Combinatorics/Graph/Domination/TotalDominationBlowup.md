# Independent-fibre substitution on actual subsets

## Abstract

Independent fibres retain actual total-domination subsets and give the known polynomial substitution.

V and W are actual finite vertex types, with Fintype instances. G is an arbitrary SimpleGraph on V. For the total-domination identity W is nonempty. Each v is replaced by the independent fibre consisting of all (v,i) with i in W. Vertices in two fibres are adjacent exactly when their original vertices are adjacent. An occupied fibre contributes a nonempty actual subset, not one selected representative.

**Definition 1.1 (The actual independent-fibre graph).**

$$\operatorname{blowupGraph}\left(G, W\right) = \operatorname{comap}\left(G, \operatorname{fst}\left(\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/TotalDominationBlowup.blowupGraph` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The result has vertex type V times W and adjacency G.Adj(a.fst,b.fst). There are no internal edges in a fibre. This is SimpleGraph.comap Prod.fst, so symmetry and looplessness are inherited. It is the edgeless-fibre lexicographic blowup, not a clique blowup.

**Definition 1.2 (Actual subset-to-fibre equivalence).**

$$\operatorname{subsetFamilyEquiv}\left(\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/TotalDominationBlowup.subsetFamilyEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For finite V and W this is an equivalence between Finset(V times W) and V -> Finset W. A global subset S maps at v to all i in W with (v,i) in S. The inverse maps f to all (v,i) with i in f(v). Extensional membership proves the inverse laws. The private cardinal theorem says the inverse subset cardinality equals sum_v card(f(v)).

**Definition 1.3 (Occupied fibres).**

$$\operatorname{support}\left(f\right) = \operatorname{occupiedFibres}\left(f\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/TotalDominationBlowup.support` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

occupiedFibres(f) is the finite subset of all v in V for which f(v) is nonempty. For nonempty W, the private total_family theorem proves that the actual inverse subset totally dominates blowupGraph G W if and only if this support totally dominates G. The forward direction tests any vertex in each fibre; the reverse direction uses a selected neighbour in an occupied adjacent fibre. Selected vertices obey exactly the same condition.

**Theorem 1.4 (The known actual-subset substitution identity).**

$$\operatorname{complexPolynomial}\left(\operatorname{blowupGraph}\left(G, W\right)\right) = \operatorname{comp}\left(\operatorname{complexPolynomial}\left(G\right), (1+X)^{\operatorname{card}\left(W\right)}-1\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Domination/TotalDominationBlowup.blowup_polynomial` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite V,W, nonempty W, and SimpleGraph G on V, T_blowup(x)=T_G((1+x)^card(W)-1) in C[X]. Both polynomials are the literal subset sums defined in TotalDominationSeeds.complexPolynomial. The fibre equivalence, cardinal sum and occupied-support equivalence reduce the left side to a sum over families. For a fixed support A, product-of-sums and the sum of all nonempty fibre subsets give ((1+x)^card(W)-1)^card(A). Summing the supports gives polynomial composition. This is an attributed H-join ingredient from Subramanian and Selvakumar, Filomat 2025, with no new identity or external-resolution credit.

**Theorem 1.5 (Power-map pullback of the shrinking seeds).**

$$\operatorname{seedBlowupRoots}\left(epsilon, k\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Domination/TotalDominationBlowup.seed_blowup_roots` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every positive real epsilon and every positive natural k there exist n : N, G : SimpleGraph(Fin n), and r : R with n>=2, 0<1+r<epsilon, complexPolynomial G nonzero, and every vertex of G having a neighbour. For every complex w, (1+w)^k=1+r implies that w is a root of complexPolynomial(blowupGraph G (Fin k)). The blowup polynomial is also nonzero and every blowup vertex has a neighbour; its leading coefficient at its vertex count is one. The same fixed G and r work for all these branches. The proof consumes the new right-hand seed theorem and the known actual-fibre substitution. This is an auxiliary bridge, not WholePlaneDensity: no approximation to an arbitrary target z or unbounded negative seed family is asserted.

**Theorem 1.6 (A single labelled witness for every branch).**

$$\operatorname{labelledSeedBlowupRoots}\left(epsilon, k\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Domination/TotalDominationBlowup.labelled_seed_blowup_roots` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every positive real epsilon and positive natural k there exist m : N, H : SimpleGraph (Fin m), and r : R such that m>=2, 0<1+r<epsilon, complexPolynomial H is nonzero, every vertex of H has a neighbour, and for every complex w, (1+w)^k=1+r implies complexPolynomial H has root w. The product vertex type of the independent-fibre graph is reindexed to Fin m through Fintype.equivFin. Actual subsets, their cardinalities, adjacency, every power branch and the same polynomial are preserved. No graph is separately chosen for each branch. This theorem does not assert proximity to an arbitrary complex z.

The full issue 23313 target remains WholePlaneDensity in TotalDominationSeeds. The independent-fibre identity and these power-map branches do not by themselves establish the complete complex density or authorize resolution credit.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/TotalDominationBlowup.blowupGraph`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/TotalDominationBlowup.blowup_polynomial`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/TotalDominationBlowup.labelled_seed_blowup_roots`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/TotalDominationBlowup.seed_blowup_roots`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/TotalDominationBlowup.subsetFamilyEquiv`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/TotalDominationBlowup.support`
- Dependency: [D5/S3/Combinatorics/Graph/Domination/TotalDominationSeeds](TotalDominationSeeds.md)
