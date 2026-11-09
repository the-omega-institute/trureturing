# Alexandroff duplicate and its exact clopen locus

## Abstract

The actual Alexandroff duplicate has a dense clopen-basis locus and a closed connected bottom copy.

K is an arbitrary compact Hausdorff connected nontrivial space with carrier in Type u. Duplicate(K) has the actual carrier K times Bool. Lower(x) is (x,false), Upper(x) is (x,true), and Projection(x,b) is x. Upper singletons are open. A bottom point Lower(x) in an open set U has a base-open neighborhood V containing x such that Lower(y) belongs to U for every y in V, and Upper(y) belongs to U for every y in V distinct from x. Thus the basic bottom neighborhoods are exactly (V times Bool) minus the singleton Upper(x); this is not the product topology.

HasClopenBasis(z) means that for every actual ambient open U containing z there is an ambient clopen C with z in C and C contained in U. TopologicalSpaceU bundles a carrier and its topology; TTwoSpace means Hausdorff, Range denotes actual function range, and Negation is logical negation.

**Theorem 1.1 (Compact Hausdorff duplicate with exactly the upper clopen locus).**

$$\forall K \in TopologicalSpaceU,\; \left(CompactSpace\left(K\right) \land \left(TTwoSpace\left(K\right) \land \left(ConnectedSpace\left(K\right) \land Nontrivial\left(K\right)\right)\right)\right) \Rightarrow \left(CompactSpace\left(Duplicate\left(K\right)\right) \land \left(TTwoSpace\left(Duplicate\left(K\right)\right) \land \left(Continuous\left(Projection\left(K\right)\right) \land \left(LeftInverse\left(Projection\left(K\right), Lower\left(K\right)\right) \land \left(IsClosedEmbedding\left(Lower\left(K\right)\right) \land \left(Dense\left(Range\left(Upper\left(K\right)\right)\right) \land \left(\left(\forall z \in Duplicate\left(K\right),\; HasClopenBasis\left(z\right) \Leftrightarrow Mem\left(z, Range\left(Upper\left(K\right)\right)\right)\right) \land Negation\left(ZeroDimensionalSpace\left(Duplicate\left(K\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Topology/Separation/AlexandroffDuplicate.topological_frontier` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The duplicate is compact and Hausdorff. Projection is continuous and is a left inverse of Lower. Lower is a closed embedding of the original K. The range of Upper is dense. A point has a clopen neighborhood basis if and only if it belongs to that upper range. The duplicate is not zero-dimensional.

For compactness, choose one bottom cover member and a base neighborhood at every base point. Finitely many such base neighborhoods cover K. Their duplicate neighborhoods miss at most the finitely many upper points with those chosen base coordinates; adding one cover member for each supplies a genuine finite subcover. This finite remainder is constructed, not assumed. For the clopen locus, the preimage of any clopen neighborhood under Lower is a nonempty clopen subset of the connected K, hence all of K. An open neighborhood omitting a different bottom point therefore has no such clopen refinement. The upper singleton supplies the converse.

This is the topological prerequisite of proposition 34.2 in the matrix-bundle quantum source. Its two-sphere base is retained by specialization. The theorem does not construct the Hopf bundle, prove its endomorphism bundle nontrivial, establish winding or classify the original response D. Those are separate source clauses; no physical preparation or transport condition follows from this topology alone.

## References

- Truth anchor: `D5/S3/Topology/Separation/AlexandroffDuplicate.topological_frontier`
