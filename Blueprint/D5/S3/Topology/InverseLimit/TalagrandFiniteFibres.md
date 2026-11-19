# Finite fibres on the Talagrand compactum

## Abstract

Finite-to-one maps on the Talagrand compactum have finitely many multiple fibres.

**Definition 1.1 (The Grothendieck property of the real continuous dual).**

Lean statement: `D5/S3/Topology/InverseLimit/TalagrandFiniteFibres.Grothendieck`

*Formalization.* `D5/S3/Topology/InverseLimit/TalagrandFiniteFibres.Grothendieck` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

On the dual of the real continuous functions on K, convergence of a sequence on every continuous function to the evaluations of a fixed functional implies convergence to that functional on every continuous linear bidual test.

**Theorem 1.2 (Simultaneous clopen separation along a subsequence).**

$$\forall K \in ZeroDimensionalCompactHausdorffSpaces,\; \operatorname{Grothendieck}\left(K\right) \Rightarrow \left(\forall I \in NonemptyCountableTypes,\; \forall x \in \operatorname{Arrays}\left(I, K\right),\; \left(\operatorname{DisjointColumns}\left(x\right) \land \operatorname{EventuallyDistinctRows}\left(x\right)\right) \Rightarrow \operatorname{EventuallyClopenSeparatedSubsequence}\left(x\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Topology/InverseLimit/TalagrandFiniteFibres.exists_subseq_pairwise_clopen_separation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let K be compact Hausdorff and zero-dimensional with the Grothendieck property, and let I be nonempty and countable. Columns of x are indexed by the natural numbers and have disjoint sets of values. Distinct rows differ eventually. There is a single strictly increasing subsequence such that for every ordered pair of distinct rows, one clopen eventually contains the first row and excludes the second.

Finite clopen tests separate the Dirac differences of disjoint pairs. Weak-star compactness gives a single bidual test taking value one on every difference. If each clopen separated the ordered pairs only finitely often, compactness of the space of pairs would force the differences to converge to zero on every continuous function, contradicting the Grothendieck property. Successive extraction and diagonalization handle all ordered pairs.

**Theorem 1.3 (A uniform bound on finite fibres).**

$$\forall K \in ZeroDimensionalCompactHausdorffSpaces,\; \operatorname{Grothendieck}\left(K\right) \Rightarrow \left(\forall Y \in HausdorffSpaces,\; \forall q \in \operatorname{ContinuousMaps}\left(K, Y\right),\; \operatorname{AllFibresFinite}\left(q\right) \Rightarrow \operatorname{UniformFibreBound}\left(q\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Topology/InverseLimit/TalagrandFiniteFibres.exists_uniform_fibre_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let K be compact Hausdorff and zero-dimensional with the Grothendieck property, and let Y be Hausdorff. If each fibre of q is finite, their cardinalities share a natural-number bound. Otherwise enumerate larger and larger fibres over distinct points and separate their countably many rows. A cluster tuple has pairwise distinct coordinates with the same image under q.

**Theorem 1.4 (Finitely many nonsingleton fibres on the CH Talagrand compactum).**

$$\forall hCH \in ContinuumEqualsAlephOne,\; \forall Y \in HausdorffSpaces,\; \forall q \in \operatorname{ContinuousMaps}\left(\operatorname{ActualFinalLimit}\left(hCH\right), Y\right),\; \operatorname{AllFibresFinite}\left(q\right) \Rightarrow \left(\operatorname{UniformFibreBound}\left(q\right) \land \operatorname{FinitelyManyNonsingletonFibres}\left(q\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Topology/InverseLimit/TalagrandFiniteFibres.actual_finite_to_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Tomasz Kania and Jerzy Kakol (2026). *Talagrand compacta, 2DCP, and pointwise quotients*. URL: <https://arxiv.org/abs/2607.06808v2>.

*Commentary.*

The domain is SignedOrdinalRealization.finalPrefix(hCH).LimitSpace and Y is Hausdorff. Every continuous map with finite fibres admits a uniform cardinal bound, and only finitely many fibres contain at least two points.

If infinitely many fibres were nonsingleton, choose the largest size occurring infinitely often and place the points of those fibres in disjoint clopens. A convergent sequence of distinct image points would lift to a sequence whose cluster set is finite. A closed neighborhood isolating one cluster point would give a convergent subsequence of distinct points in K. Thus the separated fibres accumulate away from the finitely many larger fibres. An infinite closed set of such image points lifts homeomorphically into each clopen, contradicting the finite-image endpoint for disjoint copies.

## References

- Truth anchor: `D5/S3/Topology/InverseLimit/TalagrandFiniteFibres.Grothendieck`
- Truth anchor: `D5/S3/Topology/InverseLimit/TalagrandFiniteFibres.actual_finite_to_one`
- Truth anchor: `D5/S3/Topology/InverseLimit/TalagrandFiniteFibres.exists_subseq_pairwise_clopen_separation`
- Truth anchor: `D5/S3/Topology/InverseLimit/TalagrandFiniteFibres.exists_uniform_fibre_bound`
- Dependency: [D5/S3/Topology/InverseLimit/ContinuousFiniteImageTail](ContinuousFiniteImageTail.md)
- Dependency: [D5/S3/Topology/InverseLimit/SignedBallHistoryEndpoints](SignedBallHistoryEndpoints.md)
