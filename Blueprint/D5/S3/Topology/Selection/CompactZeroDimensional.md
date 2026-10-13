# Compact zero-dimensional continuous selection

## Abstract

Closed nonempty lower semicontinuous fibers over compact zero-dimensional spaces admit continuous selections, including prescribed fiber points.

The universe levels u and v are independent. B is an arbitrary compact Hausdorff totally disconnected topological space, and K is a complete metric space. Phi maps B to subsets of K. Hit(Phi,U) denotes exactly the set of b for which Phi(b) intersects U nontrivially. Nonempty(Phi(b)) means nonemptiness of that subset, rather than a carrier typeclass. The open-hit condition is the literal lower semicontinuity hypothesis, equivalent to Mathlib's LowerHemicontinuous.

**Theorem 1.1 (Continuous fiber-member selection).**

$$\begin{aligned}\forall B: Type_{u}, \forall K: Type_{v}, \\{}[\operatorname{TopologicalSpace}\left(B\right)] {}[\operatorname{CompactSpace}\left(B\right)] {}[\operatorname{TTwoSpace}\left(B\right)] {}[\operatorname{TotallyDisconnectedSpace}\left(B\right)] \\{}[\operatorname{MetricSpace}\left(K\right)] {}[\operatorname{CompleteSpace}\left(K\right)] \\\forall \phi: B \to \operatorname{Set}\left(K\right), \\{\forall b: B, \operatorname{Nonempty}\left(\phi(b)\right)} \Rightarrow\\{\forall b: B, \operatorname{IsClosed}\left(\phi(b)\right)} \Rightarrow\\{\forall U: \operatorname{Set}\left(K\right), \operatorname{IsOpen}\left(U\right) \Rightarrow \operatorname{IsOpen}\left(\operatorname{Hit}\left(\phi, U\right)\right)} \Rightarrow\\\exists f: B \to K, \operatorname{Continuous}\left(f\right) \land {\forall b: B, f(b) \in \phi(b)}\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Topology/Selection/CompactZeroDimensional.exists_continuous_selection` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every multifunction with nonempty closed fibers and open hitting sets for all open target sets, there exists a continuous function f from B to K with f(b) in Phi(b) at every b. B need not be metrizable, first countable, second countable, separable, or equipped with a countable basis. K need not be compact, separable, convex, or linear.

Choose fiber points to form an open cover by fiber hitting balls. TopologicalSpace.IsOpenCover.exists_finite_nonempty_disjoint_clopen_cover refines the cover into finitely many disjoint clopen cells. The value assigned to each cell is the center belonging to the cover member that contains the cell. This gives a finite locally constant first approximation with fiber error less than one.

At stage n put epsilon(n)=(1/2)^n. Intersect the open equality fiber of the old locally constant map with a fiber hitting ball centered at an actual nearby fiber point. A finite clopen refinement gives the next approximation, with fiber error less than epsilon(n+1) and pointwise increment at most epsilon(n). These inequalities give the same bound in the uniform metric on bounded continuous functions. Mathlib's geometric Cauchy theorem and completeness supply a bounded continuous limit with uniform tail bound 2 epsilon(n). A fiber point within epsilon(n) of the nth approximation is within 3 epsilon(n) of the limit; closedness of each exact fiber puts the limit in that fiber.

Neither B nor K has a Nonempty assumption in the theorem. If B is empty, the cell-index function and all subsequent functions are empty functions, even when K is empty. No arbitrary target inhabitant is chosen. If B has a point, the nonempty fiber at that point already supplies a target point.

**Theorem 1.2 (Selection through a prescribed fiber point).**

$$\begin{aligned}\forall B: Type_{u}, \forall K: Type_{v}, \\{}[\operatorname{TopologicalSpace}\left(B\right)] {}[\operatorname{CompactSpace}\left(B\right)] {}[\operatorname{TTwoSpace}\left(B\right)] {}[\operatorname{TotallyDisconnectedSpace}\left(B\right)] \\{}[\operatorname{MetricSpace}\left(K\right)] {}[\operatorname{CompleteSpace}\left(K\right)] \\\forall \phi: B \to \operatorname{Set}\left(K\right), \\{\forall b: B, \operatorname{Nonempty}\left(\phi(b)\right)} \Rightarrow\\{\forall b: B, \operatorname{IsClosed}\left(\phi(b)\right)} \Rightarrow\\{\forall U: \operatorname{Set}\left(K\right), \operatorname{IsOpen}\left(U\right) \Rightarrow \operatorname{IsOpen}\left(\operatorname{Hit}\left(\phi, U\right)\right)} \Rightarrow\\\forall bzero: B, \forall kzero: K, \\kzero \in \phi(bzero) \Rightarrow\\\exists f: B \to K, \operatorname{Continuous}\left(f\right) \land {\forall b: B, f(b) \in \phi(b)} \land f(bzero) = kzero\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Topology/Selection/CompactZeroDimensional.exists_continuous_selection_through` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every bzero in B and every kzero in Phi(bzero), one may also require f(bzero)=kzero. Replace only the fiber at bzero by the singleton containing kzero. All fibers stay nonempty and closed. For an open U containing kzero, its hitting set is unchanged. For U excluding kzero, its hitting set is the old open hitting set minus the closed singleton containing bzero. Thus the modified multifunction still satisfies the literal open-hit condition. The full selection theorem applied to it gives both membership in the original fibers and the prescribed equality.

This is the compact-domain form of Michael's classical zero-dimensional selection principle. Valov's arXiv:0801.1721v2 uses the classical principle in Lemma 2.2 and cites Michael's Selected selection theorems; the consulted source and its scope are recorded in Library/Topology/valov2008milyutinmaps.md. No theorem number from the uninspected original Michael article or from Semenov and Shchepin's article is asserted here. The result supplies prescribed sections for a future open-map resolution argument under a metrizable-kernel hypothesis. That resolution is not asserted by these selection statements, and neither Peng Question 5.1 nor Question 5.2 is resolved here.

## References

- Truth anchor: `D5/S3/Topology/Selection/CompactZeroDimensional.exists_continuous_selection`
- Truth anchor: `D5/S3/Topology/Selection/CompactZeroDimensional.exists_continuous_selection_through`
