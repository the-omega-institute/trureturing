# Synchronized ambient clopen supports

## Abstract

Continuous infinite-image maps between disjoint closed sides have synchronized source-image pairs in disjoint ambient clopen supports.

X is an arbitrary topological space with carrier in Type u, compact, Hausdorff and zero-dimensional. F is a closed subset, and f maps its actual subtype continuously into X. The actual range of f is infinite and disjoint from F. No injectivity of f, relative partition, point sequence or ambient support family is assumed. In the formula TopologicalSpaceU includes the carrier and its topology, Subtype(F) is the subtype of points belonging to F, Function denotes a function type, Range is actual set range, Complement is ambient complement, and Subset and Mem are literal set relations. At evaluates a sequence, Value is subtype inclusion, Apply evaluates f, and Ne is inequality.

**Theorem 1.1 (Disjoint ambient supports retaining both corresponding points).**

$$\forall X \in TopologicalSpaceU,\; \left(CompactSpace\left(X\right) \land \left(T2Space\left(X\right) \land ZeroDimensionalSpace\left(X\right)\right)\right) \Rightarrow \left(\forall F \in Set\left(X\right),\; IsClosed\left(F\right) \Rightarrow \left(\forall f \in Function\left(Subtype\left(F\right), X\right),\; \left(Continuous\left(f\right) \land \left(Infinite\left(Range\left(f\right)\right) \land Disjoint\left(F, Range\left(f\right)\right)\right)\right) \Rightarrow \left(\exists P \in Set\left(X\right),\; IsClopen\left(P\right) \land \left(Subset\left(F, P\right) \land \left(Subset\left(Range\left(f\right), Complement\left(P\right)\right) \land \left(\exists a \in Function\left(Nat, Subtype\left(F\right)\right),\; \exists W \in Function\left(Nat, Set\left(X\right)\right),\; \left(\forall n \in Nat,\; IsClopen\left(At\left(W, n\right)\right)\right) \land \left(\left(\forall m \in Nat,\; \forall n \in Nat,\; Ne\left(m, n\right) \Rightarrow Disjoint\left(At\left(W, m\right), At\left(W, n\right)\right)\right) \land \left(\forall n \in Nat,\; Mem\left(Value\left(At\left(a, n\right)\right), At\left(W, n\right)\right) \land Mem\left(Apply\left(f, At\left(a, n\right)\right), At\left(W, n\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Topology/Separation/SynchronizedClopenSupports.exists_synchronized_clopen_supports` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Tomasz Kania and Jerzy Kakol (2026). *Talagrand compacta, 2DCP, and pointwise quotients*. URL: <https://arxiv.org/abs/2607.06808v2>.

*Commentary.*

There is one ambient clopen P containing all of F, whose complement contains the entire range of f. There are a sequence a from Nat into F and a sequence W of ambient subsets of X. Every W(n) is clopen. For distinct m and n the sets W(m) and W(n) are literally disjoint in X. Both Value(a(n)) and f(a(n)) belong to W(n). Thus each support is nonempty. Equality of two selected source points or two image points would put one point in two disjoint supports, so both point sequences are injective even though the given map need not be injective.

The closed domain is compact, so its continuous image is compact and therefore closed in the Hausdorff ambient space. Mathlib's exists_clopen_of_closed_subset_open separates F from this image. Apply exists_seq_infinite_isOpen_pairwise_disjoint to the actual image subspace. Choose one y(n) in each relative open U(n), then choose a(n) from actual range membership with f(a(n)) equal to y(n). Lift U(n) to an ambient open O(n). Continuity makes its preimage open in F; lift that preimage to an ambient open S(n).

The clopen basis supplies C(n) around a(n) inside P intersect S(n), and D(n) around y(n) inside the complement of P intersect O(n). A selected source point in C(m), or its image in D(m), would put y(n) in U(m). Disjointness of the relative U sets excludes this for m different from n. The opposite-side memberships are excluded by P. Hence both selected points of column n miss every E(m) with m different from n, where E(m) is C(m) union D(m). This step excludes the marked points; it does not assert disjointness of arbitrary ambient extensions.

Define W(n) as E(n) minus the union of E(m) over m less than n. This is a clopen difference of a clopen and a finite clopen union. Both marked points survive because they miss all earlier E(m). If n is less than m, W(n) is contained in E(n), while W(m) excludes E(n). This proves literal ambient disjointness without an infinite-union closedness claim or a recursive support construction.

For a homeomorphism between disjoint infinite closed subspaces, composing with ambient inclusion supplies exactly this map f. The resulting P and W are the initial synchronized geometry for the final-capture argument in the Talagrand CH route. The existing CountableClopenReflection.exists_common_stage can reflect P together with the countably many W(n) to one proper stage of a suitable profinite inverse system. The selected points remain actual final source-image pairs inside these supports. This local separation result constructs no transfinite system, proves no anti-homeomorphism conclusion or signed analytic endpoint, and does not resolve arXiv:2607.06808v2 Problem 8.2. No literature novelty is asserted.

## References

- Truth anchor: `D5/S3/Topology/Separation/SynchronizedClopenSupports.exists_synchronized_clopen_supports`
