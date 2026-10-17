# Reconstruction from legal nested fibers

## Abstract

Nonempty compact fibers indexed by legal Boolean prefixes reconstruct a continuous surjection when their real diameters vanish along each legal branch.

LegalDigits is the existing space of functions from the natural numbers to Bool with no adjacent true entries, with its product subspace topology. Prefix(n) consists exactly of functions w from Fin(n) to Bool for which some p in LegalDigits satisfies p(i)=w(i) at every i<n. The function legalPrefix(p,n) restricts p to indices zero through n minus one. The symbol zero denotes the all-false legal stream. There is one prefix at level zero. A child t at level n+1 agrees with its parent s through castSucc, the inclusion of Fin(n) into Fin(n+1). Thus the coverage equivalence in the theorem is exactly equality with the union of all legal child fibers.

**Theorem 1.1 (Unique reconstruction and existence of names).**

$$\begin{aligned}\forall X: \operatorname{Type}\left(u\right), [\operatorname{MetricSpace}\left(X\right)] [\operatorname{CompactSpace}\left(X\right)],\\\forall K: (n: \operatorname{Nat}\left(\right)) \to \operatorname{Prefix}\left(n\right) \to \operatorname{Set}\left(X\right),\\\left(\left(\forall n \in \operatorname{Nat}\left(\right),\; \forall s \in \operatorname{Prefix}\left(n\right),\; \operatorname{Nonempty}\left(\operatorname{K}\left(n, s\right)\right)\right) \land \left(\left(\forall n \in \operatorname{Nat}\left(\right),\; \forall s \in \operatorname{Prefix}\left(n\right),\; \operatorname{IsCompact}\left(\operatorname{K}\left(n, s\right)\right)\right) \land \left(\operatorname{K}\left(0, \operatorname{legalPrefix}\left(\operatorname{zero}\left(\right), 0\right)\right) = \operatorname{univ}\left(X\right) \land \left(\left(\forall n \in \operatorname{Nat}\left(\right),\; \forall s \in \operatorname{Prefix}\left(n\right),\; \forall x \in X,\; x \in \operatorname{K}\left(n, s\right) \Leftrightarrow \left(\exists t \in \operatorname{Prefix}\left(n+1\right),\; \left(\forall i \in \operatorname{Fin}\left(n\right),\; \operatorname{t}\left(\operatorname{castSucc}\left(i\right)\right) = \operatorname{s}\left(i\right)\right) \land x \in \operatorname{K}\left(n+1, t\right)\right)\right) \land \left(\forall p \in \operatorname{LegalDigits}\left(\right),\; \operatorname{Tendsto}\left({n \mapsto \operatorname{diam}\left(\operatorname{K}\left(n, \operatorname{legalPrefix}\left(p, n\right)\right)\right)}, \operatorname{atTop}\left(\right), \operatorname{nhds}\left(0\right)\right)\right)\right)\right)\right)\right) \Rightarrow \left(\exists f \in \operatorname{LegalDigits}\left(\right) \to X,\; \operatorname{Continuous}\left(f\right) \land \left(\operatorname{Surjective}\left(f\right) \land \left(\forall p \in \operatorname{LegalDigits}\left(\right),\; \forall x \in X,\; \operatorname{f}\left(p\right) = x \Leftrightarrow \left(\forall n \in \operatorname{Nat}\left(\right),\; x \in \operatorname{K}\left(n, \operatorname{legalPrefix}\left(p, n\right)\right)\right)\right)\right)\right)\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Topology/LegalFiberReconstruction.continuous_reconstruction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The type X is any compact metric space, at arbitrary universe level u. All nonemptiness and compactness assumptions range over legal prefixes only. Diameter is real-valued; compactness supplies the boundedness needed by the distance estimate. Shrinking is quantified separately for each legal infinite branch. The map f is continuous and onto, and its value is the unique point belonging to every fiber on that branch, including the root. Different names may represent the same point. Child fibers may overlap. No uniform shrinking rate or effective selection algorithm is asserted.

Child coverage makes each branch decreasing. Cantor's compact intersection theorem supplies a point in its full intersection. The distance between any two such points is bounded by every branch diameter, so it is zero. For a prescribed point x, choose successively a legal child whose fiber still contains that same x. The selected finite words agree on every earlier coordinate. Their diagonal entries define a stream, and every selected word is its exact restriction. Its adjacent entries occur together in a legal finite word, so this stream is an element of LegalDigits. It names x.

At a fixed name p, choose a prefix whose fiber diameter is below the desired positive error. All names agreeing with p on this finite prefix form a neighborhood. Their reconstructed points lie in the same fiber, proving continuity without a uniform convergence hypothesis. The compact-intersection supplier is IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed; the real metric estimate is Metric.dist_le_diam_of_mem. These classical results are applied directly. The legal-prefix construction uses the existing LegalDigits representation.

## References

- Truth anchor: `D5/S3/Topology/LegalFiberReconstruction.continuous_reconstruction`
- Dependency: [D5/S1/Digit/Infinite/SuccessorContinuity](../../S1/Digit/Infinite/SuccessorContinuity.md)
