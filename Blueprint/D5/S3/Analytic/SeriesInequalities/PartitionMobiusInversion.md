# Partition-Lattice Mobius Inversion

## Abstract

Incidence-algebra inversion gives both finite partition moment-cumulant formulas.

**Theorem 1.1 (Moments and cumulants invert over finite set partitions).**

$$\forall X \in Type, R \in CommRing, A \in \operatorname{Finset}\left(X\right), M \in \operatorname{Finset}\left(X\right) \to R, kappa \in \operatorname{Finset}\left(X\right) \to R,\; \left(\left(\neg A = \emptyset\right) \land \left(\left(\forall pi \in \operatorname{Finpartition}\left(A\right),\; \operatorname{partitionProduct}\left(M, pi\right) = \sum_{sigma \leq pi} \operatorname{partitionProduct}\left(kappa, sigma\right)\right) \land \left(\forall pi \in \operatorname{Finpartition}\left(A\right),\; \operatorname{mu}\left(R, pi, top\right) = {-1}^{\operatorname{card}\left(\operatorname{parts}\left(pi\right)\right) - 1} \cdot \operatorname{factorial}\left(\operatorname{card}\left(\operatorname{parts}\left(pi\right)\right) - 1\right)\right)\right)\right) \Rightarrow \left(kappa\left(A\right) = \sum_{pi \in \operatorname{Finpartition}\left(A\right)} {-1}^{\operatorname{card}\left(\operatorname{parts}\left(pi\right)\right) - 1} \cdot \operatorname{factorial}\left(\operatorname{card}\left(\operatorname{parts}\left(pi\right)\right) - 1\right) \cdot \operatorname{partitionProduct}\left(M, pi\right) \land M\left(A\right) = \sum_{pi \in \operatorname{Finpartition}\left(A\right)} \operatorname{partitionProduct}\left(kappa, pi\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/SeriesInequalities/PartitionMobiusInversion.partition_mobius_moment_cumulant_inversion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let A be a nonempty finite set and let M and kappa assign values in a commutative ring to finite subsets. For a partition pi, P_w(pi) denotes the product of the block weights w(B).

Assume on every coarse partition that its moment product is the sum of the cumulant products over all refinements. Also assume the displayed classical closed formula for the partition-lattice Mobius function.

Mathlib's general incidence-algebra Mobius inversion then gives the cumulant formula at the top partition. Evaluating the assumed forward relation at that same top partition gives the reverse moment formula.

The source omitted the nonempty case split implicit in |pi|-1. The theorem requires A to be nonempty, ensuring every partition has at least one block and preventing truncated natural subtraction at zero.

## References

- Truth anchor: `D5/S3/Analytic/SeriesInequalities/PartitionMobiusInversion.partition_mobius_moment_cumulant_inversion`
