# Discrete Cut Reconstruction

## Abstract

All rational binary cuts reconstruct a real parameter, while every finite selection leaves a distinct compatible parameter.

**Theorem 1.1 (The complete rational cut profile reconstructs its real parameter).**

$$\forall x \in \mathbb{R},\; \operatorname{sSup}\left(\left\{(q : \mathbb{R}) \mid q \in \mathbb{Q}, \operatorname{decide}\left(q < x\right) = true\right\}\right) = x \land \left(\left(\forall q \in \mathbb{Q},\; \exists y \in \mathbb{R},\; y \ne x \land \operatorname{decide}\left(q < x\right) = \operatorname{decide}\left(q < y\right)\right) \land \left(\left(\forall cuts \in \operatorname{Finset}\left(\mathbb{Q}\right),\; \exists y \in \mathbb{R},\; y \ne x \land \left(\forall q \in \mathbb{Q},\; q \in cuts \Rightarrow \operatorname{decide}\left(q < x\right) = \operatorname{decide}\left(q < y\right)\right)\right) \land \left(\forall p \in \mathbb{Q}, q \in \mathbb{Q},\; p \le q \Rightarrow \left(\left(\operatorname{decide}\left(q < x\right) = true \Rightarrow \operatorname{decide}\left(p < x\right) = true\right) \land \left(\operatorname{decide}\left(p < x\right) = false \Rightarrow \operatorname{decide}\left(q < x\right) = false\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Completion/DiscreteCutReconstruction.discrete_cut_reconstruction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a real x and rational q, the binary name is the decidable truth value of q < x. The supremum clause uses exactly the rational casts whose binary names are true, so the reconstruction is attached to the source threshold semantics rather than to an abstract code.

A single cutoff cannot identify x. More generally, for any finite set of cutoffs, the proof constructs a distinct y below x with all selected readouts unchanged. If some selected cutoff lies below x, y is chosen between x and the largest such cutoff; otherwise x minus one works.

The final two implications state compatibility with rational order: a true readout propagates to every lower cutoff, and a false readout propagates to every higher cutoff. Pinned Mathlib supplies rational density and the conditional-completeness supremum bridge, but no whole theorem.

## References

- Truth anchor: `D5/S3/Observer/Completion/DiscreteCutReconstruction.discrete_cut_reconstruction`
