# Positive Weighted Readout Gram Kernel

## Abstract

A finite positive-weighted readout Gram operator has the common readout kernel.

**Theorem 1.1 (Strictly positive weights preserve exactly the common readout kernel).**

$$\begin{aligned}\forall I: \operatorname{Type}, [\operatorname{Fintype}(I)],\\{}V: \operatorname{Type}, \operatorname{RealInnerFD}(V),\\{}\forall i: I, Y_{i}: \operatorname{Type} \land \operatorname{RealInnerFD}(Y_{i}),\\{}C: \forall i: I, V \to Y_{i}, w: I \to \mathbb{R},\\{}\forall i: I, 0 < w_{i},\\{}W := \sum_{i \in I} w_{i} C_{i}^{*} C_{i},\\{}\forall v: V, \langle v, Wv\rangle = \sum_{i \in I} w_{i} \operatorname{norm}(C_{i}(v))^{2},\\{}\operatorname{ker}(W) = \{v \in V \mid \forall i: I, C_{i}(v) = 0\}.\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/PositiveWeightedReadoutGramKernel.positive_weighted_readout_gram` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The index type is finite, the state space is a finite-dimensional real inner-product space, and each readout may have its own finite-dimensional real inner-product codomain.

The energy identity follows from the adjoint pairing. If the Gram energy vanishes, nonnegativity of every summand and strict positivity of every weight force each readout norm to vanish.

The empty protocol family is included: both kernels are then the whole state space. Strict positivity is essential for nonempty families because a zero weight could hide a nonzero readout.

## References

- Truth anchor: `D5/S3/Observer/PositiveWeightedReadoutGramKernel.positive_weighted_readout_gram`
