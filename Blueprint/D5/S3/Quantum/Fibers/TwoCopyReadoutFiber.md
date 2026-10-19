# Two-Copy Readout Fiber

## Abstract

The real two-copy Bell readout identifies exactly the hidden-phase involution q ↔ 1-q.

Use the explicit five-coordinate phase mixture and its real two-copy Bell readout. The fiber theorem classifies every pair of parameters in the closed unit interval that produce the same readout.

**Theorem 1.1 (Two-copy Bell readout fiber).**

$$\forall q \in \operatorname{IccReal}(0,1),\; \forall r \in \operatorname{IccReal}(0,1),\; (\operatorname{twoCopyProbability}(q) = \operatorname{twoCopyProbability}(r)) \Leftrightarrow (((q: \mathbb{R}) = (r: \mathbb{R})) \lor ((q: \mathbb{R})+(r: \mathbb{R}) = 1))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fibers/TwoCopyReadoutFiber.two_copy_bell_readout_fiber` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The readout sees the square of the signed coordinate 1 - 2q. Its observational fiber is exactly q = r or q + r = 1, so the residual ambiguity is the involution q ↦ 1-q.

This is a finite-dimensional statement for the explicit phase-mixture family. It supplies no FIB Source-to-density bridge, physical preparation, or QFT realization.

## References

- Truth anchor: `D5/S3/Quantum/Fibers/TwoCopyReadoutFiber.two_copy_bell_readout_fiber`
- Dependency: [D5/S3/Quantum/Fibers/FiveModeTwoCopyPhase](FiveModeTwoCopyPhase.md)
