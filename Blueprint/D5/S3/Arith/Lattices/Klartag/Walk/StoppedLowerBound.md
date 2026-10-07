# Stopped Lower Bound

## Abstract

Gaussian matrix walk, filtration and stopped increments.

Gaussian matrix walk, filtration and stopped increments. The results below relate stopped lower bound to the stochastic ellipsoid construction.

**Theorem 1.1 (state Bounds of state Good).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Walk/StoppedLowerBound.stateBounds_of_stateGood`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Walk/StoppedLowerBound.stateBounds_of_stateGood` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The state bounds from stateGood at the same index. CutSideConditions' proof with the goodCut membership replaced by the weaker stateGood, which the stopping time supplies.

**Theorem 1.2 (norm incr le of state Good).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Walk/StoppedLowerBound.norm_incr_le_of_stateGood`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Walk/StoppedLowerBound.norm_incr_le_of_stateGood` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The increment ceiling from stateGood one index later. stateGood (j+1) carries both ‖ξ_j‖ ≤ η and card C_{j+1} ≤ c₃, and newActive_j ⊆ C_{j+1}.

**Theorem 1.3 (log Det stopped ge).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Walk/StoppedLowerBound.logDet_stopped_ge`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Walk/StoppedLowerBound.logDet_stopped_ge` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The pathwise lower bound on the stopped log-determinant, at every ω. The index is K' = min K (τ−1), which is what stoppedState reads, and every j < K' is strictly below τ, so StoppedChain.stateGood_of_lt_tau discharges both side conditions with no good event.

## References

- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Walk/StoppedLowerBound.logDet_stopped_ge`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Walk/StoppedLowerBound.norm_incr_le_of_stateGood`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Walk/StoppedLowerBound.stateBounds_of_stateGood`
- Dependency: [D5/S3/Arith/Lattices/Klartag/Contact/CutSideConditions](../Contact/CutSideConditions.md)
