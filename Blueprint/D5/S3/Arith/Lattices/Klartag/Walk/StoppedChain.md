# Stopped Chain

## Abstract

Gaussian matrix walk, filtration and stopped increments.

Gaussian matrix walk, filtration and stopped increments. The results below relate stopped chain to the stochastic ellipsoid construction.

**Definition 1.1 (tau Of).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Walk/StoppedChain.tauOf`

*Formalization.* `D5/S3/Arith/Lattices/Klartag/Walk/StoppedChain.tauOf` (`✓ std3`).

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The first exit before N. tauOf G N ω is the least k < N with ω ∉ G k, and N if there is none.

**Theorem 1.2 (mem of lt tau Of).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Walk/StoppedChain.mem_of_lt_tauOf`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Walk/StoppedChain.mem_of_lt_tauOf` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

Before the stopping time every event has held.

**Theorem 1.3 (tau Of le iff).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Walk/StoppedChain.tauOf_le_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Walk/StoppedChain.tauOf_le_iff` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

{τ ≤ k} unfolds to a finite union of the failures at times ≤ k.

**Theorem 1.4 (is Stopping Time tau Of).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Walk/StoppedChain.isStoppingTime_tauOf`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Walk/StoppedChain.isStoppingTime_tauOf` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

tauOf is a stopping time for any filtration measuring each G k at time k.

**Definition 1.5 (state Good).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Walk/StoppedChain.stateGood`

*Formalization.* `D5/S3/Arith/Lattices/Klartag/Walk/StoppedChain.stateGood` (`✓ std3`).

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The ℱ k-measurable part of the good event at step k — exactly the three facts StateInvariant4.stateBounds_wired' consumes, and no more: the *earlier* per-step bounds, the accumulated bound at k, and the contact count at k.

**Theorem 1.6 (state Good zero).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Walk/StoppedChain.stateGood_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Walk/StoppedChain.stateGood_zero` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The chain starts inside: gaussSum … 0 = 0 and C₀ = ∅.

**Definition 1.7 (tau).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Walk/StoppedChain.tau`

*Formalization.* `D5/S3/Arith/Lattices/Klartag/Walk/StoppedChain.tau` (`✓ std3`).

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The stopping time: the first index at which the state conditions fail. It is a genuine stopping time for ℱ — stateGood k is ℱ k-measurable — and stateGood_zero makes it at least 1, so τ − 1 is always a *good* index. That is what the stopped state freezes at.

**Theorem 1.8 (one le tau).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Walk/StoppedChain.one_le_tau`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Walk/StoppedChain.one_le_tau` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The chain never stops at 0.

**Theorem 1.9 (state Good of lt tau).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Walk/StoppedChain.stateGood_of_lt_tau`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Walk/StoppedChain.stateGood_of_lt_tau` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

Every index strictly below the stopping time is good.

**Definition 1.10 (stopped State).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Walk/StoppedChain.stoppedState`

*Formalization.* `D5/S3/Arith/Lattices/Klartag/Walk/StoppedChain.stoppedState` (`✓ std3`).

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The stopped state A^τ_k := A_{min k (τ−1)}: frozen at the last index the state conditions covered. one_le_tau makes τ − 1 well defined and good.

**Theorem 1.11 (state Bounds stopped).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Walk/StoppedChain.stateBounds_stopped`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Walk/StoppedChain.stateBounds_stopped` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The bounds hold for the stopped state everywhere — no good event and no a.e. This is what makes the inverse state, its log-determinant and the chain error bounded, and so the eight integrability and measurability hypotheses of the drift theorem reachable.

**Theorem 1.12 (is Stopping Time tau).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Walk/StoppedChain.isStoppingTime_tau`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Walk/StoppedChain.isStoppingTime_tau` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

τ is a stopping time for any filtration that measures the state conditions at their own index — which ChainSetup.filtration does, since Chain.measurable_chain makes the chain adapted and ξ j is ℱ (j+1)-measurable for j < k.

## References

- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Walk/StoppedChain.isStoppingTime_tau`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Walk/StoppedChain.isStoppingTime_tauOf`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Walk/StoppedChain.mem_of_lt_tauOf`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Walk/StoppedChain.one_le_tau`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Walk/StoppedChain.stateBounds_stopped`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Walk/StoppedChain.stateGood`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Walk/StoppedChain.stateGood_of_lt_tau`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Walk/StoppedChain.stateGood_zero`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Walk/StoppedChain.stoppedState`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Walk/StoppedChain.tau`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Walk/StoppedChain.tauOf`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Walk/StoppedChain.tauOf_le_iff`
- Dependency: [D5/S3/Arith/Lattices/Klartag/State/StateInvariant4](../State/StateInvariant4.md)
- Dependency: [D5/S3/Arith/Lattices/Klartag/Walk/ChainSetup](ChainSetup.md)
