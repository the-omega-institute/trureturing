# Good Path Bounds

## Abstract

Uniform constants and completion of lattice packing.

Uniform constants and completion of lattice packing. The results below relate good path bounds to the stochastic ellipsoid construction.

**Theorem 1.1 (h S of int Weight).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Completion/GoodPathBounds.hS_of_intWeight`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Completion/GoodPathBounds.hS_of_intWeight` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

hS, derived. GoodPathLight.sum_free_ge_cut at Nfun := stoppedFreeDim, Cset := C_k, Good k := {k < τ}, dd := dim E, with the contact total rewritten by ContactIntegrated.integrated_count_eq into (1/h)·∑_{W} intWeight and bounded by the light contact.

**Theorem 1.2 (state Good of good Cut).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Completion/GoodPathBounds.stateGood_of_goodCut`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Completion/GoodPathBounds.stateGood_of_goodCut` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

On goodCut the state conditions hold at every index up to K.

**Theorem 1.3 (lt tau of good Cut).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Completion/GoodPathBounds.lt_tau_of_goodCut`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Completion/GoodPathBounds.lt_tau_of_goodCut` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

Hence the stopping time has not fired by K.

**Theorem 1.4 (state Bounds good Cut).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Completion/GoodPathBounds.stateBounds_goodCut`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Completion/GoodPathBounds.stateBounds_goodCut` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

StateBounds at index K on goodCut — StateInvariant4.stateBounds_wired''s proof with the count taken at K directly instead of transported from N.

## References

- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Completion/GoodPathBounds.hS_of_intWeight`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Completion/GoodPathBounds.lt_tau_of_goodCut`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Completion/GoodPathBounds.stateBounds_goodCut`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Completion/GoodPathBounds.stateGood_of_goodCut`
- Dependency: [D5/S3/Arith/Lattices/Klartag/Completion/GoodPathCore](GoodPathCore.md)
