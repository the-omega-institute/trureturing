# Drift Accumulated

## Abstract

Second order log determinant bounds and accumulated drift.

Second order log determinant bounds and accumulated drift. The results below relate drift accumulated to the stochastic ellipsoid construction.

**Theorem 1.1 (sum good le of prefix).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Drift/DriftAccumulated.sum_good_le_of_prefix`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Drift/DriftAccumulated.sum_good_le_of_prefix` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

DriftStopped5.sum_good_le with the freeze count removed. The indicator restricts the sum to k < τ ω − 1, i.e. to Finset.range (min m (τ ω − 1)), and that index is < τ ω; so a single prefix-sum bound at one index replaces "dim E freezes, each costing ε".

**Theorem 1.2 (sum stopped Err le acc).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Drift/DriftAccumulated.sum_stoppedErr_le_acc`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Drift/DriftAccumulated.sum_stoppedErr_le_acc` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

DriftStopped5.sum_stoppedErr_le with the accumulated total. Only the good-range summand changes; the middle case is still one increment read at τ − 1.

**Theorem 1.3 (integral sum stopped Err le acc).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Drift/DriftAccumulated.integral_sum_stoppedErr_le_acc`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Drift/DriftAccumulated.integral_sum_stoppedErr_le_acc` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

DriftStopped6.integral_sum_stoppedErr_le with the accumulated total.

**Theorem 1.4 (sum integral stopped Err le acc).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Drift/DriftAccumulated.sum_integral_stoppedErr_le_acc`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Drift/DriftAccumulated.sum_integral_stoppedErr_le_acc` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

DriftStopped6.sum_integral_stoppedErr_le with the accumulated total — the shape ChainDrift.drift_bound consumes.

**Theorem 1.5 (drift bound stopped acc).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Drift/DriftAccumulated.drift_bound_stopped_acc`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Drift/DriftAccumulated.drift_bound_stopped_acc` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

DriftStopped6.drift_bound_stopped_maximal with the accumulated total. This is a *re-instantiation*: DriftStopped6.drift_bound_stopped already takes the error total E as an input, so only the argument supplied for it changes.

**Definition 1.6 (drift RHS acc).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Drift/DriftAccumulated.driftRHS_acc`

*Formalization.* `D5/S3/Arith/Lattices/Klartag/Drift/DriftAccumulated.driftRHS_acc` (`✓ std3`).

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

GoodPathBounds.driftRHS with the error total free. driftRHS n A₀ c₃ ε S is driftRHS_acc n A₀ c₃ (dim E · ε) S definitionally (driftRHS_eq).

**Theorem 1.7 (drift bound at acc).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Drift/DriftAccumulated.drift_bound_at_acc`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Drift/DriftAccumulated.drift_bound_at_acc` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The accumulated prefix error bound controls determinant drift up to a good cut, with total error E in place of a separate charge for every active-set change.

**Theorem 1.8 (sum chain Err le c3).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Drift/DriftAccumulated.sum_chainErr_le_c3`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Drift/DriftAccumulated.sum_chainErr_le_c3` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The prefix-sum hypothesis, discharged. ChainErrBudget.sum_chainErr_le_of_lt_tau gives |C_K|·η/m; stateGood K (available because K < τ) gives |C_K| ≤ c₃.

## References

- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Drift/DriftAccumulated.driftRHS_acc`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Drift/DriftAccumulated.drift_bound_at_acc`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Drift/DriftAccumulated.drift_bound_stopped_acc`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Drift/DriftAccumulated.integral_sum_stoppedErr_le_acc`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Drift/DriftAccumulated.sum_chainErr_le_c3`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Drift/DriftAccumulated.sum_good_le_of_prefix`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Drift/DriftAccumulated.sum_integral_stoppedErr_le_acc`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Drift/DriftAccumulated.sum_stoppedErr_le_acc`
- Dependency: [D5/S3/Arith/Lattices/Klartag/Completion/GoodPathBounds](../Completion/GoodPathBounds.md)
- Dependency: [D5/S3/Arith/Lattices/Klartag/Completion/GoodPathLight](../Completion/GoodPathLight.md)
- Dependency: [D5/S3/Arith/Lattices/Klartag/Completion/TerminalRatio](../Completion/TerminalRatio.md)
- Dependency: [D5/S3/Arith/Lattices/Klartag/Drift/Stopped/DriftStopped6d](Stopped/DriftStopped6d.md)
- Dependency: [D5/S3/Arith/Lattices/Klartag/Walk/ChainErrBudget](../Walk/ChainErrBudget.md)
