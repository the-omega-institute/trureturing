# Tail Wiring

## Abstract

Lattice tail bounds along the matrix walk.

Lattice tail bounds along the matrix walk. The results below relate tail wiring to the stochastic ellipsoid construction.

**Definition 1.1 (Wg).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Tail/TailWiring.Wg`

*Formalization.* `D5/S3/Arith/Lattices/Klartag/Tail/TailWiring.Wg` (`✓ std3`).

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

Abbreviation for the chain the drift side runs: the reach-2 window, the chain's own q and A₀, and the adopted Gaussian step.

**Theorem 1.2 (int Weight mono steps).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Tail/TailWiring.intWeight_mono_steps`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Tail/TailWiring.intWeight_mono_steps` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

intWeight is monotone in the step count.

**Theorem 1.3 (int Weight le prof win).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Tail/TailWiring.intWeight_le_prof_win`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Tail/TailWiring.intWeight_le_prof_win` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The integrated bound on windowOfR2, pointwise and real. intWeight_leRW2 at the window, then intWeight_mono_steps down to any K ≤ N.

**Theorem 1.4 (htail win).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Tail/TailWiring.htail_win`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Tail/TailWiring.htail_win` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The terminal bound on windowOfR2, in the exact htail shape — 2·weight + 0 with weight y = 2·profileAt … (horizon (m+1)) ‖toE (m+1) y‖, at every K < N.

**Theorem 1.5 (sum lt of sum of Real).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Tail/TailWiring.sum_lt_of_sum_ofReal`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Tail/TailWiring.sum_lt_of_sum_ofReal` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

A sum of ENNReal.ofReals below ENNReal.ofReal Θ is a real strict inequality.

**Theorem 1.6 (sums at window Of R2).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Tail/TailWiring.sums_at_windowOfR2`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Tail/TailWiring.sums_at_windowOfR2` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The two sums, from one light-contact hypothesis at the combined profileAt family. The first is FinalDischarge2.hS_of_intWeight_wired's hlight; the second is TerminalCount.countGood_of_terminal_weight's hθ, at the weight htail_win supplies.

**Theorem 1.7 (h S light win).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Tail/TailWiring.hS_light_win`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Tail/TailWiring.hS_light_win` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

hS's hypothesis, in FinalDischarge2.hS_of_intWeight_wired's exact shape (≤).

**Theorem 1.8 (hcnt win).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Tail/TailWiring.hcnt_win`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Tail/TailWiring.hcnt_win` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

hcnt, finished — TerminalCount.countGood_of_terminal_weight at htail_win and the second sum. Holds at every K < N, so the count index is the caller's choice.

## References

- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Tail/TailWiring.Wg`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Tail/TailWiring.hS_light_win`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Tail/TailWiring.hcnt_win`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Tail/TailWiring.htail_win`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Tail/TailWiring.intWeight_le_prof_win`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Tail/TailWiring.intWeight_mono_steps`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Tail/TailWiring.sum_lt_of_sum_ofReal`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Tail/TailWiring.sums_at_windowOfR2`
- Dependency: [D5/S3/Arith/Lattices/Klartag/Completion/Theorem2R4](../Completion/Theorem2R4.md)
- Dependency: [D5/S3/Arith/Lattices/Klartag/Tail/TailHypsWindow](TailHypsWindow.md)
