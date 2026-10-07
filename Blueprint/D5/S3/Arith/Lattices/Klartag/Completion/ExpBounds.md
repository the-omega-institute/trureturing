# Exp Bounds

## Abstract

Uniform constants and completion of lattice packing.

Uniform constants and completion of lattice packing. The results below relate exp bounds to the stochastic ellipsoid construction.

**Theorem 1.1 (exp three le).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Completion/ExpBounds.exp_three_le`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Completion/ExpBounds.exp_three_le` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

e³ ≤ 20.0856.

**Theorem 1.2 (exp six le).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Completion/ExpBounds.exp_six_le`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Completion/ExpBounds.exp_six_le` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

e⁶ ≤ 403.429. Note this is not (e³)²: 20.0856² = 403.4313 overshoots.

**Theorem 1.3 (exp half le).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Completion/ExpBounds.exp_half_le`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Completion/ExpBounds.exp_half_le` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

e^{1/2} ≤ 1.64873, from (e^{1/2})² = e < 2.7182818286 < 1.64873².

**Theorem 1.4 (exp half mul Kc R le).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Completion/ExpBounds.exp_half_mul_KcR_le`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Completion/ExpBounds.exp_half_mul_KcR_le` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The hypothesis TerminalRatio.thetaTight_terminal_le takes, discharged. Verbatim its hKcR binder (TerminalRatio.lean:78).

## References

- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Completion/ExpBounds.exp_half_le`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Completion/ExpBounds.exp_half_mul_KcR_le`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Completion/ExpBounds.exp_six_le`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Completion/ExpBounds.exp_three_le`
- Dependency: [D5/S3/Arith/Lattices/Klartag/Completion/TerminalRatio](TerminalRatio.md)
