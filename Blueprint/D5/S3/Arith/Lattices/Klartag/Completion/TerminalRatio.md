# Terminal Ratio

## Abstract

Uniform constants and completion of lattice packing.

Uniform constants and completion of lattice packing. The results below relate terminal ratio to the stochastic ellipsoid construction.

**Theorem 1.1 (n mul pow mul C1c R).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Completion/TerminalRatio.n_mul_pow_mul_C1cR`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Completion/TerminalRatio.n_mul_pow_mul_C1cR` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

ThetaTight.n_mul_pow_mul_C1c at KcR. C1cR differs from C1c only by Kc → KcR, so the same identity holds and the combination is again α-free.

**Theorem 1.2 (alpha mul rho C pow le).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Completion/TerminalRatio.alpha_mul_rhoC_pow_le`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Completion/TerminalRatio.alpha_mul_rhoC_pow_le` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

(α·ρ)ⁿ ≤ 1 at a₀ = a0C n: √(a0C n) = (1 − 1/n)⁻¹, so α·ρ ≤ 1 − 3/(4n) < 1.

**Theorem 1.3 (theta Tight terminal le).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Completion/TerminalRatio.thetaTight_terminal_le`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Completion/TerminalRatio.thetaTight_terminal_le` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The terminal threshold is Θ(n²) with an absolute constant. b is the coefficient the combined weight gives the terminal summand (b = 1 for the bare radial bound, b = 4 once ChainRaw3.tailT's own factor is counted).

## References

- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Completion/TerminalRatio.alpha_mul_rhoC_pow_le`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Completion/TerminalRatio.n_mul_pow_mul_C1cR`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Completion/TerminalRatio.thetaTight_terminal_le`
- Dependency: [D5/S3/Arith/Lattices/Klartag/Contact/Lemma43UniformR2](../Contact/Lemma43UniformR2.md)
- Dependency: [D5/S3/Arith/Lattices/Klartag/Drift/Stopped/DriftStopped6c](../Drift/Stopped/DriftStopped6c.md)
