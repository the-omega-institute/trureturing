# Theta Tight

## Abstract

Contact profile counts and accumulated projection dimension.

Contact profile counts and accumulated projection dimension. The results below relate theta tight to the stochastic ellipsoid construction.

**Theorem 1.1 (alpha mul rho C).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Contact/ThetaTight.alpha_mul_rhoC`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Contact/ThetaTight.alpha_mul_rhoC` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

α·ρ = (√a₀)⁻¹ + α√n/2 — the α-dependence of ρ is exactly one factor of α⁻¹.

**Theorem 1.2 (alpha mul rho C le).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Contact/ThetaTight.alpha_mul_rhoC_le`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Contact/ThetaTight.alpha_mul_rhoC_le` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The upper end of α·ρ, from the tiling defect n·(α√n/2) ≤ 1/4.

**Definition 1.3 (theta Tight).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Contact/ThetaTight.thetaTight`

*Formalization.* `D5/S3/Arith/Lattices/Klartag/Contact/ThetaTight.thetaTight` (`✓ std3`).

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The tight threshold. Params.markov asks for 2(p−1)·n·κ_n·C < θ·(pⁿ−1); this is the smallest θ that meets it, written out. Unlike 16·C it is α-free to within the tiling defect, because n·κ_n·C1c = p^{n−1}·(n·αⁿ·C1c).

**Theorem 1.4 (two mul lt theta Tight mul).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Contact/ThetaTight.two_mul_lt_thetaTight_mul`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Contact/ThetaTight.two_mul_lt_thetaTight_mul` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

thetaTight clears markov's bound with a factor of two to spare.

## References

- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Contact/ThetaTight.alpha_mul_rhoC`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Contact/ThetaTight.alpha_mul_rhoC_le`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Contact/ThetaTight.thetaTight`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Contact/ThetaTight.two_mul_lt_thetaTight_mul`
- Dependency: [D5/S3/Arith/Lattices/Klartag/Completion/TerminalCount](../Completion/TerminalCount.md)
