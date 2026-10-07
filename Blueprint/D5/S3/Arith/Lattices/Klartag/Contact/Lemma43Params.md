# Lemma43Params

## Abstract

Contact profile counts and accumulated projection dimension.

Contact profile counts and accumulated projection dimension. The results below relate lemma43params to the stochastic ellipsoid construction.

**Theorem 1.1 (params a0 ge one).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Contact/Lemma43Params.params_a0_ge_one`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Contact/Lemma43Params.params_a0_ge_one` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

a₀ = (1 − 1/n)⁻¹² ≥ 1 for n ≥ 2. ha₀ of hgbound_chained.

**Theorem 1.2 (a0 ge one).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Contact/Lemma43Params.a0_ge_one`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Contact/Lemma43Params.a0_ge_one` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

Params' inherits a₀ ≥ 1.

**Theorem 1.3 (window sub pos).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Contact/Lemma43Params.window_sub_pos`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Contact/Lemma43Params.window_sub_pos` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The extended radial parameters ensure that a0-sqrt(T)*y stays positive throughout the substitution window.

**Theorem 1.4 (window one sub pos).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Contact/Lemma43Params.window_one_sub_pos`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Contact/Lemma43Params.window_one_sub_pos` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The window smallness condition keeps 1-sqrt(T)*y positive throughout the substitution window.

## References

- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Contact/Lemma43Params.a0_ge_one`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Contact/Lemma43Params.params_a0_ge_one`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Contact/Lemma43Params.window_one_sub_pos`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Contact/Lemma43Params.window_sub_pos`
- Dependency: [D5/S3/Arith/Lattices/Klartag/Completion/HJ](../Completion/HJ.md)
- Dependency: [D5/S3/Arith/Lattices/Klartag/Walk/ChainDataInst](../Walk/ChainDataInst.md)
