# Good Path Light

## Abstract

Uniform constants and completion of lattice packing.

Uniform constants and completion of lattice packing. The results below relate good path light to the stochastic ellipsoid construction.

**Theorem 1.1 (sum free ge cut).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Completion/GoodPathLight.sum_free_ge_cut`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Completion/GoodPathLight.sum_free_ge_cut` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

sum_free_ge, corrected for a cut free dimension. sum_free_ge needs dim − |C_k| ≤ Nfun k ω everywhere; when Nfun is cut at a stopping time that fails after it, and the repair is the extra term dim·∑_k P(bad k). Everything else is sum_free_ge's own argument.

## References

- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Completion/GoodPathLight.sum_free_ge_cut`
- Dependency: [D5/S3/Arith/Lattices/Klartag/Completion/TerminalCount](TerminalCount.md)
- Dependency: [D5/S3/Arith/Lattices/Klartag/State/StateSupply](../State/StateSupply.md)
