# Good Path Var

## Abstract

Uniform constants and completion of lattice packing.

Uniform constants and completion of lattice packing. The results below relate good path var to the stochastic ellipsoid construction.

**Theorem 1.1 (pos part split).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Completion/GoodPathVar.pos_part_split`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Completion/GoodPathVar.pos_part_split` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

(x − L)⁺ = (x − L) + (L − x)⁺.

**Theorem 1.2 (exists mem of variance).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Completion/GoodPathVar.exists_mem_of_variance`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Completion/GoodPathVar.exists_mem_of_variance` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The existence step against a lower-tail bound. s is the expected shortfall below L and f the good event's failure probability. Markov runs on (X − L)⁺, so nothing here needs a pointwise floor for X — which is the whole point: the floor n·log (mAt n c₃) is what made GoodPathBounds.exists_mem_of_integral_le's margin decay like 1/n.

## References

- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Completion/GoodPathVar.exists_mem_of_variance`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Completion/GoodPathVar.pos_part_split`
- Dependency: [D5/S3/Arith/Lattices/Klartag/Completion/GoodPathBounds](GoodPathBounds.md)
