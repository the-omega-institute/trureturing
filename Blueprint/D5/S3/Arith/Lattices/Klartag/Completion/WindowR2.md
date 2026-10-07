# Window R2

## Abstract

Uniform constants and completion of lattice packing.

Uniform constants and completion of lattice packing. The results below relate window r2 to the stochastic ellipsoid construction.

**Definition 1.1 (m R2).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Completion/WindowR2.mR2`

*Formalization.* `D5/S3/Arith/Lattices/Klartag/Completion/WindowR2.mR2` (`✓ std3`).

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The weakest eigenvalue bound the far band can use: a0C n − 1/2.

**Theorem 1.2 (m R2 ge).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Completion/WindowR2.mR2_ge`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Completion/WindowR2.mR2_ge` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

window_small at the generic reach, now le_refl.

**Theorem 1.3 (a0C le one add).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Completion/WindowR2.a0C_le_one_add`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Completion/WindowR2.a0C_le_one_add` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

a0C n ≤ 1 + 3/n.

**Theorem 1.4 (m At ge m R2).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Completion/WindowR2.mAt_ge_mR2`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Completion/WindowR2.mAt_ge_mR2` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

For every admissible contact threshold, the state lower bound dominates the fixed lower bound used to define the enlarged reach window.

**Definition 1.5 (YR2).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Completion/WindowR2.YR2`

*Formalization.* `D5/S3/Arith/Lattices/Klartag/Completion/WindowR2.YR2` (`✓ std3`).

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

YR2 n·√T = a0C n − mR2 n = 1/2, identically in t.

**Definition 1.6 (reach Num2).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Completion/WindowR2.reachNum2`

*Formalization.* `D5/S3/Arith/Lattices/Klartag/Completion/WindowR2.reachNum2` (`✓ std3`).

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The generic reach window's numerator: windowR2 α n = reachNum2 n/α + √n/2 by rfl.

**Definition 1.7 (window R2).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Completion/WindowR2.windowR2`

*Formalization.* `D5/S3/Arith/Lattices/Klartag/Completion/WindowR2.windowR2` (`✓ std3`).

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The generic reach window.

**Theorem 1.8 (reach Num2 eq).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Completion/WindowR2.reachNum2_eq`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Completion/WindowR2.reachNum2_eq` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

reachNum2 = 1/√(mR2).

**Theorem 1.9 (window R2 lt p).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Completion/WindowR2.windowR2_lt_p`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Completion/WindowR2.windowR2_lt_p` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

window_lt_p at the generic reach: 2·reachNum2 n ≤ α·p and α·√n ≤ 1 give windowR2 α n < p. reachNum2 ≈ √2, so the hypothesis is 2.829 ≤ α·p.

## References

- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Completion/WindowR2.YR2`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Completion/WindowR2.a0C_le_one_add`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Completion/WindowR2.mAt_ge_mR2`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Completion/WindowR2.mR2`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Completion/WindowR2.mR2_ge`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Completion/WindowR2.reachNum2`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Completion/WindowR2.reachNum2_eq`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Completion/WindowR2.windowR2`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Completion/WindowR2.windowR2_lt_p`
- Dependency: [D5/S3/Arith/Lattices/Klartag/Completion/GoodPathBounds](GoodPathBounds.md)
- Dependency: [D5/S3/Arith/Lattices/Klartag/Completion/WindowR](WindowR.md)
