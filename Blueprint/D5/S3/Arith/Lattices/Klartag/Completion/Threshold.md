# Threshold

## Abstract

Uniform constants and completion of lattice packing.

Uniform constants and completion of lattice packing. The results below relate threshold to the stochastic ellipsoid construction.

**Definition 1.1 (small Const).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Completion/Threshold.smallConst`

*Formalization.* `D5/S3/Arith/Lattices/Klartag/Completion/Threshold.smallConst` (`✓ std3`).

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The small-dimension constant at the adopted threshold: min_{1 ≤ m < 839} Vol(B^{m+1})/m².

**Definition 1.2 (const).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Completion/Threshold.const`

*Formalization.* `D5/S3/Arith/Lattices/Klartag/Completion/Threshold.const` (`✓ std3`).

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The theorem's constant: c = min c₀ c₁, positive.

**Theorem 1.3 (klartag packing of phi).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Completion/Threshold.klartag_packing_of_phi`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Completion/Threshold.klartag_packing_of_phi` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

Final.klartag_packing_of_hyps with the large-n branch in φ form. Final.Remaining is stated through Assembly.Lemma52, which is the *lattice*-level packaging; the Params route (Assembly.exists_phi_of_params) produces the φ directly, so this variant lets it feed the endgame without repackaging.

## References

- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Completion/Threshold.const`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Completion/Threshold.klartag_packing_of_phi`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Completion/Threshold.smallConst`
- Dependency: [D5/S3/Arith/Lattices/Klartag/Completion/Assembly](Assembly.md)
- Dependency: [D5/S3/Arith/Lattices/Klartag/Completion/Final](Final.md)
