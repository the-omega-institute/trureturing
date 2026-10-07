# Exp Decay99

## Abstract

Uniform constants and completion of lattice packing.

Uniform constants and completion of lattice packing. The results below relate exp decay99 to the stochastic ellipsoid construction.

**Theorem 1.1 (pow div le exp).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Completion/ExpDecay99.pow_div_le_exp`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Completion/ExpDecay99.pow_div_le_exp` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

(x/20)^20 ≤ exp x for x ≥ 0. Real.add_one_le_exp at x/20, then pow_le_pow_left₀; exp x = (exp (x/20))^20 is Real.exp_nat_mul.

**Theorem 1.2 (exp neg le).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Completion/ExpDecay99.exp_neg_le`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Completion/ExpDecay99.exp_neg_le` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

e^{-x} ≤ 20²⁰/x²⁰ for x > 0 — the decay FailTotalBound99 consumes.

**Theorem 1.3 (exp neg nat le).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Completion/ExpDecay99.exp_neg_nat_le`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Completion/ExpDecay99.exp_neg_nat_le` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The form the failure bound uses: at a natural n ≥ 1.

## References

- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Completion/ExpDecay99.exp_neg_le`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Completion/ExpDecay99.exp_neg_nat_le`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Completion/ExpDecay99.pow_div_le_exp`
