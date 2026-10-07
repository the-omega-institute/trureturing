# Good Path Core

## Abstract

Uniform constants and completion of lattice packing.

Uniform constants and completion of lattice packing. The results below relate good path core to the stochastic ellipsoid construction.

**Definition 1.1 (const Fil).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Completion/GoodPathCore.constFil`

*Formalization.* `D5/S3/Arith/Lattices/Klartag/Completion/GoodPathCore.constFil` (`✓ std3`).

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The constant filtration, so the ℱ-relative lemmas of DriftInputsStopped give their ambient forms with no second proof.

**Theorem 1.2 (coe v adopted).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Completion/GoodPathCore.coe_v_adopted`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Completion/GoodPathCore.coe_v_adopted` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

v = c² = h at the adopted step scale.

**Theorem 1.3 (step tail exponent).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Completion/GoodPathCore.step_tail_exponent`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Completion/GoodPathCore.step_tail_exponent` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The per-step tail is exactly e^{−n} — the adopted η = √(2hdn) is chosen for it.

**Theorem 1.4 (acc Good thr).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Completion/GoodPathCore.accGood_thr`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Completion/GoodPathCore.accGood_thr` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The accGood failure bound. The adopted r₀ = 24√(log n/n) is exactly 6·√(N·h)·√n, so the GOE tail closes at s = 1 with equality.

**Theorem 1.5 (measurable op Norm smul sym Mat).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Completion/GoodPathCore.measurable_opNorm_smul_symMat`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Completion/GoodPathCore.measurable_opNorm_smul_symMat` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The operator norm of r • symMat is measurable — Increments.measurable_opNorm_mkMat through Increments.smul_symMat_eq_mkMat.

**Definition 1.6 (fail Total).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Completion/GoodPathCore.failTotal`

*Formalization.* `D5/S3/Arith/Lattices/Klartag/Completion/GoodPathCore.failTotal` (`✓ std3`).

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The three failure probabilities, summed.

## References

- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Completion/GoodPathCore.accGood_thr`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Completion/GoodPathCore.coe_v_adopted`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Completion/GoodPathCore.constFil`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Completion/GoodPathCore.failTotal`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Completion/GoodPathCore.measurable_opNorm_smul_symMat`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Completion/GoodPathCore.step_tail_exponent`
- Dependency: [D5/S3/Arith/Lattices/Klartag/Completion/GoodPathLight](GoodPathLight.md)
- Dependency: [D5/S3/Arith/Lattices/Klartag/Contact/ThetaTight](../Contact/ThetaTight.md)
- Dependency: [D5/S3/Arith/Lattices/Klartag/State/StateSupply](../State/StateSupply.md)
