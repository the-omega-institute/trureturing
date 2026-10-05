# Profile Bound7

## Abstract

Contact profile counts and accumulated projection dimension.

Contact profile counts and accumulated projection dimension. The results below relate profile bound7 to the stochastic ellipsoid construction.

**Theorem 1.1 (one le log of three).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Contact/ProfileBound7.one_le_log_of_three`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Contact/ProfileBound7.one_le_log_of_three` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

log n ≥ 1 for n ≥ 3, because e < 3. This is n₁.

**Theorem 1.2 (drift eq).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Contact/ProfileBound7.drift_eq`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Contact/ProfileBound7.drift_eq` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The drift is 2√(log n) exactly at T = 16·log n/n².

**Theorem 1.3 (one le sqrt log).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Contact/ProfileBound7.one_le_sqrt_log`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Contact/ProfileBound7.one_le_sqrt_log` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

√(log n) ≥ 1 for n ≥ 3.

**Theorem 1.4 (window mul le).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Contact/ProfileBound7.window_mul_le`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Contact/ProfileBound7.window_mul_le` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

From √t·Y ≤ 1/2 and 0 ≤ y ≤ Y: the window's basic inequality.

**Theorem 1.5 (window one sub pos).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Contact/ProfileBound7.window_one_sub_pos`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Contact/ProfileBound7.window_one_sub_pos` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

hpos : 0 < 1 − √t·y on the window.

**Theorem 1.6 (window gap).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Contact/ProfileBound7.window_gap`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Contact/ProfileBound7.window_gap` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

hSc : 0 < a₀ − √t·y on the window, and shape 4's gap: a₀ − 1/2 ≤ a₀ − √t·y, so the Jacobian bound of substDeriv_le applies with ε = a₀ − 1/2.

**Theorem 1.7 (radius Of nonneg).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Contact/ProfileBound7.radiusOf_nonneg`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Contact/ProfileBound7.radiusOf_nonneg` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

hρ : 0 ≤ radiusOf 0 — the shell's inner radius is positive.

**Theorem 1.8 (radius Of le end).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Contact/ProfileBound7.radiusOf_le_end`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Contact/ProfileBound7.radiusOf_le_end` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

hρW : radiusOf 0 ≤ radiusOf Y and hW : radiusOf y ≤ radiusOf Y — monotonicity.

## References

- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Contact/ProfileBound7.drift_eq`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Contact/ProfileBound7.one_le_log_of_three`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Contact/ProfileBound7.one_le_sqrt_log`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Contact/ProfileBound7.radiusOf_le_end`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Contact/ProfileBound7.radiusOf_nonneg`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Contact/ProfileBound7.window_gap`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Contact/ProfileBound7.window_mul_le`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Contact/ProfileBound7.window_one_sub_pos`
- Dependency: [D5/S3/Arith/Lattices/Klartag/Contact/ProfileBound6](ProfileBound6.md)
