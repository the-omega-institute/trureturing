# Lemma43Uniform R

## Abstract

Contact profile counts and accumulated projection dimension.

Contact profile counts and accumulated projection dimension. The results below relate lemma43uniform r to the stochastic ellipsoid construction.

**Definition 1.1 (r16).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Contact/Lemma43UniformR.r16`

*Formalization.* `D5/S3/Arith/Lattices/Klartag/Contact/Lemma43UniformR.r16` (`✓ std3`).

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

n^{1/16}, as four nested square roots.

**Theorem 1.2 (junk endpoint two log).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Contact/Lemma43UniformR.junk_endpoint_two_log`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Contact/Lemma43UniformR.junk_endpoint_two_log` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

At the doubled logarithmic endpoint and above the dimension threshold, the correction term is at most three. The logarithmic growth is bounded by a sixteenth power of the dimension.

**Theorem 1.3 (pieces four).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Contact/Lemma43UniformR.pieces_four`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Contact/Lemma43UniformR.pieces_four` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The four-piece radial bound. pieces_at_params on (0, Ymid] and FarBand.far_le on (Ymid, Y1], summed. The far band contributes at most 1, so K becomes K + 1.

**Theorem 1.4 (logn sqrt T le quarter).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Contact/Lemma43UniformR.logn_sqrtT_le_quarter`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Contact/Lemma43UniformR.logn_sqrtT_le_quarter` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

log n·√T ≤ 1/4 — the quarter version of Lemma43Uniform.logn_sqrtT_le, needed because the split point is 2·log n.

**Theorem 1.5 (twelve le log).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Contact/Lemma43UniformR.twelve_le_log`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Contact/Lemma43UniformR.twelve_le_log` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

12 ≤ log n at the threshold (e¹² = 162 755 ≤ 2 073 600).

**Definition 1.6 (Kc R).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Contact/Lemma43UniformR.KcR`

*Formalization.* `D5/S3/Arith/Lattices/Klartag/Contact/Lemma43UniformR.KcR` (`✓ std3`).

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

pieces_four's constant: Lemma43Uniform.Kc + 1.

**Definition 1.7 (C1c R).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Contact/Lemma43UniformR.C1cR`

*Formalization.* `D5/S3/Arith/Lattices/Klartag/Contact/Lemma43UniformR.C1cR` (`✓ std3`).

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

Lemma 4.3's per-t constant at the reach window.

**Theorem 1.8 (ct le).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Contact/Lemma43UniformR.ct_le`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Contact/Lemma43UniformR.ct_le` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

((n+2)/2)·t ≤ 1/100 for t ≤ T — the far band's a ≥ 0.49.

**Theorem 1.9 (cs le).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Contact/Lemma43UniformR.cs_le`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Contact/Lemma43UniformR.cs_le` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

((n+2)/2)·√t ≤ 3·√(log n) for t ≤ T.

**Theorem 1.10 (far numerics).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Contact/Lemma43UniformR.far_numerics`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Contact/Lemma43UniformR.far_numerics` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The far band's two numeric side conditions, as a standalone lemma: pieces_four's hlam and hfar at the split point Ymid ≥ 2·log n.

**Definition 1.11 (C1R).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Contact/Lemma43UniformR.C1R`

*Formalization.* `D5/S3/Arith/Lattices/Klartag/Contact/Lemma43UniformR.C1R` (`✓ std3`).

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

Lemma 4.3's per-t constant at the reach window, with the small-t branch's e².

## References

- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Contact/Lemma43UniformR.C1R`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Contact/Lemma43UniformR.C1cR`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Contact/Lemma43UniformR.KcR`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Contact/Lemma43UniformR.cs_le`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Contact/Lemma43UniformR.ct_le`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Contact/Lemma43UniformR.far_numerics`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Contact/Lemma43UniformR.junk_endpoint_two_log`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Contact/Lemma43UniformR.logn_sqrtT_le_quarter`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Contact/Lemma43UniformR.pieces_four`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Contact/Lemma43UniformR.r16`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Contact/Lemma43UniformR.twelve_le_log`
- Dependency: [D5/S3/Arith/Lattices/Klartag/Contact/Lemma43Uniform](Lemma43Uniform.md)
- Dependency: [D5/S3/Arith/Lattices/Klartag/Tail/FarBand](../Tail/FarBand.md)
