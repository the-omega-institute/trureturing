# Lemma43D

## Abstract

Contact profile counts and accumulated projection dimension.

Contact profile counts and accumulated projection dimension. The results below relate lemma43d to the stochastic ellipsoid construction.

**Theorem 1.1 (integrable On t of bounded).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Contact/Lemma43D.integrableOn_t_of_bounded`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Contact/Lemma43D.integrableOn_t_of_bounded` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

hgt, discharged. The fixed-radius slice t ↦ g t r is integrable on (0,T] because it is bounded and (0,T] has finite measure. Φ ≤ 1/2 supplies the bound.

**Theorem 1.2 (integrable On Ioi of support).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Contact/Lemma43D.integrableOn_Ioi_of_support`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Contact/Lemma43D.integrableOn_Ioi_of_support` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

Extending integrability from a bounded window to (0,∞). A profile supported in (0, L] is integrable on Ioi 0 as soon as it is integrable on the window. This is what turns the fixed-window bound into RadialWeightData.radial_bound's Ioi 0 statement.

## References

- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Contact/Lemma43D.integrableOn_Ioi_of_support`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Contact/Lemma43D.integrableOn_t_of_bounded`
- Dependency: [D5/S3/Arith/Lattices/Klartag/Contact/Lemma43C](Lemma43C.md)
- Dependency: [D5/S3/Arith/Lattices/Klartag/Walk/ChainDataInst](../Walk/ChainDataInst.md)
