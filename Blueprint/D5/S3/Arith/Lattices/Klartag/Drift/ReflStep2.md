# Refl Step2

## Abstract

Second order log determinant bounds and accumulated drift.

Second order log determinant bounds and accumulated drift. The results below relate refl step2 to the stochastic ellipsoid construction.

**Definition 1.1 (refl Step2).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Drift/ReflStep2.reflStep2`

*Formalization.* `D5/S3/Arith/Lattices/Klartag/Drift/ReflStep2.reflStep2` (`✓ std3`).

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The reflected step, *defined* through the past.

**Theorem 1.2 (refl Step2 eq refl Step).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Drift/ReflStep2.reflStep2_eq_reflStep`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Drift/ReflStep2.reflStep2_eq_reflStep` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The bridge. Fresh definition on the left; the frozen reflStep is one delta step away.

**Theorem 1.3 (refl Of past eq refl Step).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Drift/ReflStep2.reflOf_past_eq_reflStep`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Drift/ReflStep2.reflOf_past_eq_reflStep` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The same at an index j < k, against the past truncated at k.

## References

- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Drift/ReflStep2.reflOf_past_eq_reflStep`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Drift/ReflStep2.reflStep2`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Drift/ReflStep2.reflStep2_eq_reflStep`
- Dependency: [D5/S3/Arith/Lattices/Klartag/Construction/LiftBound](../Construction/LiftBound.md)
