# Profile

## Abstract

Contact profile counts and accumulated projection dimension.

Contact profile counts and accumulated projection dimension. The results below relate profile to the stochastic ellipsoid construction.

**Definition 1.1 (Phi C).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Contact/Profile.PhiC`

*Formalization.* `D5/S3/Arith/Lattices/Klartag/Contact/Profile.PhiC` (`✓ std3`).

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

Φ with the paper's Φ(0) = 1/2 restored. Phi 0 = min (1/2) 0 = 0 in Lean.

**Theorem 1.2 (Phi antitone On).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Contact/Profile.Phi_antitoneOn`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Contact/Profile.Phi_antitoneOn` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

Φ is antitone on (0,∞): both e^{−y²/2} and 1/y decrease.

**Definition 1.3 (y Of).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Contact/Profile.yOf`

*Formalization.* `D5/S3/Arith/Lattices/Klartag/Contact/Profile.yOf` (`✓ std3`).

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

y(r) = t^{−1/2}·(a₀ − r^{−2}), the paper's substitution variable (p. 20).

**Theorem 1.4 (y Of monotone On).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Contact/Profile.yOf_monotoneOn`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Contact/Profile.yOf_monotoneOn` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

y(·) is monotone on (0,∞) — and only there; it is even in r.

**Definition 1.5 (profile).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Contact/Profile.profile`

*Formalization.* `D5/S3/Arith/Lattices/Klartag/Contact/Profile.profile` (`✓ std3`).

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

Klartag's Lemma 4.3 integrand, concretely. profile a₀ α W n t r: * 0 beyond the window W — the shell R_t is bounded (eq. 55), and this is what makes the profile integrable; * 1/2 when the inward-shifted, scaled radius α·(r − √n/2) is non-positive — below the shell the weight is Φ(0) = 1/2, and this branch is what keeps the profile globally antitone despite y(·) being even in r; * Φ(y(α·(r − √n/2))) otherwise — the weight at the cube's inner radius.

**Theorem 1.6 (profile antitone).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Contact/Profile.profile_antitone`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Contact/Profile.profile_antitone` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The profile is globally antitone — the hypothesis Lemma43B.dom_of_antitone needs.

**Theorem 1.7 (measurable profile uncurry).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Contact/Profile.measurable_profile_uncurry`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Contact/Profile.measurable_profile_uncurry` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

hgmeas, discharged. (t, r) ↦ profile a₀ α W n t r is jointly measurable: it is a two-branch if over measurable sets, with PhiC ∘ y(·) measurable on the last branch.

**Theorem 1.8 (measurable profile time).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Contact/Profile.measurable_profile_time`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Contact/Profile.measurable_profile_time` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

Fixing the radius leaves a measurable function of t.

**Theorem 1.9 (measurable profile radius).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Contact/Profile.measurable_profile_radius`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Contact/Profile.measurable_profile_radius` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

Fixing the time leaves a measurable function of r.

**Theorem 1.10 (integrable On profile time).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Contact/Profile.integrableOn_profile_time`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Contact/Profile.integrableOn_profile_time` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

hgt, at the concrete profile. Bounded by Φ ≤ 1/2 on a finite-measure interval.

## References

- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Contact/Profile.PhiC`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Contact/Profile.Phi_antitoneOn`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Contact/Profile.integrableOn_profile_time`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Contact/Profile.measurable_profile_radius`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Contact/Profile.measurable_profile_time`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Contact/Profile.measurable_profile_uncurry`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Contact/Profile.profile`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Contact/Profile.profile_antitone`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Contact/Profile.yOf`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Contact/Profile.yOf_monotoneOn`
- Dependency: [D5/S3/Arith/Lattices/Klartag/Contact/Lemma43D](Lemma43D.md)
