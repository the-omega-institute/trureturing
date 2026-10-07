# Construction A

## Abstract

Construction A lattices, covolumes and ellipsoid transfer.

Construction A lattices, covolumes and ellipsoid transfer. The results below relate construction a to the stochastic ellipsoid construction.

**Definition 1.1 (red Mod).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Construction/ConstructionA.redMod`

*Formalization.* `D5/S3/Arith/Lattices/Klartag/Construction/ConstructionA.redMod` (`✓ std3`).

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

Coordinatewise reduction ℤⁿ → (ZMod p)ⁿ.

**Definition 1.2 (On Line).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Construction/ConstructionA.OnLine`

*Formalization.* `D5/S3/Arith/Lattices/Klartag/Construction/ConstructionA.OnLine` (`✓ std3`).

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

Construction A with k = 1: the residue v lies on the line C_g = ⟨g⟩.

**Theorem 1.3 (card filter on Line).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Construction/ConstructionA.card_filter_onLine`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Construction/ConstructionA.card_filter_onLine` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The line count. A nonzero residue lies on exactly p - 1 lines ⟨g⟩.

**Theorem 1.4 (sum card filter on Line).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Construction/ConstructionA.sum_card_filter_onLine`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Construction/ConstructionA.sum_card_filter_onLine` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

First-moment lemma (exact form). Summing over *all* g, the total number of incidences between a finite set A of p-indivisible integer points and the lines ⟨g⟩ is exactly (p - 1) * |A|. This is the swap of two finite sums.

**Theorem 1.5 (sum card filter on Line erase).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Construction/ConstructionA.sum_card_filter_onLine_erase`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Construction/ConstructionA.sum_card_filter_onLine_erase` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The g = 0 line carries no p-indivisible point, so the sum over g ≠ 0 is the same.

**Theorem 1.6 (sum card le).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Construction/ConstructionA.sum_card_le`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Construction/ConstructionA.sum_card_le` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The density bound, division-free. p^{n-1} · Σ_{g≠0} (count) ≤ (pⁿ - 1) · |A|, i.e. the average over the pⁿ - 1 nonzero g is at most |A| · p^{1-n}.

**Theorem 1.7 (exists mem not mem).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Construction/ConstructionA.exists_mem_not_mem`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Construction/ConstructionA.exists_mem_not_mem` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The union bound / selection step (1/2 + 1/e < 1): if the two bad sets together miss some element of s, a good g exists.

**Theorem 1.8 (le abs of dvd).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Construction/ConstructionA.le_abs_of_dvd`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Construction/ConstructionA.le_abs_of_dvd` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

A nonzero integer point all of whose coordinates are divisible by p has a coordinate of absolute value at least p. This is why the pℤⁿ term of the first-moment lemma vanishes identically once p exceeds the radius of the support.

**Theorem 1.9 (card erase univ).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Construction/ConstructionA.card_erase_univ`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Construction/ConstructionA.card_erase_univ` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The number of nonzero g is pⁿ - 1.

**Theorem 1.10 (card bad one le).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Construction/ConstructionA.card_bad_one_le`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Construction/ConstructionA.card_bad_one_le` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

Use 1's Markov step (eq. 64), discrete counterpart. The number of lines meeting the finite set A at all is at most (pⁿ-1)·|A|/p^{n-1}.

**Theorem 1.11 (discrete Topology of le).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Construction/ConstructionA.discreteTopology_of_le`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Construction/ConstructionA.discreteTopology_of_le` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

Generic sublattice criterion (absent from Mathlib). If M ≤ L with L a ℤ-lattice and M ⊇ k · L for some k ≠ 0, then M is a ℤ-lattice.

**Definition 1.12 (to Real).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Construction/ConstructionA.toReal`

*Formalization.* `D5/S3/Arith/Lattices/Klartag/Construction/ConstructionA.toReal` (`✓ std3`).

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The ℤ-linear inclusion ℤⁿ ↪ ℝⁿ.

**Definition 1.13 (red Lin).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Construction/ConstructionA.redLin`

*Formalization.* `D5/S3/Arith/Lattices/Klartag/Construction/ConstructionA.redLin` (`✓ std3`).

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

Coordinatewise reduction ℤⁿ → (ZMod p)ⁿ, as a ℤ-linear map.

**Definition 1.14 (line Z).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Construction/ConstructionA.lineZ`

*Formalization.* `D5/S3/Arith/Lattices/Klartag/Construction/ConstructionA.lineZ` (`✓ std3`).

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The p-ary line C_g = ⟨g⟩, as a ℤ-submodule.

**Definition 1.15 (lat Z).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Construction/ConstructionA.latZ`

*Formalization.* `D5/S3/Arith/Lattices/Klartag/Construction/ConstructionA.latZ` (`✓ std3`).

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

Construction A in ℤⁿ: Λ₀(g) = {y ∈ ℤⁿ : y mod p ∈ ⟨g⟩}.

**Theorem 1.16 (smul mem lat Z).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Construction/ConstructionA.smul_mem_latZ`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Construction/ConstructionA.smul_mem_latZ` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

Λ₀(g) contains p·ℤⁿ.

**Definition 1.17 (int Lat).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Construction/ConstructionA.intLat`

*Formalization.* `D5/S3/Arith/Lattices/Klartag/Construction/ConstructionA.intLat` (`✓ std3`).

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The standard integer lattice in ℝⁿ.

**Definition 1.18 (lat R).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Construction/ConstructionA.latR`

*Formalization.* `D5/S3/Arith/Lattices/Klartag/Construction/ConstructionA.latR` (`✓ std3`).

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

Construction A in ℝⁿ: Λ(g) = {x ∈ ℤⁿ : x mod p ∈ ⟨g⟩} ⊆ ℝⁿ.

**Theorem 1.19 (index lat Z).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Construction/ConstructionA.index_latZ`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Construction/ConstructionA.index_latZ` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The index of Construction A in ℤⁿ is p^{n-1}.

**Definition 1.20 (to Real Equiv).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Construction/ConstructionA.toRealEquiv`

*Formalization.* `D5/S3/Arith/Lattices/Klartag/Construction/ConstructionA.toRealEquiv` (`✓ std3`).

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

toReal as a ℤ-linear equivalence onto the standard integer lattice of ℝⁿ.

**Theorem 1.21 (rel Index lat R).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Construction/ConstructionA.relIndex_latR`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Construction/ConstructionA.relIndex_latR` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The relative index of Λ(g) in ℤⁿ ⊆ ℝⁿ is p^{n-1}.

**Definition 1.22 (int Lat Basis).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Construction/ConstructionA.intLatBasis`

*Formalization.* `D5/S3/Arith/Lattices/Klartag/Construction/ConstructionA.intLatBasis` (`✓ std3`).

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

A ℤ-basis of the standard integer lattice of ℝⁿ.

**Theorem 1.23 (covolume lat R).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Construction/ConstructionA.covolume_latR`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Construction/ConstructionA.covolume_latR` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The covolume of Construction A. covol Λ(g) = p^{n-1}.

**Theorem 1.24 (mem lat Z iff on Line).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Construction/ConstructionA.mem_latZ_iff_onLine`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Construction/ConstructionA.mem_latZ_iff_onLine` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

Membership in Construction A is exactly the incidence relation counted above.

## References

- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Construction/ConstructionA.OnLine`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Construction/ConstructionA.card_bad_one_le`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Construction/ConstructionA.card_erase_univ`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Construction/ConstructionA.card_filter_onLine`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Construction/ConstructionA.covolume_latR`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Construction/ConstructionA.discreteTopology_of_le`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Construction/ConstructionA.exists_mem_not_mem`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Construction/ConstructionA.index_latZ`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Construction/ConstructionA.intLat`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Construction/ConstructionA.intLatBasis`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Construction/ConstructionA.latR`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Construction/ConstructionA.latZ`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Construction/ConstructionA.le_abs_of_dvd`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Construction/ConstructionA.lineZ`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Construction/ConstructionA.mem_latZ_iff_onLine`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Construction/ConstructionA.redLin`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Construction/ConstructionA.redMod`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Construction/ConstructionA.relIndex_latR`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Construction/ConstructionA.smul_mem_latZ`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Construction/ConstructionA.sum_card_filter_onLine`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Construction/ConstructionA.sum_card_filter_onLine_erase`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Construction/ConstructionA.sum_card_le`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Construction/ConstructionA.toReal`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Construction/ConstructionA.toRealEquiv`
