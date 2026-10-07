# Chain

## Abstract

Gaussian matrix walk, filtration and stopped increments.

Gaussian matrix walk, filtration and stopped increments. The results below relate chain to the stochastic ellipsoid construction.

**Definition 1.1 (k Set).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Walk/Chain.kSet`

*Formalization.* `D5/S3/Arith/Lattices/Klartag/Walk/Chain.kSet` (`✓ std3`).

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

kSet q W = {A | ∀ i ∈ W, 1 ≤ ⟪A, q i⟫}. With q x = x ⊗ x this is Klartag's set of L-free matrices (p. 6, eq. 9): E_A = {x | ⟪A x, x⟫ < 1} misses every x with q x a constraint.

**Theorem 1.2 (q ne zero of nonempty).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Walk/Chain.q_ne_zero_of_nonempty`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Walk/Chain.q_ne_zero_of_nonempty` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

If K_L is nonempty then no constraint vector vanishes (⟪A, 0⟫ = 0 < 1).

**Definition 1.3 (Is Proj On).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Walk/Chain.IsProjOn`

*Formalization.* `D5/S3/Arith/Lattices/Klartag/Walk/Chain.IsProjOn` (`✓ std3`).

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

p is *the* projection of u onto K: p ∈ K and K lies in the half-space through p orthogonal to u - p.

**Theorem 1.4 (eq).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Walk/Chain.eq`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Walk/Chain.eq` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The projection onto a convex set is unique.

**Definition 1.5 (free Sub).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Walk/Chain.freeSub`

*Formalization.* `D5/S3/Arith/Lattices/Klartag/Walk/Chain.freeSub` (`✓ std3`).

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The free subspace F(C) = {B | ∀ i ∈ C, ⟪B, q i⟫ = 0} (Klartag eq. 13).

**Theorem 1.6 (free Sub eq orthogonal).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Walk/Chain.freeSub_eq_orthogonal`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Walk/Chain.freeSub_eq_orthogonal` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

F(C) is the orthogonal complement of the span of the active constraints.

**Theorem 1.7 (finrank free Sub ge).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Walk/Chain.finrank_freeSub_ge`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Walk/Chain.finrank_freeSub_ge` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

dim F(C) ≥ dim E - |q(C)|: Klartag's N_t ≥ n(n+1)/2 - |∂E_t ∩ L|/2 (p. 16). Counting the *image* q '' C rather than C itself is what supplies the paper's factor 1/2, since q x = x ⊗ x = q (-x) identifies the antipodal pairs of contact points.

**Theorem 1.8 (finrank free Sub ge card).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Walk/Chain.finrank_freeSub_ge_card`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Walk/Chain.finrank_freeSub_ge_card` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The crude form of finrank_freeSub_ge, without the antipodal saving.

**Definition 1.9 (violated).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Walk/Chain.violated`

*Formalization.* `D5/S3/Arith/Lattices/Klartag/Walk/Chain.violated` (`✓ std3`).

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The window constraints broken by A'.

**Definition 1.10 (lift).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Walk/Chain.lift`

*Formalization.* `D5/S3/Arith/Lattices/Klartag/Walk/Chain.lift` (`✓ std3`).

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The one-sided lift back into K_L: move along the broken constraints only, each by exactly the amount that makes it tight.

**Theorem 1.11 (lift mem k Set).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Walk/Chain.lift_mem_kSet`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Walk/Chain.lift_mem_kSet` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The lift lands in K_L. The only structural input is non-negative correlation of the constraint vectors, 0 ≤ ⟪q i, q j⟫ — true for q x = x ⊗ x, where it is (x ⬝ᵥ y)² ≥ 0.

**Definition 1.12 (step To).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Walk/Chain.stepTo`

*Formalization.* `D5/S3/Arith/Lattices/Klartag/Walk/Chain.stepTo` (`✓ std3`).

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

One step of the chain: Gaussian increment inside the free subspace, then the lift, then the newly broken constraints are adjoined to the active set.

**Definition 1.13 (chain).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Walk/Chain.chain`

*Formalization.* `D5/S3/Arith/Lattices/Klartag/Walk/Chain.chain` (`✓ std3`).

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The chain (A_k, C_k), driven by an arbitrary sequence ξ. Klartag's Proposition 2.3.

**Theorem 1.14 (chain fst mem k Set).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Walk/Chain.chain_fst_mem_kSet`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Walk/Chain.chain_fst_mem_kSet` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

A_k ∈ K_L for every k (Klartag Proposition 2.3(C), the L-free half).

**Theorem 1.15 (chain snd subset succ).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Walk/Chain.chain_snd_subset_succ`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Walk/Chain.chain_snd_subset_succ` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The active set only grows (Klartag Proposition 2.3(D)).

**Definition 1.16 (free Dim).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Walk/Chain.freeDim`

*Formalization.* `D5/S3/Arith/Lattices/Klartag/Walk/Chain.freeDim` (`✓ std3`).

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

N_k = dim F(C_k), Klartag's N_t (p. 13, eq. 39).

**Definition 1.17 (new Active).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Walk/Chain.newActive`

*Formalization.* `D5/S3/Arith/Lattices/Klartag/Walk/Chain.newActive` (`✓ std3`).

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

V_{k+1}: the constraints newly broken at step k.

**Theorem 1.18 (violated disjoint).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Walk/Chain.violated_disjoint`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Walk/Chain.violated_disjoint` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

A step breaks no already-active constraint.

**Theorem 1.19 (card chain snd succ).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Walk/Chain.card_chain_snd_succ`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Walk/Chain.card_chain_snd_succ` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The active set grows by exactly the size of the new block.

**Theorem 1.20 (sum card new Active).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Walk/Chain.sum_card_newActive`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Walk/Chain.sum_card_newActive` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

∑_{k<m} |V_k| = |C_m| — the number of terms in the discretisation-error sum.

**Theorem 1.21 (measurable Set filter eq).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Walk/Chain.measurableSet_filter_eq`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Walk/Chain.measurableSet_filter_eq` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

A Finset-valued filter of measurable predicates is measurable.

**Theorem 1.22 (lift eq sum window).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Walk/Chain.lift_eq_sum_window`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Walk/Chain.lift_eq_sum_window` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The lift, written as a sum over the whole window: this is the form measurability uses.

**Theorem 1.23 (measurable chain).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Walk/Chain.measurable_chain`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Walk/Chain.measurable_chain` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

Adaptedness. If ξ k is m (k+1)-measurable along a monotone family of σ-algebras, then (A_k, C_k) is m k-measurable — Klartag Proposition 2.3's "adapted to the filtration".

**Theorem 1.24 (measurable chain fst).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Walk/Chain.measurable_chain_fst`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Walk/Chain.measurable_chain_fst` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

A_k is measurable.

**Theorem 1.25 (measurable Set mem active).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Walk/Chain.measurableSet_mem_active`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Walk/Chain.measurableSet_mem_active` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

{ω | i ∈ C_k ω} is measurable — the form the contact-count expectation E |C_N| = ∑_i P(i ∈ C_N) consumes.

## References

- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Walk/Chain.IsProjOn`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Walk/Chain.card_chain_snd_succ`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Walk/Chain.chain`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Walk/Chain.chain_fst_mem_kSet`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Walk/Chain.chain_snd_subset_succ`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Walk/Chain.eq`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Walk/Chain.finrank_freeSub_ge`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Walk/Chain.finrank_freeSub_ge_card`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Walk/Chain.freeDim`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Walk/Chain.freeSub`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Walk/Chain.freeSub_eq_orthogonal`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Walk/Chain.kSet`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Walk/Chain.lift`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Walk/Chain.lift_eq_sum_window`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Walk/Chain.lift_mem_kSet`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Walk/Chain.measurableSet_filter_eq`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Walk/Chain.measurableSet_mem_active`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Walk/Chain.measurable_chain`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Walk/Chain.measurable_chain_fst`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Walk/Chain.newActive`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Walk/Chain.q_ne_zero_of_nonempty`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Walk/Chain.stepTo`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Walk/Chain.sum_card_newActive`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Walk/Chain.violated`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Walk/Chain.violated_disjoint`
