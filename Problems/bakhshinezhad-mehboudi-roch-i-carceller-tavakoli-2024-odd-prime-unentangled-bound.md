---
slug: bakhshinezhad-mehboudi-roch-i-carceller-tavakoli-2024-odd-prime-unentangled-bound
bibkey: bakhshinezhad2024scalable
doi: 10.1103/PRXQuantum.5.020319
url: https://arxiv.org/abs/2401.00796v2
triage: theorem
motivation_gids:
  - D5/S3/QuantumBounds/UnentangledOddPrimeCommunication.result
---

# Without shared entanglement the odd-prime communication task succeeds with probability at most 2/(d + 1)

## Problem

P. Bakhshinezhad, M. Mehboudi, C. Roch i Carceller and A. Tavakoli, *Scalable entanglement certification via quantum communication*, PRX Quantum 5, 020319 (2024), arXiv:2401.00796v2, certify entanglement through a symmetric prepare-and-measure task.
- **The task.** For an odd prime d, Alice and Bob receive x, y ∈ {0, …, d − 1}² and send d-dimensional messages; Charlie receives z ∈ {0, …, d}, may measure the two messages jointly, and outputs c. He wins when c = w_z, with w_z = x₁ + y₁ − 2z(x₀ − y₀) for z ≠ d and w_d = x₀ − y₀ mod d (Eq. (27)), and R_d is the average success probability (Eq. (28)).
- **Without shared entanglement.** p(c | x, y, z) = tr(α_x ⊗ β_y M_c|z) (Eq. (19)); sending x₀ and y₀ achieves R_d = 2/(d + 1).
- **The conjecture.** After see-saw searches at d = 3 and d = 5: "Conjecture 1. For every odd prime d, the largest average success probability achievable in a quantum model without shared entanglement is R_d = 2/(d + 1). (29)" With shared entanglement and product measurements R_d = 1, so the bound would certify every state with a non-trivial maximally entangled fraction.

The verbatim statements are in [the literature note](../Library/QuantumBounds/bakhshinezhad2024scalable.md).

Issue [#16770](https://github.com/the-omega-institute/trureturing/issues/16770) fixes the reading: messages are d × d density matrices, Charlie's measurement for each z is any d-outcome POVM on the joint d²-dimensional space, and shared classical randomness is a finite mixture of strategies with one common index. The conjecture is proved for every odd prime d.

## Motivation

Roch i Carceller and Tavakoli (arXiv:2410.15388, Phys. Rev. Lett. 134, 120203) show that bound entangled states violate this bound for d = 3, 5, 7, but could prove the bound itself only for those three dimensions, by semidefinite relaxations. Márton–Bene–Vértesi (arXiv:2502.08293v2) describe the witness as generalizing to all odd primes "modulo the conjectured separable bound for d > 7". The bound for every odd prime makes the witness valid in every odd prime dimension.

## Gap

Issue #16770 records the literature check before any Lean:
- arXiv v1–v2; v2 and the journal version state Conjecture 1;
- Roch i Carceller–Tavakoli prove it for d = 3, 5, 7 only; Márton–Bene–Vértesi (revised October 2025) still call it conjectured for d > 7;
- the full texts of the citing works with arXiv identifiers (17 citing works of arXiv:2401.00796 and 6 of arXiv:2410.15388 listed by Semantic Scholar) were scanned; none proves the bound for all odd primes;
- the repository had no entry for the paper.

`not-found-in-searched-scope`.

## Route

Write χ(t) = e^{2πit/d} and F = ZMod d.
1. **Character expansion.** With w_z = a_z(x) + b_z(y), the indicator of c = w_z is d⁻¹ Σ_k χ(k(w_z − c)). The k = 0 term contributes exactly 1/d, so R_d = 1/d + (d⁵(d + 1))⁻¹ Σ_z Σ_{k≠0} Re tr[(A_{zk} ⊗ B_{zk})C_{zk}], with A_{zk}, B_{zk} the Fourier modes of Alice's and Bob's encodings and C_{zk} = Σ_c χ(−kc)M_c|z.
2. **The measurement.** ‖C_{zk}‖²_F ≤ d² for every POVM, because tr(M_c M_{c′}) ≥ 0 and Σ_c M_c = 1.
3. **Cauchy–Schwarz.** Re tr[(A ⊗ B)C] ≤ d‖A‖_F‖B‖_F ≤ (d/2)(‖A‖²_F + ‖B‖²_F).
4. **Slopes and Parseval.** Since 2 and every nonzero slope are invertible in F, the frequencies of the modes (z, k ≠ 0) are exactly the nonzero vectors of F², each once. Parseval with the constant mode removed gives Σ_{z,k≠0} ‖A_{zk}‖²_F = d² Σ_x ‖α_x‖²_F − ‖Σ_x α_x‖²_F ≤ d⁴ − d³, using purity and ‖S‖²_F ≥ (tr S)²/d.
5. **The bound.** R_d ≤ 1/d + d(d⁴ − d³)/(d⁵(d + 1)) = 2/(d + 1); mixtures obey it by linearity.
6. **Attainment.** Alice and Bob send |x₀⟩ and |y₀⟩; Charlie measures r − s in the computational basis for z = d and outputs uniformly otherwise.

## Falsifier

The proof would not settle the conjecture if the module's strategies were narrower than the source's model without shared entanglement, if its score differed from Eq. (28), or if the bound were not attained. The module allows arbitrary density matrices and arbitrary joint POVMs (entangled measurements included), finite mixtures with shared randomness, the source's winning functions and normalization, and exhibits a strategy with score exactly 2/(d + 1).

## Evidence

The canonical source is `D5/S3/QuantumBounds/UnentangledOddPrimeCommunication.lean` (632 lines).
- It defines `tensor`, `phase`, `win`, `Valid`, `score`, `mixtureScore` and `claim`, and proves `result : claim` for every odd prime d.
- It uses the frozen `CartesianVariance.trace_product_cauchy` and `frobSq_eq_sum`, `RHLinalg.frobSq`, `RHLinalg.trace_mul_nonneg_of_posSemidef`, `ProjectionProbabilityFlow.trace_hermitian_product_real`, `GurvitsBarnumBall.psd_trace_sq` (made public for this settlement), `FullBispectrumStability.cyclic_parseval` and `SparseGeneratorFamily.char_sum`, with Mathlib's `ZMod.stdAddChar`, `Matrix.trace_kronecker` and `finProdFinEquiv`.
- It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.
- The escape registration in `Reg/D5/S3/QuantumBounds/UnentangledOddPrimeCommunication.lean` reads out the bound d ↦ 2/(d + 1) of the fixed-strategy clause of `claim`. Its rejected realization, d ↦ 1/(d + 1), fails at d = 3, where the attaining strategy of `result` scores 1/2 > 1/4. It is `declared_validated`.

Frozen state: `Golden/Frozen/state/D5/S3/QuantumBounds/UnentangledOddPrimeCommunication.lean.json`, statement `sha256:5d5b48b9af9eeb99ee86e41c69c32b3dc1bcd057b5b4b0d918fa955336c4c323`.

Declaration statements:
- `result`: `sha256:8d8a4cf6e96ccc82fcee57b2cf36c862a556407d8fc3af7a70556979544efafc`;
- `claim`: `sha256:013f22e6ba35e5b13b3b6a9f801a5e9deece2005c905521527ab903a07f7160c`.

## Triage

Tier 1 conjecture of a 2024 paper, preregistered in issue #16770 before any Lean.
`theorem`; resolution `proved`.

| declaration | proof_shape | escape_witness | admission_basis |
| --- | --- | --- | --- |
| result | bind-only | none: after inlining, the character expansion, the POVM and Cauchy–Schwarz bounds, the slope bijection, Parseval and the attaining strategy are instantiations of frozen D5 and pinned Mathlib results followed by normalization | open-problem-resolution |
| the tensor, character, Parseval, slope, energy, score and attainment helpers (private) | bind-only (consumed on the proof path of `result`) | none | consumed helpers |

Every other declaration is a definition used by a public statement or a compiler-generated proof on the proof path of `result`. The bind-only form is admitted under the open-problem-resolution basis of CLAUDE.md §3.2; no escape witness is claimed. The utility is `none`. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** for every odd prime d, every quantum strategy without shared entanglement, with arbitrary joint measurements and shared classical randomness, has R_d ≤ 2/(d + 1), and 2/(d + 1) is attained.

**Computed, not formalized** (orchestrator, NumPy, 14 October 2026): on random mixed states and POVMs at d = 3 and d = 5 the character expansion of step 1 agrees with the direct score to 4 × 10⁻¹⁶; random instances satisfy the bounds of steps 2 and 4 at d = 3, 5, 7; the attaining strategy scores exactly 0.5 and 1/3 at d = 3 and d = 5; random pure-state strategies score at most 0.342 (d = 3) and 0.201 (d = 5).

**Argued, not formalized.**
- The mechanism: the sum of the d² unit-trace states of an encoding has trace d², so by Cauchy–Schwarz its squared Frobenius norm is at least d⁴/d = d³, and removing the constant Fourier mode subtracts at least d³ from the encoding's energy (step 4). Each nonzero Fourier mode of a measurement has squared Frobenius norm at most d² (step 2). In the classical attaining strategy the encoding sums to d·1 and saturates the encoding energy bound, and the measurement bound is saturated on the contributing z = none modes; for z = some t the uniform measurement has zero nonzero modes.
- Oddness makes 2 invertible in ZMod d, and primality makes every nonzero slope invertible; for odd d > 1 the latter holds exactly when d is prime.
- With the bound established, every state whose maximally entangled fraction EF_d exceeds 1/d admits a quantum model with R_d = 1/(d + 1) + d·EF_d/(d + 1) > 2/(d + 1) by the source's Proposition 3 (Eq. (30)), so the witness certifies entanglement in every odd prime dimension.

**Open.**
- The largest score achievable with bound entangled states. Roch i Carceller–Tavakoli (arXiv:2410.15388, Table I) find 0.5387, 0.3862 and 0.2931 at d = 3, 5, 7 by numerical search, without an optimality proof, and do not treat d > 7.
- Analogous bounds for composite d, where the slope bijection fails.

**Effect on the paper.** Conjecture 1 holds for every odd prime d, so the scalable entanglement witness of §VI is valid in every odd prime dimension, not only for d = 3, 5, 7.

## ASSUMED-UNVERIFIED

The bounded literature check does not establish exhaustive worldwide novelty or priority. The statements in "Computed, not formalized" and "Argued, not formalized" are not formalized.
