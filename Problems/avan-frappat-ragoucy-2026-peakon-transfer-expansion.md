---
slug: avan-frappat-ragoucy-2026-peakon-transfer-expansion
bibkey: avan2026peakonquadratic
doi: 10.1088/1751-8121/ae7683
url: https://arxiv.org/abs/2512.11066v3
triage: theorem
motivation_gids:
  - D5/S3/FluidDynamics/Solitons/CamassaHolmPeakonTransferExpansion.result
---

# The peakon transfer matrices expand in the Hamiltonians h^(k) with explicit universal coefficients

## Problem

J. Avan, L. Frappat and E. Ragoucy, *Quadratic Poisson brackets for the Camassa–Holm peakons*, arXiv:2512.11066v3, J. Phys. A **59**, 245202 (2026), study the two-parameter deformation of the Camassa–Holm peakon Lax matrix.
- Its matrices are A, T and S of Eqs. (2.1)–(2.3), and its Lax matrix is L(z) = S + Λ(z)T + ξ(z)A with ξ² = Λ² + γΛ + 1 (5.18).
- The transfer matrices are τ_m(z) = tr L(z)^m.
- Proposition 5.1 gives their degree-one term in Λ, h^(m) = m tr((T + γA/2)(S + A)^{m−1}) (5.17).

Conjecture 5.2 asserts that τ_m(z) = Σ_j Λ^j Σ a_j(k_1, …, k_j) h^(k_1)⋯h^(k_j), summed over partitions k_1 ≥ ⋯ ≥ k_j of m (5.20), with a_1(m) = 1 and the values a_m(1, …, 1) = 1 and a_{j+1}(m − j, 1, …, 1) = m/(m − j) for 0 ≤ j < m − 1 (5.21). It leaves "the other coefficients … to be determined", and the conclusion calls for a proof. The verbatim statements are in [the literature note](../Library/FluidDynamics/avan2026peakonquadratic.md).

Issue [#16323](https://github.com/the-omega-institute/trureturing/issues/16323) fixes the reading: for every N and m ≥ 1, there are coefficients independent of N and of all parameters with these values such that (5.20) holds. It also preregisters the explicit coefficients a_j(k) = m (j − 1)! / (∏_i k_i · ∏_r e_r!), where e_r counts the parts equal to r.

## Motivation

The expansion expresses every transfer matrix through the single family of Hamiltonians h^(k) of Proposition 5.1. It is the step the source needs for its bi-Hamiltonian analysis of the deformed peakon hierarchy, and the explicit coefficients determine the hierarchy's time evolutions from τ_m without further computation.

## Gap

Issue #16323 records the literature check before any Lean:
- arXiv v3 is the latest version and still states the conjecture;
- the authors' earlier peakon papers (arXiv:2203.13593, 2309.08412), Ragnisco–Bruschi and arXiv:2311.16582 contain no determinant identity of this form;
- web and Zenodo searches return no proof;
- the repository had no peakon entry.

`not-found-in-searched-scope`.

## Route

The proof works with formal power series in t over ℂ.
1. **Triangularity.** B = S + A has (i, j) entry 0 whenever q_i ≤ q_j: the sign cancels when q_i < q_j, and sinh 0 = 0 when q_i = q_j. A block-triangular determinant labelled by the positions gives det(1 − tB) = det(1 − tBᵀ) = 1, without sorting.
2. **Rank two.** With u_i = w_i e^{νq_i/2} and v_i = w_i e^{−νq_i/2}, T = (uvᵀ + vuᵀ)/2, A = (uvᵀ − vuᵀ)/2 and B − Bᵀ = uvᵀ − vuᵀ. So L = B + αuvᵀ + βvuᵀ with α = (Λ + ξ − 1)/2 and β = (Λ − ξ + 1)/2.
3. **The determinant.** The matrix determinant lemma, applied with the explicit resolvent Σ Bⁿtⁿ of 1 − tB, gives det(1 − t(B + a uvᵀ + b vuᵀ)) = 1 − af − bg + ab·d. The case a = −1, b = 1 is Bᵀ, which forces d = f − g. With (5.18):
   det(1 − tL) = 1 − Λ·H(t), with H(t) = Σ_k (h^(k)/k) t^k.
4. **Logarithmic derivative.** Jacobi's formula gives det(1 − tL) · Σ_m τ_m t^{m−1} = −(d/dt) det(1 − tL). A finite geometric sum then gives τ_m = m Σ_{j=1}^m (Λ^j/j) [t^m] H(t)^j.
5. **Regrouping.** The multinomial expansion of [t^m] H^j, grouped by partitions of m with j parts, gives the coefficient m (j − 1)! / (∏ k_i ∏ e_r!). It equals 1 for the single part m and for m ones, and m/(m − j) for (m − j, 1, …, 1).

## Falsifier

The proof would not settle the conjecture if:
- the matrices of the module differed from (2.1)–(2.3), with √(p_i p_j) = w_i w_j and s_ii = 0;
- τ_m or h^(m) differed from tr L^m and (5.17);
- the partition sum differed from (5.20)'s sum over 0 < k_j ≤ ⋯ ≤ k_1 with Σk = m.

The module allows complex ν, complex weights and unsorted positions with coincidences. Each generalizes the source's setting without changing the identity, and positive p_i correspond to w_i = √p_i.

## Evidence

The canonical source is `D5/S3/FluidDynamics/Solitons/CamassaHolmPeakonTransferExpansion.lean` (756 lines).
- It defines `A`, `T`, `S`, `Lambda`, `xi`, `L`, `tau`, `h`, `universalCoeff`, `prescribedValues`, `expansion` and `claim`, and proves `result : claim`.
- It uses Mathlib's block-triangular determinants, `Matrix.det_one_sub_mul_comm`, `Matrix.det_updateRow_sum`, power-series derivatives and coefficients, `Finset.sum_pow`, `Multiset.countPerms` and `Nat.Partition`; it has no frozen D5 dependency.
- It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.
- The escape registration in `Reg/D5/S3/FluidDynamics/Solitons/CamassaHolmPeakonTransferExpansion.lean` reads out the coefficient family of `claim`, and its rejected realization (the zero family) fails at a_1(1) = 1. It is `declared_validated`.

Frozen state: `Golden/Frozen/state/D5/S3/FluidDynamics/Solitons/CamassaHolmPeakonTransferExpansion.lean.json`, statement `sha256:af28d23be4d45567631ba8c592193f5bf3117b379da0bc6dfb657c75ee610c82`.

Declaration statements:
- `result`: `sha256:0c5ecf0ad7774592a98e85cd816ca8fbea500f4af87c4fdb8949235312672a29`;
- `claim`: `sha256:a6e36905fd3ffd555aa7bbb964d44e9de554265e06fafbf939958f83d8c69714`.

## Triage

Tier 1 conjecture of a 2026 paper, preregistered in issue #16323 before any Lean.
`theorem`; resolution `proved`.

| declaration | proof_shape | escape_witness | admission_basis |
| --- | --- | --- | --- |
| result | bind-only | none: the route instantiates pinned Mathlib results (block-triangular determinants, `Matrix.det_one_sub_mul_comm`, `Matrix.det_updateRow_sum`, the power-series derivative and coefficient API, `Finset.sum_pow`, `Nat.multinomial_spec`) and normalizes | open-problem-resolution |
| the triangular, rank-two, resolvent, Jacobi, logarithmic-extraction, partition and coefficient helpers (private) | bind-only (consumed on the proof path of `result`) | none | consumed helpers |

Every other declaration is a definition used by a public statement or a compiler-generated equation or proof on the proof path of `result`. The bind-only form is admitted under the open-problem-resolution basis of CLAUDE.md §3.2; no escape witness is claimed. The utility is `none`. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** Conjecture 5.2 holds for every N and m ≥ 1. All its coefficients are determined, a_j(k_1, …, k_j) = m (j − 1)! / (∏_i k_i · ∏_r e_r!), and they are independent of N, the positions, the weights, ν, γ and z.

**Established inside the proof.** The characteristic polynomial of the deformed Lax matrix is affine in Λ: det(1 − tL(z)) = 1 − Λ(z) Σ_k (h^(k)/k) t^k, with the same h^(k) for every z. Equivalently, Σ_m τ_m t^{m−1} = ΛH′(t) / (1 − ΛH(t)), and the expansion is the coefficient extraction of −log(1 − ΛH(t)).

**Argued, not formalized.**
- (S + A)^N = 0 because S + A is strictly triangular after ordering the positions, so h^(k) = 0 for k > N. So at most the first N Hamiltonians h^(1), …, h^(N) are needed, and every τ_m with m > N is a polynomial in them; their functional independence is not claimed. A numerical check (NumPy, N = 2, 3, 5, complex weights and parameters) gives |h^(k)| = 0 for k > N and agreement of det(1 − tL) with 1 − ΛH(t) to 2·10⁻¹⁵.
- The Hamiltonians are coefficients of the spectral curve: comparing coefficients of t^k gives h^(k) = (−1)^{k+1} k e_k(L(z))/Λ(z) for every z with Λ(z) ≠ 0, where e_k is the k-th elementary symmetric function of the eigenvalues of L(z). This answers the source's request for "an explicit expression for the Hamiltonians h^(m), going beyond the expression (5.17)" in terms of the principal minors of L(z).

**Open.**
- The bi-Hamiltonian and Poisson-commutativity statements of the source are not addressed.
- Uniqueness of the coefficients is not claimed. For a fixed N, partitions with a part larger than N multiply a vanishing h^(k), so their coefficients are determined only by the universality over all N.

**Effect on the paper.** Conjecture 5.2 is a theorem, and the undetermined coefficients of (5.20) are given in closed form. The time evolutions that §5.3 derives from τ_m can be written with these coefficients.

## ASSUMED-UNVERIFIED

The bounded literature check does not establish exhaustive worldwide novelty or priority. The statements in "Argued, not formalized" are not formalized.
