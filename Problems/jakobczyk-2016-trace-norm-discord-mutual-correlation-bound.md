---
slug: jakobczyk-2016-trace-norm-discord-mutual-correlation-bound
bibkey: jakobczyk2016maximalmutual
doi: null
url: https://arxiv.org/abs/1607.06585v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Information/TraceNormDiscordMutualCorrelationBound.result
---

# Maximal mutual correlation dominates the trace-norm geometric discord of two qubits

## Problem

L. Jakóbczyk, *Maximal mutual correlation: an algebraic measure of correlations in bipartite quantum systems*, arXiv:1607.06585v1, abstract:

> In the  states containing some quantum correlations, maximal mutual correlation is always greater or equal to geometric measure of quantum discord. This relation is proved to be valid in the class of Bell - diagonal states and it is conjectured that  is also true for general two - qubit states.

The quantities are defined as follows:
- **Trace-norm geometric discord:** D₁(ρ) = min over projective measurements 𝒫 on A of ‖ρ − 𝒫(ρ)‖₁, where 𝒫(ρ) = Σ_k (P_k ⊗ I) ρ (P_k ⊗ I).
- **Maximal mutual correlation:** C_M(ρ) is the supremum of |ω(ab) − ω(a)ω(b)| over local a, b of operator norm 1.

The definitions are quoted in [the literature note](../Library/QuantumContext/jakobczyk2016maximalmutual.md); C_M is the quantity of the companion settlement `D5/S3/Quantum/Information/GeometricDiscordMutualCorrelationBound`.

Issue [#19706](https://github.com/the-omega-institute/trureturing/issues/19706) fixes the reading: for every two-qubit density matrix ρ, D₁(ρ) ≤ C_M(ρ). This is proved.

## Motivation

The source proposes C_M as an algebraic measure of correlations. It argues that C_M bounds quantum discord from above, so that discord is the quantum part of the correlations that C_M measures. The companion question for the Hilbert–Schmidt discord, √D_G ≤ C_M, was settled in the repository by #19777. The source uses the trace-norm discord D₁ as its discord measure.

## Gap

The literature check before any Lean is recorded in #19706:
- arXiv:1607.06585 has only v1;
- OpenAlex and INSPIRE list no citing work;
- Crossref finds no journal version;
- the related works checked for the companion (#19704), including arXiv:1902.07297, do not compare D₁ with C_M;
- the repository had no record.

`not-found-in-searched-scope`.

## Route

Write x for the Bloch vector of A, T for the correlation matrix, and Q = T − x yᵀ for the connected correlation matrix.
1. **Measurement.** Measure A along a unit u ∥ x (any u if x = 0). The disturbance δ = ρ − 𝒫(ρ) equals ¼ Σ_ij (PQ)_ij σ_i ⊗ σ_j with P = I − uuᵀ.
2. **Rotation in the plane.** Rotate an orthonormal pair (v, w) of u^⊥ so that a = Qᵀv′ and b = Qᵀw′ are orthogonal. Then δ = ¼ ((v′·σ) ⊗ (a·σ) + (w′·σ) ⊗ (b·σ)).
3. **The two terms.** They commute, and their squares are |a|² I and |b|² I.
4. **Trace norm.** The positive square root of δ² is explicit, so ‖δ‖₁ = max(|a|, |b|).
5. **Comparison.** For unit c = v′ and d = a/|a|, the covariance of c·σ ⊗ I and I ⊗ d·σ is |a|, and likewise for b. Hence C_M ≥ max(|a|, |b|) ≥ D₁.

## Falsifier

The proof would not settle the conjecture if the module's D₁ or C_M differed from the source's. The module:
- takes D₁ as the infimum over all orthonormal bases of ℂ² (the columns of U ∈ U(2)) of the trace norm of ρ − 𝒫_U(ρ), with the source's 𝒫;
- uses the companion settlement's C_M, a supremum over 2 × 2 local operators of operator norm 1;
- quantifies over all positive semidefinite ρ of trace one.

## Evidence

The canonical source is `D5/S3/Quantum/Information/TraceNormDiscordMutualCorrelationBound.lean` (402 lines).
- **Proof.** It proves `result : claim`.
- **Axioms.** It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.

Frozen state: `Golden/Frozen/state/D5/S3/Quantum/Information/TraceNormDiscordMutualCorrelationBound.lean.json`, statement `sha256:92f535fc5d24c7b228aefc6c01ef7322b89781ae802add6fade1950e590e3ebf`.

Declaration statements:
- `result`: `sha256:263ca98fe1592e8d4936e677d43e6e9a5f29b83f13287e35bfa2b54d9c345bc9`;
- `claim`: `sha256:26b2181f9e309d4dea7f2fa4c4354fce7c48a35c41d93b748d4c4a6d43390a7e`.

## Triage

Tier 1 conjecture of a 2016 paper, preregistered in issue #19706 before any Lean.
`theorem`; resolution `proved`.

The module is admitted under the open-problem-resolution basis of CLAUDE.md §3.2; the per-declaration proof shapes are listed in the delivery PR. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** for every two-qubit density matrix ρ, D₁(ρ) ≤ C_M(ρ).

**Computed, not formalized** (orchestrator, numpy, recorded in #19706):
- over 2000 random states of ranks 1–4, the trace norm of the disturbance along u equals the largest singular value of PQ to 5.6·10⁻¹⁶;
- with 60 sampled further directions, the smallest value found never exceeds ‖Q‖_op.

**Argued, not formalized.**
- *Mechanism.* After the measurement along the Bloch vector of A, the disturbance is a sum of two commuting local Pauli products. Its trace norm is therefore the larger of their two weights, and each weight is witnessed in C_M by one pair of local spin observables.
- *Comparison with the Hilbert–Schmidt case.* The Hilbert–Schmidt version (#19777) bounds D_G by half the sum of the two squared weights, each at most C_M². The trace-norm version keeps only the larger weight, so the same witnesses give the bound without the square root.
- *Effect on the paper.* The inequality C_M ≥ D₁, which the source proves for Bell-diagonal states, holds for all two-qubit states.

## ASSUMED-UNVERIFIED

The bounded literature check does not establish exhaustive worldwide novelty or priority. The statements in "Computed, not formalized" and "Argued, not formalized" are not formalized.
