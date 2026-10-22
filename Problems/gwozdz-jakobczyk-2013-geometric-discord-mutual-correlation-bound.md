---
slug: gwozdz-jakobczyk-2013-geometric-discord-mutual-correlation-bound
bibkey: gwozdz2014discordspontaneous
doi: 10.1007/s11128-013-0639-0
url: https://arxiv.org/abs/1306.0130v2
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Information/GeometricDiscordMutualCorrelationBound.result
---

# Maximal mutual correlation dominates the square root of geometric discord for all two-qubit states

## Problem

M. Gwóźdź and L. Jakóbczyk, *Spontaneous emission can locally create quantum discord out of classical correlations*, arXiv:1306.0130v2, Quantum Inf. Process. 13 (2014) 171–183, Section II:

> C_{M}(\ro)\geq \sqrt{D_{G}^{A}(\ro)}\geq N(\ro).

> The second inequality was shown in Ref. \cite{Adesso} whereas the first one can be proved analytically for Bell-diagonal states and numerical simulations suggest that it is valid for all mixed two-qubit states \cite{J}.

D_G^A is the normalized one-sided geometric discord, d/(d − 1) times the least squared Hilbert–Schmidt distance between ρ and its image under a projective measurement of A. C_M is the maximal mutual correlation, the supremum of |ω_ρ(ab) − ω_ρ(a) ω_ρ(b)| over local elements of norm 1. Both definitions are quoted in [the literature note](../Library/QuantumContext/gwozdz2014discordspontaneous.md).

Issue [#19704](https://github.com/the-omega-institute/trureturing/issues/19704) fixes the reading: for every two-qubit density matrix ρ, √(D_G^A(ρ)) ≤ C_M(ρ). The conjecture is proved.

## Motivation

The source uses C_M as a measure of total correlations and D_G^A as a measure of quantum correlations. The first inequality states that C_M sees at least as much as the geometric discord, which the source proves for Bell-diagonal states and supports numerically otherwise. For pure states the three quantities C_M, √D_G^A and the negativity N agree.

## Gap

The literature check before any Lean is recorded in #19704:
- arXiv:1306.0130 has v1 and v2, and v2 keeps the statement;
- Ref. [23] appeared as arXiv:1607.06585, which treats the trace-norm discord D₁ and leaves its own comparison as a conjecture, recorded as #19706;
- the search seat reports that the citing works and related papers, including arXiv:1902.07297, give no settlement;
- the repository had no record.

`not-found-in-searched-scope`.

## Route

Write x_i = tr(ρ σ_i ⊗ I), y_j = tr(ρ I ⊗ σ_j), T_ij = tr(ρ σ_i ⊗ σ_j) and Q = T − x yᵀ.
1. **Measurement disturbance.** Measure A along a unit u parallel to x (any u if x = 0), and let P = I − uuᵀ. The measurement keeps the components of the Bloch expansion along u and removes the others. The disturbance is δ = ¼ Σ_ij (PT)_ij σ_i ⊗ σ_j, so ‖δ‖₂² = ‖PT‖_F²/4. Since Px = 0, PT = PQ.
2. **Discord bound.** D_G^A(ρ) ≤ 2‖δ‖₂² = ‖PQ‖_F²/2 = (‖Qᵀv‖² + ‖Qᵀw‖²)/2 for an orthonormal completion u, v, w.
3. **Correlation witnesses.** For real unit vectors c and d, the operators c·σ and d·σ have operator norm 1, and the covariance of c·σ ⊗ I and I ⊗ d·σ is cᵀ Q d. Hence C_M ≥ ‖Qᵀv‖ and C_M ≥ ‖Qᵀw‖.
4. **Conclusion.** D_G^A(ρ) ≤ C_M(ρ)², and both sides are nonnegative.

## Falsifier

The proof would not settle the conjecture if the module's quantities differed from the source's. The module:
- takes the minimum over all projective measurements of A, parametrized by the unitary basis U, with the normalization d/(d − 1) = 2 and ‖m‖₂² = tr(m m*);
- takes the supremum over all 2×2 complex matrices a, b of operator norm 1, placed as a ⊗ I and I ⊗ b;
- quantifies over every positive semidefinite trace-one 4×4 matrix.

## Evidence

The canonical source is `D5/S3/Quantum/Information/GeometricDiscordMutualCorrelationBound.lean` (404 lines).
- **Proof.** It proves `result : claim`.
- **Axioms.** It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.
- **Registration.** The §3.9 registration is `Reg/D5/S3/Quantum/Information/GeometricDiscordMutualCorrelationBound.lean`.

Frozen state: `Golden/Frozen/state/D5/S3/Quantum/Information/GeometricDiscordMutualCorrelationBound.lean.json`, statement `sha256:41717f8d19e81c057aa9f53026ccc732eedc92c3728427dbc0f3cec533c3d1e5`.

Declaration statements:
- `result`: `sha256:e02db0e273c24443c3f5cbea9c3be9b87ea0719662d3f7e7942cbc0652e80846`;
- `claim`: `sha256:ea36b19938e594f5f1ad419e6efe314e3dc2239697edf0f820e0d33fa5175a40`.

## Triage

Tier 1 conjecture of a 2013 paper, preregistered in issue #19704 before any Lean.
`theorem`; resolution `proved`.

The module is admitted under the open-problem-resolution basis of CLAUDE.md §3.2; the per-declaration proof shapes are listed in the delivery PR. `utility: none`. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** for every two-qubit density matrix ρ, √(D_G^A(ρ)) ≤ C_M(ρ).

**Computed, not formalized** (orchestrator, numpy, recorded in #19704): over 3000 random states of ranks 1–4, the least value of ‖Q‖² − D_G^A is −8.3·10⁻¹⁶, roundoff at equality.

**Argued, not formalized.**
- *Mechanism.* Measuring A along its own Bloch vector leaves only the part of the correlation tensor orthogonal to x. That part is the correlation matrix Q with its x-direction removed, so its two remaining singular directions are each witnessed by a pair of spin observables.
- *Sharpness.* Equality holds for pure states, where the source shows C_M = √D_G^A.
- *Trace norm.* The same measurement gives ‖ρ − 𝒫(ρ)‖₁ = s_max(PQ) numerically, which would settle the trace-norm comparison D₁ ≤ C_M of arXiv:1607.06585; that is the separate preregistration #19706.

**Effect on the paper.** The first inequality of (II.23) holds for all two-qubit states, so C_M bounds both √D_G^A and, by the source's second inequality, the negativity.

## ASSUMED-UNVERIFIED

The bounded literature check does not establish exhaustive worldwide novelty or priority. The published journal text was not read; the quotations are from arXiv v2. The statements in "Computed, not formalized" and "Argued, not formalized" are not formalized.
