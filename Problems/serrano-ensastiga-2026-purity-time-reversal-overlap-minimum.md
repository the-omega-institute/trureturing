---
slug: serrano-ensastiga-2026-purity-time-reversal-overlap-minimum
bibkey: serranoensastiga2026monogamy
doi: 10.1103/9fkf-hm8l
url: https://arxiv.org/abs/2507.12680v2
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Entanglement/PurityTimeReversalOverlapMinimum.result
---

# The minimum of purity plus time-reversal overlap

## Problem

E. Serrano-Ensástiga, O. Giraud and J. Martin (arXiv:2507.12680, quant-ph;
Phys. Rev. A 113 (2026) 012415) bound the sector lengths of multiqubit states
through the reduced states `ρ_A` of a pure state and their time-reversed
partners `ρ̃ = σ_y^{⊗k} ρ^* σ_y^{⊗k}`, with the overlap `R_ρ = Tr(ρ ρ̃)`.
Their Proposition 1 gives `Tr(ρ_A²) + R_{ρ_A} ≥ 2^{−min(k, N−k)}`, and they
state:

> Let $A|\bar{A}$ be a bipartition of an $N$-qubit system into $k=|A|$ and
> $N-k=|\bar{A}|$ qubits. Then, the minimum of
> $\mathrm{Tr}(\rho_A^2) + R_{\rho_A}$ taken over all pure states
> $|\psi\rangle$ of the $N$-qubit system, is given by
> $\min_{|\psi\rangle} \big(\mathrm{Tr}(\rho_A^2) + R_{\rho_A}\big) =
> 2^{k-N}$ if $2k > N$, and $2^{-k + 1}$ if $2k \leq N$.

Issue #11730 fixes the reading: `A` is any set of `k` qubits with
`1 ≤ k ≤ N − 1`, a pure state is a unit vector of amplitudes on the `2^N`
configurations, `ρ_A` is the partial trace over the other qubits, and the
minimum means a lower bound for every unit vector together with a unit vector
that attains it. The result proves the conjecture.

## Motivation

The paper uses `Tr(ρ_A²) + R_{ρ_A}` to derive sector-length inequalities, and
the conjecture identifies the exact minimum of this quantity. The paper
proves the case `k = 1` (the sum is identically `1`) and reports the other
values from numerical optimization for up to ten qubits. The frozen
declaration
`D5/S3/Quantum/Entanglement/PurityTimeReversalOverlapMinimum.result` proves
the statement for every `N` and every bipartition.

## Gap

Issue #11730 preregisters the reading, the route and the literature check.
The two citing papers listed by Semantic Scholar (2604.09766, 2510.06602) do
not state the quantity, and arXiv searches for sector lengths after 2025-07
return works that neither cite the paper nor mention the time-reversed state.
The bound `2^{1−k}` follows from the paper's own expansions of the purity and
of `R_ρ` in sector lengths (see Triage); this consequence is not drawn in the
paper, and the paper keeps the statement as a conjecture.

These readings are `not-found-in-searched-scope`; they do not establish an
exhaustive worldwide literature search, priority, or the absence of an
independent answer.

## Route

Write `d = 2^k`, `r = 2^{N−k}`, `M` the `d × r` matrix of amplitudes, so that
`ρ_A = M Mᴴ` with `Tr ρ_A = 1`, and `Φ = Y M̄` with `Y = σ_y^{⊗k}`.
1. `Y` is Hermitian and `Y Y = 1`, so `ρ̃_A = Φ Φᴴ`, `Tr ρ̃_A = 1`, and
   `Φᴴ Φ` is the entrywise conjugate of `Mᴴ M`.
2. `F = Tr(ρ_A²) + R_{ρ_A}` equals `Tr((MᴴM)²) + ‖Mᴴ Φ‖_F²`, and
   `Tr((MᴴM)²) = ‖MᴴM‖_F² ≥ |Tr MᴴM|²/r = 1/r` by Cauchy–Schwarz on the
   diagonal. So `F ≥ 1/r`.
3. For the Hermitian matrix `S = ρ_A + ρ̃_A`, `Re Tr S² = 2F` and
   `Re Tr S² = ‖S‖_F² ≥ |Tr S|²/d = 4/d`. So `F ≥ 2/d`.
4. If `2k ≤ N`, an injection of `A` into the other qubits gives a maximally
   entangled state with `ρ_A = ρ̃_A = 1/d` and `F = 2/d`.
5. If `2k > N`, an injection `κ` of the other qubits into `A` and a qubit `i₀`
   of `A` outside its image give a state with `MᴴM = 1/r`, so
   `Tr(ρ_A²) = 1/r`, and with `MᴴΦ = 0`, because every entry contains the
   factor `σ_y(0, 0) = 0` at `i₀`; so `F = 1/r`.
6. `max(1/r, 2/d)` is `2^{k−N}` when `2k > N` and `2^{1−k}` when `2k ≤ N`.

## Falsifier

The proof depends on `σ_y` in the time reversal: with the identity in its
place, `ρ̃ = ρ̄`, and for the state of step 5 the overlap equals
`Tr ρ_A² = 1/r`, so that state gives `2/r` instead of `1/r`. The trivial
bipartitions are excluded by the reading; for them `max(1/r, 2/d)` is also
the minimum (argument, not formalized): `1` for `k = N`, attained by a
configuration state, and `2` for `k = 0`, where the quantity is constant.

## Evidence

Double-precision checks (issue #11730): 6 300 random states for
`2 ≤ N ≤ 7` and every `1 ≤ k ≤ N − 1` never go below the claimed minimum
(smallest gap `−1.1·10^{−15}`), and the states of steps 4–5 reach it for
`2 ≤ N ≤ 8`.

The canonical source is
`D5/S3/Quantum/Entanglement/PurityTimeReversalOverlapMinimum.lean`. Its
public declarations are `Outside`, `join`, `reducedState`, `sigmaYTensor`,
`timeReversed`, `purityPlusOverlap`, `conjecturedMin`, `claim` and `result`;
`reducedState` is the frozen `partialTraceRight` of
`D5/S3/Quantum/Information/PartialTraceMutualInformation`, and `σ_y` is
`i X Z` for the frozen `qubitX`, `qubitZ` of `D5/S3/Quantum/FiniteDimensional`. The frozen module state has statement identity
`sha256:87c4a3cae46e43203f1199d25a532167e7f7081fce502b7a09424e459bcfdfae`.
The result declaration has statement identity
`sha256:9593b9fd4c17d3f8f700bb16c229ae17c995960ac448b47ad392b40f7fbc2d3e`.
The Freeze event is
`sha256:0d70d7f5d6fdf9d03f26605b8ac9e940feeadc27899164f9c3e1a21cc4a347f9`
and its project-level frozen prerequisites are these two modules. The proof
uses only the
standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`,
`native_decide`, or new axiom.

## Triage

Tier 1 conjecture from a 2025 quant-ph paper, preregistered in issue #11730
before any Lean. `theorem`; resolution `proved`. The public theorem has
`proof_shape: bind-only`: the Frobenius identity, `sq_sum_le_card_mul_sum_sq`
and trace cyclicity give the two lower bounds, and coefficient computations
give the two explicit states; every step is a local `have` of `result`. There
is no escape witness. The admission basis is `open-problem-resolution`.
Utility `none`.

### What the settlement shows

**Proved (Lean):** for every `N` and every set `A` of `1 ≤ k ≤ N − 1` qubits,
the minimum of `Tr(ρ_A²) + R_{ρ_A}` over pure states is
`max(2^{1−k}, 2^{k−N})`.

**Source consequences (paper's Proposition 1, not formalized):** its lower
bound `2^{−min(k, N−k)}` is attained exactly when `2k > N`; for
`2 ≤ k ≤ N − k` the minimum is twice that bound.

**Mechanism (argument, not formalized):** the paper's Eq. (`trArA`) gives
`Tr(ρ_A²) = 2^{−k} Σ_m S_m(ρ_A)` and `R_{ρ_A} = 2^{−k} Σ_m (−1)^m S_m(ρ_A)`,
so `Tr(ρ_A²) + R_{ρ_A} = 2^{1−k} Σ_{m even} S_m(ρ_A)`. With `S_0 = 1` and
`S_m ≥ 0` (the paper's Eqs. `Eq.Trace1`, `Ineq.Sk`) this is at least
`2^{1−k}`, with equality exactly when every even sector length
`S_m(ρ_A)`, `m ≥ 2`, vanishes; the maximally mixed `ρ_A` of step 4 is such a
state. The bound `2^{k−N}` is the purity of the reduced state of the smaller
part, `Tr ρ_A² = Tr ρ_Ā² ≥ 2^{−(N−k)}`, together with `R ≥ 0`.

**Not formalized (argument):** when `2k > N`, equality `F = 2^{k−N}` forces
`ρ_A` to have `2^{N−k}` equal non-zero eigenvalues and its support to be
orthogonal to its image under the time reversal, as for the state of step 5.

## ASSUMED-UNVERIFIED

The published Phys. Rev. A text was not read, so it is unverified whether
the conjecture was edited there. The bounded literature check does not
establish exhaustive worldwide novelty, priority, or the absence of an
independent answer. The Lean kernel does not authenticate the external source
or its version history.
