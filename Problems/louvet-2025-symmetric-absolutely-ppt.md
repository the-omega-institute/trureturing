---
slug: louvet-2025-symmetric-absolutely-ppt
bibkey: louvet2025symmetricppt
doi: 10.1103/PhysRevA.111.042418
url: https://arxiv.org/abs/2411.16461v2
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Entanglement/AbsoluteSeparability/LouvetSymmetricAbsolutelyPPT.result
---

# Louvet symmetric absolutely-PPT spectrum conjecture

## Problem

J. Louvet, E. Serrano-Ensástiga, T. Bastin and J. Martin, *Nonequivalence between absolute separability and positive partial transposition in the symmetric subspace*, arXiv:2411.16461v2 and Physical Review A 111, 042418 (2025), state Conjecture 1: every symmetric $N$-qudit state with

$$D = \binom{N+d-1}{d-1}$$

non-zero eigenvalues of the form

$$1-(D-1)p/D,\quad p/D,\ldots,p/D,$$

where $p \in [p_{\min},1]$ and

$$p_{\min}=1/(1+2[D\binom{N}{\lfloor N/2\rfloor}]^{-1}),$$

is symmetric absolutely PPT. The formal claim uses `Matrix.PosSemidef`, the symmetric-column predicate, the full-space characteristic polynomial with $d^N-D$ zero roots, and positivity of every site partial transpose.

### Statement echo

| source clause | Lean counterpart | fidelity |
| --- | --- | --- |
| symmetric $N$-qudit state | `IsSymmetricOperator ρ` together with `ρ.PosSemidef` | exact quantified predicate |
| $D=\binom{N+d-1}{d-1}$ | `D N d` | literal definition |
| $p_{\min}=1/(1+2[D\binom{N}{\lfloor N/2\rfloor}]^{-1})$ | `pmin N d` | literal definition with `Nat.div` |
| prescribed non-zero spectrum and $d^N-D$ zero roots | the `ρ.charpoly` equality in `claim` | exact characteristic-polynomial factors |
| $p\in[p_{\min},1]$ | `pmin N d ≤ p` and `p ≤ 1` | exact interval hypotheses |
| symmetric absolutely PPT | `IsSAPPT ρ` | exact quantified conclusion |

## Motivation

The paper leaves this explicitly stated qudit conjecture after proving the qubit case. Issue [#19125](https://github.com/the-omega-institute/trureturing/issues/19125) records the source statement, conventions, literature screen and settlement target. The settling declaration is `D5/S3/Quantum/Entanglement/AbsoluteSeparability/LouvetSymmetricAbsolutelyPPT.result`.

## Gap

The source gives a symbolic and numerical rationale for the threshold while leaving Conjecture 1 as a conjecture. The missing unbounded argument is the combination of the symmetric-projector partial-transpose floor, the rank-one partial-transpose lower bound, the occupation-class dimension bridge and the central-binomial estimate.

## Route

The permutation symmetrizer has a positive partial-transpose floor on every site bipartition. The residual spectral part is positive on the symmetric range, while a normalized rank-one partial transpose is bounded below by minus one half on that range. The threshold inequality makes the resulting coefficient non-negative for every $N\ge2$, $d\ge2$ and every subset of sites. The Lean result applies these ingredients to the exact characteristic polynomial and symmetry hypotheses.

## Falsifier

A symmetric positive-semidefinite operator satisfying the displayed characteristic polynomial and $p\ge p_{\min}$ whose unitary conjugate has a partial transpose that is not positive-semidefinite would refute the claim. An error in the projector floor, the rank-one bound, the occupation dimension, or the threshold inequality would also falsify the settlement.

## Evidence

The kernel-checked declaration is `D5.S3.Quantum.Entanglement.AbsoluteSeparability.LouvetSymmetricAbsolutelyPPT.result : claim`. Its proof uses the delivered permutation-floor and pure-bound modules and the frozen `OccupancyWordSectors` declarations named in the module comment. The public declaration axiom closure is contained in `{propext, Classical.choice, Quot.sound}`.

The external numerical diagnostic is pinned to [`the-omega-institute/trureturing-experiments@32dbff0969a37515f545a199bd6359ff12bec569/docs/reports/louvet-serrano-bastin-martin-2025-conjecture1-sappt`](https://github.com/the-omega-institute/trureturing-experiments/tree/32dbff0969a37515f545a199bd6359ff12bec569/docs/reports/louvet-serrano-bastin-martin-2025-conjecture1-sappt). `check.py` has SHA-256 `8e42fe9ed85db7a48e6bd0a3ef0c0e954f5a2119a25b5cd164ab49764c453ae3`; `git -C ../trureturing-experiments show 32dbff0969a37515f545a199bd6359ff12bec569:docs/reports/louvet-serrano-bastin-martin-2025-conjecture1-sappt/check.py | python3` exits 0 with `RESULT PASS` for $(N,d)\in\{(2,2),(2,3),(3,2),(3,3),(4,2),(2,4),(4,3),(5,2),(3,4)\}$ and all site subsets for the projector-floor checks, with 30 random states per pair on every nontrivial site subset and balanced GHZ diagnostics. This is numerical evidence for the listed finite scope; the unbounded result is the Lean theorem.

## Triage

| target item | status | evidence |
| --- | --- | --- |
| Proved under the unchanged conventions | proved | kernel-checked `LouvetSymmetricAbsolutelyPPT.result`; the projector-floor, pure-bound and spectral reduction steps give the stated SAPPT conclusion |
| Exact minimum eigenvalue of $(P/D)^{T}$ on the local symmetric space | open | the experiment checks finite instances and the Lean result uses a lower bound; no exact-eigenvalue theorem is declared |
| Sharpness/NPT for all $p<p_{\min}$ in all qudit dimensions | open | the experiment checks the listed GHZ diagnostics; no universal sharpness theorem is declared |
| A complete literature census or an independent novelty claim | open | the literature screen is bounded and its completeness is `ASSUMED-UNVERIFIED` |
| Split the verified proof according to the four-module plan and recompile each exact module | proved | the delivered source has the pure-bound, permutation-floor and settling modules; the spectral reduction helpers are integrated into the settling module and the scoped Lean build exits 0 |
| Keep each module below 1000 lines and keep real helper consumers | proved | current line counts are 299, 710 and 453; the scoped proof terms consume the private helpers recorded in the Scribes |
| Add the corresponding Scribes, resolution claim, dossier, registration, freeze and admission checks | open | the Scribes, resolution claim, dossier and all three canonical state records are delivered; the four-slot escape registration remains unfinished under issue #19210 |
| Mechanism | proved | kernel-checked `SymmetricAbsolutePPTPermutationFloor.symmetrizer_partialTranspose_floor` gives the unnormalized projector floor $1/\binom{N}{k}$; `SymmetricAbsolutePPTPureBound.psd_partialTranspose_half_trace` gives the trace-scaled minus-one-half bound. Division of the projector by $D$ gives the normalized floor $1/(D\binom{N}{k})$ by linearity |
| Source’s conclusion | open | literature reading: the cited source states the qudit sufficient condition as Conjecture 1 and reports symbolic evidence, while its Theorem 1 concerns qubits; the conjecture is proved by this delivery, and completeness of the wider literature screen remains unverified |

### What the settlement shows

The sufficient condition in Conjecture 1 holds for every $N\ge2$ and $d\ge2$ under the source's conventions. The mechanism is a uniform positive floor from the identity coset of the symmetrizer, combined with the minus-one-half rank-one bound and the central-binomial threshold inequality. The theorem does not establish the exact local minimum eigenvalue, universal sharpness below the threshold, or a complete literature census.

The source's qubit if-and-only-if result is consistent with this sufficient condition. The Lean result supplies the unbounded sufficient direction for the qudit spectrum; it does not settle the neighbouring sharpness question.

## ASSUMED-UNVERIFIED

The literature completeness claim and any independent novelty claim are `ASSUMED-UNVERIFIED`; the search covered the preregistration's cited source and bounded citation checks. The escape audit for the public theorem declarations is unfinished under [issue #19210](https://github.com/the-omega-institute/trureturing/issues/19210); no `declared_validated` registration is claimed. Exact local eigenvalues and universal below-threshold NPT remain open as stated in the Triage.
