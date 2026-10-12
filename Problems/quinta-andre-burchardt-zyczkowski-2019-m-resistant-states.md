---
slug: quinta-andre-burchardt-zyczkowski-2019-m-resistant-states
bibkey: quinta2019resistant
doi: 10.1103/PhysRevA.100.062329
url: https://arxiv.org/abs/1908.10390v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Entanglement/MResistantQuditExistence.result
---

# M-resistant qudit states exist for every admissible loss parameter

## Problem

Quinta, André, Burchardt and Życzkowski, *Cut-resistant links and multipartite entanglement resistant to particle loss*, Phys. Rev. A 100, 062329 (2019), arXiv:1908.10390v1, Section V, state:

> **Conjecture.** For any $N$ and $m$, there exists an $m$-resistant $N$-qudit state in some local dimension $d$.

Their Section III definition says that an entangled state remains entangled after tracing out any $m$ subsystems and becomes separable after tracing out any $m+1$ subsystems. This dossier uses finite full separability for the separable predicate and the admissible range $N\geq3$, $m+2\leq N$.

### Statement echo

The Lean `claim` quantifies all natural $N,m$ with $3\leq N$ and $m+2\leq N$, then supplies a natural local dimension $d$, a pure amplitude function on $(\mathrm{Fin}\,N)\to\mathrm{Fin}\,d$, unit norm by the finite sum of `Complex.normSq`, and `IsMResistant m ψ`. `IsMResistant` is the conjunction of initial failure of full separability, failure after every loss set of cardinality $m$, and full separability after every loss set of cardinality $m+1$. The pure-state convention is the frozen `rankOneDensity` declaration.

## Motivation

The source leaves existence in some local dimension open for the full admissible range. Zhang, Han, Shi and Zhang, arXiv:2505.06567v1, Conjecture 1, restate the same existence question. Han, Zhang and Zhang, arXiv:2606.08561v1, still report only the range $m\leq (N-2)/2$ as known. The frozen declaration `D5/S3/Quantum/Entanglement/MResistantQuditExistence.result` proves the source conjecture in its stated admissible range.

## Gap

The construction has local dimension $d=2\binom{N}{m}$. The source conjecture asks only for existence in some dimension, so this closes its quantified claim. The least possible local dimension is not determined here. Qubit constructions for $m>(N-2)/2$ and the minimal local dimension remain open.

The literature screen in preregistration #15010 is bounded to the cited source, Zhang et al. (2025), Han et al. (2026), and its recorded searches; it supports `not-found-in-searched-scope` and does not assert exhaustive worldwide priority. The escape audit is unfinished under issue [#15589](https://github.com/the-omega-institute/trureturing/issues/15589). Its concrete gap is a faithful dependent-family registration with full source reconstruction and equivalence bridge, actual-positive law, whole-family variation, independent sensitivity, and observational-dependence evidence. The delivered-head DTR reading is `DTR-Unregistered` (Observe) for `separable_exchange_zero` and `result`; no `declared_validated` registration is claimed.

## Route

Let $k=N-m$. Encode each $k$-subset $S$ together with a bit. Every site records the common subset label, and the bit is recorded only at sites in $S$. An explicit equivalence embeds these labels into a finite local basis of size $d=2\binom{N}{m}$. The state is the uniform superposition of the resulting distinct product-basis configurations.

A loss of $m+1$ sites meets every $k$-subset, so all off-diagonal terms disappear. The remaining diagonal is a finite convex mixture of products of local basis projectors and is fully separable. A loss of $m$ sites leaves exactly one intact flag. Its surviving coherence has a zero exchanged diagonal; `separable_exchange_zero` rules out full separability. The same exchanged-diagonal obstruction gives initial entanglement.

## Falsifier

A counterexample would be an admissible pair $(N,m)$ for which every finite local dimension fails to provide a normalized pure state satisfying the three resistance clauses, or a failure of one of the universal loss-set clauses for the displayed construction. The kernel-checked result covers all natural $N,m$ in the claim's range. A qubit-only counterexample outside that range would not refute the settled claim.

## Evidence

The supporting declaration `D5/S3/Quantum/Entanglement/FullySeparableExchangeObstruction.separable_exchange_zero` has declaration statement ID `sha256:cc9db09ebb15605032c0bc389540ec1e76e4442c2d71fdc283cde133048236a2`. The settling declarations have declaration statement IDs `sha256:1327de9bec1f4dd508480f4407987fe29f8fc10c5d9ea9fb2b41f0ed887faa6b` for `IsMResistant`, `sha256:7d826234e720b0c2efc25eaac6761eee1912e871a92f4c99589597d27d7cd5ad` for `claim`, and `sha256:57e94cd6f0c4b6a84a1ae0d8066ee21cce8b203557c717e0a3f2ad90f98b2e6c` for `result`. The settling module state pin is `sha256:cc99e7d4b3509064bf7c9ba23b3a83bcdf0858f728cfe0ce70f3b5f31418998d`.

The kernel axiom closure of every public declaration is contained in `{propext, Classical.choice, Quot.sound}`. The frozen prerequisites used by the settling proof are `D5/S3/Quantum/PureState/PureStateHandshake.rankOneDensity`, `D5/S3/Quantum/Entanglement/LocalObservationPartialTraceEquivalence.partialTraceFirst`, `D5/S3/Quantum/Foundation/FiniteStateChannel.DensityState`, and `D5/S3/Quantum/Information/OrthogonalRecordEntropy.pointerState`; the supporting obstruction is a same-delivery prerequisite.

The exact-rational reading is published at [`docs/reports/quinta-andre-burchardt-zyczkowski-2019-m-resistant-states/check.py`](https://github.com/the-omega-institute/trureturing-experiments/tree/664831fdc0f2267cd539af109024ede9e42826ab/docs/reports/quinta-andre-burchardt-zyczkowski-2019-m-resistant-states) in commit `664831fdc0f2267cd539af109024ede9e42826ab`. The command `python3 check.py` exits `0`, ends with `ALL_OK`, and checks $3\leq N\leq6$ with exact rational entries. The script SHA-256 is `c25ee3e55a0028bdabbeffd0e80e260e26022c08bd59b97cf359d319e9f1bb70`.

## Triage

| Item | Status | Evidence and boundary |
| --- | --- | --- |
| Flag-code every $k=N-m$ subset with a shared label and a bit localized to that subset; every $(m+1)$-loss is diagonal and fully separable; every $m$-loss retains an obstruction coherence. | proved | `MResistantQuditExistence.result` is kernel-checked; `separable_exchange_zero` supplies the exchanged-diagonal implication. |
| Local dimension. | proved in prose | The construction uses $d=2\binom{N}{m}$, as described in Route. The least possible $d$ is open. |
| Exact finite reading. | computed | `python3 check.py`, exit `0`, script SHA-256 `c25ee3e55a0028bdabbeffd0e80e260e26022c08bd59b97cf359d319e9f1bb70`, scope $3\leq N\leq6$, exact rational entries, final line `ALL_OK`. |
| Qubit states for $m>(N-2)/2$. | open | The construction uses larger local dimensions; no qubit existence result in this range is claimed. |
| Minimal local dimension. | open | No lower bound or optimality theorem is proved beyond the displayed construction. |

### What the settlement shows

The decisive mechanism is the shared subset label plus a localized branch bit. It works uniformly for every admissible natural $N,m$ and yields the explicit dimension $2\binom{N}{m}$. The proof extends the source's known range $m\leq(N-2)/2$ to the whole pure-state existence conjecture in arbitrary local dimension. It does not settle qubit existence beyond that known range or optimize the local dimension. The source's ordinary resistance statements remain compatible: this result supplies the existence premise in the full admissible range, while minimal dimension and qubit-specific questions remain separate.

The public result is the settling result for the named open problem and is admitted under `open-problem-resolution (#15010; Proved)`. The escape audit remains unfinished under #15589 with the `DTR-Unregistered` reading above; no `declared_validated` registration is claimed.

## ASSUMED-UNVERIFIED

The Lean kernel verifies the formal finite-dimensional statement and its standard axiom closure. The correspondence between the formal predicates and the source's physical terminology, the quoted literature statements, and completeness of the bounded literature screen are external assumptions. The exact-rational experiment is evidence only for $3\leq N\leq6$ and does not replace the uniform Lean proof.
