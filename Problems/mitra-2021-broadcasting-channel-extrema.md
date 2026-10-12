---
slug: mitra-2021-broadcasting-channel-extrema
bibkey: mitra2021layers
doi: 10.1103/PhysRevA.104.022206
url: https://arxiv.org/abs/2101.05752v4
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Measurements/BroadcastingChannelExtremaRefutation.result
---

# Mitra broadcasting-channel extrema

## Problem

A. Mitra, *Layers of classicality in the compatibility of measurements*, Phys. Rev. A 104, 022206 (2021), arXiv:2101.05752v4, Section III.A asks whether the broadcasting channels of an observable have a highest element and whether they have a lowest element under precomposition by channels that are nondisturbing for that observable. The source repeats both questions in its Conclusions.

The formal convention uses an observable with outcomes `Fin m`, input matrices on `Fin d`, output matrices on `Fin d × Fin d`, finite Kraus channels, the broadcasting predicate, the nondisturbing predicate, and the precomposition relation. The settling declaration `D5/S3/Quantum/Measurements/BroadcastingChannelExtremaRefutation.result` has type `¬ claim` and carries `OpenProblemResolutionClaim(Refuted)`.

### Statement echo

The source's broadcasting condition is the pair of marginal trace equalities in `Broadcasts`; its nondisturbance condition is equality of each observable effect's trace after channel application in `Nondisturbing`; `ConstructedFrom` is precomposition by such a channel. `HasHighest` and `HasLowest` quantify over broadcasting channels and this relation. `claim` combines observability, existence of a broadcasting channel, and the disjunction of the two extrema. The fixed witness uses `d = 3`, `m = 2`, and the observable `A`; the remaining binders and hypotheses are those displayed by the corresponding Scribe nodes.

## Motivation

Issue [#15501](https://github.com/the-omega-institute/trureturing/issues/15501) records the published question, its statement, the literature screen, and the fixed Lean conventions. The result refutes both alternatives for one observable in the preregistered finite instance.

## Gap

Mitra leaves open whether every nonempty broadcasting-channel set has a highest element or a lowest element. The source does not settle the displayed qutrit observable used here; no general extremum theorem follows from this instance.

## Route

Let $P=\operatorname{diag}(1,1,0)$ and $Q=I-P$, and set $A(0)=\frac34P+\frac14Q$ and $A(1)=I-A(0)$. Three Kraus broadcasting channels prepare distinct matrix units in the $P$ sector and one matrix unit in the $Q$ sector. The kernel-checked argument shows that every nondisturbing channel fixes $P$, hence fixes each displayed broadcasting channel under precomposition. Two distinct fixed channels exclude a lowest element. A highest element would produce three orthogonal pure outputs from states supported in the two-dimensional $P$ sector; positivity and Kraus completeness force their total trace to be at most $\operatorname{trace}(P)=2$, while each contributes at least one, giving the contradiction $3\le2$.

## Falsifier

A highest or lowest element for this displayed observable, satisfying the definitions in the module, would falsify the settling result. The Lean theorem establishes the negation of the complete `claim`, so either extremum is excluded for the same observable.

## Evidence

The kernel-checked evidence is the declaration `D5/S3/Quantum/Measurements/BroadcastingChannelExtremaRefutation.result`; its public type is `¬ claim`. The module reuses the frozen `IsPOVM`, `IsDensity`, `MatrixMap.of_kraus`, `rowReset`, and `rankOneDensity` declarations. The designated result is the only public theorem, carries `utility: kind=certified-instance; basis=refutes=…`, and is exempt from four-slot escape registration under CLAUDE.md §3.9.

The numerical reading is published in [`trureturing-experiments`](https://github.com/the-omega-institute/trureturing-experiments/tree/4c6e4c505346b3370b9fa974cb87697ff55511de/docs/reports/mitra-2021-broadcasting-channel-extrema) at commit `4c6e4c505346b3370b9fa974cb87697ff55511de`. The checked command is `python3 check.py`, exit 0, with `bad= 0`; `check.py` has SHA-256 `f9fdd8b3b0d2191bcd42ca25e1eff2c967a5c3a8785f3f464520071b9dae6aef`.

## Triage

The named Section III.A questions are refuted under `admission_basis: open-problem-resolution (#15501; Refuted)`.

| Item | Status | Evidence kind and boundary |
| --- | --- | --- |
| Mechanism excluding both extrema | proved | Kernel-checked by `result` and its consumed declarations: nondisturbing channels fix $P$, two fixed distinct broadcasting channels rule out a lowest element, and the trace contradiction rules out a highest element. |
| Numerical certificate for the displayed witness | computed | The experiment entry checks the finite matrix construction and reports `bad= 0`; it is a computation for the stated $d=3,m=2$ instance, not a general theorem. |
| Sharp observables of full rank | open | No declaration in this delivery settles whether the same extremum questions have an answer for sharp full-rank observables. |
| Qubit observables | open | The module does not settle the corresponding $d=2$ questions. |
| General rank-$r$ family | open | The trace argument is used only in the delivered qutrit instance; no uniform rank-family theorem is claimed. |

### What the settlement shows

- **Proved in `result`:** for the displayed qutrit two-outcome observable, the proposed universal disjunction “highest or lowest” fails. The lowest-element failure is caused by distinct broadcasting channels that are all fixed by every nondisturbing precomposition. The highest-element failure is caused by the dimension-two support of $P$ versus three orthogonal required outputs.
- **Nearest surviving statements:** the result concerns only the `d = 3`, `m = 2` observable `A`. Questions for full-rank sharp observables, qubits, and a general rank family remain open here.
- **Effect on the source:** Mitra's Section III.A questions and their repetition in the Conclusions are answered negatively for this instance; no claim about the source's other compatibility results is changed.

## ASSUMED-UNVERIFIED

The literature citation identifies the published questions and their location; it does not establish a worldwide priority claim. The correspondence between the source's operator notation and the finite-matrix predicates is recorded in the module and Library note. The experimental reading is computational evidence for the fixed instance and does not extend the formal scope.
