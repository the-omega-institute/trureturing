---
slug: campbell-2010-log-negativity-resource-independence
bibkey: campbell2010optimalentangling
doi: 10.1103/PhysRevA.82.042314
url: https://arxiv.org/abs/1007.1445
triage: theorem
motivation_gids:
  - D5/S3/Quantum/QuantumChannels/LogNegativityCapacityResourceDependence.result
---

# Log-negativity entangling capacity depends on the input resource for CPTP maps

## Problem

E. T. Campbell, *Optimal entangling capacity of dynamical processes*, Phys. Rev. A **82**, 042314 (2010), arXiv:1007.1445v2, Section VII, p. 7, asks:

> The most obvious open question is whether log-negativity EC is resource independent for all unitaries, or indeed all CPTP maps, or whether this is a singular feature of 2-qubit gates.

The all-CPTP clause is refuted. The unitary clause and the source's two-qutrit unitary conjecture remain open. The statement and source scope are fixed in [#17047](https://github.com/the-omega-institute/trureturing/issues/17047); the source quotations are in the [Campbell note](../Library/QuantumContext/campbell2010optimalentangling.md).

### Statement echo

| Source clause | Lean counterpart | Scope |
| --- | --- | --- |
| Every bipartite CPTP map | `claim` quantifies local dimensions and finite Kraus families with completeness | Finite-dimensional square input/output spaces; the Choi–Kraus representation supplies this interpretation. |
| Free local ancillary systems | `extend`, and the suprema in `capSep` and `capAssisted` | Every pair of natural-number ancillary dimensions; the cut is $AA':BB'$. |
| Eq. (1), separable inputs | `capSep` | Density matrices that are finite convex mixtures of products of density matrices. |
| Eq. (2), increase of entanglement | `capAssisted` | All density inputs, subtracting the input's own log-negativity. |
| Eqs. (4)–(5), logarithmic rescaling | `Real.logb 2` of `traceNorm (partialTranspose ...)` | Base two; the partial transpose acts on $BB'$. |
| Resource independence | Equality of the two capacities in `claim` | Suprema are in `EReal`, preserving unbounded suprema. |
| A negative answer to the all-CPTP clause | `result` | A fixed two-qutrit channel with 18 Kraus operators and $t=1$. |

The generalized `IptPptSquaredEquivalence.IsSeparable` retains the finite-convex-mixture condition. Its local factors are positive semidefinite with trace one, the body of the reused `IsDensity` predicate. The auxiliary density condition in `capSep` is consistent with those mixtures; it does not exclude a source separable state.

## Motivation

Resource independence asks whether prior entanglement can improve the maximum increase of the same entanglement measure. Log-negativity vanishes on every PPT state, including bound-entangled states. A PPT effect with a strict separable-input overlap gap can therefore distinguish a free input from a zero-log-negativity resource input.

## Gap

Campbell establishes resource independence for basic unitaries, including two-qubit gates, and gives numerical evidence for two-qutrit unitaries. Neither assertion settles the all-CPTP alternative.

The preregistration's literature screen reports no such separation in Kao–Chou (Sci. Rep., 2020), Kao's thesis arXiv:2008.03893, Seddon–Campbell arXiv:1901.03322, Ganguly–Chatterjee–Majumdar arXiv:1401.5324, Chen–Yu arXiv:1604.05788, or Patra arXiv:2305.17636. The channel-measure works Gour–Scandolo arXiv:1907.02552 and Bäuml–Das–Wang–Wilde arXiv:1907.04181 do not state Campbell's separable-input versus assisted separation. These follow-up readings are source-check evidence reported in #17047, rather than Lean theorems. Literature completeness is `ASSUMED-UNVERIFIED`.

## Route

The five Tiles product vectors define an orthogonal projector $P$; put $Q=I_9-P$, $\tau=Q/4$, $\phi=(|00\rangle+|11\rangle)/\sqrt{2}$, $\Phi=|\phi\rangle\langle\phi|$, and $F=|22\rangle\langle22|$. The fixed channel is

$$\Lambda(X)=\operatorname{Tr}(QX)\Phi+\operatorname{Tr}(PX)F.$$

The rational inverse certificates yield the strict product-overlap estimate $\operatorname{Tr}(Q\sigma)\leq 1-1/6561$ for every separable density matrix. For arbitrary local ancillas, positivity of conditional matrices follows through the existing `IptPptSquaredEquivalence.weighted_psd` theorem. Partial transposition preserves their positivity for separable inputs. The orthogonal flagged output blocks then give the norm bound $2-1/6561$.

The PPT density input $\tau$ has partial-transpose trace norm one and output norm two. Consequently the assisted capacity is at least one, while the separable-input capacity is at most $\log_2(2-1/6561)<1$.

## Falsifier

The refutation would fail to answer the source question if it restricted the separable upper bound to a fixed ancilla size, omitted the input subtraction in the assisted objective, changed the logarithm's base, or used an incomplete Kraus family. The quantified bound `unassisted_norm_upper`, the literal definitions `capSep` and `capAssisted`, and `K_complete` cover these obligations. The theorem does not assert that the witness channel is unitary.

## Evidence

The canonical source is [LogNegativityCapacityResourceDependence.lean](../D5/S3/Quantum/QuantumChannels/LogNegativityCapacityResourceDependence.lean), with its [Blueprint](../Blueprint/D5/S3/Quantum/QuantumChannels/LogNegativityCapacityResourceDependence.md). Its only public theorem is `result : ¬ claim`. The axiom closure of every public declaration is contained in {`propext`, `Classical.choice`, `Quot.sound`}.

The public result is the designated refutation result (`basis=refutes`) and is exempt from four-slot escape registration (CLAUDE.md §3.9).

The escape audit for `ConicalDesignConcurrenceComparability.traceNorm_isometry`, `FiniteTraceDistance.traceNorm_sub_orthogonal`, `IptPptSquaredEquivalence.weighted_psd`, `SeparableStateLocalUnitaryStabilizerObstruction.trace_projector_overlap`, and `SchurChannelMixedUnitaryDistance.reindex_traceNorm` is unfinished: [#17573](https://github.com/the-omega-institute/trureturing/issues/17573). No validated four-slot registration is claimed for them.

The numerical experiment is [the published experiment directory at commit `bee0020dbf891d5d67751b57f732c4e41d86929b`](https://github.com/the-omega-institute/trureturing-experiments/tree/bee0020dbf891d5d67751b57f732c4e41d86929b/docs/reports/campbell-2010-log-negativity-resource-independence). Command: `python3 docs/reports/campbell-2010-log-negativity-resource-independence/check.py`, executed on that commit's file; exit 0, `ALL_OK`. Script SHA-256: `251156abdf2a05a6fe1a24879116e8975a6eed35f2375d6774b653dba5b16f79`.

The exact checks cover Tiles orthonormality, $Q^2=Q$, rank four, $Q^\Gamma=Q$, all ten inverse certificates and their squared Frobenius norms at most nine. The numerical optimization uses 3,000 restarts, 60 alternating steps each, and returns $\beta_{\mathrm{num}}=0.9715837867$. This is a numerical candidate, not a certified optimum. The Kraus/action and assisted-norm checks use $t\in\{0.25,0.5,0.9\}$. At each of these three values, 400 random four-term separable inputs with qubit ancillas on both sides give the following maximum partial-transpose trace norms:

| $t$ | Assisted norm | Sample maximum separable norm | $1+t\beta_{\mathrm{num}}$ |
| --- | --- | --- | --- |
| 0.25 | 1.25 | 1.154394 | 1.242896 |
| 0.5 | 1.5 | 1.326950 | 1.485792 |
| 0.9 | 1.9 | 1.569093 | 1.874425 |

These finite numerical checks establish neither a uniform bound nor an exact capacity.

## Triage

### What the settlement shows

| Target item | Status and evidence kind | Evidence and boundary |
| --- | --- | --- |
| PPT effect, strict product gap and arbitrary-ancilla separation mechanism | Proved; kernel-checked | The source's private `Q_pos`, `Q_pt`, `tau_density`, `tau_norm`, `separable_Q_gap`, `rho1_output_norm`, `conditional_ancilla_upper` and `unassisted_norm_upper` feed `result`. The scope is the fixed $t=1$ channel; the capacities satisfy $E_{LN}\leq\log_2(2-1/6561)<1\leq E_{LN}^D$. The last inequality is a lower bound, not an exact assisted capacity. |
| Every $t\in(0,1]$ separates | Open in this formalization | The delivered theorem fixes $t=1$; it has no universally quantified channel-family theorem. The experiment checks only the three listed values. The family criterion is therefore not marked kernel-checked. |
| Consequences for resource independence | Proved; kernel-checked | `result` refutes the universal all-CPTP assertion. This leaves Campbell's unitary results and the unitary question within their stated scope; no theorem about all unitaries is refuted. |
| Unitary clause and two-qutrit unitaries | Open | The witness is a measure-and-prepare CPTP map; the theorem supplies no unitary counterexample. |
| Numerical overlap candidate $\beta\approx0.97158$ | Computed | The experiment's alternating optimization yields the stated numerical value over its recorded finite search. |
| Certified sharp overlap bound | Open | Lean uses the weaker exact bound $1-1/6561$; no globally certified sharp value is proved. |
| Full-rank assisting state | Open in this formalization | The delivered assisting state is the rank-four $Q/4$; no full-rank perturbation theorem is included. |
| Published experiment | Computed | The pinned experiment, command, exit code, SHA-256, exact checks and finite numerical scope appear in Evidence. |
| Literature completeness | Open; literature reading | The listed follow-ups do not state this separation according to #17047. The unread sources are listed below. |

The failure mechanism is that a PPT resource input attains a measurement effect that all separable inputs miss by a strict amount, although its input log-negativity is zero. Positivity of conditional ancillas keeps the gap valid with free local ancillas. Campbell's basic-unitary results survive; the all-CPTP alternative has a counterexample.

## ASSUMED-UNVERIFIED

- Literature completeness: the Kao–Chou supplementary file, Seddon's 2022 thesis and arXiv:1408.3701 are unread in the supplied literature screen.
- The numerical overlap is not a certified global optimum. The samples do not certify arbitrary inputs or all $t$.
- The uniform channel family, full-rank assistance and the unitary questions are outside the delivered Lean theorem.
- The five owner-theorem escape registrations remain unfinished under #17573.
