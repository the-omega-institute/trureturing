---
slug: hasheminejad-ramazi-2023-mixed-imitation-best-response-nonequilibration
bibkey: hasheminejadramazi2023equilibration
doi: 10.1109/LCSYS.2023.3292049
url: https://arxiv.org/abs/2306.03243v3
triage: theorem
motivation_gids:
  - D5/S3/ConceptDynamics/DecisionValue/MixedImitationBestResponseCycle.result
---

# Mixed imitation and best-response dynamics need not equilibrate on general graphs

## Problem

N. Hasheminejad and P. Ramazi, *Equilibration of Coordinating Imitation and Best-Response Dynamics*, arXiv:2306.03243v3 [math.DS], IEEE Control Systems Letters 7 (2023) 3078-3083, study finite undirected networks whose agents use either imitation or best response in two-strategy coordination games. The source defines persistence as every agent becoming active infinitely often. Its abstract asks:

> It is therefore, unknown, whether a potential function also exists for mixed populations or if there actually exists a counter example where an activation sequence prevents equilibration.

(`main.tex`, abstract, l. 71.) In Section 2 it states:

> However, it remains open whether the dynamics equilibrate under an arbitrary persistent activation sequence.

(`main.tex`, l. 225.) The conclusion specifies the general-graph question:

> Whether dense trees or general graphs equilibrate under every activation sequence remains an open problem.

(`main.tex`, l. 668.)

The module's `claim` is the general-graph statement: for every `n : ℕ`, every symmetric and irreflexive adjacency relation on `Fin n`, every imitator assignment and real payoff map satisfying $\max\{\mathrm{pay}_i(B,A),\mathrm{pay}_i(A,B)\}<\min\{\mathrm{pay}_i(A,A),\mathrm{pay}_i(B,B)\}$ for every agent, every initial state, and every persistent activation sequence, some trajectory state is an `IsEquilibrium`. Here `false` denotes $A$ and `true` denotes $B$; `IsEquilibrium` quantifies over every activation sequence.

## Motivation

A positive answer to the universal claim would extend equilibration from the source's special network classes to all finite symmetric irreflexive graphs. The source's coordination condition and persistence assumption are retained exactly in the formal claim, so a counterexample under those hypotheses isolates the role of graph structure and mixed update rules. The settlement supplies a concrete non-equilibrating persistent schedule while leaving the source's separate potential-function question as a distinct statement.

## Gap

Issue [#22604](https://github.com/the-omega-institute/trureturing/issues/22604) records a bounded literature check: arXiv versions v1-v3 retain the open question; the cited random-activation result of Sakhaei, Maleki, and Ramazi concerns almost-sure equilibration and does not cover arbitrary persistent schedules; Crossref and Semantic Scholar searches found no work settling the general-graph question; and no repository record was found. The result of that check was `not-found-in-searched-scope`.

## Route

The module fixes four agents and defines `graph` by $i\ne j$ with only the $0$--$2$ edge removed, `kinds` with agent $1$ a best responder and agents $0,2,3$ imitators, the four payoff quadruples $(1,0,0,4)$, $(3,2,2,3)$, $(4,1,0,4)$, and $(4,3,3,4)$, the eight Boolean states `orbit`, and the activation sequence `activation` with repeating block $(2,0,3,1)$.

- `graph_symmetric` proves `Symmetric graph`, and `graph_irreflexive` proves `Std.Irrefl graph`. `payoffs_coordination` proves, for every $i : \mathrm{Fin}\,4$, the strict coordination inequality used by `claim`.
- `activation_persistent` proves `IsPersistent activation`: for every $i$ and $t$, it supplies a $u\ge t$ with `activation u = i`; the four cases use $u=4t+1,4t+3,4t,4t+2$, respectively, for agents $0,1,2,3$.
- `utility_values` proves the displayed utility vector for every $r : \mathrm{Fin}\,8$ and $i : \mathrm{Fin}\,4$. `alternative_values` proves agent $1$'s utility after `Function.update (orbit r) 1 s` for every $r : \mathrm{Fin}\,8$ and $s : \mathrm{Bool}$. `first_two` proves that the first two activations leave `orbit 0` unchanged.
- `cycle_steps` proves, for every $r : \mathrm{Fin}\,8$, that activating `activation (r.val + 2)` at `orbit r` produces `orbit ⟨(r.val + 1) % 8, Nat.mod_lt _ (by decide)⟩`.
- `first_ten` proves, for every $t : \mathbb N$ with $t\le10$, that the trajectory equals `orbit 0` when $t<2$ and otherwise equals `orbit ⟨(t - 2) % 8, Nat.mod_lt _ (by decide)⟩`.
- `activation_period` proves `activation (t + 8) = activation t` for every $t : \mathbb N$. Using it, `trajectory_period` proves the trajectory equality at $t+8$ and $t$ for every $t$ satisfying $2\le t$; `trajectory_reduce` then proves the reduction from $t+2$ to $(t\bmod8)+2$ for every $t$.
- `equilibrium_step` states that for arbitrary $n$, adjacency, imitator map, payoff map, state $x$, equilibrium proof $h : \mathrm{IsEquilibrium}\,\mathrm{adj}\,\mathrm{imitator}\,\mathrm{pay}\,x$, and agent $i$, `step adj imitator pay x i = x`; it obtains this from $h$ at time $1$ under the constant schedule `fun _ => i`. `orbit_not_equilibrium` applies this to every $r : \mathrm{Fin}\,8$ and the designated activation, using `cycle_steps` to show a move. `never_equilibrium` proves the negation of equilibrium for every natural trajectory time, using the $t<2$ case and the periodic reduction.
- `result` assumes `claim`, instantiates it at $n=4$ with `graph`, `kinds`, `payoffs`, `orbit 0`, and `activation`, discharges the symmetry, irreflexivity, coordination, and persistence hypotheses with the named lemmas, and contradicts `never_equilibrium`.

## Falsifier

The refutation would not address the source question if the formal update rules or equilibrium notion differed. The module's `utility` sums $ \mathrm{pay}\ i\ (x\,i)\ (x\,j)$ over the filtered neighbours; `hasMaximizer` requires a neighbouring agent using the candidate strategy whose unchanged-state utility is at least every neighbouring utility; imitators keep their current strategy when both strategies maximize or when no strategy has a maximizer; best responders compare their own utilities after replacing their coordinate by `false` and `true`, switching only on a strict inequality; and `step` changes one coordinate. The no-switch tie convention, arbitrary-sequence definition of `IsEquilibrium`, and $\forall i,t\,\exists u\ge t$ definition of persistence are therefore part of the falsification target.

The witness satisfies the module's full hypotheses: `graph_symmetric`, `graph_irreflexive`, `payoffs_coordination`, and `activation_persistent` provide the required premises. A different payoff convention, a schedule-specific equilibrium notion, or a weaker persistence condition would be a different statement.

## Evidence

The canonical source is `D5/S3/ConceptDynamics/DecisionValue/MixedImitationBestResponseCycle.lean`.
Frozen state: `Golden/Frozen/state/D5/S3/ConceptDynamics/DecisionValue/MixedImitationBestResponseCycle.lean.json`.
Declaration statements:
- `result`: `sha256:027e51660e22098c1596788afc3988335a155df9340eda2574eef20896269c17`;
- `claim`: `sha256:308ee07540444ef0ad1a37c45b8fb493566755d30900f4272b7bb44ed9cd40d9`.

- **Proof.** It proves `result : ¬ claim`.
- **Axioms.** `result` depends only on `propext`, `Classical.choice`, and `Quot.sound`; there is no `sorry`, `native_decide`, or new axiom.

## Triage

Tier 1 question from the 2023 IEEE Control Systems Letters paper, preregistered in issue [#22604](https://github.com/the-omega-institute/trureturing/issues/22604) before any Lean.
`theorem`; resolution `refuted`.

| declaration | proof_shape | escape_witness | admission_basis |
| --- | --- | --- | --- |
| `result` | content | none: the four-agent witness, finite utility computations, periodicity, and non-equilibrium argument are consumed on its proof path | open-problem-resolution |
| `trajectory_period`, `trajectory_reduce`, `never_equilibrium` (private) | content | none: inductions on time consumed on the proof path of `result` | open-problem-resolution |
| `utility`, `hasMaximizer`, `update`, `step`, `traj`, `IsEquilibrium`, `IsPersistent`, `claim` | bind-only | none: definitions used by `result` | open-problem-resolution |
| other private witness and helper declarations | bind-only | none: consumed on the proof path of `result` | open-problem-resolution |

The module is admitted under the open-problem-resolution basis of CLAUDE.md §3.2; the per-declaration proof shapes are listed above. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** the proposition `claim` is false: the universal assertion quantified by `claim`—over every $n$, symmetric irreflexive adjacency, imitator assignment, coordinating payoff map, initial state, and persistent schedule—does not hold.

**Computed, not formalized** (the orchestrator's exact enumeration recorded in issue #22604): for the four-agent witness network, the only equilibrium states among its 16 Boolean states are $AAAA$ and $BBBB$, and the displayed periodic trajectory does not visit either state.

**Argued, not formalized.**
- **Mechanism.** The graph $K_4$ with the $0$--$2$ edge removed contains triangles, and the mixed roles let the best responder at agent $1$ switch on its own payoff comparison while the three imitators relay the resulting local maxima. Under the persistent block $(2,0,3,1)$, the eight listed states $BABB,BABA,BBBA,BBAA,ABAA,ABAB,AAAB,AABB$ are traversed cyclically; this is the structural failure of a universal equilibration guarantee.
- **Missing structure.** The strict coordination inequalities and persistence condition do not supply a common decreasing potential on this general graph. The witness is not a tree, so the source's sparse-tree mechanism does not apply.
- **Nearby statements that survive.** The source's positive results for linear graphs, rings, starlike networks, and sparse trees are not contradicted by this witness. The settlement does not decide whether dense trees equilibrate under every persistent schedule, whether a potential function exists for mixed populations, or whether some other schedule can equilibrate this particular network. It also does not address the source's separate random-activation, almost-sure result.

## ASSUMED-UNVERIFIED

The literature check is bounded and does not establish exhaustive worldwide novelty or priority; the citation searches and the cited random-activation result were not independently reproved here. The source's positive equilibration theorems, its potential-function discussion, and the issue's enumeration of all equilibria are not formalized by this module. Any extension from this four-agent non-tree witness to dense trees, or any claim about non-existence of potential functions, remains open.
