---
slug: demo-2026-strong-period-bound
bibkey: demo2026periodicity
doi: null
url: https://arxiv.org/abs/2606.25493v1
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/Graph/Walks/DemoStrongPeriodBoundRefutation.result
---

# Refutation of the unrestricted strong distance-two period bound

## Problem

Gregory Demo, David Lund and Oleksiy Al-saadi, *On the Periodicity of
k-distance Graphs*, [arXiv:2606.25493v1](https://arxiv.org/abs/2606.25493v1),
Section 4, Conjecture 1, printed PDF page 11:

> Conjecture 1. Any connected graph G=(V,E) has ρ²(G)≤|V|−3.

The exact target and integer interpretation are registered in
[#23003](https://github.com/the-omega-institute/trureturing/issues/23003).
The [source note](../Library/Geometry/demo2026periodicity.md) records the
source qualification; the
[earlier metamour note](../Library/Geometry/erickson2024metamour.md) records
the known fixed-point example.

### Definitions and statement echo

Let $V$ be a finite vertex set and $G$ a simple undirected graph on $V$.
Define $T(G)$ on the same vertices by
$u\sim_{T(G)}v\iff\operatorname{edist}_G(u,v)=2$.
The extended distance is infinity for unreachable pairs, so $T$ is defined
also on disconnected graphs and every iterate remains in its domain.
Write $T^0(G)=G$. A positive return is an integer iteration count $t>0$
with an ordinary graph isomorphism $T^t(G)\cong G$. Define
$\rho_2(G)=\min\{t\in\mathbb N: t>0,\ T^t(G)\cong G\}$ when that set is
nonempty, and $\rho_2(G)=0$ otherwise. The source starts at $G_1^2=G$,
so its return index is $f=t+1$ and its period $f-1=t$.

The full closed assertion is

$$\forall V\text{ finite},\ \forall G\text{ simple on }V,\quad
G\text{ connected}\ \Longrightarrow
\operatorname{Int.ofNat}(\rho_2(G))\leq
\operatorname{Int.ofNat}(|V|)-3.$$

Both casts precede integer subtraction. There is no size lower bound,
nontriviality requirement, edge requirement, periodicity hypothesis or
restriction on intermediate graphs. Isomorphism need not preserve labels;
eventual periodicity is a different assertion.

| Source clause | Lean counterpart | Scope |
| --- | --- | --- |
| Finite simple undirected graph | `V : Type`, `Fintype V`, `SimpleGraph V` in `claim` | All finite orders admitted by connectedness |
| Exact geodesic distance two on the same vertices | `distanceTwo` | Extended distance also handles disconnected iterates |
| Positive isomorphism return to the initial graph | `PositiveReturn` | Strictly positive count and ordinary graph isomorphism |
| Least return, or zero if absent | `strongPeriod` | `Nat.find` on precisely that predicate, otherwise zero |
| Only connectedness is assumed | `claim` | No added size hypothesis |
| Integer upper bound | `claim` | Period and cardinality cast before subtracting three |
| Negation of the entire assertion | `result` | Literally `Not claim`, with no free term or universe parameters |

All declaration names in this table belong to
`D5.S3.Combinatorics.Graph.Walks.DemoStrongPeriodBoundRefutation`.

## Motivation

A universal period bound must include every graph admitted by its stated
hypotheses. The connected singleton tests the lower-order boundary without
changing the operator or the least-return definition. Its fixed-point and
period-one properties are prior mathematics, not a new fixed-point result.

## Gap

The bounded source and literature qualification in #23003 found no global
size condition excluding the singleton and no published resolution of this
exact later bound in the inspected sources. Local order assumptions on cycle
lemmas and on ear or existence results do not supply an unstated global
hypothesis for Conjecture 1. The authors' intended repaired range is unknown.
The qualification is not a worldwide novelty or ownership certificate.

## Route

Take the edgeless graph $K_1$ on a singleton vertex set. It is connected:
every pair of vertices coincides and has a length-zero walk. Its only
self-distance is zero. Consequently $T(K_1)=K_1$, so an identity isomorphism
gives a positive return at $t=1$. Every positive natural count is at least
one; hence the least positive return is exactly one. The zero fallback does
not apply because this return exists.

Substituting $|V|=1$ and $\rho_2(K_1)=1$ gives $1\leq 1-3=-2$, which is false.
This counterexample negates the full universal assertion. These intermediate
equalities are proved in prose here and are local steps inside the Lean
proof of `result`; they are not separately authored public Lean theorems.

The proof directly uses pinned Mathlib's `SimpleGraph.edist_comm`,
`SimpleGraph.edist_self`, `Function.iterate_one`, `SimpleGraph.Iso.refl`,
`Nat.find_spec`, `Nat.find_min'`, `Nat.le_antisymm`,
`Nat.succ_le_of_lt`, `SimpleGraph.Connected.of_subsingleton` and
`Fintype.card_unique`, with integer normalization. No paper theorem is
assumed as an axiom and no conjecture is used as a premise.

## Falsifier

The singleton route would not refute a statement that explicitly excluded
it, used a different return definition, or had an additional global condition
removing it. Such a condition is absent from the qualified v1 target.
A separately stated conjecture restricted to nontrivial graphs or larger
orders requires its own analysis; the counterexample supplies no answer to it.

## Evidence

The kernel-checked settling declaration is
`D5.S3.Combinatorics.Graph.Walks.DemoStrongPeriodBoundRefutation.result`.
It proves the complete closed claim's negation. The four public model
definitions are `distanceTwo`, `PositiveReturn`, `strongPeriod` and `claim`.
Every declaration is honestly classified `proof_shape: bind-only`;
the admission basis is `open-problem-resolution` under #23003, not an
escape-witness claim. The axiom closure of every public declaration is
contained in $\{\mathrm{propext},\mathrm{Classical.choice},\mathrm{Quot.sound}\}$.

The public result is the designated refutation result (`basis=refutes`)
and is exempt from four-slot escape registration (CLAUDE.md §3.9).
There is no additional authored public theorem or escape-audit completion
claim. No experiment is needed for this exact singleton argument.

The prior literature is Erickson et al.,
[arXiv:2409.02306v1](https://arxiv.org/abs/2409.02306v1), Theorem 4.1
(edgeless fixed points) and the proof of Theorem 6.5 (the singleton's period
one). Those are acknowledged literature statements; they are not an imported
Lean theorem on this module's dependency path.

## Triage

- **Singleton mechanism — proved in prose.** The Route derivation establishes
  connectedness, $T(K_1)=K_1$ and $\rho_2(K_1)=1$. The same instance is used
  internally by the kernel-checked `result`; no separate Lean theorem for
  those intermediate facts is claimed.
- **Integer-bound failure — kernel-checked.** `result` negates the whole
  closed universal assertion. The Route explains the contradictory instance
  $1\leq-2$, with casts before subtraction.
- **Old edgeless fixed-point fact — prior literature.** Erickson et al.,
  Theorem 4.1 and the proof of Theorem 6.5, already supply the fixed-point
  and singleton-period facts as literature results. No novelty for them is
  asserted.
- **Missing lower-order condition — proved in prose.** Any valid repaired
  statement retaining this operator and bound must exclude $K_1$ or otherwise
  change the assertion, because the Route supplies a counterexample under
  the original hypotheses. This necessary correction does not establish a
  sufficient repaired order threshold.
- **Nontrivial and larger-order bounds — open.** No separately formulated
  restriction to nontrivial graphs or to larger orders is settled here;
  in particular no uniform repaired bound is proved.
- **Other source results — proved in prose as a scope statement.** Negating
  Conjecture 1 supplies a counterexample to that assertion only. It does not
  negate the source's separately stated cycle, ear or existence theorems.
  Their independent truth is not adjudicated by this result.

## ASSUMED-UNVERIFIED

The source and literature qualification is the bounded, orchestrator-reported
screen in #23003. Absence of unsearched, private, unpublished or all-language
resolutions is unverified. Source author intent for a corrected lower-order
range is unverified. Larger-order variants remain open. No worldwide novelty,
solution credit, final-review clearance, required-CI success or merge is
asserted by this dossier.
