---
slug: fresan-figueroa-goldfeder-lozano-2026-mutual-visibility-maximal-connectivity
bibkey: fresanfigueroa2026mutualvisibility
doi: 10.48550/arXiv.2610.24324
url: https://arxiv.org/html/2610.24324v1
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/Graph/MutualVisibility/MinimumPair.result
---

# Maximal connectivity of full mutual-visibility reconfiguration graphs

## Problem

Julián A. Fresán-Figueroa, Ilán A. Goldfeder and Aldo Lozano-Piña,
*Reconfiguration graphs of mutual-visibility sets*, arXiv:2610.24324v1,
Section 3.3 immediately after Theorem 3.6, asks:

> A natural question is whether $\mathcal{R}_{\mathcal{M}}(G)$ is maximally connected for every connected $G$, that is, whether $\kappa(\mathcal{R}_{\mathcal{M}}(G))=\delta(\mathcal{R}_{\mathcal{M}}(G))$ holds, where $\delta$ denotes minimum degree?

This dossier anchors exactly this question, repeated in Section 7. The source's
standing convention is finite, simple, undirected, connected graphs. Connected
hosts are nonempty; orders one and two are included. The preceding theorem's
order-at-least-three hypothesis does not restrict the question.

For every distinct selected pair, some shortest path in the original host
must avoid the other selected vertices. Different pairs may use different
paths. The configuration graph contains every feasible subset, including empty
and all feasible cardinalities. Distinct configurations $S,T$ are adjacent
when $|S\mathbin{\triangle}T|=1$, or when $S\setminus T=\{x\}$,
$T\setminus S=\{y\}$ and $xy$ is an actual host edge. Thus a slide replaces
an occupied vertex by an unoccupied neighbor.

### Statement echo

| Source clause | Lean counterpart |
| --- | --- |
| Every finite nonempty simple undirected host | `V`, `[Fintype V]`, `[DecidableEq V]`, `[Nonempty V]`, `H : SimpleGraph V` in `FullMaximalConnectivityClaim` |
| Connected, with no order or rank restriction | `H.Connected` is the only graph hypothesis |
| Some original-host geodesic avoids the other selected vertices | `Visible` uses an existential `H.Walk` of length `H.dist`; shortest walks are paths |
| All feasible subsets, including empty | `Configuration H` is the subtype of all visible `Finset V` |
| Addition/removal and actual host-edge slides | The two disjuncts of `MixedMove`, used by `reconfiguration` |
| Standard vertex connectivity | `Separates` deletes to at most one vertex or to an induced graph that is not preconnected; `vertexConnectivity` minimizes cut size |
| Equality to minimum degree | `result : FullMaximalConnectivityClaim` |

The separator convention gives $\kappa(K_q)=q-1$ for every positive $q$;
`Connectivity.connectivity_complete` verifies this convention. No geodesic,
separator, sparse-slide, girth or diameter premise is added to the conclusion.

## Motivation

The settling declaration is
`D5/S3/Combinatorics/Graph/MutualVisibility/MinimumPair.result`.
Its Scribe attaches this dossier's single `OpenProblemResolutionClaim(Proved)`.
The [Library note](../Library/GraphInvariants/fresanfigueroa2026mutualvisibility.md)
records the primary definitions and literature attribution.

The target is the entire mixed graph. Fixed-cardinality, slide-only, path-host,
complete-host or finite-census results would not answer it. The known hereditary
visibility property is credited to Proposition 2.1 and Cicerone et al. (2023).

## Gap

The source proves $3\leq\kappa(\mathcal{R}_{\mathcal{M}}(G))\leq n$ for
connected hosts of order $n\geq3$ and settles equality for its extremal host
families. It asks for equality with actual minimum degree for every host.
Slide edges can raise minimum degree beyond that of the hereditary add/remove
skeleton, so connectivity of that skeleton alone does not supply this bound.

Preregistration [#21882](https://github.com/the-omega-institute/trureturing/issues/21882)
quotes this full event as a tier-1 recent structural question on a research line.
Bounded repository, pinned-Mathlib, third-party and literature searches
authenticated no exact existing solution or direct binding. A separate
independent source check found only v1 on the arXiv abstract page, one exact
mutual-visibility/reconfiguration search record (the source), and no
authenticated full solution among 30 Crossref title-query records. These are
bounded nonfindings, not a global novelty or priority certificate.

## Route

Names below are in `D5.S3.Combinatorics.Graph.MutualVisibility`; a module
qualifier identifies the source file when a helper is private.

1. `SingletonCore.minDegree_le_host_order` uses the empty configuration's
   degree. A cut smaller than minimum degree is smaller than host order.
   `CleanRoots.exists_cleanRoot` supplies a root, and
   `SingletonCore.singleton_core` joins all surviving singletons.
2. `CyclicIntervals.high_rank_component` excludes a stranded component
   containing only configurations of size at least three. Cubes of feasible
   subsets and disjoint cyclic deletion paths pay for deletion, addition and
   actual slide neighbors from the same cut. Thus a stranded component has
   a pair whose endpoint singletons are cut.
3. `RootComparability.stranded_pair_comparable` orders a stranded pair by
   mandatory root ancestry, meaning membership on every root geodesic. This
   auxiliary relation does not replace existential visibility. Choose a
   reachable pair minimizing the sum of its endpoint distances to the root.
4. `MinimumPair.minimum_pair_local_bound` pays for neighbors associated with
   each outside label using a local cut class. There are at most two slides
   and one addition per outside label. A nonvisible triple with two slides
   yields a closer replacement pair; minimality forces a cut payment. A
   visible triple cannot have all three pair faces stranded, because their
   rooted comparabilities contradict its visibility.
5. A surviving visible triple with two actual slides is the remaining local
   deficit. `PairPayments` uses one fixed inward predecessor for the chosen
   pair to assign distinct extra cut configurations. Each has two labels
   outside the pair, separating these payments from every local class and the
   internal class. `MinimumPair.minimum_pair_degree` sums payments for the
   same host, cut, component and predecessor, proving pair degree at most
   cut size.
6. `MinimumPair.stranded_component_impossible` contradicts cut size below
   minimum degree. Every survivor therefore reaches the same root singleton.
   `result` combines this preconnectedness with generic separator inequalities.

Separately optimized local budgets would not justify the joint degree bound.
Rooted comparability and simultaneous same-cut payments supply the synthesis;
the source definitions, hereditary property and known extremal cases retain
their original credit.

## Falsifier

A counterexample would be a finite nonempty connected simple undirected host
and a cut in its full mixed configuration graph smaller than minimum degree,
leaving at most one configuration or a disconnected survivor graph. Feasibility
must use original-host shortest paths, and every legal addition, removal and
actual host-edge slide must be retained. `result` excludes this configuration.
A disconnected fixed layer or restricted move graph would not falsify it.

## Evidence

The nine Lean modules and Scribe mirrors are in
`D5/S3/Combinatorics/Graph/MutualVisibility/` and its `Blueprint/` mirror.
The endpoint is `MinimumPair.result : FullMaximalConnectivityClaim`.
The scoped report covers the entire import closure. Every declaration's
axiom closure is contained in
$\{\mathrm{propext},\mathrm{Classical.choice},\mathrm{Quot.sound}\}$,
with no `sorryAx`.

Only `MinimumPair.lean` is registered through `deposit-uncovered`; supporting
closed imports, including `Model`, remain unregistered. There is no matching
theory volume or atom. First-freeze admission is `escape-witness`; the result's
proof shape is `content`. The distinct intermediate estimate is
`MinimumPair.minimum_pair_local_bound`, used by `minimum_pair_degree`, then
`stranded_component_impossible`, then `result`. There are no direct
baseline-frozen D5 dependencies.

Information-escape audit
[#22007](https://github.com/the-omega-institute/trureturing/issues/22007)
is unfinished. Whole-family variation, per-role sensitivity, actual
observational dependence, faithful lower-connectivity reconstruction,
`sourceSelection` and exact source-state identity, and lawful current
registration binding remain missing. No Reg mirror or `declared_validated`
registration is asserted.

## Triage

### What the settlement shows

- **Proved, `MinimumPair.result`:** the full original equality holds for all
  finite nonempty connected hosts and all feasible configurations, with both
  move types. Small hosts and the standard complete-graph convention are
  included. The theorem identifies minimum separator size with minimum
  degree; it does not classify every minimum separator.
- **Proved, `MinimumPair.minimum_pair_local_bound` and its consumers:** rooted
  comparability and simultaneous inward payments absorb extra slide degree
  using one actual cut. No global star-forest or sparse-slide assumption is
  needed. Actual visibility supplies essential geodesic structure; no
  extension to an arbitrary hereditary family is asserted.
- **Proved, `SingletonCore.minDegree_le_host_order`:** minimum degree is at
  most host order. Together with equality this bounds vertex connectivity.
  The source's $3\leq\kappa\leq n$ bound for $n\geq3$ and its extremal
  families remain valid with their original credit.
- **Open, untested successor from Section 7:** characterize the finite
  nonempty connected hosts for which every nonempty fixed-cardinality
  mutual-visibility layer is connected. Precisely, for every
  $0\leq k\leq |V(G)|$ admitting a feasible $k$-set, the induced slide graph
  on all feasible $k$-sets must be connected. A characterization must prove
  necessity and sufficiency, preserve original-host geodesic feasibility and
  actual edge slides, and handle isolated maximum layers. The present theorem
  permits changes of cardinality and supplies no fixed-layer conclusion.
  No successor proof, probe or resolution binding is included here.

The source's fixed-layer reachability, layer-component counting and mobility
questions remain separate. No consequence here asserts that connected layers
cover the host. Only the full mixed maximal-connectivity question is anchored
by this dossier.

## ASSUMED-UNVERIFIED

Global literature absence, exhaustive citing-work coverage and historical
priority are unverified. Some arXiv API, OpenAlex and Semantic Scholar searches
returned access or rate-limit failures. The 2023 attribution is verified from
the primary paper's Proposition 2.1 and bibliography, without an independent
reading of the 2023 full text. Audit #22007 remains unfinished. Independent
final triplet review, exact-head required CI and delivery to `dev` are separate
publication requirements; no merged-delivery or KPI credit is asserted here.
