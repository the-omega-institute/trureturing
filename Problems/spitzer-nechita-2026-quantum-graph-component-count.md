---
slug: spitzer-nechita-2026-quantum-graph-component-count
bibkey: spitzernechita2026quantumgraph
doi: 10.22331/q-2026-10-06-2228
url: https://arxiv.org/abs/2603.23651v3
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Matrix/QuantumGraphStrangeComponentCount.result
---

# The component count is the graph count plus loop-free strange components

## Problem

G. L. Spitzer and I. Nechita, *Quantum Graph Theory by Example*, arXiv:2603.23651v3 [math.OA, cross-listed math-ph, quant-ph] (Quantum 10, 2228, 2026), leave the component-count question in the conclusion. The source text states in `content/conclusion.tex`, line 8:

> It would be interesting to determine the exact number of connected components of $X_{A, \ccdot, C}$ in terms of $\mathfrak{G}(A, C)$, and in particular to understand the role played by isolated strange edges with phase $\pi$.

The paper defines the strange graph $\mathfrak{G}(A,C)$ from the nonzero two-vertex blocks of a quantum graph of the form $X_{A,B,C}$. The formal module fixes the $B=\operatorname{diag}A$ reading through the following declarations. For $A,C : \operatorname{Mat} n$ and $d : \operatorname{Fin} n \to \mathbb C$, `realignedProjector A C d` is the matrix with diagonal-coordinate entries $d$ and off-diagonal blocks determined by $A$ and $C$, and `adjacency A C d` is the linear map obtained from that realigned matrix. `HasComponents G k` means that there are $k$ nonzero star projections summing to the identity whose cross terms $P_s G(P_t Z)$ vanish for every $s \ne t$ and every $Z$. `underlyingGraph A C` has an edge exactly when the corresponding off-diagonal entry of $A$ or $C$ in either direction is nonzero. `IsLoopFreeStrangeComponent A C d Q` says that a connected component $Q$ has support $\{i,j\}$ for distinct vertices, is adjacent, has $A_{ij}=1/2$, and has $d_i=d_j=0$. The two counts are `graphComponentCount A C` and `loopFreeStrangeComponentCount A C d`, the latter counting such components.

The Lean `claim` quantifies over every natural $n$, every $A,C : \operatorname{Mat} n$, and every $d : \operatorname{Fin} n \to \mathbb C$. Under $A_{ii}=d_i$, $C_{ii}=d_i$, Hermiticity and idempotence of `realignedProjector A C d`, and Hermiticity of `offDiag A`, it asserts that the set of $k$ for which `HasComponents (adjacency A C d) k` holds has greatest element `graphComponentCount A C + loopFreeStrangeComponentCount A C d`.

## Motivation

The source relates connectedness of $X_{A,B,C}$ to connectedness of its strange graph and exhibits a disjoint union of strange edges with phase $\pi$ whose quantum graph has twice as many components as the strange graph (the construction is in `content/graphtheory/conncomp.tex`, lines 247--254). An exact formula for the $X_{A,\cdot,C}$ family identifies which local blocks create the extra quantum components and whether the phase itself is responsible. The settlement supplies that formula in the formal model and separates the exceptional two-vertex, loop-free case from all other connected components.

## Gap

The bounded check recorded in [issue #20910](https://github.com/the-omega-institute/trureturing/issues/20910) reports that the arXiv versions retain the conclusion question, that OpenAlex and Crossref report no citing works for this question, that MathDB has no record for it, and that `google-deepmind/formal-conjectures` has no entry. The repository had no prior issue or module for this connected-component count.

`not-found-in-searched-scope`.

## Route

1. **Block classification.** From Hermiticity of the realigned projector and of `offDiag A`, together with idempotence, the proof classifies each off-diagonal block as zero, a classical block with $A_{ij}=1$, or a rank-one strange block with $A_{ij}=1/2$ and $C_{ij}C_{ji}=1/4$. This also shows that every edge in `underlyingGraph A C` has nonzero $A_{ij}$.

2. **Commutant reduction.** The columns of the realigned projector give a Kraus representation of `adjacency A C d`. A Gram-sum argument turns the separating condition in `HasComponents` into commutation of each resolving projection with every column. Thus the greatest-component problem becomes a commutant-resolution problem.

3. **Upper bound.** Commutant diagonals are constant on components. For commuting Hermitian $P$, $P_{ij}\ne0$ ($i\ne j$) forces $i$ into a loop-free strange component if it has a neighbor. Select one vertex per component and both endpoints of exceptional components. Isolated vertices are singleton components, each retained as one dimension. Off-diagonals incident to omitted vertices vanish; compression yields nonzero idempotents summing to identity, hence $k\le c+s_0$.

4. **Attainment.** The projection onto each graph component commutes with all Kraus columns. For every loop-free strange component, a square root of the phase produces a rank-one edge projection; its complement inside the component projection is another nonzero commuting projection. Splitting precisely those components yields a resolution indexed by all graph components plus one extra index for each exceptional component, so the bound is attained and the `IsGreatest` statement follows.

## Falsifier

The result would not settle the source question if the formal objects differed from the source's $X_{A,\cdot,C}$ or strange graph. A faithful check must therefore preserve:

- the realignment convention used by `realignedProjector` and the induced Kraus map `adjacency`;
- the exact `HasComponents` quantifiers, including nonzero star projections, their sum being the identity, and the all-$Z$ cross-term condition;
- the `underlyingGraph` edge predicate and the exact support, $A_{ij}=1/2$, and endpoint-diagonal conditions in `IsLoopFreeStrangeComponent`;
- the fact that `claim` proves an `IsGreatest` value, hence both an upper bound and an attained resolution, for every $n,A,C,d$ satisfying all five hypotheses.

The formal claim does not separately assume that $d$ is a binary vector or that a phase is $\pi$; adding such assumptions would change the proposition. A numerical check of a finite family would establish nothing about other matrices or sizes.

## Evidence

The canonical source is `D5/S3/Quantum/Matrix/QuantumGraphStrangeComponentCount.lean` (986 lines).
- **Proof.** It proves `result : claim`.
- **Axioms.** It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.

Frozen state: `Golden/Frozen/state/D5/S3/Quantum/Matrix/QuantumGraphStrangeComponentCount.lean.json`, statement `sha256:986cd1a54ffe6126278ee3583d78df2092930ec3f573320dd2c084bf34ed3cf2`.

Declaration statements:
- `result`: `sha256:9f8dc4c86031a5cc7e2734ac8d378c6160c8e9611c9f347b4f5d358b03987c04`;
- `claim`: `sha256:c40f5457501a0fac36dc0be9046b1f65e34ceba3b3c87ef50815dc363a595ae5`.

## Triage

Tier 1 closing question of a 2026 paper, preregistered in issue #20910 before any Lean.
`theorem`; resolution `proved`.

The module is admitted under the open-problem-resolution basis of CLAUDE.md §3.2; the per-declaration proof shapes are listed in the delivery PR. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** For every $n$, $A$, $C$, and $d$ satisfying the five hypotheses in `claim`, the greatest $k$ for which `HasComponents (adjacency A C d) k` holds is exactly `graphComponentCount A C + loopFreeStrangeComponentCount A C d`.

**Hand computation from the definitions, not formalized:** for the disjoint union of $m$ strange edges without loops (the source's doubling example, `content/graphtheory/conncomp.tex` l. 247–254, for every phase), $c=m$ and $s_0=m$, so the formula gives $2m$ components, matching the source's count $n=2m$.

**Argued, not formalized.**

- **Mechanism.** The attaining resolution uses one component projection on each nonexceptional component and splits each loop-free strange pair into two rank-one phase eigenspaces. The phase enters the eigenvectors but not the number of eigenspaces, so every phase has the same count in this exceptional case.
- **Sharpness and nearby cases.** The `IsGreatest` conclusion includes an explicit commuting resolution attaining the upper bound. A connected component with more than two vertices, a classical edge component, or a strange pair with a nonzero endpoint diagonal has no additional summand in the formula. The predicate `IsLoopFreeStrangeComponent` is the exact boundary used by the theorem.
- **Effect on the source.** Within this formal reading, the source's phase-$\pi$ disjoint-edge example is the case in which every component is exceptional, so the formula explains the doubling. The source's broader $X_{A,B,C}$ questions with a nontrivial $B$, and its separate clique, colouring, and quantum-symmetry questions, are unaffected. The source's earlier connectedness and lower-bound propositions remain compatible with this exact count.

## ASSUMED-UNVERIFIED

The literature check is bounded to the records reported in issue #20910 and does not establish exhaustive worldwide novelty, priority, or the absence of an unpublished settlement. The direct source reading covered arXiv v3, including `content/conclusion.tex`, `content/graphtheory/conncomp.tex`, `content/groupactions.tex`, and `content/prelims.tex`; the source-to-Lean correspondence beyond the declarations in this module is not independently formalized. The phase-convention comparison mentioned in the preregistration, the source's full $X_{A,B,C}$ definitions, and the source's other propositions are not separate declarations here. The hand computation and the arguments in “Argued, not formalized” are not formalized as independent results.
