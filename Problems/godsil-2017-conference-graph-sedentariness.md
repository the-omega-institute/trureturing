---
slug: godsil-2017-conference-graph-sedentariness
bibkey: godsil2021sedentary
doi: 10.1016/j.laa.2020.08.027
url: https://arxiv.org/abs/1710.11192v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Dynamics/ConferenceGraphSedentariness.result
---

# Sharp return-probability bounds for conference graphs

## Problem

Chris Godsil, *Sedentary quantum walks*, arXiv:1710.11192v1 (2017; Linear Algebra and its Applications 614 (2021), 356–375), Section “Questions?”, TeX source `conemix.tex`, lines 1037–1038:

> We do not know whether, for conference graphs, the diagonal entries of $M(t)$ can be
> bounded away from zero.

In the Introduction, `conemix.tex`, lines 190–207, Godsil defines $U(t)=\exp(itA)$ for the adjacency matrix $A$ and $M(t)=U(t)\circ\overline{U(t)}$, where $\circ$ is the Schur product. Thus $M(t)_{u,u}=|U(t)_{u,u}|^2$.

Issue [#26302](https://github.com/the-omega-institute/trureturing/issues/26302) fixes the reading as a sharp classification, distinguishing a positive bound for each fixed graph from a bound uniform across orders. Write $n=4m+1$, with $m\in\mathbb N$ and $m\ge1$. The module takes a finite vertex type $V$ with decidable equality and a simple graph $G$ with decidable adjacency satisfying `G.IsSRGWith (4 * m + 1) (2 * m) (m - 1) m`. This means that $|V|=n$, every vertex has degree $2m$, adjacent vertices have $m-1$ common neighbours, and distinct nonadjacent vertices have $m$ common neighbours. For $u\in V$, put $p_u(t)=|\exp(itA)_{u,u}|^2$.

The classification gives a sharp positive bound $1/n^2$ exactly at square orders; at nonsquare orders, return probabilities become arbitrarily small at positive times. Its precise quantified statement is given under “Proved by `result`”.

## Motivation

Godsil's Section “Other Strongly Regular Graphs”, `conemix.tex`, lines 1009–1023, discusses a lower bound for the diagonal of the average mixing matrix and explains that it provides no useful bound for the instantaneous diagonal entries in the conference-graph case. The question concerns instantaneous return probability, rather than its time average. A sharp answer distinguishes graphs whose return probability stays uniformly positive in time from graphs admitting arbitrarily small returns, and distinguishes either behaviour from concentration near one as the order grows.

## Gap

The bounded literature check recorded in #26302 covers the original arXiv version, citing works and recent sedentariness papers. The arXiv submission listing has only v1, and its TeX retains the question.

A known partial answer must be separated from the sharp classification. Karen Meagher, Hermie Monterde and Tung T. Nguyen, *Sedentariness in Cayley graphs* (2026), arXiv:2611.00567v1, `final_version.tex`, lines 924–926, state:

> Let $\Gamma$ be a connected, integral, walk-regular graph with valency $d$. If the multiplicity of each $\lambda\in\sigma(\Gamma)\backslash\{d\}$ is a multiple of some integer $q\geq 2$, then $\Gamma$ is sedentary.

Their Theorem `thm:C`, lines 1014–1016, also gives an explicit positive amplitude bound under its necklace-polynomial hypothesis. The application to square-order conference graphs is explained below. This already supplies positivity in that case; positivity alone is not the remaining gap.

The sharp value $1/n^2$, its attainment, the nonsquare arbitrarily-small-value clause and the bound for all sufficiently large orders were not located in the checked scope. The other citing-work readings and repository searches are reported in #26302 rather than independently reproduced here.

`not-found-in-searched-scope` for the sharp classification, not for square-order positivity alone.

## Route

For every graph step below, fix $m\in\mathbb N$ with $m\ge1$, a finite vertex type $V$ with decidable equality, a simple graph $G$ with decidable adjacency and `G.IsSRGWith (4 * m + 1) (2 * m) (m - 1) m`. Write $n=4m+1$, $A=G.\mathrm{adjMatrix}\,\mathbb C$, $I$ for the identity matrix and $J$ for the all-ones matrix.

1. **Adjacency identity.** `conference_identity`, under these hypotheses, gives $A^2=mI-A+mJ$.
2. **Three idempotents.** Set $r=\sqrt n$, $\theta=(-1+r)/2$, $\tau=(-1-r)/2$, $P=J/n$, $Q=I-P$, $B=A-2mP$, $E=(B-\tau Q)/r$ and $F=(\theta Q-B)/r$. Under the same graph hypotheses, `conference_projectors` gives idempotence of $P,E,F$, zero products in both orders between distinct members, $P+E+F=I$, $A=2mP+\theta E+\tau F$, and, for every $u\in V$, $P_{u,u}=1/n$ and $E_{u,u}=F_{u,u}=(n-1)/(2n)$.
3. **Return formula.** For finite $V$ with decidable equality, complex matrices $P,E,F$ satisfying those idempotence, both-sided zero-product and sum hypotheses, and arbitrary complex scalars $a,b,c$, `three_projector_exp` gives $\exp(aP+bE+cF)=e^aP+e^bE+e^cF$. Applied to the projectors above, `conference_walk` gives the diagonal amplitude for every vertex $u$ and real time $t$. With the standing graph hypotheses, `return_formula` gives
   $p_u(t)=n^{-2}\left|e^{int/2}+(n-1)\cos(\sqrt n\,t/2)\right|^2$
   for every $u\in V$ and $t\in\mathbb R$.
4. **Square lower bound.** `odd_cos_bound` states $|\cos(qx)|\le q|\cos x|$ for every odd natural $q$ and every real $x$. With $m\ge1$ and the additional hypothesis that $4m+1$ is a square, `square_lower` bounds the squared norm in the numerator of `return_formula` below by $1$ for every real $t$. Indeed, writing $n=q^2$ gives odd $q\ge3$; with $a=n-1$ and $x=qt/2$, the numerator is at least $1+a(a-2q)\cos^2x\ge1$. Together with `return_formula` under the standing graph hypotheses, this gives $p_u(t)\ge1/n^2$.
5. **Attainment at every order.** Under the standing graph hypotheses and for each vertex $u$, `floor_attainment` gives a positive time with $p_u(t)=1/n^2$. Its witness is $t=\pi/\sqrt n$, which makes the cosine zero. The lemma requires no square-order hypothesis; in the square case it attains the lower bound.
6. **Nonsquare small values.** For $m\ge1$, nonsquare $4m+1$ and every real $\varepsilon>0$, `nonsquare_small` makes the scalar expression in `return_formula` smaller than $\varepsilon$ at a positive time. It uses irrationality of $\sqrt n$ and density of integer multiples of $2\pi/\sqrt n$ on the circle. The continuous function $(1+(n-1)\cos z)^2/n^2$ vanishes at $z=\arccos(-1/(n-1))$ and equals $1$ at zero. Density supplies a nonzero integer $j$ with value below $\min(\varepsilon,1)$; $t=4\pi|j|/n>0$ realizes that value. With `return_formula` and the standing graph hypotheses, this gives the nonsquare clause of `claim`.
7. **Growing orders.** For every real $c>0$, `family_small` chooses $N\in\mathbb N$ with $N>\max(1,1/c)$. For every $m\ge1$ with $N\le4m+1$ and every graph and vertex satisfying the standing hypotheses, `floor_attainment` supplies a positive time with $p_u(t)=1/n^2<c$. This proves the family clause without a square-order restriction.

## Falsifier

The settlement would not answer the source question if the walk convention, graph predicate or time quantifiers differed. The module uses `ProjectionProbabilityFlow.hamiltonianPropagator A (-t)`. That propagator is defined as $\exp(-isA)$ at argument $s$, and `RationalWeightPathTransfer.hamiltonianPropagator_neg`, for a finite vertex type with decidable equality, any complex matrix $A$ and real $t$, identifies its value at $-t$ with $\exp(itA)$.

The strongly regular predicate includes the vertex count as well as the common-neighbour counts. The restriction $m\ge1$ excludes order one and makes $0<2m<n-1$, so the complete and empty degeneracies do not enter. The square lower bound is for every real time; attainment and arbitrarily small values use strictly positive times. The family clause quantifies over every graph of each sufficiently large admissible order and every vertex, with the existential time inside those quantifiers. It does not assert existence of conference graphs at any prescribed order or at unbounded orders.

## Evidence

The canonical source is `D5/S3/Quantum/Dynamics/ConferenceGraphSedentariness.lean`.

- **Proof.** It defines `claim : Prop` and proves `result : claim`.
- **Axioms.** It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.

Frozen state: `Golden/Frozen/state/D5/S3/Quantum/Dynamics/ConferenceGraphSedentariness.lean.json`.

Declaration statements:

- `result`: `sha256:4c7c3d6a97e9501e4accb5465460498cf030b105033ac5b2dace1e2ef698c1b7`;
- `claim`: `sha256:68a0f8dabec9e80fb61245649251221ecf6e9ebe1ee3f5079e0a367c72431a29`.

## Triage

Tier 1 question of a 2017 preprint published in 2021, preregistered in issue #26302 before any Lean.
`theorem`; resolution `proved`.

The module is admitted under the open-problem-resolution basis of CLAUDE.md §3.2. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** for every natural $m\ge1$, every finite vertex type with decidable equality, every simple graph with decidable adjacency and strongly regular parameters $(4m+1,2m,m-1,m)$, and every vertex $u$, writing $n=4m+1$:

- if $n$ is a square, $p_u(t)\ge1/n^2$ for every real $t$, and $p_u(t)=1/n^2$ at some positive real time;
- if $n$ is nonsquare, $p_u(t)\ge0$ for every real $t$, and for every real $\varepsilon>0$ there is a positive real time with $p_u(t)<\varepsilon$.

Also, for every real $c>0$ there is $N\in\mathbb N$ such that, for every natural $m\ge1$ with $N\le4m+1$, every finite vertex type with decidable equality, every simple graph with decidable adjacency and strongly regular parameters $(4m+1,2m,m-1,m)$, and every vertex $u$, there is a positive real time with $p_u(t)<c$.

**Computed, not formalized:** None.

**Argued, not formalized.**

- *Infimum interpretation and sharpness.* For every graph and vertex in `result`, the set $S_u=\{p_u(t):t>0\}$ is nonempty, since $t=1$ is permitted, and bounded below by zero, since its elements are squared norms. In the square case, $1/n^2$ is a lower bound and belongs to $S_u$, so it is the minimum and infimum. In the nonsquare case, zero is a lower bound and every proposed positive lower bound is contradicted by the corresponding $\varepsilon$ clause, so the infimum is zero. These are order-theoretic consequences of the quantified statement; the module contains no separate infimum declaration.
- *The known square-order partial answer.* For the graphs quantified in `result`, additionally assuming square order $n=q^2$ with natural $q$, any two nonadjacent distinct vertices have $m>0$ common neighbours, so the graph is connected. Here $q$ is odd and $q\ge3$. Under these graph hypotheses, `conference_projectors` decomposes $A$ into idempotents with zero mutual products summing to $I$, with respective scalars $2m,(-1+q)/2,(-1-q)/2$. These scalars are distinct integers. The ranges of the idempotents therefore give the corresponding eigenspaces. Their constant diagonal entries make every diagonal entry of every power of $A$ constant, giving walk-regularity. For an idempotent its trace is its rank, so summing these diagonal entries gives both nonprincipal multiplicities $(q^2-1)/2$, divisible by $4$ because an odd square is $1$ modulo $8$. Thus the hypotheses of Meagher–Monterde–Nguyen's quoted theorem apply. This explains the overlap with existing literature; the sharp minimum and its attainment are additional conclusions here. This spectral application of that external theorem is not separately formalized.
- *Scope of the scalar mechanism.* If another walk has the same diagonal amplitude up to a complex factor of norm one, its return probability is identical: $|\zeta z|^2=|\zeta|^2|z|^2=|z|^2$ when $|\zeta|=1$. It therefore has the same classification whenever its parameters satisfy the same order conditions. Establishing that amplitude representation for any additional graph family remains a separate obligation; walk-regularity by itself does not supply the representation.
- *The family reading.* For any family of these conference graphs with unbounded realized orders, a positive lower bound uniform over the family contradicts the last clause of `result`: choose a member beyond the corresponding $N$ and the supplied positive time. Existence of such an unbounded family is an additional premise, not a conclusion of the Lean statement.
- *Neighbouring questions.* Whether zero is attained at nonsquare orders, quantitative bounds on a time achieving a prescribed small return, and a classification for general walk-regular graphs remain open in this settlement. The arbitrarily-small-value clause alone supplies neither attainment of zero nor a bound on the required time.
- *Effect on the source.* In Godsil's v1 TeX, the conference-graph question is posed in the closing section, and no theorem is stated conditionally on an affirmative answer. The settlement resolves that question by separating square and nonsquare orders. It supplies no revision of the source's average-mixing or off-diagonal theorems. The adjacent closing request to extend the results to walk-regular graphs remains broader than the conference-graph classification.

## ASSUMED-UNVERIFIED

The literature check is bounded and does not establish exhaustive worldwide novelty or priority. Godsil's arXiv v1 question and walk convention, and the quoted theorem and explicit-bound statement in Meagher–Monterde–Nguyen, arXiv:2611.00567v1, were checked in their TeX sources. The other literature readings reported in #26302 were not independently reproduced: arXiv:1711.08831v4, 2207.05168v2, 2303.06297v3, 2402.15878v2, 2307.01963v3, 2308.16378v1, 2401.00362v1, 2402.07078v3, 2601.18964v2, 2610.10017v1 and Monterde's 2025 thesis. The reported OpenAlex citation listing and repository-wide issue searches were not reproduced. The published 2021 journal text was not compared with the arXiv version.

The statements under “Argued, not formalized” are not additional Lean declarations. No existence construction, quantitative return-time estimate, nonsquare zero-attainment result, Laplacian-walk statement, general strongly-regular or walk-regular classification, off-diagonal statement or average-mixing statement is formalized by this settlement.
