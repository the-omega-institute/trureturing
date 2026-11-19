---
slug: bitonti-hogan-noel-tsarev-2026-question-5-3
bibkey: bitonti2026sidorenko
doi: 10.48550/arXiv.2611.23222
url: https://arxiv.org/abs/2611.23222v1
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/ExtremalDensity/ChenLinFlipLimit.source_fullConvergence
---

# Connected relatively anti-Sidorenko orientations with 3 modulo 4 arcs

## Problem

Veronica Bitonti, Emma Hogan, Jonathan A. Noel and Dmitry Tsarev ask the following in arXiv:2611.23222v1, p. 25.

> Does there exist a connected relatively anti-Sidorenko oriented graph $\vec{H}$ whose number of arcs is congruent to $3$ modulo $4$?

[Question 5.3](https://arxiv.org/html/2611.23222v1#S5.E3)

An oriented graph is loopless and has at most one arc on each unordered pair. Write $U(D)$ for the simple graph obtained by forgetting arc directions and $m=|A(D)|$. The question asks whether there exists a finite oriented graph $D$ with $U(D)$ connected and $m\equiv3\pmod 4$ such that for every finite oriented graph $G$,
$$
2^m\operatorname{hom}(D,G)\leq\operatorname{hom}(U(D),U(G)).
$$
Each homomorphism count includes every adjacency-preserving vertex map, including noninjective maps. Host size is arbitrary, disconnected hosts are allowed, and an empty host gives two zero counts for this nonempty pattern. The connectedness condition applies to the underlying graph of the pattern. [Source definition](https://arxiv.org/html/2611.23222v1#S1.E2) · [Preregistered event](https://github.com/the-omega-institute/trureturing/issues/31481#issuecomment-6980164298)

## Motivation

Section 5 reports examples for every other residue and asks whether the missing residue reflects a general obstruction. It attributes the exclusion of residue three for trees to a personal communication from Jiaxi Nie and Fan Wei. The triangle-free, nonbipartite witness contains the underlying five-cycle 1-3-0-7-2-1 and addresses the unrestricted existence question. The frozen motivation theorem concerns convergence of a tournament path threshold and supplies neighboring homomorphism-density context on complete hosts. [Section 5](https://arxiv.org/html/2611.23222v1#S5) · [Chen–Lin dossier](chen-lin-2026-question-6-1-flip-threshold-limit.md)

## Gap

The issue registers Tier 2 and records a bounded literature screen. The pinned source poses the exact question, and the related Nie–Wei preprint supplies an eight-arc sign gadget and a nine-arc triangle example. The checked sources supply neither a residue-three witness nor the fixed-root construction described below. Section 3.3 of the question source gives a different family of sign constructions. The initial issue discusses tests for three and seven arcs. The submitted nineteen-arc argument uses a direct inequality over hosts of unbounded finite order. [Issue #31481](https://github.com/the-omega-institute/trureturing/issues/31481) · [Bitonti et al., Remark 3.10](https://arxiv.org/html/2611.23222v1#S3.E10) · [Nie–Wei, §5](https://arxiv.org/html/2611.15027v1#S5)

## Route

The pattern uses vertices $0,\ldots,12$. For each terminal $b\in\{1,2\}$, join four private vertices to both $0$ and $b$. Each private vertex realizes one of the four sign pairs below, in the order (terminal $0$, terminal $b$). A plus sign directs the arc from the terminal to the private vertex.

| Terminal $b$ | $(+,+)$ | $(+,-)$ | $(-,+)$ | $(-,-)$ |
| --- | ---: | ---: | ---: | ---: |
| $1$ | $3$ | $4$ | $5$ | $6$ |
| $2$ | $7$ | $8$ | $9$ | $10$ |

Add $1\to2$ and $11\to0\to12$. The sign copies share the root $0$. The underlying graph is connected and the arc count is $8+8+1+2=19\equiv3\pmod 4$.

In a host $G$ with vertex set $V$, let $A(y,z)$ be the arc indicator, $B(y,z)=A(y,z)+A(z,y)$ the adjacency indicator of $U(G)$, $N^+(x),N^-(x)$ the out- and in-neighbors, and $N(x)$ their disjoint union. At fixed root image $x$, set
$$
C_x(y)=|N(x)\cap N(y)|,\qquad
P_x(y)=\prod_{\sigma,\tau\in\{+,-\}} |N^\sigma(x)\cap N^\tau(y)|.
$$
For one copy with terminal images $x,y$, the directed extension count is $P_x(y)$ and the undirected count is $C_x(y)^4$. The four sign-class intersections partition $N(x)\cap N(y)$, giving $2^8P_x(y)\le C_x(y)^4$ by AM–GM. This also covers coinciding terminal images and empty sign classes. The private choices are independent after fixing the terminal images, and distinct private vertices may have the same image. [Nie–Wei, Definition 3](https://arxiv.org/html/2611.15027v1#Thmdefinition3) · [Equation (18)](https://arxiv.org/html/2611.15027v1#S5.E18)

Both copies give the same profile $P_x$ when $x$ is held fixed. Interchanging the two free terminal images yields
$$
2\sum_{y,z\in V} A(y,z)P_x(y)P_x(z)
 =\sum_{y,z\in V} B(y,z)P_x(y)P_x(z).
$$
Apply the pointwise bound to both factors on the right with nonnegative weights $B(y,z)$. This gives the factor $2^{17}$ with the root image fixed. If $d^+(x),d^-(x)$ denote the two directed degrees, the added path contributes $d^+(x)d^-(x)$ to the directed count and $(d^+(x)+d^-(x))^2$ to the undirected count. The second expression is at least four times the first. The directed and undirected counts with root image $x$ are exactly the respective terminal sums times these path factors. Multiplying the bounds and summing over $x$ gives the universal factor $2^{19}$.

## Falsifier

A finite loopless oriented host with $2^{19}\operatorname{hom}(D,G)>\operatorname{hom}(U(D),U(G))$ would reject this witness. An arc-list error affecting connectedness or the arc count would also reject this witness. A negative answer to Question 5.3 would require a violating finite host for every connected oriented pattern in the residue class.

## Evidence

The pinned arXiv v1 source supplies the wording and Definition 1.2. The issue description quotes part of the source sentence. The preregistration comment states the complete quantified mathematical event. The Lean theorem `question_5_3` quantifies existentially over the finite pattern order and supplies a pattern with thirteen vertices and nineteen arcs. Its proof establishes the exact two homomorphism counts by splitting and reconstructing the maps. It uses the edge count of the underlying pattern in the rational form of Definition 1.2. For an oriented graph each underlying edge has exactly one arc above it, giving the equivalent cleared inequality. [Primary PDF](https://arxiv.org/pdf/2611.23222v1) · [Issue description](https://github.com/the-omega-institute/trureturing/issues/31481) · [Preregistered event](https://github.com/the-omega-institute/trureturing/issues/31481#issuecomment-6980164298)

## Triage

- **Proved in Lean.** The thirteen-vertex orientation with nineteen arcs satisfies the relative anti-Sidorenko inequality for every finite oriented host.
- **Literature-attested.** Nie–Wei's $t=2$ copy uses the four sign classes. Their nine-arc example symmetrizes an edge between the gadget's own two terminals. This construction duplicates the gadget, shares a root, and interchanges the two other terminals while keeping the root image fixed. [Nie–Wei, proof of Proposition 1.8](https://arxiv.org/html/2611.15027v1#S5)
- **Open here.** The least possible arc count in the target residue and the tree classification asked for in Problem 5.2. [Section 5](https://arxiv.org/html/2611.23222v1#S5)

## ASSUMED-UNVERIFIED

The bounded literature screen leaves worldwide priority and the contents of the personal communication cited as reference [29] unverified.
