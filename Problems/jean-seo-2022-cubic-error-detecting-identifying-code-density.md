---
slug: jean-seo-2022-cubic-error-detecting-identifying-code-density
bibkey: jeanseo2022errordetection
doi: 10.48550/arXiv.2208.06052
url: https://arxiv.org/abs/2208.06052v1
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/Graph/Domination/JeanSeoCubicErrorDetectingCode.result
---

# A connected cubic counterexample to Jean–Seo Conjecture 1

## Problem

Jean and Seo, *Optimal Error-detection system for Identifying Codes*, arXiv:2208.06052v1, Section 4.2.2, Conjecture 1:

> For a cubic graph G, DET:IC%(G) ≥ 3/4.

The source explicitly defines density for finite graphs. Its Theorem 2.1 characterizes a DET:IC by two-domination and asymmetric two-separation. The source statements and locators are in [the Library note](../Library/GraphInvariants/jeanseo2022errordetection.md). Issue [#19618](https://github.com/the-omega-institute/trureturing/issues/19618) preregisters the finite connected reading.

### Statement echo

| Source clause | Lean counterpart | Scope |
| --- | --- | --- |
| $N[u]=N(u)\cup\{u\}$ and $N_S[u]=N[u]\cap S$ | `closedDominators` | Closed neighborhood, intersected with the finite detector set. |
| Every vertex is at least 2-dominated | First conjunct of `IsDETIC` | At least two closed detectors at every vertex. |
| Distinct vertices are 2#-distinguished | Second conjunct of `IsDETIC` | Either directed neighborhood difference has cardinality at least two. |
| Cubic graph | `SimpleGraph` and `IsRegularOfDegree 3` in `claim` | Finite simple graph; degree three everywhere. |
| Lowest density is at least $3/4$ | Every code has rational density at least $3/4$ in `claim` | Equivalent universal reading of a lower bound on the minimum. |
| Connectedness | `Connected` in `claim` | Additional restriction; a connected counterexample also refutes the unrestricted conjecture. |
| Finite enumerability and decidability | `Fintype`, `DecidableEq`, `DecidableRel` | Computational presentation of finite graphs, not an extra mathematical restriction. |

## Motivation

The source exhibits cubic examples at density $3/4$ and a family at $7/8$ in Theorem 4.2. Its conjecture would make $3/4$ a universal lower bound. A code of density $18/25$ refutes that bound without requiring its own minimality.

## Gap

The literature screen in #19618 reports no settlement in later preprints 2504.14124, 2307.16312, 2306.12583, 2212.08193, 2211.14962, 2209.04500 and citing paper 2407.10595. The journal version is Networks 85(1), 61–75, DOI 10.1002/net.22254. Its full text and its final disposition of Conjecture 1 are unverified. Literature completeness is `ASSUMED-UNVERIFIED`; no unconditional priority claim is made.

## Route

The Lean construction uses vertices $0,\ldots,49$. Vertices $0,\ldots,7$ are of type $A$, $8,\ldots,13$ of type $B$, and the next three blocks of twelve are $P,Q,R$. The code consists of vertices $14,\ldots,49$.

An explicit symmetric loopless neighbor table defines the graph. The private statements `regular`, `connected` and `detic` establish cubicity, connectedness and the detector conditions. `density` certifies the strict inequality below $3/4$; `result` applies these certificates to refute `claim`. All names belong to `D5.S3.Combinatorics.Graph.Domination.JeanSeoCubicErrorDetectingCode`.

## Falsifier

The counterexample would fail if its graph were not simple, connected or cubic, or if any vertex had fewer than two closed detectors, or if both directed detector differences of a distinct pair had fewer than two vertices. These are exactly the hypotheses tested by the kernel-checked certificates. An earlier published resolution changes novelty credit, not the counterexample's mathematical validity.

## Evidence

The settling declaration is `D5/S3/Combinatorics/Graph/Domination/JeanSeoCubicErrorDetectingCode.result`, proving the negation of the literal finite connected claim. Its proof uses only the three standard axioms. No digestion atom or cover is involved; admission is `open-problem-resolution (#19618; Refuted)` and utility is a certified instance refuting `claim`.

The public result is the designated refutation result (`basis=refutes`) and is exempt from four-slot escape registration (CLAUDE.md §3.9).

### Independent experiment

[Experiment directory at commit `90e09a81d1be6fca25dd3fc171ab0562cfe03eba`](https://github.com/the-omega-institute/trureturing-experiments/tree/90e09a81d1be6fca25dd3fc171ab0562cfe03eba/docs/reports/jean-seo-2022-cubic-error-detecting-identifying-code-density).

Command from that experiment checkout: `uv run --with networkx==3.4.2 python3 docs/reports/jean-seo-2022-cubic-error-detecting-identifying-code-density/check.py`; exit 0. Script SHA-256: `5fccbcc0bc2c5ae535386760feae56dfe5a1967b92eebdbdb43bb3e9d8899c67`.

For exactly $t=1,2,3,4$, the checker obtains $(|V|,|E|,|S|)=(50t,75t,36t)$, simple connected cubic graphs, two-domination and zero failing pairs among $1225,4950,11175,19900$ pairs respectively. It obtains detector-neighborhood sizes $(3,2,2,4,3)$ for types $(A,B,P,Q,R)$. These are computations at four finite parameters, not a uniform Lean theorem.

## Triage

Tier 2 in the preregistration; resolution **Refuted** for the v1 finite connected claim. Literature completeness remains `ASSUMED-UNVERIFIED`.

### What the settlement shows

| Item | Status and evidence |
| --- | --- |
| The v1 finite connected cubic lower bound $3/4$ is false in the binding conventions. | **Proved in Lean:** `result`. |
| One 50-vertex graph admits a 36-vertex DET:IC. | **Proved in prose from kernel-checked certificates:** `regular`, `connected` and `detic` apply to the explicit graph and code. The vertices of the code are exactly the 36 integers from 14 through 49. Thus $|S|=50-14=36$ and $|S|/|V|=36/50=18/25$. The strict comparison is kernel-checked by `density`. |
| Any universal cubic lower bound must be at most $18/25$. | **Proved in prose:** applying such a bound to the preceding graph and code gives $b\le36/50=18/25$. |
| The 8 $A$ and 6 $B$ vertices are non-detectors; twelve of each of $P,Q,R$ are detectors, with detector-neighborhood sizes $(3,2,2,4,3)$. | **Computed:** the pinned checker, exactly $t=1,2,3,4$. |
| The required asymmetric separation holds on the 50-vertex graph. | **Proved in Lean:** private `separation`, transferred to actual neighborhoods by `closed_dominators_eq` and `detic`. |
| Previously exhibited examples at $3/4$ and $7/8$ are not contradicted. | **Proved in prose:** existence of a different example below $3/4$ does not negate existence of those examples. The cited source's results remain compatible. |
| Whether this graph has a smaller DET:IC. | **Open:** neither the certificates nor the checker minimize over codes. |
| Whether $18/25$ is the true cubic infimum. | **Open:** this construction supplies only an upper bound on that infimum. |
| A uniform-in-$t$ Lean proof of the candidate family. | **Open:** the Lean theorem certifies the 50-vertex instance; the checker covers only four parameters. |
| The final disposition of Conjecture 1 in the journal revision. | **Open:** journal full text unverified. |

The failure mechanism is the compatible use of only 36 detectors: two-domination and directed separation coexist with 14 non-detectors. Consequently any argument using the conjectured universal $3/4$ bound needs an independent replacement. The source's exhibited examples and Theorem 4.2 do not depend on the universal bound for their validity.

## ASSUMED-UNVERIFIED

The journal revision's treatment of Conjecture 1 and worldwide completeness of the prior-resolution search are unverified. The four computed family members provide no proof for all $t$. Minimality of the displayed code, the exact cubic infimum and a uniform formal family remain open.
