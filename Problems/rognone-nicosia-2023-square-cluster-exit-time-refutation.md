---
slug: rognone-nicosia-2023-square-cluster-exit-time-refutation
bibkey: rognonenicosia2023clusters
doi: 10.1088/2632-072X/aeb36a
url: https://arxiv.org/abs/2308.07880v1
triage: theorem
motivation_gids:
  - D5/S3/StatisticalMechanics/RandomWalks/SquareClusterExitTimeRefutation.result
---

# Squares do not maximize the mean exit time of lattice clusters

## Problem

S. Rognone and V. Nicosia, *Clusters in randomly-coloured spatial networks*, arXiv:2308.07880v1 (J. Phys. Complexity, 2026), section on the mean exit time from a cluster:

> Characterising clusters with maximal exit time at each fixed $N$ seems to be a harder quest. Here we conjecture that the maximal exit time is obtained for squares with $N$ nodes.

Here:
- **Cluster:** a set of nodes of the square lattice, connected through nearest neighbours; the walk moves to each of the four neighbours with probability 1/4.
- **Mean exit time** $\tau(S)$: the average over the starting nodes of $S$ of the expected first time the walk is outside $S$.

The definitions are quoted in [the literature note](../Library/StatisticalMechanics/rognonenicosia2023clusters.md). The source's displayed formula averages node-to-node hitting times, while its prose and every worked first-step system use the first-exit time; the settlement uses the first-exit time.

Issue [#20034](https://github.com/the-omega-institute/trureturing/issues/20034) fixes the reading: for every $m\ge1$ and every connected cluster $S$ of $m^2$ nodes, $\tau(S)\le\tau(\{0,\dots,m-1\}^2)$. This is refuted.

## Motivation

The source proposes the mean exit time as a descriptor of the compactness of coloured clusters: lines minimize it, and the square, with the most internal 4-cycles and the smallest surface, is conjectured to maximize it. The conjecture provides the upper benchmark against which sampled cluster ensembles are compared.

## Gap

The literature check before any Lean is recorded in #20034:
- arXiv lists only v1, and the accepted manuscript keeps the conjecture;
- OpenAlex and Crossref list no citing works;
- the source's own evidence covers the five tetrominoes, rectangles, and $10^4$ Eden-growth samples at $N=225$, not an optimization over all clusters;
- the repository had no record.

`not-found-in-searched-scope`.

## Route

Take $m=11$, the lattice disk $C=\{(x,y):x^2+y^2\le37\}$ (121 nodes) and the square $Q$ of side 11.
1. **The cluster.** $C$ has 121 nodes and is connected: each node joins the axis along its row.
2. **Certificates.** Exact rational vectors $t_C$ and $t_Q$, constant on the orbits of the dihedral group of order 8, satisfy $t=\mathbf 1+Pt$ on each set, where $P$ averages over neighbours inside the set.
3. **Identification.** From $1\le t\le43$, $0\le P^nt\le(42/43)^nt$, so $t=\sum_kP^k\mathbf 1$. $(P^k\mathbf 1)(p)$ is the probability that the first $k$ positions stay in the set, so $t(p)$ is the expected exit time.
4. **Comparison.** $\tau(C)=198008236169/8338377773=23.7466\ldots>\tau(Q)=2811118983/119333830=23.5568\ldots$

## Falsifier

The counterexample would not answer the conjecture if the module's exit time were a different quantity. The module:
- defines the exit-time distribution from direction words of the four-neighbour walk;
- defines the expected exit time as the expectation of that distribution;
- requires the competing cluster to be connected and to have exactly $m^2$ nodes.

## Evidence

The canonical source is `D5/S3/StatisticalMechanics/RandomWalks/SquareClusterExitTimeRefutation.lean` (408 lines).
- **Proof.** It proves `result : ¬ claim`.
- **Axioms.** It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.

Frozen state: `Golden/Frozen/state/D5/S3/StatisticalMechanics/RandomWalks/SquareClusterExitTimeRefutation.lean.json`, statement `sha256:9f2ba2b6d533316b1eb1e06204f78ab975a83281a606ba195767fa63e595c2db`.

Declaration statements:
- `result`: `sha256:8a8e346c725c8c5ee9bf1cb7905440f9f5e59237f778bfeca281e1975b8d995a`;
- `claim`: `sha256:14bd2d4f54053103d1e7ddbbe742dd755598ab572c03bdd3386ad0a0c99ad571`.

## Triage

Tier 1 conjecture of a 2023 paper, preregistered in issue #20034 before any Lean.
`theorem`; resolution `refuted`.

The module is admitted under the open-problem-resolution basis of CLAUDE.md §3.2; the per-declaration proof shapes are listed in the delivery PR. `utility: kind=certified-instance; basis=refutes`. There is no digestion atom.

### What the settlement shows

**Proved in the module:** the 121-node lattice disk has a strictly larger mean exit time than the 11 × 11 square, so the square does not maximize the mean exit time at $N=121$.

**Computed, not formalized** (orchestrator, recorded in #20034):
- *Persistence.* Lattice disks with exactly $m^2$ nodes beat the $m\times m$ square for $m=11,13,14,15,16,18,20,21,22,23,24$; for example $42.1002>40.4316$ at $N=225$, the size the source sampled.
- *Small sizes.* For $m\le10$ no lattice disk with exactly $m^2$ nodes beats the square.
- *Local optimality.* No single-cell move from the square raises $\tau$ for $m\le11$, so the square is a local maximum that a global rearrangement beats.

**Argued, not formalized.**
- *Mechanism.* The mean exit time is the discrete torsional rigidity of the cluster divided by its size. Its continuum analogue is maximized by the disk among planar domains of given area (the Saint-Venant inequality), and lattice disks approach that shape as $N$ grows.
- *Effect on the paper.* The square remains the maximizer among the sampled Eden clusters and among rectangles, but it is not the maximizer over all clusters of square size. A corrected benchmark should be the near-circular cluster.

## ASSUMED-UNVERIFIED

The bounded literature check does not establish exhaustive worldwide novelty or priority. The statements in "Computed, not formalized" and "Argued, not formalized" are not formalized; whether 121 is the smallest square size with a counterexample was not checked over all cluster shapes.
