---
bibkey: rognonenicosia2023clusters
authors: Silvia Rognone; Vincenzo Nicosia
year: 2023
title: "Clusters in randomly-coloured spatial networks"
doi: 10.1088/2632-072X/aeb36a
url: https://arxiv.org/abs/2308.07880v1
claim: "The paper studies monochromatic clusters of randomly coloured square lattices, defines the mean exit time of a simple random walk from a cluster, computes it for the tetrominoes, rectangles and sampled clusters, and conjectures that at each fixed size N the square maximizes the mean exit time."
strata_touched:
  - D5/S3/StatisticalMechanics/RandomWalks/SquareClusterExitTimeRefutation
license: citation-only
triage: anchor
---

# Clusters in randomly-coloured spatial networks

S. Rognone and V. Nicosia, arXiv:2308.07880v1 (2023-08-15); J. Phys. Complexity (2026). Quotations are from the v1 TeX source.

The mean exit time:

> We define the Mean Exit time $\tau_{\mathcal{C}}$ from the cluster $\mathcal{C}$ with $N$ nodes as the average time needed to a walker to reach the frontier of $\mathcal{C}$ when starting from one of the nodes of $\mathcal{C}$.

> According to our definition of exit time from a cluster, we are interested in the average time needed for a walker to reach for the first time any node not belonging to the cluster, independently of the actual node reached by the walker.

The worked first-step system for the straight tetromino:

> \tau_{1,\fC}&=&1+\pi_{12}\tau_{2,\fC}

> Where $\pi_{ij}$ represents the probability that a walker at node $i$ jumps to node $j$ in one step. In our case, all the one-step probabilities are the same and equal to $1/4$, i.e., as each node in the lattice is connected with exactly four neighbours.

The conjecture:

> Characterising clusters with maximal exit time at each fixed $N$ seems to be a harder quest. Here we conjecture that the maximal exit time is obtained for squares with $N$ nodes.

The displayed formula `eq:eq_tau_c` averages node-to-node hitting times; the prose above and every worked system use the first-exit time.

## Verified locator

Source: https://arxiv.org/abs/2308.07880v1
- URL: https://arxiv.org/abs/2308.07880v1 (source `rgm_njp.tex`, md5 `efc6b5a2bbd8d2e79f519768d60e7125`):
  - the mean exit time, l. 646–672;
  - the worked first-step system, l. 728–749;
  - the conjecture, l. 988–990.
- DOI: 10.1088/2632-072X/aeb36a (https://doi.org/10.1088/2632-072X/aeb36a).
