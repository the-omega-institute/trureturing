---
slug: de-panafieu-et-al-2026-colored-cayley-tree-clt
bibkey: depanafieu2026stabilization
doi: 10.48550/arXiv.2611.17989
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/Graph/CayleyColoring/NormalLimit.colored_cayley_tree_clt
---

# The central limit theorem for the colored Cayley tree

## Problem

Élie de Panafieu, Fabien Mathieu, Maria Potop-Butucaru and Sébastien Tixeuil state in Section 6 of *The Exact Stabilization Time of Self-Stabilizing Coloring: Mean, Variance, and Distribution*:

> We leave open the central limit theorem for the 𝑘-colored tree, which the linear variance Eq. (18) and the 𝑛-th power in Eq. (19) suggest, and the regime 𝑝 → 0 of the bipartite model.

Fix an integer k ≥ 2. For each n ≥ 1 draw a uniform rooted labeled simple tree on n vertices and independently assign each vertex a uniform initial color among k colors. At each step choose uniformly from the currently enabled vertices and recolor that vertex with any ambient color absent from its neighborhood. The source assumes the ambient palette size q is at least k and at least one greater than the maximum degree. These conditions supply a valid free-color policy, which is the hypothesis in the Lean theorem. Let Tₙ count these updates. The tree question asks for the standard Gaussian weak limit of (Tₙ − E[Tₙ]) / √Var(Tₙ), with positive variance at all sufficiently large n. [arXiv v1, Section 6](https://arxiv.org/pdf/2611.17989v1#page=15)

## Motivation

Theorem 10 gives the generating function of the count for every finite size, and Equation (18) gives linear variance growth. The limit identifies the distribution of the typical fluctuations of the sequential dynamics at that scale.

## Gap

The registered statement, the exact source quotation, and bounded searches for a prior resolution are recorded in the tier-1 preregistration. The probe verifies the fixed-root peak-to-leaf equivalence on the native tree type. The central limit theorem also requires the sequential history law, the finite occupancy distribution, and convergence using the actual source moments. [Issue #33415](https://github.com/the-omega-institute/trureturing/issues/33415)

## Route

The scheduler chooses a vertex uniformly from the endpoints of the remaining conflict edges. Recoloring removes just the conflict edges incident to that mover. Since the enabled sets shrink, a uniform ranking assigns each legal terminal history probability equal to the product of the reciprocal enabled-set sizes.

The rooted tree and its independent initial colors give a uniform root color and independent uniform additive edge marks. Replace each zero-mark component by its fixed-root peak-to-leaf image, keeping the intercomponent edges and transporting the nonzero marks with them. Seitz reroots at the greatest label for local minima, recursively transforms the branches, and swaps that label with the original root label. The order-dual construction for peaks cuts at the least label, applies the same branch recursion, and swaps the least label with the designated root. [Seitz, §5.3.1.2, pp. 106–107](https://repositum.tuwien.ac.at/handle/20.500.12708/10695)

An anchor-based code transforms a target function to the parent coordinates of a rooted tree and preserves each target occurrence. Consequently Tₙ has the ordinary-bin occupancy distribution of n−1 independent uniform pairs of a vertex and a mark. A throw lands in the vertex's bin at mark zero and is discarded otherwise.

The entire word pushes forward to independent throws with probability 1/(kn) per ordinary bin and discard probability 1−1/k. The count distribution transports the expectation and variance. The occupancy proof uses the exact conditional Bernoulli increments, a linear variance lower bound and a telescoping comparison of characteristic functions with Gaussian factors. Lévy continuity gives the limit after standardization by the source moments.

## Falsifier

A positive row size, fixed k ≥ 2 and valid free-color policy for which a count atom disagrees with the ordinary occupancy count would refute the finite bridge. A family of the stipulated source rows whose standardized laws fail to converge weakly to the standard Gaussian would refute the claimed limit.

## Evidence

The resolution declaration is `D5/S3/Combinatorics/Graph/CayleyColoring/NormalLimit.colored_cayley_tree_clt`. The theorem uses the native `SimpleGraph.IsTree` sample, a valid policy in every row, the source expectation and variance, and weak convergence to `gaussianReal 0 1`. Its axiom closure is `Classical.choice`, `Quot.sound` and `propext`.

The local source-bound escape audit validates the bindings for `CayleyTreeProbability.microstate_word_law` and `CayleyTreeProbability.colored_cayley_tree_clt`. 71 public theorem audits are unfinished. The exact target list and missing source binding evidence are recorded on issue #33415. [Audit disclosure](https://github.com/the-omega-institute/trureturing/issues/33415#issuecomment-7090845908)

The all-size finite law is `D5/S3/Combinatorics/Graph/CayleyColoring/FiniteLaw.native_daemon_occupancy`. Its ranking-to-history transport uses `totalEquiv` and the conditional fibers in `conditionalEquiv`, supplied by `policy_terminal_law`. The word and count pushforwards are in `D5/S3/Combinatorics/Graph/CayleyColoring/FiniteProbability`. Row N has N+1 vertices and N throws. The singleton therefore has an empty throw word and count zero.

## Triage

`theorem`. The fixed-k tree clause is proved for every k ≥ 2.

### What the settlement shows

- **Proved.** The count law depends on the initial palette through the independent zero marks on the edges. Free-color policies satisfying the update rule give the same conditional mover-history law on every input.
- **Proved.** The count law is an exact equality in every positive finite row. The Gaussian limit uses the exact expectation and variance of that count.
- **Proved.** The row variance is eventually positive. The occupancy lower bound is already positive at every size n ≥ 2.
- **Open.** The sparse bipartite question in the same source sentence and limits with varying k are outside the fixed-k theorem.

## ASSUMED-UNVERIFIED

The preregistration's literature searches are bounded. Exhaustive citation-index coverage and publication priority are unverified.
