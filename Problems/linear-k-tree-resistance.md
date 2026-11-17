---
slug: linear-k-tree-resistance
bibkey: barrettevansfrancis2017resistance
doi: 10.1016/j.dam.2018.10.043
url: https://arxiv.org/abs/1712.05883v1
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/SpectralGraph/LinearKTreeResistance.result
---

# Straight linear k-tree resistance increments

## Problem

Barrett, Evans and Francis, *Resistance distance in straight linear 2-trees*, arXiv:1712.05883v1, Definition 43 and Conjecture 44, ask whether the endpoint resistance increment tends to $6/(k(k+1)(2k+1))$ for every fixed integer $k\ge1$. Evans and Francis restate this as Conjecture 4.5 in arXiv:2108.07942v2. The source note is `Library/Eigenstructure/barrettevansfrancis2017resistance.md`; the question is [#22865](https://github.com/the-omega-institute/trureturing/issues/22865).

### Statement echo

| Source clause | Formal counterpart | Scope |
| --- | --- | --- |
| Unit edges with $0<|i-j|\le k$ | `LinearKTreeResistance.graph` uses `SimpleGraph.fromRel` and natural-number distance | Vertex `i` represents source vertex $i+1$; loops are excluded. |
| One unit of current enters the first vertex and leaves the last | `IsResistanceSequence` requires the graph Laplacian equation and its voltage difference | No resistance or solution existence is assumed. |
| Every fixed $k\ge1$ | `claim` quantifies over $k$ and its positive lower bound | Includes $k=1$. |
| Sizes $n$ and $n+1$ | Sequence index $t$ represents $n=t+2$ | The finite index shift preserves the limit. |
| Increment limit $6/(k(k+1)(2k+1))$ | `result` proves `claim` with this slope | Includes existence of a sequence and the assertion for every such sequence. |

## Motivation

The settling declaration is `D5/S3/Combinatorics/SpectralGraph/LinearKTreeResistance.result`. Both new modules have generality G, utility none and admission basis escape-witness. `LinearKTreeBoundary.pow_prefix_eq` is the finite-propagation witness behind `boundary_moments_stabilize`. The settling module's witness is its private `correction_converges_of_stable_moments`, consumed by `result`.

## Gap

The increment theorem requires control of the endpoint correction, beyond an estimate of linear growth. Finite calculations alone do not establish convergence as the graph size tends to infinity.

## Route

For $N=n-1$, the interval Gram matrix $Q_N$ gives $R_{n,k}=\mathbf1^TQ_N^{-1}\mathbf1$. With $D=\sum_{d=1}^k d^2$ and $c_N=D\mathbf1-Q_N\mathbf1$, the exact identity is

$$R_{n,k}=\frac ND+\frac{\mathbf1^Tc_N+c_N^TQ_N^{-1}c_N}{D^2}.$$

The defect is confined to endpoint profiles. Finite propagation makes each polynomial moment eventually constant, including vanishing cross-endpoint moments. The inverse polynomial approximation has an error uniform in $N$. These facts give convergence of $c_N^TQ_N^{-1}c_N$; the defect sum is eventually constant. Consecutive differences of a convergent correction tend to zero. Finally, $6\sum_{d=1}^k d^2=k(k+1)(2k+1)$ identifies the slope. The Kirchhoff-coordinate and existence arguments apply to the literal source graph.

## Falsifier

The mathematical assertion would fail if a positive fixed $k$ and a Kirchhoff resistance sequence had a different increment limit, or no such sequence existed. The Lean result proves existence and the asserted limit under the displayed definitions. Uniformity in varying $k$ and finite-increment monotonicity are different assertions.

## Evidence

Kernel evidence: `LinearKTreeResistance.result`; supporting public statements in `LinearKTreeBoundary`, with the complete formulas in their Blueprint Scribes. The accepted axiom boundary is the standard set $\{\mathrm{propext},\mathrm{Classical.choice},\mathrm{Quot.sound}\}$.

The finite experiment is [the pinned experiment directory](https://github.com/the-omega-institute/trureturing-experiments/tree/c784a368d3c5fd1e28aa068e471bd26ba501293d/docs/reports/barrett-evans-francis-linear-k-tree-resistance). Command from the experiments repository: `git show c784a368d3c5fd1e28aa068e471bd26ba501293d:docs/reports/barrett-evans-francis-linear-k-tree-resistance/check.py | python3`; exit 0. The script SHA-256 is `b7e38a0b7175a4f56a6de59894f28ca8e5743bd7bac5c7c9331d4ec8968e065b`. The independently rerun readings are 28 exact $k=2$ formula checks for $3\le n\le30$; 128 graph/Gram/spectral/correction cases for $1\le k\le8$ and $2\le n\le2k+8$; 64 stabilized-defect cases; 49 same-boundary moment comparisons and 98 zero opposite-boundary moments for $2\le k\le8$ and powers 0 through 6. These are finite exact computations.

The four-slot escape audit is unfinished for every new public theorem and the published owner `SmallSignedEntryTranscriptCompensation.quadratic_row_bound`: [#25440](https://github.com/the-omega-institute/trureturing/issues/25440). The missing evidence is a source-faithful realization bridge with actual variation, whole-family sensitivity and observational dependence. No registration is declared validated.

## Triage

| Item | Status | Evidence kind |
| --- | --- | --- |
| The conjectured limit holds for every fixed $k\ge1$, including $k=1$, without finite-$k$ enumeration. | Proved | Kernel-checked `LinearKTreeResistance.result`. |
| Resistance has an eventual affine decomposition with a convergent boundary correction. | Proved | Proved in prose below from the module's inverse-defect identity and correction-convergence argument. |
| 28 exact $k=2$ checks, 128 graph/Gram/spectral/correction cases, 64 defect cases, 49 same-boundary moments and 98 vanishing cross moments. | Computed | The pinned experiment and exact tested ranges in Evidence; exit 0 and script SHA-256 given there. |
| Growing $k$, a uniform rate in $k$, finite-increment monotonicity, arbitrary bent $k$-trees and adjacent graph-family conjectures. | Open | Outside `claim` and the proved estimates. |

### What the settlement shows

**Proved in Lean:** the full fixed-positive-$k$ increment limit, including existence of the resistance sequence and universality over Kirchhoff solutions, is `LinearKTreeResistance.result`.

**Proved in prose:** fix $k\ge1$. The proof's electrical identification and `LinearKTreeBoundary.inverse_defect_expansion` give the identity in Route for all sufficiently large $N$. `boundary_sum_constant` fixes $\mathbf1^Tc_N$, while the private theorem `LinearKTreeResistance.correction_converges_of_stable_moments`, applied to the moments supplied by `boundary_moments_stabilize`, gives $c_N^TQ_N^{-1}c_N\to s_k$. Therefore the correction converges to a real constant $C_k$, and $R_{n,k}=(n-1)/D+C_k+o(1)$. This is a mathematical consequence of those identities; it is not a separate named Lean theorem. Subtracting consecutive terms proves the increment claim through `increment_limit_of_affine_correction`.

**Computed:** the finite experiment verifies exactly the ranges stated in Evidence. Its increment errors have both signs, so these readings give no monotone-approach claim.

**Open:** no extension to $k$ growing with $n$, uniform convergence rate, arbitrary bent $k$-trees or neighbouring graph-family conjectures is asserted. Fixed nonnegative length-dependent conductances with positive length-one conductance are a candidate extension requiring separate proof. The source reading in #22865 identifies no downstream theorem that assumes this conjecture; adjacent conjectures remain separate.

## ASSUMED-UNVERIFIED

Literature completeness is ASSUMED-UNVERIFIED. The source arXiv texts and the partial literature screen are recorded in #22865. The journal versions, the full texts at DOI `10.1016/j.laa.2020.06.031` and `10.1216/rmj.2026.56.123`, and the listed metadata-only citation records are not cleared. There is no exhaustive absence-of-prior-proof or priority claim. The bounded Resistance helper/local-fact owner search has the coverage limitation disclosed by the independent mirror envelope; this is not evidence that an upstream owner does not exist.
