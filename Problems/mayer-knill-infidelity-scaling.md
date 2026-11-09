---
slug: mayer-knill-infidelity-scaling
bibkey: mayerknill2018unitary
doi: 10.1103/PhysRevA.98.052326
url: https://arxiv.org/abs/1805.04491v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/QuantumChannels/MayerKnillInfidelityScalingTransition.result
---

# Mayer–Knill process-infidelity transition

## Problem

Mayer and Knill, *Quantum Process Fidelity Bounds from Sets of Input States*, arXiv:1805.04491v1, p. 4, ask: “The transition from sub-linear to linear scaling is not explained by the proof of Thm. 2 and thus remains an open question.” The published location is §V.B. The quantified classification is preregistered in [#24695](https://github.com/the-omega-institute/trureturing/issues/24695).

Fix $d\ge2$ and a finite indexed unit family $S=(\psi_k)_{k=1}^N$ in $\mathbb C^d$. Assume that it spans $\mathbb C^d$ and that nonzero overlaps generate a connected relation on the indices. Put $P_k=\psi_k\psi_k^\dagger$ and

$$A_S=\{A:(I-P_k)A\psi_k=0\text{ for every }k\}.$$

For CPTP maps let $F$ be normalized process fidelity and let

$$f_S(\epsilon)=1-\inf\{F(\Phi):\langle\psi_k,\Phi(P_k)\psi_k\rangle\ge1-\epsilon\text{ for every }k\}.$$

The classification is

$$A_S=\mathbb CI\iff f_S(\epsilon)=\Theta(\epsilon),\qquad A_S\ne\mathbb CI\iff f_S(\epsilon)=\Theta(\sqrt\epsilon)\quad(\epsilon\downarrow0).$$

Every comparison uses positive constants and a positive radius chosen for the fixed family. Errors are equal at every input.

### Statement echo

| Source clause | Lean counterpart | Scope |
| --- | --- | --- |
| Finite complex Hilbert space, $d\ge2$ | `claim`, binders `d N psi`, hypothesis `2 ≤ d` | All dimensions and all finite family sizes |
| Pure unit inputs | `unitInputFamily` | Every indexed vector has unit squared norm |
| Inputs span | `spanInputFamily` | Complex submodule span equals top |
| Connected nonorthogonality graph | `nonorthogonalityConnected` | Generated equivalence relation connects all indices |
| Pure-state projector | `PureStateHandshake.rankOneDensity` | Existing owner; no duplicate projector definition |
| CPTP channel and survival constraints | `admissibleAt`, `survivalFidelity` | Existing `CPTP` and all input inequalities |
| Normalized Choi overlap | Inline expression in `f` | Existing Choi matrix, normalized maximally entangled vector and division by $d$ |
| Worst process infidelity | `f` | Real infimum; identity channel provides a feasible map and fidelities are bounded below |
| Line-preserving obstruction space | `obstructionSpace`, `scalarObstruction` | Literal residual condition; its line-preservation interpretation uses unit inputs |
| Two-sided local rates | `LinearScaling`, `SqrtScaling` | Positive lower/upper constants, radius and errors |
| Both directions of both classifications | `result` | Full conjunction in `claim`; no additional source hypothesis |

## Motivation

The settling declaration is `D5/S3/Quantum/QuantumChannels/MayerKnillInfidelityScalingTransition.result`. The module has generality `G`, utility `none`, and admission basis `open-problem-resolution (#24695; Proved)`. The supporting `MayerKnillInfidelityScalingCore` has generality `G`, utility `none`, and admission basis `escape-witness`: its finite connected-relation estimate supplies the graph-propagation step. The [source note](../Library/QuantumChannels/mayerknill2018unitary.md) owns the paper's DOI.

## Gap

The paper gives a general square-root bound and examples with linear behavior. The classification identifies exactly which fixed input families have each rate. Dimension formulas for support graphs and symmetric-POVM optimality remain outside this statement.

## Route

Center each Kraus operator by subtracting its scalar trace part. Its squared Hilbert–Schmidt norm contributes to process loss; tested orthogonal residuals contribute to input loss. In the scalar-obstruction case, the detection map is injective on traceless matrices, so finite-dimensional coercivity bounds process loss linearly. An identity/reset mixture gives a positive linear lower bound.

A nonscalar obstruction can be centered and normalized to operator norm one. The two Kraus operators $\sqrt t A$ and $(I-tA^\dagger A)^{1/2}$ are trace preserving. Their tested error is at most $t^2$, while process loss is bounded below by a positive multiple of $t$. For the upper bound, Stinespring Gram defects propagate along the finite connected overlap relation; spanning evaluation controls the whole matrix. Linear and square-root rates are mutually exclusive.

## Falsifier

A counterexample must satisfy every unit, spanning and connectedness hypothesis and violate at least one direction of `claim`. A degenerating family with no uniform constants, or a channel tested on unequal-error faces with zero coordinates, does not refute the fixed-family equal-error statement.

## Evidence

### Formal evidence

`MayerKnillInfidelityScalingTransition.result` states the classification. The private declarations `scalar_channel_upper`, `nonscalar_sqrt_lower`, `universal_linear_lower`, and `general_channel_upper` state the supporting estimates with their exact hypotheses. `MayerKnillInfidelityScalingCore.finite_graph_squared_distance_bound` states the finite graph estimate. These are claims about the corresponding Lean statements, with verification supplied by the module build and frozen state records.

The escape audit for the five new or published public theorem targets is unfinished at [#25592](https://github.com/the-omega-institute/trureturing/issues/25592). No four-slot registration is claimed validated.

### Exact experiment

The [experiment directory](https://github.com/the-omega-institute/trureturing-experiments/tree/13e02810fd61a2a33d29201d8a346bd880710678/docs/reports/mayer-knill-infidelity-scaling-transition) is pinned to commit `13e02810fd61a2a33d29201d8a346bd880710678`. Command: `git -C ../trureturing-experiments show 13e02810fd61a2a33d29201d8a346bd880710678:docs/reports/mayer-knill-infidelity-scaling-transition/check.py | python3 -`. Exit: 0. Script SHA-256: `7f3818753ed48cd64fb0ab024ecf7540ae0965c579d8f695ce2ce3e828d82bf5`.

The exact tested scope is $d=2$, $\epsilon=1/10$ for the depolarizing example, with process fidelity $17/20$, input error $1/10$, and the two probes $e_0,(3/5,4/5)$ with overlap $3/5$. The script computes the raw traceless line-preserving matrix $B=\begin{pmatrix}1&-3/2\\0&-1\end{pmatrix}$ and verifies both tested eigenvector relations. It does not compute a general-dimension classification or the normalized matrix norms.

## Triage

| Item | Status and evidence kind | Evidence and boundary |
| --- | --- | --- |
| Every fixed finite unit spanning connected family in $d\ge2$ has exactly the stated linear/scalar or square-root/nonscalar rate | Proved; kernel-checked | `MayerKnillInfidelityScalingTransition.result` |
| Scalar-obstruction upper bound requires unit probes, not connectedness | Proved; kernel-checked | `scalar_channel_upper`; neither a spanning nor a connectedness hypothesis occurs |
| Nonscalar square-root lower bound requires unit probes and positive dimension; matching upper bound uses connectedness and spanning | Proved; kernel-checked | `nonscalar_sqrt_lower` and `general_channel_upper`, respectively |
| Every unit family in $d\ge2$ has a positive linear lower bound with coefficient $1-1/d^2$ | Proved; kernel-checked bound; coefficient proved in prose | `universal_linear_lower` states existence of positive constants. Its identity/reset channel has process fidelity $1-\epsilon+\epsilon/d^2$ by `reset_process`, is admissible by `reset_admissible`, and hence yields $(1-1/d^2)\epsilon\le f_S(\epsilon)$ for $0<\epsilon<1$ |
| General square-root upper estimate from Gram defects, graph propagation and spanning evaluation | Proved; kernel-checked | `general_channel_upper` uses `channel_gram_defect`, `finite_graph_squared_distance_bound` and `spanning_evaluation_coercivity` |
| Two-probe nonnormal obstruction, normalized matrix $A=B/2$ | Computed for raw $B$; normalized norm claims proved in prose | The pinned experiment computes $B$. For $A=\begin{pmatrix}1/2&-3/4\\0&-1/2\end{pmatrix}$, the derivation below proves operator norm one and squared Hilbert–Schmidt norm $17/16$. These norms are not asserted as outputs of the pinned script or as Lean theorems |
| Support-graph dimension formulas and symmetric-POVM optimality | Open | Neither is part of `claim`; no formalization is asserted |
| Uniform constants under degenerating spanning/overlap data and general unequal-error faces with zero coordinates | Open | No uniform extension is asserted |

### What the settlement shows

The decisive criterion is scalarity of the tested-line obstruction space. It replaces an example-by-example rate question with a condition on a finite-dimensional linear space. The scalar upper estimate needs no connectedness, whereas the square-root lower estimate needs only unit probes and positive dimension. Spanning and connectedness supply the general upper estimate. The classification concerns the source's transition question and leaves the symmetric-POVM optimality conjecture unresolved.

For the normalized concrete obstruction, direct multiplication gives

$$A^\dagger A=\begin{pmatrix}1/4&-3/8\\-3/8&13/16\end{pmatrix},\qquad \operatorname{tr}(A^\dagger A)=17/16,\qquad \det(A^\dagger A)=1/16.$$

Thus its characteristic polynomial is $(\lambda-1)(\lambda-1/16)$. Its singular values are $1,1/4$, proving $\lVert A\rVert_{\mathrm{op}}=1$ and $\lVert A\rVert_{\mathrm{HS}}^2=17/16$. This is an exact prose derivation, rather than a claim that the cited experiment computes these norms. The numerical evidence label is restricted to what the immutable script actually checks.

### Literature status

The source passage and preregistration literature screen identify no settlement in the searched scope. The screen covers source/author and citing-paper searches, repository statements and dossiers, and public problem indexes. API rate limits and unread works are listed in #24695. Search completeness is `ASSUMED-UNVERIFIED`; an unsuccessful bounded search is not a proof of novelty.

## ASSUMED-UNVERIFIED

Literature completeness is `ASSUMED-UNVERIFIED`, including the unread works and rate-limited citation endpoints listed in #24695. No empirical claim about quantum hardware follows from the formal finite-dimensional CPTP result. Four-slot escape registration remains unfinished at #25592. Support-graph dimension formulas, symmetric-POVM optimality, uniform degenerate-family constants, and general unequal-error boundary faces remain open.
