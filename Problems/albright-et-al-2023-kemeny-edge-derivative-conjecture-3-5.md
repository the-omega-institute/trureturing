---
slug: albright-et-al-2023-kemeny-edge-derivative-conjecture-3-5
bibkey: albright2023kemenyedgederivative
doi: 10.48550/arXiv.2211.01495
url: https://arxiv.org/abs/2211.01495v2
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/SpectralGraph/AlbrightKemenyEdgeDerivativeRefutation.result
---

# The path does not minimize Kemeny's edge derivative

## Problem

C. Albright, K. P. Hadaway, A. H. Pomerance, J. Jeffries, K. J. Lorenzen
and A. K. Nix, *On the Edge Derivative of the Normalized Laplacian with
Applications to Kemeny's Constant*, arXiv:2211.01495v2, Conjecture 3.5,
printed page 19:

> For a given n, the derivative of Kemeny's constant on simple graphs of order n is smallest on the path on n vertices with respect to the non-edge connecting the ends of the path. The value of this derivative is O(n³).

The minimality sentence is refuted under the literal conventions in
[preregistration #19527](https://github.com/the-omega-institute/trureturing/issues/19527).
The [Library note](../Library/GraphInvariants/albright2023kemenyedgederivative.md)
records the source definitions. The path's own cubic growth sentence is not
negated by this settlement.

### Statement echo

All short declaration names below belong to
`D5.S3.Combinatorics.SpectralGraph.AlbrightKemenyEdgeDerivativeRefutation`.

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| $A(t)=A+tB$, with $B$ indicating one unordered pair | `paramAdj` | The two matrix units have weight one; degrees change with $t$ |
| $L=I-D^{-1/2}AD^{-1/2}$ | `normLap` | $D$ contains the row sums of the perturbed matrix |
| $K=\sum_{\lambda_L\ne0}1/\lambda_L$ | `kemeny` | Nonzero real characteristic roots, counted with multiplicity; the proof identifies them spectrally |
| Simple graphs of order $n$ | `claim`: $G$ on `Fin n`, $2\le n$ | Connectedness is the domain where the source's random-walk constant is defined |
| Edge or non-edge with distinct ends | `claim`: $a\ne b$ | The witness uses a missing edge, so also refutes a non-edge-only comparison |
| Path on $n$ vertices, endpoint perturbation | `SimpleGraph.pathGraph n`, endpoints $0,n-1$ | Bounds follow from $2\le n$ |
| Smallest derivative | `claim`: two `HasDerivAt` premises at zero and $d_P\le d_G$ | Derivative existence is required; no default value for a nondifferentiable function |
| Universal minimality fails | `result` | Negates this entire proposition |
| The path value is $O(n^3)$ | Outside `claim` | The refutation makes no contrary assertion about the path value |

The instance class `DecidableRel G.Adj` supplies computation on the finite
graph and imposes no mathematical restriction. Real parameters allow the
ordinary two-sided derivative; the proof establishes positive degrees and
the inverse update on a neighborhood of zero. No source clause within the
minimality proposition is dropped.

## Motivation

Two dense cliques joined through a long path concentrate degree mass at
widely separated vertices. The derivative records the change in degrees as
well as the change in the grounded inverse. This distinguishes the
perturbation from a degree-preserving edge modification.

## Gap

The source and literature screen in #19527 reports that arXiv v1 and v2
retain Conjecture 3.5. Bini–Meini–Poloni, arXiv:2508.21506, treats
degree-preserving perturbations; Abiad et al., arXiv:2609.17481, treats
Kemeny's constant itself. Neither is reported there as settling this
minimality assertion. These are orchestrator-reported literature readings.
Completeness and priority remain `ASSUMED-UNVERIFIED`.

## Route

The graph $B_8$ has cliques on $\{0,\ldots,7\}$ and
$\{8,\ldots,15\}$, joined by $0,16,17,18,19,20,21,22,8$.
The chord $\{0,8\}$ is absent. The private `barbell_connected` proves
connectedness. The private `barbell_hasDerivAt` and `path_hasDerivAt` give

$$
D_{0,8}K(B_8)=-\frac{7683669}{4096},\qquad
D_{0,22}K(P_{23})=-\frac{77763}{44}.
$$

Their difference is $-4891047/45056<0$, as used by the private
`derivative_comparison` and the public `result`.

The private `kemeny_eq_grounded` identifies the characteristic-root sum
with the weighted grounded trace

$$
K(A)=\sum_i d_i X_{ii}-\frac{d^{\mathsf T}Xd}{\sum_i d_i},
\qquad
(\operatorname{diag}(d)-A)X=I-e_0\mathbf1^{\mathsf T}.
$$

It uses Hermitian spectral decomposition. The private
`kemeny_edge_hasDerivAt` differentiates a rational rank-one update of $X$
on a neighborhood of zero. Exact rational matrices certify the two
instances; their casts to the reals preserve the inverse and voltage
identities. No external numerical output is a premise of `result`.

## Falsifier

This counterexample would fail if its graph were disconnected, its selected
vertices coincided, either asserted derivative failed to exist with the
stated value, or the strict comparison failed. The corresponding finite
and analytic certificates occur on `result`'s proof path. A minimum-order
claim or an infinite-family claim requires additional arguments and is not
inferred from this instance.

## Evidence

The kernel-checked public theorem is
`D5.S3.Combinatorics.SpectralGraph.AlbrightKemenyEdgeDerivativeRefutation.result`.
Its conclusion is the closed negation of `claim`. The axiom closure of every
public declaration is contained in
$\{\mathrm{propext},\mathrm{Classical.choice},\mathrm{Quot.sound}\}$.

The public result is the designated refutation result (`basis=refutes`) and is exempt from four-slot escape registration (CLAUDE.md §3.9).
There is no other public theorem and no published owner declaration in this
delivery. The module's admission basis is
`open-problem-resolution (#19527; Refuted)`; its finite certificates have
utility `certified-instance` with the designated refutation.

### Experiment

[Published numerical and rational check](https://github.com/the-omega-institute/trureturing-experiments/tree/a77baff05a953c8b7776552046bee2173c9a2fea/docs/reports/albright-et-al-2023-kemeny-edge-derivative-conjecture-3-5),
script `check.py`, SHA-256
`713d110b73e66bd8febc61a2ee8188420a38164bb9b32bff332e014c1c70ba95`.
Command: `/tmp/op-lwc-venv/bin/python /Users/auric/trureturing-experiments/docs/reports/albright-et-al-2023-kemeny-edge-derivative-conjecture-3-5/check.py`;
exit 0, `RESULT PASS`. The interpreter requires NumPy; the script is
available at the pinned repository path and accepts no arguments.

Computed scope: central differences of the nonzero normalized-Laplacian
eigenvalue sum for $k=3,\ldots,15$, at $n=3k-1$, agree with the proposed
closed forms within the script's tolerances; among those tested values the
barbell first beats the path at $k=8$. Exact rational elimination at
$k=8,10$ gives respectively $-7683669/4096,-23324553/5000$ for the
barbells and $-77763/44,-204363/56$ for the paths. The two exact
comparisons are strict. The experiment does not enumerate other graphs
or certify all $k$.

## Triage

| Item | Status and evidence |
| --- | --- |
| Settlement: Refuted | Proved in Lean: public `result` negates Conjecture 3.5's minimality assertion |
| Instance $n=23$, $B_8$ chord $(0,8)$ against $P_{23}$ chord $(0,22)$ | Proved in Lean: private `barbell_connected`, `barbell_hasDerivAt`, `path_hasDerivAt`, and `derivative_comparison`, consumed by `result` |
| Single-instance scope with literature and admission limitations | Proved in Lean: `result` settles the order-23 minimality refutation; the separate literature and admission boundaries below are retained |
| Smallest counterexample among all graphs | Open: no graph enumeration or exclusion below 23 is provided |
| Optional infinite barbell family | Open in Lean: no theorem covers every $k$; the finite experiment is separate evidence |
| Tested barbell family | Computed: eigenvalue differences at $k=3,\ldots,15$ and rational comparisons at $k=8,10$, by the experiment entry above |
| Asymptotic growth of the global minimum | Open: no uniform family theorem or matching extremal estimate is proved |
| Exhaustive literature novelty | `ASSUMED-UNVERIFIED`: the partial source and literature screen in #19527 |
| Canonical frozen membership | Machine evidence: the canonical module state record under `Golden/Frozen/state/D5/S3/Combinatorics/SpectralGraph/AlbrightKemenyEdgeDerivativeRefutation.lean.json`; not a claim about literature novelty |
| CI admission | Outside the mathematical claim: admission is decided by the required CI check on the PR head; mathematical refutation does not itself assert CI admission |

### What the settlement shows

**Proved in Lean.** Connectedness, unweighted simplicity and existence of
both derivatives do not force the path-ends derivative to be minimal:
`result` supplies a strict failure at order 23. Restricting the comparison
to nonedges also does not remove this witness, since $(0,8)$ is absent in
$B_8$. This last finite fact is proved in prose from `rel`: the two
vertices belong to different cliques, neither ordered pair is a connector
edge or a consecutive pair on the joining path, and symmetrizing `rel`
therefore creates no edge between them.

**Explanation from the proved trace identity.** In `kemeny_eq_grounded`,
the squared voltage enters through the rank-one update of the grounded
inverse. Dense cliques supply degree mass while the connecting path
separates their voltage levels. This explains how a chord between the
attachment vertices can decrease the constant faster than closing a path.
This explanation does not assert a uniform asymptotic estimate.

**Computed.** In the experiment's tested family, $k=3,\ldots,7$ does not
violate the path comparison and $k=8,\ldots,15$ does. No conclusion about
other graphs at these orders follows. Whether a graph on 16 through 22
vertices beats the path, and whether a smaller counterexample exists, are
open here. The source's small-order tables are literature evidence rather
than a Lean classification.

**Open.** A uniform proof of the proposed barbell derivative formula would
imply magnitude growth $n^4/162$ along $n=3k-1$. For a minimum $m(n)$ of
the signed derivative this would give an upper bound on $m(n)$, or a lower
bound on $-m(n)$, not a lower bound on the negative minimum itself. Neither
that uniform formula nor the sharp growth order is a conclusion of this
module. The source's path cubic-growth statement is compatible with the
single counterexample.

**Literature reading.** The source's Theorems 2.19 and 3.3 are independently
proved bounds; their proofs do not assume Conjecture 3.5. Section 4 uses
Conjectures 2.20, 3.4 and 3.5 as motivation for stronger bounds. The present
refutation removes path minimality as support for that proposed cubic
lower-growth picture; it neither refutes those proved bounds nor settles
Conjectures 2.20 or 3.4. These dependency and scope observations are based
on the paper, not additional Lean statements.

## ASSUMED-UNVERIFIED

Literature completeness, priority, and the absence of an unlocated external
settlement are `ASSUMED-UNVERIFIED`. The optional infinite family, the
smallest counterexample order and the sharp global extremal growth remain
outside the kernel-checked settlement. Numerical finite differences are
corroborating computations, not formal certificates of a uniform claim.
