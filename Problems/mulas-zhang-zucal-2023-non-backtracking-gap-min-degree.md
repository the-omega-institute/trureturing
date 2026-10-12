---
slug: mulas-zhang-zucal-2023-non-backtracking-gap-min-degree
bibkey: mulaszhangzucal2023nonbacktracking
doi: 10.1016/j.laa.2023.10.014
url: https://arxiv.org/abs/2303.00373v2
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/NonBacktracking/LaplacianGapMinDegree.result
---

# Non-backtracking Laplacian gap and minimum degree

## Problem

R. Mulas, D. Zhang and G. Zucal, *There is no going back: Properties of the
non-backtracking Laplacian*, arXiv:2303.00373v2, Section 5, Conjecture 5.3:

> If $G$ is not the cycle graph, then $\varepsilon\leq\frac{1}{\delta-1}$.

The source assumes a finite simple graph of minimum degree $\delta\ge2$.
Its transition matrix is $P=\mathcal D^{-1}\mathcal A$, and its
non-backtracking Laplacian is $\mathcal L=I-P$. The gap from $1$ is
$\varepsilon=\min_{\lambda\in\sigma(P)}|\lambda|$.

## Motivation

`D5/S3/Combinatorics/NonBacktracking/LaplacianGapMinDegree.result`
proves the source's claim. The proof also establishes the bound without
cycle exclusion, and produces a positive real transition eigenvalue
when $\delta\ge3$.

## Gap

[Preregistration #15268](https://github.com/the-omega-institute/trureturing/issues/15268)
identifies the published conjecture, the verbatim source and the literature
screen. The source proves the regular case and a weaker general bound.
The recorded literature screen found no settlement in its searched scope;
this is not an exhaustive priority claim.

The public conventions use `G : SimpleGraph (Fin n)`, positive order,
`Arc G` as adjacent ordered vertex pairs, the literal transition weights
$1/(\deg(v)-1)$, and `nbGap` as the infimum of spectral norms. In finite
dimension with a nonempty spectrum this is the source's minimum. The
formal estimate uses membership of an explicit eigenvalue and the
nonnegativity of all spectral norms.

## Route

Write $n$ for the number of vertices, $m$ for the number of edges and $R$
for arc reversal. The tail-block matrix $S$ has blocks
$(J_d-I)/(d-1)$. Its inverse $T$ has blocks $J_d-(d-1)I$, since
$J_d^2=dJ_d$. Thus $P=RS$ and $P^{-1}=TR$.

On the tail-sum-zero subspace $W$, the form of $T-(\delta-1)R$ is
nonpositive. The antisymmetric arc subspace has dimension $m$ and the
form of $T-\Delta R$ is positive there. When $\delta\ge3$, $m>n$ gives
the dimension inequality required by
`D5/S3/Combinatorics/NonBacktracking/HermitianPencilCrossing.pencil_singular_of_subspaces`.
The selected ordered eigenvalue crosses zero at
$t^*\in[\delta-1,\Delta)$. If $Tx=t^*Rx$ and $x\ne0$, then $Rx$ is an
eigenvector of $P$ with positive eigenvalue $1/t^*\le1/(\delta-1)$.
For $\delta=2$, the all-ones vector is an eigenvector with eigenvalue $1$.

## Falsifier

A finite simple graph with positive order, minimum degree at least two
and $\varepsilon>1/(\delta-1)$ would falsify the quoted bound. For the
strengthening at minimum degree at least three, absence of a positive
real eigenvalue in $(0,1/(\delta-1)]$ would falsify that conclusion.

## Evidence

The settling declaration is `result : claim`. Its axiom closure, and the
closures of the supporting and newly public owner theorems, are contained
in $\{\texttt{propext},\texttt{Classical.choice},\texttt{Quot.sound}\}$.
The support uses the owner's subspace Rayleigh bounds and eigenvalue
perturbation estimate by their public names.

The four-slot escape audit is unfinished for `result`,
`pencil_singular_of_subspaces` and the three newly public owner theorems;
[#15386](https://github.com/the-omega-institute/trureturing/issues/15386)
names the source-family reconstruction, bridge and sensitivity gaps.
No valid registration is claimed.

## Triage

### What the settlement shows

| Item | Status | Evidence kind and scope |
| --- | --- | --- |
| The mechanism: inverse factorization, large nonpositive subspace, endpoint inertia and singular crossing | Proved | Kernel-checked selected-eigenvalue route through `T_mul_S`, `W_finrank_lower`, `pencil_left_nonpos`, `pencil_right_pos`, `pencil_graph_singular` and `pencil_to_eigenpair`; exact dimension and complete inertia statements follow from the paper argument below, rather than a separate Lean inertia theorem. |
| Cycle exclusion is unnecessary; at minimum degree two the all-ones vector has eigenvalue one | Proved | Kernel-checked `S_mul_one`, `nbGap_le_one` and `result`; `result` does not use its cycle-exclusion argument. |
| A positive real eigenvalue exists when minimum degree is at least three | Proved | Kernel-checked private `positive_small_eigenpair`, on `result`'s proof path, gives $0<r\le1/(\delta-1)$ with a nonzero complex eigenvector. |
| Numerical readings in the specified experiment entry | Computed | Experiment entry below: 3013 tested graphs, no failed bound or positive-real-eigenvalue check in the tested scope. |
| Equality cases $\varepsilon=1/(\delta-1)$ | Open | No classification proved here. |
| A uniform improvement $\varepsilon\le c/(\delta-1)$ with $c<1$ for irregular graphs | Open | No such estimate proved here. |
| The source's companion question on $\mathcal E$ | Open | No settlement of that question is claimed. |

The exact dimension and inertia assertions have the following paper
argument. Each vertex has a nonempty tail block. Prescribing the value
of one coordinate in each block shows that the tail-sum map onto
$\mathbb C^n$ is surjective; rank-nullity gives $\dim W=2m-n$.
On $W$, $x^*Tx\le-(\delta-1)\|x\|^2$, and arc reversal is an isometry,
so $|x^*Rx|\le\|x\|^2$. Hence $T-(\delta-1)R$ is nonpositive on $W$.
The tail-block eigenvalues of $T$ are $1$ and $-(d-1)$, whence
$-(\Delta-1)\|x\|^2\le x^*Tx\le\|x\|^2$.
On the $+1$ reversal eigenspace, $x^*(T-\Delta R)x\le(1-\Delta)\|x\|^2<0$;
on the $-1$ reversal eigenspace it is at least $\|x\|^2>0$.
Both eigenspaces have dimension $m$. The min-max dimension bounds give
at least $m$ negative and $m$ positive eigenvalues, so exactly $m$ of
each and no zero eigenvalue. Finally $2m\ge3n$ and $n>0$ imply $m>n$;
with eigenvalues ordered increasingly, the $(m+1)$-st eigenvalue is
nonpositive at $\delta-1$ and positive at $\Delta$. Its continuity forces
a singular parameter before $\Delta$. The Lean proof uses decreasing
order and zero-based index $m-1$, the same eigenvalue. This complete inertia exposition is a paper argument;
the Lean proof uses the sufficient endpoint subspace signs directly.

The general crossing theorem applies to arbitrary finite Hermitian
pencils with the stated subspace dimension and sign hypotheses.
The settlement supplies the general upper bound sought in Conjecture
5.3; the source's regular-case result and its weaker upper bound remain
valid. No other source theorem is assigned a new formal conclusion here.

### Experiment entry

[Experiment directory](https://github.com/the-omega-institute/trureturing-experiments/tree/2e8dfba4ca8f5606fd9e562af35b15ec19db4408/docs/reports/mulas-zhang-zucal-2023-non-backtracking-gap-min-degree),
entry `docs/reports/mulas-zhang-zucal-2023-non-backtracking-gap-min-degree/check.py`,
command `python3 check.py`, exit 0, script SHA-256
`94e63cc6bdda813d600e980556008d347b1a650081dde901d240b3cda9276523`.
The final reading is `tested 3013 bad= 0`: wheels $W_4,\ldots,W_{11}$,
complete graphs $K_4,\ldots,K_8$ and 3000 random graphs on 4–12 vertices
with minimum degree at least two. The positive real eigenvalue test
applies to those tested graphs with minimum degree at least three.
These finite readings do not certify untested graphs; the general bound
is supported by the Lean theorem.

## ASSUMED-UNVERIFIED

The literature screen does not prove worldwide absence of an earlier
settlement. Exact equality classification, a strict irregular-graph
improvement and the companion question on $\mathcal E$ remain open.
The full inertia exposition above has no separate kernel-checked
inertia-count declaration. The four-slot escape audits remain unfinished.
