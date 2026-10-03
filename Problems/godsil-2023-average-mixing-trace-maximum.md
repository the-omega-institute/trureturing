---
slug: godsil-2023-average-mixing-trace-maximum
bibkey: godsil2023diagonal
doi: 10.48550/arXiv.1910.02039
url: https://arxiv.org/abs/1910.02039v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Dynamics/AverageMixingTraceMaximum.result
---

# The complete graph maximizes the trace of the average mixing matrix

## Problem

Chris Godsil, Krystal Guo and Mariia Sobchuk, *Diagonal entries of the
average mixing matrix*, arXiv:1910.02039v1, Section 9 (Conjecture 9.1 of
Australas. J. Combin. 86(3) (2023) 373–386), write:

> Based on the computations summarized in Table 2 and on Corollary 6.3, we also make the following conjecture. The complete graph on $n$ vertices attains the maximum trace with respect to the $\widehat{M}_{A}$ for all $n$.

For a graph $X$ with adjacency matrix $A=\sum_\theta\theta E_\theta$ over
its distinct eigenvalues, $E_\theta$ the orthogonal projection onto the
$\theta$-eigenspace, the average mixing matrix of the continuous quantum
walk is $\widehat M_A(X)=\sum_\theta E_\theta\circ E_\theta$ (Schur
product), and $\operatorname{tr}\widehat M_A(K_n)=(n^2-2n+2)/n$.

The precise question, preregistered in issue #11821, is whether
$\operatorname{tr}\widehat M_A(X)\le\operatorname{tr}\widehat M_A(K_n)$
for every $n$ and every connected graph $X$ on $n$ vertices. Over all
graphs the statement is false: the empty graph has $\widehat M_A=I$ and
trace $n$. The paper's Laplacian results on the maximum trace are stated
for connected graphs, and A. Mohan, C. Tamon, Y. Xu and H. Zhan
(arXiv:2608.20739, 2026) restate the conjecture over connected graphs.

## Motivation

The diagonal entry $(\widehat M_A)_{aa}$ is the long-run average
probability that the walk started at $a$ is found at $a$, so the trace
measures how lazy the walk is. The frozen declaration
`D5/S3/Quantum/Dynamics/AverageMixingTraceMaximum.result` proves that
among connected graphs on $n$ vertices the complete graph is the laziest
for the adjacency Hamiltonian, the counterpart of the paper's Laplacian
result.

## Gap

Issue #11821 classifies the question as Tier 1 and records the bounded
literature check before any Lean: the four citing works listed by
Semantic Scholar (arXiv:2608.20739, 2404.02236, 2308.16378, 2211.02037)
were searched; arXiv:2608.20739 restates the conjecture as open and proves
Laplacian results only, and the others cite the paper generally. Web
searches for the average mixing matrix with trace, maximum and complete
graph, for the coauthor's thesis, and for vertex bounds on graph angles
found no proof; `google-deepmind/formal-conjectures` has no entry.

These are orchestrator-reported literature readings,
`not-found-in-searched-scope`; they do not establish exhaustive worldwide
novelty or exclude an independent answer. The graph-angle literature
(Cvetković–Rowlinson–Simić, *Eigenspaces of Graphs*) was not read.

## Route

1. For a vertex $a$ with a neighbour and an eigenvalue $\theta$, put
   $q=(E_\theta)_{aa}$ and $u=E_\theta e_a$. Then $Au=\theta u$,
   $u_a=q$ and $\|u\|^2=q$, so the coordinates of $u$ off $a$ have squared
   norm $q-q^2$.
2. Cauchy–Schwarz on the eigen-equation at $a$ gives
   $\theta^2q^2\le(n-1)(q-q^2)$. At a neighbour $b$ of $a$,
   $q=\theta u_b-\sum_{c\in N(b)\setminus\{a\}}u_c$ is a combination over
   $\deg b$ vertices other than $a$, so
   $q^2\le(\theta^2+n-2)(q-q^2)$.
3. Eliminating $\theta$ gives $(q^2-(n-1)(q-q^2))(q^2+q-q^2)\le0$, hence
   $q^2\le(n-1)q(1-q)$ and $q\le1-1/n$.
4. The numbers $(E_\theta)_{aa}$ are nonnegative with sum $1$ and each is
   at most $1-1/n$, so $(\widehat M_A)_{aa}=\sum_\theta(E_\theta)_{aa}^2\le
   1-2/n+2/n^2$. Every vertex of a connected graph with $n\ge2$ has a
   neighbour, so $\operatorname{tr}\widehat M_A(X)\le n-2+2/n$; for $n=1$
   the trace is $1$.
5. For $K_n$ with $n\ge2$, $A=J-I$: an eigenvector with eigenvalue other
   than $-1$ is constant with eigenvalue $n-1$, and
   $\operatorname{tr}A=0$ leaves exactly one such eigenbasis vector, so
   $(E_{n-1})_{aa}=1/n$, $(E_{-1})_{aa}=1-1/n$ and
   $\operatorname{tr}\widehat M_A(K_n)=n-2+2/n$.

## Falsifier

A connected graph on $n$ vertices whose average mixing matrix with respect
to the adjacency matrix has trace greater than $(n^2-2n+2)/n$ would
falsify the conjecture; the kernel-checked `result` excludes it. Replacing
the adjacency matrix by another Hamiltonian, or dropping connectivity,
changes the question.

## Evidence

The canonical source is
`D5/S3/Quantum/Dynamics/AverageMixingTraceMaximum.lean`; the only public
theorem is `result : claim`. The public definitions are the spectral
idempotent `idempotent`, the average mixing matrix `avgMixing` and
`claim`.

- Module statement identity: `sha256:e9ed4aafa0539ad392a8da26418ae5af60eaf51671d3d661f56e05577edd7ac5`.
- `result`: `sha256:543de5ce995d1f90520172a150daffb22fe40d8024fbab20b31098cb15fd7dd0`.
- `claim`: `sha256:6886baf6f8f18b6815d1b15135636c68dd967e4517343a3140921b3dd9f47e86`.
- `avgMixing`: `sha256:7611a60f0f8b9b05283e0dfe4e1ecda2ba69c0aa90a6b731bbba19c013596049`.
- `idempotent`: `sha256:64ed2f0892f8f978123e3bf15ad51c0d5ff7dc5b38413a148671ba2d3f512d5a`.
- Freeze event: `sha256:4219620e5a540f5ea48ae5ee766904b8e95a474f3e74c4ec82c1208c48408599`.

The proof uses only `propext`, `Classical.choice` and `Quot.sound`, with
no `native_decide`, `sorry` or new axiom. Inside `result`, the local fact
`vertex_bound` proves steps 1–3 for any vector $u$ with $Au=\theta u$ and
$\|u\|^2=u_a$; the local fact `simplex_bound` proves step 4; the local fact
`complete_diag` proves step 5.

## Triage

Tier 1 published conjecture; resolution `Proved` by
`D5/S3/Quantum/Dynamics/AverageMixingTraceMaximum.result`.
`proof_shape: content`; `admission_basis: open-problem-resolution`
(issue #11821). Utility `none`: the result is a theorem over every $n$.

### What the settlement shows

- **Proved inside `result`, as local facts:** `vertex_bound` gives
  $(E_\theta)_{aa}\le1-1/n$ at every vertex $a$ with a neighbour, for
  every simple graph on $n$ vertices, and `simplex_bound` turns it into
  $(\widehat M_A)_{aa}\le1-2/n+2/n^2$; neither assumes connectivity,
  which `result` uses only to give every vertex a neighbour.
- **Follows from those local facts, not stated as a declaration:** the trace
  bound $n-2+2/n$ holds for every graph on $n\ge2$ vertices without
  isolated vertices. Isolated vertices are exactly where the literal
  all-graphs reading fails, each contributing $1$ to the trace.
- **Proved in this module:** the per-vertex bound is attained at every
  vertex of $K_n$, where $(E_{n-1})_{aa}=1/n$ and
  $(E_{-1})_{aa}=1-1/n$.
- **Computed, not formalized:** over every graph of the NetworkX atlas
  with at most $7$ vertices, the maximum of the vertex bound equals
  $1-1/n$ and the maximum trace over connected graphs is attained only by
  $K_n$ (issue #11821).
- **Open:** uniqueness of the maximizer. Equality in the trace bound
  forces equality in step 3 at every vertex, hence every vertex adjacent
  to all others; this equality analysis is not formalized here. The
  paper's companion questions on the minimum trace and on graphs with
  constant diagonal remain open here.
- **Open follow-up:** whether the second laziest connected graph is the
  star $K_{1,n-1}$, which arXiv:2608.20739 raises from data on at most 9
  vertices. No additional theorem is included in this settlement.

## ASSUMED-UNVERIFIED

The bounded literature check does not establish worldwide priority or
absence of an independent solution; in particular the vertex bound may be
known in the graph-angle literature, which was not read. The Lean kernel
verifies the encoded statement and its axiom closure; correspondence to
the external paper is checked by reading the source, the definitions and
the mirror. The independence of `idempotent` from the chosen orthonormal
eigenbasis is a standard fact stated in its docstring and not formalized
in this module.
