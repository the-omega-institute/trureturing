---
slug: farinholt-2015-qunit-real-weak-values
bibkey: farinholt2015weak
doi: 10.48550/arXiv.1512.02113
url: https://arxiv.org/abs/1512.02113v2
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Measurement/QunitRealWeakValueRefutation.result
---

# Real weak values for qunits and the span of two bases

## Problem

J. M. Farinholt, A. Ghazarians and J. E. Troupe, *The Geometry of Qubit Weak
Values*, arXiv:1512.02113v2, Section 7, conjecture:

> Let $M \in \mc{S}$. Then for all $i,j \in \{0, 1, \dots n-1\}$, $\mc{W}_{\varphi_i, \psi_j}(M) \in \mbb{R}$ if and only if $M \in \mc{R}_{\varphi, \psi}$.

Here $\varphi_0,\dots,\varphi_{n-1}$ and $\psi_0,\dots,\psi_{n-1}$ are
orthonormal bases of $\mathbb{C}^n$ with $\varphi_0$, $\psi_0$ distinct and
nonorthogonal; $\mathcal{S}$ is the space of traceless Hermitian matrices;
$\mathcal{W}_{\varphi,\psi}(M)=\langle\psi|M|\varphi\rangle/\langle\psi|\varphi\rangle$
is the weak value; and $\mathcal{R}_{\varphi,\psi}$ is the real span of the
traceless projectors $|\varphi_i\rangle\langle\varphi_i|-I/n$ and
$|\psi_j\rangle\langle\psi_j|-I/n$. The paper proves the direction
$M\in\mathcal{R}\Rightarrow$ all weak values real, and for $n=2$
$\mathcal{R}$ is its pre- and post-selection plane.

## Motivation

The paper characterizes qubit weak values geometrically and names the
characterization of real weak values for $n>2$ as the first step towards
higher dimensions. The frozen declaration
`D5/S3/Quantum/Measurement/QunitRealWeakValueRefutation.result` refutes the
conjecture.

## Gap

Issue #12048 classifies the conjecture as Tier 1 and records the bounded
literature check before any Lean:

- arXiv v2 is the latest version, with no journal reference;
- the citing works (arXiv:1512.02256 and a 2016 SPIE paper on QKD with weak
  measurements) do not treat $n>2$;
- arXiv:1702.04836, 2202.11145, 1612.07023 and 2211.05692 do not
  characterize all-real weak values for $n>2$;
- web searches return nothing that settles the conjecture.

These are orchestrator-reported literature readings,
`not-found-in-searched-scope`; they do not establish exhaustive worldwide
novelty or exclude an independent answer.

## Route

1. Take $n=3$, $\varphi_i=e_i$, and $\psi_j$ the $j$-th column of the
   orthogonal matrix $O=\frac13\begin{pmatrix}1&2&2\\2&1&-2\\2&-2&1\end{pmatrix}$.
   The overlap $\langle\psi_j|\varphi_i\rangle=O_{ij}$ is never $0$, and no
   $\varphi_i$ equals a $\psi_j$.
2. $M=E_{01}+E_{10}$ is traceless Hermitian, and its nine weak values are
   $2,\tfrac12,-1;\ \tfrac12,2,-1;\ 0,0,0$, all real.
3. In $M=\sum a_i(|e_i\rangle\langle e_i|-I/3)+\sum b_j(|\psi_j\rangle\langle\psi_j|-I/3)$
   only the $\psi$ projectors have off-diagonal entries; the entries
   $(0,1)$, $(0,2)$, $(1,2)$ give $(2b_0+2b_1-4b_2)/9=1$,
   $(2b_0-4b_1+2b_2)/9=0$ and $(4b_0-2b_1-2b_2)/9=0$. The last two force
   $b_0=b_1=b_2$, and then the first reads $0=1$.

## Falsifier

The kernel-checked `result` exhibits orthonormal bases of $\mathbb{C}^3$,
with every pair of basis vectors distinct and nonorthogonal, and a traceless
Hermitian matrix with all weak values real outside
$\mathcal{R}_{\varphi,\psi}$. This excludes the direction "all weak values
real $\Rightarrow M\in\mathcal{R}$". Changing the weak value, the trace-0
restriction or the span changes the question.

## Evidence

Exact SymPy arithmetic gives the overlaps and weak values above and finds
no real solution of $M=\sum c_k(P_k-I/3)$. As controls, an element of
$\mathcal{R}$ has all-real weak values and is found in $\mathcal{R}$, and
$i(E_{01}-E_{10})$ has non-real weak values (issue #12048).

The canonical source is
`D5/S3/Quantum/Measurement/QunitRealWeakValueRefutation.lean`. Its public
declarations are `weakValue`, `IsONB`, `tracelessProj`, `realSpan`, `claim`
and `result`. The frozen module state has statement identity `sha256:89a321dc370ee2f337a16f4bff7e2103b4acb42c7ac7f49b2d61ade77ff87653`.
The result declaration has statement identity `sha256:366175e94668d9b63dcad0264131ea04cb97ea9d639b7131e14e42e4a6b2df40`. The Freeze event
is `sha256:a4061caab45372b9ec6d5e4ca8eff6c7cc4ddf98a2825bb98fda8391c53b5dd4`. It has no project-level frozen prerequisites (pinned
Mathlib only). The proof uses only the standard axioms `propext`,
`Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new
axiom.

## Triage

Tier 1 published conjecture; resolution `Refuted` by
`D5/S3/Quantum/Measurement/QunitRealWeakValueRefutation.result`.
`proof_shape: bind-only` (evaluation at explicit bases and an explicit
matrix); `admission_basis: open-problem-resolution` (issue #12048). Utility
`certified-instance`, refuting `claim`.

### What the refutation shows

- **Proved in this module:** for $n=3$ the direction "all weak values real
  $\Rightarrow M\in\mathcal{R}_{\varphi,\psi}$" fails, for bases satisfying
  every hypothesis of the conjecture.
- **Where the conjecture fails:** the set of traceless Hermitian $M$ with all
  weak values real is a real subspace containing $\mathcal{R}$, which has
  dimension at most $2n-2$. When both bases are real and all overlaps are
  nonzero, every real symmetric traceless $M$ has real weak values, a space of
  dimension $n(n+1)/2-1$, which exceeds $2n-2$ for $n\ge3$. So the conjecture
  fails for every such pair of real bases with $n\ge3$ (model derivation, not
  formalized). At $n=2$ the two dimensions agree, matching the paper's qubit
  results.
- **Computed, not formalized (orchestrator):** the failure is not confined to
  real bases. For $n=4$, the standard basis against the Fourier basis $F_4$
  (all overlaps of modulus $1/2$) and $M=E_{02}+E_{20}$ give weak values
  $\pm1$ and $0$, all real, with $M\notin\mathcal{R}$.
- **Computed, not formalized (scout reading):** for random complex bases with
  $n=3,4,5$ the real-weak-value subspace has dimension exactly $2n-2$, the
  dimension of $\mathcal{R}$; real bases give $5,9,14$ against $4,6,8$, and the
  Fourier pair at $n=4$ gives $7$ against $6$.
- **Open here:** whether the conjecture holds for generic bases (all pairs
  outside a proper algebraic subset), as the dimension count suggests, and a
  description of the exceptional pairs.
- **Unchanged:** the paper's qubit characterization and its Proposition
  ($M\in\mathcal{R}\Rightarrow$ all weak values real) do not depend on the
  conjecture.

## ASSUMED-UNVERIFIED

The bounded literature check does not establish worldwide priority or
absence of an independent counterexample. The Lean kernel verifies the
encoded statement and its axiom closure; correspondence to the external
paper, including the reading of "for all $i,j$" with every weak value
defined and of $\mathrm{Span}_{\mathcal{S}}$ as the real span, is checked by
reading the source and the definitions.
