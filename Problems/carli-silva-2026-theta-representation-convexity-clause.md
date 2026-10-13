---
slug: carli-silva-2026-theta-representation-convexity-clause
bibkey: carlisilva2026kfoldtheta
doi: null
url: https://arxiv.org/html/2609.06312v1
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/Orthogonality/ThetaRepresentationNonconvex.result
---

# The theta representation set: Question (iv), first convexity clause

## Problem

Marcel K Carli Silva, Gabriel Coutinho, Thiago Oliveira and Levent Tunçel,
*On some k-fold generalizations of Lovász theta and their sandwich theorems*,
arXiv:2609.06312v1, §7, Open questions, item (iv), ask:

> Is the orthonormal representation set $\texttt{M}_k(G)$ convex? If not, can one characterize its closed convex lower hull, i.e., the convex corner whose support function is $\varphi_k(G,\cdot)$?

This dossier identifies **only the first convexity clause** of that version
and item. The closed convex lower hull characterization is a separate,
unresolved question. The preregistration is
[issue #15881](https://github.com/the-omega-institute/trureturing/issues/15881).

In §5.3, the proof of Theorem 16 defines, for a finite ordinary simple graph
$G=(V,E)$ and $n=|V|$,

$$
\texttt{M}_k(G)=\left\{x\in\mathbb R_+^V:\begin{array}{l}
\exists M\in\mathbb S_+^V,\quad I-M\in\mathbb S_+^V,\quad \operatorname{tr}(M)=k,\\
\exists u:V\to\mathbb R^V,\quad \forall i\in V,\ \langle u_i,u_i\rangle=1,\\
\forall i,j\in V,\ ij\in E\Rightarrow\langle u_i,u_j\rangle=0,\\
\forall i\in V,\ x_i=u_i^{\mathsf T}Mu_i
\end{array}\right\}.
$$

Here $\mathbb S_+^V$ consists of real symmetric positive semidefinite
$V\times V$ matrices. The source's order $M\preccurlyeq I$ means
$I-M\succeq0$, and its matrix inner product is $\langle A,B\rangle
=\operatorname{tr}(AB)$, so $\langle I,M\rangle=k$ is exact trace equality.
One common matrix and one common vector family realize every coordinate.
There is no rank or projector restriction. The ambient real dimension is
exactly $|V|$. In the source's convention, $u$ is an orthonormal
representation of $\overline G$: orthogonality is imposed on edges of $G$,
with no condition on its nonedges. Vectors at nonadjacent vertices may
coincide; the family need not be a mutually orthogonal basis.

## Motivation

The source extends theta-type relaxations for the maximum $k$-colorable
induced subgraph problem. Its Theorem 16 identifies, for nonnegative vertex
weights $w$, the support values
$\varphi_k(G,w)=\max\{\langle w,x\rangle:x\in\texttt{M}_k(G)\}$.
Immediately after that theorem, the authors state that even convexity for
$k>1$ is unclear. This is a recent explicit external question, the first
research tier of the preregistration, rather than a repository-created
assertion. The settling declaration supplies a negative answer at $k=2$.

## Gap

The exact affirmative assertion encoded by `claim` is

$$
\forall V\text{ finite},\quad |V|\ge1\ \Longrightarrow\
\forall G\in\operatorname{SimpleGraph}(V),\quad
\forall k\in\mathbb R,\quad
0<k\le |V|\ \Longrightarrow\ \operatorname{Convex}_{\mathbb R}(\texttt{M}_k(G)).
$$

Convexity quantifies over every $x,y\in\texttt{M}_k(G)$ and every real
$a,b\ge0$ with $a+b=1$, requiring $ax+by\in\texttt{M}_k(G)$.
The Lean binders are `V : Type`, `[Fintype V]`, `[DecidableEq V]`,
`1 ≤ Fintype.card V`, `G : SimpleGraph V` and real `k` with the displayed
guards. Finite decidable equality adds no graph restriction. The upper
bound is the feasible positive trace range of PSD contractions, not an
additional hypothesis quoted from Theorem 16, which states $k>0$.

`D5/S3/Combinatorics/Orthogonality/ThetaRepresentationNonconvex.result`
has the closed type `¬ claim`. Its proof uses $V=\operatorname{Fin}(5)$,
$G=C_5$ and $k=2$, which satisfy every guard and lie in both the integer
and real parameter regimes. Thus the negative answer is not a claim that
every graph or every $k>1$ gives a nonconvex set. It does not answer the
second clause of item (iv).

## Route

Label the five-cycle by $0,1,2,3,4$ with edges $01,12,23,34,40$.
The kernel-checked construction realizes the three points

$$
a=(0,1,1,1,1),\qquad b=(1,0,1,1,1),\qquad c=(1,1,0,1,1)
$$

using $M=\operatorname{diag}(1,1,0,0,0)$ and the standard coordinate
vectors $e_0,e_1,e_2\in\mathbb R^5$. The respective families are

$$
(e_2,e_0,e_1,e_0,e_1),\qquad
(e_1,e_2,e_0,e_1,e_0),\qquad
(e_0,e_1,e_2,e_0,e_1).
$$

Each edge joins orthogonal unit vectors, and the common diagonal matrix
is a PSD contraction of trace two. Hence all three points belong to the
full source-defined set. Their average is
$t=(2/3,2/3,2/3,1,1)$.

To exclude $t$, allow an arbitrary source-admissible $M,u$. Write
$A=u_3$, $B=u_4$. The edge $34$ makes them orthogonal unit vectors.
The saturated coordinates $t_3=t_4=1$ give zero quadratic form for
$I-M$ at both vectors. Positivity yields $MA=A$ and $MB=B$.
For $P=AA^{\mathsf T}+BB^{\mathsf T}$ and
$r(w)=w-\langle A,w\rangle A-\langle B,w\rangle B$, expansion gives

$$
w^{\mathsf T}(M-P)w=r(w)^{\mathsf T}Mr(w)\ge0.
$$

Thus $M-P$ is PSD, and its trace is $2-1-1=0$. PSD trace-zero rigidity
forces $M=P$. The projection is a consequence of saturation and exact
trace; it is never imposed on the realization domain.

Set $\alpha=\langle A,u_0\rangle$, $\beta=\langle B,u_2\rangle$,
$p=\langle A,u_1\rangle$, $q=\langle B,u_1\rangle$.
Edges $40$ and $23$ imply $\langle B,u_0\rangle=0$ and
$\langle A,u_2\rangle=0$. The coordinate equations therefore give

$$
\alpha^2=\beta^2=\frac23,\qquad p^2+q^2=\frac23,
\qquad \|r(u_i)\|^2=\frac13\quad(i=0,1,2).
$$

Edges $01$ and $12$ give residual inner products $-\alpha p$ and
$-\beta q$. Cauchy–Schwarz yields

$$
\frac23p^2\le\frac19,\qquad \frac23q^2\le\frac19,
\qquad p^2+q^2\le\frac13,
$$

contradicting $p^2+q^2=2/3$. This excludes every allowed matrix and vector
family, not just the displayed endpoint realizations. If the set were
convex, $d=(b+c)/2$ would belong to it, followed by
$a/3+2d/3=t$. The excluded average refutes convexity.

## Falsifier

The first-clause settlement requires the literal closed negation of the
full assertion and feasible witnesses in its actual domain. Restricting
$M$ to projectors, choosing separate matrices for separate coordinates,
reversing the complement convention, changing trace equality to an
inequality, or excluding only selected realizations would not settle it.
The `representationSet` definition retains those source conditions, and
the exclusion in `## Route` starts from arbitrary allowed $M,u$.
The sole public theorem is the utility-designated `result : ¬ claim`;
its designated-refutation exemption does not assert four-slot registration.

## Evidence

**Kernel evidence.** The Lean module proves the closed refutation with
axioms contained in `{propext, Classical.choice, Quot.sound}`. Its private
helpers construct all three feasible realizations, derive saturation for
the full matrix domain and exclude the average. The Blueprint describes
the entire source definition, the universal assertion and its negation.
The typed `OpenProblemResolutionClaim(Refuted)` binds only this dossier's
first-clause slug to `ThetaRepresentationNonconvex.result`; this binding
is not itself a proof or a certification of publication priority.

**Source and version evidence.** The primary
[HTML definition](https://arxiv.org/html/2609.06312v1#S5.SS3),
[question](https://arxiv.org/html/2609.06312v1#S7.I1.i4.p1) and
[TeX source](https://arxiv.org/src/2609.06312v1) identify the exact domain
and two separate clauses. The source/version reading of 2026-10-12 found
only v1 in the [submission history](https://arxiv.org/abs/2609.06312)
and [exact-id API](https://export.arxiv.org/api/query?id_list=2609.06312),
with published and updated timestamps 2026-09-06T00:03:11Z. The served
paper retains item (iv). Tunçel's
[publication directory](https://www.math.uwaterloo.ca/~ltuncel/publications/)
lists this title as a September 2026 research report. No journal
publication was verified.

**Bounded prior-resolution evidence.** The source qualification recorded
in issue #15881 found no answer in the checked current paper, author
listing or bounded arXiv metadata searches. The search combining
“orthonormal representation” with “convex”, or title “k-fold” with
“theta”, returned the candidate and arXiv:2012.00554v2; the latter's
abstract describes a general optimization hierarchy, not an answer to
this named question, and its full text was not audited. An author/topic
search from the candidate's submission through 2026-10-12 returned the
candidate alone; a wider date/topic search returned it and two unrelated
abstracts. Exact-id metadata search returned zero, which does not measure
full-text citations. A Crossref title query's five leading records had no
exact match. These are bounded no-resolution-found readings.

The source cites Thiago Oliveira's *The Maximum k-Colorable Subgraph
Problem* (2024), Theorem 5.11, for support-function equivalence. Its
[primary catalog](https://doi.org/10.11606/D.45.2024.tde-25082025-111037)
verifies defense on 2024-07-12 and public release on 2025-08-25. The thesis
full text was not qualified; the catalog cannot exclude an answer there.

The preregistration's duplicate screen found no matching candidate in
the repository's Problems/Library/formal content, public problem-page
snapshot or GitHub issue searches, and no textual match in the 1,797
searched Lean/Markdown/JSON/YAML/TOML files of
[formal-conjectures at bdda9748e16d1df263db93d5241011fb399abfae](https://github.com/google-deepmind/formal-conjectures/tree/bdda9748e16d1df263db93d5241011fb399abfae).
Text searches are not theorem-equivalence proofs or worldwide priority
certificates.

## Triage

### What the settlement shows

**Proved in Lean: failure mechanism.** The exact $C_5,k=2$ counterexample
shows failure of convex closure even though the matrix constraints are
convex. Realization also requires a single compatible unit-vector family
on the whole graph. At the proposed average, two saturated adjacent
coordinates exhaust the trace and force a two-dimensional projection;
the remaining edge equations then violate residual Cauchy–Schwarz.
Convexity of the matrix domain alone cannot establish convexity of the
joint representation image. The argument uses actual feasible endpoints
and a universal exclusion, rather than separately optimized coordinates.

**Proved in Lean: reusable insight and boundary.** Saturation converts
the full PSD-contraction domain into a rigid projection in this
configuration; removing the projection components turns edge constraints
into bounds on residual inner products. The module's `saturated_projection`
helper proves the trace-two identity for any finite real coordinate type
with two orthogonal saturated unit vectors. The contradiction itself is
the five-cycle calculation above. No assertion of minimal graph order,
nonconvexity for every $k>1$, or a family beyond this instance is made.
Changing exact trace or the saturated coordinates removes hypotheses
used by this proof; the outcome for those changed problems remains open
here.

**Source-attested surviving statements.** Theorem 16's support-function
identity does not assert convexity of the realizing set and is not
contradicted by its nonconvexity. Section 6, equation (25), separately
defines the convex substitute $\operatorname{TH}_k(G)=
k\operatorname{TH}(G)\cap[0,1]^V$, and Theorem 21 proves
$\varphi_k\le\vartheta_k$. These are source-attested statements,
not companion theorems of this Lean module. Neither definition nor
inequality identifies $\texttt{M}_k(G)$ with that substitute.

**Open neighbouring questions and effect on the source.** The second
clause's closed convex lower hull characterization remains unresolved
by this result. The source's question about SDP representability and
the corresponding hull-description problem are not additional Lean
settlements in this unit. A general
characterization of when $\texttt{M}_k(G)$ is convex is also outside this
settlement. No other source question is answered and no other source
theorem is refuted here; the support-function and separate convex-body
results retain their stated scopes. No unverified special-case convexity
claim is supplied as a replacement theorem.

## ASSUMED-UNVERIFIED

Worldwide absence of an earlier answer, publication priority, unpublished
or unindexed follow-ups and the unread thesis full text remain
ASSUMED-UNVERIFIED. OpenAlex and Semantic Scholar citation endpoints
returned HTTP 429; MathDB yielded an application shell or HTTP 403, and
general-web searches yielded access or human-verification pages. They
provide no zero-hit evidence. ArXiv metadata searches do not cover all
bibliographies or full text, and the public page and issue screens are
snapshot readings. The first-clause theorem does not certify any of
these literature premises, resolve the hull clause, or imply that the
whole two-clause item has been settled.
