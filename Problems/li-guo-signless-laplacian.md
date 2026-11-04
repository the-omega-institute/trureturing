---
slug: li-guo-signless-laplacian
bibkey: liguo2025degreesequence
doi: 10.2298/FIL2513551L
url: https://www.pmf.ni.ac.rs/filomat-content/2025/39-13/39-13-22-25952.pdf
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/Graph/SignlessLaplacian/LiGuoDegreeSequenceRefutation.result
---

# Li–Guo Conjecture 2.22

## Problem

Wen-Jun Li and Ji-Ming Guo, *A new conjecture on Laplacian eigenvalues and degree
sequence of a graph*, Filomat 39:13 (2025), 4551–4564, Conjecture 2.22, asserts

$$
\sum_{q_i\geq2}(q_i-2)^2\leq
\left(1-\frac1{d_1}\right)\sum_{i=1}^n d_i(d_i-1).
$$

The graph is finite, simple, undirected and loopless; $Q=D+A$ is its signless
Laplacian, and all eigenvalues occur with algebraic multiplicity. Degrees are
ordered decreasingly in the source. The denominator restricts the assertion to
$d_1=\Delta(G)>0$. There is no connectedness or regularity hypothesis.
Preregistration: [#23307](https://github.com/the-omega-institute/trureturing/issues/23307).

### Statement echo

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| A graph with $n$ vertices | `n : ℕ`, `G : SimpleGraph (Fin n)` in `claim` | All finite labelled simple graphs; no additional structural restriction. |
| $Q=D+A$ and the eigenvalues $q_i$ | Existing `sourceMatrix G .signless` and `graphSpectrum G .signless` | Actual real eigenvalues, retaining multiplicity. |
| Sum over $q_i\geq2$ | `TQ` | Sum of $\max(q-2,0)^2$ over the entire spectral multiset; the summand at $q=2$ is zero. |
| $d_1$ | `SimpleGraph.maxDegree` | The maximum vertex degree. |
| Degree-sequence sum | `R` | Sum over vertices; permutation of the degree sequence preserves it. |
| $1/d_1$ is defined | `0 < G.maxDegree` | Positive denominator domain; an edgeless graph is excluded. |
| The displayed upper bound | `TQ G ≤ R G` | Every degree is cast to $\mathbb R$ before subtraction and division. |
| Universal assertion is false | `result : ¬ claim` | A triangle contradicts the unchanged assertion. |

`TQ`, `R` and `claim` retain the literal binding definitions in #23307. Graph
matrices, degrees and multiplicity-preserving spectra reuse their existing owners.

## Motivation

`D5.S3.Combinatorics.Graph.SignlessLaplacian.LiGuoDegreeSequenceRefutation.result`
refutes the universal claim using $C_3$: its signless spectrum is $\{4,1,1\}$,
its maximum degree is $2$, and the two sides are $4$ and $3$.
This is a certified instance (`generality: I`), with admission basis
`open-problem-resolution (#23307; Refuted)`. The unbounded cycle family is not
part of this Lean certificate.

## Gap

The literature screen recorded in #23307 found no published settlement of this
exact conjecture in the inspected sources. Özdemir's *Remarks on two conjectures
of Li and Guo on Laplacian eigenvalues and degree sequences*, version DOI
10.5281/zenodo.23669771, concerns ordinary-Laplacian Conjectures 1.1 and 1.2.
Chen–Li–Lv, arXiv:2610.29048v1, concerns induced-subgraph spectral-radius
conjectures. Neither supplies this signless truncated-square settlement.
The screen includes incomplete full-text and author-index coverage; literature
completeness and worldwide absence remain `ASSUMED-UNVERIFIED`.

## Route

The private helper `triangle_degree` applies Mathlib's cycle degree theorem.
`triangle_maxDegree` applies the regular-graph maximum-degree theorem.
`triangle_matrix` evaluates the existing signless matrix at the triangle as
$\begin{pmatrix}2&1&1\\1&2&1\\1&1&2\end{pmatrix}$.
`triangle_charpoly` obtains $(X-4)(X-1)(X-1)$ by the three-by-three determinant
formula. `triangle_spectrum` applies the Hermitian characteristic-root theorem
and polynomial root identities, retaining both occurrences of $1$.
`triangle_values` evaluates $T_Q(C_3)=4$ and $R(C_3)=3$; `result` specializes
`claim` to this graph and derives a contradiction.

## Falsifier

A mismatch in the source domain, the denominator domain, the matrix, spectral
multiplicity or degree arithmetic would invalidate the source correspondence.
The certificate uses real subtraction and actual graph eigenvalues. It does not
replace the assertion by a variant excluding triangles or imposing a cycle-order
restriction.

## Evidence

Canonical module:
`D5/S3/Combinatorics/Graph/SignlessLaplacian/LiGuoDegreeSequenceRefutation.lean`,
with its corresponding Blueprint Scribe. The only public theorem is `result`;
the six proof helpers are private. Its proof shape is `bind-only`, obtained by
upstream application, finite entry evaluation, polynomial normalization and the
claim specialization. No escape witness or new general spectral theorem is asserted.

The public result is the designated refutation result (`basis=refutes`) and is exempt from four-slot escape registration (CLAUDE.md §3.9).

### Finite experiment

[Immutable experiment directory](https://github.com/the-omega-institute/trureturing-experiments/tree/42ee049a937e7915d9fc24bdce9f35c73c43e5ea/docs/reports/li-guo-signless-laplacian).
The script is `check.py` at commit
`42ee049a937e7915d9fc24bdce9f35c73c43e5ea`, verified by `git cat-file`.
SHA-256: `aee5314867ff87b0895d7292fe5c67aba70e36dbca98769aa9b0d719c779b9a3`.
The implementation seat extracted those immutable bytes and ran
`python3 /Users/auric/.sshx/360d40b89af3a13f47fd8a9f/attempt-1/stageb/experiment-check.py`
with SymPy 1.14.0; exit 0, ending in `ALL_CHECKS_OK`.
The computation uses exact cyclotomic reduction and independent rational root
isolation for cycle orders $3\leq n\leq35$. It also checks source Lemma 2.5(1)
for complete graphs of orders $2$–$8$, and source Lemma 2.5(4), Theorem 2.14 and
Remark 2 for cycles of orders $3$–$35$. These are finite computations, not Lean
certification of their uniform extensions.

## Triage

### What the settlement shows

1. **Proved in Lean.** The binding universal claim fails already at $C_3$:
   spectrum $\{4,1,1\}$, $T_Q=4$, $R=3$, maximum degree $2$.
   Evidence: private `triangle_spectrum`, `triangle_values`, `triangle_maxDegree`,
   and public `result` in the canonical module.
2. **Proved in prose from the certified values.** Subtracting $2$ from
   $4,1,1$ gives $2,-1,-1$. The positive-part squares are $4,0,0$, while the
   discarded negative-tail squares are $1,1$. Thus the two tails have square
   masses $4$ and $2$, and the conjectured bound is $3$. This is the
   positive/negative spectral-tail imbalance at the triangle. No separate
   adjacency-spectrum theorem is delivered.
3. **Computed.** All nine orders $3,7,11,15,19,23,27,31,35$ violate the bound.
   Evidence: the immutable finite experiment above, exact cyclotomic formula
   checks and independent rational root isolation; command exit 0 and script
   SHA-256 as in Evidence. This covers $C_{4k+3}$ only for $0\leq k\leq8$.
4. **Computed.** Even cycle orders $4,6,\ldots,34$ satisfy equality; orders
   $5,9,13,17,21,25,29,33$ lie strictly below the bound. Evidence: the same
   experiment, command exit 0 and script SHA-256 as in Evidence. These finite
   cases are the nearest verified surviving instances here.
5. **Open.** The all-orders $C_{4k+3}$ formula, all-orders cycle classification,
   and connected regular-graph classification have no Lean certification in
   this delivery. The finite experiment does not close these uniform statements.
6. **Open.** A repaired conjecture for arbitrary irregular graphs and connected
   ordinary-Laplacian Conjecture 1.1 are not settled by this certificate.

Conjecture 2.22 is the final conjecture on the source's last page. No later
source theorem depends on it. This refutation leaves the earlier source results
and their own hypotheses intact; it does not refute the ordinary-Laplacian
conjecture or prove a repaired general graph inequality.

## ASSUMED-UNVERIFIED

Literature completeness, global priority, unread full texts and author-index
coverage remain unverified. The general cycle-family and classification claims
listed as open have not been certified in Lean here. The finite experiment is
independent computational evidence and is not a kernel proof of those extensions.
