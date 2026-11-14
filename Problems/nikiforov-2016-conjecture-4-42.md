---
slug: nikiforov-2016-conjecture-4-42
bibkey: nikiforov2016beyondgraphenergy
doi: 10.1016/j.laa.2016.05.011
url: https://arxiv.org/abs/1510.02850v2
triage: theorem
motivation_gids:
  - D5/S3/Quantum/NormCompression/SchattenContinuity.schattenPow_trace
---

# Nikiforov's full complex-matrix Conjecture 4.42

## Problem

Vladimir Nikiforov, *Beyond graph energy: norms of graphs and matrices*,
arXiv:1510.02850v2, §4.5.1, Conjecture 4.42, printed p. 48. The
[source note](../Library/Eigenstructure/nikiforov2016beyondgraphenergy.md)
identifies the versioned preprint, journal publication and access limits.
This dossier anchors exactly the entire assertion of Conjecture 4.42:

> Let $p>2$, $n\ge r\ge2$, and let $A=[a_{i,j}]$ be an $n\times n$
> complex matrix with $\|A\|_{\max}\le1$. If $A$ is $r$-partite, then
> $\|A\|_p\le\|T_r(n)\|_p$.
> Equality holds if and only if the matrix $|A|=[|a_{i,j}|]$ is the
> adjacency matrix of $T_r(n)$.

Write $S_p(A)=(\sum_i\sigma_i(A)^p)^{1/p}$. Here $\sigma_i(A)$ are
the nonnegative square roots of the eigenvalues of $A^*A$, including
zeros. Multipartiteness uses one partition of the common row and column
index set into $r$ nonempty parts, with all within-part blocks zero.
The graph $T_r(n)$ has all edges between distinct parts, whose sizes
differ by at most one. Its vertex labels are arbitrary. The modulus is
entrywise, not the operator absolute value $(A^*A)^{1/2}$.

Thus the claim is the universal proposition

$$
\begin{aligned}
\forall p\in\mathbb R,\ \forall n,r\in\mathbb N,\ \forall A\in M_n(\mathbb C),\quad
& p>2\ \land\ 2\le r\le n\ \land\ (\forall i,j,\ |A_{ij}|\le1)
\ \land\ R_r(A)\\
&\Longrightarrow
\bigl(S_p(A)\le S_p(T_r(n))\bigr)
\ \land\
\bigl(S_p(A)=S_p(T_r(n))\ \Longleftrightarrow\ M_r(A)\bigr),
\end{aligned}
$$

where $R_r$ is the common-partition condition and $M_r$ identifies the
entrywise modulus with Turán adjacency after a simultaneous vertex
relabeling. No symmetry, Hermitianity or nonnegativity is assumed.

| Source clause | Lean counterpart in `NikiforovConjecture442Refutation` | Fidelity |
| --- | --- | --- |
| Every real $p>2$ | `∀ (p : ℝ), 2 < p →` in `claim` | No integral-exponent restriction |
| Every $n\ge r\ge2$ | Natural binders, `2 ≤ r`, `r ≤ n` | Both integer inequalities retained |
| Every complex $n\times n$ matrix | `Matrix (Fin n) (Fin n) ℂ` | All entries and matrices remain quantified |
| Max-norm at most one | `∀ i j, ‖A i j‖ ≤ 1` | `max_bound_iff` identifies the finite maximum when $n>0$ |
| Common nonempty index parts | `rPartite r A` | `parts_iff` gives the disjoint-cover/nonempty-part formulation |
| Balanced comparison graph | `turanMatrix n r` | Pinned `SimpleGraph.turanGraph`; `balanced_relabel` identifies arbitrary balanced parts |
| Schatten norm | `UpperBranchReduction.schattenNorm p A` | Existing singular-value definition and column-Gram bridge, with zeros retained |
| Upper bound and both equality directions | Conjunction and biconditional in `claim` | Neither the upper bound nor either equality direction is omitted |
| Entrywise modulus equals Turán adjacency | `isTuranModulus r A` | One permutation on both indices; `modulus_partition_iff` gives arbitrary equipartition adjacency |
| Comparison independent of labels | `schatten_reindex`, `balanced_norm`, `source_equality` | Common relabeling preserves the norm for positive real exponents |
| Negation of the entire assertion | `result : ¬ claim` | A witness refutes the universal conjunction through equality sufficiency |

## Motivation

The equality condition would make the entrywise modulus sufficient to
determine an extremal Schatten norm. The counterexample separates that
entrywise information from the spectral information retained in the
column Gram matrix. It concerns the complex-matrix conjecture, not the
adjacent graph-only problems or the older Ky Fan-gap conjecture.

## Gap

The proposed implication from Turán modulus to equality fails. The
upper-bound-only assertion remains unresolved by this proof. Removing
the equality criterion gives a distinct question; no answer to that
successor or to graph-only variants is asserted here. The literature
screen has the explicit limits stated in the source note.

## Route

Use the saved witness at $p=6$ and $n=r=3$:

$$
A=\begin{pmatrix}0&1&1\\-1&0&1\\-1&-1&0\end{pmatrix},\qquad
B=T_3(3)=\begin{pmatrix}0&1&1\\1&0&1\\1&1&0\end{pmatrix}.
$$

Singleton parts prove multipartiteness. Every entry has modulus at most
one, and $|A|=B$. The existing functional-calculus trace formula and
`cfc_pow_id` give

$$
S_6(A)^6=\operatorname{Re}\operatorname{tr}((A^*A)^3)=54,
\qquad
S_6(B)^6=\operatorname{Re}\operatorname{tr}((B^*B)^3)=66.
$$

The equality-sufficiency direction of `claim` would imply $S_6(A)=S_6(B)$.
Applying the existing `schattenNorm_rpow` identity would then give
$54=66$. Exact finite arithmetic closes the contradiction. The fixed
exponent is a witness against the universal claim; it does not narrow
the source claim's domain.

## Falsifier

A mismatch in common-partition semantics, complex modulus, balanced
graph labels, singular-value conventions, or the two exact trace values
would invalidate this refutation route. The source-bridge helpers address
these correspondences, and the final theorem has no additional
hypotheses. This result supplies no counterexample to the upper bound
alone, no dimension-minimality statement and no general Hadamard-family
claim.

## Evidence

The saved mathematical source is
[NikiforovConjecture442Refutation.lean](../D5/S3/Quantum/Schatten/NikiforovConjecture442Refutation.lean),
with SHA-256
`c85978f2c8e123b4c8ed7566a3d76a64e9160acd6ad6774f1d41a2a22da41098`.
The settling declaration is
`D5.S3.Quantum.Schatten.NikiforovConjecture442Refutation.result`.
The [independent CLI evaluation](https://github.com/the-omega-institute/trureturing/issues/30394#issuecomment-6878322596)
reports the selected canonical build and current literal-type/import
check both exiting zero, with axiom closures contained in
`propext`, `Classical.choice`, `Quot.sound`. The compiled claim has literal
type `Prop` and the result has literal type `Not claim`.

The [owning Blueprint Scribe](../Blueprint/D5/S3/Quantum/Schatten/NikiforovConjecture442Refutation.scribe.cs)
displays all four public definitions and the complete negated claim.
Its sole `OpenProblemResolutionClaim` attaches `ResolutionKind.Refuted`
to `result` for this dossier. That binding is publication metadata;
freeze, admission and delivery are separate obligations.

The following declaration judgement uses the saved proof's existing
classification. Names are local to the module. All 11 helper theorems
are private and consumed on the final result's proof path.

| Declaration | proof_shape | Actual consumer |
| --- | --- | --- |
| `parts_iff` | bind-only | `witness_parts` |
| `max_bound_iff` | bind-only | `witness_bound` |
| `balanced_relabel` | bind-only | `modulus_partition_iff`, `balanced_norm` |
| `schatten_reindex` | bind-only | `balanced_norm` |
| `modulus_partition_iff` | bind-only | `source_equality`, `result` |
| `balanced_norm` | bind-only | `source_equality`, `result` |
| `source_equality` | bind-only | `result` |
| `six_trace` | bind-only | `result` |
| `witness_parts` | bind-only | `result` |
| `witness_modulus` | bind-only | `result` |
| `witness_bound` | bind-only | `result` |
| `result` | bind-only | External Conjecture 4.42 refutation |

The public definitions are `rPartite`, `turanMatrix`, `isTuranModulus`
and `claim`; the private definition `witness` supplies the displayed
matrix. No helper or final result supplies an escape witness. Admission
basis is the external `open-problem-resolution` exception. The sole
public theorem is the designated refutation result and is exempt from
four-slot escape registration under CLAUDE.md §3.9; no audit-wrapper
theorem is introduced.

## Triage

This dossier concerns one externally posed assertion, preregistered in
[#30394](https://github.com/the-omega-institute/trureturing/issues/30394).
Its immutable [mathematical terminal](https://github.com/the-omega-institute/trureturing/issues/30394#issuecomment-6878332497)
settles that full assertion as refuted. It does not record completed
publication or a delivered KPI increment. The mathematical result is an
application of existing spectral identities and finite normalization,
not a new abstract spectral theorem or an originality certification.

- **Computed:** At $p=6$ and $n=r=3$, the witness in Route has
  $|A|=B=T_3(3)$ but $S_6(A)^6=54$ and $S_6(B)^6=66$.
- **Proved:** Entrywise modulus forgets signs and phases, whereas the
  Schatten norm retains column-Gram spectral information. The displayed
  pair has the same modulus and unequal norms, so Turán modulus is not
  sufficient for equality. This refutes the full universal conjunction
  through its equality-sufficiency direction.
- **Unresolved:** The upper bound alone remains unresolved by this
  refutation. Removing the equality criterion gives a separate question;
  Hermitian and graph-only variants are not settled here. No
  dimension-minimality or general-family result is claimed.
- **Unresolved impact:** Dependencies of published claims on Conjecture
  4.42 have not been verified, so no such claims are reclassified. The
  established consequence is limited to the full assertion and its failed
  equality-sufficiency direction; the adjacent questions retain the
  boundaries stated above and in Gap and Falsifier.

## ASSUMED-UNVERIFIED

Exhaustive literature coverage, priority and global novelty are
`ASSUMED-UNVERIFIED`. The source note records the accessible original PDF
and TeX, the bounded later-paper and metadata readings, and the
inaccessible publisher texts. Publisher/preprint textual identity has
not been verified. Absence of a resolution in the searched metadata
does not exclude an unindexed or inaccessible earlier resolution.

Independent pre-freeze review, canonical freezing, post-freeze admission,
the required review seats, remote required checks and the first dev-push
verification remain publication obligations. The existing evaluator was
from the same reported model family and exposed to repository priors;
neither model diversity nor sterile independence is claimed. The
upper-bound-only successor remains mathematically unresolved here.
