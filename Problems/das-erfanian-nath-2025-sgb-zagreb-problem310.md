---
slug: das-erfanian-nath-2025-sgb-zagreb-problem310
bibkey: das2025sgbzagreb
doi: 10.48550/arXiv.2501.06124
url: https://arxiv.org/abs/2501.06124v1
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/Graph/SubgroupGenerating/ZagrebInequality.hansen_vukicevic
---

# The full finite-group Zagreb question

## Problem

Shrabani Das, Ahmad Erfanian and Rajat Kanti Nath, *Zagreb indices of subgroup
generating bipartite graph*, arXiv:2501.06124v1, Problem 3.10, printed page 13
(native HTML anchor `S3.Thmtheorem10`):

> Is there any finite group G such that B(G) does not satisfy Hansen-Vukičević conjecture?

The exact registered universal event is that, for every finite group G,

$$
\frac{M_1(\mathcal B(G))}{|V(\mathcal B(G))|}
\le \frac{M_2(\mathcal B(G))}{|E(\mathcal B(G))|}.
$$

The disjoint vertex parts are all ordered pairs $G\times G$ and all subgroups
$L(G)$. Repeated pair entries are allowed. A pair $(a,b)$ is adjacent exactly
to $\langle a,b\rangle$. All subgroup isolates remain. The real index $M_1$
sums squared degrees over every vertex; $M_2$ sums endpoint-degree products
over each actual unordered edge once. The edge and vertex denominators are
$|G|^2>0$ and $|G|^2+|L(G)|>0$. Trivial, abelian and non-two-generated groups
are included, without additional assumptions.

The formal answer to the original existential question is **NO**.
Final publication review and required CI remain pending; this dossier records
no official settlement or solved-problem KPI.

The source locator, attribution and rights boundary are in the
[citation note](../Library/FiniteGroups/das2025sgbzagreb.md).

## Motivation

The source establishes the inequality for specific finite-group families and
asks whether any finite group can fail it. A universal answer must preserve
the full graph, especially its isolated subgroup vertices and ordered pairs.

## Gap

The source's unrestricted index identities reduce the question to
$|L(G)|\sum_H\Pr_H(G)^2\ge1$. The theorem supplies the standard square-sum
bound for the complete generating-pair partition and closes the full
mathematical statement. Accepted audit binding remains unresolved under the
linked exception below. Final publication review, required CI and delivery
remain separate obligations.

## Route

Put $m=|G|^2$, $k=|L(G)|$, $r(H)=|\{(a,b):\langle a,b\rangle=H\}|$ and
$S=\sum_H r(H)^2$, summing over every subgroup. The complete pair partition
gives $\sum_H r(H)=m$. Pair vertices have degree one and subgroup vertices
have degree $r(H)$, including degree zero.

The injective map sending a pair to the unordered edge joining it to its
generated subgroup has image exactly the literal edge finset. Therefore
$M_1=m+S$, $M_2=S$, $|E|=m$ and $|V|=m+k$. These match source Theorem 3.1
(`S3.Thmtheorem1`) and Theorem 3.2 (`S3.Thmtheorem2`), with
$\Pr_H(G)=r(H)/m$. Source Theorem 3.3 (`S3.Thmtheorem3`) identifies the
equivalent criterion $kS\ge m^2$.

The pinned Mathlib declaration `sq_sum_le_card_mul_sum_sq`, applied to the real
values $r(H)$, gives exactly $m^2\le kS$. Clearing the positive denominators
proves the registered comparison. The formal proof retains the actual graph
and uses the supplier's `sum_pairCount`, `edge_count`, `degree_pair` and
`degree_subgroup`; only the original private visibility of the last two changes.

## Falsifier

A finite group whose literal graph has $M_1/|V|>M_2/|E|$ would refute the
registered event. A changed graph carrier, omitted subgroup isolates, unordered
generating pairs, duplicated edge contributions or an extra group hypothesis
would invalidate source correspondence and must fail independent evaluation.

## Evidence

The compiled endpoint is
`D5.S3.Combinatorics.Graph.SubgroupGenerating.ZagrebInequality.hansen_vukicevic`.
Its retained D5 source defines both Zagreb indices on the inherited finite
simple graph; its compiled axiom closure contains only `propext`,
`Classical.choice` and `Quot.sound`.

The source, graph conventions and native Theorems 3.1–3.3 and Problem 3.10
are directly readable in the fixed arXiv HTML. The prior bounded source and
later-answer qualification is described in
[issue #28349](https://github.com/the-omega-institute/trureturing/issues/28349).
The two prospective probabilities are both 0.65; they are forecasts rather
than mathematical evidence. The unchanged exact event is in the
[immutable preregistration](https://github.com/the-omega-institute/trureturing/issues/28349#issuecomment-6731353916).

The retained Reg source compiles but is **not** `declared_validated`. Its
assessment is `declared_unresolved`, `IE-C050 ClosedTruthReadout`,
`unclassified_form:source.coordinate_dependency`,
`missing=0;selected=#[3];scope=4`. A dependency-closed source-coordinate/readout
reconstruction and accepted binding evidence are missing. The concrete
[unfinished-audit disclosure](https://github.com/the-omega-institute/trureturing/issues/28349#issuecomment-6731659148)
is the linked-issue exception under CLAUDE §3.9.

The inherited SGB modules are separately owned frozen parent work integrated
from published commit `4419f6eab133becbd680239fc623f3da27826038` in
[PR #28357](https://github.com/the-omega-institute/trureturing/pull/28357).
That draft is an explicit unmerged dependency. The original `degree_pair` and
`degree_subgroup` declarations are public with unchanged statements and proof
bodies; their owning frozen module is canonically repinned. The parent's
proofs, source attribution, dossier, registration exception and resolution
claim retain their own ownership. This consumer supplies no parent settlement
or KPI.

## Triage

Theorem for the entire published question. The decisive mechanism is
the complete pair partition and its square-sum bound, transported to the literal
unordered edges. The compiled scope already includes all finite groups; no
nonabelian or nontrivial restriction is needed. The source's family-specific
Zagreb inequalities are subsumed by the universal conclusion. This does not
settle the source's other topological-index
questions or the separate SGB energy problem.

All five theorems have `proof_shape: bind-only`. The private
`pairEdge_injective` and `actual_edges` are consumed by `second_formula`;
`first_formula` and `second_formula` are consumed by `hansen_vukicevic`.
The endpoint has `admission_basis: open-problem-resolution`. The helpers are
consumed proof organization, and no new escape witness or new parent
mathematics is claimed.
Equality classification, sharp refinements and extensions beyond this literal
graph are unassessed neighboring boundaries, with no new solved claim here.

## ASSUMED-UNVERIFIED

Accepted Reg binding remains unresolved. Final independent publication review,
required CI, the parent dependency's merge, this PR's merge and first-dev
verification are pending. No official mathematical terminal, complete delivery
or solved-problem KPI is asserted. Model diversity and independence of the
forecasts are unverified. The journal body and rights, uninspected literature
and worldwide priority remain unverified; bounded searches do not establish
absence of an earlier answer.
