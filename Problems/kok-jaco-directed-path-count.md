---
slug: kok-jaco-directed-path-count
bibkey: kok2014jaco
doi: null
url: https://arxiv.org/abs/1404.1714v1
triage: theorem
motivation_gids:
  - D5/S3/ConceptDynamics/GraphColoring/JacoDirectedPathCount.result
---

# The original Jaco directed path-count equivalence

## Problem

Johan Kok, Paul Fisher, Bettina Wilkens, Mokhwetha Mabula and Vivian
Mukungunugwa pose Proposition 4.4 in Section 4 of
https://arxiv.org/abs/1404.1714v1. Its proof placeholder is “(Conjectured)”;
the final list explicitly asks “[Open problem: Prove Proposition 4.4]”.

For every natural $k\geq7$ and every Fibonacci bracket index $i$ with
$F_i<k\leq F_{i+1}$, the complete question is

$$
\bigl(d^+(v_{k-1})\ne d^+(v_k)\ \land\ d^+(v_k)\ne d^+(v_{k+1})\bigr)
\quad\Longleftrightarrow\quad
\bigl(\psi(v_{k-1})\ne\psi(v_k)\ \land\ \psi(v_k)\ne\psi(v_{k+1})\bigr).
$$

The vertices have positive labels. An original directed arc goes from
$v_h$ to $v_j$ exactly when $h<j$ and $j\leq2h-d^-(v_h)$.
The degree is the infinite outdegree. Each $\psi(v_n)$ counts distinct
shortest directed edge sequences from $v_1$ to $v_n$ in that endpoint's
own induced finite truncation $J_n(1)$. Length counts edges.
Both adjacent comparisons, the iff, the lower bound and all bracket
indices are part of the claim.

## Motivation

The source asks whether adjacent repetition of the infinite outdegrees
exactly matches adjacent repetition of actual shortest-directed-path
cardinalities. Resolving the full equivalence requires connecting the
endpoint arithmetic to actual directed paths, including transitions
between Fibonacci distance layers.

## Gap

The original source explicitly poses the question as open. The bounded
literature scope and access gaps are recorded in the source note
`Library/Certificates/kok2014jaco.md`. No whole-equivalent earlier answer
was authenticated in that scope. Matching MathDB bodies and some journal
or follow-up full texts remain unread; worldwide openness, absence of
earlier solutions, novelty and priority are unverified.

## Route

Every forward path stays between its endpoints. Decomposition by its
last predecessor gives finiteness of the actual path sets; consecutive
forward arcs give connectivity and hence positive shortest-path counts.
The same endpoint bounds identify paths across larger truncations
without changing their directed edge sequences or their lengths.

For each edge budget $l$, the reachable positive labels are exactly those
at most $F_{l+2}$. The endpoint identities prove this by induction, yielding
the exact shortest-distance threshold. Removing the final edge of a
shortest path to a label $n$ in the layer $F_j<n\leq F_{j+1}$ gives a
bijection with pairs consisting of a predecessor in
$[\operatorname{beattyOut}(n),F_j]$ and an actual shortest path to it.
Appending the unique final arc is the inverse. Thus the cardinality is
a suffix sum of positive actual path counts.

Within one layer the next lower endpoint stays fixed or increases by
one, so the sums agree exactly when that endpoint stays fixed. A separate
Fibonacci-boundary argument handles the change of distance layer.
Together these facts prove both adjacent comparisons in the original
iff. The proof uses no converse of Proposition 4.3.

## Falsifier

A source mismatch in direction, endpoint truncation, infinite outdegree,
path distinctness, or a missing original quantifier would invalidate the
source interpretation. A label $k\geq7$ with a valid Fibonacci bracket
and unequal truth values for the two conjunctions would refute the
stated mathematical event. A counterexample to the last-edge bijection,
positivity or boundary argument would identify the corresponding proof
obligation; finite computations alone cannot establish the universal iff.

## Evidence

The complete result is
`D5/S3/ConceptDynamics/GraphColoring/JacoDirectedPathCount.result : claim`;
`claim` has type `Prop` and retains the full source event.
The typed `Proved` resolution is attached only to that result.
The public `path_count_foundations` and `fibonacci_distance` theorems
supply actual finite positive counts, truncation invariance and the
all-budget Fibonacci threshold. The existing Blueprint contains the
full source formulas and the mechanism of the count proof.

The admission basis is `open-problem-resolution`; the live
`reachable_prefix` proof also supplies substantive path-existence
content. Utility remains `none`. Supporting lemmas and the claim
definition are not separate external-problem resolutions.

## Triage

`theorem`. The complete original Proposition 4.4 is established by the
single result above.

### What the settlement shows

The decisive structure is the actual final-edge bijection and its suffix
sum of positive shortest-path cardinalities. Within each Fibonacci layer,
moving the lower summation endpoint removes a positive term precisely
when the count changes. At Fibonacci boundaries the proof separately
establishes endpoint counts equal to one and the following counts at
least two, so the layer transition is covered.

The internal adjacent-equality argument holds for every label $n\geq5$;
the external result retains the published $k\geq7$ and every original
Fibonacci-bracket index. This proof makes the source equivalence
independent of the Proposition 4.3 converse. It establishes no correction
of that converse and no additional consequence asserted elsewhere in the
source. Analogous count laws for other Jaco functions or further source
questions remain open.

## ASSUMED-UNVERIFIED

The identification with the author's terminology rests on the
independently checked versioned source reading. It is not itself a Lean
theorem about the paper. The bounded literature checks do not certify
worldwide absence, novelty or publication priority.

The foundations registration has its validated certificate and current
binding. The distance registration remains unfinished with
`IE-C050/source.roles`, and the result registration remains unfinished
with `IE-C050/source.selection_missing`; neither has a current certificate.
These audit gaps are disclosed in
https://github.com/the-omega-institute/trureturing/issues/25912 under the
current linked-issue exception. Final independent reviews and remote
required CI are separate pending checks.
