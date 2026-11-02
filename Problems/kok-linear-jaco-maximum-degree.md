---
slug: kok-linear-jaco-maximum-degree
bibkey: kok2025jaco
doi: 10.48550/arXiv.2507.16500
triage: theorem
motivation_gids:
  - D5/S3/ConceptDynamics/GraphColoring/JacoMaximumDegree.result
---

# Kok's maximum degree and literal A319433 deletion

## Problem

Johan Kok, *Integer sequences with conjectured relation with certain graph
parameters of the family of linear Jaco graphs*, arXiv:2507.16500v1,
Section 2.2, Conjecture 2.2, states:

> For the finite linear Jaco graphs J_{n}(x), n=2,3,4,\dots the respective
> maximum degrees \Delta(J_{n}(x)) are yielded by the sequence A319433 with
> closed formula \Delta(J_{n}(x))=\lfloor\frac{2(n+2)}{1+\sqrt{5}}\rfloor-1,
> n=2,3,4,\dots
>
> Furthermore, it implies that sequence A319433 is p-graphical where
> p(G)=\Delta(G) and \mathcal{F}=\{G:G=J_{n}(x),n=1,2,3,\dots\}.

The formal graph is the underlying simple undirected graph of the finite
directed linear Jaco graph with `f(x)=x`. For vertices `v_i`, `1 ≤ i ≤ n`,
write `d_i` for the number of earlier vertices `v_k` satisfying
`2*k-d_k ≥ i`; for `i < j ≤ n`, the directed arc `(v_i,v_j)` exists exactly
when `2*i-d_i ≥ j`. `J_n(x)` forgets orientation and `Delta` is its ordinary
maximum degree.

The sequence term uses its actual offset-zero index. For `n > 0`, write the
canonical Zeckendorf representation with weights `Fib_2=1`, `Fib_3=2`, and no
consecutive occupied positions. Delete the digit position of weight `Fib_2`,
whether its digit is one or zero: remove occupied index 2 if present, lower
every surviving occupied index by one, and decode in the same Fibonacci
system. Call the result
`a(n)=deleteLeast(n)`, with `a(0)=a(1)=0`.

The complete assertion is

$$
\left(\forall n\in\mathbb N,\;2\le n\Rightarrow
\left(\Delta(J_n(x))=\left\lfloor\frac{2(n+2)}{1+\sqrt5}\right\rfloor-1
\land\Delta(J_n(x))=a(n)\right)\right)
\land
\left(\forall n\in\mathbb N,\;1\le n\Rightarrow
\Delta(J_n(x))=a(n)\right).
$$

The second conjunct retains the singleton `J_1(x)`, whose degree and deletion
value are both zero. The first conjunct starts at `n=2`, exactly as in the
source. The index-zero sequence term is not reassigned to `J_1`; no `J_0`,
offset shift, order cutoff, subsequence, changed graph, or extra premise is
included.

## Motivation

The theorem supplies a complete all-order resolution of the two clauses in
Conjecture 2.2 for the source's actual recursive graph and sequence indexing.
The fixed family `{J_n(x) : n ≥ 1}` therefore realizes every positive-index
term and every positive finite prefix under `p(G)=Delta(G)`.

## Gap

The source presents the statement as a conjecture. The accepted formal
delivery closes its universal graph and sequence assertions; finite tables,
the source's earlier graph results, and the bounded literature screen are not
used as substitutes for the Lean proof. Literature completeness, priority,
and worldwide non-settlement remain outside this dossier's evidence.

## Route

`JacoEndpointBeatty.endpoint_recurrence` identifies the actual recursive
endpoint array, and `endpoint_eq_beatty` proves its all-order golden Beatty
law. `JacoMaximumDegree.degree_formula` counts the actual incoming and
outgoing neighbor intervals. The deletion-block bridge identifies the literal
Zeckendorf deletion with the attained maximum, and
`max_degree_eq_deletion` proves the positive-order family, including the
singleton. The public `result` combines the floor formula for every `n ≥ 2`
with the same-index deletion identity and the full `n ≥ 1` family clause.

The deletion definitions in `D5/S1/Words/Powers/ZeckendorfDeletion` are a
consumed helper on the live path to `result`; that module is not presented as
an independent resolution of this problem.

## Falsifier

A falsifier would be a positive order for which the encoded recursive Jaco
graph has a maximum degree different from either the displayed floor value or
the literal same-index deletion. A mismatch in the graph carrier, a shift of
the sequence offset, or omission of the singleton would also falsify the
source-faithful interpretation. The kernel-checked `result` discharges these
possibilities for the stated definitions and quantifiers.

## Evidence

The settling declaration is
`D5/S3/ConceptDynamics/GraphColoring/JacoMaximumDegree.result`, whose exact
statement is the conjunction displayed above. Its owning Blueprint Scribe
contains the single typed `OpenProblemResolutionClaim` with resolution
`Proved` for this dossier. The corresponding source note is
[`Library/Certificates/kok2025jaco.md`](../Library/Certificates/kok2025jaco.md),
which records the verified locator
`https://arxiv.org/html/2507.16500v1#S2.Thmtheorem2` (Conjecture 2.2),
the DOI, and the original A319433/A014417 sequence attribution.

The unchanged D5/Reg sources carry the proof terms; the accepted scoped Lean
report supplies the standard axiom-closure and current-binding evidence.
Canonical frozen states record statement IDs and declaration name/kind lists.
No new Lean declaration, axiom, or reproof is introduced by this dossier. The
four-slot audit boundary for
the accepted delivery is:

| Target | Current audit state |
| --- | --- |
| `D5/S1/Words/Powers/ZeckendorfDeletion.deletion_block` | `declared_validated` |
| `D5/S3/ConceptDynamics/GraphColoring/JacoEndpointBeatty.beatty_bounds` | `declared_validated` |
| `D5/S3/ConceptDynamics/GraphColoring/JacoEndpointBeatty.beatty_threshold` | `declared_validated` |
| `D5/S3/ConceptDynamics/GraphColoring/JacoEndpointBeatty.endpoint_eq_beatty` | `declared_validated` |
| `D5/S3/ConceptDynamics/GraphColoring/JacoEndpointBeatty.endpoint_recurrence` | `declared_unresolved` — forbidden `Nat.decLe` dependency; issue [#25698](https://github.com/the-omega-institute/trureturing/issues/25698), comment 6582601274 |
| `D5/S3/ConceptDynamics/GraphColoring/JacoMaximumDegree.degree_formula` | `declared_unresolved` — forbidden `Nat.decLt` dependency; issue [#25698](https://github.com/the-omega-institute/trureturing/issues/25698), comment 6582601274 |
| `D5/S3/ConceptDynamics/GraphColoring/JacoMaximumDegree.max_degree_eq_deletion` | `declared_unresolved` — forbidden `Nat.decLt` dependency; issue [#25698](https://github.com/the-omega-institute/trureturing/issues/25698), comment 6582601274 |
| `D5/S3/ConceptDynamics/GraphColoring/JacoMaximumDegree.result` | registration remains unfinished; no false validation is asserted |

The unresolved continuation is `unknown` and supplies no missing source law.
These audit readings do not change the mathematical statement or its kernel
proof.

## Triage

**Proved:** `JacoMaximumDegree.result` proves both source clauses for the
actual finite recursive Jaco graphs and literal A319433 deletion. The Scribe
claim is attached only to this complete result. The endpoint and degree
lemmas are proof components, and the Zeckendorf deletion module is a consumed
helper rather than a second problem resolution.

**Proved structure:** The recursive endpoint law connects the graph
construction to the Beatty description. Incoming and outgoing neighbor
intervals give the vertex degrees, and the attainment argument supplies a
vertex meeting the maximum-degree bound. The deletion bridge therefore
identifies an attained maximum, rather than only an upper bound. The
positive-order identity also settles the source's dependent p-graphical
clause, including the singleton and every positive finite prefix.

**Unresolved extensions:** The result does not settle other graph parameters
or other Jaco defining functions. Extending this route requires an endpoint
law, a neighbor-counting formula and an attainment argument for the proposed
family; no such extension or further source-conjecture consequence is proved
here.

The source is a mathematical application of the cited article and OEIS
sequence. Attribution is retained; code licensing is not asserted.

## ASSUMED-UNVERIFIED

The literature and ownership checks are bounded to the source note and the
surfaces recorded there. They do not establish exhaustive priority,
worldwide openness, publisher status, or legal-code licensing. Four audit
targets remain unfinished in total: the three `declared_unresolved` targets
and the aggregate result without registration, under the linked issue
exception [#25698, comment 6582601274](https://github.com/the-omega-institute/trureturing/issues/25698#issuecomment-6582601274).
The `unknown` continuation is not a
claim of undecidability or inexhaustibility.
