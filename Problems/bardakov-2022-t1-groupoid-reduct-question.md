---
slug: bardakov-2022-t1-groupoid-reduct-question
bibkey: bardakov2024simplex
doi: 10.1134/S1055134424010012
url: https://arxiv.org/abs/2206.08906v1
triage: theorem
motivation_gids:
  - D5/S3/StatisticalMechanics/VertexModels/TetrahedralGroupoidReductRefutation.result
---

# A two-element T1-groupoid whose reduct is not a reduced T1-groupoid

## Problem

V. Bardakov, B. Chuzinov, I. Emel'yanenkov, M. Ivanov, T. Kozlovskaya and V. Leshkov, *Set-theoretical
solutions of simplex equations*, arXiv:2206.08906v1, Section 9.2 (Мат. труды 27(1) (2024), pp. 51–53;
Siberian Adv. Math. 34(1) (2024) 1–40), define a first tetrahedral 4-groupoid ($T_1$-groupoid)
$(X,*,\circ,\triangleleft,\triangleright)$ by four identities and a reduced $T_1$-groupoid $(X,*,\circ)$ by three
identities, both giving elementary 1-solutions of the tetrahedron equation. They write: "It is not clear
if there is a $T_1$-groupoid such that forgetting about $x\triangleleft y$ and $x\triangleright y$ will not yield
a reduced $T_1$-groupoid." The verbatim statements are in
[the literature note](../Library/StatisticalMechanics/bardakov2024simplex.md).

Issue [#14643](https://github.com/the-omega-institute/trureturing/issues/14643) reads the question as
whether the universal statement "the reduct $(X,*,\circ)$ of every $T_1$-groupoid is a reduced
$T_1$-groupoid" fails.

## Motivation

A $T_1$-groupoid gives the elementary 1-solution $R(x,y,z)=(x\triangleright(y\circ z),y,z)$ and a reduced
$T_1$-groupoid gives $R(x,y,z)=(x*(y\circ z),y,z)$. The source introduces the reduced system as a
two-operation analogue of the $T_1$-groupoid; the question asks whether every $T_1$-groupoid restricts
to one.

## Gap

Issue #14643 records the literature check before any Lean: the citing works of arXiv:2206.08906 do not
mention tetrahedral groupoids; Crossref, MathDB and the formal-conjectures repository show no answer;
`not-found-in-searched-scope`. The journal version keeps the question.

## Route

On $X=\{0,1\}$ put $x*y=x$, $x\circ y=x\wedge y$, $x\triangleleft y=x$ and $x\triangleright y=x$. The four
$T_1$ identities reduce to $x\wedge y=x\wedge y$ and $x=x$. The first reduced identity
$x\circ y=(x\circ z)\circ(y\circ z)$ fails at $x=y=1$, $z=0$, where the left side is $1$ and the right
side is $0$.

## Falsifier

The answer would fail under a reading of the axioms other than the printed one; the journal version
prints the same axioms.

## Evidence

The canonical source is `D5/S3/StatisticalMechanics/VertexModels/TetrahedralGroupoidReductRefutation.lean`,
with public `IsT1Groupoid`, `IsReducedT1Groupoid`, `claim` and `result : ¬ claim`. It imports only
Mathlib. `result` depends on no axiom; there is no `sorry` or `native_decide`.
The module statement is `sha256:69db89abd489c6f32fa36e390abd9dce98f20b07e0fdb2c9d01a20e4cc0491f6`, the
`result` statement `sha256:4e3d62d072135e8c8eaaed38c2189e72639d5353deecd7eba236997192565455` and the
`claim` statement `sha256:3e0f70a9644101ba06129d4d05e9ff39697e258b577c843093d3fc8022083672`. The Freeze
event is `sha256:5e7d55ef0b7475d5e9b944f2f70b2bd56b7375a8d0e46d9d17f366439e3a74ef`; it has no project-level
prerequisite.

## Triage

Tier 1 question of a 2022 paper (journal version 2024), preregistered in issue #14643 before any Lean.
`theorem`; resolution `refuted` (the universal statement fails, so the answer to the question is yes).

| declaration | proof_shape | escape_witness | admission_basis |
| --- | --- | --- | --- |
| result | bind-only | none | open-problem-resolution |

Utility is `kind=certified-instance; basis=refutes` (the claim and its refutation). There is no
digestion atom.

### What the answer shows

**Proved by `result`:** some $T_1$-groupoid has a reduct that is not a reduced $T_1$-groupoid, so the
answer to the question is yes.

**Argued, not formalized.**

- *The preceding sentence of the source.* The witness has $x*y=x=x\triangleright y$. So the source's
  sentence "if in $T_1$-groupoid $x*y=x\triangleright y$ then forgetting about operations
  $x\triangleleft y$ and $x\triangleright y$ yields a reduced $T_1$-groupoid" is false as stated; the same
  sentence appears in the journal version.
- *Mechanism.* The first $T_1$ identity constrains $\circ$ only through $\triangleleft$; when
  $\triangleleft$ is a projection it imposes nothing, while the first reduced identity
  $x\circ y=(x\circ z)\circ(y\circ z)$ is the same identity with $\triangleleft$ replaced by $\circ$. Any
  $\circ$ that violates the first reduced identity gives a witness, as long as $*$ and $\triangleright$
  satisfy the remaining identities.
- *Size.* A one-element set satisfies every identity, so two elements is the smallest size.

**Open.** Which additional identities between $\triangleleft$, $\triangleright$ and $\circ$ make the reduct of
a $T_1$-groupoid reduced.

## ASSUMED-UNVERIFIED

The English journal version (Siberian Adv. Math.) was not read; the Russian original was. The bounded
literature check does not establish exhaustive worldwide novelty, priority, or the absence of an
independent answer.
