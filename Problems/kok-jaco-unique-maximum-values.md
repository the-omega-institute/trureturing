---
slug: kok-jaco-unique-maximum-values
bibkey: kok2025jaco
doi: 10.48550/arXiv.2507.16500
triage: theorem
motivation_gids:
  - D5/S3/ConceptDynamics/GraphColoring/JacoMaximumDegree.result
---

# Kok's unique maximum-degree values and infinite realizing family

## Problem

Johan Kok, *Integer sequences with conjectured relation with certain graph
parameters of the family of linear Jaco graphs*, arXiv:2507.16500v1,
Section 2.2, Conjecture 2.3, printed page 5
([primary locator](https://arxiv.org/html/2507.16500v1#S2.Thmtheorem3)), states:

> For $t = 1,2,3,\dots$ the values given by sequence A003622 i.e. the Wythoff compound sequence AA: $a(t) = \lfloor t \times (\frac{1+\sqrt{5}}{2})^2\rfloor -1$ are the unique maximum degrees of corresponding linear Jaco graphs.
>
> Furthermore, it implies that sequence A003622 is $p$-graphical where $p(G) = \Delta(G)_{unique}$ and $\mathcal{F} \in \{G:G=J_n(x), n = 1,2,3,\dots\}$.

The preceding paragraph says the maximum-degree values that appear once
across graph orders are intended and explicitly excludes $\Delta(J_1(x))=0$.
This is numerical value uniqueness across orders, not a singleton set of
maximizing vertices within one graph; Conjecture 2.5 concerns the latter.

Retain the original recursive graph with $f(x)=x$. For every positive $i$,
let $d_i=\#\{j:1\le j<i,\ 2j-d_j\ge i\}$. For every positive $n$,
$J_n$ is the simple undirected graph on $\{1,\ldots,n\}$ with an edge
$\{i,j\}$ exactly when $1\le i<j\le n$ and $2i-d_i\ge j$.
Write $\Delta_n$ for its ordinary maximum vertex degree,
$\phi=(1+\sqrt5)/2$, and $a(t)=\lfloor t\phi^2\rfloor-1$.
For an integer $k$, define

$$
U(k)\iff k\ge1\ \land\ \exists n\ge2,\quad
\Delta_n=k\ \land\ \forall m\ge2,\ (\Delta_m=k\Rightarrow m=n).
$$

The complete assertion, with natural graph orders and term indices, is

$$
\left(\forall k\in\mathbb Z,\ k\ge1\Rightarrow
  [U(k)\iff\exists t\ge1,\ k=a(t)]\right)
\ \land\
\left(\exists r:\mathbb N_{>0}\to\mathbb N_{>0},\ \forall t\ge1,\
 r(t)\ge2\ \land\ a(t)\ge1\ \land\ \Delta_{r(t)}=a(t)
 \ \land\ \forall m\ge1,\ [\Delta_m=a(t)\Rightarrow m=r(t)]\right).
$$

There is one whole infinite indexed family $G_t=J_{r(t)}$, not only separate
finite prefixes. Every positive graph order remains in the reference class,
including $m=1$ in the realizing clause. The Lean witness is a function on
all natural numbers whose assertions are restricted to positive indices.
It additionally identifies $r$ with `realizingOrder`; no value at zero is
claimed as a source sequence term.

The source conventions are explicit. Read the printed family/element notation
memberwise: each realizing graph belongs to the class of source graphs. The
introduction's existential realizing-family definition permits selection of
corresponding orders; neither exhaustion of all orders nor $r(t)=t$ is
required. Extend that termwise definition to the positive infinite index set
printed in Conjecture 2.3. On
$D=\{J_n:n\ge1,\ U(\Delta_n)\}$, interpret the qualified parameter as
$p_D(G)=\Delta(G)$. No value is assigned outside $D$. Read “are the unique
maximum degrees” as the full iff classification, retaining both inclusions.
These conventions normalize the source's notation; they are not an
author-issued correction or a certificate of uniquely intended semantics.

## Motivation

The existing all-order degree theorem for the same recursive graph makes the
multiplicity of each positive degree value accessible. Conjecture 2.3 asks
which values have a singleton fiber and whether the entire displayed sequence
has one admissible infinite realizing family. This is distinct from the
maximum-degree formula of Conjecture 2.2 and from Conjecture 2.5's vertex-count
question.

## Gap

The published source presents Conjecture 2.3 as a conjecture. In the supplied
bounded qualification, the complete primary article and author TeX, original
graph definitions in arXiv:1506.06538v1, an arXiv Jaco-title query returning
18 metadata records, Crossref metadata and Olga's abstract did not identify a
specific prior resolution of 2.3. Later journal full texts were not verified
because publisher reads failed. Repository/issue searches for Jaco, 2.3 and
A003622 found no dedicated earlier 2.3 unit in the searched scope. These are
source and search qualifications, not proofs of worldwide openness or
priority.

The known MathDB answer to Conjecture 2.2 by Shivam Patel
([primary answer](https://mathdb.com/p/369423/maximum-degree-formula-conjecture-for-finite-linear-jaco-gra),
solution timestamp 2026-08-20T11:27:39.872868Z), together with the pre-existing
OEIS formula, is prior content for 2.2. Its fresh-resolution credit is zero.
A separate report concerns 2.5; neither is evidence of a 2.3 solution. The
current dossier adds no worldwide absence-of-proof or first-priority claim.

## Route

Use the existing source graph `JacoDomPathDiameterRefutation.jaco` and
`JacoMaximumDegree.result` directly. Put $B(q)=\lfloor q\phi\rfloor$ and
$C(q)=\lfloor q/\phi\rfloor$. Inverting the existing degree law gives, for
every integer $k\ge1$, exactly the orders

$$
B(k+1)-1\le n\le B(k+2)-2.
$$

The lower endpoint is at least two. This interval is a singleton precisely
when $C(k+2)=C(k+1)$. A strict jump corresponds to $k+1$ in the positive lower
Beatty sequence. Apply pinned Mathlib's
`Irrational.beattySeq_symmDiff_beattySeq_pos` at $\phi$ and $\phi^2$ to obtain
the complementary upper Beatty sequence, hence both directions of the value
classification. The floor identities and irrationality facts are reused
Mathlib results; the recursive endpoint and maximum-degree laws are existing
repository suppliers, not newly proved content here.

One function selects the singleton endpoint:
$r(t)=B(\lfloor t\phi^2\rfloor)-1$ for every $t\ge1$.
`realizingOrder` uses `Int.toNat`; its proved lower bound shows that no
truncation occurs on this domain. Positivity of $a(t)$ excludes the singleton
graph's zero degree, extending uniqueness to every positive $m$, including
one. No additional graph or uniqueness hypothesis is assumed.

## Falsifier

A positive value with a different fiber from the stated interval, a positive
unique value outside the displayed sequence, a positive sequence term without
its unique source order, or failure of the one realizing function at any
positive index would contradict the asserted result. A changed graph,
finite-order cutoff, missing reverse implication, omitted $m=1$, or replacement
by maximizing-vertex uniqueness would fail the stated source correspondence.

## Evidence

The single settling declaration is
`D5/S3/ConceptDynamics/GraphColoring/JacoUniqueMaximumValues.result`.
Its owning Scribe attaches exactly one `OpenProblemResolutionClaim` with
`ResolutionKind.Proved` to this dossier. The displayed statement retains both
the full positive-value classification and one infinite realizing function.
The source identity and attribution use the existing
[kok2025jaco note](../Library/Certificates/kok2025jaco.md); the exact 2.3
locator and formula are given above.

The complete D5 and mirrored Reg proof terms supply the mathematical and
typed audit evidence. The current scoped report for those two modules binds
`result` to statement ID
`sha256:64eeb63382c166d212a6e03e7714254085c02b789bf83e4485644792d65c0775`.
Its axiom closure is `propext`, `Classical.choice`, and `Quot.sound`, with no
`sorryAx`. The public declaration inventory is `UniqueValue`, `sequenceValue`,
`realizingOrder`, and the single theorem `result`. The private helpers are
consumed on its proof path. Conservative classification is
`proof_shape: bind-only`, `escape_witness: none`,
`admission_basis: open-problem-resolution`, under preregistered issue
[#25813](https://github.com/the-omega-institute/trureturing/issues/25813).
No new mathematical declaration or supplier reproof is introduced by this
dossier. Existing supplier audit limitations remain those disclosed in the
[2.2 dossier](kok-linear-jaco-maximum-degree.md); this resolution does not
recertify them.

Source attribution: Johan Kok and the Online Encyclopedia of Integer
Sequences, [A003622](https://oeis.org/A003622). Mathematical notation is
adapted from the article under [CC BY-SA 4.0](https://creativecommons.org/licenses/by-sa/4.0/)
and the [OEIS terms](https://oeis.org/wiki/The_OEIS_End-User_License_Agreement).
No claim about licensing third-party executable code is made.

## Triage

**Proved:** Under the explicit source conventions, `result` establishes the
entire two-clause Conjecture 2.3 event for the original $f(x)=x$ recursive
family: every positive unique value and only those values, every positive
sequence index, and one whole infinite family with uniqueness across all
positive graph orders. The p-graphical clause therefore follows with the
qualified parameter on $D$; no finite-prefix substitute is used.

**Proved mechanism and surviving scope:** The interval fiber and the
complementary Beatty partition explain why precisely these values occur once.
The same interval description remains valid for every positive value,
including values that occur more than once; they are excluded from the
restricted parameter domain, not from the source graph class. The proof
retains the zero-degree singleton as an allowed graph while excluding zero
from the unique-positive-value assertion. It imposes no order cutoff.

**Unresolved exact next candidate:** Determine the complete classification of
the number of maximizing vertices in $J_n(x)$ for every $n\ge1$, then compare
it with the separate Conjecture 2.5. This is a different fiber statistic;
value uniqueness does not imply vertex-set uniqueness. The reported prior
2.5 answer must be read and compared before admitting any fresh candidate.
No new theorem or credit for that question is claimed here. Other defining
functions $f(x)$ require their own endpoint, degree and multiplicity laws;
no such extension or further dependent source conjecture is settled.

## ASSUMED-UNVERIFIED

Correspondence between the printed prose and the explicit typed source
normalization is an interpretation, not a Lean theorem about author intent.
A globally total qualified parameter, an exhaustive realizing family, an
order-preserving witness requirement and $G_t=J_t$ are outside that reading.
The literature screen and specific prior-answer qualifications are bounded;
later publisher texts, worldwide openness and priority remain unverified.
The Reg continuation `unknown` asserts no undecidability or inexhaustibility.
Final resolution-binding validation requires current frozen membership of
the settling declaration. Canonical rendering alone does not certify this
binding; this source unit makes no claim that publication obligations are
complete.
