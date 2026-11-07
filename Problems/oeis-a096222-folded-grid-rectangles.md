---
slug: oeis-a096222-folded-grid-rectangles
bibkey: barker2020a096222
doi: null
url: https://oeis.org/A096222/internal?rev=13
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/Geometry/FoldedGridRectangleSeries.result
---

# Barker's joint folded-grid rectangle conjectures

## Problem

The source is OEIS A096222 revision 13, Colin Barker's complete FORMULA
conjecture block, attributed Feb 04 2020:

```text
Conjectures from _Colin Barker_, Feb 04 2020: (Start)
G.f.: (1 - 3*x - 9*x^2 + 24*x^3) / ((1 - 2*x)*(1 - 4*x)*(1 - 8*x^2)).
a(n) = 6*a(n-1) - 48*a(n-3) + 64*a(n-4) for n>3.
(End)
```

The COMMENTS sentence fixes the object: "In this sequence we count the
rectangles in an a X b array of squares, where a=2^floor(n/2) and
b=2^ceiling(n/2)." The sequence was submitted by Bill Liebeskind.

For every natural n, including zero, put

$$
r_n=2^{\lfloor n/2\rfloor},\qquad s_n=2^{\lceil n/2\rceil}.
$$

Let a(n) count the actual grid-line endpoint rectangles: pairs
((x0,x1),(y0,y1)) of natural endpoint pairs satisfying
0 <= x0 < x1 <= r_n and 0 <= y0 < y1 <= s_n. Endpoints on the two axes
are chosen independently; different placements are distinct. In Lean,
natural divisions n/2 and (n+1)/2 implement the floor and ceiling.

The one original problem is the conjunction, on this same count, of

$$
A(X)=\sum_{n\geq0}a(n)X^n
=\frac{1-3X-9X^2+24X^3}{(1-2X)(1-4X)(1-8X^2)}
\quad\hbox{in }\mathbb Q[[X]],
$$

and, for every natural n >= 4,

$$
a(n)=6a(n-1)-48a(n-3)+64a(n-4).
$$

The denominator's constant coefficient is one, so its formal-series inverse
exists. The recurrence uses integer casts before signed subtraction. There
are no hypotheses on n beyond its stated guard and no finite upper bound.
The generating series includes a(0). Analytic convergence is outside this
formal-series statement. A recurrence-defined substitute would not establish
the required connection with rectangle placements.

## Motivation

Independent choices of two increasing grid-line endpoints give a direct
combinatorial meaning to the product of triangular numbers already present
in the source. Relating that count to both asserted identities establishes
that the published coefficient generators describe the original placements.
The frozen result linked above retains the count and both clauses as one
conclusion. The two formulas are not two separately counted problems.

## Gap

The source conjecture year is 2020; the preregistered classification is
Tier 1, a specific externally named OEIS formula block. Neither that year
nor that classification establishes difficulty, openness or priority.

The source's existing formula a(n)=r_n*s_n*(r_n+1)*(s_n+1)/4 is prior work.
The following pinned implementations also receive explicit credit; their
locators and mathematical correspondence are in the linked Library note.

| Prior body | Supplied content | Limit of the inspected body |
| --- | --- | --- |
| Georg Fischer's jOEIS A096222.java, revision 7424b90f536c7d509b1b092de0f43e0ebffa5c2d | Numerator [1,-3,-9,24], denominator [1,-6,0,48,-64], and a coefficient generator retaining Conjectural | No full endpoint-count-to-joint-claim proof |
| Geoff's LODA A096222.asm, revision f1b383b2344ab03ae8f79f41289360a6bd4394bd | Floor/parity closed formula and straight-line term generator | No all-index proof of both original clauses |
| gfis/OEIS-mat colin.holos.man, revision 1c42f8a58af04f3e566ec1fdf9a1f9014e755873 | A096222 recurrence-manifest membership | No endpoint-count proof |
| Sidney Cadot's recurrence catalog, revision ddcbe9d0c29c6d662849aed100547b12afa1eb5b | Initials [1,3,9,30] and recurrence coefficients [64,-48,0,6] | Parameters for a recurrence-defined generator, without the full placement bridge |

The bounded reuse search covered repository D5 sources including private
declarations, pinned Mathlib and materialized Lean packages, with exact ID,
full numerator, recurrence signature, half-exponent and folded-rectangle
wording searches. No exact whole-result owner was identified. The directly
reused upstream ingredients are Finset.card_product_filter_lt,
Nat.cast_choose_two and PowerSeries.eq_mul_inv_iff_mul_eq, together with
index, cast, coefficient and algebra normalization. There is no frozen D5
mathematical supplier for this module.

External searches covered the exact source ID in GitHub Lean code and arXiv,
the original OEIS revision and the four pinned bodies above. The exact-ID
GitHub Lean search returned zero with incomplete_results=false; the arXiv
exact-ID query returned zero. Target-ID and placement-wording repository
issue/PR searches identified the preregistration, with inspected broad-query
hits concerning other sequences. Broad punctuation-heavy or truncated
queries provide no exhaustive clearance. Targeted Leansearch/Loogle access
and MathDB content access encountered HTTP 403; those failures are not
negative search results. No complete joint proof was observed within the
inspected bodies. This does not establish worldwide absence or originality.

The current dev additions HardinA204612 and DirectSumHeredityRefutation concern
ordered binary-array minors and evolution-algebra heredity respectively;
neither supplies this endpoint-count identity. Source/shape searches found
no corresponding theory volume or digestion atom. This unit therefore uses
the uncovered freeze route without inventing a theory prerequisite.

## Route

For an axis with r unit intervals, Finset.card_product_filter_lt counts
increasing endpoint pairs by choose(r+1,2). Taking the product for the two
independent axes gives the actual count. Nat.cast_choose_two and cast
normalization identify its rational value with

$$
q(n)=\frac{2^{\lfloor n/2\rfloor}(2^{\lfloor n/2\rfloor}+1)
2^{\lceil n/2\rceil}(2^{\lceil n/2\rceil}+1)}4.
$$

The two possible relationships between the half exponents, and their shifts
by four, reduce q(n+4)=6q(n+3)-48q(n+1)+64q(n) to polynomial normalization.
Casting back gives the signed integer recurrence for every n >= 4.

Write D=(1-2X)(1-4X)(1-8X^2) and N=1-3X-9X^2+24X^3. Expansion gives
D=1-6X+48X^3-64X^4. Coefficient extensionality proves A*D=N: the four
initial coefficients use a(0),a(1),a(2),a(3)=1,3,9,30, while every later
coefficient vanishes by the recurrence. Since D has constant coefficient
one, the pinned inverse equivalence yields A=N*D^(-1). The public result
assembles exactly the two original conjuncts.

`admission_basis: open-problem-resolution`, preregistered in
[issue #27623](https://github.com/the-omega-institute/trureturing/issues/27623).
Every authored theorem and the Prop carrier are bind-only; there is no
escape witness. The necessary declarations and their live consumers are:

| Declaration | proof_shape | Consumers |
| --- | --- | --- |
| a | not-a-Proposition | count, countQ, recurrence, A, coefficientIdentity, claim |
| count | bind-only | countQ, coefficientIdentity |
| q | not-a-Proposition | countQ, recurrenceQ |
| countQ | bind-only | recurrence |
| recurrenceQ | bind-only | recurrence |
| recurrence | bind-only | coefficientIdentity, result |
| A | not-a-Proposition | coefficientIdentity, gf, claim |
| D | not-a-Proposition | denominator, denominatorConstant, coefficientIdentity, gf |
| N | not-a-Proposition | coefficientIdentity, gf |
| denominator | bind-only | coefficientIdentity |
| denominatorConstant | bind-only | gf |
| coefficientIdentity | bind-only | gf |
| gf | bind-only | result |
| claim | bind-only | result's statement type |
| result | bind-only | Terminal complete external joint resolution |

The local closed hex in coefficientIdentity is consumed ring normalization.
The helpers provide proof organization, without mathematical escape credit.
`utility: none`: this is an all-natural identity, not a delivered bounded
enumeration, checker, numerical reduction or certified finite instance.
The four initial coefficient calculations are steps in the infinite identity.

`question_answered`: the complete quoted Barker block on the actual
placement count, as registered in #27623.

`dominating_theorem_search`: `not-found-in-searched-scope` for an exact whole
settlement, within the bounded repository/private, pinned-upstream and public
source scope described above. General ingredients were found and reused.
Exhaustive dominating-theorem and global historical clearance remain
unverified; the result is not presented as a new general theorem.

## Falsifier

A rectangle omitted or counted twice by the endpoint representation would
invalidate source fidelity. A natural index with a different coefficient in
the asserted rational formal series, or an n >= 4 violating the signed
recurrence for the actual count, would refute the original joint claim.
The zero family illustrates why the recurrence alone is insufficient: it
satisfies that homogeneous relation but fails the generating function at
coefficient zero. A verified prior full settlement would invalidate the
external-resolution qualification, without making the Lean theorem false.
An audit or publication failure is not a mathematical counterexample.

## Evidence

The mathematical source is
`D5/S3/Combinatorics/Geometry/FoldedGridRectangleSeries.lean`, SHA256
`d06cb8b609dc0b1ac9862b61390eddd89b89904b5b451d85861a0f42d0c38469`.
The theorem result has statement_id
`sha256:0c8cc75cf33811397979b7c888b9d631535893d23d0683045bb2252cb7f2858b`;
its literal claim carrier has statement_id
`sha256:fb0f207e058dff8b1f4ad500bd3693f5d4539a676d45951891e7ee981c834b24`.
The canonical frozen member is
`Golden/Frozen/state/D5/S3/Combinatorics/Geometry/FoldedGridRectangleSeries.lean.json`.
The typed Scribe resolution binds this one dossier to result as Proved.

| Original clause | Exact formal counterpart |
| --- | --- |
| Every natural n, including zero | a : Nat -> Nat; A uses every natural coefficient |
| Sides 2^floor(n/2), 2^ceiling(n/2) | r=2^(n/2), s=2^((n+1)/2) using Nat.div |
| Actual independent grid-aligned placements | Filtered endpoint products with x0<x1<=r, y0<y1<=s; outer product/cardinality |
| Full rational formal generating function | A=PowerSeries.mk(fun n => (a n : Rat)); first conjunct of claim |
| Inverse of the entire denominator | Product (1-2X)(1-4X)(1-8X^2), constant coefficient one |
| Source n>3, without an upper bound | forall n : Nat, 4<=n -> ... in the second conjunct |
| Signed coefficients and subtraction | Counts cast to Int before 6*a(n-1)-48*a(n-3)+64*a(n-4) |
| Both assertions on the same count | Hypothesis-free result : claim, the literal conjunction |

The 15 authored declarations have 43 compiled report rows including compiler
internals. Their axiom closure is limited to Classical.choice, Quot.sound
and propext, with no sorry or private axiom. The source-bound one-module
scoped report has SHA256
`b0e02e5f9bc741c0edca880bba221687a4a331fe91b0fbb359ec41726dbde67c`.
Its 19 recorded source/config inputs match the unchanged mathematical unit.
This evidence is scoped and does not certify whole-project health.

The retained Reg source has SHA256
`4dd8fdee79ead64073efffd8e766fb40561c074146ddd6df0898bcb6345c1c48`.
It compares the whole natural-indexed actual count family with the zero
family. Its Law is the complete conjunction, bridge is Iff.rfl, variation
and sensitivity use the rejected family's failed constant coefficient, and
observational dependence distinguishes states zero and one. Continuation is
unknown and familyRecord is none. The local source-bound record is
declared_validated, diagnostic null, evidence_ref
`49dd0fd4158d1c5291a4bd965a813116c31baa72a99895e06dcc3bab9b7ac737`.
Required-CI/DTR reading remains pending; the local certificate alone does not
establish a completed public audit.

The fixed preregistration event is
`A096222-joint-rectangles-gf-recurrence-v1`, digest
`795318eaae98ee968fd9fd0a47a3f5e3a54d59548b0662f9828c9c61a710b097`.
The original deadline remains 2026-11-07T12:00:00Z and the two mathematical
truth forecasts remain 0.75/0.75. The immutable original issue body SHA256 is
`d6966a7682a0fd3f25782e75ed2003497e42e04c1bb135579859e26ff45e0b5b`.
The unique bounded probe is consumed. The retained result is ordinary later
formal work; it earns no new probe, timing or forecast credit.

## Triage

- **Proved in the delivered source:** independent endpoint choices yield
  the product of binomial coefficients, and countQ gives the rational
  triangular-product expression for every natural n. This explains why
  parity splitting applies without replacing the original placement count.
  Congruent rectangles in different positions remain distinct.
- **Proved in the delivered source:** the recurrence and the four initial
  values determine every coefficient of A*D; D's unit constant gives the full
  formal quotient. The joint assertion therefore covers the original zero
  index as well as all later indices. The Reg rejectedLaw verifies that a
  zero-family intervention fails the generating-function clause. Agreement
  with a homogeneous recurrence alone cannot identify the source count.
- **Deductive consequence, not a separate kernel theorem:** strong
  induction on n using the four initial values and the guarded recurrence
  gives uniqueness among integer sequences with those data. This explains
  the mathematical role of jOEIS/Cadot's parameters. No end-to-end theorem
  about the execution of those external programs is delivered or counted.
- **Unresolved generalization here:** replacing the folding base two by
  another integer, or replacing the grid by a higher-dimensional box, needs
  its own denominator and recurrence analysis. The independent-endpoint
  counting method suggests a route, but the present literal identities do
  not assert those generalizations.
- **Unresolved adjacent questions here:** minimal recurrence order,
  quantitative asymptotics and variants that count congruence classes rather
  than placements need separate statements and evidence. These are possible
  follow-up questions, not claims of globally open problems or new theorems.
  The inspected source bodies supply no further conditional theorem whose
  full resolution is asserted by this unit.

## ASSUMED-UNVERIFIED

MathDB content, full citation-network review, exhaustive third-party and
dominating-theorem clearance, and global novelty/priority remain unverified.
An uninspected complete prior settlement remains possible. Bounded nonhits,
Conjectural markers and failed HTTP access do not establish global openness.

Required CI and its actual DTR reading remain pending, as do the later
independent delivery review and merge. The optional full-report-only Scribe
consumer does not accept the scoped report schema; no full-library report
or altered report is supplied to satisfy it. The local source-bound audit
record, typed resolution and mathematical result imply no whole-project
green status, solved-problem KPI, strict timing credit or completed parent
goal.
