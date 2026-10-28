---
slug: rather-2026-book-domination-root-conjecture
bibkey: rather2026bookroots
doi: null
url: https://arxiv.org/abs/2604.08998v2
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/Graph/Domination/RatherBookRootRefutation.result
---

# Rather's book domination-root Conjecture 5.4

## Problem

Bilal Ahmad Rather, arXiv:2604.08998v1, *Root geometry of domination
polynomials for friendship and book graphs*, and v2, *On roots of domination
polynomials for friendship and book graphs*, Section 5, printed page 12,
Conjecture 5.4:

> The numerical data suggest the following sharper parity-dependent statement.
> (i) If n is even, then D(B_n,x) has exactly four real roots counting multiplicity:
> 0 with multiplicity 2, one simple root in (-infinity,-2), and one simple root in (-1/2,0).
> (ii) If n is odd, then D(B_n,x) has exactly four real roots counting multiplicity:
> 0 with multiplicity 2 and two simple roots in (-1/2,0).

Section 2, printed page 3, defines the domain and graph:

> For n >= 1, the book graph B_n is formed by identifying a common edge in n copies of C_4, see Figure 1(b).

The source uses finite simple undirected graphs and ordinary domination:
$S$ dominates $G$ when every vertex is in $S$ or has a neighbor in $S$,
equivalently $N[S]=V(G)$. Its polynomial counts each dominating subset once:

$$D(G,X)=\sum_{S\text{ dominates }G}X^{|S|}.$$

The complete closed claim quantifies over every natural $n\geq1$. For even
$n$ there are distinct nonzero $a,b\in\mathbb R$ with $a<-2$ and
$-1/2<b<0$; for odd $n$ there are distinct nonzero $a,b\in(-1/2,0)$.
In each branch, $0,a,b$ are actual roots, their exact multiplicities are
$2,1,1$, and for every real $r$,

$$D(B_n,r)=0\quad\Longleftrightarrow\quad r=0\ \lor\ r=a\ \lor\ r=b.$$

The delivered conclusion is the literal negation of this entire universal
claim. It retains both parity branches and all intervals, multiplicities
and exhaustiveness conditions. The legal odd value $n=1$ is the witness;
restricting the source to $n\geq2$ gives a different, unsettled assertion.
Proposition 5.3 has a local $n\geq2$ hypothesis, which is not a hypothesis
of Conjecture 5.4. Printed page 11 explicitly identifies $B_1=C_4$.

### Statement correspondence

| Source object or clause | Lean counterpart |
| --- | --- |
| Every shared-edge book $B_n$, $n\geq1$ | `claim` quantifies `n : Nat` with `1 <= n`; `bookGraph n` has vertices `Fin (2*n+2)`. |
| One shared edge and otherwise disjoint pages | Vertices 0,1 are shared; page `i : Fin n` is `0--1--(2*i.val+2)--(2*i.val+3)--0`; `pageForward` and its reverse give exactly adjacency. |
| Ordinary dominating subsets | Existing `DominatingSetAverage.domSets` and `mem_domSets`, using existing `SimpleGraph.IsDominating`. |
| Count each subset by cardinality | `dominationPolynomial` sums `Polynomial.X ^ S.card` over those actual subsets, with real coefficients. |
| Even and odd intervals | Both implications in `claim`, including the real endpoint `-(1/2 : Real)`. |
| Exact multiplicities and no further real root | `FourRealRoots`, including nonzero/distinct roots, `Polynomial.IsRoot`, `Polynomial.rootMultiplicity` values 2,1,1 and the universal root iff. |
| Negation of the whole statement | Closed `claim : Prop`; `result : Not claim`. |

## Motivation

The conjecture concerns finite real-root configurations on the Euclidean
real line. Its literal domain includes a graph whose polynomial has only
zero as a real root, so checking the boundary distinguishes the original
statement from a proposed amendment. The frozen ordinary-domination owner
supplies the invariant; no certified or independent-domination replacement
is used.

## Gap

The full literal target, source boundaries, model and count are preregistered
in [#23025](https://github.com/the-omega-institute/trureturing/issues/23025).
The inspected arXiv v1/v2 texts contain the same complete Conjecture 5.4.
The bounded primary-source screen did not identify an equivalent settlement;
its unread full-text gaps remain explicit below. This is not a claim of
worldwide priority or exhaustive ownership.

## Route

`D5/S3/Combinatorics/Graph/Domination/RatherBookRootRefutation.result`
is the sole authored public theorem. Its admission basis is
`open-problem-resolution` under the preregistered external target #23025.
Its proof shape is honestly `bind-only`, with no escape witness claimed.
The seven other authored public declarations are necessary model definitions
and the two explicit decision instances. Three private helpers are consumed:
`book_one_eq_cycle` and `cycle_domSets` feed `book_one_polynomial`, which
feeds `result`. Generated proof companions are not authored conclusions.

The graph equality is with the actual `SimpleGraph.cycleGraph 4`. The
finite subset enumeration uses the existing `mem_domSets` owner. Six pairs,
four triples and the full set give

$$D(B_1,X)=6X^2+4X^3+X^4=X^2((X+2)^2+2).$$

For every nonzero real $a$, both $a^2$ and $(a+2)^2+2$ are positive.
Applying the odd clause at $n=1$ would supply a nonzero root $a$,
contradicting this positive evaluation. No formula for arbitrary books is
assumed as an axiom or substituted for the graph/count bridge.

## Falsifier

A mismatch in the indexed shared-edge construction, replacement of ordinary
domination, omission of a source condition, or an additional global
$n\geq2$ hypothesis in the targeted arXiv versions would invalidate the
source correspondence. The actual $C_4$ subset list and positive cofactor
rule out the proposed odd roots at the legal value $n=1$. A correction or
journal statement with a different domain requires its own target and does
not change the literal arXiv conclusion.

## Evidence

The canonical formal result is
`D5.S3.Combinatorics.Graph.Domination.RatherBookRootRefutation.result`,
whose type is literally `Not claim`, with the closed definition
`claim : Prop`. Its axiom closure is contained in
`{Classical.choice, Quot.sound, propext}`. The eight authored public
entries have complete Blueprint mirrors. A single `OpenProblemResolutionClaim`
of kind `Refuted` binds this dossier to the frozen result. The designated
refutation result is exempt from the four-slot theorem audit; no Reg
wrapper or companion theorem is asserted.

The graph equality, eleven-subset enumeration and polynomial identity are
kernel-checked consumed private helpers in the same module. The positive
cofactor contradiction occurs in `result` itself. These are formal proofs,
not imported numerical experiments or an arbitrary-polynomial surrogate.

## Triage

### What the settlement shows

- **Proved**, `D5/S3/Combinatorics/Graph/Domination/RatherBookRootRefutation.result`:
  the original complete arXiv v1/v2 all-$n\geq1$ Conjecture 5.4 is false.
  The defect is precisely its legal $n=1$ odd instance.
- **Proved on the consumed helper path** of that GID: `bookGraph 1` is
  the actual four-cycle; the dominating subsets are its six pairs, four
  triples and full vertex set; their sum is $6X^2+4X^3+X^4$. The finite
  normalization does not provide a new general root-classification theorem.
- **Proved inside `result`**, the same GID: evaluation away from zero is
  $a^2((a+2)^2+2)>0$. Thus the nonzero root demanded by the odd clause
  cannot exist. No separate public theorem for a stronger classification
  or exact zero multiplicity is introduced.
- **Open here**: the amended assertion for $n\geq2$, its sharp interval
  bounds and any complete finite-order root classification beyond this
  boundary contradiction. The proof does not decide these questions.
- **Unaffected by this refutation**: the source's other proved results,
  including its stated book-polynomial formula and Proposition 5.3.
  A result using the original conjecture as a premise cannot acquire that
  premise from this settlement; no other source theorem is thereby refuted.

The established ordinary book formula already appears in arXiv:1401.2092,
Theorem 8, and arXiv:1501.05856, Theorem 5; the latter's Theorem 10 concerns
a root-limit set. The familiar $C_4$ count and positive quadratic are prior
ingredients. The retained contribution is the source-qualified negation of
the named full claim, not novelty for those ingredients. The relevant
Jahari--Alikhani 2018 paper treats other graph constructions, and certified
domination uses a different invariant.

## ASSUMED-UNVERIFIED

The author bibliography lists the paper as Filomat (2026), to appear, and
the arXiv record states acceptance. The actual journal text, corrections and
independently revised author manuscript remain unread. There is no journal
agreement, correction-absence or author-intent claim.

Alikhani's six-page 2013 article, DOI `10.1016/j.endm.2013.07.062`, remains
unread. The located arXiv:1210.3144v1 document is a one-page abstract and
the institutional IPM record links an empty TeX file; neither closes the
full-text gap. The inspected primary sources support only a bounded
literature conclusion, not global novelty, absence or exclusive ownership.

Two optional prior exact-search helper controls (`cycle_domSets` and
`book_one_polynomial`) timed out at 100000 heartbeats; search completeness
remains ASSUMED-UNVERIFIED. Their actual kernel-checked implementations
and existing owner applications are retained. No broader ecosystem search
completeness, $n\geq2$ settlement or required-CI success follows.
