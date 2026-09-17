---
slug: oeis-a399755-pell-class-successor
bibkey: wu2026a399755
doi: null
url: https://oeis.org/A399755
triage: theorem
motivation_gids:
  - D5/S3/ArithUnits/NegativePellSquare.negative_pell_square_unit
---

# A399755: generalized Pell classes and the least square partner

## Problem

The single external named target is Chai Wah Wu's A399755 conjecture,
attributed in the entry to September 10, 2026:

> Conjecture: A399491(k) < 4*k^3+3*k if and only if k is a term of this sequence.

The A399755 name is:

> Numbers k such that the generalized Pell equation x^2-(k^2+1)*(y^2+1) = 0 has more than one fundamental solution in (x, y).

The companion A399491 name is:

> The smallest integer m > n such that (n^2+1)*(m^2+1) is a perfect square.

For every natural k, define D = Discriminant(k) = (k : Int)^2 + 1.
All generalized Pell coordinates and all unit coordinates below are integers.
The exact definitions and sole target are:

```text
Discriminant(k : Nat) : Int = (k : Int)^2 + 1
Sol(k : Nat, x y : Int) := x^2 - Discriminant(k)*y^2 = Discriminant(k)
SameClass(k : Nat, x y r s : Int) :=
  exists u v : Int,
    u^2 - Discriminant(k)*v^2 = 1 AND
    x = r*u + Discriminant(k)*s*v AND y = r*v + s*u
MultipleClasses(k : Nat) :=
  exists x y r s : Int,
    Sol(k,x,y) AND Sol(k,r,s) AND NOT SameClass(k,x,y,r,s)
NextSquarePartner(k m : Nat) :=
  k < m AND IsSquare((k^2+1)*(m^2+1)) AND
  forall n : Nat,
    k < n -> IsSquare((k^2+1)*(n^2+1)) -> m <= n
result : forall k : Nat, 0 < k ->
  exists m : Nat, NextSquarePartner(k,m) AND
    (m < 4*k^3+3*k IFF MultipleClasses(k))
```

IsSquare here is the predicate on natural numbers. The existential result
includes totality and the full minimum property, not only a bound on an
assumed partner. Membership refers to k itself, not to the kth value listed
in A399755. The source convention selects one fundamental representative
per generalized solution class; it is distinct from the unique fundamental
positive solution of the norm-one equation.

SameClass is Robertson's integral norm-one relation, including the unit -1
and hence simultaneous negation of both coordinates. It does not impose
positive coordinates, primitivity, or squarefree D, and it does not use
fractional units of a maximal order. Any representative-based formulation
must be proved equivalent to this predicate on arbitrary integral pairs.

## Motivation

The frozen motivation declaration
`D5/S3/ArithUnits/NegativePellSquare.negative_pell_square_unit` relates a
restricted negative-Pell family to explicit norm-one units. Its parameter
is 6*j and its conclusion is a norm and coordinate identity. It supplies
context for unit multiplication; it is not the all-k class or least-partner
statement, and no proof dependency on it is asserted.

The present question links the order of square partners to the number of
generalized Pell classes. The proposed address is
`D5/S3/ArithUnits/PellClassSuccessor`, with generality I. Only the five
necessary source definitions and one public result are in scope.

## Gap

The saved A399755 entry labels the strict equivalence a conjecture. A399491
also states the one-class implication for equality at the cubic bound and
labels its converse a conjecture. Those comments are source assertions,
not proved premises of the target.

The bounded literature and identifier searches recorded in issue #8016
found no exact resolution in the inspected scopes. They do not establish
exhaustive semantic absence or global priority. The inspected Mathlib
interfaces for Pell.Solution1 and IsFundamental concern norm-one solutions;
they do not by themselves supply completeness and ordering for arbitrary
norm-D classes. Robertson states relevant class and interval facts but
explicitly supplies no proofs in the article and refers to other books.

## Route

The proof uses elementary integer algebra and descent. Write
A=2*k^2+1 and B=4*k^3+3*k.

1. The endpoint B is a square partner, with square root D*(4*k^2+1).
   The natural-number least-witness principle then supplies m and its
   entire universal minimum condition.
2. MultipleClasses(k) is equivalent to the existence of an integral
   norm-D solution whose x-coordinate is not divisible by D. The base
   solution is (D,k). Two solutions with D dividing their x-coordinates
   are connected by explicitly constructed integral norm-one units.
   Conversely, every solution in the base class has D dividing x.
3. The inverse unit map sends (x,y) to
   (A*x-2*k*D*y, A*y-2*k*x). It preserves the norm and nondivisibility.
   For nonnegative coordinates with y>k, the absolute value of its new
   y-coordinate is strictly smaller. Minimizing that absolute value
   therefore gives a nondivisible solution with 0<=y<=k and k<x<D.
4. Applying the forward unit map to this reduced solution gives a square
   partner t with k<t<B. Conversely, an intermediate partner maps under
   the inverse unit to a norm-D solution with absolute y-coordinate <k.
   A norm-D solution with D dividing x must have absolute y-coordinate
   at least k, so this intermediate partner forces another class.
5. The complete minimum property transfers the intermediate-partner
   equivalence to the same least m in result.

All auxiliary facts are local to the single result. The proof uses no
previously frozen D5 declaration, no fundamental-unit minimality theorem,
and no classical interval completeness theorem. The five public
source definitions retain arbitrary integral coordinates and the exact
natural-number square and minimum predicates.

## Falsifier

A positive k with multiple classes but no square partner strictly between
k and 4*k^3+3*k would refute the equivalence. A positive k with such an
intermediate partner but only one class would refute the reverse direction.
Failure of least-partner existence for a positive k would refute the total
statement.

A prior exact published resolution, incompatible class semantics, or a
dedicated active owner invalidates the candidate's selection basis. A
finite prefix, a positive-only pair model, or fractional-coordinate units
cannot replace the target.

## Evidence

The preregistration is
https://github.com/the-omega-institute/trureturing/issues/8016,
created 2026-09-15 at 04:29:56 UTC before the new proof, as recorded by the
GitHub issue. It fixes the quoted source and the exact target above.

The full saved A399755 source is revision 12, timestamp
2026-09-14T23:49:50-04:00, retrieved with HTTP 200 at
2026-09-15T04:02:11.774431Z. Its JSON SHA-256 is
`19d73093da6a2e330eb00325720de647203d56f26ec039678dd82a01d72e3488`.
The full saved A399491 source is revision 25, timestamp
2026-09-12T06:07:18-04:00; its JSON SHA-256 is
`84ad2705b0e5283ccdd2ecadfbeabcba5f089081fc0cccf95ad82dad8172050f`.
The companion's immutable official mirror is
https://github.com/oeis/oeisdata/blob/ba8580c292f2c51dd0dc3ae2f3ba052c7f17c7d3/seq/A399/A399491.seq.
The earlier mirror returned 404 for the newly added A399755, so its fixed
source is the authoritative live snapshot just identified.

Class semantics are documented in
`D5/L/robertson2004generalizedpell`, especially pages 12-14. The pinned
SymPy 1.14.0 diop_DN docstring is a semantic reference for one tuple per
class, not trusted execution or a substitute for class completeness.
Source programs, listed terms, and examples have no proof weight here.

Issue #8016 records zero exact identifier matches in the checked D5,
Blueprint, Problems, Library, registry, and pinned Mathlib source, and zero
results for the specified all-state owner queries, with
`incomplete_results=false`. The broader Pell query returned 27 records;
#7895 concerned a distinct fixed-golden Pell budget target. Public indexed
Lean-code queries for the two IDs and generalized Pell returned zero.
These are the preregistered readings, not a fresh search of later live state.

## Triage

`theorem`: a first-tier external named conjecture under CLAUDE.md
section 3.6. The admission basis is `open-problem-resolution`, tied to
issue #8016 and exactly one public result. The five necessary source
definitions have no proof-shape classification; result has
`proof_shape: content`, from its integral class criterion and unbounded
integer descent. `escape_witness: none`: the selected admission basis
is the preregistered named problem, not a newly claimed escape obligation.
Every declaration has `computational_content.kind: none`; the result is
unbounded symbolic mathematics. There are no extra public helper theorems.

`dominating_theorem_search: not-found-in-searched-scope` uses the bounded
scopes in Evidence. No prior exact resolution was found in those scopes;
this is not an exhaustive absence claim. The source definitions and full
quantified conclusion correspond to the Lean declarations at
`D5/S3/ArithUnits/PellClassSuccessor`. Triage identifies the question class;
the Scribe claim records its proved resolution after canonical freezing.

## ASSUMED-UNVERIFIED

The source snapshots and Robertson pages establish attribution and class
terminology. Robertson states classical interval facts without proofs;
those facts are not premises of the Lean derivation. The source program
and its finite output are also not mathematical premises.

The bounded search in #8016 inspected related OEIS entries and bibliography
titles but not the referenced books or linked papers. Accessible Brave
queries found no relevant resolution and also missed the fresh source;
later Brave formula/author queries, Google, DuckDuckGo, and arXiv scopes
were blocked by challenges or rate limits. The direct Robertson host failed
DNS resolution; the cited Wayback copy supplied the article. Later live
changes, inaccessible sources, and results under different terminology
remain outside that evidence. No exhaustive absence or global priority is
asserted.
