---
slug: oeis-a381737-hermite-tie-recurrence
bibkey: sheppard2025a381737
doi: null
url: https://oeis.org/A381737/internal?rev=28
triage: theorem
motivation_gids:
  - D5/S3/Analytic/Polynomial/HermiteTieRecurrence.result
---

# The complete A381737 Conjecture 2 recurrence

## Problem

OEIS A381737 revision 28, by Mike Sheppard (2025), names the sequence:

> Orders k of Hermite polynomials whose maximal coefficient in absolute value appears twice.

Its Formula field states:

> Conjecture 2: a(n) = a(n-1) + 2*a(n-2) - 2*a(n-3) - a(n-4) + a(n-5).

The offset is 1,1. Let $H_k$ be the physicists Hermite polynomial represented
by `HermiteSignedMode.physicistsHermite` over the rationals. For every
natural order $k$ and exponent $j$, put

$$
M(k,j)\iff j\le k\ \land\ \forall i\le k,\quad
|[x^i]H_k|\le |[x^j]H_k|.
$$

Let $S$ consist of exactly the natural orders $k$ for which there are
natural exponents $u<v$ such that, for every natural $j$, $M(k,j)$ holds
if and only if $j=u$ or $j=v$. Thus exactly two distinct exponents attain
the absolute maximum of the entire row $0,\ldots,k$, including parity-zero
coefficients.

The complete assertion is that there exists $g:\mathbb Z\to\mathbb N$
satisfying all of the following:

- For every integer $n\ge1$, $g(n)>0$.
- For all integers $1\le n<m$, $g(n)<g(m)$.
- For every natural order $k$, including zero, $k\in S$ if and only if
  there is exactly one integer $n\ge1$ with $k=g(n)$.
- For every integer $n\ge6$,

$$
(g(n):\mathbb Z)=(g(n-1):\mathbb Z)+2(g(n-2):\mathbb Z)
-2(g(n-3):\mathbb Z)-(g(n-4):\mathbb Z)+(g(n-5):\mathbb Z).
$$

Every sequence value is cast separately to the integers before subtraction.
The positive-index restriction of $g$ is the actual increasing exhaustive
one-based enumeration of $S$. Its values at nonpositive indices impose no
restriction on this event. There is no finite cutoff, eventual qualification,
selected subfamily, signed maximum, probabilists normalization or
recurrence-defined replacement sequence.

## Motivation

The whole external Conjecture 2 event is preregistered at
https://github.com/the-omega-institute/trureturing/issues/25941#issuecomment-6593756660.
Its execution-clock reference is
https://github.com/the-omega-institute/trureturing/issues/25941#issuecomment-6594367458.
The original forecasts and clock remain those immutable source records.
The stronger frozen Conjecture 1 enumeration supplies the actual sequence;
its separate dossier is `oeis-a381737-hermite-absolute-ties`.

## Gap

A recurrence of an arbitrary sequence would not identify the source event.
The needed bridge retains every qualifying polynomial order, positive
index, and unique membership correspondence while transferring the frozen
natural-indexed integer formula to a natural-valued enumeration indexed by
positive integers. Finite source programs do not prove this universal event.

## Route

`HermiteAbsoluteTieOrders.result` supplies positivity, strict increase and
exhaustive unique positive indexing for the original predicate, with

$$
b(m)=2m(m+2)+(m+1)(-1)^{m+1}.
$$

For positive integer $n$, use $g(n)=\operatorname{toNat}(b(n.\operatorname{toNat}))$.
Positivity makes the integer cast of this natural value equal to $b$.
Positive natural and positive integer indices correspond exactly, preserving
strict increase and unique exhaustion. At $t=n-5$, the existing quadratic
and alternating linear formula satisfies the displayed recurrence by power
expansion and polynomial normalization. The retained private
`formula_recurrence` helper is used by the public `result` on that live path.
No new classification of Hermite coefficient ties is required.

## Falsifier

The complete event would fail if no total increasing exhaustive positive-index
enumeration with unique indexing existed, or if its actual values violated
the displayed recurrence at some integer $n\ge6$. A discrepancy must concern
this actual enumeration of the full original coefficient rows. A prefix,
other normalization or proxy sequence cannot decide the event.

## Evidence

`D5/S3/Analytic/Polynomial/HermiteTieRecurrence.result` proves the entire
`claim`. The owning Scribe attaches a typed `OpenProblemResolutionClaim`
of kind `Proved` to this dossier. The canonical delivery has no corresponding
theory atom and uses `deposit-uncovered` for this GID.

The public `result` and its consumed private `formula_recurrence` helper
are both `proof_shape: bind-only`; `escape_witness: none`.
The admission basis is `open-problem-resolution`, with the external source
and preregistration above. The claim definition states the exact source
event. All declarations have `utility: none`: this is an unbounded mathematical
consequence, with no bounded enumeration, checker, numerical-premise reduction
or certified finite-instance delivery. The stronger frozen C1 supplier is
attributed; this resolution grants no automatic independent new-result or
KPI credit.

The author Reg mirror is
`Reg/D5/S3/Analytic/Polynomial/HermiteTieRecurrence.lean`.
Its source-family proofs compile, but the audit is `declared_unresolved`,
certificate null, diagnostic `IE-C050 ClosedTruthReadout`, reason
`unclassified_form`, rule `source.observation_data`.
The missing accepted source-observation reconstruction/binding certificate
is disclosed under the CLAUDE 3.9 linked-issue exception:
https://github.com/the-omega-institute/trureturing/issues/25957.
This is an unfinished audit, not `declared_validated`.

## Triage

The source classification is `theorem`. The resolution covers the complete
Conjecture 2 actual-enumeration recurrence. C1's separate dossier and
mathematical supplier retain their original scope. Conjecture 3 remains
outside this resolution.

### What the settlement shows

Proved by `D5/S3/Analytic/Polynomial/HermiteTieRecurrence.result`: the stronger
C1 closed formula already forces C2 for the complete actual enumeration,
with no additional assumptions or finite index bound. Positivity permits
exact integer/natural transport; the quadratic and alternating linear
parts provide the recurrence mechanism. The proof settles this neighboring
question of C1 without another coefficient classification. It neither
changes C1's statement nor settles Conjecture 3. No additional general
recurrence theorem or new mathematical endpoint is claimed.

## ASSUMED-UNVERIFIED

The mapping from the source name, offset and conjecture to the explicit
quantified event is a source-to-formal correspondence; Lean verifies the
formal event, not OEIS prose. The checked repository, pinned Mathlib,
selected Lean-ecosystem and source searches identified no prior whole named
C2 settlement in their inspected scopes. These are bounded literature and
reuse checks, not worldwide openness, originality or priority certification.
Rooney's full text, the unidentified Dudeja-Hsu citation and broad citation
tails remain uninspected. Source programs and finite agreement supply no
universal proof. The unfinished Reg binding audit and the existing raw/scoped
reader boundaries recorded in issues #15595 and #24733 remain disclosed;
selected build success does not clear those boundaries or certify all CI.
