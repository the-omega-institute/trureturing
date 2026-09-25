---
slug: sun-lowercase-turan-conjecture-52
bibkey: sun2026generalizations
doi: 10.48550/arXiv.2608.13192
url: https://arxiv.org/html/2608.13192v1
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/LucasCompanion.lucasV
---

# Sun Conjecture 5.2: both lowercase strict Turan clauses

## Problem

Sun, arXiv:2608.13192v1, Conjecture 5.2 asks for both assertions, for
every integer `n >= 1`:

$$
g_n(x)^2>g_{n-1}(x)g_{n+1}(x)\quad\text{for every real }x\leq-1,
$$

and

$$
v_n(x)^2>v_{n+1}(x)v_{n-1}(x)\quad\text{for every real }x\leq-1/8.
$$

The source's literal initial values and multiplied quadratic/cubic
recurrences are reproduced in `Library/Recurrence/sun2026generalizations.md`.
Both endpoints are included. A proof of only one clause, a finite-index
check, or a non-strict statement does not settle this source question.

## Motivation

The frozen `LucasCompanion.lucasV` is an existing repository example of
defining a sequence by a recurrence-related algebraic construction. It
does not imply either Sun inequality. The new source target tests an
all-index strict determinant property for two different literal
three-term recurrences over negative real half-lines.

## Gap

Krasikov's Theorem 8 supplies a weighted non-strict inequality only on
the right tail. The `g` endpoint is degenerate for the local quadratic,
and the `v` clause needs a positive radical normalization and a local
interval reaching the exact `1/8` boundary. The uppercase `G,V` results
of Mao--Xiao and the p-adic Li--Sun result do not resolve these clauses.
The cited Abreu--Bustoz and Bustoz--Ismail bodies were unread in the
bounded source assessment, so no claim about their exact reach is made.

## Route

`Sequences.g` and `Sequences.v` define the two source sequences.
`StrictlyIncreasingTail.weighted_turan_nonneg_of_strict_mono` proves
the reusable strictly-increasing-coefficient tail. `GEndpoint` gives
all-index endpoint strictness by factorial scaling and parity;
`GStrict.g_strict_turan` combines it with local quadratic positivity
and the tail for every `x<=-1`. `VTail.v_tail_strict` establishes radical
coefficient growth, positive scaling, recurrence uniqueness, and strict
tail transport. `VStrict.v_strict_turan` uses
`4m^3-(m-1/8)^2(4m+1)=(12m-1)/64>0` to show its local interval
reaches the closed `1/8` boundary, then joins it to the tail. In the
formal result the order of the two real neighbor factors is reversed
from the source's `v` display by commutativity.

## Falsifier

Any positive index and real `x` in either stated closed domain with a
nonpositive corresponding determinant would refute that clause. A
failure of positive radical normalization or of the local/tail covering
would invalidate this proof route without itself refuting the source
conjecture. The theorem's unbounded quantifiers rule out finite search
as a substitute.

## Evidence

The primary versioned HTML was checked for both definitions and both
Conjecture 5.2 clauses. All six Lean owners have completed joint first
Freeze, with twelve canonical accepted/state artifacts. The scoped Lean
build exited zero over 3011 jobs, and the symbolic consumer checked the
source recurrences, generic strict statements, endpoints, and standard-three
axiom closure. Source and companion reviews approved the six-owner result.
The prebinding candidate `20a91df388d604fffb8c4436538f94995154283e`
passed required CI run `36160400233` with all six checks successful.

The `GStrict` Describe source attaches one typed `Proved` claim for this slug,
with frozen members `D5/S1/Recurrence/Sun/GStrict.g_strict_turan` and
`D5/S1/Recurrence/Sun/VStrict.v_strict_turan`. The GStrict member is the
host; the VStrict member is an additional `DeclarationHandle`. The five
theorem selectors without committed projection fixtures use disclosed,
authored `Formula` statements in their companions. The named-set binding
passed local canonical `make emit` and Scribe projection, Describe, and
Markdown checks against the refreshed Lean report. The emitted GStrict
page has two v1 member markers under the one claim. Prebinding CI does
not certify this later binding change.

## Triage

`theorem`; first-tier external two-clause named conjecture. Issue 9833
was filed after the ordinary probes and grants no retrospective
`open-problem-resolution` bind-only exception. Against original joint
baseline `15664c84561c0ea57b6ca22cf328802a5ba5f897`, the three
literal definitions and all five public theorems are assessed together.
Each theorem has live content and `admission_basis: escape-witness`;
the two final clauses are separate public results, bound to one problem
credit without a conjunction wrapper or duplicate claim. No proof-shape
or completion claim is inferred from this problem file itself.

## ASSUMED-UNVERIFIED

The bounded prior-art search did not find a later exact proof through
25 September 2026; worldwide absence and priority are unverified.
The source mathematical result and repository delivery completion are
different questions. Final candidate CI, ordinary merge to dev, main
synchronization, and a separate completion audit remain to be checked by
the delivery owner.
