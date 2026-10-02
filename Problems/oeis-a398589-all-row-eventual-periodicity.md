---
slug: oeis-a398589-all-row-eventual-periodicity
bibkey: weinstein2026a398589
doi: null
url: https://oeis.org/A398589
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/OeisA398589EventualPeriodicity
---

# Eventual periodicity of every A398589 row

## Problem

> Conjecture: All of the rows in this sequence are eventually periodic.

For every k in Nat, let a_k(0)=k. At time t>0 choose the least natural x>=k
such that every prior occurrence a_k(s)=x, s<t, satisfies s+x<t. The original
claim is that for every k there exist N in Nat and p>0 such that
for every t>=N, a_k(t+p)=a_k(t). The row is its infinite continuation;
OEIS display truncation is not a premise.

## Motivation

This is a tier-one external named conjecture, preregistered in
[issue #11736](https://github.com/the-omega-institute/trureturing/issues/11736)
before the mathematical probe. The Library note quotes the definition and
targeted conjecture and gives the index correspondence. The other source
conjecture, asserting a nonempty preperiod for every k>2, is excluded.

## Gap

The inspected OEIS entry reports verification through k=100. The SeqFans
thread withdraws an upper-density argument. The bounded prior-work check
also covers packing-coloring and scheduling literature, private-inclusive
repository declarations, pinned Mathlib and bounded GitHub Lean queries.
No exact all-k result was found in that scope. Existence of a coloring does
not imply this fixed greedy trajectory; maximum-gap scheduling is a
different constraint. Unindexed resolutions remain unverified.

## Route

The recursion is total because among k,...,k+t one label is absent from the
t earlier positions. For k>0, its minimum label k occurs exactly at
multiples of P=k+1. Put B=k(k+2)=kP+k. If every label in [k,B] is blocked at
time t, choose one exclusion witness for each label. They all lie in
W={s<t : t<=s+B}, which has at most B positions. The witnesses for labels
strictly above k number B-k. The k+1 clock occurrences (floor(t/P)-j)P,
0<=j<=k, also lie in W. Their row values distinguish them from all the
higher-label witnesses, yielding B+1 distinct positions and a contradiction.
Thus every actual row value is at most B, without an inductive bound premise.

The exact finite state at time t is the B-symbol window a_k(t+i), i<B,
with each value in Fin(B+1). A candidate x in [k,B] is legal at t+B exactly
when every matching position i satisfies i+x<B. Occurrences before t are
irrelevant because x<=B. The total transition shifts and appends the least
eligible label. The bound and legality show that the fallback is never used
on the actual orbit. Its initial state is the actual prefix at zero,
independent of periodicity. Induction verifies transition equality, and
the head projection recovers a_k(t).

The proof directly applies the frozen
`finite_input_generator_eventually_periodic` with C=U=Unit to this actual
finite-window orbit. Generic finite-state periodicity is reused. The k=0
branch is constant zero, with N=0 and p=1.

## Falsifier

Refuting the original law would require some k for which every N and every
positive p have a t>=N with a_k(t+p)!=a_k(t). A finite prefix mismatch can
refute a proposed period, but cannot establish this universal refutation.
An occurrence that invalidates the clock, shared-window packing, or exact
transition correspondence would refute the corresponding proof obligation.

## Evidence

The sole public result in
`D5/S3/Combinatorics/OeisA398589EventualPeriodicity.lean` is
`eventual_periodicity`, with the complete original domain and no additional
premise. The necessary model definitions are `legal`, `rowStep` and `row`.
All recurrence facts, the clock, the uniform bound and the actual-orbit
bridge are local proof steps. Scoped D5 and Reg compilation succeeds; the
result and registration use only propext, Classical.choice and Quot.sound.

The Reg law retains the complete forall-k eventual-periodicity statement.
Its rejected family b_k(t)=t violates that full law: at t=N any positive
period would force N+p=N. Its observational-dependence witness uses the
actual k=1 row at times zero and one; legality rules out equal observations.
The registration proves the exact bridge, variation, sensitivity and
actual observational dependence. The scoped inspector verifies source-equivalence
with the original full statement and accepts the declared registration. The
residual is literal open.

## Triage

`theorem`, resolving the original eventual-periodicity conjecture.
`proof_shape: content`; `admission_basis: open-problem-resolution`.
The clock, augmented shared-window counting and exact actual-orbit bridge
are live content. The generic finite-state supplier is an existing frozen
dependency, with statement identity
sha256:abc6046c79b8a7bca6c9361945c46abc65f5dd80eef867403a7840b9e246d8ce.
This is an unbounded symbolic proof, not bounded enumeration, a checker,
a numerical reduction or a certified finite instance; utility is none.

The minimum-clock/shared-window mechanism is proved within the original
result. Its extension to arbitrary one-symbol histories with the same clock
is a mathematical route beyond the stated result, not a delivered theorem.
The source's nonempty-preperiod conjecture remains open. A stronger bound
4k+1 and minimal period or preperiod formulas are not proved. No identified
source-dependent theorem is invalidated or separately resolved by this
result.

## ASSUMED-UNVERIFIED

The literature check is limited to the sources and searches above. No
priority or first-proof claim is made. The displayed OEIS truncation is
connected to the infinite row by the stated source indexing and rule;
it is not an independent formal theorem about the OEIS database.
