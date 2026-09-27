---
slug: oeis-a398542-fixed-bottom-polynomial
bibkey: norton2026a398542
doi: null
url: https://oeis.org/A398542
triage: theorem
motivation_gids:
  - D5/S1/Words/Patterns/DerangementRatioNonconvergence.Contains
---

# A398542 fixed-bottom polynomial conjecture

## Problem

Charles Cornell Norton, OEIS A398542, August 1, 2026; revision 18,
August 30, 2026, 18:45:04, exact selected %F:

> Conjecture: for every m >= 1 and every b in S(m), d(b,k) = p(k)*binomial(2*k,k) + q(k)*4^k for polynomials p and q depending on b, with deg p <= m-1 and deg q <= m-2. Verified for m <= 6 and k <= 12.

S(m)=Av_m(132). For every m>=1 and b in S(m), choose p_b,q_b in Q[X]
independently of k such that the displayed identity holds for every k>=0.
The degree bounds are m-1 and m-2 for m>=2, with q_b=0 when m=1.
Here d(b,k) counts actual permutations of 1,...,m+k avoiding 1324 whose
lower-value subsequence is exactly b and whose standardized upper-value
subsequence avoids 213. The value cut is fixed, the empty upper cell is
allowed, and d(b,0)=1. Rational coefficients are an explicit sufficient
choice beyond the source's unspecified coefficient field.

## Motivation

The preregistration https://github.com/the-omega-institute/trureturing/issues/9332
contains the exact source and full ordinary proof. The frozen generic
`Contains` definition supplies classical pattern containment by increasing
position embeddings and exact relative value order. The target is the whole
fixed-bottom assertion, not a bounded fit or a recursively defined count.

## Gap

The source's checked range m<=6, k<=12 does not imply its unbounded
conjecture. Aggregate domino enumeration does not determine every fixed
bottom. The missing uniform connection is an actual minimum-split
equivalence followed by a guarded inverse-power bound for all intervals.
The new Library note records the bounded prior-source comparison. No exact
settlement was found in those inspected bodies; worldwide priority is not
claimed.

## Route

Insert upper permutations into weakly increasing gaps of the same complete
bottom b. Mixed 1324 occurrences are exactly interleaved lower and upper
ascents, giving the strict deadline cutoff. Split at the upper minimum,
with the forced value shifts and either child allowed to be empty. Take
cardinalities of the actual equivalence to obtain the interval convolution.
In Q[[X]], separate singleton Catalan states and prove
F(l,h)=T A(T), deg A<=2(h-l)-2, only for l<h<=m and h<dead(l), where
T=(1-2XC)^(-1). Extract odd/even powers through the pinned binomial and
Pochhammer identities to obtain the rational polynomials and degree bounds.

## Falsifier

Removing the guard is invalid: for b=(1,2), dead(1)=2 and
F(1,2)=C^2=4/(1+s)^2, where s=1-2XC. This interval fails h<dead(l);
the full state F(0,2)=(1+s)/(2s^2) is guarded. Removing the strict cutoff
counts six rather than five objects for this bottom, interval [1,2], and
upper size two. These are method falsifiers, not counterexamples to the
source conjecture. Replacing actual cardinality or allowing p,q to depend
on k would fail the stated target.

## Evidence

`A398542FixedBottom.Actual` defines the literal permutation subtype and
`actualEquiv` proves its configuration equivalence.
`A398542MinimumRecurrence.actual_cardinal_recurrence` supplies the actual
minimum split, zero coefficient and full-interval equality.
`A398542Polynomial.actual_series` and `guarded_polynomial` connect that
cardinality to the formal series argument. `A398542Polynomial.result`
states the complete all-m, all-b, all-k conclusion with rational
polynomials, both bounds and explicit m=1 zero condition. Its
Nat.centralBinom is Nat.choose (2*k) k. Admission and resolution state
are supplied by the canonical report, Freeze and typed Scribe claim,
not by a handwritten status in this dossier.

## Triage

`theorem`: first-tier recent fixed-bottom conjecture, allocated on the
strength of the complete ordinary proof in #9332. The historical
tier-3/note-only record in `Library/Words/oeis2026triage0911.md` remains
unchanged. This allocation does not reclassify unrestricted 1324
enumeration. Neither A398446 nor the full L-gridding generating function
is settled by this statement; supporting formalizations are not additional
resolved problems.

## ASSUMED-UNVERIFIED

Worldwide priority and the absence of a proof outside the inspected
literature are unverified. The bounded source audit is attributed in
`norton2026a398542`; this delivery directly rechecked OEIS revision 18.
Source fidelity is a semantic review obligation beyond kernel type
checking. Correctness of the separate official program, the optional
tree representation, unrestricted enumeration, publication, required CI,
merge and the caller's completion audit are separate from this theorem.
