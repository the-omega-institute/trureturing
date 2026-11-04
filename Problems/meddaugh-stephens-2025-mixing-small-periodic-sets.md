---
slug: meddaugh-stephens-2025-mixing-small-periodic-sets
bibkey: meddaugh2025neighborhoodshadowing
doi: null
url: https://arxiv.org/abs/2509.04312v1
triage: theorem
motivation_gids:
  - D5/S1/Dynamics/Shadowing/ProgressionExample.quadratic_progression_example
---

# Weak mixing and neighborhood shadowing without small periodic sets

## Problem

Jonathan Meddaugh and Elyssa Stephens, *Shadowing with small diameter sets
of bounded cardinality*, arXiv:2509.04312v1, Question 5.6:

> Is there a weakly mixing system which has the neighborhood N-shadowing property (N>1) that does not have dense small periodic sets?

Use the intended **nonempty** meaning of a small periodic set: a nonempty
compact set B with f^p(B)=B for a positive natural p. The printed definition
omits nonemptiness. The phase space is compact metric and the map continuous;
the source does not require a homeomorphism.

## Motivation

Ordinary shadowing and weak mixing yield dense small periodic sets in the
source's cited setting. The question asks whether the initial small diameter
of a finite tracing set forces the same conclusion. The example separates
that finite tracing property from every nonempty periodic-set neighborhood.

## Route

Let X consist of binary sequences on the natural numbers such that for every
s>=0 and p>=1 some j<=p^2+2 satisfies x(s+jp)=0. Equip X with the genuine
first-disagreement metric d(x,y)=2^(-firstDiff(x,y)), and shift left once.
Each fixed progression condition is clopen. Their intersection is closed
in the compact binary product. The zero point lies in X, and prepending
zero gives a legal preimage of every point, so the shift is onto.

Allowed prefixes of lengths a,b can be joined by zeros at every position
n>=a+max(a,b). A forbidden progression that crosses the gap must have step
larger than either prefix and thus at most two supported terms. This is
impossible for a forbidden length at least three. This proves mixing and,
by simultaneous hitting of two open rectangles, weak mixing on X times X.

For an accuracy epsilon, first fix R>=1 with 2^(-(R+1))<epsilon. Put
M=32(R+1), alpha=sqrt(2)/M, P=256M(M+3), D=max(R,P^3+2P) and delta=2^(-D).
For an arbitrary infinite delta-pseudo-orbit z, its diagonal c(n)=z(n)(0)
agrees with z(i) through D+1 after shifting by i. Hence all progression
constraints with p<=P already hold in c.

The lower bound ||k alpha||>=1/[M(M+3)k], combined with a short Dirichlet
return q<=16 and a signed mesh with explicit integer lifts, makes every
quarter-circle interval hit within Pp steps, uniformly in the starting
phase and positive p. Delete c on phases [1/8,3/8] to form a, and on
[5/8,7/8] to form b. Both branches preserve the already present small-step
zeros. For p>P, each forbidden progression meets each deletion mask by
index Pp<p^2+3, so both whole branches lie in X.

The initial R-window avoids both masks, while every later R-window avoids
at least one: R alpha<1/8 and the two quarter masks are separated across
integer boundaries. Thus the same nonempty set A={a,b}, of cardinality at
most two, has initial diameter less than epsilon and satisfies
infDist(z(i),sigma^i(A))<epsilon for every natural i. The choice of branch
may change with i; no all-time image-diameter bound is imposed.

Finally U=[1] contains 10-infinity and is clopen. If a nonempty B subset U
satisfied sigma^p(B) subset B for p>0, any b in B would have b(jp)=1 for
every natural j, contradicting its p-progression constraint. This excludes
nonempty compact periodic sets in a nonempty open set.

## Falsifier

The existence conclusion would fail if the specified carrier were not a
nonempty compact metric system, product transitivity failed, or the same
fixed N=2 did not satisfy the original infinite pseudo-orbit quantifiers.
In particular, conditional mask existence, a finite time horizon, a
time-dependent tracing set or omission of its initial diameter would not
answer the question. The periodic-set obstruction must use a nonempty open
U and explicitly nonempty B; the empty set supplies no obstruction.

## Evidence

The full endpoint is
`D5/S1/Dynamics/Shadowing/ProgressionExample.quadratic_progression_example`.
Its supporting modules are `ProgressionSubshift`, `QuadraticRotationHitting`
and `ProgressionTwoShadowing` in the same directory, with corresponding
Blueprint Scribe sources. Native canonical scoped elaboration has succeeded
for the full endpoint. Formal independent scientific review, freezing and
required CI are separate acceptance obligations.

The construction and explicit constants are attributed to the supplied
completed Pro proposal and its isolated ordinary mathematical review.
Native Lean implementation does not inherit a scientific or novelty verdict
from that ordinary review.

## Gap

The full intended mathematical existence conclusion has a native Lean proof.
No homeomorphism version, coherent single tracer or all-branches tracing
statement is asserted. The optional period-collapse and superlinear-length
generalization in the ordinary source are outside this endpoint.

The full-scope four-slot information-escape audit is unfinished under
[issue #26047](https://github.com/the-omega-institute/trureturing/issues/26047).
The Reg mirrors preserve full telescope positive-law attempts; they are not
Contract.Registration values or declared_validated evidence. Enrolled source
reconstruction, realization bridges, whole-family variation and sensitivity,
actual observational dependence and lawful readout binding remain missing.

## Triage

The construction proves the intended Question 5.6 existence conclusion with
the single fixed N=2. It also proves the stronger obstruction to every
nonempty forward power-invariant subset of [1], without compactness or
image equality. This is one original question; the arithmetic and topology
lemmas do not count as additional solved originals. The hierarchy Questions
5.1 and 5.2 and language-characterization Questions 5.4 and 5.5 remain
outside this result.

## ASSUMED-UNVERIFIED

Source correspondence uses the explicitly nonempty interpretation and a
genuine compatible symbolic metric, rather than the degenerate printed
window-infimum expression. The current arXiv metadata lookup returns v1
and the primary v1 text still asks Question 5.6. Bounded repository,
Mathlib, GitHub code and arXiv searches do not establish exhaustive exclusion
of a prior answer, novelty, worldwide priority or unique status. No official
acceptance, merged publication or complete escape audit is asserted here.
