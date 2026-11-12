---
slug: gangloff-guillon-oprocha-circle-finite-positive-expansivity
bibkey: gangloff2023various
doi: null
url: https://arxiv.org/abs/2310.17241v1
triage: theorem
motivation_gids:
  - D5/S1/Dynamics/Shadowing/CircleFinitePositiveExpansiveness.positivelyExpansive_of_finitelyPositiveExpansive
---

# Finite positive expansivity on the entire circle

## Problem

Silvère Gangloff, Pierre Guillon and Piotr Oprocha, *Various questions around
finitely positively expansive dynamical systems*, arXiv:2310.17241v1,
Question 3.1, Section 3, page 7, ask:

> Can we find, for every n ≥ 1, a positively (n + 1)-expansive map of the circle which is not positively n-expansive?

Write $\mathbb T=\mathbb R/\mathbb Z$, with its usual quotient metric, and

$$B^+_\varepsilon(x)=\{y\in\mathbb T:\ \forall t\in\mathbb N_0,\ d(f^t(x),f^t(y))<\varepsilon\}.$$

The exact repository theorem is

$$
\forall f:\mathbb T\to\mathbb T,\quad
\left[\operatorname{Continuous}(f)\ \land
\exists\varepsilon>0\ \exists N\in\mathbb N,\ N\ge1\ \land
\forall x\in\mathbb T,\ \#B^+_\varepsilon(x)\le N\right]
\Longrightarrow
\exists c>0\ \forall x,y\in\mathbb T,
\left[(\forall t\in\mathbb N_0,\ d(f^t(x),f^t(y))<c)\Longrightarrow x=y\right].
$$

Here `Circle` is exactly `AddCircle (1 : ℝ)`. `ForwardBowen` quantifies over
every natural time, including zero, with strict distance inequalities;
`ForwardBowenBound f univ ε N` uses extended cardinality of the actual set.
The same epsilon and finite natural bound work for every center on the entire
circle. The conclusion supplies a uniform positive scale that may differ
from epsilon. No smoothness, invertibility, surjectivity, covering, local
injectivity, orientation or mixing assumption is added.

## Motivation

The target GID is
`D5/S1/Dynamics/Shadowing/CircleFinitePositiveExpansiveness.positivelyExpansive_of_finitelyPositiveExpansive`.
A positively $(n+1)$-expansive map satisfies the finite hypothesis with
$N=n+1$. The conclusion is positive $1$-expansivity, hence positive
$n$-expansivity for every $n\ge1$. Thus the theorem rules out each requested
strict level, rather than only refuting the assertion for one value of $n$.
Conversely ordinary uniform positive expansivity gives the finite property
with $N=1$. This is a source consequence of the theorem, not a map
classification.

## Gap

The paper's Theorem 3.8, Section 3.1, page 9, states: “No interval system is
finitely positively expansive.” The repository's direct interval proof is
consumed by the circle proof and is not a new discovery. An interval
obstruction alone does not handle the circle seam or maps whose image is the
whole circle. The circle argument must derive local injectivity from the
original finite Bowen bound and then control complete forward orbits.

## Route

Failure of local injectivity supplies two distinct lifted turns. The
two-target crossing bridge handles both proper-arc and whole-circle images;
in the latter case the targets and selected pullbacks account for the seam
instead of treating the whole circle as an injective coordinate chart.
Exact transit and fold pullbacks extend each actual common-terminal history
into two disjoint histories. Prefix control includes every time through
$T+q+1$, including the final application of $f$; terminal equality controls
every later time. Repeating the extension produces $2^N$ distinct points in
one original strict infinite-time Bowen set, contradicting its bound $N$.
Thus local injectivity is derived.

Compactness then supplies a uniform injectivity radius. Uniform continuity
and the exact short-arc image lemma propagate an endpoint-close short arc
through every iterate. Distinct endpoints would force the entire infinite
arc into one finite Bowen set, a second contradiction. The resulting
separation scale is uniform over the full circle.

## Falsifier

A continuous selfmap of the entire circle satisfying one uniform finite
strict all-natural-time Bowen bound but lacking every uniform positive
expansivity scale would falsify the theorem. For the route, an unhandled
whole-circle image or seam, loss of disjointness in doubling histories, a
missing terminal-time estimate, or failure of short-arc propagation would
invalidate the proof. A bounded-time test or an argument assuming local
injectivity would not settle the stated target.

## Evidence

The target theorem and
`D5/S1/Dynamics/Shadowing/CircleFinitePositiveExpansiveness.isLocallyInjective_of_finitelyPositiveExpansive`
have compiled proofs with only `propext`, `Classical.choice` and `Quot.sound`
in their axiom closures. The interval obstruction is attributed to
[the source note](../Library/Topology/gangloff2023various.md), which records
the pinned primary question and theorem locators. The
[owning Blueprint](../Blueprint/D5/S1/Dynamics/Shadowing/CircleFinitePositiveExpansiveness.md)
connects the exact theorem to the negative answer to Question 3.1.

The four-slot escape audits remain unfinished under
[#27948](https://github.com/the-omega-institute/trureturing/issues/27948)
and the `CLAUDE.md` §3.9 linked-issue exception. No `declared_validated` Reg
registration is asserted.

## Triage

The settlement excludes all strict finite positive-$n$ hierarchy levels
above one for continuous selfmaps of the entire circle. Local injectivity
is a proved consequence; ordinary uniform positive expansivity itself
satisfies the finite property. The original paper's other results remain
unaffected. Question 3.2 concerning other one-dimensional continua remains
unresolved here; no extension to arbitrary graphs, higher dimensions or a
classification of circle maps is asserted.

The delivery uses `admission_basis: escape-witness`, supported by the new
two-target bridge, exact fold/history doubling and short-arc propagation on
the live proof path. The known interval obstruction is a consumed result.
The source-connection `OpenProblemResolutionClaim` records a mathematical
negative answer, not the `open-problem-resolution` admission basis. No circle
preregistration was found in the exact `2310.17241` GitHub query; no historical
preregistration or satisfaction of that basis's conditions is asserted.

## ASSUMED-UNVERIFIED

The primary arXiv v1 leaves Question 3.1 open; the indexed text of the 2026
journal version also displays it. Direct publisher-body access to that
version was unavailable, so unchanged numbering outside the pinned v1 is
not asserted. Comparison with Alfonso Artigue, *Symbolic models for
positively N-expansive homeomorphisms*, DOI
10.1016/j.topol.2026.110006, remains unresolved because its full body was
unavailable after primary retrieval attempts. Its abstract does not decide
whether its body contains an overlapping result for noninvertible circle
maps. No worldwide novelty, priority or present solved/unsolved-status claim
is made. The repository-derived circle proof is distinguished from the
known cited interval theorem.
