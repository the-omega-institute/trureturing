---
slug: meddaugh-stephens-2025-neighborhood-two-shadowing
bibkey: meddaugh2025neighborhoodshadowing
doi: null
url: https://arxiv.org/abs/2509.04312v1
triage: theorem
motivation_gids:
  - D5/S1/Dynamics/Shadowing/PowersTwoReturnDistances.powers_two_return_distance_example
---

# Neighborhood two-shadowing without quasi-finite type

## Problem

Jonathan Meddaugh and Elyssa Stephens, *Shadowing with small diameter sets
of bounded cardinality*, arXiv:2509.04312v1, Question 5.3:

> Are there subshifts with neighborhood 2-shadowing which are not a subshift of quasi-finite type?

Use neighborhood shadowing from Definition 2.1 and exact-length
quasi-finite type from Definition 3.5, with their full quantifiers as
retained in the [source note](../Library/Dynamics/meddaugh2025neighborhoodshadowing.md).

## Motivation

The explicit example separates the finite tracing-set property with an
initial diameter bound from the exact-length language gluing property.
The general theorem `unbounded_return_neighborhood_two` supplies a reusable
positive result for every return-distance set containing one and
arbitrarily large positive distances.

## Route

Let $X_D\subseteq\{0,1\}^{\mathbb Z}$ consist of configurations whose
consecutive ones have distances in $D=\{2^j:j\geq0\}$, and put
$\sigma(x)(k)=x(k+1)$. The zero-run lengths are $2^j-1$, rather than
$2^j$. The space includes finite supports, singleton supports and the
configuration with no ones. Its defining local exclusion is closed and
invariant under integer shifts, so it is a nonempty compact subshift.

For each $\varepsilon>0$, choose a signed window radius $r$ controlling
the compatible product metric, an allowed distance $h>2r$, and
$\delta>0$ forcing pseudo-orbit overlap on radius $2h$. The signed
diagonal extends the negative-time part using the exact orbit of the
initial point. Retain its ones from $-r$ onward. Short consecutive gaps
are legal; a forbidden gap $(p,q)$ longer than $2h$ is repaired by
inserting ones from $p+h$ to $q-h$. New consecutive distances are $h$ or
$1$, both allowed. This gives one tracer; truncating the original support
to $[-r,r]$ gives the other. They agree initially on this window.
At every natural time, a window containing an original one agrees with
the repaired tracer, while a window with no original one agrees with the
truncated tracer. Their fixed set $A$ is nonempty, has at most two points
and initial diameter less than $\varepsilon$, and satisfies
$\operatorname{infDist}(x_i,\sigma^i(A))<\varepsilon$ for every $i$.

For a proposed QFT threshold $M$, take $n=\max(M,1)$ and
$H=2^{n+2}$. The nonempty words $u=10^H$, $w=0^n$ and $v=1$ belong to
the language, as do $uw$ and $wv$. A replacement $z$ of length exactly
$n$ with $uzv$ in the language would force the first return after the
leading one to lie in $(H,H+n+1]$. This interval lies strictly between
the consecutive powers $H$ and $2H$, so no such return is allowed.

## Falsifier

The proposed source-level answer would fail if some $\varepsilon>0$
allowed, for every $\delta>0$, a natural-time $\delta$-pseudo-orbit in
$X_D$ with no fixed nonempty finite $A\subseteq X_D$ satisfying
$|A|\leq2$, $\operatorname{diam}(A)<\varepsilon$ and
$\operatorname{dist}(x_i,\sigma^i(A))<\varepsilon$ for every $i\geq0$.
The displayed QFT obstruction would fail if, for some proposed threshold
$M$, its words admitted a language word $z$ of length exactly
$n=\max(M,1)$ with $uzv$ in the language. A mismatch with the original
Definitions 2.1 or 3.5 would defeat the claimed source correspondence.
These are failure criteria for the inference, not claims that they occur.

## Evidence

The endpoint is
`D5/S1/Dynamics/Shadowing/PowersTwoReturnDistances.powers_two_return_distance_example`.
It states nonemptiness and compactness of the actual binary two-sided
subshift, continuity of its shift, original neighborhood two-shadowing,
and negation of the original exact-length QFT predicate. Its three
supporting modules are `ReturnDistanceSupport`, `ReturnDistanceSubshift`
and `ReturnDistanceShadowing` in the same D5 directory. The corresponding
Blueprint document gives the statement and consumer exposition.

The encoded metric is Mathlib's genuine compatible countable-product
metric, not the degenerate printed infimum over disagreeing windows.
The proof uses the product uniformity directly. It preserves natural
pseudo-orbit time, integer configuration coordinates, a fixed nonempty
finite tracing set and exact bridge lengths.

The four-slot information-escape audit is unfinished under
[issue #22664](https://github.com/the-omega-institute/trureturing/issues/22664).
The 23 typed positive-law checks are not registrations: source
reconstruction, whole-family variation and sensitivity, observational
dependence, and enrolled readout binding remain missing. They are not
`declared_validated` evidence.

## Gap

The encoded example answers the stated existence question affirmatively.
The primary version still lists the question; bounded independent search
found no exact prior answer within its searched scope. This is not an
exhaustive novelty or global-priority claim. The source note records
full-text limits for Carrasco-Olivera et al. (2022) and Dastjerdi–Hosseini
(2010), and the withdrawal of Dastjerdi–Jangjoo arXiv:1108.3242.
Ordinary $N$-shadowing, density shadowing and entropy QFT do not replace
the two definitions used here.

## Triage

The mathematical endpoint concerns Question 5.3 only. It does not settle
the full Question 5.2 hierarchy or assert nonsoficity. Kernel verification
certifies the encoded statements; correspondence to the scholarly
question remains a source-reading judgement. No official acceptance is
claimed.

## ASSUMED-UNVERIFIED

Source correspondence remains a source-reading judgement using the
genuine compatible product metric, not equality with the degenerate
printed infimum. Literature exclusions are bounded: the full texts of
Carrasco-Olivera et al. (2022) and Dastjerdi–Hosseini (2010) remain unread.
The audit under issue #22664 remains unfinished; the 23 positive-law
checks are not `declared_validated`. No exhaustive novelty, global
priority or official acceptance is claimed.
