---
slug: rakic-2026-theorem-2-13-ring-extension
bibkey: rakic2026squareanalogue
doi: 10.48550/arXiv.2611.34245
url: https://arxiv.org/pdf/2611.34245v1#page=33
triage: theorem
motivation_gids:
  - D5/S3/ArithUnits/RakicTheorem213RingExtension.result
---

# Rakić's Theorem 2.13 over rings

## Problem

Rakić asks which of the matrix results remain valid in rings and calls
out the use of Cayley–Hamilton in Theorem 2.13. The ring question for
that theorem is the following. Let \(R\) be a unital associative ring.
Let \(a,\alpha,b,\beta\in R\) satisfy \(G(a,\alpha)\) and \(G(b,\beta)\),
where \(G(x,y)\) means \(xyx=x\), \(yxy=y\), and \(xy=yx\).
Write \(a\le^- b\) if some \(u\in R\) satisfies \(aua=a\), \(ua=ub\),
and \(au=bu\). Is
\[
a\le^- b\ \land\ G(b-a,\beta-\alpha)
\quad\Longleftrightarrow\quad
a^3=aba=ab^2=b^2a\ \land\ (b-a)^3=b^3-a^3?
\]
[Theorem 2.13](https://arxiv.org/pdf/2611.34245v1#page=11) ·
[Section 4](https://arxiv.org/pdf/2611.34245v1#page=33)

## Motivation

The cubic conditions only use ordered ring operations. The matrix proof
uses finite-dimensional identities, so a proof over arbitrary
associative rings requires a different argument.

## Gap

Both directions must preserve the order of factors and establish
all three inverse equations for the difference. The ring may have any
characteristic and may be the zero ring.

## Route

Let \(p=b\beta\), \(e=a\alpha\), and \(c=b-a\). The minus relation is
equivalent to \(pa=ap=a\) and \(a\beta a=a\). For the reverse implication
in this witness characterization, use \(u=\beta a\beta\). These
identities also give \(c\beta c=c\).

In the forward direction the group inverse equations for \(c\) and
\(\beta-\alpha\) give \(c\alpha c=0\), \(\alpha b\alpha=\alpha\),
and \(be\beta=\beta eb\). The last two identities give \(ebe=a\)
and \(b^2e=eb^2=a^2\), hence the first three cubic equalities.
Apply the same argument to \(c\le^- b\) to get
\(c^3=b^2c=b^3-a^3\).

Conversely the first three cubic equalities give the support
conditions and \(a\beta a=a\). The last equality gives
\(bab=ba^2+a^2b-a^3\). Multiplication on the left by \(\beta^2\)
gives \(c\alpha c=0\). Substituting in the ordered product
expansions gives both inverse identities and commutation.

## Falsifier

A pair of group-invertible elements in a unital associative ring
would refute the extension if exactly one side of the equivalence
held for their specified group inverses.

## Evidence

The Lean theorem gives both directions over \([\mathrm{Ring}\ R]\).
The group inverse is represented by the finite Drazin relation with
zero remainder, which is equivalent to the three equations above.
[Lean source](../D5/S3/ArithUnits/RakicTheorem213RingExtension.lean) ·
[Versioned source and attribution](../Library/ArithUnits/rakic2026squareanalogue.md) ·
[Preregistration](https://github.com/the-omega-institute/trureturing/issues/35233)

## Triage

**Proved.** The matrix criterion extends to all unital associative
rings, including the zero ring.

## ASSUMED-UNVERIFIED

The bounded search recorded in the preregistration located no earlier
settlement. Worldwide priority remains unverified.
