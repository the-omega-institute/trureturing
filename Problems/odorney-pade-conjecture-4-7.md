---
slug: odorney-pade-conjecture-4-7
bibkey: odorney2026pade
doi: 10.48550/arXiv.2611.01029
url: https://arxiv.org/pdf/2611.01029v1#page=16
triage: theorem
motivation_gids:
  - D5/S1/Depth/ContinuedFractions/ODorneyPadeJunctionRefutation.claim
---

# O'Dorney's Conjecture 4.7

## Problem

For every pair of nonzero integers $a,b$ with $D=a^2+4b>0$ and every
integer pair $1\le i<k$, the conjecture asserts that
$\Upsilon_{k,i}(\alpha)=0$ implies $k=4$, $i=3$, and $a^2=b$. Here
$h(X)=X^2-aX-b$ and $\alpha=(a+\sqrt D)/2$ is its larger real root.
Write $\beta_j=[X^{2i-j}]h(X)^{i-1}(X-\alpha)^2$ for $0\le j\le 2i$
and set $\beta_j=0$ outside that range. Equation (4.2) defines
$\Upsilon_{k,i}(\alpha)$ as the determinant of the $(k-i)$-square matrix
with entry $\beta_{i+c-r}$ at zero-based row $r$ and column $c$.
[O'Dorney, arXiv:2611.01029v1, §4.2, p. 16, Exercise 4.6 and Conjecture 4.7](https://arxiv.org/pdf/2611.01029v1#page=16)

## Motivation

The determinant detects extra contact at one basepoint in a two-point
Padé approximation. Exercise 4.6 relates its zero to an empty junction
and equal adjacent patches after renormalizing an existing patch-junction
decomposition.

## Gap

The proposed exception overlooks cancellation in the one-entry matrix
at $(k,i)=(5,4)$.

## Route

At $(a,b,k,i)=(3,3,5,4)$ the sole entry is $\beta_4$. The coefficients of
$X^2,X^3,X^4$ in $(X^2-3X-3)^3$ are $-54,27,18$. Multiplying by
$(X-\alpha)^2$ gives
$\beta_4=-54-54\alpha+18\alpha^2=18(\alpha^2-3\alpha-3)=0$.
The discriminant is $21$ and the proposed conclusion would force $5=4$.

## Falsifier

An admissible input outside the proposed exception with exact zero
determinant refutes the universal implication. For the preregistered
one-entry route, the zero must follow from the coefficient in (4.2) at
the larger root. The witness also meets the auxiliary arithmetic
conditions in Exercise 4.1 since $3>0$, $4^2<21<5^2$, and $3\mid 9$.
[Preregistration #31986](https://github.com/the-omega-institute/trureturing/issues/31986)

## Evidence

Lean checks the closed `claim : Prop` and the literal `result : Not claim`
by the particular witness above. The source field's real embedding
preserves and reflects the determinant zero. The problem's typed
refutation is attached to the result's Scribe declaration.
[Source DOI](https://doi.org/10.48550/arXiv.2611.01029)

## Triage

Tier 1 named determinant conjecture. For the single index pair $(k,i)=(5,4)$,
a supplemental algebraic calculation gives the full zero criterion.
The coefficients of $X^2,X^3,X^4$ in $h^3$ are
$3b^2-3a^2b$, $-a^3+6ab$, and $3a^2-3b$. Combining them with weights
$1,-2\alpha,\alpha^2$ and substituting $\alpha^2=a\alpha+b$ gives
$\Upsilon_{5,4}(\alpha)=5a(a^2-3b)\alpha$.
Since $a\ne0$ and $h(0)=-b\ne0$, the determinant vanishes exactly when
$a^2=3b$. The resulting integer family is $(a,b)=(3m,3m^2)$ for
nonzero integers $m$, with $D=21m^2$. Its positive-$a$ members have
nonsquare discriminant and $b\mid a^2$. The cases $b=1$ and $b=-1$ give
no zero at this index pair. The Lean theorem uses only the member $m=1$.
The paper reports a search for additional invisible junctions through
$k\le20$. The calculation here covers the specified index pair.
[Source search and verification criteria](https://github.com/the-omega-institute/trureturing/issues/31986)

For the witness $(a,b,k)=(3,3,5)$, multiply the descending coefficient
vector of $h^i$ by convolution with $(1,-3,-3)$ to get the vector for
$h^{i+1}$. With zero extension, Lemma 2.1, equation (2.7), takes
$\Delta_{5,i}$ to be the $(5-i)$-square determinant with entry
$c_{i+c-r}$ at zero-based row $r$ and column $c$, where
$c_j=[X^{2i-j}]h^i$. Exact evaluation gives
$(\Delta_{5,0},\ldots,\Delta_{5,5})(3,3)=(1,171,1296,1701,-189,1)$.
[Lemma 2.1, p. 6](https://arxiv.org/pdf/2611.01029v1#page=6)

For $u_0=0$, $u_1=1$, and $u_{n+2}=3u_{n+1}+3u_n$, the conditions
$a=3>0$, $D=21$ positive and nonsquare, $3\mid9$, and all six
$\Delta_{5,i}(3,3)\ne0$ give the hypotheses of Exercise 4.1(b).
The exercise gives a patch-junction decomposition of $(u_{n+1}/u_n)^5$
for all sufficiently large $n$. Its words depend on residue classes
of $n$, its patch repetition counts are linear within the stated residue
classes, and its partial quotients remain bounded as $n$ grows.
In this decomposition, Exercise 4.6 applies to $\Upsilon_{5,4}(\alpha)=0$
and gives $J_{4,n}=\varnothing$ and $P_{3,n}=P_{4,n}$ after
renormalization for all such $n$. Its converse gives determinant zero
if the empty junction and equal adjacent patches occur for some $n$.
These continued-fraction conclusions use the paper's exercises and the
exact computation above. Lean certifies the $\Upsilon$ counterexample.
[Exercise 4.1(b), p. 15](https://arxiv.org/pdf/2611.01029v1#page=15) · [Exercise 4.6, p. 16](https://arxiv.org/pdf/2611.01029v1#page=16)

## ASSUMED-UNVERIFIED

Open here are explicit patch and junction words and period values for the
witness, a general classification of invisible junctions, vanishing at other
indices in the $b=\pm1$ subdomain, and the global $\Delta$ question behind
Conjecture 4.5. The bounded literature screen recorded in the preregistration
establishes the scope checked for earlier settlements.
