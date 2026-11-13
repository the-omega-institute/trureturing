---
slug: oeis-a116387-six-term-recurrence
bibkey: mathar2011a116387
doi: null
url: https://oeis.org/A116387
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/Algebraic/MatharA116387SixTermRecurrence.result
---

# The six-term Motzkin recurrence A116387

## Problem

Let $M$ be the native Motzkin ordinary generating function, and let
$y^2=1-2x-3x^2$ with $y(0)=1$. Set

$$F=\frac1{y(2-M)},\qquad a_n=[x^n]F.$$

Mathar's conjecture in OEIS A116387 asks for

$$
\begin{aligned}
&n(17n-142)a_n+(17n^2+95n+138)a_{n-1}\\
&+(-391n^2+2488n-2908)a_{n-2}
+(-17n^2-603n+1892)a_{n-3}\\
&+2(697n-2021)(n-4)a_{n-4}
+60(17n-47)(n-4)a_{n-5}=0.
\end{aligned}
$$

The complete domain is every natural $n\ge5$. This is the maximal
well-formed offset-zero interpretation of all six printed terms. The
source does not print an onset; OFFSET `0,2` is not a recurrence onset.
Scalars are rational and lagged indices use natural subtraction, which
agrees with ordinary subtraction on this domain. The immutable source,
attribution and license are in
`Library/RecurrenceAlgebraic/mathar2011a116387.md`.

## Motivation

The problem concerns one particular six-term recurrence for the exact
native generating function. Existing sequence computation and generic
holonomic methods do not alone answer this assertion.

## Gap

The bounded
source and prior comparison is in
https://github.com/the-omega-institute/trureturing/issues/30173.
It makes no claim of global priority or exhaustive absence of earlier
proofs.

## Route

Construct $M=c(x^2/(1-x)^2)/(1-x)$ using the native Catalan series.
Its constant coefficient is one, and the Catalan quadratic gives
$M=1+xM+x^2M^2$. For any second solution $m$,
$(1-x-x^2(m+M))(m-M)=0$; the first factor has constant coefficient one.
Thus the native solution exists and is unique. Define
$y=1-x-2x^2M$. The same quadratic gives its required square and constant
coefficient. Any other normalized root $z$ satisfies
$(z+y)(z-y)=0$ with $(z+y)(0)=2$, hence equals $y$. The denominator
$y(2-M)$ has constant coefficient one, so $F$ is a genuine unit inverse.

Write $d=1-2x-3x^2$, $q=1-2x-4x^2$, and $p=1-x-4x^2$.
The native quadratic gives the exact bridge

$$2qyF=y+p.$$

No step treats $x$ as a unit. Differentiation, together with
$yy'=-1-3x$, yields

$$DF'-eF=f,$$

where

$$D=pqd,\quad e=2-2x-14x^2-14x^3+40x^4+48x^5,
\quad f=2x-6x^2-6x^3.$$

Let $P_j$ be the printed coefficient polynomials and
$L=\sum_{j=0}^5x^jP_j(\theta+j)$, where $\theta=x\partial$ and
each $P_j(\theta+j)$ acts before multiplication by $x^j$.
For $w=17x^2(5x+1)$ and $v=-5x(47x+25)$, the exact ordered identity is

$$pL=wD\partial^2+[w(D'-e)+vD]\partial-we'-ve.$$

Apply this identity to $F$ and use the differential equation and its
derivative:

$$pLF=wf'+vf=6px^2(5x-36).$$

Cancel $p$, which has constant coefficient one. For every $n\ge5$ the
forcing coefficient vanishes, and
$[x^n](x^jP_j(\theta+j)F)=P_j(n)a_{n-j}$ for each $j=0,\ldots,5$.
The coefficient equation is exactly the six printed terms, including
the boundary index $n=5$.

## Falsifier

A nonzero printed left side for this exact native coefficient sequence
at any $n\ge5$ refutes the assertion. Finite-prefix agreement cannot
prove the universal statement. A different generating function, root
branch, recurrence or eventual onset is a different target.

## Evidence

The candidate Lean address is
`D5/S1/Recurrence/Algebraic/MatharA116387SixTermRecurrence.result`.
Its claim includes the explicit native source specification and the
unbounded recurrence. Its helpers provide only the source construction,
normalization, bridge, differential equation and operator equation
required by this result. Classical power-series identities and
polynomial normalization are not separate open-problem resolutions.

The retained sources are an unverified proof candidate. Current Lean
compilation, accepted axiom closure, source-bound Reg evidence and the
canonical rendered projection are unavailable. The original target
remains unsettled as a formal delivery. The unfinished audit of `result`
is associated with issue #30173; no validated binding is asserted.

## Triage

| Assertion | Mechanism and boundary |
| --- | --- |
| Native source | Open as a compiled result: the candidate gives construction, quadratic uniqueness, normalized-root uniqueness and unit inverse |
| Exact six-term event | Open as a compiled result: the candidate differential certificate and six shifts target every $n\ge5$ |
| Polynomial certificate | Computed symbolically: the three ordered operator residuals and forcing residual are zero; this is not Lean evidence |
| Finite coefficients | No finite-prefix experiment substitutes for the universal theorem |
| General algebraic recurrences | Classical supporting method, with no separate open-problem claim |
| Other assertions in A116387 | Asymptotics, the inverse Motzkin transform and double-binomial representation are outside this theorem |
| Priority | Universal absence of a prior proof remains unverified; the literature comparison is bounded |

## ASSUMED-UNVERIFIED

The candidate's Lean elaboration, proof terms, standard-three axiom
closure and source-bound registration have not been verified. The build
blocker and missing evidence are recorded in issue #30173. Source
structure and symbolic polynomial checks do not establish
the universal recurrence. No theorem settlement or publication is
claimed by this dossier.
