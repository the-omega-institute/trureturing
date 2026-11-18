---
slug: johnston-leong-tudzi-2026-conjecture-5-1
bibkey: johnstonleongtudzi2026summatory
doi: 10.1080/10586458.2025.2483942
url: https://arxiv.org/abs/2408.04143v3
triage: theorem
motivation_gids:
  - D5/S3/Arith/Robin/Analytic/OmegaSigned/JLTConjecture.result
---

# The large-parameter signed Omega limsup

## Problem

Johnston, Leong, and Tudzi, Section 5.2, Conjecture 5.1:

> Let s_a be defined as in Theorem 1.5. Then lim_{a→∞} s_a = 1.

For real $a>2$, put $v=\log_2a$ and
$W_a(x)=\sum_{1\le n\le\lfloor x\rfloor}(-a)^{\Omega(n)}$,
where $\Omega$ counts prime factors with multiplicity. The target is
$s_a\to1$, with $s_a=\limsup_{x\to\infty}|W_a(x)|/x^v$.

## Motivation

The conjecture isolates the large-parameter limit of a normalized signed
summatory function. Its source statement and literature comparison are
supplied by preregistration #31439. This target does not require an
estimate uniform down to $a=2$.

## Gap

Termwise absolute values discard cancellation between successive powers
of two. The required bound retains that cancellation inside each odd-part
fiber, then controls the remaining odd integers uniformly in the cutoff.
The real limsup also requires upper boundedness and coboundedness.

## Route

Write $n=2^jm$ with $m$ odd. The signed sum on each fiber is
$(-a)^{\Omega(m)}G_J(a)$, where
$G_J(a)=(1-(-a)^{J+1})/(a+1)$ and $|G_J(a)|\le a^J$.
For odd $m$, $3^{\Omega(m)}\le m$ and
$2^{3\Omega(m)}\le m^2$. Thus, for $v\ge6$,

$$
\frac{a^{\Omega(m)}}{m^v}\le m^{-v/3},\qquad
\sum_{m=3}^M m^{-v/3}
\le3^{2-v/3}\sum_{m=3}^M\frac1{m(m-1)}
\le\frac12 3^{2-v/3}.
$$

The odd part $m=1$ gives the main term. A uniform upper bound applies
for all real $x\ge1$. At $x=2^k$, the same residual bound and the reverse
triangle inequality give the lower bound as $k\to\infty$.
Finally the error tends to zero and the two-sided estimate gives the limit.

## Falsifier

Distinct-prime counting in place of multiplicity, omission of the odd
part $m=1$, or use of a real limsup inequality without its boundedness
conditions would not establish the source assertion. An estimate only
along powers of two gives the lower bound, not the full upper bound.

## Evidence

**Proved in Lean:** The designated statements are `JLTConjecture.quantitative` and
`JLTConjecture.result`. The former asserts, for every real $a\ge64$,

$$
\frac a{a+1}-B(a)\le s_a\le1+B(a),\qquad
B(a)=\frac12 3^{2-\log_2a/3}.
$$

The latter asserts the exact limit of Theorem 1.5's real limsup.
The natural floor and the closed interval starting at one are explicit
in the Lean definition of $W$.

## Triage

**Proved mathematically from the quantitative estimate:** With
$\delta=\log3/(3\log2)>0$, the identity
$B(a)=(9/2)a^{-\delta}$ for $a>0$ gives

$$
|s_a-1|\le\frac1{a+1}+\frac92a^{-\delta}\qquad(a\ge64).
$$

Indeed $3^{2-\log_2a/3}=9\exp(-\log a\log3/(3\log2))$;
the two one-sided errors are bounded by $B(a)+1/(a+1)$.
The power identity and this error reformulation are not separate Lean
claims of the module.

**Computed exactly:** $a=64$ gives $v=6$ and $B(a)=1/2$;
$a=32$ gives $v=5$ and $r=v/3=5/3>1$.

**Proved mathematically, not separately formalized:** For $a<64$, the
particular telescoping comparison requiring $r=v/3\ge2$ no longer applies:
$m^{2-r}\le3^{2-r}$ fails for $m>3$ when $r<2$.
This is a limitation of the displayed estimate, not loss of uniform
boundedness of the odd-part sum. For $8<a<64$, one still has $1<r<2$;
the same odd-weight comparison gives a finite cutoff-independent constant
$C(a)=\sum_{m=3}^{\infty}m^{-r}$. In particular, at $a=32$ the convergent
series $\sum_{m=3}^{\infty}m^{-5/3}$ controls the odd-part contribution.
An integral comparison gives $C(a)\le2^{1-r}/(r-1)$.
The same proof then gives $a/(a+1)-C(a)\le s_a\le1+C(a)$;
this lower bound need not be close to one. The formula $B(a)$ has only
been certified as a tail bound for $a\ge64$; it is not asserted to work
below that threshold. For $2<a\le8$, the coarse majorant
$\sum m^{-v/3}$ diverges, which proves nothing about divergence of the
actual odd-part sum.

**Source-verified dependency, with proved consequences:** In the cited
v3, Conjecture 5.1 is the final conjecture of Section 5.2; no theorem in
the paper uses it as a hypothesis. Theorem 1.5 is proved independently
in Section 4 and already gives $s_a\ge1/2$ and

$$
s_a<U(a):=\frac{a-1}{a+1}\frac{3^v-1}{3^v-a}\zeta(v),\qquad a>2.
$$

The paper explicitly observes that $U(a)\to1$ as $a\to\infty$.
The new estimate supplies the missing lower bound tending to one,
$a/(a+1)-B(a)$ for $a\ge64$. Both sets of bounds remain valid; their
combination gives $s_a\ge\max\{1/2,a/(a+1)-B(a)\}$ and the upper
bounds $s_a\le1+B(a)$ and $s_a<U(a)$ in that range. No pointwise
comparison between the two upper bounds is asserted. Theorem 1.5's
full range $a>2$ is not replaced by the narrower formalized estimate.
Its zeta bound is a source theorem, not an additional Lean claim here.

**Unresolved here:** Conjecture 1.4 asserts the eventual strict bound
$|W_a(x)|<x^{\log_2a}$ for each fixed real $a\ge2$.
Neither $s_a\to1$ nor the upper bound $1+B(a)>1$ proves that assertion,
even for all sufficiently large fixed $a$. A parameter limit at infinity
does not supply $s_a<1$ for any particular $a$; even $s_a=1$ alone would
not imply the eventual strict inequality. Thus this settlement does not
settle a large-$a$ case of Conjecture 1.4, its complete parameter range,
or Sun's $a=2$ conjecture. The paper's independent Theorem 1.6 at $a=3$
is unaffected.

**Unresolved numerical claims, with source-verified motivation:** Section
5.2 reports plots and finite-window maxima for $x\le10^6$, and uses the
observed approach of maxima to one to motivate Conjecture 5.1. The
parameter limit is now proved, but these finite-window computations are
not independently recomputed here. The result does not turn those data
into exact values of $s_a$, prove the plotted strict bound for unbounded
$x$, or justify interchanging the finite-window and parameter limits.

## ASSUMED-UNVERIFIED

Worldwide priority and completeness of later literature are unverified.
The definitions, Conjectures 1.4 and 5.1, Theorems 1.5 and 1.6, and the
Section 5.2 dependency statements refer to the cited arXiv v3 text.
The paper's finite-window numerical results have not been independently
recomputed.
