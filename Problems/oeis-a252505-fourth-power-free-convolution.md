---
slug: oeis-a252505-fourth-power-free-convolution
bibkey: oeis2026a252505
doi: null
url: https://oeis.org/A252505
triage: theorem
motivation_gids:
  - D5/S3/Arith/Divisors/OeisA252505FourthPowerFreeConvolution.claim
---

# The whole A252505 convolution

## Problem

For every positive integer $n$,
$$
a(n)=\sum_{d\mid n}b(d)c(n/d).
$$
Here $a(n)$ counts positive divisors not divisible by any prime fourth power.
The value $b(n)$ counts positive integer pairs $x\le y$ satisfying
$1/n=1/x+1/y$ in $\mathbb Q$, with $x=y$ allowed. Write
$$
h(n)=\sum_{d\mid n}\left\lceil\frac{\tau(d)}2\right\rceil,
\qquad g(n)=h(n)\bmod2.
$$
The integer function $c$ has $c(1)=1$ and, for $n>1$,
$$
c(n)=-\sum_{d\mid n,\ d<n}g(n/d)c(d).
$$
The exact unchanged Lean proposition is 'claim'. Its quantifier is
'all n : Nat, 1 <= n -> ...'; no restriction on prime support or exponents
and no multiplicativity of $b$ or $g$ is assumed.

## Motivation

The target connects the fourth-power-free divisor count with the native rational
unit-fraction count and the specified Dirichlet inverse on every positive index.

## Gap

The two counting theorems retain unfinished source-family audits in
https://github.com/the-omega-institute/trureturing/issues/27506.

## Route

### Native bridges

The actual rational solutions biject with the positive factor pairs
$(x-n)(y-n)=n^2$, ordered by size. The swap involution has precisely the
fixed pair $(n,n)$; consequently $2b(n)=\tau(n^2)+1$, including the diagonal
$(x,y)=(2n,2n)$.

The canonical Mathlib Dirichlet inverse satisfies the stated recursion, whose
positive-domain solution is unique. No value at zero occurs in 'claim'.

### Finite exponent-box proof

Write $f(p)=v_p(n)$. Positive divisors correspond to the complete finite box
$0\le v\le f$, and fourth-power-free divisors impose $v(p)\le3$. Hence
$a(n)=\prod_p(\min(f(p),3)+1)$.

Define the integer local functions
$$
T(e)=\sum_{k=0}^e(k+1),\qquad U(e)=\sum_{k=0}^e[2\mid k],
$$
and define $S(e)$ to be one on residues zero and one modulo four and zero
elsewhere. Let $R(e)$ be one on residue zero, minus one on residue one,
and zero elsewhere. Products range over the finite support of $f$.
The ordinary ceiling identity $2\lceil m/2\rceil=m+(m\bmod2)$ and a finite
box expansion give
$$
2h(n)=\prod_pT(f(p))+\prod_pU(f(p)).
$$
The local formulas $2T(e)=(e+1)(e+2)$ and $U(e)=\lfloor e/2\rfloor+1$
yield the following congruences in $\mathbb Z/4\mathbb Z$:
$$
T(e)^2=S(e),\qquad T(e)U(e)=R(e),\qquad
T(e)^2=U(e)^2,\quad T(e)+U(e)=T(e)^2+T(e)U(e).
$$
The last two relations are preserved under coordinatewise multiplication
of pairs. Consequently
$$
\prod_pT(f(p))+\prod_pU(f(p))\equiv
\prod_pS(f(p))+\prod_pR(f(p))\pmod4.
$$
Set $\Gamma(f)=(\prod_pS(f(p))+\prod_pR(f(p)))/2$. The two products are
either both zero, or one and a sign. Thus $\Gamma(f)\in\{0,1\}$ and
$g(n)=h(n)\bmod2=\Gamma(f)$, as an equality of integers.

The local finite convolution identities are
$$
\sum_{k=0}^e(\min(e-k,3)+1)S(k)=2e+1,\qquad
\sum_{k=0}^e(\min(e-k,3)+1)R(k)=1.
$$
Both follow from the four-step recurrence and their first four values.
Expanding the finite exponent box now gives
$$
2\sum_{d\mid n}a(d)g(n/d)=\prod_p(2f(p)+1)+1
=\tau(n^2)+1=2b(n).
$$
Therefore $b=a*g$ on every positive index. The exact inverse recursion then
cancels $g$ and gives $a=b*c$, the unchanged complete conjecture. Empty
support gives $n=1$; the original unit-fraction count retains $(2n,2n)$.

## Falsifier

A positive integer at which the two sides of the displayed convolution differ,
with the exact counts and inverse recursion above, would falsify the conjecture.

## Evidence

### Source and literature boundary

The primary conjecture is the A252505 FORMULA line quoted in
Library/PrimeForms/oeis2026a252505.md. Preregistration:
https://github.com/the-omega-institute/trureturing/issues/27491.
The accepted bounded source and literature screen supplies the attribution
and unproved-in-searched-scope premise.
The attribution is The OEIS Foundation Inc.; the source is cited under the
`citation-only` license recorded in Library/PrimeForms/oeis2026a252505.md.

The resolving declaration is
`D5.S3.Arith.Divisors.OeisA252505FourthPowerFreeConvolution.result : claim`.
It assumes no multiplicativity of $b$ or $g$. The parity argument stays over
the integers before passing to the finite ring of characteristic four.

The exact inverse recursion and its positive-domain uniqueness supply the
source identification; neither is a separate retained mathematical endpoint.
No fresh transient verification is asserted here.

## Triage

The proposed admission basis is `open-problem-resolution` under #27491.
The retained public theorem targets are `unit_fraction_count`,
`unit_fraction_divisor_formula` and `result`. The result has a validated source
mirror.
The parity bridge `g_gamma` is content on the live
derivation path of `result`; no auxiliary claim of separate novelty is made.

## ASSUMED-UNVERIFIED

Worldwide openness and originality outside the accepted bounded source and
literature screen are ASSUMED-UNVERIFIED.
