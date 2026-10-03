---
bibkey: cfmp2026fibonacciobstruction
authors: trureturing contributors
year: 2026
title: CFMP Fibonacci return observation obstruction
doi: null
url: https://github.com/the-omega-institute/trureturing/pull/11418
claim: A scoped framed-return congruence obstruction with exact positive-modulus kernel normal form and image condition.
license: citation-only
triage: anchor
strata_touched: []
---

The cyclic CFMP return observation on integer pairs is

$$C(x,y)=(2x-y,x+2y).$$

These are the additive low and high return parameters of the cyclic construction;
they are not geometric edge lengths. The full discussion appears in
[Sections 133–139](../../docs/develop/theory/CFMP_GEOMETRIC_REALIZATION_OBSERVATION_DYNAMICS.md).
The elementary coordinate calculations below explain the observation and its
modular information loss.

Write

$$J(x,y)=(y,x),\qquad F(x,y)=(y,x+y),\qquad
D(x,y)=(-x+2y,2x+y),\qquad W=J\circ F\circ J.$$

Expanding both coordinates gives

$$D^2(x,y)=(5x,5y),\qquad C=D\circ J,\qquad C\circ W=F\circ C.$$

Thus $C$ first swaps the coordinates and then applies $D$. In the coefficient
basis $(1,\theta)$ of $\mathbb Z[\theta]/(\theta^2-\theta-1)$, $D$ is multiplication
by $2\theta-1$, whose square is five. The substitution matrix $F$ is the ordinary
Fibonacci matrix; identifying this particular readout does not identify the
whole tetrahedron geometry with a Fibonacci evolution.

For $k,t\in\mathbb N$, set $s(k,t)=(kt,2kt)$. Direct substitution gives the two
separate coordinate identities

$$C(z+s(k,t))_1=C(z)_1,\qquad
C(z+s(k,t))_2=C(z)_2+5kt.$$

If $a\equiv b\pmod m$ means $m\mid b-a$, these identities show that both observed
coordinates of $z+s(k,t)$ and $z$ agree modulo $5k$. The complete integer
description of this congruence kernel is

$$C(x,y)\equiv(0,0)\pmod{5k}
\quad\Longleftrightarrow\quad
\exists t,s\in\mathbb Z:\quad
x=kt,\quad y=2kt+5ks.$$

For necessity, write $-2x+y=5ka$ and $-x-2y=5kb$. Then
$x=-k(2a+b)$ and $y=2k[-(2a+b)]+5ka$, so take $t=-(2a+b)$ and $s=a$.
For sufficiency, the displayed input has output $(-5ks,5k(t+2s))$.

When $k>0$, reducing this normal form modulo $5k$ gives precisely

$$\ker C_{5k}=\{(kt,2kt):t=0,1,2,3,4\}.$$

The first coordinates are distinct modulo $5k$: if $5k\mid k(t-t')$, cancellation
of the nonzero integer $k$ gives $5\mid t-t'$, which forces $t=t'$ in the stated
range. Every nonempty observation fibre is a translate of this kernel and has
five residue classes. For $k=0$, congruence modulo zero means equality; the
normal form instead forces $x=y=0$, and all shifts $s(0,t)$ coincide. There is
no five-element kernel in that case. Over the integers themselves, $C$ is
injective; the five-element ambiguity concerns positive finite moduli divisible
by five.

The corresponding image condition is

$$\exists x,y\in\mathbb Z:\quad C(x,y)\equiv(r,s)\pmod{5k}
\quad\Longleftrightarrow\quad 5\mid 2r+s.$$

Indeed, $2C(x,y)_1+C(x,y)_2=5x$, proving necessity even after reduction modulo
$5k$. Conversely, if $2r+s=5q$, then $(x,y)=(q,2q-r)$ has output exactly $(r,s)$.
This equivalence also holds at $k=0$ as the image condition for the integer map.

At modulus $5040=5\cdot1008$, the five shifts are $(1008t,2016t)$ for
$t=0,1,2,3,4$. Their output differences are $(0,5040t)$. This is the same
factor-five obstruction; the factor seven contributes no additional kernel
state to this readout. It supplies no implication for Robin's criterion or RH.

The obstruction concerns framed return-parameter observations. Distinct residue
parameters do not by themselves prove distinct unmarked manifolds, a general
hyperbolic realization, or a counterexample to the minimum-six CFMP conjecture.
Sections 133–139 separately give the fuller dynamics and geometric families;
their finite auxiliary checks are in
[cfmp_fibonacci_ramification_check.py](../../docs/develop/theory/cfmp_fibonacci_ramification_check.py).
