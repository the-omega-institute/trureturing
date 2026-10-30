---
bibkey: trureturing2026jointreciprocalvariational
authors: trureturing research synthesis
year: 2026
title: Joint reciprocal variational construction and exact measurable-class values
doi: null
url: https://github.com/the-omega-institute/trureturing/blob/c68136a75d73324c52cb78e83821f2683126fae6/Library/Estimation/trureturing2026pricegapconvexity.md#the-same-source-response-admits-a-larger-joint-variational-margin
claim: An attributed exact excerpt of the original JVM1--JVM6 analytic construction: the scalar endpoint, explicit positive functional, complete bounded positive measurable competitor class, attained joint infima, and the source-relative margin. The excerpt preserves the original 0<b<1 scope; the endpoint b=1 is a separate formal extension in the Lean/Scribe result.
strata_touched: []
license: Apache-2.0
triage: anchor
---

# Joint reciprocal variational construction and exact measurable-class values

This note is a concise faithful excerpt from the original project synthesis, [Actual Robin price gaps, forced-core tail records and the selected-sign boundary](https://github.com/the-omega-institute/trureturing/blob/c68136a75d73324c52cb78e83821f2683126fae6/Library/Estimation/trureturing2026pricegapconvexity.md), pinned to commit `c68136a75d73324c52cb78e83821f2683126fae6`, section **The same-source response admits a larger joint variational margin**. The excerpt below carries the complete JVM1--JVM6 analytic definitions, formulas, competitor scope, and attribution. The original section is a paper derivation and explicitly makes no Lean/kernel verification or literature-priority claim.

The original source section has scope $b=1-aQ_\eta\in(0,1)$. The later long note discusses the endpoint $b=1$ as an extension; that endpoint is not part of the original JVM1--JVM2 claim. The corresponding Lean formalization separately proves the endpoint in its stated range $0<b\le1$.

## Faithful source excerpt

## The same-source response admits a larger joint variational margin

Keep OSP1--OSP6's entire original conditional RH-failure source, all
fixed parameters $1-\Theta<\eta<1/2$, including allowed $\Theta=1$,
all original full windows and maximizing ties, the complete future,
original mesh and coarse ceiling. Keep the original one-use $a$ and
$b=1-aQ_\eta\in(0,1)$. Reuse OSP4's existing actual-source interface and the classical
convex supporting inequality. The resulting full-functional analytic
infimum supplies a larger source margin. This is a paper derivation;
no literature-priority or Lean/kernel verification is claimed.

### A scalar constant for the complete positive functional

Define

$$
D_b(v)=2b+3(1-b)v-6v^2,\qquad
\nu_b=\frac{3(1-b)+\sqrt{9(1-b)^2+48b}}{12},
$$

and, on $0\le v<\nu_b$,

$$
\Phi_b(v)=\int_0^v\frac{2b+6s}{D_b(s)}\,ds.
$$

This is strictly increasing, starts at zero and diverges at $\nu_b$.
Let $v_b$ be its unique solution of $\Phi_b(v_b)=\log2$, and put

$$
\mathcal C_b=8v_b^2(b+2v_b),\qquad
R_{\rm joint}(b)=\frac d2\sqrt{\mathcal C_b}.
\tag{JVM1}
$$

For a measurable $u$ bounded above and away from zero on $[1,2]$, set

$$
A=\int_1^2u(x)dx,\qquad U(x)=\int_1^x u(r)dr,
$$

$$
\mathcal D_b[u]=b\int_1^2\frac{x}{u(x)}dx
                  +\int_1^2\frac{U(x)}{u(x)^2}dx.
$$

The analytic value is

$$
\inf_u A\mathcal D_b[u]=\mathcal C_b,\qquad
\inf_u\frac d8\bigl(4A+\mathcal D_b[u]\bigr)
       =R_{\rm joint}(b).
\tag{JVM2}
$$

The infima are attained by smooth positive increasing functions; this
is an assertion about the analytic class, not arithmetic attainability.

### Convex sufficient comparison for the actual functional

By scaling $u$ it suffices to minimize $\mathcal D_b$ subject to $A=1$.
Use $y=\sqrt{U(x)}\in[0,1]$, write its inverse as $x=x(y)$ and set
$z(y)=x(y)^{3/2}$. Change of variables gives exactly

$$
\mathcal D_b[u]=\int_0^1\mathscr L_b(y,z,z')dy,\qquad
\mathscr L_b(y,z,p)=\frac{2b}{9y}p^2+\frac2{27}\frac{p^3}{z},
\quad z(0)=1,\ z(1)=2\sqrt2.
\tag{JVM3}
$$

The integrand is convex in $(z,p)$ for $z>0,p\ge0$. For $p>0$,
the Hessian of $p^3/z$ has entries
$2p^3/z^3$, $-3p^2/z^2$, $6p/z$ and determinant $3p^4/z^4>0$;
the first term is convex in $p$ as well. For global sufficiency, apply
R. T. Rockafellar, *Conjugate convex functions in optimal control and
the calculus of variations*, Journal of Mathematical Analysis and
Applications **32** (1970), 174--222,
[author-hosted primary paper](https://sites.math.washington.edu/~rtr/papers/rtr034-ConjConFnsOptimalControl.pdf),
Corollary 1, printed p.210. Its basic assumptions (A)--(D) are on
pp.179--180; extremality is (9.3) and (9.5), printed p.208.

Here extend $\mathscr L_b$ by $+\infty$ outside
$1\le z\le2\sqrt2$, $p\ge0$. At $y=0$ use the indicator of
$[1,2\sqrt2]\times\{0\}$. The endpoint function is the indicator
of $(z(0),z(1))=(1,2\sqrt2)$. These are proper lower semicontinuous
convex data. The integrand is Borel and hence Lebesgue-normal; its
nonnegativity supplies the zero affine minorant in (C), and the
constant measurable selection $(z,p)=(1,0)$ with zero value supplies
(D). Thus the singular $1/y$ coefficient satisfies the published
hypotheses. Only the classical global sufficiency statement is
imported; the following curve and its value are computed for JVM3.

Construct $v(x)=\Phi_b^{-1}(\log x)$ for $1\le x\le2$. Let
$w(x)>0$ solve

$$
\frac{w'(x)}{w(x)}=\frac{b+3}{x(2b+6v(x))},
\qquad\int_1^2 w(x)dx=1.
\tag{JVM4}
$$

Its normalization is possible because the differential equation is
linear for $\log w$ with a finite coefficient. It is smooth and
increasing. Direct differentiation, using
$xv'=D_b(v)/(2b+6v)$, gives

$$
W(x):=\int_1^xw(r)dr=xw(x)v(x),\qquad
w'=\frac{(b+3)w^2}{2bxw+6W}.
$$

In particular $w(2)=1/(2v_b)$. If
$P=-bx/w^2-2W/w^3$, the same equation gives $P'=1/w^2$, which
is the Euler equation for $bx/W'+W/(W')^2$.

For the corresponding $z_*$ in JVM3, put
$m=\partial_p\mathscr L_b(y,z_*,z_*')$. Differentiation gives
$m'=\partial_z\mathscr L_b=-2(z_*')^3/(27z_*^2)$.
Near $y=0$, $z_*(y)=1+O(y^2)$, $z_*'=O(y)$ and
$m(y)\to4b/(3w(1))$. Thus $m$ extends to an absolutely continuous
coextremal on $[0,1]$. The constructed curve lies in the interior of
the state and positive-velocity constraints almost everywhere, so
these derivatives give the published subgradient condition (9.3).
The fixed endpoint function imposes no further restriction in (9.5).
Rockafellar's Corollary 1 therefore gives global minimality among the
feasible absolutely continuous curves.

For every measurable bounded positive $u$ above, the inverse map is
Lipschitz, with $z(y)=1+O(y^2)$ near zero, and belongs to that feasible
class. This verifies the comparison on the entire stated analytic
class. The constructed equality profile $w$ has no zero or singular
endpoint. No general existence or dual-attainment theorem is needed.

Finally $(WP)'=-bx/w-W/w^2$. Thus

$$
\mathcal D_b[w]=-[WP]_1^2
 =\frac{2b}{w(2)^2}+\frac2{w(2)^3}
 =8v_b^2(b+2v_b)=\mathcal C_b.
$$

This proves the first assertion of JVM2. For arbitrary $A$, scaling
gives $A\mathcal D_b[u]\ge\mathcal C_b$; minimizing
$4A+\mathcal C_b/A$ proves the second. Its optimizer is
$u_*=(\sqrt{\mathcal C_b}/2)w$.

### Strict gain over the already retained Opial margin

The known Beesack--Das application OSP1 and pointwise AM--GM imply
$R_{\rm joint}\ge R_{\rm Op}$, with the latter defined in OSP5.
If equality held, apply those two inequalities to $u_*$. The
pointwise nonnegative AM--GM gap would have integral zero, forcing

$$
u_*(x)=\frac12\sqrt{bx+(x-1)^2}\quad(1\le x\le2).
$$

This profile has logarithmic derivative $1/2$ at $x=1$.
JVM4 instead gives $u_*'(1)/u_*(1)=(b+3)/(2b)>1/2$.
Both profiles are smooth, so they cannot agree almost everywhere.
Consequently, for every fixed original $0<b<1$,

$$
\boxed{R_{\rm joint}(b)>R_{\rm Op}(b).}
\tag{JVM5}
$$

No numerical approximation to $v_b$ or uniform positive gain as
$b\downarrow0$ is asserted.

### Consume the constant on the original full source

Use OSP4 without changing its proof. On its fixed interior interval
$[a_\theta,b_\theta]=[1+\theta,2-\theta]$ of length
$h=1-2\theta$, substitute $x=a_\theta+h(z-1)$ and
$u_X(x)=\sqrt h\,\widetilde u(z)$, $1\le z\le2$.
The source clock remains on its existing compact interior range,
so JVM2's analytic hypotheses hold. Since $x=hz+3\theta\ge hz$,
the right side of OSP4 is at least

$$
h^{3/2}\frac d8\left[4\int_1^2\widetilde u
  +b\int_1^2\frac z{\widetilde u(z)}dz
  +\int_{1\le r<v\le2}
       \frac{\widetilde u(r)}{\widetilde u(v)^2}drdv\right]-o(1)
\ge h^{3/2}R_{\rm joint}(b)-o(1).
$$

Take the source lower limit at fixed $\theta$, then
$\theta\downarrow0$. Exactly the existing bounded-response
contradiction in OSP2--OSP5 therefore yields

$$
\boxed{\liminf\frac{\mathcal G_{X,\mathcal T}}{M_XL_X}
\ge R_{\rm joint}(b)>R_{\rm Op}(b).}
\tag{JVM6}
$$

The bound is uniform over the original windows and tie assignments;
HC2 and CQ5 give the same margin for every original admissible-height
head and $\mathcal J_X$. The analytic infimum is not an assertion
that any prime-selected source attains it. No real-parameter capacity
extension, global clock bound, second compensation credit or pointwise
future-error sign is introduced. The independent same-source strict
upper, strict Robin for every integer above 5040 and RH remain open.



## Locator

- Immutable original URL: https://github.com/the-omega-institute/trureturing/blob/c68136a75d73324c52cb78e83821f2683126fae6/Library/Estimation/trureturing2026pricegapconvexity.md#the-same-source-response-admits-a-larger-joint-variational-margin
- Original source path: `Library/Estimation/trureturing2026pricegapconvexity.md`.
- Pinned source commit: `c68136a75d73324c52cb78e83821f2683126fae6`.
- Reviewed source SHA-256: `e4b0ba77ef6a7e8eb1f39c3e4874aaf69d3f8b84d91590f29176e0cb95342963`.

This local excerpt is the source citation used by the two joint reciprocal variational Scribes. It contains every analytic formula cited by JVM1--JVM6, including the complete bounded positive measurable class and the full variational targets. The original long note remains the immutable attribution and locator; this excerpt does not assert a new RH result or literature priority.
