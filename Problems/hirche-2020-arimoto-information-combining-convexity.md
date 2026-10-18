---
slug: hirche-2020-arimoto-information-combining-convexity
bibkey: hirche2020renyibounds
doi: 10.48550/arXiv.2004.14408
url: https://arxiv.org/abs/2004.14408v1
triage: theorem
motivation_gids:
  - D5/S3/Entropy/RenyiCombining/HircheArimotoCombining.result
---

# Arimoto information combining convexity and concavity

## Problem

C. Hirche, Rényi Bounds on Information Combining, ISIT 2020,
arXiv:2004.14408v1, §IV-A, Conjecture IV.6:

> There exists a value 1 < α̂ < 1.5783, such that k_α^A(k_α^A⁻¹(x) ∗ k_α^A⁻¹(y)) (47) is convex for 0 < α < 1 and concave for 1 < α ≤ α̂.

Equation (23) defines

$$
K_\alpha^A(X\mid Y)=e^{((1-\alpha)/\alpha)H_\alpha^A(X\mid Y)}.
$$

For binary $X\sim\{p,1-p\}$, $k_\alpha^A(p)=K_\alpha^A(X)$, hence

$$
k_\alpha^A(p)=(p^\alpha+(1-p)^\alpha)^{1/\alpha},\qquad
p\star q=p+q-2pq.
$$

Write $k_\alpha=k_\alpha^A$ below. Lemma IV.3, cited from
Hsu–Asoodeh–Salamatian–Calmon, gives convexity for $\alpha\ge2$;
Lemma IV.4 shows neither convexity nor concavity for
$\alpha\in(1.58,1.97)$.

The inverse is the restriction to $[0,1/2]$, with range
$I_\alpha=[\min(1,\delta_\alpha),\max(1,\delta_\alpha)]$,
where $\delta_\alpha=2^{(1-\alpha)/\alpha}$. Orders and exponents are real.
For each permitted order and every fixed $y\in I_\alpha$, the claim is the
full two-point `ConvexOn` or `ConcaveOn` inequality on the closed interval
$I_\alpha$. The specified witness is $\hat\alpha=3/2$.

## Motivation

This scalar inequality supplies the separate curvature needed for binary
Arimoto conditional Rényi information combining. The exact inverse branch,
real orders and boundary inputs are part of the assertion.

## Gap

The sign certificate at three halves requires an analytic proof over the
entire bias interval. A numerical sign test does not establish that uniform
claim. Rioul–Béguinot, HAL hal-05074668v1, Proposition 1 and Remark 6,
stated the threshold $\hat\alpha=3/2$ from a numerical sign check without
proving the sign throughout the parameter domain. See
[the source note](../Library/Entropy/rioulbeguinot2025informationcombining.md).

## Route

Set $\psi_\alpha(t)=k_\alpha((1-t)/2)$ and $E_\alpha(t)=t\psi_\alpha''(t)/\psi_\alpha'(t)$
on $0<t<1$. For $u=(1+t)/2$, $w=(1-t)/2$, $S=u^\alpha+w^\alpha$
and $D=u^{\alpha-1}-w^{\alpha-1}$, differentiation gives

$$
\psi_\alpha'={1\over2}S^{1/\alpha-1}D,\qquad
\psi_\alpha''={\alpha-1\over4}S^{1/\alpha-2}(uw)^{\alpha-2}.
$$

All bases are strictly positive. The slope has the sign of $\alpha-1$.
For $b=\alpha-1$, $t=\tanh s$ and $s>0$,

$$
\mathcal E_b(s)=E_\alpha(\tanh s)
={b\sinh s\cosh^2s\over\sinh(bs)\cosh((b+1)s)}>0.
$$

Its derivative divided by itself is

$$
L_b(s)=\coth s+2\tanh s-b\coth(bs)-(b+1)\tanh((b+1)s).
$$

For fixed $s>0$, both $f_s(r)=r\coth(rs)$ and $g_s(r)=r\tanh(rs)$
strictly increase on $r>0$. In the first case the derivative numerator is
$\sinh z\cosh z-z>0$, since its value at zero is zero and its derivative is
$2\sinh^2z>0$ for $z>0$. The second derivative formula is
$g_s'(r)=\tanh(rs)+rs/\cosh^2(rs)>0$.

If $-1<b<0$, put $q=-b\in(0,1)$. Oddness gives
$b\coth(bs)=q\coth(qs)$, so
$L_b=f_s(1)-f_s(q)+2g_s(1)-g_s(b+1)>0$.
If $0<b\le1/2$, the same comparisons give $L_b\ge L_{1/2}$.
At that exact endpoint,

$$
\mathcal E_{1/2}(s)={\cosh^2s\over2\cosh s-1},\qquad
\mathcal E_{1/2}'(s)=
{2\cosh s(\cosh s-1)\sinh s\over(2\cosh s-1)^2}>0.
$$

Thus $E_\alpha$ increases for both claimed order ranges. The identity
$p\star q=(1-tv)/2$, for $p=(1-t)/2$ and $q=(1-v)/2$, gives
$G_\alpha(\psi_\alpha(t),\psi_\alpha(v))=\psi_\alpha(tv)$.
The transported first derivative is
$R(t)=v\psi_\alpha'(vt)/\psi_\alpha'(t)$, and

$$
R'(t)={v\psi_\alpha'(vt)\over t\psi_\alpha'(t)}
       (E_\alpha(vt)-E_\alpha(t))\le0.
$$

The prefactor is positive. For $\alpha<1$ the inverse bias decreases,
giving a nondecreasing derivative in the coordinate $x$ and hence convexity.
For $\alpha>1$ it increases, giving concavity. Continuity extends these
inequalities to the closed interval. Bias $v=0$ gives a constant slice;
$v=1$ gives the identity slice.

The formal proof reuses the Cachin slope rather than rederiving the
real-power second derivative. With $c=(1-\alpha)/\alpha$ and the shared
positive bias slope $f(t)=-\frac{d}{dt}h_\alpha((1-t)/2)$,
$\psi_\alpha=\exp(c h_\alpha)$ and $\psi_\alpha'=-c\psi_\alpha f$.
The shared certificate $f'=fF/t$ gives $E_\alpha=F-ctf=A/(1+tT)$.
The identity $T=\tanh(bs)$ and uniqueness of derivatives identify this
expression with $\mathcal E_b$. Also,
$k_\alpha^{-1}(x)=h_\alpha^{-1}(\log(x)/c)$, so continuity of the inverse
comes directly from the existing inverse.

| Needed interface | Reused source | Use |
| --- | --- | --- |
| Convolution and bias product | `BinaryRenyiCombining.bconv`, `bconv_bias` | The combining reduction |
| Positive power sum and monotone probability entropy | `HircheCachinCombiningConcavity.powerSum_pos`, `h_strictMonoOn`, `h_image` | The exponential change of coordinate and exact range |
| Specified entropy inverse | `hInv_h`, `hInv_continuousOn` | The Arimoto probability inverse and its continuity |
| Bias derivative and positive slope | `psi_hasDerivAt`, `slope_pos` | The Arimoto bias derivative and its sign |
| Real-power elasticity | `slope_hasDerivAt`, `slope_eq`, `T_comp_hasDerivAt` | The Arimoto elasticity and its hyperbolic identity |
| Closed-interval curvature | Mathlib `MonotoneOn.convexOn_of_deriv`, `AntitoneOn.concaveOn_of_deriv` | Continuous endpoint extension |

## Falsifier

A violation consists of an allowed real order, a permitted fixed $y$, two
points of $I_\alpha$ and a convex weight violating the corresponding
inequality. Source fidelity and bibliographic priority are separate from
mathematical correctness of this statement.

## Evidence

The settling declaration is `result : claim` in
`D5/S3/Entropy/RenyiCombining/HircheArimotoCombining.lean`.
Its statement includes all real orders in both ranges and both coordinate
endpoints. The hyperbolic certificate is
`ArimotoHyperbolic.strictMonoOn_elasticity`.

## Triage

Conjecture IV.6 is **PROVED** with $\hat\alpha=3/2$ by `result : claim`.
Since $1<3/2<1.5783$, this witness meets the source's strict numerical
bound. The conjecture asks for the existence of such a threshold; it does
not assert concavity throughout $(3/2,1.5783)$.

The following full separate-curvature classification on positive orders
is **computed**, with its strictness and additional order ranges **OPEN**
as formalization targets:

| Order | Internal slices |
| --- | --- |
| $0<\alpha<1$ | Strictly convex |
| $1<\alpha\le3/2$ | Strictly concave |
| $3/2<\alpha<2$ | Neither convex nor concave |
| $\alpha\ge2$ | Strictly convex; this is the regime of Hirche's Lemma IV.3 |

Here “internal” means the fixed second bias belongs to $(0,1)$.
Endpoint slices are constant or identity and satisfy the non-strict
inequalities. At $\alpha=1$ the original coordinate is constant and the
specified inverse does not exist.

For the computed sharpness calculation, let $Q(z)=\sinh z/z$ with
$Q(0)=1$. Its convergent even Taylor expansion is $Q(z)=1+z^2/6+O(z^4)$. Therefore

$$
\mathcal E_b(s)={Q(s)\cosh^2s\over Q(bs)\cosh(\alpha s)},\qquad
E_\alpha(t)=1-{(2\alpha-3)(\alpha+1)\over3}t^2+O_\alpha(t^4).
$$

For $\alpha>3/2$ and every fixed $0<v<1$, the difference
$E_\alpha(vt)-E_\alpha(t)$ is strictly positive for sufficiently small
positive $t$. In particular, $v=1/2$ gives the slice
$y=k_\alpha(1/4)$ and positive second derivative, excluding concavity.
For $3/2<\alpha<2$, the explicit formula for $\psi''/\psi'$ shows
$E_\alpha(t)\to+\infty$ as $t\to1^-$, whereas $E_\alpha(vt)$ has a finite
limit. The second derivative is then negative near that endpoint,
excluding convexity as well. For $b\ge1$, parameter comparison gives
$L_b\le L_1=2(\tanh s-\tanh(2s))<0$, so elasticity decreases and internal
slices are strictly convex. Sharpness for $\alpha>3/2$, including failure
of concavity at $y=k_\alpha(1/4)$ for $\alpha\in(3/2,1.5783)$, is
**computed / OPEN**: these sharpness, strictness and remaining-range
arguments are not formalized.

## ASSUMED-UNVERIFIED

Citation indexes and subsequent literature have not been exhaustively
checked; bibliographic priority and the absence of a later analytic proof
are not established.
