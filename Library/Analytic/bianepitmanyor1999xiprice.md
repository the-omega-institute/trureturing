---
bibkey: bianepitmanyor1999xiprice
authors: Philippe Biane, Jim Pitman, Marc Yor
year: 1999
title: Probability laws related to the Jacobi theta and Riemann zeta functions, and Brownian excursions
doi: null
url: https://arxiv.org/abs/math/9912170v1
claim: The classical positive xi law admits positive inverse-moment calibration for the Robin price observer. Every occupied exponent layer then has nonnegative observed cost; the complete signed Robin comparison remains unpaid.
strata_touched: []
license: citation-only
triage: anchor
---

# Positive inverse-moment xi observation and actual occupied layers

The primary is Biane--Pitman--Yor,
[arXiv:math/9912170v1](https://arxiv.org/pdf/math/9912170v1),
§2.2, equation (20), printed p.6, and Proposition 1(i), equation (21),
p.7. The inspected 40-page PDF has SHA-256
`04a444275e5522cef9a1ba9f7d1b9f20a752764d3548f9c48be6dbc055bb12ea`.
The probability law and its reciprocal identity are classical; the
[Nicolas card's XLR1](../ArithSums/nicolas2025comparison.md#a-classical-positive-xi-law-pays-the-smoothed-response-on-an-unlimited-range)
already owns their mean-normalized Robin use. They are not reconstructed
here. The application below uses inverse normalization instead, with
KTO's existing observation kernel. It supplies a sign for the actual
occupied layers, rather than positivity of a signed measure or a new
prime-distribution estimate. No literature priority or Lean certification
is claimed, and RH and full strict Robin remain unresolved.

## A positive source with exact inverse moment

Reuse the primary's positive variable $Y$ with
$\mathbb E Y^s=2\xi(s)$ for every complex $s$. Set

$$
C=Y^{-1},\qquad h(s)=\mathbb E C^{s-1}=2\xi(s),\qquad
m=\pi/3,\qquad b_+=h(1/2),\qquad a_+=\mathbb E\log C.
\tag{IPX1}
$$

All fixed real moments are finite, $\mathbb EC^{-1}=1$ and
$\mathbb EC=m>1$. Nondegeneracy and strict Jensen give
$0<b_+=\mathbb E\sqrt Y<1$ and $a_+=-\mathbb E\log Y>0$.
The zeros $h(\rho)=0$ include every actual nontrivial zeta zero,
without a premise about its real part. This source differs from XLR's
$1/(mY)$; its ordinary mean is not one.

For $A=\log n$ sufficiently large, put $L=\log A$,
$T_A=\sqrt A L$ and define

$$
\tau_A=2e/A,\qquad U_A=\max\{C,\tau_A\},\qquad
z_A=\mathbb E U_A^{-1},\qquad \eta_A=\operatorname{Law}(z_AU_A).
\tag{IPX2}
$$

With $M_{-4}=\mathbb EC^{-4}<\infty$,

$$
0\le1-z_A\le\mathbb E[C^{-1};C<\tau_A]
\le\tau_A^3M_{-4}=O(A^{-3}).
$$

Hence $z_A\ge1/2$ eventually. The source $\eta_A$ is positive, has
mass one, support $c\ge e/A$, and inverse moment exactly one. All
fixed real and weighted logarithmic moments are uniformly bounded.
In particular

$$
\int c^{-1/2}d\eta_A=b_++O(A^{-3}),\qquad
\int\log c\,d\eta_A=a_++O(A^{-3}).
\tag{IPX3}
$$

For the first error use
$\mathbb E[C^{-1/2};C<\tau_A]\le\tau_A^{7/2}M_{-4}$.
For the second, integrate
$\mathbb P(C<u)\le M_{-4}u^4$ over $0<u<\tau_A$ to bound
$\mathbb E[\log(\tau_A/C);C<\tau_A]$ by
$M_{-4}\tau_A^4/4$. The scale change $\log z_A=O(A^{-3})$
accounts for the remaining error. No negative correction atom is used.

## Keep the actual price observer and its full tail

Retain exactly KTO5's kernel $\kappa_{A,c}$, price
$\lambda(x)=1/(x\log x)$, weight $K=-\lambda'$ and benchmark
$B(x)=\gamma+\log\log x-1/\log x$. Define

$$
\omega_A(E)=\int\kappa_{A,c}(E)\,d\eta_A(c).
\tag{IPX4}
$$

KTO6--KTO8 and the uniform moments above give absolute kernel Fubini,
finite variation, and the exact identities

$$
\int d\omega_A=1,\qquad
\int\lambda(Av)d\omega_A=\lambda(A),\qquad
\int B(Av)d\omega_A=B(A).
\tag{IPX5}
$$

These use the inverse moment, not $\mathbb EC=1$.
The positive source does not make $\omega_A$ positive: KTO's
$c>1$ kernel still has its negative infinite density tail.

The unclamped law of $z_AC$ has Mellin transform
$z_A^{s-1}2\xi(s)$, so it retains all actual zero cancellations.
Apply the full-response proof GPC5--GPC6 to this law; its needed
moments are uniformly bounded for $1/2\le z_A\le1$.
On $c\ge A^{-1/2}$ the clamp is inactive, and the integrated explicit
formula therefore has only the omitted small-source zero remainder,
of normalized size $O(A^{-1})$. The entire $c<A^{-1/2}$ response
costs $O(LA^{-3/2})$ by GPC6, for both the unclamped law and $\eta_A$.
The absolute constant and trivial-zero cost is $O(A^{-1/2})$.
Consequently the unchanged full response $J_c^\psi$ satisfies

$$
T_A\left|\int J_c^\psi(A)d\eta_A(c)\right|=O(A^{-1/2}),\qquad
T_A\left|\int I_\psi(Av)d\omega_A(v)\right|=O(A^{-1/2}).
\tag{IPX6}
$$

The second equality uses KTO7's exact transported response. Every zero,
small clock, elementary correction and infinite kernel tail is retained.
Mellin cancellation is assigned to the unclamped source, not to $\omega_A$.

## Every occupied layer has an exact nonnegative observation

For any actual exponent layer, write
$r=r_{p,j}=\log(1+1/(p+\cdots+p^j))/\log p>0$, and let $t>1$
be the unique solution of $\lambda(t)=r$. The actual occupied cost is
$\log p\,(\lambda(Av)-r)_+$.
For every $c\ge e/A$, finite Stieltjes integration by parts in KTO5
gives

$$
\int(\lambda(Av)-r)_+d\kappa_{A,c}(v)
=\frac{\lambda(A)-\lambda(\max\{A,t/c\})}{c}\ge0.
\tag{IPX7}
$$

If $t\le Ac$, the integrand is zero on the whole kernel support and
both sides are zero. Otherwise its support ends at $v=t/A$;
the upper boundary value is zero, while the cumulative kernel is
$c^{-2}K(Av/c)/K(Av)$. Multiplication by
$-d\lambda(Av)=AK(Av)dv$ leaves
$c^{-1}\int_A^{t/c}K(u)du$, which proves the formula including its
lower atom. This also covers $t<e$, when the first zero case applies.

Positivity of $\eta_A$ transports this sign exactly. If $a_p=v_p(n)$,
summing all occupied layers of the same original integer yields

$$
0\le O_A(n):=\sum_p\sum_{j\le a_p}\log p
 \int(\lambda(Av)-r_{p,j})_+d\omega_A(v)
\le\lambda(A)\sum_pa_p\log p=\frac1L.
\tag{IPX8}
$$

The upper bound uses IPX7 and the exact inverse moment. There is no
factor counting divisors or exponent layers, no CA replacement, and
no discarded correction error. The statement is uniform for every
original integer at its own $A$. Negative observed contributions can
only enter through unoccupied layers. Dropping positive occupied terms
is a valid lower-bound step, but need not preserve the cancellation
needed at the root scale.
