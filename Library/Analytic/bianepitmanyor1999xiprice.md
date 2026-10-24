---
bibkey: bianepitmanyor1999xiprice
authors: Philippe Biane, Jim Pitman, Marc Yor
year: 1999
title: Probability laws related to the Jacobi theta and Riemann zeta functions, and Brownian excursions
doi: null
url: https://arxiv.org/abs/math/9912170v1
claim: The classical positive xi law admits positive inverse-moment calibration for the Robin price observer. Every occupied exponent layer then has nonnegative observed cost, and the complete higher-layer cost is eventually positive; the negative far-prime tail and the full signed Robin comparison remain unpaid.
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
Its ordinary mean is $m+O(A^{-3})$, retaining a different normalization
from the earlier mean-one source. In particular

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

## Retain the complete higher layers and the original integer

Use HLD1--HLD4's actual higher pressure and tail $F_2$, and KTO1's
actual reserve $R$, without changing any exponent cutoff. Both have
the owned quantitative form $c/(\sqrt x\log x)+O(1/(\sqrt x\log^2x))$
and are bounded on $[e,\infty)$. KTO9--KTO10's root-tail argument,
now with IPX3's bounded fixed moments, gives

$$
\begin{aligned}
T_A\int R(Av)d\omega_A(v)&=c_Rb_++O(L^{-1}),
 &c_R&=2(\sqrt2-1),\\
T_A\int F_2(Av)d\omega_A(v)&=2\sqrt2b_++O(L^{-1}).
\end{aligned}
\tag{IPX9}
$$

Its small-clock bound and the complete later kernel support are the
same as KTO's. No positive-power moment is assigned to $\omega_A$.
Let $G_{2,A}(n)=d_2(n,\lambda(A))\ge0$ be the unchanged original
higher-layer baseline, and $D_{2,A}(n)$ its observed complete defect.
Exact mass and price, as in HLD7--HLD8, therefore give

$$
T_AD_{2,A}(n)=T_AG_{2,A}(n)+2\sqrt2(1-b_+)+O(L^{-1}).
\tag{IPX10}
$$

Thus the actual complete higher-layer cost is eventually positive,
uniformly for all original integers. On the actual strict CA family,
[HCB3](polak2026finiterobinca.md#actual-strict-ca-sources-have-a-root-small-own-price-higher-baseline)
makes its normalized limit exactly $2\sqrt2(1-b_+)>0$.
This differs from HCB4's negative limit under its other, unchanged source.

Let $D_{1,A}(n)$ be the complete observed first-layer defect for this
$\omega_A$, with both occupied and absent primes retained. The same
exact pressure account KTO12, IPX6 and IPX9--IPX10 yield

$$
\boxed{\quad
T_A\Delta(n)=T_A[D_{1,A}(n)+G_{2,A}(n)]
+c_R+2(1-b_+)+O(L^{-1}).\quad}
\tag{IPX11}
$$

Here $\Delta(n)=\gamma+\log\log\log n-\log(\sigma(n)/n)$.
The new constant exceeds $c_R$, but it is paired with a different
first-layer account. IPX11 is not a stronger proved Robin margin.

## The same positive source produces a negative actual far tail

Keep $P=A^{16}$, $Z=\log P=16L$, and define the exact actual-prime tail

$$
\mathscr U_A=\int\sum_{p>P}\log p\,(r_{p,1}-\lambda(Av))_+
                          d\omega_A(v).
\tag{IPX12}
$$

The full-pressure majorant in JPT3 applies because $\eta_A$ has
uniform fixed moments. It proves absolute kernel/source Fubini and
absolute interchange of the entire prime sum. Restricting the source
to $A^{-1/2}\le c\le A^8$ costs $O(A^{-1}(1+\log L))$, by JPT4.
For these clocks every far-prime atom sees zero hinge. Reuse JPT5's
exact response, with $\lambda(t_p)=r_{p,1}$:

$$
\int(r_{p,1}-\lambda(Av))_+d\kappa_{A,c}(v)
=-\frac{\log c}{t_p\log t_p\log(t_p/c)}.
$$

JPT6's complete prime-tail calculation, including $t_p=p+O(1)$ and
the effective unconditional PNT error, gives on that source interval

$$
\int\sum_{p>P}\log p\,(r_{p,1}-\lambda(Av))_+
                      d\kappa_{A,c}(v)
=\log(1-\log c/Z)
 +O\!\left(|\log c|e^{-d\sqrt Z}
           +\frac{|\log c|}{P\log P}\right)
$$

for a fixed $d>0$. Since $|\log c|/Z\le1/2$, the Taylor remainder
is bounded by $C(\log c)^2/Z^2$. IPX3 and the uniform second logarithmic
moment, with the same source-tail bounds, consequently give

$$
\boxed{\quad\mathscr U_A=-\frac{a_+}{16L}+O(L^{-2})<0
\quad\text{eventually}.\quad}
\tag{IPX13}
$$

The comparison error here is not root-small; it determines the tail's
sign and size, rather than replacing its exact value in IPX11.
Exact mass and price keep the same original integer's entire far account:

$$
D_{\mathrm{far},A}(n)=\mathscr U_A+
 \sum_{\substack{p>P\\p\mid n}}(\lambda(A)-r_{p,1})\log p.
\tag{IPX14}
$$

Each occupied-prime correction is nonnegative. For an actual strict
CA integer $N_x$, $A\sim x$ and every prime factor is less than $x$;
therefore this correction is zero eventually. IPX13 is then a negative
observed far defect on actual integers, although its integrand and
its source $\eta_A$ are nonnegative. The sign is introduced by the
transport kernel, not by an invented arithmetic model.

At any actual own-price zero-defect source, $G_{2,A}=0$.
Combining the original exact
$\Delta(n)=I_\psi(A)+R(A)$ with IPX11 gives

$$
T_AD_{1,A}(n)=T_AI_\psi(A)-2(1-b_+)+O(L^{-1}).
\tag{IPX15}
$$

Thus the apparent constant gain is compensated in the same first-layer
account. The sign interface in IPX7--IPX8 locates negative observations
in unoccupied layers, and IPX10 pays the complete higher sector, but
neither supplies a sufficient lower bound for the remaining first-prime
account. Its center and exact negative far tail still need a joint
estimate. No improved finite verification range, unbounded Robin bound,
RH proof or new Lean theorem follows from these applications.
