---
bibkey: bianepitmanyor1999xiprice
authors: Philippe Biane, Jim Pitman, Marc Yor
year: 1999
title: Probability laws related to the Jacobi theta and Riemann zeta functions, and Brownian excursions
doi: null
url: https://arxiv.org/abs/math/9912170v1
claim: The classical positive xi law admits positive inverse-moment calibration for the Robin price observer. Occupied layers have nonnegative cost, and absent-layer responses have a unique asymptotic sign boundary determined by an exact theta budget; the full signed Robin comparison remains unpaid.
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
[HCB3](../Analytic/polak2026finiterobinca.md#actual-strict-ca-sources-have-a-root-small-own-price-higher-baseline)
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


## An exact theta budget for the absent-layer sign

The same positive source admits a more precise absent-layer analysis.
Reuse GP's already owned weight $w_c(t)=c^{-1}\lambda(\max\{A,t/c\})$
in the [Nicolas card](../ArithSums/nicolas2025comparison.md#a-directed-prime-weight-comparison-for-the-complete-gamma-response).
Its complete response, the mass/price identities and IPX7 are inputs,
not new formulas to reprove. The additional classical input is BPY,
Proposition 1(ii), equation (23), printed p.7. The estimates below
control the cap residual for IPX2's broad positive source; GP2's
ordinary-mean-one hypothesis does not hold for this source.

Fix $A$ sufficiently large. Write $C_A$ for a variable of law $\eta_A$,
$X=\log C_A$, $a_A=\mathbb EX=a_++O(A^{-3})>0$, and
$M_{2,A}=\mathbb EX^2=O(1)$. For an actual absent layer with
$\lambda(t)=r_{p,j}$, its full observed hinge is

$$
\mathcal H_A(t)
=\int(r_{p,j}-\lambda(Av))_+d\omega_A(v)
=\lambda(t)-\mathbb E\frac{\lambda(\max\{A,t/C_A\})}{C_A}.
\tag{IPX16}
$$

The second equality follows from IPX7 and the exact mass and price
identities, using $(r-q)_+-(q-r)_+=r-q$. It retains the lower atom and the entire signed
kernel tail. It is also the negative of GP's existing weight difference
for $t\ge A$, rather than a new smoothing kernel.

For $t=AB\ge A$ set $s=\log B$, $v=L+s$, and define

$$
\mathcal S_A(B)=\mathbb E(1-B/C_A)_+,\qquad
\mathcal P_A(s)=\mathbb P(X\ge s),\qquad
\mathcal T_A(s)=\mathbb E(X-s)_+.
\tag{IPX17}
$$

Split the expectation in IPX16 at $C_A=B$. On $X<s$ use the exact
identity
$(v-X)^{-1}=v^{-1}+Xv^{-2}+X^2/[v^2(v-X)]$.
The resulting cap account is

$$
\begin{aligned}
v^2t\mathcal H_A(t)
={}&\frac{v^2}{L}\mathcal S_A(B)-a_A+\mathcal T_A(s)\\
&-\frac{s^2}{L}\mathcal P_A(s)
 -\mathbb E\!\left[\frac{X^2}{v-X};X<s\right].
\end{aligned}
\tag{IPX18}
$$

Here $v-X\ge L$ on the last event, and
$s^2\mathcal P_A(s)\le M_{2,A}$. Since $s\ge0$ and $a_A>0$,
multiplying by $L^2/v^2$ gives the uniform lower bound; dropping the
last two nonpositive terms gives the upper bound:

$$
\begin{aligned}
L^2t\mathcal H_A(t)&\ge
 L\mathcal S_A(B)-a_A-\frac{2M_{2,A}}L,\\
v^2t\mathcal H_A(t)&\le
 \frac{v^2}{L}\mathcal S_A(B)-a_A+\mathcal T_A(s).
\end{aligned}
\tag{IPX19}
$$

These bounds apply to every $B\ge1$. No term involving the cap or
source tail has been treated as a root-small prime error.

Put $C_0=1/Y$. BPY's cited equation gives for every $u>0$

$$
\mathbb P(C_0>u)=4\pi u^3\sum_{n\ge1}n^2e^{-\pi n^2u^2}.
$$

Tonelli's theorem therefore evaluates its positive cap budget exactly:

$$
\mathcal S_0(B)
=B\int_B^\infty\frac{\mathbb P(C_0>u)}{u^2}\,du
=2B\sum_{n\ge1}e^{-\pi n^2B^2},\qquad
\mathcal S_A(B)=\mathcal S_0(B/z_A)\quad(B\ge1).
\tag{IPX20}
$$

The last equality is exact: for sufficiently large $A$,
$z_A\tau_A<1$, so the positive part in IPX17 vanishes on the entire
clamped part of the source. Scaling the surviving upper source by
$z_A$ is the only change. No estimate for a newly truncated law is
being substituted for $\eta_A$.

For $u=B/z_A\ge1$, differentiation of the absolutely convergent
positive series yields

$$
\begin{aligned}
\frac d{ds}\mathcal S_A(e^s)
 &=\mathcal S_A(e^s)-\mathcal P_A(s)
 \le(1-2\pi u^2)\mathcal S_A(e^s)<0,\\
\mathcal T_A(s)
 &=\mathcal S_A(e^s)+\int_s^\infty\mathcal S_A(e^w)\,dw
 \le\left(1+\frac1{2\pi-1}\right)\mathcal S_A(e^s).
\end{aligned}
\tag{IPX21}
$$

Thus IPX19 has an explicit decreasing theta budget, with a uniformly
controlled logarithmic tail. The statement concerns the full absent
response of the fixed source, rather than positivity of $\omega_A$.


## A unique absent-layer sign boundary and its scale

There is, for every sufficiently large $A$, exactly one $t_*(A)>A$
where IPX16 vanishes. Its position is determined by the actual
calibrated source:

$$
\boxed{\quad
\pi\left(\frac{t_*(A)}{Az_A}\right)^2
=\log L+\frac12\log\log L
 +\log\frac{2}{a_+\sqrt\pi}+o(1),\qquad
 t_*(A)\sim A\sqrt{\frac{\log\log A}{\pi}}.\quad}
\tag{IPX22}
$$

The statement is asymptotic: no certified numerical starting $A$ is
specified. All source parameters remain those of IPX2; a new source
is not chosen as $t$ varies.

To prove existence and locate every possible zero, define $B_-,B_+>1$
by

$$
L\mathcal S_A(B_-)=2a_A,\qquad
L\mathcal S_A(B_+)=a_A/2.
$$

For large $A$ these unique numbers exist by IPX20--IPX21. The first
term of the positive theta series, with its exponentially smaller
remaining terms, gives for both endpoints

$$
\pi(B_\pm/z_A)^2
=\log L+\tfrac12\log\log L+O(1).
\tag{IPX23}
$$

IPX19's lower bound proves $\mathcal H_A(AB)>0$ for every
$1\le B\le B_-$. For $B\ge1$ and $L>2$, the upper-bound supplier

$$
\frac{(L+\log B)^2}{L}\mathcal S_A(B)
 +\mathcal T_A(\log B)
$$

strictly decreases: IPX21 bounds the logarithmic derivative of its
first positive term by $2/(L+\log B)+1-2\pi(B/z_A)^2<0$, and the
second term decreases. At $B_+$ this supplier is
$a_A/2+o(1)<a_A$. IPX19 therefore proves
$\mathcal H_A(AB)<0$ for every $B\ge B_+$, including arbitrarily
large $B$. Every zero is confined to $[AB_-,AB_+]$; no uncontrolled
outer region remains.

For uniqueness, differentiate at fixed $A$ and put
$Q_A(s)=L^2Ae^s\mathcal H_A(Ae^s)$. The only source atom is below
$C_A=1$, so the BPY density makes this differentiation valid for
$s\ge0$. Differentiating the two cap pieces cancels their boundary
terms and gives

$$
\begin{aligned}
Q_A'(s)={}&L\frac d{ds}\mathcal S_A(e^s)\\
&+L^2\left[-\frac1{v^2}
 +\mathbb E\!\left[\frac1{(v-X)^2};X<s\right]\right],\\
\left|L^2\left[-\frac1{v^2}
 +\mathbb E\!\left[\frac1{(v-X)^2};X<s\right]\right]\right|
&\le\mathcal P_A(s)+\frac{2\mathbb E|X|}{L}.
\end{aligned}
\tag{IPX24}
$$

For the last bound, subtract $v^{-2}$ inside the expectation on
$X<s$ and apply the mean value theorem; both denominators are at
least $L$. The omitted probability contributes at most
$\mathcal P_A(s)$.
On $B_-\le e^s\le B_+$, IPX20 gives
$\mathcal P_A(s)=O((\log L)/L)$, while IPX21 and IPX23 give
$L\,d\mathcal S_A(e^s)/ds\le-c\log L$ for some fixed $c>0$.
Thus $Q_A'<0$ throughout this whole band for sufficiently large $A$.
Continuity and the endpoint signs yield exactly one zero.

At the zero, IPX18, IPX21, bounded $M_{2,A}$ and IPX23 imply
$L\mathcal S_A(t_*/A)=a_A+o(1)$. Write $u=t_*/(Az_A)$.
Using $\mathcal S_A(t_*/A)=2u e^{-\pi u^2}
(1+O(e^{-3\pi u^2}))$ and $a_A\to a_+>0$, taking logarithms
first gives $u^2\sim(\log L)/\pi$ and then IPX22, including its
constant $\log(2/(a_+\sqrt\pi))$.

For $1<t<A$, IPX7 gives
$\mathcal H_A(t)\ge\lambda(t)-\lambda(A)>0$.
At $t=A$, every source value except $C_A=1$ has
$C_A^{-1}\lambda(\max\{A,A/C_A\})<\lambda(A)$, so
nondegeneracy gives strict positivity there as well. The complete
single-layer classification is consequently

$$
\mathcal H_A(t)>0\ (1<t<t_*),\qquad
\mathcal H_A(t_*)=0,\qquad
\mathcal H_A(t)<0\ (t>t_*).
\tag{IPX25}
$$

This locates the actual absent-layer sign; it does not assert that
all actual primes are present below that boundary. For first layers,
$\lambda(t_p)=r_{p,1}$ satisfies $p<t_p<p+1$: use
$1/(p+1)<\log(1+1/p)<1/p$ and monotonicity of $\lambda$.
Thus an absent first prime $p\le t_*-1$ has positive response and an
absent first prime $p\ge t_*$ has negative response. IPX7 separately
keeps every occupied response nonnegative. Negative observed terms
can therefore occur only in absent layers whose actual activation
threshold exceeds $t_*$.

The unique boundary improves the sign description, rather than the
proved complete Robin margin. The positive and negative prime sums
still use the same source and actual integer; neither may be omitted
from IPX11. In particular the negative far contribution in IPX13 is
still present, and no root-small replacement for its exact prime sum
has been supplied. A sign boundary at $A\sqrt{\log\log A/\pi}$
does not make the full comparison error root-small. The quantitative
joint arithmetic estimate, strict Robin above 5040 and RH remain
unproved. These are paper-level applications of the cited BPY tail
and the existing full kernel response, with no Lean certification or
literature-priority claim.


## The complete negative first-prime mass at the natural sign boundary

IPX22--IPX25 locate the negative responses. Their complete size can
also be estimated on the actual prime set. The inputs are GP's owned
absolute-weight Fubini and primitive, the unconditional Chebyshev and
effective PNT bounds already used in JPT and ACC, and the unchanged
calibrated source. No new prime-counting theorem or qualitative
cancellation mechanism is used.

Keep $A$ sufficiently large and put
$B_*=t_*/A$, $s_*=\log B_*$, $v_*=\log t_*$ and
$u_*=B_*/z_A$. In addition to $a_A$ and $M_{2,A}$, use the uniform
third absolute logarithmic moment $M_{3,A}=\mathbb E|X|^3=O(1)$.
For every actual first-prime activation $\lambda(t_p)=r_{p,1}$ define

$$
g_A(t)=(-\mathcal H_A(t))_+,\qquad
\mathfrak N_A=\sum_p\log p\,g_A(t_p),\qquad
\mathfrak n_A=\int_{t_*}^\infty g_A(t)\,dt.
\tag{IPX26}
$$

The sum uses every actual prime, not a prime-density model.
For an integer $n$, its actual negative first-layer part includes only
$p\nmid n$, so it is bounded by $\mathfrak N_A$. Equality requires
that all primes with $t_p>t_*$ be absent; it is not assumed for an
arbitrary integer. The continuous quantity $\mathfrak n_A$ is only
an intermediate comparison.

For $B\ge1$, write $s=\log B$, $v=L+s$. GP's absolute convergence
permits the full-source primitive

$$
J_A(B):=\int_{AB}^\infty\mathcal H_A(t)\,dt
=\mathbb E\log\!\left(1-\frac{\min(X,s)}v\right)
 -\frac{\mathcal S_A(B)}L.
\tag{IPX27}
$$

For a source value $X<s$, the primitive is $\log(1-X/v)$.
For $X\ge s$, it is $\log(L/v)-(1-e^{s-X})/L$.
Thus IPX27 includes the entire capped source, rather than extending
the reciprocal logarithm across its pole. It uses absolutely
convergent differences, with no subtraction of two divergent
$\lambda$ integrals. By IPX25, $\mathfrak n_A=-J_A(B_*)$.

Write $S=\mathcal S_A(B_*)$ and

$$
R_1=\int_{s_*}^\infty\mathcal S_A(e^w)\,dw,\qquad
R_2=\int_{s_*}^\infty\mathcal T_A(w)\,dw,\qquad
k_*=2\pi u_*^2-1\asymp\log L.
$$

IPX21 gives
$R_1\le S/k_*$,
$\mathcal T_A(s_*)=S+R_1$ and
$R_2\le(1+1/k_*)S/k_*$.
For $Y=\min(X,s_*)$ the first two moments are exactly

$$
\mathbb EY=a_A-\mathcal T_A(s_*),\qquad
\mathbb EY^2=M_{2,A}-2s_*\mathcal T_A(s_*)-2R_2.
$$

Taylor expansion in IPX27 therefore yields

$$
\begin{aligned}
J_A(B_*)={}&-\frac{a_A}{v_*}-\frac{M_{2,A}}{2v_*^2}
 +\frac{R_1}{v_*}+\frac{s_*R_1}{v_*^2}
 +\frac{R_2}{v_*^2}-\frac{s_*^2S}{Lv_*^2}
 +O(L^{-3}),\\
\mathfrak n_A={}&\frac{a_A}{v_*}
 +\frac{M_{2,A}}{2v_*^2}
 +O\!\left(\frac1{L^2\log L}\right).
\end{aligned}
\tag{IPX28}
$$

The expansion does not require $|X|<v_*$. For the unbounded negative
part use
$|\log(1+z)-z+z^2/2|\le z^3/3$ for $z\ge0$; for the positive
part, $Y\le s_*=o(v_*)$ gives the same third-moment allowance.
The second-order cap terms are retained: their cancellation uses
$S/v_*+s_*S/v_*^2-S/L=-s_*^2S/(Lv_*^2)$.
Finally $S=O(1/L)$, $s_*=O(\log\log L)$ and the bounds on $R_1,R_2$
make all remaining boundary terms
$O(1/(L^2\log L))$.

For the literal activations, differentiate IPX16 at fixed $A$:

$$
\mathcal H_A'(t)=-K(t)
 +\mathbb E[C_A^{-2}K(t/C_A);C_A<t/A].
$$

On $t\ge t_*$ the last kernel has $\log(t/C_A)\ge L$, so
$|g_A'(t)|\le C/(t^2L)$ almost everywhere, with $g_A(t_*)=0$.
Below $t_*$, $g_A$ is zero. The already owned bracket
$p<t_p<p+1$ and the Chebyshev bound consequently give

$$
\begin{aligned}
\left|\sum_p\log p\,[g_A(t_p)-g_A(p)]\right|
&\le\frac C L\sum_{p>t_*-1}\frac{\log p}{p^2}
 =O\!\left(\frac1{t_*L}\right),\\
T_A\left|\sum_p\log p\,[g_A(t_p)-g_A(p)]\right|&=o(1).
\end{aligned}
\tag{IPX29}
$$

There is no factor counting primes, divisors or exponent layers.
This activation shift is controlled at the root scale.

Retain the exact primary-prime quadrature error

$$
\mathfrak E_A
=\int_{t_*}^\infty g_A(t)\,d(\vartheta(t)-t)
=-\int_{t_*}^\infty(\vartheta(t)-t)g_A'(t)\,dt.
\tag{IPX30}
$$

The boundary terms vanish. The same effective PNT supplier used in
ACC gives $|\vartheta(t)-t|\le Ct e^{-d\sqrt{\log t}}$
for a fixed $d>0$ and all sufficiently large $t$. Hence

$$
|\mathfrak E_A|
\le\frac C L\int_{\log t_*}^\infty e^{-d\sqrt u}\,du
=O\!\left(\frac{e^{-d\sqrt L}}{\sqrt L}\right).
\tag{IPX31}
$$

This allowance is smaller than every fixed negative power of $L$.
It is insufficient to guarantee a root-small actual quadrature error;
the exact $\mathfrak E_A$ remains available when that precision is
required.

Combining IPX28--IPX31 gives the full literal-prime expansion

$$
\boxed{\quad
\mathfrak N_A
=\frac{a_A}{v_*}+\frac{M_{2,A}}{2v_*^2}
 +O\!\left(\frac1{L^2\log L}\right)
\sim\frac{a_+}{L}.\quad}
\tag{IPX32}
$$

In particular this includes all negative first-prime responses from
the natural boundary onward, rather than just IPX13's artificial
$p>A^{16}$ tail. The continuous integral is used only with its paid
literal activation and prime-quadrature errors. No improvement of
the underlying PNT is asserted.

For the same original integer $n$, let $h_{p,A}(n)$ be the observed
first-layer response before multiplication by $\log p$: it is IPX7's
nonnegative expectation when $p\mid n$ and
$\mathcal H_A(t_p)$ when $p\nmid n$. Define its complete positive
and negative first-layer parts by

$$
\mathfrak P_A(n)=\sum_p\log p\,(h_{p,A}(n))_+,\qquad
\mathfrak N_A(n)=\sum_{p\nmid n}\log p\,g_A(t_p).
$$

The owned absolute convergence gives
$D_{1,A}(n)=\mathfrak P_A(n)-\mathfrak N_A(n)$ and
$\mathfrak N_A(n)\le\mathfrak N_A$.
Reuse [ACC3--ACC5's actual strict products](../ArithSums/nicolas2025comparison.md#use-actual-strict-products-at-their-own-size)
$N_x$, with $A=\log N_x\sim x$. Every prime factor lies below $x$,
whereas $t_*/x\to\infty$. Thus eventually all negative first primes
are absent from this same $N_x$, and
$\mathfrak N_A(N_x)=\mathfrak N_A$ exactly.

ACC5 also gives $0\le G_{2,A}(N_x)\le d_A(N_x)$ and
$d_A(N_x)=O(e^{-d\sqrt L}/L)$ for some $d>0$.
Use the unchanged exact account
$\Delta(N_x)=d_A(N_x)+I_\psi(A)+R(A)$, IPX11 and the owned
$R(A)=c_R/T_A+O(1/(T_AL))$. They give

$$
\begin{aligned}
D_{1,A}(N_x)
&=d_A(N_x)-G_{2,A}(N_x)+I_\psi(A)
  -\frac{2(1-b_+)}{T_A}+O\!\left(\frac1{T_AL}\right)\\
&=O(e^{-d_1\sqrt L})+O(T_A^{-1})
 =o(L^{-m})\qquad\text{for every fixed }m>0,
\end{aligned}
$$

for a fixed $d_1>0$, by the same effective PNT input as ACC2.
Consequently on these actual integers,

$$
\mathfrak P_A(N_x)
=\frac{a_A}{v_*}+\frac{M_{2,A}}{2v_*^2}
 +O\!\left(\frac1{L^2\log L}\right),\qquad
\frac{\mathfrak P_A(N_x)}{\mathfrak N_A(N_x)}\longrightarrow1.
\tag{IPX33}
$$

Both parts use the same integer, source and literal prime set. This
quantifies the full sign split at the natural boundary; ACC already
owns the actual-integer qualitative compensation mechanism.

The surviving sufficient estimate for IPX11 is, for some fixed
$\epsilon>0$ and every sufficiently large original integer $n$,

$$
T_A[\mathfrak P_A(n)-\mathfrak N_A(n)+G_{2,A}(n)]
\ge -c_++\epsilon,\qquad c_+=c_R+2(1-b_+).
\tag{IPX34}
$$

It would imply eventual strict Robin; a complete proof above 5040
would also have to cover the remaining integers. On the actual
family in IPX33 the residual scale $T_A^{-1}$ is of relative order
$A^{-1/2}$ compared with either sign part $\sim a_+/L$.
The logarithmic remainder in IPX32--IPX33 and the unconditional
prime-quadrature allowance do not supply that one-sided precision.
A larger positive residual is favorable: no two-sided smallness of
the actual difference is required or claimed. The joint bound
IPX34, a certified numerical starting scale, full strict Robin and
RH remain unproved. IPX26--IPX33 are paper-level applications of
the cited source and existing arithmetic estimates, without Lean
certification or a literature-priority claim.

## The complete first-layer response has a sharp conditional root benchmark

IPX33's actual first-layer account also has a root-scale consumer.
The inputs are the already owned complete signed explicit formula,
NPC1's two-price benefit bound, and classical simultaneous phase
recurrence. No new Ramanujan theorem, zero-distribution estimate or
recurrence principle is introduced. Keep exactly the IPX source and
observer, and the actual strict products $N_x$ of ACC, with
$A=A_x=\log N_x$, $L=\log A$ and $T_A=\sqrt A L$.

The classical xi logarithmic-derivative identity, already used in
[GE1](../ArithSums/nicolas2025comparison.md#an-explicit-one-sided-bound-for-the-combined-gamma-remainder),
and differentiation of IPX1's Mellin identity give

$$
c_0=2+\gamma-\log(4\pi)=2a_+,\qquad
\kappa_\xi=c_0+2(1-b_+)>0.
\tag{IPX35}
$$

Indeed $a_+=-2\xi'(0)=2\xi'(1)$ and $\xi(1)=1/2$;
the classical zero weight is $2\xi'(1)/\xi(1)$.
The positivity also follows directly from IPX1's strict Jensen
inequalities. This connects existing constants; it is not a new
identity for the zeta zeros.

**Assume RH throughout the following conditional calculation.**
The classical estimate $\vartheta(x)-x=O(\sqrt x\log^2x)$,
ACC's literal first-layer bracket and its complete higher inventory
give $A_x-x=O(\sqrt x\log^2x)$. In NPC1,
$h=O(\log^2x/\sqrt x)$, so
$T_Ad_A(N_x)\to0$. Since $0\le G_{2,A}(N_x)\le d_A(N_x)$,
the same holds for its higher baseline. These facts apply to every
large real price $x$, including strict endpoint conventions; no
own-price equality $A_x=x$ is assumed.

Reuse [the complete signed formula](../ArithSums/nicolas2025comparison.md#the-2026-signed-formula-and-the-available-absolute-error-scale),
Broadbent--Fiori--Kadiri--Ng--Wilk, Proposition 13(i), as recorded
there. Under RH its normalized form and IPX33's existing account give

$$
\begin{aligned}
T_AI_\psi(A)&=-\mathcal B(\log A)+O(L^{-1}),\\
\mathcal B(y)&=2\sum_{\tau>0}
       \frac{\cos(\tau y)}{1/4+\tau^2},\\
T_AD_{1,A}(N_x)&=-\mathcal B(\log A_x)-2(1-b_+)+o(1).
\end{aligned}
\tag{IPX36}
$$

Here $\tau$ runs over all positive nontrivial-zero ordinates with
their multiplicities. No infinite-height tail is omitted. The leading
factor of the exact formula is $1+1/L$; its complete integral
remainder is $O(L^{-1})$ after normalization, by the convergent
weight $\sum_\rho1/(|\rho||1-\rho|)$. The constant and trivial-zero
corrections are root-small. On RH this weight is $c_0$, and the
cosine series is absolutely and uniformly convergent.

Its coefficients are positive, so $\mathcal B(y)\le\mathcal B(0)=c_0$.
For any positive error tolerance, retain a finite head with smaller
absolute tail. The classical simultaneous approximation theorem,
as in [the existing Kronecker source](../Fourier/onishchik2020kronecker.md),
returns arbitrarily large $y$ for which every head phase is arbitrarily
close to one. This uses recurrence toward the identity, not density
in the whole phase torus or rational independence of zero ordinates.
The paid tail then gives $\limsup_{y\to\infty}\mathcal B(y)=c_0$.

Set $x=e^y$ and retain its same strict integer $N_x$. Since
$\log A_x-\log x\to0$, uniform continuity of this series transports
the recurrence to $\log A_x$. The step-valued inventory therefore
does not change the extremum. IPX36 yields the sharp conditional
benchmark

$$
\boxed{\quad
\mathrm{RH}\ \Longrightarrow\
\liminf_{x\to\infty}
 T_{A_x}D_{1,A_x}(N_x)=-\kappa_\xi<0.
\quad}
\tag{IPX37}
$$

This is a paper-level application at the specified observed first layer.
The RH premise remains essential to its lower bound and sharp value;
it is not an unconditional estimate for IPX34 or a Lean certification.

## Actual negative first-layer responses persist without an RH premise

For the complementary case reuse
[the existing actual regular-source family S5](../Arith/caveney2012sacaga.md#retain-the-original-oscillation-exponent-on-the-regular-ga1-source).
If RH fails, it supplies an unbounded family of actual event-free
own-price integers $N$, $A=\log N$, with
$G(N)>e^\gamma(1+c_\eta A^{-\eta})$ for fixed
$c_\eta>0$ and $0<\eta<1/2$. The source's already retained
prime-local bridge gives the strict identity $N=N_A$; there is no
new replacement of tied endpoints or separately chosen integer.
On this same family,

$$
T_A\Delta(N)
\le-\frac{c_\eta}{2}A^{1/2-\eta}L\longrightarrow-\infty.
$$

IPX11 and $G_{2,A}(N)\ge0$ then give
$T_AD_{1,A}(N)\le T_A\Delta(N)-c_++O(L^{-1})\to-\infty$.
Together with IPX37 this establishes the paper-level dichotomy

$$
\liminf_{x\to\infty}T_{A_x}D_{1,A_x}(N_x)=
\begin{cases}
-\kappa_\xi,&\text{if RH holds},\\
-\infty,&\text{if RH fails}.
\end{cases}
\tag{IPX38}
$$

In particular, without assuming either answer to RH,
$\liminf_{x\to\infty}T_{A_x}D_{1,A_x}(N_x)\le-\kappa_\xi<0$.
Thus on an unbounded family of these actual strict CA integers,

$$
T_A[\mathfrak N_A(N_x)-\mathfrak P_A(N_x)]
>\kappa_\xi/2.
\tag{IPX39}
$$

This rules out eventual nonnegativity of the **complete** observed
first layer on the actual CA family. It does not follow merely from
IPX13's negative far tail: here the occupied and positive absent
responses have also been retained. In particular IPX33's ratio tending
to one coexists with an actual negative difference at the root scale.

The sufficient target IPX34 remains a lower bound for the complete
joint account, and has not been proved. It allows the negative values
above: the constant gap $c_+-\kappa_\xi=c_R-c_0>0$ is the classical
RH-conditional Ramanujan margin in this logarithmic normalization, as in
[the existing Ramanujan source](../Analytic/musin2020strongramanujan.md#the-positive-margin-already-assumes-rh),
rather than an extra unconditional reserve created by this observer.
IPX38 is a quantitative consumer for the specified source, not a new
RH criterion or a proof of either branch's premise. No numerical
starting threshold, stronger unconditional Robin bound, mathematical
priority or Lean certification is claimed.
