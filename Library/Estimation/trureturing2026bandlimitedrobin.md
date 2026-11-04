---
bibkey: trureturing2026bandlimitedrobin
authors: trureturing research synthesis
year: 2026
title: A truncated Fourier cutoff in the complete finite Robin transport
doi: null
url: https://github.com/the-omega-institute/trureturing/blob/dev/Library/Estimation/trureturing2026bandlimitedrobin.md
claim: A truncated classical Fourier density has positive mean-normalized multiplicative law, variance at most approximately 10/H^2 and complete complex tail response below 10^-26 at H = 3 times 10^12. With the original five analytic premises this pays strict Robin for each integer with 8 times 10^46 < log n <= 17 times 10^47, without an added density or seven-eighths premise. RH remains unproved.
strata_touched: []
license: Apache-2.0
triage: anchor
---

# A positive Fourier cutoff for the complete Robin response

Use the five analytic premises and endpoint conventions in
[GAK section 1](../ArithSums/nicolas2025comparison.md#1-exact-theorem-and-premises),
its complete coefficient GAK10--GAK17, centered transport GAK18--GAK23,
and unrestricted reserve GAK36--GAK39. In particular the verified height
is $H=3\cdot10^{12}$, with no criticality asserted above it.
The Fourier construction below uses classical Plancherel, differentiation
and autocorrelation identities. It is not a new general Fourier or
probability theorem. Its truncation and full complex response are a
project application to the existing consumer. No literature priority,
independent verification of the external analytic premises, or Lean/kernel
certification is claimed.

## A classical positive density with three exact Fourier cancellations

Use the unitary Fourier convention and put

$$
g(v)=\sqrt2\cos(\pi v)\,\mathbf1_{[-1/2,1/2]}(v),\qquad
h(t)=\frac1{\sqrt{2\pi}}\int_{\mathbb R}g(v)e^{itv}\,dv
=\frac{2\sqrt\pi\cos(t/2)}{\pi^2-t^2},\qquad p(t)=|h(t)|^2.
\tag{BFR1}
$$

The apparent singularities at $t=\pm\pi$ are removable. Direct interval
integration gives $\|g\|_2=1$ and $\|g'\|_2^2=\pi^2$.
The endpoints of $g$ vanish, so its weak derivative has no point masses.
Plancherel and its derivative identity therefore give

$$
p\ge0,\qquad p(-t)=p(t),\qquad
\int_{\mathbb R}p(t)\,dt=1,\qquad
\int_{\mathbb R}t^2p(t)\,dt=\pi^2.
$$

The autocorrelation formula gives
$\phi(s)=\int p(t)e^{ist}dt=\int g(v)g(v+s)dv$, supported on $[-1,1]$.
The finite second absolute moment makes $\phi\in C^2(\mathbb R)$.
Consequently, including the endpoints,

$$
\int_{\mathbb R}t^j p(t)e^{ist}\,dt=0
\quad(|s|\ge1,\ j=0,1,2).
\tag{BFR2}
$$

For $|t|\ge2\pi$, the explicit density and $\pi<22/7$ give

$$
p(t)\le\frac{64\pi}{9t^4}<\frac{23}{t^4}.
$$

Set

$$
\varepsilon=\frac1{2000},\qquad R=H\varepsilon,\qquad
\tau_j=\frac{46}{(3-j)R^{3-j}}\quad(j=0,1,2),\qquad
z=\int_{-R}^Rp(t)dt.
\tag{BFR3}
$$

Then $1-\tau_0\le z\le1$ and the removed $j$th absolute moment is
at most $\tau_j$. Since $R>2\pi$, splitting the third moment there gives

$$
\int_{-R}^R|t|^3p(t)dt
\le2\pi^3+46\log\frac R{2\pi}
<2(22/7)^3+46\log R<1100.
\tag{BFR4}
$$

Here $R=1.5\cdot10^9<2^{31}$ and $\log2<7/10$ imply $\log R<22$.
All these moments concern the same density.

## Truncate before constructing multiplicative scales

Let $Y=t/H$ under the conditional density
$z^{-1}p(t)\mathbf1_{[-R,R]}dt$. Define

$$
m=\mathbb Ee^Y,\qquad d=\log m,\qquad C=e^{Y-d},\qquad
v_0=\frac{10}{H^2(1-\tau_0)},\qquad
M_*=(1-2v_0)^{-1},\qquad
V_*=\frac{v_0}{1-2\varepsilon}.
\tag{BFR5}
$$

This is a positive probability law, symmetric in $Y$, with
$\mathbb EY=0$, $\mathbb EY^2\le v_0$ and $|Y|\le\varepsilon$.
Taylor's bound and $e^\varepsilon<2$ give
$1\le m\le1+v_0$, hence $0\le d\le v_0$.
It follows that $|\log C|\le\varepsilon+v_0<1/1000$ and the entire
support is inside $(.99,1.01)$. Its mean and inverse moment are

$$
\mathbb EC=1,\qquad
\mathbb EC^{-1}=m^2\le(1+v_0)^2\le M_*.
$$

Moreover, variance is bounded on this same whole law by

$$
\operatorname{Var}C
=\frac{\operatorname{Var}(e^Y)}{m^2}
\le\mathbb E(e^Y-1)^2
\le e^{2\varepsilon}\mathbb EY^2\le V_*.
\tag{BFR6}
$$

The last bound uses $e^x\le(1-x)^{-1}$ for $0\le x<1$.
All denominators are positive. Truncation is essential: no finite
exponential moment of the untruncated polynomial-tail law is assumed.

## Pay the complete complex tail after truncation and normalization

For $0<\beta<1$, $|\gamma|\ge H$, put $u=\beta-1$ and $s=\gamma/H$.
Expand only the real exponential $e^{ut/H}$ through degree two, keeping
$e^{ist}$ intact. Equation (BFR2) cancels all three full-line terms.
Their removed tails cost $\tau_0+\tau_1/H+\tau_2/(2H^2)$, and (BFR4)
pays the complete Taylor remainder. Thus

$$
\left|\int_{-R}^R p(t)e^{ut/H}e^{ist}dt\right|
\le \tau_0+\frac{\tau_1}H+\frac{\tau_2}{2H^2}
+\frac{1100}{6H^3(1-\varepsilon)}.
$$

The normalization factor is
$|e^{-(u+i\gamma)d}|=e^{-ud}\le e^d\le(1-v_0)^{-1}$.
Dividing by the actual mass $z\ge1-\tau_0$ therefore gives

$$
\begin{aligned}
|\mathbb EC^{\beta-1+i\gamma}|&\le q_*,\\
q_*&=\frac{\tau_0+23/(HR^2)+23/(H^2R)
+1100/[6H^3(1-\varepsilon)]}{(1-\tau_0)(1-v_0)}
<10^{-26}.
\end{aligned}
\tag{BFR7}
$$

The bound covers both ordinate signs, every actual real part, and the
entire infinite tail. It is not an assertion that the truncated law
has an exactly compactly supported transform. For every zero, including
the verified head, positivity and concavity also give the unchanged
bound $|\mathbb EC^{\rho-1}|\le M_*$ as in GAK9.


## Consume the same complete response on a larger finite clock slab

For every real clock in

$$
8\cdot10^{46}<A\le17\cdot10^{47},\qquad
L=\log A,\quad T_A=\sqrt A L,\quad r=1.304\cdot10^{24},
\tag{BFR8}
$$

the reused GAK25--GAK26 enclosures give $L>107$, $\sqrt A>10^{23}$
and $\eta_0(A)<10^{-6}$; also $\sqrt A<r$ since $r^2>17\cdot10^{47}$.
Apply the same complete coefficient and law-centered transport from
GAK12--GAK24 to this $C$. No log-uniform-product formula is used in
those law-general steps. The actual complex coefficient series,
its elementary response and every cutoff atom remain included.

The verified head has $\beta=1/2$ and is bounded by $M_*c_0$, with
$c_0<1/20$. For the unverified tail use (BFR7), the full-strip inequality
$A^{\beta-1/2}\le\sqrt A$, and the original
$2S_2(H)<74/(25\cdot10^{12})$. The factor two already counts both
ordinate signs with their actual multiplicities. The resulting allowance is

$$
\begin{aligned}
U_h&=\frac{108}{107}\frac{527}{500}\frac{M_*}{20},\\
U_t&=\frac{108}{107}\frac{10001}{10000}\,10^{-26}r
               \frac{74}{25\cdot10^{12}},\\
U_v&=\frac{260001}{500000}\,rV_*,\qquad
U_e=\frac{5M_*}{10^{23}},\\
-T_AI_\psi(A)&<U:=U_h+U_t+U_v+U_e<\frac{81}{100}.
\end{aligned}
\tag{BFR9}
$$

There is no additional inverse-moment multiplier on $U_t$: (BFR7)
already bounds the normalized response. Exact rational substitution gives
$U_h<0.0532$, $U_t<4\cdot10^{-14}$, $U_v<0.755$,
$U_e<6\cdot10^{-23}$, and

$$
Q_R-U>\frac3{1000},\qquad
Q_R=\frac{67838284064811}{83593750000000}.
$$

The last comparison uses the complete exact $U$, rather than adding the
rounded component bounds. The same GAK37 unrestricted reserve gives,
for each actual integer with $A=\log n$ in (BFR8), at its own price,

$$
\boxed{\quad
T_A\left[\gamma+\log L-\log\frac{\sigma(n)}n\right]
>\frac3{1000}+\frac{L}{(L+2)^3}+T_Ad_A(n)>0.
\quad}
\tag{BFR10}
$$

Here $d_A(n)\ge0$ is exactly GAK39's unrestricted-price defect of this
same original integer. It is neither replaced by a different optimizer
nor assumed zero. Thus this is strict Robin throughout the displayed
all-integer slab, under the original five analytic premises and the
classical Fourier identities used above. It needs no additional
zero-density estimate or zero-free half-plane at unverified heights.

The [prior GAD slab](../ArithSums/nicolas2025comparison.md#project-application-density-weighted-order-nine-transport-reaches-3e47)
reaches $3\cdot10^{47}$ using density inputs, and
[CDR1--CDR9](../Analytic/polak2026finiterobinca.md#a-seven-eighths-ceiling-in-the-complete-positive-law-robin-transport)
reach $6\cdot10^{47}$ with an additional $7/8$ ceiling. Their conclusions
and source conditions are preserved. The present change is the new
whole-law estimate in their existing complete consumer. Classical
Plancherel and the cosine window are reused; the project application
and finite slab are not attributed to a new external theorem.
The owning sources and targeted arXiv searches on Robin/Fourier smoothing
were checked; this is not an exhaustive literature or originality claim.

The [exact rational certificate](https://github.com/the-omega-institute/trureturing-experiments/tree/6f16e4e0df39286b91bb05a838de8e973612e403/experiments/robin-bandlimited-clock)
checks 25 scalar inequalities and reuses the existing rational logarithm
enclosure. It does not numerically certify the Fourier identities,
reverify zeros, or audit the external analytic proofs. These are
paper-level conditional results, without Lean/kernel certification.

No all-integer assertion below the lower endpoint, least-counterexample
bound or new verified zero height is inferred. For fixed $H$ the positive
variance term in (BFR9) still grows with $\sqrt A$. Thus the original
unbounded signed estimate, strict Robin for every integer above 5040,
and RH remain unproved.
