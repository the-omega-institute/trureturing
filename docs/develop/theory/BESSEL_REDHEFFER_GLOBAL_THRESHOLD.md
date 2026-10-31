# A global threshold for the normalized Bessel Redheffer ratio

## 1. Functions, zeros, and powers

**Definition 1.1 (Normalized Bessel function).** For a real number $\nu>-1$,
put $b=\nu+1>0$ and define

$$
F_\nu(x)=\sum_{k=0}^{\infty}
 \frac{(-x^2/4)^k}{k!(b)_k},\qquad
(b)_0=1,\qquad (b)_k=\prod_{\ell=0}^{k-1}(b+\ell)\quad(k\ge1).
\tag{1.1}
$$

The ratio of successive absolute terms tends to zero on every bounded
complex $x$-set, so this series defines an even entire function. For $x>0$
it is the classical normalization
$F_\nu(x)=2^\nu\Gamma(\nu+1)x^{-\nu}J_\nu(x)$.
The series and this correspondence are those of Baricz–Mehrez,
[arXiv:1701.08446v1](https://arxiv.org/pdf/1701.08446v1), and of
[Defs and Series](https://github.com/the-omega-institute/trureturing/tree/0acdf52ecf2d680cff8b44345188dbb02034280d/D5/S3/Analytic/BesselRedheffer).

**Definition 1.2 (The actual first zero and the proposed bound).** Let
$j=j_{\nu,1}$ be the smallest positive zero of $J_\nu$, equivalently of
$F_\nu$, and write

$$
J=j^2,\qquad
\theta=\frac{J}{4b(b+1)},\qquad
T_b=\frac{4b(b+1)(b+2)}{3b+2}.
\tag{1.2}
$$

For every real $x$ with $|x|<j$, set

$$
R_\nu(x)=\frac{F_{\nu+1}(x)}{F_\nu(x)},\qquad
L_\nu(x)=\left(\frac{J}{J-x^2}\right)^\theta.
\tag{1.3}
$$

Every real power here has a positive base and means
$a^c=\exp(c\log a)$ for $a>0$. In particular $L_\nu(0)=1$.
The first-zero existence, positivity, and nonvanishing denominators needed
in this definition are justified in the proof below for every $b>0$.

## 2. The global criterion

**Theorem 2.1 (Local obstruction and global sufficiency).** For every real
$\nu>-1$, with the actual first zero and parameters of Definition 1.2,

$$
\left[\ \forall x\in\mathbb R,\quad |x|<j
       \ \Longrightarrow\ L_\nu(x)\le R_\nu(x)\ \right]
\quad\Longleftrightarrow\quad J\ge T_b.
\tag{2.1}
$$

If $J\ge T_b$, including $J=T_b$, equality holds exactly at $x=0$.
If $J<T_b$, there exists $\varepsilon\in(0,j)$ such that
$R_\nu(x)<L_\nu(x)$ for every real $x$ with $0<x<\varepsilon$.

The quartic obstruction in this theorem is inherited from
[Expansion and the problem's local comparison](https://github.com/the-omega-institute/trureturing/blob/0acdf52ecf2d680cff8b44345188dbb02034280d/Problems/baricz-mehrez-2018-bessel-redheffer-lower-bound.md).
The additional inference is the converse on the entire first-zero
interval, including the critical equality of parameters.

Proof. Fix any real $b>0$ and put $\nu=b-1$.

The classical zero statements in
[DLMF §10.21(i)](https://dlmf.nist.gov/10.21#i) give infinitely many
positive zeros of $J_\nu$ and simplicity of its nonzero zeros for these
orders. The factor relating $F_\nu$ to $J_\nu$ is strictly positive on
$(0,\infty)$. Also $F_\nu(0)=1$, and analyticity excludes zeros in a
neighborhood of zero. A positive zero therefore exists, its positive
infimum is attained by continuity, and $j>0$ is the actual smallest
positive zero. The intermediate value theorem gives
$F_\nu(x)>0$ for $0\le x<j$.

Termwise differentiation and coefficient comparison in (1.1) give

$$
F_\nu'(x)=-\frac{x}{2b}F_{\nu+1}(x),\qquad
F_\nu''(x)+\frac{2b-1}{x}F_\nu'(x)+F_\nu(x)=0\quad(x>0),
\tag{2.2}
$$

and

$$
F_\nu(x)=F_{\nu+1}(x)
 -\frac{x^2}{4b(b+1)}F_{\nu+2}(x).
\tag{2.3}
$$

These are the shifted derivative, differential equation, and contiguous
relation supplied by [Series](https://github.com/the-omega-institute/trureturing/blob/0acdf52ecf2d680cff8b44345188dbb02034280d/D5/S3/Analytic/BesselRedheffer/Series.lean),
including its coefficient and proof-local entire-series identities.
For the full range $b>0$, integration of (2.2) gives

$$
x^{2b-1}F_\nu'(x)
 =-\int_0^x r^{2b-1}F_\nu(r)\,dr\qquad(0<x\le j).
\tag{2.4}
$$

Indeed, the integral is finite because $2b-1>-1$, and the omitted
boundary value is zero because
$r^{2b-1}F_\nu'(r)=O(r^{2b})$ as $r\downarrow0$.
The integral is strictly positive before and at $j$, hence
$F_\nu'(x)<0$ and $F_{\nu+1}(x)>0$ on $(0,j]$.
At zero the latter function is one. This also proves
$F_\nu'(j)<0$, so the first zero is simple. In particular all ratios
in (1.3) are positive on their stated domain. This argument uses the
classical actual zeros for $b>0$; it does not extend the hypotheses of
any restricted-order first-zero estimate.

For fixed $b>0$, analytic division at zero and the positive-base binomial
expansion give the inherited local comparison

$$
\begin{aligned}
R_\nu(x)
 &=1+\frac{x^2}{4b(b+1)}
   +\frac{x^4}{8b^2(b+1)(b+2)}+O(x^6),\\
L_\nu(x)
 &=1+\frac{x^2}{4b(b+1)}
   +\left(\frac{1}{32b^2(b+1)^2}
           +\frac{1}{8b(b+1)J}\right)x^4+O(x^6),\\
R_\nu(x)-L_\nu(x)
 &=\frac{(3b+2)J-4b(b+1)(b+2)}
 {32b^2(b+1)^2(b+2)J}\,x^4+O(x^6).
\end{aligned}
\tag{2.5}
$$

For completeness, the quotient calculation uses
$F_\nu(x)=1-x^2/(4b)+x^4/(32b(b+1))+O(x^6)$ and the
same formula with $b$ replaced by $b+1$ in the numerator.
The series is analytic for each fixed positive $b$, so these remainder
statements hold for every $b>0$; they do not assert a uniform error
constant as $b\downarrow0$.
The coefficient identity is the one in the private
`coefficient_gap` and `redheffer_lower` of
[Expansion](https://github.com/the-omega-institute/trureturing/blob/0acdf52ecf2d680cff8b44345188dbb02034280d/D5/S3/Analytic/BesselRedheffer/Expansion.lean).
Its private `series_remainder`, `quotient_remainder`, and `ratio_remainder`
supply explicit errors on their stated nonnegative-order ranges;
the arbitrary-$b$ expansions just used follow directly from (1.1).
If $J<T_b$, the last coefficient in (2.5) is negative, and the remainder
divided by $x^4$ tends to zero. This proves strict failure at every
sufficiently small positive $x$, and proves necessity in (2.1).

We next record the classical zero sums that will be consumed in the
sufficiency argument. Put $\lambda_n=j_{\nu,n}^2$ and
$\sigma_m=\sum_{n\ge1}\lambda_n^{-m}$. Equations (2.2)–(2.3)
of Baricz–Mehrez, arXiv:1701.08446v1, give, in the present normalization,

$$
\frac{F_{\nu+1}(\sqrt t)}{F_\nu(\sqrt t)}
 =4b\sum_{n\ge1}\frac1{\lambda_n-t},\qquad 0\le t<J,
\qquad \sigma_1=\frac1{4b}.
\tag{2.6}
$$

Here their (2.3) is the Mittag–Leffler expansion of the ordinary
$J_{\nu+1}/J_\nu$; multiplying by $2b/\sqrt t$ produces (2.6).
Their (2.2) is its Rayleigh power-series expansion.
For $|t|\le\rho<J$, the geometric expansion and all fixed-order
coefficient comparisons are dominated by
$(1-\rho/J)^{-1}\sum_n\lambda_n^{-1}$.
Thus comparison with (2.5) is legitimate and gives

$$
\sigma_2=\frac1{16b^2(b+1)},\qquad
\sigma_3=\frac1{32b^3(b+1)(b+2)}.
\tag{2.7}
$$

These zero-sum identities and the elementary comparisons below are
classical inputs, not independent additional conclusions.
Since there are zeros beyond $\lambda_1=J$,

$$
\sigma_2<\frac{\sigma_1}{J},\qquad
\sigma_3>\frac1{J^3}.
\tag{2.8}
$$

Consequently

$$
0<\theta<1,\qquad
J>\bigl(32b^3(b+1)(b+2)\bigr)^{1/3}.
\tag{2.9}
$$

A useful continuous parameter comparison is

$$
\begin{aligned}
(3b+2)^3-2(b+1)^2(b+2)^2
 &=b\bigl(-2b^3+15b^2+28b+12\bigr)\\
 &=b\bigl(2b^2(9-b)+b(28-3b)+12\bigr)>0
 \qquad(0<b\le9).
\end{aligned}
\tag{2.10}
$$

All factors used to cube positive quantities are positive. Therefore
(2.9)–(2.10) imply

$$
J>T_b\quad(0<b\le9).
\tag{2.11}
$$

This will also control the critical case: $J=T_b$ forces $b>9$.

Assume now $J\ge T_b$. Set $p=\theta$ and, for $0\le s<1$, define

$$
a(s)=\frac{F_\nu(\sqrt{Js})}{F_{\nu+1}(\sqrt{Js})},\qquad
u(s)=(1-s)^p,\qquad h(s)=a(s)-u(s).
\tag{2.12}
$$

The compositions with $\sqrt{Js}$ have analytic extensions in $s$ near
zero because the original series are even. They satisfy
$a(0)=u(0)=1$ and $a'(0)=u'(0)=-p$.
Writing $f(t)=F_\nu(\sqrt t)$ and $g(t)=F_{\nu+1}(\sqrt t)$,
(2.2)–(2.3) yield
$f'(t)=-g(t)/(4b)$ and $g'(t)=-b(g(t)-f(t))/t$ for $t>0$.
Thus the exact equation for $a$ is

$$
s a'(s)=b a(s)(1-a(s))-(b+1)p s.
\tag{2.13}
$$

At $s=1$, $g(J)>0$ and $f'(J)=-g(J)/(4b)$; Taylor's formula gives

$$
a(s)=(b+1)p(1-s)+O((1-s)^2),\qquad
\frac{a(s)}{u(s)}\longrightarrow0\quad(s\uparrow1),
\tag{2.14}
$$

because $0<p<1$. In particular $h(s)<0$ sufficiently near one.

Define the residual of the comparison function by

$$
\begin{aligned}
E(s)&=b u(s)(1-u(s))-(b+1)p s-su'(s)\\
 &=b\bigl((1-s)^p-(1-s)^{2p}\bigr)
   -(b+1)p s+p s(1-s)^{p-1}.
\end{aligned}
\tag{2.15}
$$

We will prove that $E$ is strictly negative and then strictly positive,
with exactly one intervening zero in $(0,1)$.
The proof requires coefficient signs at every degree, rather than
only the quartic comparison. For $n\ge1$ put

$$
A_n=-(-1)^n\binom pn=\frac{p(1-p)_{n-1}}{n!}>0,
\qquad B_n=(-1)^n\binom{2p}{n}.
\tag{2.16}
$$

The binomial series in (2.15), convergent for $|s|<1$, has zero
constant and linear coefficients. For $n\ge2$ it has coefficient

$$
e_n=(n-b)A_n-b B_n,\qquad
E(s)=\sum_{n\ge2}e_n s^n,\qquad
 e_2=\frac p2\bigl(b+2-(3b+2)p\bigr)\le0.
\tag{2.17}
$$

The coefficient $nA_n$ in the last term of (2.15) follows by
differentiating $(1-s)^p=1-\sum_{n\ge1}A_n s^n$.
The last inequality in (2.17) is precisely $J\ge T_b$.

First suppose $1/2<p<1$. Then $B_n>0$ for all $n\ge2$.
For $q_n=B_n/A_n$,

$$
q_{n+1}=q_n\frac{n-2p}{n-p},\qquad
0<q_{n+1}<q_n\quad(n\ge2).
\tag{2.18}
$$

Hence $e_n/A_n=n-b-bq_n$ is strictly increasing and is eventually
positive. For $p=1/2$, $B_n=0$ for $n\ge2$, and the same conclusion
holds with $q_n=0$.

If instead $0<p<1/2$, put $r_n=-B_n/A_n>0$ for $n\ge2$ and
$c_n=e_n/A_n=n-b+br_n$. Then

$$
r_{n+1}=r_n\frac{n-2p}{n-p},\qquad
c_{n+1}-c_n=1-\frac{bp r_n}{n-p}.
\tag{2.19}
$$

The positive sequence $r_n/(n-p)$ strictly decreases, since the ratio
of its next term to its present term is
$(n-2p)/(n+1-p)<1$. Thus the differences $c_{n+1}-c_n$ strictly
increase, and $c_n\ge n-b$ is eventually positive. If $c_2<0$,
this convex sequence can change sign only once, from negative to positive:
a positive value after $c_2$ has a positive preceding secant slope,
and all subsequent consecutive slopes are at least that slope.

It remains to check that the case $e_2=0$ also starts with a negative
coefficient at a later degree. This case is $J=T_b$, so (2.11) gives
$b>9$ and

$$
p=\frac{b+2}{3b+2}\in(1/3,2/5),\qquad
b=\frac{2(1-p)}{3p-1},\qquad
r_2=\frac{2(1-2p)}{1-p}.
\tag{2.20}
$$

Substitution in (2.19) gives

$$
c_2=0,\qquad
c_3=c_3-c_2
 =\frac{(5p-2)(p+1)}{(3p-1)(2-p)}<0.
\tag{2.21}
$$

The same increasing-slope argument now applies starting at $c_3$.
This proves in all cases that the coefficients of $E$ have a nonempty
initial negative part, possibly preceded by the zero $e_2$, and then
a positive tail, with no return to negative values.

More precisely, there is an integer $m\ge2$ for which
$e_n\le0$ for $2\le n\le m$, at least one of these inequalities
is strict, and $e_n>0$ for every $n>m$.
For $0<s<1$, termwise differentiation on compact subintervals gives

$$
\frac{d}{ds}\left(\frac{E(s)}{s^m}\right)
 =\sum_{n\ge2}(n-m)e_n s^{n-m-1}>0.
\tag{2.22}
$$

Every term is nonnegative and the positive tail is nonempty.
The first nonzero coefficient of $E$ is negative, whereas
$E(s)\to+\infty$ as $s\uparrow1$ by (2.15) and $p<1$.
Continuity and strict increase in (2.22) therefore yield a unique
$s_*\in(0,1)$ such that

$$
E(s)<0\ (0<s<s_*),\qquad E(s_*)=0,\qquad
E(s)>0\ (s_*<s<1).
\tag{2.23}
$$

Subtracting the equation for $u$ from (2.13) gives the exact linear
identity along the two functions

$$
s h'(s)=b(1-a(s)-u(s))h(s)+E(s).
\tag{2.24}
$$

Although the coefficient after division by $s$ is singular at zero,
analyticity determines the initial sign without invoking an initial-value
theorem there. Since $h(0)=h'(0)=0$, comparison of quadratic
coefficients in (2.24) gives

$$
h(s)=\frac{e_2}{b+2}s^2+O(s^3)\quad(e_2<0).
\tag{2.25}
$$

If $e_2=0$, comparison first at degree two and then at degree three gives

$$
h(s)=\frac{e_3}{b+3}s^3+O(s^4),\qquad e_3<0.
\tag{2.26}
$$

Thus $h<0$ sufficiently near zero, also in the critical case.
On any closed subinterval of $(0,1)$ a positive integrating factor
for (2.24) exists: with
$k(s)=b(1-a(s)-u(s))/s$ one may take
$M(s)=\exp(-\int_{s_0}^s k(v)\,dv)>0$.
It satisfies $(Mh)'=ME/s$.
Starting at a sufficiently small positive $s_0<s_*$, (2.23) shows
$Mh$ strictly decreases up to $s_*$; hence $h<0$ on $(0,s_*]$.
After $s_*$ the same transformed function strictly increases on every
compact subinterval. If $h$ were ever nonnegative there, it would
be strictly positive at every later point, contradicting (2.14).
Consequently $h(s)<0$ for every $0<s<1$.

We have proved $0<a(s)<(1-s)^p$ for every $s\in(0,1)$.
Taking positive reciprocals gives

$$
R_\nu(x)>\left(1-\frac{x^2}{J}\right)^{-\theta}
 =L_\nu(x)\qquad(0<|x|<j).
\tag{2.27}
$$

Evenness supplies all negative arguments in this statement, and both
sides equal one at zero. Together with (2.5), this proves every assertion
of the theorem. ∎

## 3. A continuous unconditional range

**Corollary 3.1 (Orders through eight).** For every real $\nu$ with
$-1<\nu\le8$ and every real $x$ with $|x|<j_{\nu,1}$,

$$
\left(\frac{j_{\nu,1}^2}{j_{\nu,1}^2-x^2}\right)^
 {j_{\nu,1}^2/[4(\nu+1)(\nu+2)]}
 \le \frac{F_{\nu+1}(x)}{F_\nu(x)},
\tag{3.1}
$$

with equality if and only if $x=0$.

Proof. This entire real interval is $0<b\le9$. Equations (2.9)–(2.11)
give $J>T_b$ there by a single polynomial inequality, and Theorem 2.1
applies. ∎

The classical Rayleigh comparison is an intermediate in this deduction;
the substantive conclusion combines its continuous parameter estimate
with the global converse of Theorem 2.1.

## 4. Mathematical citations and comparison of bounds

The objects of Theorem 2.1 are exactly the normalization, first zero,
exponent, and real argument domain in Baricz–Mehrez,
[arXiv:1701.08446v1, §3, Conjecture 1, (3.2)](https://arxiv.org/pdf/1701.08446v1).
Their (2.2)–(2.3) supply the Rayleigh and Mittag–Leffler expansions used
in (2.6), and their Theorem 6 proves the lower bound at $\nu=-1/2$.
Their Theorems 1–2 concern individual normalized Bessel functions;
those statements are distinct from the adjacent-order ratio in (2.1).

Baricz–Wu, *Sharp exponential Redheffer-type inequalities for Bessel
functions*, [DOI:10.5486/PMD.2009.4291, Theorem 1, (1.3)](https://doi.org/10.5486/PMD.2009.4291),
prove, for every real $\nu\ge-7/8$ and $|x|<j_{\nu,1}$,

$$
\frac{F_{\nu+1}(x)}{F_\nu(x)}
 \ge\left(\frac{J+x^2}{J-x^2}\right)^{J/[8b(b+1)]}.
\tag{4.1}
$$

For $0<s=x^2/J<1$, the logarithm of the lower bound in Theorem 2.1
minus that of (4.1) is

$$
-p\log(1-s)-\frac p2\log\frac{1+s}{1-s}
 =-\frac p2\log(1-s^2)>0.
\tag{4.2}
$$

Thus on the common parameter range where $J\ge T_b$, the bound
in (2.1) is stronger; (4.1) retains its separate domain and conclusion
when that condition is absent. The two bases and exponents are different.

Aktaş–Baricz–Singh, *Geometric and monotonic properties of hyper-Bessel
functions*, [arXiv:1802.05226v1, §2.6, Theorems 6–7](https://arxiv.org/pdf/1802.05226v1),
consider parameters $\alpha_i>-1$. Their Theorem 6 states absolute
monotonicity of auxiliary functions $h_{\boldsymbol\alpha}$ and
$q_{\boldsymbol\alpha}$ built from a single normalized hyper-Bessel
function, on $[0,j_{\boldsymbol\alpha,1}^{d+1})$.
Their Theorem 7 treats the single function on
$0<x<j_{\boldsymbol\alpha,1}$; at $d=1$, $\alpha_1=\nu$, it gives

$$
(1-x^2/J)^{J/(4b)}\le F_\nu(x)\le1-x^2/J.
\tag{4.3}
$$

These are single-function results, whereas (2.1) compares the consecutive
orders with exponent $J/[4b(b+1)]$.

Alzahrani–Mondal, *Redheffer-Type Bounds of Special Functions*,
[DOI:10.3390/math11020379, primary XML](https://mdpi-res.com/d_attachment/mathematics/mathematics-11-00379/article_deploy/mathematics-11-00379.xml?version=1672996709),
define the product classes $\mathcal F_\nu$ and $\mathcal G_\nu$ in
(13)–(14) with respective factors $1-x^2/b_n(\nu)^2$ and
$1+x^2/b_n(\nu)^2$ and convergence assumptions.
Their Theorem 1(6) bounds a single member of $\mathcal F_\nu$ by powers
of $1-x^2/b_1(\nu)^2$ on $|x|<b_1(\nu)$.
The Bessel specialization is Theorem 5, (40), exactly (4.3) for
$\nu>-1$ and $|x|<j_{\nu,1}$. Their Theorem 1(5) concerns the ratio of
the plus-product and minus-product functions with the same zero data;
that ratio is different from $F_{\nu+1}/F_\nu$.

For the inherited obstruction, the
[complete Series, Expansion, FirstZero, and Result sources](https://github.com/the-omega-institute/trureturing/tree/0acdf52ecf2d680cff8b44345188dbb02034280d/D5/S3/Analytic/BesselRedheffer)
supply the differential identities, the fourth-order comparison, and the
following complementary failure mechanism. The proof-local weighted
Picone identity in `FirstZero.picone_integral`, together with
`energy_moments`, uses $u(r)=(1-r^2)^3$ and yields the bound
$J\le(6/5)b(b+6)$ on the stated range $b\ge31$.
There $(6/5)b(b+6)<T_b$, since
$b^2-30b-16>0$. The local comparison therefore yields failure at every
sufficiently small positive argument for every $\nu\ge30$;
`Expansion.failure_of_energy_bound` and `Result.failure_family` supply
this inherited family and `Result.result` supplies the universal
refutation. No first-zero existence or energy estimate outside their
stated order hypotheses is inferred from those sources. The unrestricted
classical first-zero input in this proof is the one from DLMF cited above.

## 5. The remaining order question

**Definition 5.1 (Validity set and residual sign question).** Define

$$
\mathcal V=\left\{\nu>-1:
 j_{\nu,1}^2\ge
 \frac{4(\nu+1)(\nu+2)(\nu+3)}{3\nu+5}\right\},
\qquad
H(b)=j_{b-1,1}^2-T_b\quad(b>0).
\tag{5.1}
$$

Theorem 2.1 identifies $\mathcal V$ exactly with the orders for which
(1.3) holds throughout $|x|<j_{\nu,1}$, and Corollary 3.1 gives
$(-1,8]\subset\mathcal V$. The inherited failure family gives
$[30,\infty)\cap\mathcal V=\varnothing$.
The residual question is to determine the sign of $H(b)$ on
$9<b<31$, including its zero set. The present conclusions do not specify
that zero set or a unique change of sign. An exact determination of that
sign set would determine the remaining orders through (2.1), without
altering its argument quantifiers or its exponent.

## 追加锚（本行以下为增补区）
## 6. The unique order threshold

**Definition 6.1 (Critical parameter).** Continue to write

$$
H(b)=j_{b-1,1}^{\,2}-T_b,\qquad
T_b=\frac{4b(b+1)(b+2)}{3b+2}\quad(b>0).
\tag{6.1}
$$

The first-zero dependence on the order is continuous, and is continuously
differentiable wherever the zero is simple.  For positive order the order
variation formula for a positive cylinder-function zero is

$$
\frac{d}{d\nu}j_{\nu,1}
 =2j_{\nu,1}\int_0^\infty
 K_0\!\left(2j_{\nu,1}\sinh t\right)e^{-2\nu t}\,dt .
\tag{6.2}
$$

This is the first-zero specialization of DLMF [§10.21(iv), (10.21.17)](https://dlmf.nist.gov/10.21#E17); the positivity and integral representation of $K_0$ used below are the classical formulas in DLMF [§10.32(i), (10.32.9)](https://dlmf.nist.gov/10.32#E9).

**Lemma 6.2 (Every zero of $H$ is a downward crossing).** If $b>9$ and
$H(b)=0$, then $H'(b)<0$.

**Proof.** Put

$$
\nu=b-1,\qquad r=\sqrt{T_b}=j_{\nu,1},\qquad
\rho=\frac{\nu}{r}.
$$

The identity

$$
T_b-(b-1)^2=\frac{b^3+16b^2+9b-2}{3b+2}>0
\tag{6.3}
$$

shows that $0<\rho<1$.  Moreover,

$$
\frac{d}{db}\rho^2
 =\frac{(b-1)(13b^3+27b^2+16b+4)}
 {4b^2(b+1)^2(b+2)^2}>0,
\tag{6.4}
$$

and $\rho^2|_{b=9}=232/495>7/15$.  Thus
$\rho^2\ge7/15$ for every $b\ge9$.

For $0<\vartheta<\pi/2$, the function
$\vartheta/\sin\vartheta$ is strictly increasing.  We claim that

$$
\frac{\vartheta}{\sin\vartheta}<\frac98
\quad\text{whenever}\quad
\cos^2\vartheta\ge\frac7{15}.
\tag{6.5}
$$

Indeed, let $a=41/50$.  The alternating Taylor bound on $0<a<1$ gives

$$
\cos a
 <1-\frac{a^2}{2}+\frac{a^4}{24}-\frac{a^6}{720}+\frac{a^8}{40320}
 <\frac{683}{1000}<\sqrt{\frac7{15}},
\tag{6.6}
$$

where the last two rational inequalities follow by clearing positive
denominators.  Hence
$\arccos\sqrt{7/15}<41/50$, and, using
$\sin(\arccos\sqrt{7/15})=\sqrt{8/15}$,

$$
\frac{\vartheta}{\sin\vartheta}
 \le\frac{41}{50}\sqrt{\frac{15}{8}}<\frac98;
\tag{6.7}
$$

for the final comparison, $(41/50)^2(15/8)=5043/4000<81/64$.
This proves (6.5).  Applying it to
$\vartheta=\arccos\rho$ gives

$$
\frac{\arccos(\nu/r)}{\sqrt{r^2-\nu^2}}
 =\frac1r\frac{\vartheta}{\sin\vartheta}<\frac9{8r}.
\tag{6.8}
$$

For $z>0$, $K_0(z)=\int_0^\infty e^{-z\cosh u}\,du$ is positive and
strictly decreasing.  Since $\sinh t>t$ for $t>0$, (6.2) and Tonelli's
theorem give the strict estimate

$$
\begin{aligned}
\frac{1}{2}\frac{d}{d\nu}\log j_{\nu,1}
&<\int_0^\infty K_0(2rt)e^{-2\nu t}\,dt\\
&=\int_0^\infty\!\int_0^\infty
 e^{-2\nu t-2rt\cosh u}\,du\,dt\\
&=\int_0^\infty\frac{du}{2\nu+2r\cosh u}\\
&=\frac{\arccos(\nu/r)}{2\sqrt{r^2-\nu^2}}.
\end{aligned}
\tag{6.9}
$$

The last equality follows from $y=\tanh(u/2)$ and
$\arctan\sqrt{(r-\nu)/(r+\nu)}=\tfrac12\arccos(\nu/r)$.
Consequently, (6.8) yields

$$
\frac{d}{d\nu}\log j_{\nu,1}<\frac9{8r}.
\tag{6.10}
$$

It remains to compare this with the derivative of the proposed crossing
curve.  With $r(b)=\sqrt{T_b}$, direct differentiation gives

$$
\left(r'(b)\right)^2-\left(\frac{23}{20}\right)^2
=\frac{
117b^6+585b^5+14292b^4+44704b^3+54816b^2+29936b+6400
}{400b(b+1)(b+2)(3b+2)^3}>0.
\tag{6.11}
$$

Since $T_b'>0$ for $b>0$, also $r'(b)>0$; hence
$r'(b)>23/20>9/8$.  At a zero of $H$, (6.10) and
$T_b'=2r r'$ imply

$$
H'(b)=2r^2\frac{d}{d\nu}\log j_{\nu,1}-2rr'
 <2r\left(\frac98-r'\right)<0.
\tag{6.12}
$$
This proves the lemma. ∎

**Theorem 6.3 (Complete sign classification).** There is exactly one
$b_*\in(9,31)$ such that $H(b_*)=0$, and, for every $b>0$,

$$
H(b)>0\iff b<b_*,\qquad
H(b)=0\iff b=b_*,\qquad
H(b)<0\iff b>b_*.
\tag{6.13}
$$

**Proof.** The continuous first-zero dependence noted in Definition 6.1
makes $H$ continuous.  The already established range $0<b\le9$ gives
$H(9)>0$.  The inherited energy estimate at order $\nu\ge30$ gives

$$
J\le\frac65b(b+6)<T_b\qquad(b\ge31),
\tag{6.14}
$$

because
$T_b-\frac65b(b+6)=2b(b^2-30b-16)/(5(3b+2))>0$ there; hence
$H(31)<0$.  The intermediate value theorem supplies at least one zero
in $(9,31)$.

Lemma 6.2 says that every zero in this interval has strictly negative
derivative, so each is isolated and the function is positive immediately
before it and negative immediately after it.  The zero set in $[9,31]$ is
compact, the endpoints are not zeros, and every interior point is isolated;
therefore it is finite.  If two zeros
existed, two consecutive members would therefore exist; the sign just
after the first and just before the second would then force another zero
between them, a contradiction.  Therefore the zero is unique.  Since $H$ has no zero on
either side of $b_*$ and has the signs at $9$ and $31$ just proved, its
signs are exactly (6.13). ∎

**Corollary 6.4 (The original order range).** Let
$\nu_*=b_*-1$.  For every real $\nu>-1$, with the actual first positive
zero $j_{\nu,1}$ and the unchanged definitions (1.2)–(1.3),

$$
\left[\forall x\in\mathbb R,\ |x|<j_{\nu,1}
 \Longrightarrow L_\nu(x)\le R_\nu(x)\right]
\quad\Longleftrightarrow\quad
-1<\nu\le\nu_* .
\tag{6.15}
$$

At the critical order $\nu=\nu_*$ equality is attained exactly at $x=0$.
For every $\nu>\nu_*$, the inequality fails strictly at every sufficiently
small positive $x$, by the inherited local-obstruction direction of
Theorem 2.1. ∎

## 追加锚（本行以下为增补区）
