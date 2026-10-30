# Parameter classification of Xu–Yang Mills remainders

## 1. Definitions and source correspondence

**Definition 1.1 (Original normalization and remainders).** For $x>0$ and real $a,b$, let

$$
\begin{aligned}
R(x)&=e^{x^2/2}\int_x^\infty e^{-t^2/2}\,dt,\\
Y_{a,b}(x)&=(x^2+a)R(x)^2+bxR(x),\\
c_k&=\frac{2^k\Gamma(k+1/2)}{\Gamma(1/2)}
\quad(k\ge0),\\
u_k(a,b)&=(b+1)c_k
 +(k-a)(k-1)!\sum_{j=0}^{k-1}\frac{c_j}{j!}
\quad(k\ge1).
\end{aligned}
$$

Thus $c_0=1$. These are exactly the unscaled Gaussian Mills ratio and
the expressions in Xu–Yang [XY, (1.8), (3.7)]. Throughout the remainder
statements $b=a-2$, and, for every integer $n\ge2$, define

$$
\begin{aligned}
D_n(x,a)&=Y_{a,a-2}(x)
 -\left(a-1+\sum_{k=1}^n(-1)^ku_k(a,a-2)x^{-2k}\right),\\
F_{n,a}(x)&=(-1)^nD_n(x,a).
\end{aligned}
$$

A function $f$ is completely monotone, abbreviated CM, if it is
$C^\infty$ on $(0,\infty)$ and
$(-1)^mf^{(m)}(x)\ge0$ for every integer $m\ge0$ and every $x>0$.
In particular the condition includes $m=0$.

**Definition 1.2 (Polynomial moments and thresholds).** For every integer
$j\ge0$, put

$$
A(v)=1+v^2,\qquad
I_j=\int_0^1 A(v)^j\,dv,\qquad
B_j=\int_0^1v^2A(v)^j\,dv,\qquad
\theta_j=\frac{1-I_j/B_j}{2}.
$$

All these integrals are finite, and $0<B_j<I_j$.

**Convention 1.3 (Mathematical citations).** The following source labels
specify the inputs used in the proofs.

- [XY] H.-Z. Xu and Z.-H. Yang, *Higher order monotonicity involving the
  Mills ratio with applications*,
  [DOI 10.1186/s13660-026-03505-9](https://doi.org/10.1186/s13660-026-03505-9):
  (1.8), (3.7), Theorem 3.3 and its convolution proof, Theorem 4.2,
  and Conjecture 7.1.
- [R] The repository's
  [positive-kernel proof for the Xu–Yang remainders](https://github.com/the-omega-institute/trureturing/blob/c839927b42e1589abf191d336c10b6539a962b85/D5/S3/Analytic/XuYangMillsRemainder/Result.lean),
  including the private mathematical identities named
  $\mathtt{convolutionClosed}$, $\mathtt{intPow\_rec}$,
  $\mathtt{coeff\_sum}$, $\mathtt{coeff\_factorial}$,
  $\mathtt{expRemainder\_eq}$, $\mathtt{expRemainderBounds}$,
  $\mathtt{remainderRepresentation}$ and $\mathtt{laplaceCM}$.
  Their content includes the coefficient correspondence and the
  positive Laplace representation for every $n\ge2$ at $a=-1$.

## 2. Classification for every truncation order

**Theorem 2.1 (General-parameter sign and complete monotonicity).**
For every integer $n\ge2$ and every real $a$, the following equivalences hold:

$$
\begin{aligned}
\bigl[\ \forall x>0,\ F_{n,a}(x)\ge0\ \bigr]
&\ \Longleftrightarrow\
\bigl[\ F_{n,a}\text{ is CM}\ \bigr]
\ \Longleftrightarrow\
\bigl[\ a\le\theta_{n-2}\ \bigr],\\
\bigl[\ \forall x>0,\ -F_{n,a}(x)\ge0\ \bigr]
&\ \Longleftrightarrow\
\bigl[\ -F_{n,a}\text{ is CM}\ \bigr]
\ \Longleftrightarrow\
\bigl[\ a\ge\theta_{n-1}\ \bigr].
\end{aligned}
$$

Both parameter endpoints are included. The general-$a$, arbitrary-$n$
classification and its equivalence with global sign are the
repository-derived inference here. The $n=2,3,4$ CM classifications are
inherited from [XY, Theorem 4.2], and the all-order $a=-1$ result is
inherited from [R]. The general convolution kernel, half-integer Gamma
correspondence, finite Taylor remainder and differentiation of Laplace
integrals used below are inherited inputs and methods.

*Proof.* Fix $n\ge2$ and $a\in\mathbb R$. Write $u_k=u_k(a,a-2)$.

First identify the finite coefficients without changing the normalization.
The identities in [R, $\mathtt{intPow\_rec}$,
$\mathtt{coeff\_sum}$, $\mathtt{coeff\_factorial}$] give

$$
\begin{aligned}
(2j+3)I_{j+1}-2(j+1)I_j&=2^{j+1}\quad(j\ge0),\\
\sum_{\ell=0}^{k-1}\frac{c_\ell}{\ell!}
 &=\frac{c_kI_{k-1}}{2^{k-1}(k-1)!}\quad(k\ge1),\\
c_k&=\frac{(2k-1)!}{2^{k-1}(k-1)!}\quad(k\ge1).
\end{aligned}
\tag{2.1}
$$

The first identity integrates the derivative of $v(1+v^2)^{j+1}$;
the second is the coefficient-sum identity already supplied in [R],
with its index shifted. Substitution into the original $u_k$ yields
$u_1=0$ and, for $k\ge2$,

$$
u_k=c_k\left(a-1+\frac{k-a}{2^{k-1}}I_{k-1}\right).
$$

Use the first identity of (2.1) at $j=k-2$, and
$B_{k-2}=I_{k-1}-I_{k-2}$. Explicitly,

$$
\begin{aligned}
&(a-1)2^{k-1}+(k-a)I_{k-1}\\
&\quad=(k-1)\left((2-2a)I_{k-2}+(2a-1)I_{k-1}\right)\\
&\quad=(k-1)\left(I_{k-2}+(2a-1)B_{k-2}\right).
\end{aligned}
$$

Consequently the exact coefficient identity needed below is

$$
\begin{aligned}
u_k
 &=\frac{(2k-1)!}{4^{k-1}(k-2)!}
       \left(I_{k-2}+(2a-1)B_{k-2}\right)\\
 &=\frac{2(2k-1)!B_{k-2}}{4^{k-1}(k-2)!}
       (a-\theta_{k-2})\qquad(k\ge2).
\end{aligned}
\tag{2.2}
$$

Next use the convolution integral in the proof of [XY, Theorem 3.3].
To spell out its specialization, let $h(t)=e^{-t^2/2}$ and
$e_t(v)=e^{-A(v)t^2/4}$. That source's kernel, before its power-series
expansion, gives

$$
Y_{a,a-2}(x)-(a-1)=\int_0^\infty e^{-xt}G_a(t)\,dt,
$$

where

$$
G_a(t)=t\int_0^1
 \left(\frac{t^2}{4}(1-v^2)+a\right)e_t(v)\,dv
 -at h(t).
$$

The inherited Gaussian convolution is
$R(x)^2=\int_0^\infty e^{-xt}t\int_0^1e_t(v)\,dv\,dt$;
this is also [R, $\mathtt{convolutionClosed}$].
The fundamental theorem of calculus applied to $v e_t(v)$ gives

$$
h(t)=\int_0^1\left(1-\frac{t^2v^2}{2}\right)e_t(v)\,dv.
$$

It follows directly that

$$
G_a(t)=\frac{t^3}{4}\int_0^1
 \left(1+(2a-1)v^2\right)e^{-A(v)t^2/4}\,dv.
\tag{2.3}
$$

This is a specialization and rearrangement of the supplied general
kernel, not a new kernel assertion.

For an integer $r\ge1$ and $y\ge0$, use the classical signed remainder

$$
E_r(y)=(-1)^r
 \left(e^{-y}-\sum_{j=0}^{r-1}\frac{(-y)^j}{j!}\right).
$$

Its Taylor integral formula and bound are

$$
\begin{aligned}
E_r(y)&=\frac{y^r}{(r-1)!}
       \int_0^1(1-s)^{r-1}e^{-sy}\,ds,\\
0&\le E_r(y)\le \frac{y^r}{r!}.
\end{aligned}
\tag{2.4}
$$

These finite remainders are the ones used in [R].
For $y>0$ they are strictly positive. Put $r=n-1$.
In (2.3) subtract the Taylor terms with $0\le j\le r-1$.
Their Laplace integrals are exactly

$$
\frac{(-1)^j(2j+3)!}{4^{j+1}j!x^{2j+4}}
 \int_0^1\left(1+(2a-1)v^2\right)A(v)^j\,dv
 =(-1)^{j+2}u_{j+2}x^{-2j-4}
$$

by (2.2) and
$\int_0^\infty t^q e^{-xt}\,dt=q!x^{-q-1}$.
The indices $j+2$ run from $2$ to $n$, and $u_1=0$.
Since $(-1)^n(-1)^r=-1$, this proves the exact representation

$$
\begin{aligned}
F_{n,a}(x)&=\int_0^\infty e^{-xt}L_{r,a}(t)\,dt,\\
L_{r,a}(t)&=\frac{t^3}{4}\int_0^1
 \left((1-2a)v^2-1\right)E_r\left(A(v)t^2/4\right)\,dv .
\end{aligned}
\tag{2.5}
$$

All finite subtractions and changes of integration order here are
absolutely integrable: $1\le A(v)\le2$, the coefficient weight is
bounded on $[0,1]$, and (2.4) bounds the final kernel by
$C_{r,a}t^{2r+3}$ for some finite constant $C_{r,a}$.
The original Gaussian kernel and each subtracted polynomial also
have finite Laplace integrals for $x>0$.

The additional sign comparison must handle the signed weight in (2.5).
For fixed $z>0$, set

$$
M_0(z)=\int_0^1 E_r(zA(v))\,dv,\qquad
M_2(z)=\int_0^1 v^2E_r(zA(v))\,dv .
$$

We claim

$$
\frac{B_{r-1}}{I_{r-1}}
 <\frac{M_2(z)}{M_0(z)}
 <\frac{B_r}{I_r}.
\tag{2.6}
$$

Here is a direct weighted-integral proof. For any positive continuous
weight $w$ on $[0,1]$, let $\mathbb E_w$ denote integration divided by
$\int_0^1 w$. If $p(v)=v^2$, then

$$
\begin{aligned}
&\mathbb E_w[pq]-\mathbb E_w[p]\,\mathbb E_w[q]\\
&\quad=\frac{1}{2\left(\int_0^1w\right)^2}
 \int_0^1\int_0^1
 (p(v)-p(u))(q(v)-q(u))w(v)w(u)\,du\,dv .
\end{aligned}
\tag{2.7}
$$

Thus multiplying $w$ by a positive strictly increasing function of
$v$ strictly increases the $p$-mean; a strictly decreasing multiplier
strictly decreases it. Strictness follows on the positive-measure set
$0<u<v<1$.

Formula (2.4) shows that $E_r(y)/y^r$ is strictly decreasing for $y>0$:
differentiating its integral gives a strictly negative integral.
On the other hand the same formula, after $s y=q$, reads

$$
\frac{E_r(y)}{y^{r-1}}
 =\frac{1}{(r-1)!}\int_0^y
       (1-q/y)^{r-1}e^{-q}\,dq.
\tag{2.8}
$$

This is strictly increasing. For $r=1$ it equals $1-e^{-y}$.
For $r>1$, increasing $y$ strictly increases the integrand on the
old interval $0<q<y$ and adds a positive interval.
It follows that
$E_r(zA(v))/A(v)^{r-1}$ is a strictly increasing multiplier, while
$E_r(zA(v))/A(v)^r$ is a strictly decreasing multiplier.
Apply (2.7) to the weights $A^{r-1}$ and $A^r$, respectively.
This proves (2.6).

In particular $M_0(z),M_2(z)>0$. The function
$\mu\mapsto(1-\mu^{-1})/2$ is strictly increasing for $\mu>0$;
hence (2.6) implies

$$
\theta_{r-1}
 <\frac{1-M_0(z)/M_2(z)}2
 <\theta_r .
\tag{2.9}
$$

For $t>0$, take $z=t^2/4$ in (2.5). Its inner integral is

$$
(1-2a)M_2(z)-M_0(z)
 =2M_2(z)\left(\frac{1-M_0(z)/M_2(z)}2-a\right).
$$

Therefore $L_{r,a}(t)>0$ for every $t>0$ if
$a\le\theta_{r-1}$, including equality, and
$L_{r,a}(t)<0$ for every $t>0$ if $a\ge\theta_r$,
also including equality. Since $r=n-1$, these are the two asserted
parameter ranges.

For completeness, the inherited Laplace differentiation argument gives
every derivative sign, not merely the zeroth one. The polynomial
bound following (2.5) implies, for every $m\ge0$ and $x>0$,

$$
\int_0^\infty t^m e^{-xt}|L_{r,a}(t)|\,dt<\infty.
$$

In a neighborhood of any fixed $x_0>0$, the integrands for all fixed
derivative orders are bounded by a constant times
$t^{m+2r+3}e^{-x_0t/2}$, an integrable function.
Repeated dominated differentiation yields $C^\infty$ smoothness and

$$
(-1)^mF_{n,a}^{(m)}(x)
 =\int_0^\infty t^m e^{-xt}L_{r,a}(t)\,dt .
\tag{2.10}
$$

Thus $F_{n,a}$ is CM in the first range and $-F_{n,a}$ is CM in the
second range. In fact every corresponding signed derivative is strictly
positive, because its density is strictly positive for $t>0$.
No characterization of arbitrary CM densities is needed.

It remains to prove necessity already from the global sign.
The Gaussian integral gives $R(0)=\sqrt{\pi/2}$ and continuity at zero,
so $Y_{a,a-2}(x)$ stays bounded as $x\downarrow0$. The finite definition
of $D_n$ therefore gives

$$
\lim_{x\downarrow0}x^{2n}F_{n,a}(x)=-u_n.
\tag{2.11}
$$

If $F_{n,a}\ge0$ everywhere, then $u_n\le0$.
By (2.2) this forces $a\le\theta_{n-2}$.

For the opposite sign, the needed limit at infinity follows either
from [XY, Theorem 3.1] or directly from the exact remainder.
To give the latter justification, (2.4) gives
$E_r(y)/y^r\to1/r!$ as $y\downarrow0$. Consequently

$$
\lim_{t\downarrow0}\frac{L_{r,a}(t)}{t^{2r+3}}
 =-\frac{I_r+(2a-1)B_r}{4^{r+1}r!}.
$$

In (2.5) make the substitution $t=s/x$.
The bound $|L_{r,a}(t)|\le C_{r,a}t^{2r+3}$ gives the fixed dominating
function $C_{r,a}s^{2r+3}e^{-s}$. Dominated convergence and (2.2) yield

$$
\begin{aligned}
\lim_{x\to\infty}x^{2n+2}F_{n,a}(x)
 &=-\frac{(2r+3)!}{4^{r+1}r!}
          \left(I_r+(2a-1)B_r\right)\\
 &=-u_{n+1}.
\end{aligned}
\tag{2.12}
$$

If $-F_{n,a}\ge0$ everywhere, then (2.12) forces $u_{n+1}\ge0$,
hence $a\ge\theta_{n-1}$ by (2.2).
Finally CM implies global nonnegativity by its $m=0$ condition.
Together with the two sufficiency arguments these implications prove
both full chains of equivalences. $\square$

## 3. Thresholds, simultaneous orders and sign changes

**Corollary 3.1 (Exact initial thresholds and limiting ranges).**
For the moments in Definition 1.2,

$$
\theta_0=-1,\qquad
\theta_1=-\frac34,\qquad
\theta_2=-\frac{13}{23},\qquad
\theta_3=-\frac{25}{58}.
$$

The sequence $(\theta_j)_{j\ge0}$ strictly increases to $0$.
For every real $a$,

$$
\begin{aligned}
\bigl[\ \forall n\ge2,\ F_{n,a}\text{ is CM}\ \bigr]
 &\Longleftrightarrow a\le-1,\\
\bigl[\ \forall n\ge2,\ -F_{n,a}\text{ is CM}\ \bigr]
 &\Longleftrightarrow a\ge0.
\end{aligned}
$$

*Proof.* Polynomial integration gives

$$
\begin{array}{c|cccc}
j&0&1&2&3\\ \hline
I_j&1&4/3&28/15&96/35\\
B_j&1/3&8/15&92/105&464/315
\end{array}
$$

and substitution gives the four displayed values.
To prove strict increase, let $\mathbb E_j$ denote expectation with
density $A(v)^j/I_j$ on $[0,1]$, and set
$\mu_j=\mathbb E_j[v^2]=B_j/I_j$. Then

$$
\mu_{j+1}-\mu_j
 =\frac{\mathbb E_j[v^4]-\mu_j^2}{1+\mu_j}>0.
$$

The numerator is the variance of a nonconstant continuous function
under a strictly positive density. Since $0<\mu_j<1$,
$\theta_j=(1-\mu_j^{-1})/2<0$, and $\theta_j$ strictly increases.

For $0<c<d<1$, let $\mathbb P_j$ be the same probability measure.
Its mass on $v^2\le c$ satisfies

$$
\mathbb P_j(v^2\le c)
 \le \frac1{1-\sqrt d}
          \left(\frac{1+c}{1+d}\right)^j\longrightarrow0.
$$

Indeed the numerator defining this probability is at most $(1+c)^j$,
while the normalizing integral is at least
$(1-\sqrt d)(1+d)^j$. Hence
$\liminf_j\mu_j\ge c$ for every $c<1$, whereas $\mu_j<1$.
Thus $\mu_j\to1$ and $\theta_j\to0$.
Theorem 2.1 now gives the simultaneous ranges by taking,
respectively, $\inf_{j\ge0}\theta_j=-1$ and
$\sup_{j\ge1}\theta_j=0$. $\square$

**Corollary 3.2 (Intermediate range and first-index boundary).**
For every integer $n\ge2$ and every real
$\theta_{n-2}<a<\theta_{n-1}$, there exist
$0<\varepsilon<X<\infty$ such that

$$
F_{n,a}(x)<0\quad(0<x<\varepsilon),\qquad
F_{n,a}(x)>0\quad(x>X).
$$

In particular $F_{n,a}$ has at least one zero in $(0,\infty)$.
For the finite definition extended to $n=1$, the inherited index boundary
at $a=-1$ is $F_{1,-1}(x)<0$ for every $x>0$, so $F_{1,-1}$ is not CM.

*Proof.* Equation (2.2) gives $u_n>0$ and $u_{n+1}<0$.
The strictly negative limit in (2.11) and the strictly positive limit
in (2.12) give the two asserted open intervals. Shrinking the first
and enlarging the second ensures $\varepsilon<X$.
Continuity follows from (2.5), so the intermediate value theorem
supplies a zero between points in these two intervals.
This argument asserts neither uniqueness of that zero nor any
classification of the zeros of derivatives. The comparison (2.9)
also makes no monotonicity assertion in $x$ for a threshold obtained
after integrating a signed weight.

For the stated first-index boundary, the original coefficients give
$u_1(-1,-3)=u_2(-1,-3)=0$, so $D_1(x,-1)=D_2(x,-1)$.
The inherited positive representation [R] is

$$
D_2(x,-1)=\int_0^\infty e^{-xt}\frac{t^5}{8}
       \int_0^1 v^2(1-v^2)e^{-(1+v^2)t^2/4}\,dv\,dt>0 .
$$

Strict positivity follows on $t>0$ and $0<v<1$.
Thus $F_{1,-1}=-D_2(\,\cdot\,,-1)<0$.
This is the necessary index boundary for [XY, Conjecture 7.1];
its $n\ge2$, $a=-1$ assertion is the supplied result [R]. $\square$

## 追加锚（本行以下为增补区）
