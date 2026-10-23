# Fixed-block conditional information and nuisance efficiency

This volume extends the completed-pair conditional acquisition result of Section 22 of *Real renewal instruments and detector rank* to every fixed block size. The source polynomials, stationary initialization and consecutive paid binary history are exactly those of that supplier. For a fixed integer $m\ge2$, conditioning the $m$ complete gaps on their observed total removes the geometric nuisance and yields an explicit information coefficient. The limit $s\downarrow0$ is taken with $m$ fixed; only afterwards is $m\to\infty$ considered.

The arguments are ordinary handwritten mathematics, conditional on the expressly credited actual-source interfaces. They are not kernel verification or a claim of physical realization. The pair result and its controllers are inherited results, not new pair theorems. The new content is the fixed-$m$ convolution and moment bridge, both conditional divergences, their paid normalization, and the resulting sequential efficiency comparison.

## 1. Exact source, notation and stationary acquisition

**Definition 1.1 (The two fixed rational weights).** Let $D_H=35\cdot10^{24}$. On nonnegative integer gap counts use exactly

$$
F_0(k)=k^9,
$$

and

$$
\begin{aligned}
F_1(k)=H(k)=k^9+\frac1{D_H}(&55800726477138 k-224986136658885 k^2\\
&+420664314485485 k^3-540138133491075 k^4\\
&+518234977000797 k^5-254383031435085 k^6\\
&+77668004560980 k^7+43377331415040 k^8).
\end{aligned}
$$

Write $h_p=[k^p]H(k)$ for its rational monomial coefficients; thus $h_0=0$ and $h_9=1$. For $k\ge1$ set

$$
\begin{aligned}
r_k&=\frac{H(k)}{k^9}=1+\frac ak+\sum_{j=2}^8\frac{b_j}{k^j},
&b_j&=h_{9-j},\\
a&=h_8=\frac{43377331415040}{35\cdot10^{24}}
=\frac{9914818609152}{8\cdot10^{24}}>0,
&\delta&=\frac{2749658638697}{10^{24}}\in(0,1).
\end{aligned}
$$

The exact center certificate of the supplier's Theorem 15.5 gives

$$
1\le r_k\le1+\frac\delta k\quad(k\ge1),
\qquad r_1=1+\delta.
$$

In particular both weights are positive at every positive integer and vanish at zero. This is the rational center polynomial of its equation (19.7), not the residual-zero limiting polynomial. Its instrument and that of $F_0$ retain the supplier's existing complex memory dimension six; the block size below is an observer parameter and does not change either producer.

**Definition 1.2 (Nuisance families and asymptotic notation).** For $i\in\{0,1\}$ and $q\in(0,1)$ let

$$
\begin{aligned}
Z_i(q)&=\sum_{k\ge1}F_i(k)q^k,
&f_{i,q}(k)&=\frac{F_i(k)q^k}{Z_i(q)}\quad(k\ge1),
&f_{i,q}(0)&=0,\\
S_{i,q}(t)&=\sum_{k\ge t}f_{i,q}(k)\quad(t\ge0),
&\mu_i(q)&=\mathbb E_{i,q}(K+1),
&\beta_i(q)&=\frac{\mathbb E_{i,q}[K(K+1)]}{2\mu_i(q)}.
\end{aligned}
$$

Every $Z_i(q)$ is positive and finite, and every polynomial moment is finite, by polynomial-geometric summability. Write $\mathsf P_{i,q}$ for the actual stationary binary law of this source and $\mathbb E_{i,q}$ for expectation under it or its stated gap marginal. The promise consists of the two entire families $\{\mathsf P_{0,q}:0<q<1\}$ and $\{\mathsf P_{1,q'}:0<q'<1\}$, with independent, unconstrained opposing nuisance values $q,q'$. No assertion equates them.

All logarithms in information formulas are natural. For probability laws $P,Q$ on the same finite or countable support, with positive masses there, write

$$
D(P\Vert Q)=\sum_xP(x)\log\frac{P(x)}{Q(x)}.
$$

All countable uses below have absolutely integrable log ratios by the credited unequal-parameter interface; shared zero masses are omitted. The notation $\mathsf P_{i,q}^W$ denotes the restriction to the first $W$ actual bits.

The notation $O_{H,m}(n^{-r})$ bounds the absolute remainder by a constant depending on the one fixed polynomial $H$ and the fixed integer $m$, for all sufficiently large $n$. Analogous notation in $s$ means $s\downarrow0$ with these data fixed. Constants can also depend on the fixed rational risk $\alpha$ when shown. Such notation carries no uniformity in $m$, in varying polynomials, or over the whole nuisance interval. Set $s=-\log q>0$ when discussing the near-one limit.

**Proposition 1.3 (Inherited stationary source and its paid acquisition).** Theorems 11.5, 15.3 and 17.4 of the supplier identify the actual stationary law, under each $i,q$, by

$$
\begin{aligned}
\mathsf P_{i,q}(0^a1\,0^{g_1}1\cdots0^{g_r}1\,0^b)
&=\frac{S_{i,q}(a)S_{i,q}(b)}{\mu_i(q)}
\prod_{v=1}^r f_{i,q}(g_v),\\
\mathsf P_{i,q}(0^W)
&=\frac1{\mu_i(q)}\sum_{k\ge W}(k-W+1)f_{i,q}(k).
\end{aligned}
$$

Here $r\ge0$, all run lengths are nonnegative integers, and an empty product is one. If $X_0,X_1,\ldots$ is this one actual history and

$$
\tau=\min\{t\ge0:X_t=1\},
$$

then $\tau$ is finite almost surely, $\mathbb E_{i,q}\tau=\beta_i(q)$, and the complete gaps $K_1,K_2,\ldots$ following that observed tick are iid with law $f_{i,q}$ and independent of $\tau$. The initial acquisition costs $\tau+1$ reads. A gap of $k$ zeros costs $k+1$ additional reads, including its closing tick. For either label,

$$
Z_i(e^{-s})=9!s^{-10}(1+O_H(s)),\qquad
\mu_i(e^{-s})=\frac{10}{s}+O_H(1),\qquad
\beta_i(e^{-s})=\frac{11}{2s}+O_H(1).
$$

Proof. The actual instrument construction and its own faithful stationary initializer are the credited premises. Their displayed cylinders, at a final closing tick with $b=0$, give exactly

$$
\mathsf P_{i,q}(\tau=t,K_1=k_1,\ldots,K_N=k_N)
=\frac{S_{i,q}(t)}{\mu_i(q)}\prod_{v=1}^Nf_{i,q}(k_v).
$$

Nonnegative summation gives $\sum_{t\ge0}S_{i,q}(t)=\mu_i(q)$ and

$$
\sum_{t\ge0}tS_{i,q}(t)
=\sum_{k\ge1}\frac{k(k+1)}2f_{i,q}(k).
$$

These identities prove the asserted normalization, independence and mean wait. The gap index counts zeros, so each subsequent closing one adds one read. The supplier's fixed-degree power-sum estimate, also proved in Lemma 6.1 below, gives the displayed near-one formulas: the leading moment numerators for $K$ and $K(K+1)$ are respectively $10!s^{-11}$ and $11!s^{-12}$, while the leading normalizer is $9!s^{-10}$. Thus $\mathbb EK=10/s+O_H(1)$, $\mathbb E[K(K+1)]=110/s^2+O_H(s^{-1})$, and the formula for $\beta_i$ follows. These are the acquisition and moment interfaces already used in the supplier's equations (20.29) and (22.20). $\square$

The observer's only source actions are consecutive read-next-bit and stop. Every initial zero, closing tick, rejected statistic, partial gap and unfinished block is paid. There is no free conditional draw, omitted interval, reset, second source, hidden age, probability oracle or alteration of a stationary initializer. Rational $0<\alpha<1/2$ is supplied as finite binary numerator-denominator data; a prescribed positive real tolerance can instead be met using a supplied smaller positive rational allowance. The unknown true nuisance needs no representation.

## 2. Exact completed-block laws

**Definition 2.1 (Compositions, convolution and conditional information).** Fix an integer $m\ge2$. For an integer $n\ge m$ set

$$
\Omega_{m,n}=\{(k_1,\ldots,k_m)\in\mathbb N_{\ge1}^m:
 k_1+\cdots+k_m=n\},\qquad
C_{i,m}(n)=\sum_{k\in\Omega_{m,n}}\prod_{j=1}^mF_i(k_j).
$$

Set $C_{i,m}(n)=0$ for $0\le n<m$. At legal totals define

$$
G_{i,m,n}(k)=\frac{\prod_{j=1}^mF_i(k_j)}{C_{i,m}(n)},\qquad
w_n(k)=\prod_{j=1}^m r_{k_j},\qquad
c_n=\frac{C_{1,m}(n)}{C_{0,m}(n)}.
$$

Write $\mathbb E_{i,n}$ and $\operatorname{Var}_{i,n}$ for expectation and variance under $G_{i,m,n}$, suppressing the fixed $m$. Define

$$
\begin{aligned}
d_{0,m}(n)&=D(G_{0,m,n}\Vert G_{1,m,n}),\\
d_{1,m}(n)&=D(G_{1,m,n}\Vert G_{0,m,n}),\\
\overline D_{i,m}(q)&=\sum_{n\ge m}
\frac{C_{i,m}(n)q^n}{Z_i(q)^m}\,d_{i,m}(n).
\end{aligned}
$$

**Theorem 2.2 (Exact nuisance cancellation on the paid history).** For a block of $m$ consecutive complete gaps after the actual first tick, write $K=(K_1,\ldots,K_m)$ and $T=\sum_{j=1}^mK_j$. Then

$$
\mathsf P_{i,q}(T=n)=\frac{C_{i,m}(n)q^n}{Z_i(q)^m},\qquad
\mathsf P_{i,q}(K=k\mid T=n)=G_{i,m,n}(k).
$$

Every composition at every legal total has positive mass, and

$$
c_n=\mathbb E_{0,n}w_n,\qquad
\frac{G_{1,m,n}(k)}{G_{0,m,n}(k)}=\frac{w_n(k)}{c_n},\qquad
1\le w_n,c_n\le\mathcal R_m:=(1+\delta)^m.
$$

The block consumes exactly $T+m$ reads after its starting tick, whose expectation under label $i$ is $m\mu_i(q)$.

Proof. Proposition 1.3 makes the joint mass of the observed gaps equal to

$$
\frac{\prod_{j=1}^mF_i(k_j)q^{\sum_j k_j}}{Z_i(q)^m}.
$$

Summation over ordered compositions of a given total yields its claimed mass, and division cancels $q^n/Z_i(q)^m$. Positivity follows from Definition 1.1. Summing over all totals gives one by the product of the $m$ nonnegative convergent series $Z_i(q)$. Replacing $F_1(k)$ by $r_kF_0(k)$ proves the two tilt identities. The envelope bounds each factor between one and $1+\delta$, and an expectation preserves those bounds. Finally the $m$ gaps contribute their zeros and $m$ closing ticks, hence $T+m$, with the stated expectation. Conditioning is a statistic of this acquired block, not a replacement acquisition method. $\square$

## 3. Exact polynomial convolution and endpoint moments

**Lemma 3.1 (Finite composition polynomial on its complete integer domain).** Let $m\ge1$ and $d=(d_1,\ldots,d_m)$ be a tuple of positive integers, and define

$$
D=\sum_{j=1}^m(d_j+1),\qquad
P_d(n)=\sum_{\substack{k_1+\cdots+k_m=n\\k_j\ge1}}
\prod_{j=1}^m k_j^{d_j}\quad(n\in\mathbb Z_{\ge0}).
$$

An empty composition set has sum zero, so $P_d(n)=0$ for every integer $0\le n<m$. There is a rational polynomial $\mathcal P_d(x)$ agreeing with $P_d(n)$ at every nonnegative integer, including that zero range, and

$$
\deg\mathcal P_d=D-1,\qquad
[x^{D-1}]\mathcal P_d=\frac{\prod_jd_j!}{(D-1)!}>0.
$$

In particular

$$
P_d(n)=\frac{\prod_jd_j!}{(D-1)!}n^{D-1}+O_d(n^{D-2})
\quad(n\to\infty).
$$

The polynomial is constructible by finitely many exact rational coefficient operations from $d$.

Proof. We prove polynomiality, agreement on all $n\ge0$, and the initial zero range together by induction on the number of parts. For $m=1$ take $\mathcal P_{(d_1)}(x)=x^{d_1}$. It is zero at zero because $d_1\ge1$, and at every positive integer it is the sole composition weight. Here $D=d_1+1$, giving the claimed degree and coefficient.

For the induction step let $m\ge2$, let $d'=(d_1,\ldots,d_{m-1})$, and define

$$
D'=\sum_{j=1}^{m-1}(d_j+1),\qquad d_*=d_m,
\qquad D=D'+d_*+1.
$$

The induction hypothesis gives a rational polynomial

$$
\mathcal P_{d'}(x)=\sum_{h=0}^{D'-1}c_hx^h,
\qquad \mathcal P_{d'}(0)=c_0=0,
\qquad c_{D'-1}=\frac{\prod_{j<m}d_j!}{(D'-1)!}.
$$

For any nonnegative integer $v$, let $Q_v(x)$ be the rational power-sum polynomial with $Q_v(n)=\sum_{k=0}^{n-1}k^v$ for all $n\ge0$. One finite construction, writing $\Delta f(t)=f(t+1)-f(t)$, is

$$
Q_v(x)=\sum_{r=0}^{v}\bigl(\Delta^r(t^v)\bigr)\big|_{t=0}
\binom{x}{r+1}.
$$

For $v=0$ the polynomial $t^0$ is the constant one. The binomial polynomials form a basis, and $\Delta\binom{x}{r+1}=\binom{x}{r}$; the Newton expansion therefore gives $\Delta Q_v(x)=x^v$ and $Q_v(0)=0$. Telescoping proves its values at every $n\ge0$. This also proves $\deg Q_v=v+1$ and gives a finite rational construction, without assuming a formula only on a tail of the integers.

Define the next polynomial by

$$
\mathcal P_d(x)=\sum_{h=0}^{D'-1}c_h
\sum_{r=0}^{h}(-1)^r\binom hr x^{h-r}Q_{d_*+r}(x).
$$

For every integer $n\ge1$, its value is

$$
\sum_{k=0}^{n-1}k^{d_*}\mathcal P_{d'}(n-k)
=\sum_{k=1}^{n-1}k^{d_*}P_{d'}(n-k)
=P_d(n).
$$

The term at $k=0$ is zero because $d_*\ge1$. All other arguments $n-k$ are nonnegative integers, so the full-domain induction hypothesis applies, including arguments smaller than $m-1$. Those smaller arguments have value zero. Thus if $1\le n<m$, every term vanishes, exactly as the empty composition definition requires. At $n=0$, every term in the defining polynomial contains $Q_{d_*+r}(0)=0$, so $\mathcal P_d(0)=0$ as well. This proves the necessary initial zeros and makes every invocation at a small argument legal.

Each polynomial summand has degree at most $(h-r)+(d_*+r+1)=h+d_*+1$, at most $D'+d_*=D-1$. To identify the top coefficient set $b'=c_{D'-1}>0$. The leading contribution for large positive $n$ is

$$
b'\sum_{k=1}^{n-1}k^{d_*}(n-k)^{D'-1}.
$$

All lower powers in $\mathcal P_{d'}$ contribute $O_d(n^{D'+d_*-1})$: each has at most $n$ terms bounded by a constant times $n^{d_*+D'-2}$. The normalized leading sum is a mesh-$1/n$ sum for $f(x)=x^{d_*}(1-x)^{D'-1}$ on $[0,1]$. Since $d_*\ge1$ and $D'-1\ge1$, both endpoints vanish and its derivative is integrable. Summing the error on each mesh interval bounds the difference from the integral by $n^{-1}\int_0^1|f'(x)|\,dx$. Repeated integration by parts gives

$$
\int_0^1x^{d_*}(1-x)^{D'-1}\,dx
=\frac{d_*!(D'-1)!}{(D'+d_*)!}.
$$

Therefore the coefficient of $n^{D-1}$ is $b'd_*!(D'-1)!/(D'+d_*)!=\prod_jd_j!/(D-1)!$, which is positive, proving the exact degree and remainder. Every composition, including endpoint compositions, remained in the recurrence. All operations specifying the polynomial were finite rational operations. $\square$

**Corollary 3.2 (Fixed rational block normalizers).** For either $i\in\{0,1\}$ the sequence $C_{i,m}(n)$, with its zero values for $0\le n<m$, agrees on all nonnegative integers with a rational polynomial of degree $10m-1$, and

$$
C_{i,m}(n)=b_m n^{10m-1}+O_{H,m}(n^{10m-2}),
\qquad b_m=\frac{(9!)^m}{(10m-1)!}.
$$

Its values are strictly positive for every integer $n\ge m$. These polynomials can be preprocessed exactly from the fixed rational $H$ and integer $m$.

Proof. The $F_0$ assertion is Lemma 3.1 with every exponent nine. Expand the finite product of monomial descriptions of $F_1$ inside its finite composition sum. All exponents lie in $\{1,\ldots,9\}$ because $H(0)=0$. Each resulting term is a rational coefficient times a polynomial from Lemma 3.1. The unique term with every exponent nine has coefficient one and degree $10m-1$; any other exponent tuple has $\sum_j(d_j+1)\le10m-1$ and hence polynomial degree at most $10m-2$. Thus the top coefficient is $b_m$, and the same zero-range agreement holds for every term. Positivity at legal totals follows from the original positive defining sum, regardless of signs in the polynomial's coefficients. The finite construction in the lemma supplies the preprocessing. $\square$

**Lemma 3.3 (All inverse moments through total order four).** Fix $m\ge2$ and nonnegative integers $\ell_1,\ldots,\ell_m$ with $L=\sum_j\ell_j\le4$. Then, for every legal total, the exact moment is a ratio of the polynomials of Lemma 3.1, and as $n\to\infty$,

$$
\begin{aligned}
\mathbb E_{0,n}\prod_{j=1}^mK_j^{-\ell_j}
&=\frac{P_{9-\ell_1,\ldots,9-\ell_m}(n)}{P_{9,\ldots,9}(n)}\\
&=n^{-L}\left(M_\ell+O_m(n^{-1})\right),\\
M_\ell&=\frac{(10m-1)!}{(10m-1-L)!}
\prod_{j=1}^m\frac{(9-\ell_j)!}{9!}.
\end{aligned}
$$

All these estimates can be bounded with constants valid on the entire set $n\ge m$. More specifically, for each coordinate $v$ and $0<\eta\le1/2$ there is a finite constant $C_{m,\ell}$ such that

$$
n^L\mathbb E_{0,n}\left[
\prod_jK_j^{-\ell_j}\mathbf1_{\{K_v\le\eta n\}}\right]
\le C_{m,\ell}\eta^{10-\ell_v}
\quad(n\ge m).
$$

In particular

$$
\mathbb E_{0,n}K_v^{-4}
=\frac{(10m-1)(10m-2)(10m-3)(10m-4)}{9\cdot8\cdot7\cdot6}\,n^{-4}
+O_m(n^{-5}).
$$

Proof. Multiplication by the inverse powers in the $G_0$ sum lowers its exponents from nine to $9-\ell_j\ge5$. The exact ratio follows directly, and both numerator and denominator have the full-domain polynomial description already proved. Their degrees are $10m-L-1$ and $10m-1$ respectively. Dividing their leading coefficients gives $M_\ell$. The positive leading denominator is at least $b_m n^{10m-1}/2$ for all sufficiently large $n$, which justifies the quotient remainder. Each of the finitely many remaining legal denominators is positive, so increasing the constants extends each bound to all $n\ge m$. At $L=0$ the ratio is exactly one.

For the explicit endpoint estimate, by symmetry take $v=1$, and put

$$
D_{\rm rest}=\sum_{j=2}^m(10-\ell_j).
$$

The numerator restricted to $K_1\le\eta n$ is exactly

$$
\sum_{1\le k\le\eta n}k^{9-\ell_1}
P_{9-\ell_2,\ldots,9-\ell_m}(n-k).
$$

The polynomial bound from Lemma 3.1 and its zero range give an upper bound $C_m n^{D_{\rm rest}-1}$ for the second factor, uniformly over these arguments. There is no term if $\eta n<1$. Otherwise the elementary bound for a sum of nonnegative powers gives $\sum_{k\le\eta n}k^{9-\ell_1}\le C_m(\eta n)^{10-\ell_1}$. The denominator is at least $c_m' n^{10m-1}$ on all legal integers, for some $c_m'>0$, by its positive leading coefficient and finitely many positive initial values. Since

$$
D_{\rm rest}-1+10-\ell_1=10m-L-1,
$$

division proves the stated endpoint estimate. The fourth-moment formula is the case $\ell_v=4$ and all other indices zero. Thus the endpoints are controlled quantitatively by finite sums; no weak-convergence substitution for an unbounded observable is used. $\square$

## 4. The finite-block variance and the precise tilt bounds

**Lemma 4.1 (Inverse-sum variance).** Under $G_{0,m,n}$ let $A_n=\sum_{j=1}^mK_j^{-1}$. For fixed $m\ge2$,

$$
\begin{aligned}
\mathbb E_{0,n}A_n&=\frac{m(10m-1)}{9n}+O_m(n^{-2}),\\
\mathbb E_{0,n}A_n^2
&=\frac{m(8m+1)(10m-1)(10m-2)}{648n^2}+O_m(n^{-3}),\\
\operatorname{Var}_{0,n}(A_n)&=\frac{v_m}{n^2}+O_m(n^{-3}),
\qquad v_m=\frac{m(m-1)(10m-1)}{324}>0.
\end{aligned}
$$

Proof. Lemma 3.3 supplies, for distinct $u,v$,

$$
\begin{aligned}
\mathbb E_{0,n}K_v^{-1}&=\frac{10m-1}{9n}+O_m(n^{-2}),\\
\mathbb E_{0,n}K_v^{-2}&=\frac{(10m-1)(10m-2)}{72n^2}+O_m(n^{-3}),\\
\mathbb E_{0,n}(K_u^{-1}K_v^{-1})
&=\frac{(10m-1)(10m-2)}{81n^2}+O_m(n^{-3}).
\end{aligned}
$$

Sum the first identity over $m$ coordinates. Expanding $A_n^2$ gives $m$ diagonal terms and $m(m-1)$ ordered off-diagonal terms; $m/72+m(m-1)/81=m(8m+1)/648$. Subtracting the square of the mean gives the coefficient

$$
\begin{aligned}
\frac{m(10m-1)}{648}
\bigl((8m+1)(10m-2)-8m(10m-1)\bigr)
=\frac{m(m-1)(10m-1)}{324}.
\end{aligned}
$$

The remainder in the squared mean is $O_m(n^{-3})$, so the variance statement follows.

For identification of the constant, let $X$ have density proportional to $\prod_jx_j^9$ on $x_j>0$, $\sum_jx_j=1$, with respect to $dx_1\cdots dx_{m-1}$ and $x_m=1-\sum_{j<m}x_j$. Iterated beta integration gives its normalizing integral $(9!)^m/(10m-1)!$: the two-variable beta integral is the integration-by-parts identity used in Lemma 3.1, and integrating the last free coordinate after rescaling by the remaining total reduces the dimension by one. The same argument after lowering exponents by $\ell_j$ gives exactly $M_\ell$. Thus these are the inverse moments of the Dirichlet$(10,\ldots,10)$ law, and $v_m=\operatorname{Var}(\sum_jX_j^{-1})$. The finite-$n$ conclusion was obtained from exact convolution ratios, so this identification supplies no additional limit-interchange premise. $\square$

**Lemma 4.2 (Product remainder through fourth order).** Let

$$
B=\sum_{j=2}^8|b_j|,\qquad
D_m=B+2^{m-2}(m-1)\delta^2,\qquad
\Lambda_m=\delta(1+\delta)^{m-1}.
$$

For every composition at every legal total,

$$
w_n=1+aA_n+e_n,\qquad
|e_n|\le D_m\sum_jK_j^{-2},\qquad
0\le w_n-1\le\Lambda_m A_n.
$$

Consequently, for $p\in\{1,2,3,4\}$,

$$
\begin{aligned}
\mathbb E_{0,n}|e_n|&=O_{H,m}(n^{-2}),&
\mathbb E_{0,n}e_n^2&=O_{H,m}(n^{-4}),\\
\mathbb E_{0,n}|w_n-1|^p&=O_{H,m}(n^{-p}),&
\operatorname{Var}_{0,n}(w_n)&=\frac{a^2v_m}{n^2}+O_{H,m}(n^{-3}),\\
c_n&=1+\frac{am(10m-1)}{9n}+O_{H,m}(n^{-2}).
\end{aligned}
$$

Proof. Write $u_j=r_{K_j}-1$. The exact inverse-power expansion and the envelope give

$$
0\le u_j\le\delta/K_j,\qquad
\varepsilon_j:=u_j-a/K_j,\qquad |\varepsilon_j|\le B/K_j^2.
$$

In the expansion of $\prod_j(1+u_j)$, the terms of degree at least two satisfy

$$
\sum_{|S|\ge2}\prod_{j\in S}u_j
\le\sum_{u<v}u_u u_v\prod_{j\ne u,v}(1+u_j).
$$

Indeed each nonnegative monomial indexed by $S$ appears on the right with multiplicity $\binom{|S|}{2}\ge1$. Since $1+\delta<2$ and

$$
\frac1{K_uK_v}\le\frac12(K_u^{-2}+K_v^{-2}),
$$

the right side is at most $2^{m-2}\delta^2(m-1)\sum_jK_j^{-2}/2$. Adding $\sum_j\varepsilon_j$ proves the stated, conservatively larger, constant $D_m$. A telescoping expansion of the product gives

$$
\prod_{j=1}^m(1+u_j)-1
=\sum_{j=1}^m u_j\prod_{r<j}(1+u_r)
\le\delta(1+\delta)^{m-1}\sum_jK_j^{-1}.
$$

For the square remainder, finite-sum Cauchy–Schwarz gives

$$
e_n^2\le D_m^2m\sum_jK_j^{-4}.
$$

Lemma 3.3 therefore proves its $O(n^{-4})$ expectation, as well as the $O(n^{-2})$ first absolute moment. The fourth inverse moment is essential to this particular square estimate. For $1\le p\le4$, convexity gives $(\sum_j x_j)^p\le m^{p-1}\sum_jx_j^p$ for $x_j\ge0$. Apply it to the last product bound and use the inverse moments to obtain $\mathbb E|w_n-1|^p=O(n^{-p})$.

Finally $\operatorname{Var}(e_n)\le\mathbb Ee_n^2=O(n^{-4})$, while Lemma 4.1 gives $\operatorname{Var}(A_n)=O(n^{-2})$. Cauchy–Schwarz yields $|\operatorname{Cov}(A_n,e_n)|=O(n^{-3})$. Expanding the variance of $1+aA_n+e_n$ proves its coefficient. Taking expectations proves the stated expansion of $c_n$. All estimates include the endpoint compositions. $\square$

**Proposition 4.3 (Averaged tilt control and the endpoint counterexample).** For every fixed $m\ge2$ and $p\in\{1,2,3,4\}$,

$$
\mathbb E_{0,n}\left|\frac{w_n}{c_n}-1\right|^p
=O_{H,m}(n^{-p}).
$$

The assertion $w_n/c_n=1+O_{H,m}(n^{-1})$ is false if its remainder is required uniformly over all compositions. Nevertheless

$$
\operatorname{Var}_{1,n}(w_n)=\frac{a^2v_m}{n^2}+O_{H,m}(n^{-3}).
$$

Proof. Set $U_n=w_n-1$ and $\eta_n=\mathbb E_{0,n}U_n=c_n-1\ge0$. Then $w_n/c_n-1=(U_n-\eta_n)/(1+\eta_n)$. The inequality $|x-y|^p\le2^{p-1}(|x|^p+|y|^p)$, Jensen's inequality $\eta_n^p\le\mathbb EU_n^p$, and Lemma 4.2 prove the averaged bounds.

For a counterexample to uniformity use the legal composition $(1,\ldots,1,n-m+1)$. Since $r_k\to1$, $r_1=1+\delta$ and $c_n\to1$,

$$
\frac{w_n(1,\ldots,1,n-m+1)}{c_n}
\longrightarrow(1+\delta)^{m-1}>1.
$$

The fourth-order moment bounds do not assert this exceptional composition has a typical size of tilt.

For the other variance set $z=w_n-c_n$ and $\sigma_n^2=\mathbb E_{0,n}z^2$. The exact change of measure $G_1/G_0=w_n/c_n=(c_n+z)/c_n$ and $\mathbb E_0z=0$ give

$$
\mathbb E_1z=\frac{\sigma_n^2}{c_n},\qquad
\mathbb E_1z^2=\sigma_n^2+\frac{\mathbb E_0z^3}{c_n}.
$$

Consequently

$$
\operatorname{Var}_{1,n}(w_n)
=\sigma_n^2+\frac{\mathbb E_0z^3}{c_n}
-\frac{(\sigma_n^2)^2}{c_n^2}.
$$

Here $c_n\ge1$, $\mathbb E_0|z|^3=O(n^{-3})$, and $(\sigma_n^2)^2=O(n^{-4})$ by Lemma 4.2 and the centered-moment bound just used. Its variance coefficient is therefore the same. This weighted identity supplies the required conclusion without a pointwise tilt shortcut. $\square$

## 5. Both fixed-total relative entropies

**Theorem 5.1 (Two orientations and their full remainder).** For every fixed $m\ge2$ and $i\in\{0,1\}$,

$$
d_{i,m}(n)=\frac{a^2v_m}{2n^2}+O_{H,m}(n^{-3})
=\frac{a^2m(m-1)(10m-1)}{648n^2}+O_{H,m}(n^{-3}).
$$

The remainder has a bound on all integers $n\ge m$ after enlarging its constant. Both divergences are finite and nonnegative at every legal total. They vanish at $n=m$ and $n=m+1$, and are strictly positive for every sufficiently large $n$.

Proof. All expectations in this calculation are under $G_{0,m,n}$. Put $U=w_n-1\ge0$ and $\eta=\mathbb EU=c_n-1$. The exact identities from Theorem 2.2 are

$$
\begin{aligned}
d_{0,m}(n)&=\log(1+\eta)-\mathbb E\log(1+U),\\
d_{1,m}(n)&=\frac{\mathbb E[(1+U)\log(1+U)]
-(1+\eta)\log(1+\eta)}{1+\eta}.
\end{aligned}
$$

The variable $U$ lies in $[0,\mathcal R_m-1]$. On this entire interval Taylor's theorem gives

$$
\begin{aligned}
\log(1+u)&=u-\frac{u^2}{2}+r_0(u),
&|r_0(u)|&\le\frac{u^3}{3},\\
(1+u)\log(1+u)&=u+\frac{u^2}{2}+r_1(u),
&|r_1(u)|&\le\frac{u^3}{6}.
\end{aligned}
$$

The third derivatives are respectively $2/(1+u)^3$ and $-1/(1+u)^2$, which prove those bounds for every $u\ge0$. Linear terms cancel after expectation. Thus

$$
\begin{aligned}
d_{0,m}(n)&=\tfrac12\operatorname{Var}(U)
+O(\mathbb EU^3+\eta^3),\\
d_{1,m}(n)&=\frac{\operatorname{Var}(U)}{2(1+\eta)}
+O(\mathbb EU^3+\eta^3).
\end{aligned}
$$

Lemma 4.2 gives $\eta=O_{H,m}(n^{-1})$, $\mathbb EU^3=O_{H,m}(n^{-3})$ and $\operatorname{Var}(U)=a^2v_mn^{-2}+O_{H,m}(n^{-3})$; Jensen also bounds $\eta^3$ by $\mathbb EU^3$. The divisor $1+\eta$ in the second direction changes the quadratic term by only $O_{H,m}(n^{-3})$. This proves both expansions under one reference measure, with no assumption of a uniformly small endpoint tilt.

Finiteness follows from the finite positive supports and $\mathcal R_m^{-1}\le G_1/G_0\le\mathcal R_m$. Nonnegativity follows from Jensen applied to $-\log$ and $x\log x$ in the exact formulas. At $n=m$ the sole composition is all ones. At $n=m+1$ exactly one coordinate is two and the rest are one; all $m$ permutations have equal mass under either label, so both conditional laws are uniform and equal. Their divergences therefore vanish. Since $a>0$ and $v_m>0$, the proved asymptotic makes each divergence positive at every sufficiently large total. Any finite initial range has finite divergences and can be absorbed in the remainder constant. $\square$

## 6. Averaging the total and normalizing by paid reads

**Lemma 6.1 (Power-sum averaging bound).** For every fixed nonnegative integer $r$,

$$
\sum_{n\ge1}n^r e^{-sn}=r!s^{-r-1}+O_r(s^{-r})
\quad(s\downarrow0).
$$

For each fixed integer $m\ge1$, omitting the finitely many terms $n<m$ preserves this expansion. An absolute remainder bounded by a constant times $n^r$ therefore has summed magnitude $O_r(s^{-r-1})$.

Proof. Let $f(x)=x^re^{-x}$ on $[0,\infty)$. Its derivative is integrable, including $r=0$, and $\int_0^\infty f(x)\,dx=r!$ by integration by parts. On the interval $[(n-1)s,ns]$, the difference between $sf(ns)$ and the integral of $f$ is at most $s\int_{(n-1)s}^{ns}|f'(x)|\,dx$. Sum the errors to obtain

$$
\left|s\sum_{n\ge1}f(sn)-r!\right|
\le s\int_0^\infty|f'(x)|\,dx.
$$

Dividing by $s^{r+1}$ proves the claim. Finitely many omitted terms contribute $O_{r,m}(1)$, which is within the displayed remainder. The final upper bound follows by applying the same estimate to the absolute majorant. $\square$

**Theorem 6.2 (Averaged divergence and the fixed-block paid coefficient).** For each fixed $m\ge2$ and either true label $i$,

$$
\overline D_{i,m}(e^{-s})
=\frac{a^2m(m-1)}{648(10m-2)}s^2+O_{H,m}(s^3).
$$

For every $q\in(0,1)$ one has $0<\overline D_{i,m}(q)<\infty$. Define the mean conditional information per paid post-tick read by

$$
I^{\mathrm{paid}}_{i,m}(q)
=\frac{\overline D_{i,m}(q)}{m\mu_i(q)}.
$$

Then

$$
I^{\mathrm{paid}}_{i,m}(e^{-s})=c_ms^3+O_{H,m}(s^4),\qquad
c_m=\frac{a^2(m-1)}{12960(5m-1)}.
$$

Proof. Corollary 3.2 and Theorem 5.1, with constants extended over the finite initial range, give

$$
C_{i,m}(n)d_{i,m}(n)
=b_m\frac{a^2v_m}{2}n^{10m-3}+O_{H,m}(n^{10m-4}).
$$

Lemma 6.1 sums the leading term against $e^{-sn}$ as

$$
b_m\frac{a^2v_m}{2}(10m-3)!s^{-(10m-2)}
+O_{H,m}(s^{-(10m-3)}),
$$

and bounds the entire absolute remainder sum by the same lower order. Moreover

$$
Z_i(e^{-s})^m=(9!)^m s^{-10m}(1+O_{H,m}(s))
$$

by Proposition 1.3 and fixed $m$. Dividing proves

$$
\begin{aligned}
\overline D_{i,m}(e^{-s})
&=\frac{a^2v_m}{2}\frac{(10m-3)!}{(10m-1)!}s^2+O_{H,m}(s^3)\\
&=\frac{a^2m(m-1)}{648(10m-2)}s^2+O_{H,m}(s^3).
\end{aligned}
$$

Any fixed finite range of totals separately contributes $O_{H,m}(s^{10m})$ after normalization, so even its zero-divergence cases are covered. This is averaging over each label's own actual total distribution, not a chosen total or free conditional sample.

At every fixed $q$, every legal total has positive probability. Theorem 5.1 supplies positive divergence for sufficiently large totals and nonnegativity elsewhere, which proves positive averaged drift. The log-factor bound $|\log(G_1/G_0)|\le\log\mathcal R_m$ bounds each divergence and proves finiteness. Finally the block duration is $T+m$ with mean $m\mu_i(q)$, by Theorem 2.2. Since

$$
\frac1{m\mu_i(e^{-s})}=\frac{s}{10m}(1+O_H(s)),
$$

division gives

$$
\frac{a^2(m-1)}{6480(10m-2)}s^3+O_{H,m}(s^4)
=\frac{a^2(m-1)}{12960(5m-1)}s^3+O_{H,m}(s^4).
$$

The finite-record stationary initial wait is still paid; it is separately included in Theorem 7.2. The rate definition does not discard it from any finite record. $\square$

**Corollary 6.3 (Pair check, exact coefficient ratios and ordered limits).** At $m=2$ the formulas specialize to

$$
\begin{aligned}
v_2&=19/162,\\
d_{i,2}(n)&=\frac{19a^2}{324n^2}+O_H(n^{-3}),\\
\overline D_{i,2}(e^{-s})&=\frac{a^2}{5832}s^2+O_H(s^3),\\
I^{\mathrm{paid}}_{i,2}(e^{-s})&=\frac{a^2}{116640}s^3+O_H(s^4).
\end{aligned}
$$

These agree with the published pair interface of Theorem 22.2 and its paid duration $2\mu_i$. Write $c_{\rm proj}=a^2/64800$ for the selected unequal-nuisance converse coefficient of Theorem 22.5 and $c_{\rm known}=a^2/12960$ for the known-common-$q$ coefficient of equation (19.13). Exactly,

$$
\frac{c_m}{c_{\rm proj}}
=\frac{10(m-1)}{10m-2}=1-\frac4{5m-1},
\qquad
\frac{c_m}{c_{\rm known}}=\frac{m-1}{5m-1}.
$$

For finite $s$ the proved statements are asymptotic:

$$
\frac{I^{\mathrm{paid}}_{i,m}(e^{-s})}{a^2s^3/64800}
=1-\frac4{5m-1}+O_{H,m}(s),
\qquad
\lim_{m\to\infty}\lim_{s\downarrow0}
\frac{I^{\mathrm{paid}}_{i,m}(e^{-s})}{a^2s^3/64800}=1.
$$

Replacing the denominator by the inherited selected-pair rate $I_{\rm proj}(s)=c_{\rm proj}s^3+O_H(s^4)$ leaves the same ordered limit. Relative to the known-common-$q$ rate, the corresponding ordered limit is $1/5$.

Proof. Substitution of $m=2$ gives the displayed pair coefficients; no new pair result is claimed. Division of $c_m$ by the two positive constants gives the exact rational ratios. The first ratio is strictly below one for every finite $m\ge2$, equals $5/9$ at two, and increases to one, since $4/(5m-1)$ strictly decreases to zero. The second tends to $1/5$. Divide the fixed-$m$ expansion of Theorem 6.2 by $c_{\rm proj}s^3$ to obtain its $O_{H,m}(s)$ remainder. A denominator $c_{\rm proj}s^3(1+O_H(s))$ is positive for small $s$ and has the same inner limit. The identical argument applies to the known-common-$q$ rate with coefficient $c_{\rm known}$. These arguments take $s$ to zero first at each fixed $m$; they supply no joint $m=m(s)$ estimate or interchange of limits. $\square$

## 7. A lawful fixed-block observer and its paid mean

**Definition 7.1 (Exact rational threshold rule).** Fix $m\ge2$ and a rational $0<\alpha<1/2$, and set $b=2/\alpha>1$. Wait for the first actual tick. Partition all subsequent complete gaps into consecutive nonoverlapping blocks of exactly $m$, with no rejection of a block. Let $K_{j,r}=K_{(j-1)m+r}$ and $T_j=\sum_{r=1}^mK_{j,r}$. At the closing tick of block $j$ compute

$$
R_j=\frac{\prod_{r=1}^mH(K_{j,r})\,C_{0,m}(T_j)}
{\prod_{r=1}^mK_{j,r}^9\,C_{1,m}(T_j)}
=\frac{G_{1,m,T_j}(K_{j,1},\ldots,K_{j,m})}
{G_{0,m,T_j}(K_{j,1},\ldots,K_{j,m})}.
$$

Let $M_0=1$, $M_j=\prod_{v=1}^jR_v$, and

$$
J=\inf\{j\ge1:M_j\ge b\text{ or }M_j\le b^{-1}\}.
$$

At the upper boundary emit label one; at the lower boundary emit label zero. Equalities belong to their respective boundaries, which are disjoint. If no boundary is reached, continue reading. The products and thresholds are rational; the logarithms in the proof need not be computed. All full-family probability assertions concern the stated legal source histories.

**Theorem 7.2 (Full-family risks, pointwise finite stopping and exact paid identity).** The rule in Definition 7.1 satisfies

$$
\sup_{q\in(0,1)}\mathsf P_{0,q}(\text{label }1)\le\alpha/2,
\qquad
\sup_{q'\in(0,1)}\mathsf P_{1,q'}(\text{label }0)\le\alpha/2.
$$

For each fixed true $i,q$ it stops almost surely, and, writing $\ell_m=m\log(1+\delta)$,

$$
\mathbb E_{i,q}J\le
\frac{\log b+\ell_m}{\overline D_{i,m}(q)}<\infty.
$$

Its actual read count $L_m$ has the pathwise and mean identities

$$
\begin{aligned}
L_m&=1+\tau+\sum_{j=1}^{J}(T_j+m),\\
\mathbb E_{i,q}L_m&=1+\beta_i(q)+m\mu_i(q)\mathbb E_{i,q}J<\infty.
\end{aligned}
$$

For every fixed $H,m,\alpha$,

$$
\mathbb E_{i,e^{-s}}L_m=O_{H,m,\alpha}(s^{-3})
\quad(s\downarrow0).
$$

Proof. Use only the completed-block filtration

$$
\mathcal F_j=\sigma(\tau,K_1,\ldots,K_{jm}).
$$

Proposition 1.3 supplies independence of successive blocks and of the initial wait. Under any null nuisance, condition first on $T_j=n$: the $G_0$ expectation of $R_j=G_1/G_0$ is $\sum_{k\in\Omega_{m,n}}G_1(k)=1$. Averaging over that null's own total law preserves one, so $M_j$ is a mean-one nonnegative martingale under every $\mathsf P_{0,q}$. Under every $\mathsf P_{1,q'}$, the reciprocal factor has $G_1$ expectation one, making $M_j^{-1}$ such a martingale. No relation between $q$ and $q'$ is used.

For a finite horizon $N$, bounded stopping gives $\mathbb E_{0,q}M_{J\wedge N}=1$. On $\{J\le N,\text{label }1\}$ the value is at least $b$, and it is nonnegative elsewhere, so that event has probability at most $b^{-1}$. Increase $N$ to infinity. Apply the identical argument to the reciprocal under label one for an erroneous lower crossing. These are the displayed risk bounds, obtained before assuming integrability or termination of $J$.

Under true label $i$ put $Y_j=\log R_j$ and $Z_j=(2i-1)Y_j$. The oriented variables $Z_j$ are iid with mean $\overline D_{i,m}(q)>0$, by Theorem 6.2. Theorem 2.2 gives

$$
\mathcal R_m^{-1}\le R_j\le\mathcal R_m,\qquad |Z_j|\le\ell_m.
$$

Before exit the unsigned accumulated log score lies strictly between $-\log b$ and $\log b$; at exit its last increment has magnitude at most $\ell_m$. Consequently, for every finite $N$,

$$
\left|\sum_{j=1}^{J\wedge N}Z_j\right|\le\log b+\ell_m.
$$

Since $\{J\ge j\}\in\mathcal F_{j-1}$ and the next block is independent of that sigma-field, finite summation gives

$$
\mathbb E_{i,q}\sum_{j=1}^{J\wedge N}Z_j
=\overline D_{i,m}(q)\sum_{j=1}^N\mathsf P_{i,q}(J\ge j)
=\overline D_{i,m}(q)\mathbb E_{i,q}(J\wedge N)
\le\log b+\ell_m.
$$

Monotone convergence proves the claimed bound on $\mathbb EJ$; it also proves $J<\infty$ almost surely. Every gap and the initial wait are finite almost surely, so the same holds for the actual stopping read.

Set $B_j=T_j+m$. The pathwise read identity counts the initial tick once, every initial zero, and all $m$ closing ticks per block. Predictable inclusion, now with nonnegative durations, and Tonelli yield

$$
\begin{aligned}
\mathbb E_{i,q}\sum_{j=1}^{J}B_j
&=\sum_{j\ge1}\mathbb E_{i,q}[\mathbf1_{\{J\ge j\}}B_j]\\
&=\sum_{j\ge1}\mathsf P_{i,q}(J\ge j)\,m\mu_i(q)
=m\mu_i(q)\mathbb E_{i,q}J.
\end{aligned}
$$

This argument does not require a block's duration to be independent of that same block's score or decision. Adding $1+\mathbb E\tau$ proves the mean identity. At fixed $m\ge2$, the coefficient in Theorem 6.2 is positive, so $\overline D_{i,m}(e^{-s})$ is bounded below by a positive constant times $s^2$ for small $s$. Proposition 1.3 bounds $\mu_i$ and $\beta_i$ by constants times $s^{-1}$. The bound on $\mathbb EJ$ and the exact identity then give the stated $O(s^{-3})$ paid-read order. $\square$

The proof reuses the completed-pair martingale and predictable-cost mechanism of the supplier's Theorem 22.3, with $m$ gaps per block. It proves the needed block constants explicitly: $\mathcal R_m=(1+\delta)^m$ and $\ell_m=m\log(1+\delta)$ are finite for fixed $m$. The pair-specific inequality $(1+\delta)^2<2$ is not an arbitrary-$m$ inequality. In particular no pair-specific logarithm-approximation or workspace bound is transferred through it. Nor is $M_j$ the full likelihood ratio of the visible history for any fixed pair of opposing nuisance parameters. Holding it constant through a partially read block is not asserted to give a martingale in the finer bit filtration. Its decisions nevertheless are lawful bit-history stopping decisions because each is taken at an observed closing tick.

**Proposition 7.3 (The one-gap degeneracy).** For $m=1$, define the quantities of Section 2 using its single-part compositions. Then $G_{0,1,n}=G_{1,1,n}=1$, both conditional divergences and $I^{\mathrm{paid}}_{i,1}$ are zero, and the threshold rule with $b>1$ never stops.

Proof. A legal total $n$ determines the sole gap $K=n$, so both conditional laws are the same point mass. Exactly $w_n=c_n=r_n$ and hence every factor is one. The accumulated product remains one, strictly between the two boundaries. Thus $J=\infty$; the positive-drift and finite-mean assertions of Theorem 7.2 expressly require $m\ge2$. $\square$

## 8. Increasing actual horizons and arithmetic resources

**Theorem 8.1 (Conditional information on increasing paid horizons).** Fix $m\ge2$ and one true $i,q$. Consider indefinite acquisition using the same block partition, without stopping at a threshold. Define

$$
H_N=1+\tau+\sum_{j=1}^N(T_j+m),\qquad
S_N=\sum_{j=1}^NZ_j,\qquad H_0=1+\tau,\quad S_0=0,
$$

with $Z_j=(2i-1)\log R_j$. For an integer number of actual paid reads $W$, let $N(W)$ be the number of fully completed blocks by that read, with $N(W)=0$ before the first completed block. Then almost surely

$$
\frac{S_N}{H_N}\longrightarrow I^{\mathrm{paid}}_{i,m}(q),
\qquad
\frac{S_{N(W)}}W\longrightarrow I^{\mathrm{paid}}_{i,m}(q)
\quad(W\to\infty).
$$

Both the stationary initial acquisition and any partial final block are included in the denominator $W$.

Proof. The iid increments $Z_j$ are bounded, and the iid block durations have finite mean $m\mu_i(q)>0$. The ordinary iid strong laws give

$$
\frac{S_N}{N}\to\overline D_{i,m}(q),\qquad
\frac{H_N}{N}\to m\mu_i(q)
$$

almost surely, since the one-time wait $\tau$ is finite almost surely. This proves the first ratio. Every finite block is eventually completed and durations are positive, so $N(W)\to\infty$. For all sufficiently large $W$,

$$
H_{N(W)}\le W<H_{N(W)+1}.
$$

After division by $N(W)$, both bounds tend to $m\mu_i(q)$, using $(N(W)+1)/N(W)\to1$ for the upper one. Thus $N(W)/W\to1/(m\mu_i(q))$. Multiply this by the strong-law limit for $S_{N(W)}/N(W)$ to obtain the second conclusion. The incomplete final block has already been included through the actual value of $W$ in this squeeze. This is an increasing observation horizon, not a horizon limit applied to the single finite record of a fixed-$\alpha$ threshold rule. $\square$

**Proposition 8.2 (Finite rational preprocessing and growing exact arithmetic).** The rule of Definition 7.1 can be implemented using finite binary integer arithmetic, with no value or approximation of the true nuisance. Charge the preprocessing and storage of $H,m,C_{0,m},C_{1,m}$ and $b=2/\alpha$ separately. Let $B_{H,m}$ bound the bit length of these fixed model and polynomial descriptions, and $B_\alpha$ bound the supplied risk and threshold descriptions. On a finite path prefix of $L$ reads, let $J_L$ be its number of completed blocks, and set

$$
U_L=1+B_{H,m}+B_\alpha+\lceil\log_2(L+2)\rceil.
$$

After preprocessing, conservative upper bounds are

$$
\text{storage }O_{H,m}((J_L+1)U_L),\qquad
\text{online bit work }O_{H,m}\bigl(LU_L+(J_L+1)^2U_L^2\bigr).
$$

They include arithmetic workspace and all reads through an unfinished initial wait, gap or block. At a threshold stopping path $L=L_m$, one has $J_L=J$.

Proof. Lemma 3.1 and Corollary 3.2 give a finite exact rational construction of the two convolution polynomials on their full evaluation domain. All intermediate fractions, coefficient operations and coefficient storage used to construct them are preprocessing resources. Their fixed degrees are $10m-1$, and their legal values are positive. The construction makes no online enumeration of compositions necessary. Calculating the rational threshold from the supplied risk is another charged finite operation. No bound uniform in a varying $m$ or varying polynomial is asserted for preprocessing.

After clearing fixed coefficient denominators, evaluate $H$ and the two $C_{i,m}$ by Horner schemes and form the products in Definition 7.1 by integer arithmetic. At an acquired total $T_j\le L$, each factor's numerator and denominator have $O_{H,m}(U_L)$ bits: evaluation of a fixed-degree polynomial on an integer of $O(\log(L+2))$ bits increases length by at most the degree times that length, plus the coefficient-description length and a fixed bound for the number of terms. Taking $m$ products changes only the fixed-$m$ constant. Polynomial coefficient signs cause no denominator problem, since positive legal values were proved in Theorem 2.2.

Maintain positive integer numerator and denominator products for $M_j$ without fraction reduction. After $j$ factors they have $O_{H,m}(jU_L)$ bits. Compare against $b$ and $b^{-1}$ by cross multiplication of positive integers, resolving equality by the boundary convention. There is no rounding or exact-real comparison. Each fixed-degree factor evaluation costs $O_{H,m}(U_L^2)$ schoolbook bit work. Multiplication of a $jU_L$-bit accumulator by a $U_L$-bit factor, including threshold multiplication and comparison, costs $O_{H,m}((j+1)U_L^2)$. Summing over $j\le J_L$ proves the quadratic block term in the work bound.

The retained data comprise a first-tick flag, block phase, current zero count, at most $m$ current gap counts, their total, a block index, a read counter, model and threshold descriptions, and the two growing accumulator integers. The gap and read counters have at most $O(\log(L+2))$ bits at this prefix. Each read costs at most $O_{H,m}(U_L)$ counter work, even before the first tick or during an incomplete block. A constant number of large integer intermediates suffice for each product or comparison, so the same $O_{H,m}((J_L+1)U_L)$ bound includes their workspace. At a partially read block, the current counts are retained and all its observed bits are charged even though its factor is not yet included.

This exact-product implementation uses the rational-factor idea of the supplier's Proposition 22.6 and equation (22.53), together with the new polynomial preprocessing of Section 3. Its accumulation method is different from that proposition's dyadic-score controller. Here no logarithmic score approximation is performed, so there is no uncharged precision schedule; the exact products genuinely grow with the number of blocks. The special pair bound $U<2$ used for its logarithm series is not used here. A fixed number of integer registers is not a fixed-size exact real accumulator. No raw bit record, source-probability query or hidden clock is used. $\square$

**Proposition 8.3 (Optional finite cap and its accounting boundary).** If a supplied positive integer cap $W$ is imposed on Definition 7.1, give an ordinary boundary decision priority when its block closes on the last allowed read; otherwise emit a fixed default at timeout. Then each error under $\mathsf P_{i,q}$ is at most

$$
\alpha/2+\mathsf P_{i,q}(L_m>W).
$$

Use $U_W=1+B_{H,m}+B_\alpha+\lceil\log_2(W+2)\rceil$ in Proposition 8.2, charging the cap's description even on an early-stopping path. Every such prefix has $J_L\le\lfloor(W-1)/(2m)\rfloor$.

Proof. A wrong capped decision is contained in the union of a wrong uncapped decision and timeout. This gives the probability bound without reconditioning a block law on finishing before the deadline. A block costs at least $2m$ reads after its starting tick, since every gap has at least one zero. The initial acquisition costs at least one read. The stated deterministic block-count bound follows. Counters and arithmetic at a final closing tick, or counters in a partial interval at timeout, are included as in Proposition 8.2. This proposition supplies no sharp or uniform deadline constant. $\square$

These are pathwise arithmetic upper bounds. The mean-read order in Theorem 7.2 alone does not turn a nonlinear bound in $L$ and $J_L$ into an expected bit-operation endpoint order. No optimized storage, uniformly efficient preprocessing, finite-bit producer or physical elapsed-time bound follows. Producer dimension, observer storage, arithmetic work, read count and initialization are separate resource coordinates.

## 9. Inherited converse, scope and unanswered directions

**Definition 9.1 (Supplier correspondence and attribution).** The mathematical source used here is the published volume *Real renewal instruments and detector rank*, through Section 22. Its relevant interfaces and the contribution of the present volume are as follows.

| Source | Exact role and boundary |
| --- | --- |
| Theorems 11.5 and 15.2–15.5; equation (19.7) | The two actual degree-nine instruments, their own stationary initializations, the exact rational-center $H$, positivity and $1\le r_k\le1+\delta/k$. Their construction is inherited, not replaced by a scalar sampler or a different producer. |
| Theorem 17.4; equations (20.1) and (20.29) | The actual forward wait, iid gaps after the observed tick, means and stationary read convention. Proposition 1.3 states their exact correspondence. |
| Definition 22.1 and Theorem 22.2 | The all-sum pair law and its two conditional divergence expansions. At $m=2$, $C_{i,2}(n)=A_i(n)$ and $G_{i,2,n}(k,n-k)=c_{i,n}(k)$ in that notation. Corollary 6.3 recovers those results as a consistency specialization. |
| Theorem 22.3 and Proposition 22.6 | The completed-pair martingale, predictable read identity and finite-arithmetic controller. Theorem 7.2 justifies the fixed-block version; Proposition 8.2 charges its growing exact product rather than importing the pair's dyadic workspace estimate. |
| Lemma 20.6 and Theorem 22.5 | The unequal-nuisance converse on actual stationary histories, with initialization and an unbounded tilt controlled in the supplier. Only its stated rate and decision inequality are used for comparison here. |
| Equation (19.13) | The separate known-common-$q$ rate coefficient $a^2/12960$. It is not a nuisance-free composite experiment. |
| Present Sections 2–8 | Repository-derived fixed-$m$ convolution, inverse moments through total order four, endpoint control, variance, both KL remainders, averaging, paid rate, block observer and increasing-horizon law. These are handwritten derivations, not a claim of worldwide priority. |

Conditional cancellation in exponential families, finite differences, beta integrals, Taylor remainder bounds, nonnegative-martingale crossing bounds, predictable summation and iid strong laws are the classical methods instantiated in the proofs. Their use here is supported by the displayed arguments and the credited supplier interfaces. No additional external-literature coverage or independently verified mathematical supplier is claimed.

**Corollary 9.2 (Comparison to the selected unequal-nuisance experiment).** For small $s>0$ the inherited converse selects

$$
q_0=e^{-s},\qquad q_1=e^{-s+(a/90)s^2},
$$

with each source retaining its own stationary initializer. Write

$$
\pi_{i,q}(t)=S_{i,q}(t)/\mu_i(q),\qquad
\Lambda_{i,q}(k,t)=f_{i,q}(k)/\mu_i(q)\quad(0\le t\le k),
$$

and $C(q_0,q_1)=D(\pi_{0,q_0}\Vert\pi_{1,q_1})$. Theorem 22.5 of the supplier proves

$$
\begin{aligned}
D(f_{0,q_0}\Vert f_{1,q_1})&=\frac{a^2}{6480}s^2+O_H(s^3),\\
I_{\rm proj}(s)&=\frac{D(f_{0,q_0}\Vert f_{1,q_1})}{\mu_0(q_0)}
=\frac{a^2}{64800}s^3+O_H(s^4),\\
0\le C(q_0,q_1)&\le D(\Lambda_{0,q_0}\Vert\Lambda_{1,q_1})
=\frac{a^2}{8100}s^2+O_H(s^3).
\end{aligned}
$$

For every integer cap $W\ge1$, its actual-history inequality is

$$
D(\mathsf P_{0,q_0}^W\Vert\mathsf P_{1,q_1}^W)
\le C(q_0,q_1)+(W-1)I_{\rm proj}(s).
$$

A decision with both errors at most $\alpha\in(0,1/2)$ for this selected pair must therefore satisfy

$$
(1-2\alpha)\log\frac{1-\alpha}{\alpha}
\le C(q_0,q_1)+(W-1)I_{\rm proj}(s).
$$

Early stopping and common independent randomization are included in that inherited inequality. The rate in this volume obeys

$$
\lim_{s\downarrow0}\frac{I^{\mathrm{paid}}_{i,m}(e^{-s})}{I_{\rm proj}(s)}
=1-\frac4{5m-1},\qquad
\lim_{m\to\infty}\lim_{s\downarrow0}
\frac{I^{\mathrm{paid}}_{i,m}(e^{-s})}{I_{\rm proj}(s)}=1.
$$

Proof. The supplier's Lemma 20.6 gives the actual-history projection and Bernoulli-decision inequalities at unequal parameters; its Theorem 22.5 proves the displayed gap and initialization expansions. These are credited premises, not deductions from a common-$q$ bounded likelihood ratio. For small enough $s$, $s-(a/90)s^2>0$, so both selected parameters are legal. The fixed-block comparisons are exactly Corollary 6.3 after division by the positive leading coefficient of $I_{\rm proj}$. They compare attainable conditional information per paid read with that selected converse coefficient. They do not infer sharp stopping or deadline optimality from a rate ratio. $\square$

**Proposition 9.3 (Common finite support and zero-error boundary).** Across any opposing nuisance pair in these two families, finite binary histories have the same support: all words without adjacent ones have positive probability, and words with adjacent ones have probability zero. Consequently no rule can be error-free under both laws while emitting a terminal label at a finite time with positive probability under either, even with a common independent random seed.

Proof. The cylinder formula of Proposition 1.3 contains a zero internal factor exactly when an internal gap is zero. Every positive gap factor and every boundary tail is positive; every finite all-zero cylinder is positive as well. Thus the finite restrictions have the same null sets. Product with a common independent seed preserves this equivalence. For any specified finite time and terminal label, zero error under the opposite law requires the corresponding event to have zero probability there and hence under both laws. The countable union over times and the two labels remains null. This is the inherited support argument of Corollary 17.5 applied to independent nuisance values. Finite-confidence stopping remains the separate conclusion of Theorem 7.2. $\square$

**Definition 9.4 (Remaining questions and their missing steps).** A joint limit with $m=m(s)\to\infty$ is not proved. It would require quantitative bounds uniform in $m$ for the convolution quotient remainders, inverse moments, product and Taylor errors, and the subsequent total averaging. The fixed-$m$ constants and the sequential limit alone do not supply such bounds.

Sharp expected stopping, minimax or deadline constants remain outside the result. A rate coefficient and a bounded-overshoot upper estimate do not determine the stopped-score distribution or optimality among all composite observers. Such a claim would require a matching stopping or deadline theorem on the same paid stationary histories, with the nuisance quantifiers and initialization retained. The published Section 22 deadline order is an inherited result and is not a new sharp constant here.

Expected bit-operation endpoint rates and optimal storage are not established by Proposition 8.2. Its nonlinear pathwise bounds would need appropriate quantitative stopped-length and block-count moment estimates, as well as a justified arithmetic implementation analysis in that limiting regime. Fixed-$m$ preprocessing is finite and charged; a varying-$m$ efficiency claim would require its own bound.

The block observer neither estimates $q$ nor performs empirical maximum likelihood. No exact scalar probability-query capacity, kernel or hidden-state identification, unrestricted alternative-model certification, finite-bit producer, physical realization, uniform cost over all nuisance values, worldwide originality or completion of a broader research goal is asserted. The known-common-$q$ coefficient remains a different benchmark, whose limiting comparison here is exactly one fifth. The actual-source constructions and all ordinary mathematical proofs retain their stated handwritten evidence status.

## 追加锚（本行以下为增补区）
