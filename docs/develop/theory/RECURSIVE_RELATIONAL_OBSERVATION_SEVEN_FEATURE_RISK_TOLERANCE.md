# Seven-feature risk tolerance on five local boxes

## 1. Complete laws, common flows and the finite diagnostic

**Convention 1.1 (the original source).** Fix a probability prior supported
exactly on $\{1,2,3\}$, with all three masses positive. The parameters are
$(m,d,\ell_{\rm src},n)=(2,1,2,4)$ and the source rates are
$r_1=a=1/3$, $r_2=b=2/5$, $r_3=3/8$. One $K$ is drawn before the first
paid Read. Conditional on this same $K$, all seed and payload letters are
independent with alpha probability $r_K$. Equal seed pairs remain two paid
rejections and both unequal accepted seeds remain. At p, alpha completes
marker 0 and beta suspends; at suspension, alpha returns to p and beta
completes marker 1. The third record is written before its latch in that
same update. Fourth completion enables only its matching original Stop.
Pending and delivered terminals permit no Read.

The original control $C_0$ retains the parser, both seeds, selectors, marker
words and prefixes, bare and held $B,Q^+,Z$ fields, write/latch flags,
permissions, completion and delivery. All positive finite paid rejection,
partial-parse and return histories remain. The current-record renderer $I_c$
retains every future letter and inserts its original operation block. Its
inverse reads the letters; it preserves complete-law TV and deletion of
the next operation with its block, including infinite noncompletion.
Initialization is source-independent and synthesis uses the same acquired
update kernels. These are the supplied interfaces [PAIR, §11.1; PAID,
Definitions 1.1–2.1 and Lemma 2.1.1].

**Definition 1.2 (the unchanged Borel domain).** Put

$$
w_{j,0}=(\beta\alpha)^j\alpha,\qquad
w_{j,1}=(\beta\alpha)^j\beta\beta,\qquad t_r=r(1-r).
$$

The countable complete carrier $\Omega_p$ contains these words and
$\infty_p$. The carrier $\Omega_\beta$ contains beta, all
$\alpha w_{j,c}$ and $\infty_\beta$. All subsets are measurable. The native
probability laws are

$$
P_{p,r}(w_{j,0})=rt_r^j,\quad
P_{p,r}(w_{j,1})=(1-r)^2t_r^j,\quad
P_{\beta,r}=(1-r)\delta_\beta+r\alpha P_{p,r},
\tag{1.1}
$$

with zero infinite masses. With $\lambda=4/15$, set

$$
\begin{aligned}
T_p(j)&=\{w_{n,c}:n\ge j,\ c=0,1\}\cup\{\infty_p\},\\
T_\beta(j)&=\{\alpha w_{n,c}:n\ge j,\ c=0,1\}\cup\{\infty_\beta\},\\
\mathcal K_p&=\{Q\in\operatorname{Prob}(\Omega_p):
 a\le Q(\alpha)\le b,\ Q(T_p(j))\le\lambda^j\ (j\ge0)\},\\
\mathcal K_\beta&=\{W\in\operatorname{Prob}(\Omega_\beta):
 a\le1-W(\beta)\le b,\ W(T_\beta(j))\le b\lambda^j\ (j\ge0)\}.
\end{aligned}
\tag{1.2}
$$

These are the compact metric complete-law spaces of [PAIR, Lemma 11.1],
with TV topology. Their infinite masses vanish by the tail bounds;
infinite coordinates are nevertheless retained. Write

$$
u(Q)=Q(\alpha),\quad v(W)=1-W(\beta),\quad
\mathcal R_B(Q)=\frac{Q(\beta\,\cdot)}{1-u(Q)},\quad
\mathcal R_A(W)=\frac{W(\alpha\,\cdot)}{v(W)}.
\tag{1.3}
$$

A compatible pair consists of Borel probability measures $\Gamma_B$ on
$\mathcal K_p\times\mathcal K_\beta$ and $\Gamma_A$ on the reversed
product, with the same unweighted phase marginals

$$
(\Gamma_B)_1=(\Gamma_A)_2=\nu_p,\qquad
(\Gamma_B)_2=(\Gamma_A)_1=\nu_\beta.
\tag{1.4}
$$

Their disintegrations satisfy, almost surely at the respective inputs,

$$
\mathcal R_B(Q)=\int W\,B(Q,dW),\qquad
\mathcal R_A(W)=\int Q\,A(W,dQ).
\tag{1.5}
$$

These are full measure equalities conditioned on the entire input
descriptor, equivalently coordinate equalities against every bounded
Borel input test, including the infinite coordinate. Denote this original
domain by $\mathfrak C$. The factors $1-u,v$ belong to synthetic residuals,
not to the marginals in (1.4).

**Definition 1.3 (five local boxes).** The subclass used in the main
theorem requires exactly these additional almost-sure restrictions:

$$
\begin{array}{c|c}
\nu_p\text{-almost surely}&
 \dfrac9{25}\le Q(w_{0,1})\le\dfrac49,\quad
 Q(w_{2,1})\le\dfrac{16}{729},\quad
 Q(w_{3,1})\le\dfrac{1944}{390625}\\[2mm]
\nu_\beta\text{-almost surely}&
 \dfrac{18}{125}\le W(\alpha w_{0,1})\le\dfrac4{27},\quad
 \dfrac8{243}\le W(\alpha w_{1,1})\le\dfrac{108}{3125}.
\end{array}
\tag{1.6}
$$

No other coordinate box, finite support, reversibility, deterministic
successor, mixing or recurrence hypothesis is imposed in Theorem 2.1.

**Definition 1.4 (the seven features and the finite risk).** Use exactly
[SEVEN, Definition 2.1]:

$$
\begin{aligned}
f(Q)&=(Q(w_{0,1}),Q(w_{1,1}),Q(w_{2,1})),\\
g(W)&=(W(\beta),W(\alpha w_{0,1}),W(\alpha w_{1,1}),W(\alpha w_{2,1})),\\
V&=\int\|f(Q)-f(\mathcal R_A(W))\|_2^2\,d\Gamma_A
 +\int\|g(W)-g(\mathcal R_B(Q))\|_2^2\,d\Gamma_B.
\end{aligned}
\tag{1.7}
$$

Features evaluate arbitrary probability laws on the indicated carrier, so
(1.7) is defined even before invoking (1.5). Put

$$
\begin{gathered}
E_p=\{w_{0,1},w_{1,1},w_{2,1}\},\quad
E_\beta=\{\beta,\alpha w_{0,1}\},\quad
\kappa=\frac{1116529}{806625},\quad \zeta=-\frac{151298}{268875},\\
M_p=\frac{11758471}{22781250},\quad M_\beta=\frac{5261}{6750},\quad
M_p=\kappa M_\beta+\zeta,\\
\eta=\left|\int Q(E_p)d\nu_p-M_p\right|
 +\kappa\left|\int W(E_\beta)d\nu_\beta-M_\beta\right|,\\
\rho_p=\frac{1116529}{22781250},\quad
\delta_3=\frac{344076471}{6553600000000},\quad C=10^{16}.
\end{gathered}
\tag{1.8}
$$

The partition $\Pi$ has the three cells $E_p$, $\{w_{3,1}\}$ and their
complete complement, which includes $\infty_p$. For $R=P_{p,3/8}$ define

$$
L_\Pi=\int\operatorname{TV}(\Pi_\#Q,\Pi_\#R)\,d\nu_p(Q).
\tag{1.9}
$$

TV is inside the integral. All features, residual coordinates and losses
above are bounded Borel functions. In particular $\eta,V,L_\Pi$ are finite.

## 2. Uniform explicit tolerance

**Theorem 2.1 (seven-feature quantitative separation).** Every compatible
Borel pair of Definition 1.2 satisfying the five local boxes (1.6) obeys

$$
L_\Pi+C(\eta+\sqrt V)\ \ge\ \rho_p+\frac{\delta_3}{2}.
\tag{2.1}
$$

In fact the proof gives the same assertion with $C$ replaced by
$500000000000$. The stated $10^{16}$ requires no restriction to a
small-error neighborhood. The result concerns one pair and its own two
flows; no separately chosen minimizers are combined.

The proof occupies §§3–5. Its new source-specific step is propagation of
the seven edge errors through (1.6), clipping, the stationary four-rate
envelope and the configuration risk. The zero-variance exclusion, scalar
envelope, endpoint gap, matrix evaluation and installation interface are
supplied results and are not additional contributions here.

**Corollary 2.2 (necessary conditions in the original problem).** On
$\mathfrak C$ retain the original objective

$$
\mathcal J=\max_{s=p,\beta;\ k=1,2,3}
 \left\{\int\operatorname{TV}(D_s,P_{s,r_k})d\nu_s-\rho_s\right\},
\quad D_p=Q,\ D_\beta=W,\quad \rho_\beta=\frac{239}{6750}.
\tag{2.2}
$$

Every pair with $\mathcal J=0$ satisfies

$$
V\ge\left(\frac{\delta_3}{2C}\right)^2>0.
\tag{2.3}
$$

On the class with both full endpoint boxes, for all complete atoms at
both phases, one has

$$
\frac{\delta_3}{2}
 \le [1+C(1+\kappa)]\mathcal J+C\sqrt V.
\tag{2.4}
$$

Proof. The endpoint triangle identity [PAIR, §11.8] supplies both full
boxes and both exact means at $\mathcal J=0$. They imply (1.6) and
$\eta=0$. Partition contraction gives
$L_\Pi\le\int\operatorname{TV}(Q,R)d\nu_p\le\rho_p$, hence (2.3).
For any fully boxed pair, the endpoint coordinate signs are fixed. Writing
$m_s=\int D_s(E_s)d\nu_s$, its two endpoint losses are
$P_{s,a}(E_s)-m_s$ and $m_s-P_{s,b}(E_s)$, whose maximum is
$\rho_s+|m_s-M_s|$. Consequently
$\eta\le(1+\kappa)\mathcal J$ and
$L_\Pi\le\rho_p+\mathcal J$. Substitute these two upper bounds into
(2.1). This proves (2.4). $\square$

Zero $\mathcal J$ is zero excess above the nonzero phase baselines.
Both full boxes, both means and both depth-3 budgets remain requirements
of the original zero face. Neither (2.3) nor (2.4) decides
$j_c=\min_{\mathfrak C}\mathcal J=0$ versus $j_c>0$.

## 3. From edge errors to a clipped stationary envelope

**Lemma 3.1 (one stationary path and finite product errors).** Set
$\epsilon=\sqrt V$. There is a stationary analysis path

$$
W_0\xrightarrow{A}Q_0\xrightarrow{B}W_1
 \xrightarrow{A}Q_1\xrightarrow{B}W_2\longrightarrow\cdots
\tag{3.1}
$$

whose two edge laws are the original $\Gamma_A,\Gamma_B$. Write
$u_t=u(Q_t)$, $v_t=v(W_t)$, $h_n(t)=Q_t(w_{n,1})$ and $c_t=h_0(t)$.
Define

$$
x_t=\frac{v_tc_t}{1-v_t},\qquad
y_t=\max\{\ell,\min\{L,x_t\}\},\qquad
\ell=\frac29,\quad L=\frac6{25}.
\tag{3.2}
$$

Then, at every time,

$$
\frac9{50}\le x_t\le\frac8{27}<\frac3{10},\qquad
\mathbb E|x_t-y_t|\le20\epsilon,
\tag{3.3}
$$

and for $n=1,2,3$,

$$
\mathbb E\left|h_n(t)-c_t\prod_{j=1}^n x_{t+j}\right|\le3\epsilon,
\qquad
\mathbb E\left|h_n(t)-c_t\prod_{j=1}^n y_{t+j}\right|\le70\epsilon.
\tag{3.4}
$$

Proof. Compact metric spaces admit Borel disintegrations. Starting with
$W_0\sim\nu_\beta$ and using the two disintegrations gives the path by
the usual iterated-kernel construction. Both identities (1.4) give its
stationarity under one complete A-B step. Countably many almost-sure
conditions can be imposed simultaneously along this forward path.
This construction supplies neither an inverse nor a reversible kernel.

For $0\le n\le2$ set

$$
\begin{aligned}
a_n(t)&=h_n(t)-W_t(\alpha w_{n,1})/v_t,\\
b_*(t)&=1-v_{t+1}-c_t/(1-u_t),\\
b_n(t)&=W_{t+1}(\alpha w_{n,1})-h_{n+1}(t)/(1-u_t).
\end{aligned}
\tag{3.5}
$$

Each of these seven errors has expected absolute value at most
$\epsilon$, by Cauchy–Schwarz and (1.7). They need not vanish and are
not independent. Put $d_t=1-u_t$ and $k_t=d_tv_{t+1}\le\lambda$.
The definitions give the exact identities

$$
\begin{aligned}
c_t&=d_t(1-v_{t+1})-d_tb_*(t),\\
h_n(t)&=k_th_{n-1}(t+1)-k_ta_{n-1}(t+1)-d_tb_{n-1}(t),
 \quad 1\le n\le3,\\
k_tc_{t+1}-c_tx_{t+1}&=d_tb_*(t)x_{t+1}.
\end{aligned}
\tag{3.6}
$$

The first box and $a\le v_t\le b$ give the pointwise bounds for $x_t$.
If $r_n(t)=h_n(t)-c_t\prod_{j=1}^n x_{t+j}$, then $r_0=0$ and (3.6)
implies

$$
\mathbb E|r_n(t)|
 \le\lambda\mathbb E|r_{n-1}(t+1)|
 +\left(\lambda+\frac23+\frac23(3/10)^n\right)\epsilon.
\tag{3.7}
$$

Induction gives $\mathbb E|r_n|\le3\epsilon$ for $1\le n\le3$:
the parenthesis is at most $17/15$ and
$3\lambda+17/15<3$. This uses only the displayed seven coordinates.

Let $s_n(t)=W_t(\alpha w_{n,1})$. The two suspended boxes give
$s_0\ge18/125$ and $s_1/s_0\in[\ell,L]$. Also

$$
\mathbb E|s_0-v_tc_t|\le\frac25\epsilon,\qquad
\mathbb E|s_1-v_tc_tx_{t+1}|\le\frac85\epsilon.
\tag{3.8}
$$

The second bound follows from $s_1=v_t(h_1-a_1)$ and the first bound
in (3.4). Consequently

$$
\mathbb E\left|x_{t+1}-\frac{s_1(t)}{s_0(t)}\right|
 \le\frac{125}{18}\left(\frac85+\frac3{10}\frac25\right)\epsilon
 \le20\epsilon.
\tag{3.9}
$$

Projection onto $[\ell,L]$ reduces distance to this ratio. Stationarity
gives (3.3), including time zero. Telescoping a product of $n$ factors
in $[0,3/10]$ bounds its change by the sum of the factor changes.
Since $c_t\le1$, the additional expected error is at most
$20n\epsilon\le60\epsilon$. Adding (3.7) proves the second inequality
in (3.4). $\square$

**Lemma 3.2 (quantitative envelope slack).** Set

$$
\begin{gathered}
G=\frac9{25},\quad T=\frac{16}{729},\quad q=\frac{1944}{390625},\quad
d_0=\frac{2341664383}{41527474875}>\frac1{20},\\
U(Y)=\min\{T/(y_1y_2),q/(y_1y_2y_3)\},\qquad Y=(y_0,y_1,y_2,y_3),\\
H(c,Y)=c(1+y_1+y_1y_2)-\kappa\frac{c(1+y_0)}{c+y_0}-\zeta,\\
F(Y)=H(U(Y),Y),\quad \psi(t)=F(t,t,t,t),\quad
c'=\min\{c_0,U(Y)\},\quad d=U(Y)-c',\\
S=\eta+40000\epsilon.
\end{gathered}
\tag{3.10}
$$

Then $c',U(Y)\in[G,4/9]$, $d\ge0$, and

$$
\mathbb E[-\psi(y_0)]+\frac12\mathbb E(y_1-y_0)^2+d_0\mathbb E d\le S.
\tag{3.11}
$$

Proof. On $[\ell,L]^4$, $G\le U\le4/9$, as supplied in
[REV, (16.22)]. The p boxes at indices 2 and 3 and (3.4) give

$$
\mathbb E(c_0-U)_+
 \le70(\ell^{-2}+\ell^{-3})\epsilon\le8000\epsilon.
\tag{3.12}
$$

Indeed the positive part of $c_0$ minus the minimum of the two caps is
at most the sum of the positive excesses over the individual caps.
Multiply each by its positive product denominator and use
$h_2(0)\le T$, $h_3(0)\le q$.

Let $\mathcal D=\int Q(E_p)d\nu_p-\kappa\int W(E_\beta)d\nu_\beta-\zeta$.
The second inequality of (3.4) gives

$$
\mathbb E|Q_0(E_p)-c_0(1+y_1+y_1y_2)|\le140\epsilon.
\tag{3.13}
$$

The identity $c(1+x)/(c+x)=1-v+vc$ holds for $x=vc/(1-v)$.
On $G\le c\le4/9$, $9/50\le x\le3/10$, its derivative in $x$ has
absolute value at most $4$. Together with (3.3) and (3.8) this gives

$$
\mathbb E\left|W_0(E_\beta)-\frac{c_0(1+y_0)}{c_0+y_0}\right|
 \le81\epsilon.
\tag{3.14}
$$

Thus $|\mathcal D-\mathbb E H(c_0,Y)|\le400\epsilon$, using
$\kappa<2$. On the entire segment between $c'$ and $U$, and also between
$c'$ and $c_0$, direct differentiation gives

$$
d_0\le \partial_cH(c,Y)
 =1+y_1+y_1y_2-\kappa\frac{y_0(1+y_0)}{(c+y_0)^2},
\qquad |\partial_cH(c,Y)|\le4.
\tag{3.15}
$$

The lower bound follows by replacing its positive terms by
$1+\ell+\ell^2$, its numerator by $\kappa L(1+L)$, and its denominator
by $(G+\ell)^2$. This is exactly $d_0$. The upper bound follows from
the same ranges. Therefore

$$
\mathcal D\le\mathbb EF(Y)-d_0\mathbb Ed+32400\epsilon.
\tag{3.16}
$$

Here $F(Y)-y_0y_1$ is precisely the supplied algebraic function
[REV, (16.21)–(16.25)]. Its coordinate-clipped extension is bounded
continuous and supermodular. All $y_t$ have the same marginal by
stationarity, so the bounded right-continuous comonotonic comparison
[CW, Definition 3(iii), Proposition 6] gives

$$
\mathbb EF(Y)\le\mathbb E\psi(y_0)
 -\tfrac12\mathbb E(y_1-y_0)^2.
\tag{3.17}
$$

Only the algebraic cube and equal-marginal hypotheses are needed here;
the deterministic-successor premise of REV Theorem 16.2 is not invoked.
Finally $\mathcal D\ge-\eta$ by (1.8). Combining this with (3.16)–(3.17)
and $32400\le40000$ proves (3.11). $\square$

## 4. Endpoint distance and finite-law stability

**Lemma 4.1 (a linear bound at both zeros).** For all $t\in[\ell,L]$,

$$
-\psi(t)\ge\frac1{2000}\operatorname{dist}(t,\{\ell,L\}).
\tag{4.1}
$$

Proof. Use the supplied exact numerator bounds [REV, (15.13)–(15.20)].
Let $h=q/T\in(\ell,L)$. On the diagonal in its LL rectangle set
$X=(t-\ell)/(h-\ell)$; on the HH rectangle set $X=(t-h)/(L-h)$.
The respective positive denominators and numerator bounds are

$$
\begin{array}{c|c|c}
t\text{ range}&d(t)&-N(t)\text{ lower bound}\\ \hline
[\ell,h]&2t^2(T+t^3)^2&17674\,10^{-12}[1-(1-X)^8]\\
[h,L]&2t^4(q+t^4)&26733\,10^{-12}(1-X^8).
\end{array}
\tag{4.2}
$$

Both denominators are at most $1/1000$: replace $t$ by $L$ and compare
the positive rational numbers. On $[0,1]$, $1-(1-X)^8\ge X$ and
$1-X^8\ge1-X$. With $\Delta=L-\ell=4/225$, the lower bound in either
row is at least

$$
\frac{17674}{10^9\Delta}\operatorname{dist}(t,\{\ell,L\})
 \ge\frac1{2000}\operatorname{dist}(t,\{\ell,L\}).
\tag{4.3}
$$

This includes the seam and both endpoints. The coefficient conversion and
partition of unity underlying the supplier are the ordinary Bernstein
facts [BSCA, §3.1, (3.7), Lemma 3.2]; no general positivity theorem beyond
those facts is needed. $\square$

**Lemma 4.2 (one endpoint comparison for the three-cell law).** Let $z_t$
be the nearest of $\ell,L$ to $y_t$, with ties assigned to $\ell$.
Write $r(z_t)=a$ or $b$, respectively. On the same analysis path,

$$
D_\Pi:=\mathbb E\operatorname{TV}
 (\Pi_\#Q_0,\Pi_\#P_{p,r(z_0)})
 \le10^6S+10^5\epsilon.
\tag{4.4}
$$

Proof. Put $e_t=|y_t-z_t|$. From (3.11) and (4.1),

$$
\mathbb Ee_t\le2000S,\qquad
\mathbb E(y_{t+1}-y_t)^2\le2S,\qquad \mathbb Ed\le20S.
\tag{4.5}
$$

For consecutive rounded values that differ, either
$e_t+e_{t+1}\ge\Delta/2$, or
$|y_{t+1}-y_t|\ge\Delta/2$. Thus, pointwise also when the rounded values
agree,

$$
\Delta\mathbf1_{\{z_{t+1}\ne z_t\}}
 \le\frac4\Delta(y_{t+1}-y_t)^2+2(e_t+e_{t+1}).
\tag{4.6}
$$

Since $|y_{t+1}-y_t|\le e_t+e_{t+1}
+\Delta\mathbf1_{\{z_{t+1}\ne z_t\}}$, (4.5) gives

$$
\mathbb E|y_{t+1}-y_t|\le(8/\Delta+12000)S\le13000S.
\tag{4.7}
$$

Consequently, for $j=1,2,3$,

$$
\mathbb E|y_j-z_0|\le(13000j+2000)S,
\quad
\sum_{j=1}^3\mathbb E|y_j-z_0|\le84000S.
\tag{4.8}
$$

The minimum defining $U$ switches at the fixed seam $y_3=h$.
In either branch every active partial derivative has magnitude
$U/y_j\le(4/9)/\ell=2$. At the seam the formulas coincide. Integration
on coordinate segments therefore makes $U$ globally $2$-Lipschitz for
the sum of the changes in coordinates 1, 2 and 3. Its endpoint diagonal
values are $c_a=4/9$ and $c_b=9/25$. From (3.12), (4.5) and (4.8),

$$
\mathbb E|c_0-c_{r(z_0)}|\le8000\epsilon+168020S.
\tag{4.9}
$$

For the $E_p$ coordinate, (3.13), $1+y_1+y_1y_2\le2$ and
$(1+y_2)|y_1-z_0|+z_0|y_2-z_0|
\le2|y_1-z_0|+|y_2-z_0|$ imply

$$
\mathbb E|Q_0(E_p)-P_{p,r(z_0)}(E_p)|
 \le16140\epsilon+394040S.
\tag{4.10}
$$

For the $w_{3,1}$ coordinate, telescope the three factors and use
(3.4), (4.8) and (4.9) to obtain

$$
\mathbb E|h_3(0)-P_{p,r(z_0)}(w_{3,1})|
 \le8070\epsilon+252020S.
\tag{4.11}
$$

For normalized three-cell laws whose first two coordinate differences
are $A,B$, their TV is $(|A|+|B|+|A+B|)/2\le|A|+|B|$.
The remaining coordinate includes infinity and is fixed by normalization,
not deleted. Adding (4.10)–(4.11) gives
$D_\Pi\le24210\epsilon+646060S$, which implies (4.4). All rounded
variables are Borel functions; their coupling to $Q_0$ is this one path,
not an independently chosen endpoint fit. $\square$

## 5. The midpoint and the risk separator

**Proof of Theorem 2.1.** Let $\theta=\Pr(z_0=L)$. This is an analysis
weight, not a runtime register. Since
$P_{p,a}(E_p)-P_{p,b}(E_p)=2\rho_p>1/11$, event contraction and (4.4)
give

$$
|\theta-1/2|\le\frac{\eta+D_\Pi}{2\rho_p}
 \le11(\eta+D_\Pi).
\tag{5.1}
$$

For clarity the three exact projected laws are

$$
\begin{array}{c|ccc}
r&E_p&w_{3,1}&\text{complete remainder}\\ \hline
1/3&412/729&32/6561&2821/6561\\
2/5&7299/15625&1944/390625&206206/390625\\
3/8&132025/262144&84375/16777216&8243241/16777216.
\end{array}
\tag{5.2}
$$

The first and third coordinates of the third row lie between those of
the endpoint rows. Its second coordinate exceeds both endpoints; the
upper endpoint there is the b row and the excess is $\delta_3$.
Coordinatewise absolute values therefore give exactly

$$
\begin{aligned}
\operatorname{TV}(\Pi_\#P_{p,a},\Pi_\#P_{p,b})&=2\rho_p,\\
\tfrac12\operatorname{TV}(\Pi_\#P_{p,a},\Pi_\#R)
 +\tfrac12\operatorname{TV}(\Pi_\#P_{p,b},\Pi_\#R)
 &=\rho_p+\delta_3/2.
\end{aligned}
\tag{5.3}
$$

This is the supplied endpoint gap, now on the specified three-cell
partition. No estimate on omitted individual atoms is needed.

Apply the reverse triangle inequality separately at each configuration
on the path and then integrate. Each fixed-target TV lies in $[0,1]$,
so changing the endpoint weight from $1/2$ to $\theta$ changes its
average by at most $|\theta-1/2|$. Equations (5.1)–(5.3) yield

$$
L_\Pi\ge\rho_p+\delta_3/2-12D_\Pi-11\eta.
\tag{5.4}
$$

Finally (4.4) and $S=\eta+40000\epsilon$ give

$$
12D_\Pi+11\eta
 \le12000011\eta+480001200000\epsilon
 \le500000000000(\eta+\epsilon).
\tag{5.5}
$$

Since $\epsilon=\sqrt V$ and $500000000000<10^{16}$, this proves the
asserted coefficient. Every estimate is global, so large $\eta$ or $V$
requires no additional case. $\square$

## 6. Offline application to one supplied complete installation

**Definition 6.1 (authenticated input, not an acquisition oracle).** An
application input is one already supplied finite rational period-one
installation $\mathcal I$. It includes its complete original control,
source-independent initialization, full emission and update programs,
finite label sets $X,Y$, rational arrays
$(\pi,\tau,B,A,u,v)$, representations of the installed numbers, and
its original record renderer. The authentication requirement is a supplied
equality between those arrays and this same program at its returned cuts,
with exactly PAID Definition 2.1's latch and product-update behavior. In
particular it certifies

$$
\pi_x,\tau_y>0,\quad \pi B=\tau,\quad \tau A=\pi,\quad
a\le u_x,v_y\le b,
\tag{6.1}
$$

stochasticity and normalization, rather than merely a table with similar
output statistics. The input also identifies the original fixed prior;
no prior posterior is made readable. Zero-row labels may first be removed
only after checking support closure. No inference of these input premises
from a partial trace, a digest alone, or an unknown program is included.

For a mathematical installation specified by the complete product program
below, authentication is equality to that specification. For an external
device it is an additional premise about that device, not evidence furnished
by this volume. The analysis never replaces the installed program by a
different table after seeing its risks.

**Proposition 6.2 (lawful exact supplied-table evaluation).** For one
input $\mathcal I$ of Definition 6.1, the five boxes, $\eta,V,L_\Pi$ and
the inequality (2.1) have a finite exact rational evaluation, except that
$\sqrt V$ may be kept as a symbolic square root. When the five boxes hold,
Theorem 2.1 applies to its actual own-law pair with total variation taken
separately for each configuration and then averaged over the configuration
law. No source Read or stochastic sample is required by this offline
evaluation after the authenticated input has been supplied.

Proof. With column vectors and $D=\operatorname{diag}(1-u)$,
$Z=\operatorname{diag}(v)$, use the supplied same-update recursions

$$
H=DBZA,\qquad c=DB(\mathbf1-v),\qquad h_n=H^nc,
\tag{6.2}
$$

and

$$
Q_x(w_{n,0})=(H^nu)_x,\quad Q_x(w_{n,1})=h_n(x),\quad
W_y(\beta)=1-v_y,\quad W_y(\alpha w_{n,1})=(ZA h_n)_y.
\tag{6.3}
$$

The identities $u+c+H\mathbf1=\mathbf1$ and
$H\mathbf1\le\lambda\mathbf1$ prove normalization by telescoping and
the geometric tail bounds. In particular there is no conditioning on
completion. These are PAID's matrix evaluator, reused here.

Push the two actual edge arrays forward as

$$
\Gamma_B=\sum_{x,y}\pi_xB_{xy}\delta_{(Q_x,W_y)},\qquad
\Gamma_A=\sum_{y,x}\tau_yA_{yx}\delta_{(W_y,Q_x)}.
\tag{6.4}
$$

Equations (6.1) give the common unweighted marginals. The complete
same-update equations give both residual equations conditioned on the
whole input descriptor. If multiple labels have the same own law, their
outgoing mixtures all equal the same residual; grouping them preserves
the conditional equations. This is the exact finite pushforward of
[PAIR, §11; PAID, §16], not a new realization theorem.

For the finite calculation form the row feature arrays

$$
f_x=(h_0(x),h_1(x),h_2(x)),\quad
g_y=(1-v_y,(ZA h_0)_y,(ZA h_1)_y,(ZA h_2)_y).
$$

Then all quantities are given by finite sums:

$$
\begin{aligned}
V_A&=\sum_{y,x}\tau_yA_{yx}\|f_x-(Af)_y\|^2,\\
V_B&=\sum_{x,y}\pi_xB_{xy}\|g_y-(Bg)_x\|^2,\\
m_p&=\pi(h_0+h_1+h_2),\qquad
m_\beta=\tau(\mathbf1-v+ZA h_0),\\
L_\Pi&=\frac12\sum_x\pi_x
 \bigl(|e_x-e_R|+|h_3(x)-z_R|
       +|e_x+h_3(x)-e_R-z_R|\bigr),
\end{aligned}
\tag{6.5}
$$

where $e=h_0+h_1+h_2$, $e_R=132025/262144$ and
$z_R=84375/16777216$. The boxes test $h_0,h_2,h_3,ZA h_0,ZA h_1$
on every positive row. The means give $\eta=|m_p-M_p|+
\kappa|m_\beta-M_\beta|$. Thus every computation refers to the own laws
of the same supplied installation. The finite variance identity, for
example $V_A=\sum_x\pi_x\|f_x\|^2-\sum_y\tau_y\|(Af)_y\|^2$,
is only a supplied alternative evaluator; the nonnegative formula (6.5)
avoids subtractive certification issues.

The complete program retains $C_0$ from initialization. Before the third
latch it uses fair synthetic letters with the original updates. In the
same update that writes the third record and latches it, it draws $x\sim\pi$
independently of the source and acquired word, on every seed/record fibre.
At fourth p it emits alpha with probability $u_x$; acquired or synthetic
beta uses $B_{xy}$ and the original suspension block. At fourth suspension
it emits alpha with probability $v_y$; acquired or synthetic alpha uses
$A_{yx}$ and the original return block. Completing letters clear private
labels and perform the original pendingStop transition. The sole matching
Stop delivers; the delivered residual is empty. The same sampler kernels
and the same original operation blocks are used in both modes. Sampler
internal states retain conditional continuations of that same program.

At every actual fourth-phase history, induction in (6.1) gives row $\pi$
or $\tau$. Actual acquired letters do not reweight rows by synthetic
emissions. At a history $h$ the target is
$T_h^\mu=(I_{C_0(h)})_\#\sum_k\nu_h(k)P_{s,r_k}$, with $\nu_h$ the
analysis posterior from all paid letters. The complete decoder is
$(I_{C_0(h)})_\#Q_x$ or $(I_{C_0(h)})_\#W_y$. This identifies each
configuration's law before averaging TV. PAID's positive finite
paid-history approximation of each supported depth supplies

$$
R_{{\rm conf},p}(\mathcal I)
 =\max_{k=1,2,3}\sum_x\pi_x\operatorname{TV}(Q_x,P_{p,r_k}),\quad
R_{{\rm conf},\beta}(\mathcal I)
 =\max_{k=1,2,3}\sum_y\tau_y\operatorname{TV}(W_y,P_{\beta,r_k}).
\tag{6.6}
$$

For the upper inequalities use convexity in each common-history target;
the reverse inequalities are supplied by the positive finite histories
concentrating the source posterior. The rows are exactly stationary at
each of those histories. All held records remain in their own renderers.
The source implementation of the full law is also the interface of
`NativeInstalledFullLaw.installed_configuration_identity`,
`installed_first_block_recursion` and `installed_full_law`: an installed
emitter uses the actual update on the same complete carrier, with lawful
operations, full-event residuals, deterministic pending Stop and delivered
law, and configuration-before-TV history transport. Those existing
declarations are references; no new Lean application is asserted.

Equation (6.5) needs $h_0,h_1,h_2,h_3$ only. Applying $H$ as successive
$A,Z,B,D$ products avoids dense matrix multiplication. With
$N=|X|$, $M=|Y|$, a direct implementation uses at most
$100(NM+N+M)$ rational arithmetic and comparison operations and
$O(NM+N+M)$ rational storage cells, including its input. Each coordinate
is a finite expression of the supplied rational entries. Integer bit
length, arithmetic work, input verification and output storage are charged
separately; a rational operation is not a unit physical-time assertion.
For checking (2.1), set $t=\rho_p+\delta_3/2-L_\Pi-C\eta$. If $t\le0$
the check holds; otherwise it is the rational comparison $t^2\le C^2V$.
This proves the evaluation claim without sampling. $\square$

**Example 6.3 (the supplied fair matched-endpoint installation).** One
concrete source-specified instance is the fair matched-endpoint table
of [SEVEN, (2.4), (3.4)], installed by the preceding PAID product program:

$$
X=Y=\{a,b\},\quad A=B=I_2,\quad
\pi=\tau=(1/2,1/2),\quad u=v=(1/3,2/5).
\tag{6.7}
$$

This application takes that single complete rational specification as
its already supplied input. Its authenticated mathematical identity is
(6.7) together with the initialization and full product program just
given; there is no assertion that an external physical installation has
been measured. The copied own laws are exactly $P_{s,a},P_{s,b}$, so both
full boxes, hence all five local boxes, hold. Direct evaluation gives

$$
V=0,\qquad \eta=0,\qquad
L_\Pi=\rho_p+\delta_3/2
 =\frac{468557036828959}{9555148800000000}.
\tag{6.8}
$$

This is equality in (2.1), for every permitted positive-three-depth prior.
It is not a zero-excess witness: its p depth-3 full risk is at least
(6.8), strictly above $\rho_p$. The example is a supplied boundary
consumer, not new table construction or new minimax content.

Under the original exact fair-bit service convention, an exact finite
representation has the label latch use one
fair bit. An alpha emission of $1/3$ uses two-bit blocks, rejecting value
3 and accepting alpha at value 0; an emission of $2/5$ uses three-bit
blocks, rejecting values 5, 6, 7 and accepting alpha at values 0, 1.
The independent fresh emission bits are private service bits, not source
Reads. Each service has finitely many prefix states but unbounded possible
retries, and its internal states and cursor are charged. Before the latch,
one fair service bit generates each synthetic letter. Both acquired
updates in (6.7) retain the label, until completion clears it. This fully
specifies the rational private service on top of the unchanged original
control and record program. There is no worst-case random-bit or runtime
bound from its finite state set.

**Convention 6.4 (distinct resource accounts).** COMPLETE includes the
original control, private labels, all installed table numerics and
programs, selectors, addresses, sampler states, workspace, output
cursors and persistent randomness. The offline evaluator has its own
charged input, exact arithmetic and workspace; none becomes a free
online register. The maximum completed p word length used by (6.5) is
eight; the suspended feature lengths are one, three, five and seven.
These word lengths are not source sample counts, acquisition prices,
random-bit bounds, execution-time bounds or COMPLETE bounds. The full
program and infinite complete carrier have not been truncated.

## 7. Mathematical suppliers and the remaining interfaces

**Mathematical citation 7.1 (source-relative increment).** Repository
citations in this volume refer to the snapshot
$\mathtt{be3168b337de4a9ac44ee652f02f8085a1ad0295}$.
The ordinary mathematical result is (2.1), supported by §§3–5, and its
necessary consequences (2.3)–(2.4). It is repo-derived, with no global
originality claim.

| Supplier | Reused conclusion and exact boundary |
| --- | --- |
| [SEVEN], Definition 2.1 and §§2–5 | Seven features, zero-variance rigidity, qualitative positive restricted gap and delayed branching. They do not supply the explicit tolerance proved here. |
| [REV], §§15–16 | The rational scalar sign certificate, global four-rate supermodularity including its seam, and endpoint gap. Only their stated algebraic domains are used in §§3–5. |
| [REV], §18 | $1911e(M)+110\operatorname{Br}_{\rm orig}(M)\ge121j_{\rm det}(\mu)>0$ is an existing original full-law dispersion obstruction. Theorem 2.1 concerns seven features and an explicit numerical finite-risk tolerance on five local boxes, rather than a renaming of that full-law result. |
| [PAIR], §§11, 14, 20 | The original compact common-flow model, full-law stability in a different defect, and the exact two-marginal convex-order criterion. No $V$-to-that-defect theorem or new coupling existence theorem is asserted. |
| [NATIVE], Theorems 2.1, 3.1 | Borel native tail atoms and exact eventual endpoint-recurrence recovery. Neither supplies an approximate recurrence premise here; both remain constraints on a candidate original zero pair. |
| [PAID], §§2, 14, 18 | Authentic same-update installation, common-row/history transport, matrix evaluation and existence of finite certificates. The evaluator and installation in §6 are applications of these suppliers. |
| [INSTALLED] | Existing full-law, full-event residual and original history-risk interfaces on one actual COMPLETE carrier. Their use does not authenticate an unknown device or assert a newly compiled client. |
| [WHITEBOX], §§3–10, 51, 74–77 | Task-relative distinctions, training-state seams, the finite-sample statistical boundary, and lawful read/reset frontiers under their own specified interfaces. None supplies independent descriptor samples or source reset here. |
| [SLH], §§41–45 | Common-source boundary recovery, authentic retained records, necessary acquisition evidence and consumers limited to their covered domains. These do not reconstruct an arbitrary common-flow installation. |
| [COUNTERFACTUAL] | The native branch-ladder obstruction on raw counterfactual histories retains literal address actions and impossible histories. It gives no universal code-whitebox, stream-transducer or actual-history impossibility for the present stochastic program. |

**Mathematical citation 7.2 (primary literature).** The invoked mature
comparison uses exactly the bounded continuous coordinate-clipped test
$F(Y)-y_0y_1$ and the common scalar marginal of all four coordinates.
Thus [CW]'s bounded right-continuous supermodular order is sufficient;
no unbounded-test extension or literature equality characterization is
used. The Bernstein facts in [BSCA] use a finite polynomial on a closed
rectangle, an affine map to the unit cube, nonnegative basis functions
and their partition of unity; they explain the supplied rational
certificate, not an experimental sign check. [LV, Theorems 1.2–1.4]
requires finite first moments, satisfied by PAIR's bounded vector
projections. Its barycentric couplings are background for the supplied
PAIR20 criterion; no successor is identified with its conditional mean
in this proof. These are literature-attested tools, not new general
theorems.

| Citation | Primary mathematical source |
| --- | --- |
| [CW] | Côté and Wang, *On convex order and supermodular order without finite mean*, arXiv:2502.17803v3, Definition 3(iii) and Proposition 6. |
| [BSCA] | Ben Sassi, Sankaranarayanan, Chen and Ábrahám, *Linear Relaxations of Polynomial Positivity for Polynomial Lyapunov Function Synthesis*, arXiv:1407.2952v2, §3.1, (3.7) and Lemma 3.2. |
| [LV] | Leskelä and Vihola, *Conditional convex orders and measurable martingale couplings*, arXiv:1404.0999v3, Theorems 1.2–1.4; background for the supplied PAIR20 criterion. |

**Definition 7.3 (remaining original and learning obligations).** The
original decision requires either a compatible pair on the same
unrestricted $\mathfrak C$ with both full boxes, both means and both
depth-3 budgets, or a strict positive-gap proof excluding all such pairs.
Theorem 2.1 only excludes insufficient seven-feature variation relative
to the finite-risk and mean tolerances. Positive $V$ is permitted; the
theorem neither constructs the required joint pair nor bounds $V$ above
on the full zero face. Finite-table attainment additionally needs the
supplied finite-marginal and represented-sampling bridges; it is not
obtained from a Borel analysis path.

A task-relative separation witness exhibits realizations with the same
allowed observation and different target answers or legal continuations.
The strict proof-content escape predicate in `CLAUDE.md` §3.2 is distinct
and has two legal forms. Its bind-only classification inlines local aliases,
newly added helpers, tactic expansions and definitional equalities, stopping
at existing frozen or pinned upstream declarations. Instantiation, premise
substitution, logical projection or recombination, and normalization alone
do not supply new proof content. First, a new independent intermediate
proposition may witness escape only if (i) its declaration lies in the
theorem's elaborated transitive constant-dependency closure; (ii) it cannot
be obtained directly from existing frozen or pinned upstream premises by
instantiation, projection or normalization; (iii) it is neither definitionally
equivalent to, an alias of, nor a restatement of the conclusion; and (iv)
after ζ/β/ι reduction and removal of dead terms and components discarded by
projection, it remains used on the conclusion's live proof path. If bind-only
operations on the existing premises can reach the conclusion without it,
it is not a witness; inserting an unrelated proposition in the dependency
closure does not change the proof classification. Second, the public
conclusion itself may be the witness when a non-bind-only calculation,
construction or estimate chain produces it directly on the live proof path
and the conclusion is unavailable by binding and normalization of existing
frozen or pinned upstream premises. No auxiliary intermediate proposition
may be manufactured for this second form. Neither strict form
can be replaced by a task-relative separation witness. Here the mathematical
increment is the
quantitative perturbation argument, not the naming of a feature vector
or the generic existence of a separating observation.

As a model diagnostic, (2.1) can reject an authenticated supplied-table
claim that combines the five local boxes, small mean error, small seven
conditional variances and an incompatible finite risk. It does not
identify an unknown installation from observations. Lawful acquisition
of its program, configuration features and common edge rows remains a
separate task. Statistical certification would require a specified
sampling law, access to those same configurations and edges, accuracy
and confidence margins, and charged acquisition; the once-sampled
common-$K$ histories do not themselves provide iid descriptor access.
No reset or replay service is granted. WHITEBOX51's iid complete-record
model and WHITEBOX74–77's same-checkpoint operations cannot be imported
without their hypotheses. Training attainment further needs a learner,
loss and optimization statement; generalization needs a data-generating
model and an out-of-sample guarantee. None is asserted by this finite
diagnostic. There is no empirical ML gain, universal five-class neural
theory, all-code whitebox impossibility, or resource improvement obtained
by changing the original contract.

[SEVEN]: RECURSIVE_RELATIONAL_OBSERVATION_FINITE_WORD_BRANCHING_NECESSITY.md
[REV]: RECURSIVE_RELATIONAL_OBSERVATION_REVERSIBLE_COMMON_GENERATOR_CONSTRAINTS.md
[PAIR]: RECURSIVE_RELATIONAL_OBSERVATION_PAIRED_CALIBRATION_OBSERVABILITY.md
[PAID]: RECURSIVE_RELATIONAL_OBSERVATION_EFFECTIVE_PAID_HISTORY_CERTIFICATES.md
[NATIVE]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_TAIL_ATOMS_AND_BOREL_RECURRENCE.md
[WHITEBOX]: FIB_ATOM_MACHINE_LEARNING_WHITEBOX.md
[SLH]: RECURSIVE_RELATIONAL_OBSERVATION_SPARSE_LITERAL_HISTORY_TRANSPORT.md
[INSTALLED]: ../../../D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeInstalledFullLaw.lean
[COUNTERFACTUAL]: ../../../D5/S3/Arith/FibonacciAtomic/Observer/ActualCompletionCounterfactualEscape.lean
[CW]: https://arxiv.org/html/2502.17803v3
[BSCA]: https://arxiv.org/html/1407.2952v2
[LV]: https://arxiv.org/html/1404.0999v3

## 追加锚（本行以下为增补区）
