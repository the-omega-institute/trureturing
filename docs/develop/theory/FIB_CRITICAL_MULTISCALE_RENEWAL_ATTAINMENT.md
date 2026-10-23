# Critical multiscale renewal attainment

## 1. The attained upper bound and its scope

Fix an integer $r\ge1$, put $d=2r-1$ and $a=d+1=2r$, and fix real numbers $c>0$ and $0<\alpha<1/2$. The two source shapes are exactly

$$
F_0(k)=k^d,\qquad F_1(k)=k^d+c k^{d-r}\qquad(k=1,2,\ldots).
\tag{1.1}
$$

At known common $q=e^{-s}$, one source-blind finite table must work under either true source. Every persistent configuration and both internally emitted labels count; every actual consecutive bit read through the decision is paid. Immutable real transition probabilities have arbitrary unpriced precision. Section 2 specifies the stationary experiment and observer contract completely.

The construction proves the following sufficient resource bounds. There are source-only constants $\eta\in(0,1)$ and $s_*>0$ and source/risk constants $C_M,C_T>0$, chosen before any cutoff, such that for every $0<s<s_*$ and integer $L\ge1$ with $sL\le\eta$, one common table has

$$
M(s,L)\le C_M\frac{L+2}{s^r\sqrt{H_L}},\qquad
\max_{i\in\{0,1\}}\mathbb E_iT\le C_T\frac{s^{-(2r+1)}}{H_L},
\qquad H_L=\sum_{k=1}^L\frac1k.
\tag{1.2}
$$

It meets both risks, both almost-sure stopping conditions and both finite-mean conditions. For each additionally fixed $\theta\in(0,1]$, the cutoff $L=\lfloor\eta s^{-\theta}\rfloor$ gives, on one $\theta$-dependent neighborhood,

$$
M=O_\theta\!\left(\frac{s^{-(r+\theta)}}{\sqrt{\log(1/s)}}\right),\qquad
\max_i\mathbb E_iT=O_\theta\!\left(\frac{s^{-(2r+1)}}{\log(1/s)}\right).
\tag{1.3}
$$

In particular $\theta=1$ gives the explicit sufficient configuration bound $O(s^{-(r+1)}/\sqrt{\log(1/s)})$. All parameters precede $s$ and table selection. No constants are uniform over changing $r,c,\alpha$ or over $\theta\downarrow0$.

The bridge is a saturated category of actually completed gaps, composed with an unbiased rounded likelihood score on a finite lattice. Its information deficit is comparable to $s^{2r}H_L$. The full evidence/category product is counted, including long-gap overflow and both output labels. The proofs establish finite stopping by drift before taking risk limits, then price the actual history by predictable inclusion. The minimum sufficient state cost and the full critical all-budget frontier remain unresolved.

## 2. The stationary source and the observer contract

**Definition 2.1 (The complete observed law).** For $i\in\{0,1\}$ and $s>0$ put

$$
\begin{aligned}
Z_i(s)&=\sum_{k\ge1}F_i(k)e^{-sk},&
f_i(k)&=\frac{F_i(k)e^{-sk}}{Z_i(s)}\quad(k\ge1),& f_i(0)&=0,\\
S_i(b)&=\sum_{k\ge b}f_i(k)\quad(b\ge0),&
\mu_i&=\sum_{k\ge1}(k+1)f_i(k),\\
\beta_i&=\frac{\sum_{k\ge1}k(k+1)f_i(k)}{2\mu_i}.
\end{aligned}
\tag{2.1}
$$

Draw $\tau$ with $\mathsf P_i(\tau=b)=S_i(b)/\mu_i$ for every integer $b\ge0$. Independently draw iid $K_1,K_2,\ldots$ with the full countably supported law $f_i$ on the positive integers. Define

$$
\tau_0=\tau,\qquad \tau_n=\tau+\sum_{j=1}^n(K_j+1)\quad(n\ge1),\qquad
X_t=\mathbf1_{\{t=\tau_n\text{ for some }n\ge0\}}\quad(t\ge0).
\tag{2.2}
$$

Thus $K_j$ counts zeros, and $K_j+1$ is the complete interval through its closing one. Every positive gap length has positive probability; zero-length gaps have probability zero. All other sites are zeros. The initial wait is an equilibrium residual wait, not an iid draw from $f_i$.

Throughout, $\mathsf P_i$ and $\mathbb E_i$ refer to source $i$ at the selected $s$, including independent observer coins when a controller is present. All logarithms are natural.

**Definition 2.2 (Common design, complete configurations and compliance).** At each selected known common $q$, the observer has one finite transition table and one source-independent initialization used under both true labels. The design can depend on the public pair, $q$, $\alpha$ and the selected cutoff. The number of complete persistent configurations counts control, every simultaneously retained coordinate or category, retained random information and the two internally emitted labels. It counts all possible configurations, including ones arising on rare histories. Fresh transition coins are independent of the source and of earlier fresh coins; no retained random tape or seed is free.

The fixed table, including arbitrary exact real transition probabilities, is immutable design information whose precision and design computation are unpriced. At runtime the table uses only the current counted configuration, the next actual bit and fresh randomness. It reads one uninterrupted consecutive history of (2.2). There is no external clock, age, read or gap counter, program state, archive, skipped bit, free gap, source reset, extra source, hidden source label, probability response or parameter query. The cost tally is not an input. The decision is emitted internally; no decoder from stopping time is available.

If the read prefix is $X_0,\ldots,X_{T-1}$, its paid cost is $T$. This includes the stationary first wait, all read zeros and ones, and the terminal read. A compliant table satisfies all six conditions

$$
\begin{gathered}
\mathsf P_0(D=1)\le\alpha,\qquad \mathsf P_1(D=0)\le\alpha,\\
\mathsf P_0(T<\infty)=1,\qquad \mathsf P_1(T<\infty)=1,\\
\mathbb E_0T<\infty,\qquad \mathbb E_1T<\infty.
\end{gathered}
\tag{2.3}
$$

These are pointwise obligations at the selected common $q$. They require neither one table independent of $q$ nor testing with an unknown nuisance parameter.

**Lemma 2.3 (Normalization and stationarity).** All sums and polynomial moments in (2.1) are finite for every $s>0$. The first-wait law is normalized, the process (2.2) is stationary, and

$$
S_i(0)=S_i(1)=1,\qquad \sum_{b\ge0}S_i(b)=\mu_i,\qquad \mathbb E_i\tau=\beta_i.
\tag{2.4}
$$

Proof. Polynomial growth times $e^{-sk}$ is summable with any fixed polynomial weight. Thus $Z_i$ is finite and strictly positive, and $f_i$ is a probability law with the asserted support. Its mass at $k$ occurs in $S_i(b)$ for exactly $b=0,\ldots,k$. Interchanging nonnegative sums gives

$$
\sum_{b\ge0}S_i(b)=\sum_{k\ge1}(k+1)f_i(k),\qquad
\sum_{b\ge0}bS_i(b)=\frac12\sum_{k\ge1}k(k+1)f_i(k).
\tag{2.5}
$$

Dividing by $\mu_i$ proves normalization and the mean identity, including the positive mass at $\tau=0$.

For stationarity introduce a countdown chain only on the proof probability space. From a positive value $b$ it moves to $b-1$; from zero it draws a fresh $K$ with law $f_i$. The normalized mass $\pi_i(b)=S_i(b)/\mu_i$ has incoming mass at every $b\ge0$

$$
\pi_i(b+1)+\pi_i(0)f_i(b)=\frac{S_i(b+1)+f_i(b)}{\mu_i}=\pi_i(b).
\tag{2.6}
$$

At $b=0$, use $f_i(0)=0$ and $S_i(0)=S_i(1)$. Start the chain with $\pi_i$ and output one exactly at countdown zero. Its first tick is at the initial countdown $\tau$, and later zero counts are independent draws of $K$. Its output is (2.2), so that bit process is stationary. The countdown is not an observer input or state. $\square$

## 3. One source neighborhood before every cutoff

**Lemma 3.1 (Power sums, exact normalization and moments).** There are $s_0>0$ and constants $z_-,z_+,G,C_\mu,C_\beta>0$, depending only on the fixed sources, such that for every $0<s<s_0$,

$$
z_-s^{-a}\le Z_0(s)\le z_+s^{-a},\qquad
0<g(s):=\frac{R_{r-1}(s)}{R_{2r-1}(s)}\le Gs^r,
\tag{3.1}
$$

and $\mu_i\le C_\mu/s$, $1+\beta_i\le C_\beta/s$ for both $i$, where $R_m(t)=\sum_{k\ge1}k^m e^{-tk}$ for nonnegative integers $m$. At every positive integer $k$ the exact normalized ratio is

$$
\frac{f_1(k)}{f_0(k)}=\frac{1+c k^{-r}}{1+cg(s)},\qquad g(s)=\sum_{k\ge1}f_0(k)k^{-r}\in(0,1].
\tag{3.2}
$$

Proof. The geometric identity is $R_0(t)=1/(e^t-1)$. Write $e^t-1=tE(t)$, where $E$ is analytic near zero and $E(0)=1$. Then $R_0(t)-1/t$ extends analytically through zero. Local absolute convergence on positive $t$-intervals permits differentiation of the defining series, so

$$
R_m(t)=(-\mathrm d/\mathrm dt)^mR_0(t)=m!t^{-(m+1)}+O(1)\quad(t\downarrow0).
\tag{3.3}
$$

The remainder remains bounded after each of the finitely many derivatives needed here because it is analytic. Exactly $Z_0=R_d$ and $Z_1=R_d+cR_{d-r}$, with $d-r=r-1\ge0$. Thus

$$
g(s)=\frac{(r-1)!}{(2r-1)!}s^r(1+O(s)),\qquad Z_i=d!s^{-a}(1+O(s)).
\tag{3.4}
$$

Taking the ratio of the two normalized full masses proves (3.2), including its expectation expression. These facts give (3.1) on one source-only neighborhood.

For explicit moment numerators put

$$
\begin{aligned}
W_i(s)&=R_{d+1}+R_d+i c(R_{d-r+1}+R_{d-r}),\\
\mathcal V_i(s)&=R_{d+2}+R_{d+1}+i c(R_{d-r+2}+R_{d-r+1}),
\end{aligned}
\qquad \mu_i=\frac{W_i}{Z_i},\quad \beta_i=\frac{\mathcal V_i}{2W_i}.
\tag{3.5}
$$

All power sums on the right are at $s$. Their leading terms are $(d+1)!s^{-(a+1)}$ and $(d+2)!s^{-(a+2)}$. Since $r\ge1$, each perturbation lowers degree by at least one. Therefore

$$
\mu_i=\frac a s+O(1),\qquad \beta_i=\frac{a+1}{2s}+O(1).
\tag{3.6}
$$

A finite enlargement of constants and shrinkage of the same neighborhood yield the simultaneous moment bounds. $\square$

**Definition 3.2 (Permitted cutoffs).** Fix $\eta\in(0,1)$ so that

$$
G\eta^r\le\frac12,\qquad \frac{\eta^a}{z_-}\le\frac12,
\tag{3.7}
$$

and fix $0<s_*<\min\{s_0,1,\eta/2\}$. These choices depend only on the sources. From now on a permitted pair means $0<s<s_*$ and an integer $L\ge1$ with $sL\le\eta$. No further neighborhood in Sections 4–9 depends on $L$, a budget or an observer.

## 4. The finite category and its normalized tail

**Definition 4.1 (Actual gap category and affinity).** For a permitted pair set $\mathcal Z_L=\{1,\ldots,L,\star\}$ and define $C_L(k)=k$ for $1\le k\le L$, $C_L(k)=\star$ for $k>L$. Its laws under the sources are

$$
a_i(k)=f_i(k)\quad(1\le k\le L),\qquad a_i(\star)=\sum_{k>L}f_i(k).
\tag{4.1}
$$

These laws are normalized, and every mass is strictly positive. Write

$$
A=\sum_{z\in\mathcal Z_L}\sqrt{a_0(z)a_1(z)},\qquad
u=1-A,\qquad \ell_z=\log\frac{a_1(z)}{a_0(z)},\qquad H_L=\sum_{k=1}^L\frac1k.
\tag{4.2}
$$

**Lemma 4.2 (Uniform harmonic information and bounded logs).** There are positive source-only constants $h_-,h_+$ such that every permitted pair satisfies

$$
h_-s^{2r}H_L\le u(s,L)\le h_+s^{2r}H_L,\qquad
0<A<1,\quad 0<u<1,\qquad |\ell_z|\le C_0:=\log(1+c).
\tag{4.3}
$$

Proof. For $k\le L$ put $v_k=f_1(k)/f_0(k)-1$. The exact normalization gives

$$
v_k=\frac{c(k^{-r}-g(s))}{1+cg(s)}.
\tag{4.4}
$$

Since $sk\le\eta$, (3.1) and (3.7) imply $g(s)\le G\eta^r k^{-r}\le k^{-r}/2$. Also $g(s)\le1$. Consequently

$$
\frac{c}{2(1+c)}k^{-r}\le v_k\le ck^{-r},\qquad
\frac{e^{-\eta}}{z_+}s^a k^{a-1}\le f_0(k)\le\frac1{z_-}s^a k^{a-1}.
\tag{4.5}
$$

The exact squared-root distance identity is

$$
2u=\sum_{z\in\mathcal Z_L}(\sqrt{a_1(z)}-\sqrt{a_0(z)})^2.
\tag{4.6}
$$

At a short category $k$ its summand is $f_0(k)v_k^2/(\sqrt{1+v_k}+1)^2$. The denominator is at most $(\sqrt{1+c}+1)^2$. Substituting (4.5), with $a=2r$, makes that summand at least

$$
\frac{c^2e^{-\eta}}{4z_+(1+c)^2(\sqrt{1+c}+1)^2}\frac{s^a}{k}.
\tag{4.7}
$$

Sum the short terms and divide by two. This proves the lower bound with $h_-=c^2e^{-\eta}/[8z_+(1+c)^2(\sqrt{1+c}+1)^2]$. In particular the category laws differ even for $L=1$. Positive masses give $A>0$; Cauchy–Schwarz gives $A\le1$, with equality only for equal normalized laws. Thus $0<A<1$ and $0<u<1$.

For the upper bound retain the full collapsed tail. Put

$$
\pi_0=\sum_{k\le L}f_0(k),\qquad Q=\sum_{k\le L}f_0(k)v_k^2,\qquad
m=\sum_{k\le L}f_0(k)v_k=\sum_{k\le L}(f_1(k)-f_0(k)).
\tag{4.8}
$$

Since $\sum_{k\le L}k^{a-1}\le L^a$, (3.7) gives $\pi_0\le s^aL^a/z_-\le1/2$. Normalization says that the tail mass changes by exactly $-m$. Its chi-square contribution against $a_0$ is $m^2/(1-\pi_0)$, and weighted Cauchy–Schwarz gives $m^2\le\pi_0Q$. Hence

$$
\chi^2(a_1\|a_0):=\sum_z\frac{(a_1(z)-a_0(z))^2}{a_0(z)}
=Q+\frac{m^2}{1-\pi_0}\le\frac{Q}{1-\pi_0}\le2Q.
\tag{4.9}
$$

For positive $p,q$, $(\sqrt p-\sqrt q)^2\le(p-q)^2/q$. Equations (4.6) and (4.9) yield $u\le Q$. Finally (4.5) gives

$$
Q\le\frac{c^2}{z_-}s^a\sum_{k=1}^L k^{a-1-2r}=\frac{c^2}{z_-}s^aH_L.
\tag{4.10}
$$

Thus $h_+=c^2/z_-$ is valid. The symmetric affinity has been bounded with the entire normalized tail present; no tail suffix or likelihood observation was supplied for free.

At every $k\ge1$, (3.2) and $k^{-r},g(s)\in[0,1]$ put the full ratio in $[1/(1+c),1+c]$. The ratio $a_1(\star)/a_0(\star)$ is its conditional $f_0$-average over $k>L$, so it lies in the same interval. Taking logarithms proves the uniform bound for every short and tail category. $\square$

## 5. Every actual-bit row and the complete configuration count

**Definition 5.1 (Compiled lattice rows).** For a permitted pair set

$$
\delta=\sqrt u\in(0,1),\qquad R=2\log(1/\alpha)>0,\qquad H=\lceil R/\delta\rceil.
\tag{5.1}
$$

Add a formal category $0$ solely to define impossible consecutive-one rows and set $\ell_0=0$. For every $z\in\{0,1,\ldots,L,\star\}$ compile

$$
m_z=\lfloor\ell_z/\delta\rfloor\in\mathbb Z,\qquad t_z=\ell_z/\delta-m_z\in[0,1).
\tag{5.2}
$$

At a closing one choose $m_z$ with probability $1-t_z$ and $m_z+1$ with probability $t_z$. The floor is the usual floor also for negative $\ell_z$; it does not truncate negative scores toward zero. Integers, probabilities and destinations are immutable table entries. Category $0$ is absent from both laws $a_i$ and has $m_0=t_0=0$.

**Definition 5.2 (The entire table).** The complete persistent configuration set is

$$
\mathcal Q=\{w,d_0,d_1\}\cup
\{(j,z):j\in\mathbb Z,\ -H<j<H,\ z\in\{0,1,\ldots,L,\star\}\}.
\tag{5.3}
$$

Initialize deterministically in $w$ under both sources. Every nonlabel state undertakes the next actual paid read. Entering $d_i$ internally emits $D=i$ and stops without another read. Define the immutable destination for a closing-one increment $m$ by

$$
\Phi(j,m)=
\begin{cases}
d_1,&j+m\ge H,\\
d_0,&j+m\le-H,\\
(j+m,0),&-H<j+m<H.
\end{cases}
\tag{5.4}
$$

The cases are disjoint because $H>0$. This specifies every state and bit row, including unreachable combinations:

| Current configuration and actual bit | Next configuration and probability |
| --- | --- |
| $w$, zero | $w$ with probability one |
| $w$, one | $(0,0)$ with probability one |
| $(j,k)$, zero, $0\le k<L$ | $(j,k+1)$ with probability one |
| $(j,L)$, zero | $(j,\star)$ with probability one |
| $(j,\star)$, zero | $(j,\star)$ with probability one |
| $(j,z)$, one, any $z\in\{0,1,\ldots,L,\star\}$ | $\Phi(j,m_z)$ with probability $1-t_z$; $\Phi(j,m_z+1)$ with probability $t_z$ |
| $d_i$, either bit | $d_i$ with probability one |

Coin outcomes with the same destination have their probabilities added. Label rows provide only analytical continuation; the read policy stops on entry. On the impossible consecutive-one input $z=0$, the destination is $(j,0)$ with probability one. Every nonterminal closing one resets the category to zero, without resetting the source. Saturation at $\star$ continues to read every remaining zero of that actual gap.

**Proposition 5.3 (Count and lawful access).** The table has exactly

$$
M(s,L)=3+(2H-1)(L+2)
\tag{5.5}
$$

listed complete configurations and obeys the access and accounting contract of Definition 2.2.

Proof. There are $2H-1$ live integer evidence coordinates and $L+2$ categories. They coexist, so their full product is counted; $w$ and both labels contribute three further configurations. Counting unreachable pairs only enlarges the sufficient budget. Every row has nonnegative probabilities summing to one, and every destination is listed.

The old counted state and the actual bit select the row. A fresh coin has no persistent effect except its destination. Score addition and boundary comparison describe how destinations were compiled, not external runtime arithmetic. Runtime needs no exact likelihood, logarithm, division, floor, square root, sum, gap number, overshoot register or extra output phase. Full model probabilities enter only source-blind design from the public pair and known common $q$, not a query to the true source. Neither $\tau$ nor the countdown nor future gaps are available to the table. The waiting rows pay the stationary wait and first one; saturated rows pay arbitrarily long overflow suffixes. $\square$

## 6. Independent categories and unbiased signed drifts

**Lemma 6.1 (Joint increment law and drift).** Let $Y_n=C_L(K_n)$ be the category of potential complete gap $n$. With independent fresh closing coins let $J_n$ have values $m_{Y_n}$ and $m_{Y_n}+1$ with the probabilities of (5.2), and put $V_n=\delta J_n$. Under source $i$ the pairs $(Y_n,J_n)$ are iid, independent of $\tau$, with law

$$
\mathsf P_i(Y_n=z,J_n=m_z)=a_i(z)(1-t_z),\qquad
\mathsf P_i(Y_n=z,J_n=m_z+1)=a_i(z)t_z.
\tag{6.1}
$$

They agree with the actual controller through its terminating gap. The centered error $\varepsilon_n=V_n-\ell_{Y_n}$ satisfies

$$
\mathbb E_i(\varepsilon_n\mid Y_n)=0,\quad |\varepsilon_n|\le\delta,\quad |V_n|\le C_0+\delta.
\tag{6.2}
$$

Writing $D_i=D(a_i\|a_{1-i})$, where $D(p\|q)=\sum_zp(z)\log(p(z)/q(z))$, one has

$$
\mathbb E_0V_n=-D_0,\qquad \mathbb E_1V_n=D_1,\qquad D_i\ge2u>0.
\tag{6.3}
$$

Proof. After the first actual tick the category is zero. After $K_n$ actual zeros it is exactly $K_n$ if $K_n\le L$ and $\star$ otherwise. Its closing one therefore uses category $C_L(K_n)$, obtained from that same paid gap. Independent iid gaps and fresh independent coins give (6.1). Equivalently use an independent uniform coin at each potential closing row and choose the upper value precisely when it lies below $t_{Y_n}$. This supplies a probability-space continuation after stopping, not operational access to additional gaps.

Conditional on $Y_n=z$, the error has values $-\delta t_z$ and $\delta(1-t_z)$. Hence

$$
\mathbb E_i(V_n\mid Y_n=z)=\delta(m_z+t_z)=\ell_z,\qquad
\mathbb E_i(\varepsilon_n^2\mid Y_n=z)=\delta^2t_z(1-t_z)\le\delta^2/4.
\tag{6.4}
$$

This proves (6.2) and the mean identities in (6.3). All logs and sums are finite. To prove the drift lower bound, apply $\log x\le x-1$ to $x=\sqrt{b(z)/p(z)}$, where $p=a_i$, $b=a_{1-i}$:

$$
D(p\|b)=-2\sum_zp(z)\log\sqrt{b(z)/p(z)}
\ge2\sum_z\bigl(p(z)-\sqrt{p(z)b(z)}\bigr)=2(1-A)=2u.
\tag{6.5}
$$

No category is assumed independent of its own duration or rounding error. Unbiased rounding preserves both signed divergences exactly; it need not preserve the unrounded likelihood itself. $\square$

## 7. Finite stopping before risk limits and exact paid cost

**Lemma 7.1 (Both finite gap stops by bounded finite drift).** On the potential increment space let

$$
S_0=0,\quad S_n=\sum_{k=1}^nV_k,\qquad
N=\inf\{n\ge1:S_n\ge H\delta\text{ or }S_n\le-H\delta\}.
\tag{7.1}
$$

This exit time is the actual number of post-first-tick gaps through emission. Under either source,

$$
\mathbb E_iN\le\frac{B}{2u}<\infty,\qquad \mathsf P_i(N<\infty)=1,\qquad B:=R+C_0+2.
\tag{7.2}
$$

Proof. Before exit, $S_n=j\delta$ is represented exactly by the live evidence coordinate. The compiled destinations agree with (7.1). The untruncated terminal score can overshoot, but it is a proof variable, never a retained register. At every deterministic stopped horizon,

$$
|S_{N\wedge m}|\le H\delta+C_0+\delta<R+C_0+2=B,
\tag{7.3}
$$

because a live score has magnitude less than $H\delta$, each increment has magnitude at most $C_0+\delta$, $H\delta<R+\delta$, and $\delta<1$.

Let $\mathcal F_n$ contain $\tau$ and the first $n$ complete gaps and closing coins. The event $\{N>n\}$ is $\mathcal F_n$-measurable, and the next increment is independent of $\mathcal F_n$. Put $\sigma_0=-1$ and $\sigma_1=1$ only in the proof. For each finite $m$, finite conditional summation gives the exact identity

$$
\begin{aligned}
\mathbb E_i[\sigma_i S_{N\wedge m}]
&=\sum_{n=0}^{m-1}\mathbb E_i[\mathbf1_{\{N>n\}}\sigma_i V_{n+1}]\\
&=D_i\sum_{n=0}^{m-1}\mathsf P_i(N>n)=D_i\mathbb E_i(N\wedge m).
\end{aligned}
\tag{7.4}
$$

All terms are integrable at finite $m$. This does not first assume $N$ finite, nor require the correct signed terminal score to be positive on every path. Equations (7.3)–(7.4) give $D_i\mathbb E_i(N\wedge m)\le B$. Use $D_i\ge2u$ and monotone convergence to obtain (7.2). Finite expectation implies almost-sure finite $N$. This precedes every limiting risk argument and uses no unbounded optional-stopping identity or assumed auxiliary absorption. Holding increments and arbitrarily long finite gaps are included. $\square$

**Lemma 7.2 (Actual stopping and every paid bit).** Under both sources the actual controller stops almost surely, and

$$
T=1+\tau+\sum_{n=1}^N(K_n+1)\quad\text{almost surely},\qquad
\mathbb E_iT=1+\beta_i+\mu_i\mathbb E_iN<\infty.
\tag{7.5}
$$

Proof. The waiting phase reads $\tau$ zeros and the first one. Every later begun gap is read through its actual closing one, including the terminating gap. Saturation retains less information but skips no bits. The decision is emitted on the same paid closing one that causes exit. Thus the pathwise equality counts the initial wait, every overflow suffix, every holding-update gap, every closing one and the terminal bit. No undertaken terminal gap has an unread suffix.

At each selected $s$, $\tau$ and every $K_n$ are finite almost surely by their laws. Lemma 7.1 makes $N$ finite almost surely. The finite sum then proves actual almost-sure termination under each source.

For the mean, $\{N\ge n\}$ is determined by $\mathcal F_{n-1}$ before gap $n$ is drawn; it is independent of $K_n$. Therefore

$$
\mathbb E_i[(K_n+1)\mathbf1_{\{N\ge n\}}]=\mu_i\mathsf P_i(N\ge n).
\tag{7.6}
$$

Tonelli applies to the nonnegative sum even before its integrability is known, and gives

$$
\mathbb E_i\sum_{n=1}^N(K_n+1)=\sum_{n\ge1}\mu_i\mathsf P_i(N\ge n)=\mu_i\mathbb E_iN.
\tag{7.7}
$$

Combine Lemmas 2.3, 3.1 and 7.1 for finite expectation and the mean equality. This is predictable inclusion, not independence of a duration from its score or terminal decision. It prices this complete-gap controller; it asserts no complete-gap mean formula for an arbitrary observer stopping partway through zeros. $\square$

## 8. Both risk bounds with conditional rounding control

**Lemma 8.1 (Half-likelihood supermartingales).** The same actual table satisfies $\mathsf P_0(D=1)\le\alpha$ and $\mathsf P_1(D=0)\le\alpha$.

Proof. For $|x|\le1/2$, Taylor's integral remainder bounds $e^x-1-x$ by $e^{1/2}x^2/2\le x^2$. The inequality $e^{1/2}<2$ follows by comparing its power series to $\sum_{n\ge0}(1/2)^n$, strictly from $n=2$ onward. Thus $e^x\le1+x+x^2$ on that interval. Conditional on each actual category $z$, (6.2)–(6.4) and $\delta<1$ imply for either sign

$$
\mathbb E_i[e^{\pm\varepsilon_n/2}\mid Y_n=z]
\le1+\frac14\mathbb E_i[\varepsilon_n^2\mid Y_n=z]
\le1+\frac{\delta^2}{4}=1+\frac u4.
\tag{8.1}
$$

The coarser variance bound $\delta^2$ suffices. The exact unrounded identities are

$$
\mathbb E_0e^{\ell_{Y_n}/2}=\sum_z a_0(z)\sqrt{a_1(z)/a_0(z)}=A,\qquad
\mathbb E_1e^{-\ell_{Y_n}/2}=A.
\tag{8.2}
$$

Multiply the conditional bound by the category factor and then average, without assuming independence between category and rounding error. Since $V_n=\ell_{Y_n}+\varepsilon_n$,

$$
\mathbb E_0e^{V_n/2}\le A(1+u/4)=(1-u)(1+u/4)<1,\qquad
\mathbb E_1e^{-V_n/2}\le(1-u)(1+u/4)<1.
\tag{8.3}
$$

Independence of the next increment from $\mathcal F_n$ makes $e^{S_{n\wedge N}/2}$ a nonnegative supermartingale under source zero and $e^{-S_{n\wedge N}/2}$ one under source one. At a live step use (8.3); after exit the multiplier is one. Finite conditional iteration gives expectation at most one at every deterministic horizon $m$.

Lemmas 7.1–7.2 already prove finite gap stopping and actual finite paid means. By (7.3) the stopped exponentials are uniformly bounded by $e^{B/2}$. Bounded convergence as $m\to\infty$ gives

$$
\mathbb E_0e^{S_N/2}\le1,\qquad \mathbb E_1e^{-S_N/2}\le1.
\tag{8.4}
$$

A wrong label under source zero requires $S_N\ge H\delta$; under source one it requires $S_N\le-H\delta$. Restricting the nonnegative expectations to these events yields

$$
\mathsf P_0(D=1)\le e^{-H\delta/2},\qquad
\mathsf P_1(D=0)\le e^{-H\delta/2}\le e^{-R/2}=\alpha.
\tag{8.5}
$$

The argument uses finite-horizon conditional expectations and bounded convergence after finite stopping. It introduces no unproved auxiliary stop, infinite stopped-likelihood identity, external decision decoder or runtime exponential calculation. $\square$

## 9. Uniform resources and fixed-cutoff logarithmic attainment

**Theorem 9.1 (All permitted cutoffs on one neighborhood).** Fix $(r,c,\alpha)$ as in Section 1. With the source-only $s_*,\eta$ of Definition 3.2 there are constants $C_M,C_T>0$ depending only on these fixed parameters such that

$$
\begin{gathered}
\forall s\in(0,s_*)\ \forall L\in\mathbb Z,\ L\ge1,\ sL\le\eta:\\
\exists\text{ one common table satisfying (2.3)},\\
M(s,L)=3+\left(2\left\lceil\frac R{\sqrt{u(s,L)}}\right\rceil-1\right)(L+2)
\le C_M\frac{L+2}{s^r\sqrt{H_L}},\\
\max_{i\in\{0,1\}}\mathbb E_iT\le C_T\frac{s^{-(2r+1)}}{H_L}.
\end{gathered}
\tag{9.1}
$$

Proof. Use the table of Section 5. Lemmas 7.1–8.1 prove both errors, both actual almost-sure stops and both finite paid means for that same table. The ceiling gives $H\le R/\delta+1$, hence

$$
M\le3+(2R/\delta+1)(L+2)\le(2R+4)\frac{L+2}{\delta}.
\tag{9.2}
$$

By Lemma 4.2, $\delta\ge\sqrt{h_-}s^r\sqrt{H_L}$. Thus $C_M=(2R+4)/\sqrt{h_-}$ is sufficient and fixed before $L$.

For payment combine (7.5), the source moment bounds and (7.2). Since $0<u<1$,

$$
\mathbb E_iT\le\frac{C_\beta}{s}+\frac{C_\mu B}{2su}
\le\frac{C_\beta+C_\mu B/2}{su}
\le\frac{C_\beta+C_\mu B/2}{h_-}\frac{s^{-(2r+1)}}{H_L}.
\tag{9.3}
$$

This supplies a common $C_T$ and includes the initial wait. Every bound is simultaneous for the two laws under one table on the whole permitted interval. $\square$

**Theorem 9.2 (Each fixed positive cutoff exponent).** For each additionally fixed real $\theta\in(0,1]$ there exist $s_\theta>0$ and constants $C_{\theta,M},C_{\theta,T}>0$, depending only on $(r,c,\alpha,\theta)$, such that for every $0<s<s_\theta$ one common $q$-retuned table satisfies (2.3) and

$$
M\le C_{\theta,M}\frac{s^{-(r+\theta)}}{\sqrt{\log(1/s)}},\qquad
\max_i\mathbb E_iT\le C_{\theta,T}\frac{s^{-(2r+1)}}{\log(1/s)}.
\tag{9.4}
$$

Proof. After fixing $\theta$, choose one $s_\theta<s_*$ so that throughout $0<s<s_\theta$,

$$
\eta s^{-\theta}\ge2,\qquad \theta\log(1/s)\ge\max\{1,2|\log(\eta/2)|\}.
\tag{9.5}
$$

Set $L=\lfloor\eta s^{-\theta}\rfloor$. Since $\lfloor x\rfloor\ge x/2$ for $x\ge2$, one has $L\ge\eta s^{-\theta}/2\ge1$. Also $sL\le\eta s^{1-\theta}\le\eta$ because $s<1$ and $\theta\le1$, including $\theta=1$. Every hypothesis of Theorem 9.1 holds on this single neighborhood.

Integral comparison gives $\log(L+1)\le H_L\le1+\log L$. The cutoff and (9.5) imply

$$
\begin{aligned}
H_L&\ge\log L\ge\theta\log(1/s)+\log(\eta/2)\ge\tfrac\theta2\log(1/s),\\
H_L&\le1+\log L\le1+\theta\log(1/s)\le2\theta\log(1/s),\\
L+2&\le(\eta+2)s^{-\theta}.
\end{aligned}
\tag{9.6}
$$

Substitution proves (9.4), for example with $C_{\theta,M}=C_M(\eta+2)\sqrt{2/\theta}$ and $C_{\theta,T}=2C_T/\theta$. The same table meets every condition, with all constants and the neighborhood fixed before $s$. $\square$

The range of observed short lengths supplies the harmonic sum rather than a single-scale gain. A subtypical cutoff $s^{-\theta}$ for any fixed $\theta>0$ already retains a fixed positive fraction of $\log(1/s)$. This is one jointly implemented statistic of one history; no separately optimal scale controllers or incompatible optima are combined. Smaller fixed $\theta$ changes the constants and neighborhood. Theorem 9.2 supplies exponents arbitrarily close above $r$; it supplies neither an exponent-$r$ construction nor a limit with $\theta=\theta(s)$. It gives no optimality for the square-root logarithmic state factor.

## 10. The source-class existence gap and the unresolved state cost

**Definition 10.1 (Prior source-class port).** The delivered [exact source-class renewal frontier](FIB_SOURCE_CLASS_RENEWAL_RESOURCE_FRONTIER.md), Definitions 2.1 and 3.1, supplies the exact pair, stationary convention and common-design resource contract used here. Its Theorem 11.2 gives a critical lower sandwich and a fixed sufficient-capacity upper of order $s^{-(2r+1)}$. Its Open problem 11.3 asks for an actual-bit multiscale controller attaining a logarithmic paid improvement with a declared full budget. Theorems 9.1–9.2 provide that sufficient implementation for this exact critical pair. They resolve the existence component while leaving the minimum-budget and full-frontier components unresolved. The earlier volume's statements and other source classes retain their own hypotheses.

**Proposition 10.2 (Conditional lower context only).** Grant the prior source-class lower statement, with its own general lower-bound interfaces and constants. For a compliant observer with finite complete budget $M\ge2$, let $b=1-2\alpha$ and

$$
L_M=\max\left\{1,\left\lceil\left(\frac{2c(M-2)}b\right)^{1/r}\right\rceil\right\}.
\tag{10.1}
$$

The attributed statement is that on one source/risk neighborhood, with $A_->0$ independent of $M$,

$$
\mathbb E_iT\ge\frac{A_-s^{-(2r+1)}}{1+\log(\min\{L_M,1/s\})}
\ge\frac{A_-s^{-(2r+1)}}{\log(e/s)}.
\tag{10.2}
$$

Conditional on that statement, a compliant family attaining $\mathbb E_{i_\star}T\le C_{\rm paid}s^{-(2r+1)}/\log(1/s)$ for one fixed target and one fixed constant $C_{\rm paid}>0$ must satisfy

$$
1+\log(\min\{L_{M(s)},1/s\})\ge\frac{A_-}{C_{\rm paid}}\log(1/s).
\tag{10.3}
$$

In particular $\log(1+M(s))=o(\log(1/s))$ is incompatible with that paid upper.

Proof of the conditional implication. Intersect the family neighborhood with the prior lower neighborhood. Compare the positive bounds and cancel $s^{-(2r+1)}$ to obtain (10.3). The ceiling and maximum with one give $L_M\le C_LM^{1/r}$ for a fixed source/risk constant. Thus

$$
1+\log(\min\{L_{M(s)},1/s\})\le1+\log L_{M(s)}\le C+\frac1r\log(1+M(s)).
\tag{10.4}
$$

The right side is $o(\log(1/s))$ under the subpolynomial-budget condition, contradicting (10.3). $\square$

This is attributed conditional context, not a new converse or a re-verification of the prior forest/harmonic interfaces. No such interface is needed by the upper construction in Sections 2–9. If (10.2) is granted, its budget-independent lower and Theorem 9.2's upper have the same paid order, since $\log(e/s)$ and $\log(1/s)$ are comparable near zero. This concerns attainable paid order with a sufficient budget, not a matched budget-dependent threshold.

The paid constant matters: the sufficient constant in Theorem 9.2 can grow as fixed $\theta$ decreases. Comparing different $\theta$ values does not prove necessity or sufficiency of an exponent $r$ for a prescribed paid constant. The minimum sufficient configuration cost, a matching necessary power for a specified paid constant, sharp constants, exact optimizers and the full critical all-budget frontier remain open. The construction does not classify the minimum nonempty budget or every intermediate budget.

## 11. Mathematical credit, evidence and nontransfer boundaries

The source-relative new result is the explicit composition of the actually read saturated gap category with an unbiased finite evidence lattice, together with its uniform harmonic-affinity, rounding-risk, stopping and paid-resource bounds. Power-series differentiation, equilibrium renewal normalization, Cauchy–Schwarz, chi-square domination, Hellinger affinity, relative entropy, likelihood testing, unbiased stochastic rounding, finite conditional drift, exponential supermartingales, bounded convergence and Tonelli's theorem are classical methods. Their use is not a claim to have invented them.

The supplied critical proposal's eight arguments and independent handwritten check C1–C9 concern this category/lattice construction under the stated model. Their mathematical roles are the source and cutoff estimates, complete row realization, both drift and risk directions, predictable payment and fixed-$\theta$ quantifiers displayed here. They are fallible ordinary evidence, not approval of this authored exposition or a Lean/kernel certificate. The upper is proved in full above rather than inferred from a supplier verdict or from full-gap entropy alone. The source-class lower is separately attributed in Proposition 10.2; secondary references and general lower interfaces inside that volume are not silently imported as new evidence for this upper.

As described in the supplied proposal and check, the DEV coherent reference concerns reheralded coherent windows, isometry access, joint-angle noise, total-count-commuting terminal measurements and retained setting/outcome records. Those inputs, resets, measurements and records differ from an uninterrupted stationary classical bit history with a finite persistent configuration set. No map preserving observation, permitted operations and charged resources is established here. Its reheralding supplies no source reset or free iid gap here; coherent measurements supply no classical terminal decoder; retained trial records supply no uncounted archive; and unknown-moment inversion supplies no calibration for this table. No DEV rate, spectral bound or resource theorem enters the proofs. The shared methodological point is only that information must be accompanied by an actual controller with every retained resource charged.

Complete configurations are all-history mutable states, not expected or typical-history memory. Their indices could be encoded with $\lceil\log_2M\rceil$ mutable bits, but that does not price immutable probability precision, exact-coin realization, design computation or physical storage. The paid resource is the number of actual source bits read, not physical elapsed time. No rational-only coin, finite-description table, physical, neural, hardware, empirical machine-learning, producer-dimension or broader-project completion claim follows.

The exact positive equality (1.1) and its normalization are essential to the category estimates. The source-class volume's sparse-pair example shows why a tail upper envelope alone does not determine a paid frontier. No transfer to the older rational-center polynomial $H_c$, general signed or oscillating perturbations, or other source shapes is proved. Such transfers require their own information estimate and lawful counted implementation. Known common $q$ is part of the design contract; unknown-$q$ testing, one $q$-independent table, all-interior-$q$ realization, changing-parameter uniformity and a varying $\theta(s)$ require separate arguments. No external priority audit or global originality conclusion is supplied.

## 追加锚（本行以下为增补区）
