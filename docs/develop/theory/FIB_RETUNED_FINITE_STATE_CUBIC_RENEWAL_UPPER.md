# Retuned finite-state cubic renewal upper bounds

## 1. Scope and ownership

This volume gives a finite stochastic observer for one exact pair of stationary binary renewal laws. At a known common parameter $q=e^{-s}$ sufficiently close to one, one source-blind table and one common initialization use $O_{H_c,\alpha}(s^{-1})$ complete persistent configurations and have paid mean $O_{H_c,\alpha}(s^{-3})$ under each true label. Both wrong-label probabilities are at most a fixed $0<\alpha<1/2$, both actual stopping times are almost surely finite, and both pointwise paid means are finite. Every source bit read before the internally emitted decision is charged.

The exact polynomial, all-integer envelope, stationary law and moment estimates are supplied by [Real renewal instruments and detector rank: finite observer memory](FIB_REAL_RENEWAL_INSTRUMENTS_AND_DETECTOR_RANK_CONTINUATION.md), Definitions 23.1–23.2. Its Proposition 27.2 already supplies the geometric-kernel separation used here. That proposition's three-state row example is a counterexample to a uniform kernel estimate, not a classifier satisfying the two risks. The finite survival-flag and midpoint-walk construction developed below is supplied upper-side mathematical content; this volume presents its complete operational realization and ordinary proof. Geometric marking, gambler's ruin, finite-horizon drift summation, bounded martingale convergence and predictable sums are classical methods.

The observation contract is the known-common-$q$ class of [Retuned bounded-memory uniform renewal converse](FIB_RETUNED_BOUNDED_MEMORY_UNIFORM_RENEWAL_CONVERSE.md), Definition 3.1. The necessary configuration-growth comparison is the supplied Theorem 10.1 of [Growing state budgets in the renewal paid-mean tradeoff](FIB_GROWING_STATE_BUDGET_RENEWAL_TRADEOFF.md). Its necessary exponent $4/5$ and the sufficient exponent $1$ here do not match. No optimal exponent or minimum budget is identified.

This is standalone handwritten reference theory conditional on the explicitly stated source premises. Nested proofs and references in the suppliers are credited at their stated scope. The construction, calibration and resource assertions below concern the abstract observation model; they supply no formal-verification certificate or external novelty certification. Corrections and extensions belong after the final append anchor.

## 2. Exact source and stationary payment convention

**Definition 2.1 (The fixed rational-center shapes).** For a real argument $x$, fix

$$
\begin{aligned}
H_c(x)=x^9+\frac1{35\cdot10^{24}}\bigl(&55800726477138x-224986136658885x^2
+420664314485485x^3\\
&-540138133491075x^4+518234977000797x^5
-254383031435085x^6\\
&+77668004560980x^7+43377331415040x^8\bigr).
\end{aligned}
\tag{2.1}
$$

Write $H=H_c$, $F_0(x)=x^9$, $F_1(x)=H(x)$, and

$$
\delta=\frac{2749658638697}{10^{24}},\qquad
B=1+\delta,\qquad
a=\frac{43377331415040}{35\cdot10^{24}}>0.
\tag{2.2}
$$

The credited all-integer premise is

$$
\begin{gathered}
k^9\le F_i(k)\le Bk^9\quad(i=0,1),\\
1\le\frac{H(k)}{k^9}\le1+\frac\delta k
\quad(k\in\mathbb Z,\ k\ge1).
\end{gathered}
\tag{2.3}
$$

This is exactly the continuation's equation (23.3), with its rational-center polynomial and degree-eight coefficient $a$. It is an assumption for all positive integers, not a conclusion from finitely many evaluations. Neither a varying residual polynomial nor a limiting residual-zero vector is substituted for $H_c$.

**Definition 2.2 (One stationary binary history).** For $i\in\{0,1\}$ and $0<q<1$, define

$$
\begin{aligned}
Z_i(q)&=\sum_{k\ge1}F_i(k)q^k,
&f_{i,q}(k)&=\frac{F_i(k)q^k}{Z_i(q)}\quad(k\ge1),
&f_{i,q}(0)&=0,\\
S_{i,q}(b)&=\sum_{k\ge b}f_{i,q}(k)\quad(b\ge0),
&\mu_i(q)&=\sum_{k\ge1}(k+1)f_{i,q}(k),\\
\beta_i(q)&=\frac{\sum_{k\ge1}k(k+1)f_{i,q}(k)}{2\mu_i(q)}.
\end{aligned}
\tag{2.4}
$$

All sum indices are integers. Polynomial growth and $0<q<1$ make every displayed sum finite, and $Z_i(q)>0$. The source law $\mathsf P_{i,q}$ first draws a time $\tau$ with

$$
\mathsf P_{i,q}(\tau=b)=\frac{S_{i,q}(b)}{\mu_i(q)}
\quad(b=0,1,\ldots).
\tag{2.5}
$$

It places zeros at $0,\ldots,\tau-1$ and a one at $\tau$. Independently of $\tau$, draw iid $K_1,K_2,\ldots$ with mass function $f_{i,q}$ and put subsequent ones at

$$
\tau_0=\tau,\qquad
\tau_n=\tau+\sum_{r=1}^n(K_r+1)\quad(n\ge1).
\tag{2.6}
$$

Every other bit of $X_0,X_1,\ldots$ is zero. A tick means a bit equal to one. The variable $K_n\ge1$ counts zeros between ticks; a complete post-tick interval costs $K_n+1$ reads through its closing tick. The first interval has the stationary forward-wait law (2.5), not the law of $K_n$.

For completeness, $S_{i,q}(0)=S_{i,q}(1)=1$. Nonnegative summation gives

$$
\begin{aligned}
\sum_{b\ge0}S_{i,q}(b)
&=\sum_{k\ge1}(k+1)f_{i,q}(k)=\mu_i(q),\\
\mathbb E_{i,q}\tau
&=\frac1{\mu_i(q)}\sum_{k\ge1}\left(\sum_{b=0}^k b\right)f_{i,q}(k)
=\beta_i(q).
\end{aligned}
\tag{2.7}
$$

Each $k$ occurs for exactly $b=0,\ldots,k$ in the first sum; its total weight in the second is $k(k+1)/2$. Thus (2.5) is normalized and has the claimed finite mean. These identities also cover $\tau=0$: the first one itself still costs one read.

**Assumption 2.3 (Supplied endpoint moments).** As $s=-\log q\downarrow0$, the continuation's equation (23.7) supplies, for both labels,

$$
Z_i(e^{-s})=9!s^{-10}(1+O_H(s)),\qquad
\mu_i(e^{-s})=\frac{10}{s}+O_H(1),\qquad
\beta_i(e^{-s})=\frac{11}{2s}+O_H(1).
\tag{2.8}
$$

All constants implicit in these source estimates concern the one fixed $H_c$. They are not estimates uniform over changing polynomial shapes.

## 3. Known parameter, complete configurations and six obligations

**Definition 3.1 (The permitted observer).** At a selected known common $q\in(0,1)$, the designer may choose a finite configuration set, initialization and real transition probabilities using $(q,H_c,\alpha)$. The chosen table and initialization are identical under $\mathsf P_{0,q}$ and $\mathsf P_{1,q}$. The true label and source-dependent advice are unavailable. The design may change arbitrarily with $q$; no continuity or lower bound on positive transition probabilities is assumed.

Every persistent configuration is counted: waiting and other control phases, registers, walk values, flags, retained random choices, stored seeds and both internally emitted decision labels. Fresh coins are independent of the source and previous fresh coins. A retained seed, random-tape index or counter for choosing random updates would be counted information. Immutable design constants and their exact real-probability precision are permitted by this abstract contract, without a description-size or calibration-computation bound.

Each nonterminal action reads the next bit of the single history in Definition 2.2. Choices use only the present configuration, the bit just read and fresh allowed randomness. There is no external clock, age, elapsed-read counter, program counter, archive, skipped bit, free gap, reset, parallel copy, extra source, hidden-state observation, parameter response or probability response. Known $q$ is design information, not a query to the actual source. The mathematical cost tally is unavailable to the controller. The output $D\in\{0,1\}$ is its emitted label; an external recipient does not decode $D$ from the time of stopping.

If the actual prefix $X_0,\ldots,X_{T-1}$ is read, the paid cost is $T$. Every initial zero, tick, subsequent zero, holding interval and terminal read is paid. In the general contract an observer may stop without reading, at cost zero, or inside a gap, paying its observed prefix. Compliance at this selected $q$ means all six conditions

$$
\begin{gathered}
\mathsf P_{0,q}(D=1)\le\alpha,\qquad
\mathsf P_{1,q}(D=0)\le\alpha,\\
\mathsf P_{i,q}(T<\infty)=1,\qquad
\mathbb E_{i,q}T<\infty\quad(i=0,1).
\end{gathered}
\tag{3.1}
$$

Write $\mathfrak A_M(q,\alpha)$ for the compliant machines with at most $M$ complete configurations, as in the uniform companion. The new controller is a family of such pointwise designs. It is not required to be one unchanged table over unknown parameters or to separate two full nuisance families with independently varying parameters.

## 4. Calibration and the complete bit-transition table

**Definition 4.1 (Immutable calibration on the positive-separation branch).** Set

$$
\begin{aligned}
p_i(q)&=\frac{Z_i(q^2)}{Z_i(q)},&\Delta(q)&=p_1(q)-p_0(q),\\
t&=\frac{p_0(q)+p_1(q)}2,&d&=\frac{\Delta(q)}2,\\
\ell&=\log\frac{1-\alpha}{\alpha},&L&=\left\lceil\frac\ell d\right\rceil
=\left\lceil\frac{2\ell}{\Delta(q)}\right\rceil.
\end{aligned}
\tag{4.1}
$$

This section assumes $\Delta(q)>0$. Since $p_i(q)=\mathbb E_{i,q}q^{K_1}$ and $K_1\ge1$, $0<p_i(q)\le q<1$. Therefore $0<p_0<p_1<1$, $0<t<1$, $d>0$ and $\ell>0$. The integer $L$ is finite and at least one. Both public shape probabilities are used to calibrate a single source-blind table. They are not observed statistics or runtime arithmetic registers.

**Definition 4.2 (Configurations, successors and actions).** The entire persistent configuration set is

$$
\mathcal S_q=\{w,d_0,d_1\}\cup
\{(j,h):j\in\mathbb Z,\ -L<j<L,\ h\in\{0,1\}\}.
\tag{4.2}
$$

Initialize deterministically at $w$ under both labels. Every configuration other than $d_0,d_1$ commits to a next paid read. Entry into $d_i$ emits $D=i$ and stops immediately, without another read. For an interior $j$, the immutable successor lookups are

$$
\begin{aligned}
U(j)&=\begin{cases}d_1,&j=L-1,\\(j+1,1),&j<L-1,\end{cases}\\
V(j)&=\begin{cases}d_0,&j=-L+1,\\(j-1,1),&j>-L+1.\end{cases}
\end{aligned}
\tag{4.3}
$$

The walk coordinate $j$ records accumulated evidence. The flag $h=1$ means that all survival trials on zeros since the last observed tick have succeeded; $h=0$ means at least one failed. The complete table is:

| Current configuration | Actual bit just read | Destination distribution |
| --- | --- | --- |
| $w$ | $0$ | $w$ with probability $1$ |
| $w$ | $1$ | $(0,1)$ with probability $1$ |
| $(j,1)$ | $0$ | $(j,1)$ with probability $q$; $(j,0)$ with probability $1-q$ |
| $(j,0)$ | $0$ | $(j,0)$ with probability $1$ |
| $(j,1)$ | $1$ | $U(j)$ with probability $1-t$; $(j,1)$ with probability $t$ |
| $(j,0)$ | $1$ | $V(j)$ with probability $t$; $(j,1)$ with probability $1-t$ |
| $d_0$ | either bit | $d_0$ with probability $1$ in analytical continuation |
| $d_1$ | either bit | $d_1$ with probability $1$ in analytical continuation |

Each random row uses a fresh independent coin. The decision rows specify the analytical extension only: the actual machine has already stopped. A failed survival trial changes only the internal flag. It does not stop the read sequence, reset the source, or skip the remaining zeros or closing one. Every nonterminal one transition resets the internal flag to one for the next gap. Holding at the same $j$ is therefore still a completed, paid gap. No distinct mark register is needed, since the pre-one flag selects the evidence update.

**Lemma 4.3 (Total rows and exact full count).** The table defines a legal finite observer with exactly $4L+1$ listed configurations and no additional persistent state. It is defined for every finite bit and coin history, including consecutive ones and the case $L=1$.

Proof. All probabilities are in $[0,1]$ and each row sums to one. An upward step from the largest interior coordinate selects $d_1$, and a downward step from the smallest selects $d_0$; all other successors are in (4.2). Holding and zero transitions remain in that set. The first one enters $(0,1)$, which exists since $L\ge1$.

There are $2L-1$ interior integers, each with two flag values. Adding one waiting state and two emitted labels gives

$$
|\mathcal S_q|=1+2+2(2L-1)=4L+1.
\tag{4.4}
$$

The successor functions are finite table lookups, not computations requiring an uncounted register. The only retained random consequences are $j$ and $h$. There is no gap counter, elapsed-read counter, seed, random-tape position or separate control state. The state count is over all possible histories, not just typical or terminating ones.

If $L=1$, the only interior coordinate is $j=0$; $U(0)=d_1$ and $V(0)=d_0$, while both holding rows remain defined. A consecutive one from $(j,1)$ follows its ordinary one row; a one from any other listed state also has its displayed destination. Consecutive post-tick ones have probability zero under $K_n\ge1$, but the table is total even on those inputs. Arbitrarily many initial zeros loop at $w$, and arbitrarily many zeros after a flag failure loop at $(j,0)$. Neither behavior creates a new configuration or a deterministic deadline. $\square$

## 5. Same-gap marks and the supplied separation

**Lemma 5.1 (IID potential marks from actual zero transitions).** After the first observed tick, the potential flag values at successive closing ticks are iid Bernoulli variables with parameter $p_i(q)=Z_i(q^2)/Z_i(q)$ under source $i$, independent of $\tau$. The actual flags used by the controller form the stopped prefix of this potential sequence. Independence between a mark and its own gap duration is not asserted.

Proof. A gap starts with flag one. Conditional on $K_n=k$, it has exactly $k$ zero transitions. Its flag is still one at the closing tick exactly when all $k$ survival trials succeed, an event with conditional probability $q^k$. After the first failure the remaining zero transitions leave flag zero, but every zero and the closing one is read. Therefore

$$
\mathsf P_{i,q}(\text{closing flag}=1)
=\sum_{k\ge1}\frac{F_i(k)q^k}{Z_i(q)}q^k
=\frac{Z_i(q^2)}{Z_i(q)}=p_i(q).
\tag{5.1}
$$

To make independence precise, use an analytical probability space with, for every gap, its own independent sequence of Bernoulli$(q)$ survival coins and an independent Bernoulli$(t)$ closing coin. All these supplies are independent of the source. The potential mark $A_n$ is the product of the first $K_n$ survival outcomes. Unused outcomes after a failure, and potential blocks after absorption, need never be drawn by the actual machine. They only define a continuation for analysis; they provide no accessible random tape or extra reads.

The blocks consisting of $K_n$, its survival coins and its closing coin $C_n$ are independent and identically distributed, and are independent of $\tau$. Consequently $(A_n,C_n)$ are iid potential pairs with $A_n\sim\operatorname{Bernoulli}(p_i)$ and $C_n\sim\operatorname{Bernoulli}(t)$ independent within each pair. Every nonterminal closing tick initializes the next flag at one, so the table implements these pairs up to its absorption. In particular the next pair is independent of all preceding gaps, coins and walk coordinates before absorption. The stopped prefix need not be an unconditioned fixed-length iid sample. Since its conditional success probability is $q^k$, the mark retains dependence on $K_n$; no payment step below removes that dependence. $\square$

**Lemma 5.2 (Credited endpoint separation).** With

$$
c=\frac{a}{9\cdot2^{10}}>0,
\tag{5.2}
$$

the supplied geometric-kernel statistic satisfies

$$
\Delta(e^{-s})=cs+O_H(s^2).
\tag{5.3}
$$

In particular $\Delta(e^{-s})\ge cs/2>0$ on a sufficiently small source-only endpoint neighborhood.

Proof by the supplied correspondence. Proposition 27.2 of the continuation gives, with $R(s)=Z_1(e^{-s})/Z_0(e^{-s})$,

$$
R(s)=1+\frac a9s+O_H(s^2),\qquad
\frac{Z_0(e^{-2s})}{Z_0(e^{-s})}=2^{-10}+O(s).
\tag{5.4}
$$

These are source-owned polynomial-geometric estimates, including the degree-eight coefficient $a$. For the same $p_i$ as in (5.1), the exact identity is

$$
\Delta(e^{-s})
=\frac{Z_0(e^{-2s})}{Z_0(e^{-s})}
\left(\frac{R(2s)}{R(s)}-1\right).
\tag{5.5}
$$

The denominator $R(s)$ tends to one. Dividing the two expansions gives $R(2s)/R(s)-1=(a/9)s+O_H(s^2)$; multiplying in (5.5) gives precisely (5.3), the continuation's separation formula (27.3). The positive sign is fixed by $a>0$. A bound on the absolute remainder by $C_\Delta s^2$ then makes it at most $cs/2$ when $s$ is sufficiently small. This is reuse of the supplied separation, not a new polynomial or kernel estimate. Its original row counterexample alone had no risk, accumulation or paid-mean guarantee; those require the controller and the next sections. $\square$

## 6. Lazy walk, finite stopping and exact risks

**Lemma 6.1 (Step probabilities and finite mean gap count).** Fix any $q\in(0,1)$ with $\Delta(q)>0$. At an interior walk coordinate under source $i$, the probabilities of an upward, downward and holding update are respectively

$$
u_i=p_i(1-t),\qquad v_i=(1-p_i)t,\qquad
w_i=p_it+(1-p_i)(1-t)=1-u_i-v_i.
\tag{6.1}
$$

Both $u_i,v_i$ are positive. Let $J_0=0$, freeze the walk at its first boundary, and let

$$
N=\inf\{n\ge0:|J_n|=L\}.
\tag{6.2}
$$

Thus $N$ counts completed post-first-tick gaps through the terminal one. Under each source,

$$
u_0-v_0=-d,\qquad u_1-v_1=d,\qquad
\mathbb E_{i,q}N\le\frac Ld=\frac{2L}{\Delta(q)}<\infty,
\qquad \mathsf P_{i,q}(N<\infty)=1.
\tag{6.3}
$$

Proof. For a potential pair in Lemma 5.1, its proposed increment is $A_n-C_n$. It is $+1$ exactly on $(A_n,C_n)=(1,0)$, and $-1$ exactly on $(0,1)$. The other two pairs give increment zero. This proves (6.1), its stochastic normalization and positivity. Direct subtraction gives

$$
u_i-v_i=p_i-t,
\tag{6.4}
$$

which has the two stated signs by the midpoint choice. No label-dependent table or initialization is used.

For the stopping proof, let $\mathcal F_n$ contain $\tau$, the first $n$ complete gaps and their coins. Use only past blocks in this filtration, so the next block retains its independent law. Define the analytical signed coordinate $V_n=-J_n$ under source zero and $V_n=J_n$ under source one. The sign is for the proof; it is not given to the machine. Before $N$ its conditional drift is $d$, and after $N$ it is zero. For every finite integer $m\ge1$, summing finitely many conditional expectations gives

$$
\begin{aligned}
\mathbb E_i V_m
&=d\sum_{n=0}^{m-1}\mathsf P_i(N>n)
=d\,\mathbb E_i(N\wedge m),\\
\mathbb E_i(N\wedge m)&\le\frac Ld,
\end{aligned}
\tag{6.5}
$$

where $V_0=0$ and $V_m\le L$ were used. Monotone convergence now gives the finite mean bound in (6.3). An extended nonnegative random variable with finite mean is finite almost surely, proving the other assertion. This proves finite stopping before any unbounded stopping formula is invoked.

The same finite-horizon calculation from an arbitrary tick-boundary state $(j,1)$ gives a mean at most $(L-V_0)/d\le2L/d$. Holding steps require no exceptional argument: they have zero increment and are already included in (6.5). A boundary cannot be overshot, since each move has size one and the table absorbs upon reaching it. All statements include $L=1$. $\square$

**Theorem 6.2 (Exact errors and both risk bounds).** For the same controller, put $\rho_i=v_i/u_i$. Then $\rho_0>1$ and $0<\rho_1<1$. Its wrong-label probabilities are exactly

$$
e_0:=\mathsf P_{0,q}(D=1)=\frac1{1+\rho_0^L},\qquad
e_1:=\mathsf P_{1,q}(D=0)=\frac1{1+\rho_1^{-L}},
\tag{6.6}
$$

and each is at most $\alpha$.

Proof. The signs follow from $v_0-u_0=d$ and $u_1-v_1=d$, with all move probabilities positive. At any interior coordinate, the conditional multiplier of $\rho_i^{J_n}$ is

$$
u_i\rho_i+v_i\rho_i^{-1}+w_i
=v_i+u_i+w_i=1.
\tag{6.7}
$$

After absorption its multiplier is also one. Thus $\rho_i^{J_n}$ is a martingale with initial value one. For this fixed $q$ and finite $L$, it is bounded between the smaller and larger of $\rho_i^{-L}$ and $\rho_i^L$. Lemma 6.1 has already proved $N<\infty$ almost surely. Bounded convergence at deterministic $n\to\infty$ therefore gives, with $H_i=\mathsf P_i(J_N=L)$,

$$
1=H_i\rho_i^L+(1-H_i)\rho_i^{-L}.
\tag{6.8}
$$

Because $\rho_i\ne1$, solving yields

$$
H_i=\frac{1-\rho_i^{-L}}{\rho_i^L-\rho_i^{-L}}
=\frac1{1+\rho_i^L}.
\tag{6.9}
$$

The upper boundary emits one and the lower emits zero, so $e_0=H_0$ and $e_1=1-H_1$, proving (6.6). This derivation includes the holding probability in (6.7); it does not replace holding gaps by free trials.

For $0<x<y$, integration gives $\log(y/x)=\int_x^y z^{-1}\,dz\ge(y-x)/y$. Apply this to $(u_0,v_0)$ and to $(v_1,u_1)$. Since $v_0\le1$ and $u_1\le1$,

$$
\log\rho_0\ge\frac d{v_0}\ge d,\qquad
\log\rho_1^{-1}\ge\frac d{u_1}\ge d.
\tag{6.10}
$$

The ceiling in (4.1) ensures $Ld\ge\ell$. Each error in (6.6) is consequently at most

$$
\frac1{1+e^{Ld}}\le\frac1{1+e^\ell}=\alpha.
\tag{6.11}
$$

This also covers arbitrarily small positive $\ell$ and the resulting possibility $L=1$. All martingale bounds here are at the selected finite $L$; no uniform martingale bound across changing designs was needed. $\square$

**Corollary 6.3 (Exact mean number of completed gaps).** For each $i=0,1$,

$$
\mathbb E_{i,q}N
=\frac Ld(1-2e_i)
=\frac{2L}{\Delta(q)}(1-2e_i).
\tag{6.12}
$$

Proof. The coordinate in (6.5) is bounded by $L$ in absolute value and converges almost surely to $V_N$. Bounded convergence on its left side and monotone convergence on its right side give $\mathbb E_iV_N=d\mathbb E_iN$. Under either proof sign, the correct label has $V_N=L$ and the wrong label has $V_N=-L$. Hence $\mathbb E_iV_N=L(1-2e_i)$, proving (6.12). Finite mean was established before taking this limit. Positivity also follows since $e_i\le\alpha<1/2$. No independence of $N$ from gaps or marks is used. $\square$

## 7. Actual-bit stopping and predictable payment

**Theorem 7.1 (Exact paid mean under each source).** At any fixed $q$ with $\Delta(q)>0$, the table satisfies both almost-sure actual stops and both finite pointwise means. Its actual paid length obeys

$$
T=1+\tau+\sum_{n=1}^{N}(K_n+1)
\quad\text{almost surely},
\tag{7.1}
$$

and, for each $i=0,1$,

$$
\mathbb E_{i,q}T
=1+\beta_i(q)+\mu_i(q)\mathbb E_{i,q}N
=1+\beta_i(q)+\frac{2\mu_i(q)L}{\Delta(q)}(1-2e_i)<\infty.
\tag{7.2}
$$

Proof. State $w$ reads all $\tau$ initial zeros and the first actual one. It incurs exactly $\tau+1$ reads and then enters $(0,1)$; it takes no mark from that stationary interval. Under Definition 2.2 this interval is finite almost surely and has expected cost $1+\beta_i$, including the case $\tau=0$.

Thereafter the table starts a next gap exactly when the preceding tick left it active. It never stops during zeros. In particular a failure of the survival flag still reads the entire suffix, and a holding update still completes the entire next interval. By Lemma 6.1, $N$ is finite almost surely under each label. Every $K_n$ is finite almost surely. Their countable intersection has probability one, so this finite random list of intervals reaches an actual finite tick time $\tau_N$. The terminal bit is $X_{\tau_N}=1$, and it is read before the label is emitted. Thus $T=\tau_N+1$, proving (7.1) and both actual almost-sure stopping assertions. An infinite initial wait or gap has zero probability under the stated law, although the finite table is defined on every arbitrarily long finite wait or gap.

For each $n\ge1$, the event $\{N\ge n\}$ means that no boundary was reached in the preceding $n-1$ updates. It belongs to $\mathcal F_{n-1}$ from Lemma 6.1. The next length $K_n$ is independent of that sigma-field, even though $A_n$ and the eventual update can depend on $K_n$. Hence

$$
\mathbb E_i\bigl[(K_n+1)\mathbf1_{\{N\ge n\}}\bigr]
=\mu_i(q)\mathsf P_i(N\ge n).
\tag{7.3}
$$

Tonelli's theorem for the nonnegative sum gives

$$
\begin{aligned}
\mathbb E_i\sum_{n=1}^{N}(K_n+1)
&=\sum_{n\ge1}\mathbb E_i\bigl[(K_n+1)\mathbf1_{\{N\ge n\}}\bigr]\\
&=\mu_i(q)\sum_{n\ge1}\mathsf P_i(N\ge n)
=\mu_i(q)\mathbb E_iN.
\end{aligned}
\tag{7.4}
$$

Combining (2.7), (6.12), (7.1) and (7.4) gives (7.2). The source's $\mu_i$ and $\beta_i$ are finite at every interior $q$, and Lemma 6.1 gives finite $\mathbb E_iN$ separately for both labels. Therefore both read means are finite.

The predictable event in (7.3) concerns beginning the next gap, not deciding after that gap. No independence between a duration and its own mark, terminal decision or $N$ is claimed. The identity prices the same actual history used for the evidence, including the stationary first wait, every survival-failure suffix, every holding gap and the terminal one. No closing tick of an unread continuation is charged, and no completed interval was observed for free. $\square$

Combining Theorem 6.2 with Theorem 7.1 proves every condition in (3.1) on the positive-separation branch. In particular

$$
\mathcal A_q\in\mathfrak A_{4L+1}(q,\alpha)
\quad\text{whenever }\Delta(q)>0.
\tag{7.5}
$$

## 8. One source-only neighborhood and quantitative cubic bounds

**Theorem 8.1 (Finite-state endpoint upper bound).** For the exact source premises of Section 2 and the supplied separation in Lemma 5.2, there is $s_*>0$ depending only on $H_c$, with $s_*\le1$, such that for every $0<\alpha<1/2$ and every $0<s<s_*$, the table at $q=e^{-s}$ has $\Delta(q)>0$ and satisfies all six obligations (3.1). With $c$ and $\ell$ as above, its full count $M(q)=4L+1$ and both paid means satisfy

$$
M(q)\le\left(\frac{16\ell}{c}+5\right)s^{-1},
\tag{8.1}
$$

$$
\mathbb E_{i,e^{-s}}T
\le\left(\frac{176\ell}{c^2}+\frac{44}{c}+7\right)s^{-3}
\quad(i=0,1).
\tag{8.2}
$$

Proof. The source estimates give finite nonnegative constants $C_\Delta,C_\mu,C_\beta$ and positive radii $r_\Delta,r_\mu,r_\beta$, chosen using only $H_c$, such that

$$
\begin{aligned}
|\Delta(e^{-s})-cs|&\le C_\Delta s^2&& (0<s<r_\Delta),\\
\left|\mu_i(e^{-s})-\frac{10}{s}\right|&\le C_\mu&& (0<s<r_\mu,\ i=0,1),\\
\left|\beta_i(e^{-s})-\frac{11}{2s}\right|&\le C_\beta&& (0<s<r_\beta,\ i=0,1).
\end{aligned}
\tag{8.3}
$$

For the two labels take the maximum of their bounds and minimum of their radii. A precise permissible source-only choice is

$$
s_*=
\min\left\{1,r_\Delta,r_\mu,r_\beta,
\frac{c}{2(1+C_\Delta)},
\frac1{1+C_\mu},
\frac1{2(1+C_\beta)}\right\}>0.
\tag{8.4}
$$

The additions of one make this choice valid even when a remainder bound is zero. For all $0<s<s_*$, (8.3)–(8.4) imply simultaneously

$$
\Delta(e^{-s})\ge\frac{cs}{2}>0,\qquad
\mu_i(e^{-s})\le\frac{11}{s},\qquad
\beta_i(e^{-s})\le\frac6s
\quad(i=0,1).
\tag{8.5}
$$

For example $sC_\mu\le1$ and $sC_\beta\le1/2$, which give the latter two bounds. This neighborhood does not depend on $\alpha$, the chosen table or the true label.

The ceiling contributes its full additive constant:

$$
L\le\frac{2\ell}{\Delta}+1
\le\frac{4\ell}{cs}+1,
\qquad
4L+1\le\frac{16\ell}{cs}+5
\le\left(\frac{16\ell}{c}+5\right)s^{-1}.
\tag{8.6}
$$

The last inequality uses $s\le1$. The waiting state, flags and both labels were already included in $4L+1$. Lemma 6.1 gives, separately for each source,

$$
\mathbb E_iN\le\frac{2L}{\Delta}
\le\frac{4\ell}{\Delta^2}+\frac2\Delta
\le\frac{16\ell}{c^2s^2}+\frac4{cs}.
\tag{8.7}
$$

Use (7.2), (8.5) and $1+\beta_i\le7/s$ to obtain

$$
\begin{aligned}
\mathbb E_iT
&\le\frac7s+\frac{11}{s}
\left(\frac{16\ell}{c^2s^2}+\frac4{cs}\right)\\
&=\frac{176\ell}{c^2}s^{-3}+\frac{44}{c}s^{-2}+7s^{-1}\\
&\le\left(\frac{176\ell}{c^2}+\frac{44}{c}+7\right)s^{-3}.
\end{aligned}
\tag{8.8}
$$

Again $s\le1$ justifies the final comparison. Theorems 6.2 and 7.1 give the risks and both stopping and finite-mean conditions at every parameter in this neighborhood. All estimates concern the same source-blind table at each selected $q$. $\square$

## 9. Optional all-interior-parameter family using the credited fallback

The endpoint theorem needs no fallback. This section records the existing fixed classifier so that a design may also be selected at every interior $q$ without assuming a global sign for $\Delta(q)$. The construction, sum-four certificate, threshold and performance in this section are supplied by the continuation's Definition 26.1, Lemmas 26.2–26.3 and Theorem 26.4, also restated in Section 8 of the uniform companion. Their argument is exposed here as conditional source credit; it is not additional upper-construction content.

**Assumption 9.1 (Supplied conditional sum-four certificate).** Put

$$
\begin{aligned}
C_i&=F_i(2)^2+2F_i(1)F_i(3),&
\theta_i&=\frac{F_i(2)^2}{C_i},\\
\Delta_\theta&=\theta_0-\theta_1,&
V_\theta&=\max_{i=0,1}\theta_i(1-\theta_i).
\end{aligned}
\tag{9.1}
$$

For $r_k=H(k)/k^9$, the exact supplied certificate is

$$
r_1r_3-r_2^2
=\frac{520040714516414119558257878908551006355871}
 {331776\cdot10^{48}}>0,
\qquad 0<\theta_1<\theta_0<1.
\tag{9.2}
$$

The rational equality is credited rather than recalculated. The sign is equivalent to the strict comparison of the two conditional $(2,2)$ probabilities because all $F_i(k)$ are positive. In particular $\Delta_\theta,V_\theta>0$. Choose once a rational $0<\alpha_0\le\alpha$ and define the supplied finite sample count, threshold and sufficient complete-state bound

$$
n_\alpha=\left\lceil\frac{8V_\theta}{\alpha_0\Delta_\theta^2}\right\rceil,
\qquad b_{n_\alpha}=\left\lceil\frac{n_\alpha(\theta_0+\theta_1)}2\right\rceil,
\qquad S_\alpha=10n_\alpha(n_\alpha+1)+3.
\tag{9.3}
$$

The continuation calls this sample count $M$; it is renamed here to distinguish it from a complete configuration budget.

**Definition 9.2 (Entire supplied fallback table).** Use a waiting state $w$, the two labels $d_0,d_1$, and the active configurations

$$
(z,p,m,v),\qquad
z\in\{0,1,2,3,4\},\quad p\in\{\varnothing,1,2,3\},\quad
0\le m<n_\alpha,\quad 0\le v\le m.
\tag{9.4}
$$

The zero count $z$ is saturated at four, $p$ is a pending retained category, $m$ counts accepted pairs, and $v$ counts their one marks. Initialize at $w$. Every nonlabel state orders a next actual paid read, and entry into a label stops immediately. In a row accepting a pair, the abbreviations $m'=m+1$ and $v'=v+\mathbf1_{\{p=z=2\}}$ denote successor lookups in the fixed finite table, not extra mutable workspace.

| Current state and condition | Actual bit | Deterministic destination |
| --- | --- | --- |
| $w$ | $0$ | $w$ |
| $w$ | $1$ | $(0,\varnothing,0,0)$ |
| $(z,p,m,v)$, every active state | $0$ | $(\min\{z+1,4\},p,m,v)$ |
| $(z,p,m,v)$, $z=0$ or $z=4$ | $1$ | $(0,p,m,v)$ |
| $(z,\varnothing,m,v)$, $z\in\{1,2,3\}$ | $1$ | $(0,z,m,v)$ |
| $(z,p,m,v)$, $z\in\{1,2,3\}$, $p\ne\varnothing$, $p+z\ne4$ | $1$ | $(0,\varnothing,m,v)$ |
| $(z,p,m,v)$, $p+z=4$, $m'<n_\alpha$ | $1$ | $(0,\varnothing,m',v')$ |
| $(z,p,m,v)$, $p+z=4$, $m'=n_\alpha$, $v'\ge b_{n_\alpha}$ | $1$ | $d_0$ |
| $(z,p,m,v)$, $p+z=4$, $m'=n_\alpha$, $v'<b_{n_\alpha}$ | $1$ | $d_1$ |
| $d_i$, $i=0,1$ | either bit | $d_i$ in analytical continuation |

The three accepting rows require $z\in\{1,2,3\}$ and $p\in\{1,2,3\}$. With that convention the rows are disjoint and exhaustive. A long gap keeps a pending category but is read through its actual closing one. The $z=0$ row defines the impossible consecutive-one case. Every completed retained pair clears the pending category, whether accepted or rejected. Accepted pairs are exactly $(1,3),(2,2),(3,1)$, and only $(2,2)$ supplies a one mark. All zero and pair counters are bounded in the displayed set.

**Proposition 9.3 (Credited fallback performance with full payment).** Conditional on Assumption 9.1 and the exact source premises, the supplied table has at most $S_\alpha$ complete configurations. For every $q\in(0,1)$ it has both errors at most $\alpha_0/2\le\alpha$, both almost-sure actual stops and both finite paid means. Write

$$
A_i^{\rm sh}(q)=\sum_{k=1}^3F_i(k)q^k,\qquad
\rho_i^{\rm sh}(q)=\frac{A_i^{\rm sh}(q)}{Z_i(q)},\qquad
\zeta_i(q)=\frac{C_iq^4}{(A_i^{\rm sh}(q))^2}.
\tag{9.5}
$$

Its exact supplied mean is

$$
\mathbb E_{i,q}T
=1+\beta_i(q)
+\frac{2n_\alpha\mu_i(q)Z_i(q)A_i^{\rm sh}(q)}{C_iq^4}.
\tag{9.6}
$$

Exposition of the supplied proof. The table has at most

$$
5\cdot4\sum_{m=0}^{n_\alpha-1}(m+1)+3
=10n_\alpha(n_\alpha+1)+3=S_\alpha
\tag{9.7}
$$

listed configurations, including waiting and both labels. Every table successor stays in the set or is a label; at an acceptance $v'\le m'$. The terminal label is selected on the terminal read itself. There is no separate gap, rejected-pair, elapsed-time or program-state counter.

At fixed $i,q$, each raw gap is short with probability $\rho_i^{\rm sh}>0$. Its retained category has law

$$
g_i(k)=\frac{F_i(k)q^k}{A_i^{\rm sh}(q)}\quad(k=1,2,3).
\tag{9.8}
$$

Let $W_r$ count raw gaps since the preceding retained gap, including retained gap $r$, and let $J_r$ be its category. Independence of raw gaps gives

$$
\mathsf P_i(W_r=n,J_r=k)
=(1-\rho_i^{\rm sh})^{n-1}f_{i,q}(k)
=(1-\rho_i^{\rm sh})^{n-1}\rho_i^{\rm sh}g_i(k).
\tag{9.9}
$$

The same product factorization holds for each finite list of successive blocks. Thus $(W_r)$ are iid geometric counts of mean $1/\rho_i^{\rm sh}$, independent of the entire iid category sequence $(J_r)$. This is an independence statement about numbers of gaps and retained categories, not paid durations.

Consecutive retained pairs are independent. Their probabilities for $(k,4-k)$ are $F_i(k)F_i(4-k)q^4/(A_i^{\rm sh})^2$, so their total acceptance probability is $\zeta_i>0$. Conditional on acceptance the $(2,2)$ probability is $\theta_i$, since the common factor $q^4$ cancels. More explicitly, the probability that the first accepted pair is pair $n$ and has mark $b\in\{0,1\}$ is

$$
(1-\zeta_i)^{n-1}\zeta_i\theta_i^b(1-\theta_i)^{1-b}
\quad(n\ge1).
$$

The same factorization applies to every finite sequence of successive acceptance blocks, by independence of the retained pairs. Summing out their geometric waiting counts proves that successive accepted marks are iid Bernoulli$(\theta_i)$. This proves the supplied conditional mark law without any dependence on the unknown nuisance parameter in that mark probability.

Let $V$ be the sum of the first $n_\alpha$ accepted marks and let $m_\theta=(\theta_0+\theta_1)/2$. Under source zero, wrong output means $V<b_{n_\alpha}$, hence $V\le b_{n_\alpha}-1<n_\alpha m_\theta$. Under source one, wrong output means $V\ge b_{n_\alpha}\ge n_\alpha m_\theta$. In either case $|V/n_\alpha-\theta_i|\ge\Delta_\theta/2$. For any variable $Y$ with finite variance, the pointwise bound $\mathbf1_{\{|Y-\mathbb EY|\ge r\}}\le(Y-\mathbb EY)^2/r^2$ gives the variance inequality. Apply it to $V/n_\alpha$ to get, for either error,

$$
\mathsf P_i(\text{wrong label})
\le\frac{4\theta_i(1-\theta_i)}{n_\alpha\Delta_\theta^2}
\le\frac{4V_\theta}{n_\alpha\Delta_\theta^2}
\le\frac{\alpha_0}{2}\le\alpha.
\tag{9.10}
$$

The ceiling in the threshold has therefore been accounted for on both sides. The calculation is valid at every interior parameter separately; these are also the supplied classifier's stronger separate full-family error bounds.

Let $R$ count retained pairs through the $n_\alpha$th acceptance. Independent pair acceptances give $\mathbb E_iR=n_\alpha/\zeta_i<\infty$: each successive acceptance takes a geometric count of mean $1/\zeta_i$, obtained by summing the geometric tail probabilities. Such a finite number of acceptances occurs almost surely. The raw gap count through termination is

$$
G=\sum_{r=1}^{2R}W_r.
\tag{9.11}
$$

The variable $R$ is determined by categories alone, independently of the whole sequence $(W_r)$. Tonelli applied to the nonnegative summands in (9.11) gives

$$
\mathbb E_iG
=\frac{2\mathbb E_iR}{\rho_i^{\rm sh}}
=\frac{2n_\alpha}{\rho_i^{\rm sh}\zeta_i}
=\frac{2n_\alpha Z_iA_i^{\rm sh}}{C_iq^4}<\infty.
\tag{9.12}
$$

Every raw gap begun by this table is fully read, including all discarded long gaps and rejected pairs. On its terminating paths,

$$
T=1+\tau+\sum_{r=1}^{G}(K_r+1).
\tag{9.13}
$$

The event $\{G\ge r\}$ is determined by preceding raw gaps; it is independent of the next $K_r$. The same nonnegative predictable-sum argument as (7.3)–(7.4) gives an expected post-first-tick cost $\mu_i\mathbb E_iG$, not a duration/acceptance-independence assertion. Equations (2.7) and (9.12) prove (9.6). Its terms are finite at each interior $q$, under both labels, and finite $G$, finite $\tau$ and finite individual gaps give almost-sure actual stopping. This reproduces the supplied fully paid argument. $\square$

For correspondence with the credited fixed-classifier benchmark, $C_0=301510$ and $A_0^{\rm sh}(1)=20196$ are supplied exact values; $A_1^{\rm sh}(1)=H(1)+H(2)+H(3)>0$. By (2.8) and (9.6), that same supplied classifier has

$$
\mathbb E_{i,e^{-s}}T\sim
\kappa_i s^{-11},\qquad
\kappa_i=\frac{20n_\alpha\,9!\,A_i^{\rm sh}(1)}{C_i}>0.
\tag{9.14}
$$

Indeed $A_i^{\rm sh}(e^{-s})\to A_i^{\rm sh}(1)$, $e^{-4s}\to1$, and the acquisition term in (9.6) has the displayed leading coefficient from $\mu_i\sim10/s$ and $Z_i\sim9!s^{-10}$. Its initial term is only $O_H(s^{-1})$. This fixed-classifier order and its sufficient budget are source-owned comparisons.

**Corollary 9.4 (Optional pre-observation choice for every interior $q$).** Conditional also on Assumption 9.1, a family satisfying (3.1) at every known $q\in(0,1)$ is obtained by choosing the table of Section 4 when $\Delta(q)>0$ and the supplied fallback table when $\Delta(q)\le0$. This family retains (8.1)–(8.2) throughout $0<s<s_*$.

Proof. The designer selects exactly one of the two immutable tables before observing any bit, using known $q$ and the public shapes. On the first branch, Theorems 6.2 and 7.1 prove the six obligations; on the second, Proposition 9.3 supplies them. There is no runtime branch-selection register, source-label advice or union of the two active configuration sets. The selected count is $4L+1$ or at most $S_\alpha$ respectively. By (8.5), the positive branch is always selected in the endpoint neighborhood. The fallback therefore affects neither endpoint bound. No uniform cubic mean bound outside that neighborhood or unchanged-table guarantee for the combined family follows. $\square$

## 10. Comparison with supplied necessary growth

**Supplied comparison 10.1 (Same-contract lower bound).** The lower companion's Theorems 9.1 and 10.1 apply to the same exact $H_c$, stationary history, known-common-$q$ source-blind design and complete configuration count. With $b=1-2\alpha>0$, its simultaneous bound includes

$$
\mathbb E_{i,e^{-s}}^{\mathcal A}T
\ge\frac{9!b^{11}}{8B^2\bigl(b+2\delta(M-2)\bigr)^{10}}s^{-11}
\quad\bigl(\mathcal A\in\mathfrak A_M(e^{-s},\alpha),\ i=0,1\bigr)
\tag{10.1}
$$

on a neighborhood independent of every finite $M\ge2$. This is a supplied lower theorem, not a lower-bound discovery of this volume. It includes both risks, both almost-sure stops and both finite means. In particular, if a compliant finite-budget family has, for one fixed target $i_\star$ and one fixed finite $C_T>0$,

$$
\mathbb E_{i_\star,e^{-s}}^{\mathcal A_s}T\le C_Ts^{-3}
\quad\text{eventually as }s\downarrow0,
\tag{10.2}
$$

then the supplied necessary growth conclusion is

$$
M(s)\ge2+\frac{A_Ts^{-4/5}-b}{2\delta},\qquad
A_T=\left(\frac{9!b^{11}}{8B^2C_T}\right)^{1/10}>0.
\tag{10.3}
$$

The eventual cubic constant must be independent of $s$, and the opponent must retain all its compliance obligations. This is stronger than mere pointwise finite means. Equations (10.1)–(10.3) are credited results of the supplied lower companion; no nested source or independent recalculation of its forest proof is needed by the upper construction.

**Corollary 10.2 (Nonmatching necessary and sufficient state orders).** At fixed $H_c$ and $0<\alpha<1/2$, the supplied necessary growth rate for an eventual cubic mean is $\Omega(s^{-4/5})$, while Theorem 8.1 realizes both cubic means with $O(s^{-1})$ complete configurations. These statements leave the optimal state-growth exponent unresolved.

Proof. The necessary assertion is (10.3): for sufficiently small $s$, $A_Ts^{-4/5}\ge2b$, so $M(s)-2\ge A_Ts^{-4/5}/(4\delta)$. The sufficient assertion uses the single source-blind table at each selected $q$, with constants

$$
C_M=\frac{16\ell}{c}+5,\qquad
C_{\rm up}=\frac{176\ell}{c^2}+\frac{44}{c}+7
\tag{10.4}
$$

from (8.1)–(8.2). Its two means obey the same fixed $C_{\rm up}$, so the supplied necessary theorem also applies to this family with $C_T=C_{\rm up}$ and either fixed target. The two powers differ, and neither implication supplies a construction of order $s^{-4/5}$ or a necessary lower bound of order $s^{-1}$. $\square$

The uniform companion's Theorem 7.2 already gives an observer-uniform eleventh-power lower order for every fixed complete budget. The new family has a budget depending on $s$, so it changes that quantifier. The geometric row coordinate and retuned probabilities do not by themselves alter that fixed-budget conclusion. The supplied fixed classifier of Section 9 remains a distinct attained fixed-budget benchmark. No new fixed-$M$ performance classification or minimum nonempty threshold is asserted here.

## 11. Distinct resource coordinates and applicability boundaries

The exact listed mutable state set on the new branch has size $4L+1$. It can be indexed using at most $\lceil\log_2(4L+1)\rceil$ mutable bits, hence $O_{H_c,\alpha}(1+\log(1/s))$ near the endpoint by (8.1). This is an encoding of the complete abstract configuration set. The immutable transition table, the exact values of $q,t$, their precision, and the work of calibrating or selecting a design are separate resources. The contract allows real transition probabilities of arbitrary immutable precision, and the theorem gives no finite-bit exact-coin realization or description-length bound. A mutable encoding by itself is not a physical-storage assertion.

At runtime the only operations affecting evidence are the displayed bit reads and state updates. A coin is used freshly at an actual read; its retained consequence is already represented by the flag or walk coordinate. Gap numbers, true lengths, the signed proof coordinate, potential infinite coin supplies and cost totals occur only on the analytical probability space. They are not channels, registers or free gap observations. Each actual run uses one uninterrupted stream, with the stationary first interval priced separately and every begun post-first-tick gap completed and paid.

The upper family uses one common design under the two selected labels at each known common $q$. It supplies no new parameter-free or separate-unknown-nuisance guarantee. The credited fallback is an already established fixed classifier, and the optional pre-observation choice does not change the new family's quantifiers. All state bounds are worst-case counts of possible persistent configurations, even on histories with arbitrarily long waits, long failed-survival suffixes or repeated holding. Finite expectation does not impose a deterministic horizon.

The central construction requires only the exact source, moment and geometric-separation premises; its endpoint theorem does not use the sum-four certificate or the lower-bound comparison. The optional extension additionally requires the supplied sum-four certificate. The lower companion is used only to state the necessary-growth comparison, not to prove the new risks, stopping or payment. No producer dimension, physical or neural memory model, empirical learning result, elapsed physical time, varying-$H$ uniformity or source-reset variant is a premise or conclusion. Removing either risk or either pointwise mean, changing the stationary start, or admitting an unpaid clock or stopping-time decoder would change the testing problem.

**Open question 11.1 (Closing the state-exponent gap).** A matching sufficient $O(s^{-4/5})$ budget, a stronger necessary state exponent, or another sharp tradeoff would require additional constructions or lower estimates under the unchanged six-obligation contract. The existing necessary and sufficient powers do not determine which possibility holds. Optimal constants, the minimum compliant budget and exact optimizers are likewise unresolved here.

## 12. Mathematical supplier map

| Supplier | Exact mathematical role and boundary |
| --- | --- |
| Continuation, Definitions 23.1–23.2 and equations (23.1)–(23.7) | The exact rational-center $H_c$, constants $\delta,B,a$, all-integer envelope, stationary first wait, iid subsequent zero counts and moment premises in Section 2. Nested source proofs remain credited premises. |
| Continuation, Proposition 27.2 and equations (27.2)–(27.4) | The coordinate $Z_i(q^2)/Z_i(q)$ and positive separation $cs+O_H(s^2)$ with $c=a/(9\cdot2^{10})$. Its changing-machine counterexample is not itself a classifier. |
| Uniform companion, Definition 3.1 | Known common $q$, source-blind retuning, common source-independent initialization, complete persistent configuration count, permitted immutable real probabilities and all six pointwise obligations. |
| Supplied finite geometric-mark/lazy-walk upper construction | The survival-flag realization and bounded midpoint accumulator. Sections 4–8 give the entire table, both exact errors, finite stopping before ruin formulas, exact gap and paid means, and the ceiling-aware constants for this construction. These are upper-side content relative to the credited source separation and lower theory. |
| Continuation, Lemmas 25.1–25.3 and Theorem 26.4; uniform companion, Section 6 | Discipline for actual renewal observations and predictable payment. Here stopping is at an actually read closing one, and (7.3)–(7.4) price that controller's completed gaps on its own history. |
| Continuation, Definition 26.1, Lemmas 26.2–26.3 and Theorem 26.4; uniform companion, Section 8 | The optional fixed classifier, exact sum-four certificate, conditional mark, finite threshold, complete count, both risks, both stops and fully paid means. Section 9 retains their source ownership. |
| Lower companion, Theorems 9.1 and 10.1 | The simultaneous finite-budget lower bound and necessary $\Omega(s^{-4/5})$ growth for a fixed eventual cubic constant under even one fixed target. The exact same complete-state and six-obligation contract is retained in Section 10. |
| Classical probability and finite-state methods | Independent geometric survival marking, midpoint lazy walks, gambler's ruin, bounded martingale convergence, finite conditional drift sums, geometric waiting counts, variance bounds, Tonelli and predictable inclusion. These methods are not claimed as inventions. |

The upper exposition is `repo-derived` in the sense of source-relative handwritten mathematics, incorporating the supplied upper construction. The continuation's attributions for stationary renewal conventions and finite-statistic stochastic updates remain secondary references; their external papers' scopes are not independently certified here. No external literature search or worldwide-priority claim accompanies this volume. Source-relative mathematical exposition, review of an exact manuscript, publication and formal verification are distinct acts.

## 追加锚（本行以下为增补区）
