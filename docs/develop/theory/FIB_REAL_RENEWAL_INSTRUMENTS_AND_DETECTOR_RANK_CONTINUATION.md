# Real renewal instruments and detector rank: finite observer memory

## 23. The exact source and the fixed observer experiment

**Definition 23.1 (The two fixed polynomial shapes).** Let $H=H_c$ be the rational-center polynomial from equation (19.7) of [Real renewal instruments and detector rank](FIB_REAL_RENEWAL_INSTRUMENTS_AND_DETECTOR_RANK.md). Explicitly, for a real argument $x$,

$$
\begin{aligned}
H(x)=x^9+\frac1{35\cdot10^{24}}\bigl(&55800726477138x-224986136658885x^2
+420664314485485x^3\\
&-540138133491075x^4+518234977000797x^5
-254383031435085x^6\\
&+77668004560980x^7+43377331415040x^8\bigr).
\end{aligned}
\tag{23.1}
$$

Set

$$
\begin{aligned}
F_0(x)&=x^9,&F_1(x)&=H(x),\\
\delta&=\frac{2749658638697}{10^{24}},&B&=1+\delta,&
a&=\frac{43377331415040}{35\cdot10^{24}}>0.
\end{aligned}
\tag{23.2}
$$

The polynomial is the one belonging to the rational center in Definition 12.1 of that source, rather than the limiting residual-zero coefficient vector. Theorem 15.5 there supplies, for every integer $k\ge1$,

$$
k^9\le F_i(k)\le Bk^9\quad(i=0,1),
\qquad
1\le\frac{H(k)}{k^9}\le1+\frac\delta k.
\tag{23.3}
$$

Both shapes are monic of degree nine. In particular $H(k)-k^9=ak^8+O(k^7)$. These exact shapes remain fixed in every assertion below.

**Definition 23.2 (Stationary history and its payment convention).** For $i\in\{0,1\}$ and $q\in(0,1)$ define

$$
\begin{aligned}
Z_i(q)&=\sum_{k\ge1}F_i(k)q^k,&
f_{i,q}(k)&=\frac{F_i(k)q^k}{Z_i(q)}\quad(k\ge1),&f_{i,q}(0)&=0,\\
S_{i,q}(b)&=\sum_{k\ge b}f_{i,q}(k)\quad(b\ge0),&
\mu_i(q)&=\sum_{k\ge1}(k+1)f_{i,q}(k),\\
\beta_i(q)&=\frac{\sum_{k\ge1}k(k+1)f_{i,q}(k)}{2\mu_i(q)}.
\end{aligned}
\tag{23.4}
$$

The sums defining $S_{i,q}$ use $f_{i,q}(0)=0$, so $S_{i,q}(0)=S_{i,q}(1)=1$. The source $\mathsf P_{i,q}$ is the stationary binary renewal law with $K$ zeros between consecutive ones and $K$ distributed as $f_{i,q}$. Its one-sided history $X_0,X_1,\ldots$ has the following exact description. First draw $\tau$ with

$$
\mathsf P_{i,q}(\tau=b)=\frac{S_{i,q}(b)}{\mu_i(q)}\quad(b\ge0),
\qquad \mathbb E_{i,q}\tau=\beta_i(q).
\tag{23.5}
$$

Place zeros at $0,\ldots,\tau-1$ and a one at $\tau$. Independently of $\tau$, draw iid $K_1,K_2,\ldots$ with law $f_{i,q}$ and put subsequent ones at

$$
\tau_n=\tau+\sum_{j=1}^n(K_j+1)\quad(n\ge1),\qquad \tau_0=\tau.
\tag{23.6}
$$

All other bits are zero. This is the equilibrium forward-wait convention of the owning source's Theorem 17.4 and Definition 20.1. The first wait is not distributed as $K$. The normalization in (23.5) is $\sum_{b\ge0}S_{i,q}(b)=\mu_i(q)$, and its mean is the triangular sum in (23.4). These identities are the classical finite-mean stationary renewal formulas; they also specify the observation law without referring to an unobserved initial age.

The source promise consists of the two full families $\{\mathsf P_{0,q}:0<q<1\}$ and $\{\mathsf P_{1,q'}:0<q'<1\}$. The parameters $q$ and $q'$ are separate nuisance parameters. A reading action returns the next bit of this single history, in order, and costs one. If an observer reads $X_0,\ldots,X_{T-1}$ and then stops, its paid cost is $T$; stopping before any read has cost zero. A source tick is a bit equal to one; an observed tick is one that has actually been read. Neither the parameters nor the variables in (23.4)–(23.6) are source responses.

For $s=-\log q\downarrow0$, the polynomial-geometric moment estimates of equations (18.13) and (20.29) in the owning source give

$$
Z_i(e^{-s})=9!s^{-10}(1+O_H(s)),\qquad
\mu_i(e^{-s})=\frac{10}{s}+O_H(1),\qquad
\beta_i(e^{-s})=\frac{11}{2s}+O_H(1).
\tag{23.7}
$$

Each moment in (23.4) is finite at every $q\in(0,1)$. The stationary sources here are the actual output laws identified in the owning source; their generating instruments have dimension $D=6$. That dimension is not an observer state count.

**Definition 23.3 (One fixed finite stochastic observer).** Fix $0<\alpha<1/2$. An observer $\mathcal A$ has a finite set of persistent configurations, including every register, control phase, retained random choice and decision label. Its initialization is independent of the source and has a fixed distribution. At each action it either reads the next actual bit or stops with an internally emitted label $D\in\{0,1\}$. Its state transitions and choices use only the current configuration, the bit just read when applicable, and fresh random variables independent of the source and of earlier fresh random variables. Their probabilities are fixed real numbers. The initialization, state set and transition probabilities may depend on $H$, the prescribed risk and arbitrary fixed design constants; the same machine is used throughout $q\in(0,1)$. They do not depend on the true parameter or on the number of preceding actions except insofar as information about the latter is represented in the finite configuration. Choosing a new machine as an endpoint band shrinks is a different quantifier order.

No externally available time, age, program counter, archive, reset, parallel source copy, skipped bit, parameter query or probability query is part of this experiment. In particular an external recipient does not infer the decision from the elapsed number of reads: $D$ is the label emitted by the observer itself. A mathematical cost tally $T$ supplies no input to it. A stored seed or a counter used to select random updates is persistent information and belongs in the state set; a fresh independent coin is not a persistent register.

The correctness and termination contract is

$$
\begin{gathered}
\sup_{0<q<1}\mathsf P_{0,q}(D=1)\le\alpha,
\qquad
\sup_{0<q'<1}\mathsf P_{1,q'}(D=0)\le\alpha,\\
\mathsf P_{i,q}(T<\infty)=1,
\qquad \mathbb E_{i,q}T<\infty
\quad(i=0,1, 0<q<1).
\end{gathered}
\tag{23.8}
$$

The last two assertions are pointwise in the true parameter. A deterministic horizon and a mean bound uniform on $(0,1)$ are not hypotheses.

**Lemma 23.4 (Read-ready stochastic normal form with internal labels).** Every observer of Definition 23.3 can be represented on a finite state set $\mathcal S$ by a fixed row distribution $\eta$ and two fixed row-stochastic matrices $A,C$, for reading zero and one respectively. There are two absorbing states $d_0,d_1$, both fixed by both matrices, that carry the decisions. Every other state is ready to make its next paid read. If the state is initially absorbing, the observer stops without reading; otherwise it reads until the first transition into a decision state. This representation preserves the joint law of $(T,D)$ for every source parameter.

Proof. At initialization, combine the initial random choice and the state-based choice to stop or undertake the first read. Put the stop probabilities on their actual labels and the remaining probabilities on the configurations committed to a read. Following a read, combine the bit-dependent state update with the subsequent state-based choice to stop or read again. These compositions are fixed stochastic kernels because all their inputs except the bit are contained in the finite configuration or are fresh independent random choices. A finite control phase needed to describe this composition remains part of the configuration.

Identify terminal configurations with the same emitted label and retain the two labels as distinct states. On these two states define both bit matrices to be the identity. The resulting action sequence before absorption and its final label agree with the original observer. An active-state substochastic description is thereby augmented with the labelled destinations of its lost mass; it is not interpreted as unlabelled killing. Sampling an unused future bit after absorption, while holding the decision state fixed, changes neither $T$ nor $D$ and will only be used to define analytical kernels.

This reduction does not replace stochastic transitions by a deterministic controller with an uncounted random tape. The matrices are the marginal transition probabilities of the allowed independent random choices. Nor does finiteness imply a bound on zero runs before stopping: a stochastic self-loop can survive every finite number of zeros with positive probability. $\square$

## 24. The two renewal kernels of a fixed finite observer

**Lemma 24.2 (Completed gaps and the first stationary interval).** For the fixed observer write

$$
\begin{aligned}
U_i(q)&=\sum_{k\ge1}f_{i,q}(k)A^kC,\\
R_i(q)&=\frac1{\mu_i(q)}\sum_{b\ge0}S_{i,q}(b)A^bC,
\qquad \nu_i(q)=\eta R_i(q).
\end{aligned}
\tag{24.5}
$$

These are stochastic matrices and initial distributions respectively. Define total variation of finite probability rows by $\|u-v\|_{\rm TV}=\tfrac12\sum_x|u(x)-v(x)|$, and put

$$
\varepsilon(q)=\max_{x\in\mathcal S}
\|U_0(q)(x,\cdot)-U_1(q)(x,\cdot)\|_{\rm TV},
\qquad
r(q)=\|\nu_0(q)-\nu_1(q)\|_{\rm TV}.
\tag{24.6}
$$

There are constants $C_U>0$, $C_R\ge0$ and $s_*>0$, depending on this fixed observer and $H$, such that

$$
\varepsilon(e^{-s})\le C_Us^{10},\qquad
r(e^{-s})\le C_Rs^2
\quad(0<s<s_*).
\tag{24.7}
$$

Proof. The weights in each line of (24.5) are nonnegative and sum to one. Thus these averages are stochastic, including their absorbing rows. They describe following the word $0^k1$ after an observed tick, or $0^b1$ from the stationary starting time, while fixing any already emitted label.

We use the following classical finite stochastic-matrix spectral and geometric-series facts as proof suppliers. Let $A$ be the zero-transition matrix from Lemma 23.4. Let $P$ be its spectral projection at eigenvalue one and $Q=I-P$. Define

$$
B_0=A-P,
\qquad L=(I-A+P)^{-1}Q.
\tag{24.1}
$$

These matrices exist, are real, and satisfy

$$
AP=PA=P,\qquad PL=LP=0,\qquad (I-A)L=L(I-A)=Q.
\tag{24.2}
$$

For every integer $k\ge0$,

$$
A^k=P+B_0^kQ,
\qquad
\sum_{b=0}^k A^b=(k+1)P+(I-A^{k+1})L.
\tag{24.3}
$$

The matrix function

$$
G(q)=qB_0(I-qB_0)^{-1}Q
\tag{24.4}
$$

is analytic in a neighborhood of $q=1$. For $0<q<1$ it equals $\sum_{k\ge1}q^k A^kQ$.

Indeed, nonnegativity and unit row sums give $\|A^n\|_\infty=1$ for every $n\ge0$. Thus all eigenvalues have modulus at most one. A nontrivial Jordan block at an eigenvalue of modulus one would have powers with a nonzero polynomially growing entry in Jordan coordinates, contradicting boundedness in finite dimension. Every peripheral eigenvalue is therefore semisimple, including eigenvalue one.

The spectral decomposition into the eigenspace at one and its invariant complement gives $AP=PA=P$ and $PQ=0$. The projection is real since the matrix and the isolated eigenvalue one are real. On $\operatorname{ran}P$, $I-A+P$ is the identity; on $\operatorname{ran}Q$ it is $I-A$, which is invertible. This proves (24.1)–(24.2). The first identity in (24.3) holds also for $k=0$ because $I=P+Q$. Summing on the two invariant spaces and multiplying the finite geometric sum by $I-A$ on $\operatorname{ran}Q$ proves the second.

The eigenvalues of $B_0$ are zero on $\operatorname{ran}P$ and the remaining eigenvalues of $A$ on $\operatorname{ran}Q$. None is one. Consequently $\det(I-qB_0)\ne0$ on some neighborhood of $q=1$, proving analyticity of the inverse and of $G$. For $q<1$ the absolutely convergent geometric series for the inverse gives the stated series.

This argument allows multiple closed classes and multiple copies of eigenvalue one. A periodic class may give an eigenvalue such as $-1$; its possible resolvent pole is away from $q=1$. Jordan blocks strictly inside the unit disk are allowed and their poles are likewise away from that point. No convergence of $A^k$ to $P$, aperiodicity, irreducibility or diagonalizability of the whole matrix has been used.

Let $\mathcal D=q\,d/dq$ and use the fixed scalar polynomial $F_i$ to define the matrix function

$$
V_i(q)=F_i(\mathcal D)G(q),\qquad W_i(q)=\frac{V_i(q)}{Z_i(q)}.
\tag{24.8}
$$

Analyticity of (24.4) implies that $V_i$ is analytic at one. For $0<q<1$, polynomial factors in $k$ preserve absolute local convergence, so differentiating the series for $G$ gives

$$
\begin{aligned}
V_i(q)&=\sum_{k\ge1}F_i(k)q^kA^kQ,\\
\sum_{k\ge1}f_{i,q}(k)A^k&=P+W_i(q),\qquad
U_i(q)=(P+W_i(q))C.
\end{aligned}
\tag{24.9}
$$

In a fixed finite-dimensional norm, $V_i$ is bounded near one and (23.7) gives $W_i(e^{-s})=O_{\mathcal A,H}(s^{10})$. The contribution $PC$ cancels exactly between the two normalized completed-gap kernels. Norm equivalence on the fixed state space proves the first bound in (24.7). In particular the bound accounts for absorption during zeros as well as at the closing tick.

For the initial kernel, summing first over $b\le K$ and using (24.3) gives the exact identity

$$
\begin{aligned}
R_i(q)
&=\frac1{\mu_i(q)}\mathbb E_{i,q}
   \left[\sum_{b=0}^K A^b\right]C\\
&=\left[P+\frac1{\mu_i(q)}\bigl(L-AW_i(q)L\bigr)\right]C.
\end{aligned}
\tag{24.10}
$$

Indeed $\mathbb E A^{K+1}=A(P+W_i)=P+AW_i$ and $PL=0$. Formula (23.7) yields

$$
\mu_i(e^{-s})^{-1}=\frac{s}{10}+O_H(s^2),\qquad
R_i(e^{-s})=PC+\mu_i(e^{-s})^{-1}LC+O_{\mathcal A,H}(s^{11}).
\tag{24.11}
$$

The leading $PC$ and $(s/10)LC$ terms are the same for the two families. Hence $R_0-R_1=O_{\mathcal A,H}(s^2)$. Their common, parameter-independent initial row $\eta$ proves the second bound in (24.7).

The first interval therefore has its own $O(s^2)$ estimate, not the $O(s^{10})$ completed-gap estimate. A stop before its first tick is encoded by its actual absorbing label inside $R_i$. The source continuation used to define that matrix supplies no additional decision data and incurs no declared payment. $\square$

## 25. Unbounded stopping and the lower bound for actual reads

**Lemma 25.1 (An analytical renewal chain and actually observed ticks).** Couple the normalized observer to the one-sided source of Definition 23.2, keeping its state fixed after its actual absorption. Let $Y_n$ be its resulting state just after the tick at $\tau_n$, and set

$$
N=\inf\{n\ge0:Y_n\in\{d_0,d_1\}\},\qquad
Q_T=\sum_{t\ge0}\mathbf1_{\{T>t\}}X_t.
\tag{25.1}
$$

Under $\mathsf P_{i,q}$, $Y_0$ has law $\nu_i(q)$ and $Y_n$ has transition matrix $U_i(q)$. If the observer terminates, $Y_N=d_D$ and

$$
N\le Q_T\le T.
\tag{25.2}
$$

Proof. Independence of the future complete gaps in (23.6), and the fixed fresh transition randomness, give exactly the kernels (24.5). If the observer stops before or at the first tick, $Y_0$ is already its decision and $N=0$. Otherwise, every live state $Y_n$, $n<N$, occurs immediately after an actually read tick and commits to a further read. These are $N$ distinct ticks paid before stopping. This proves the first inequality. The second holds since each counted tick is one of the $T$ actual reads.

If stopping occurs during the zeros after the last such live tick, the state at the next source tick is merely the frozen label. That next tick need not have been read and is not added to $Q_T$. Thus $N$ counts live tick boundaries, equivalently the ensuing epochs whose first read is undertaken, rather than fictitious completed paid gaps. Since all $K_j$ and $\tau$ are finite almost surely, actual termination gives a finite $N$ with the asserted terminal label. $\square$

**Lemma 25.2 (Decision separation at an unbounded stop).** Assume the termination and finite-mean conditions in (23.8) for the fixed parameter $q$, and let

$$
p_i(q)=\mathsf P_{i,q}(D=1).
$$

For each $i\in\{0,1\}$,

$$
|p_1(q)-p_0(q)|\le r(q)+\varepsilon(q)\mathbb E_{i,q}N.
\tag{25.3}
$$

Proof. For $j\in\{0,1\}$ define $h_j(x)$ to be the probability that the chain with kernel $U_j(q)$ started at $x$ eventually reaches $d_1$. This definition makes sense even at a state from which absorption has probability less than one. It gives

$$
0\le h_j\le1,\qquad U_j(q)h_j=h_j,
\qquad h_j(d_0)=0,\quad h_j(d_1)=1.
\tag{25.4}
$$

Fix $i$ and take $j=1-i$. Conditional expectation of the finitely many stopped increments gives, for every integer $m\ge1$,

$$
\mathbb E_{i,q}h_j(Y_{N\wedge m})-\nu_i(q)h_j
=\mathbb E_{i,q}\sum_{n=0}^{(N\wedge m)-1}
  \bigl[(U_i(q)-U_j(q))h_j\bigr](Y_n).
\tag{25.5}
$$

For a function valued in $[0,1]$, the difference between its averages under two probability rows is at most their total variation. Each summand in (25.5) therefore has absolute value at most $\varepsilon(q)$. Lemma 25.1 and the assumed finite mean give $\mathbb E_{i,q}N<\infty$. Bounded convergence on the left and domination by $\varepsilon(q)N$ on the right allow $m\to\infty$. Since $h_j(Y_N)=D$,

$$
|p_i(q)-\nu_i(q)h_j|\le\varepsilon(q)\mathbb E_{i,q}N.
\tag{25.6}
$$

Starting the $j$ chain with its actual initial law gives $p_j(q)=\nu_j(q)h_j$. The initial-row difference is at most $r(q)$, proving (25.3). Interchanging $i$ and $j$ gives the bound with the expectation under the other family. No assumption about termination from every abstract state was required, and no deterministic truncation remains in (25.3). $\square$

**Lemma 25.3 (A predictable tick bound prices actual reads).** Under either source and at every $q\in(0,1)$, the conditional probability that the next bit is one, given any positive-probability observed finite bit history, is at most $B(1-q)$. The same bound holds when independent observer randomness is included. Consequently every legal stopping rule, including one with an unbounded state space, satisfies the extended nonnegative expectation inequality

$$
\mathbb E_{i,q}Q_T\le B(1-q)\mathbb E_{i,q}T.
\tag{25.7}
$$

Proof. First suppose an actual tick has been observed and exactly $b$ zeros have followed it. At $b=0$ the next bit is forced to be zero, since $K\ge1$. For $b\ge1$, the next-tick probability is

$$
\frac{f_{i,q}(b)}{S_{i,q}(b)}
=\frac{F_i(b)q^b}{\sum_{k\ge b}F_i(k)q^k}
\le\frac{Bb^9q^b}{\sum_{k\ge b}b^9q^k}
=B(1-q).
\tag{25.8}
$$

All earlier complete intervals are independent of the current gap, so this conditional probability applies to the whole preceding observed history.

Before any tick has been observed, a history of $b$ zeros says exactly $\tau\ge b$. Its next-tick probability is

$$
\frac{S_{i,q}(b)}{\sum_{v\ge b}S_{i,q}(v)}.
\tag{25.9}
$$

For integers $k\ge1$ and $j\ge0$, (23.3) implies

$$
F_i(k+j)\ge(k+j)^9\ge k^9\ge B^{-1}F_i(k).
$$

Shifting each term of the tail sum by $j$ proves, also when $b=0$,

$$
S_{i,q}(b+j)\ge B^{-1}q^j S_{i,q}(b).
\tag{25.10}
$$

For $b=0$ the shifted terms start at $j+1$ and form a subset of the tail defining $S_{i,q}(j)$, which is sufficient for the inequality. Summing (25.10) over $j\ge0$ bounds (25.9) by $B(1-q)$. Thus the first stationary interval has the same hazard bound without being replaced by a complete gap.

For the payment identity, expose an independent supply of all the observer's fresh coins on the analytical probability space. Independence leaves the source's conditional next-bit probabilities unchanged. Let $\mathcal F_t$ contain these coins and $X_0,\ldots,X_{t-1}$. The event $\{T>t\}$, meaning that read $t+1$ is undertaken, belongs to $\mathcal F_t$. Tonelli and the conditional bound give

$$
\begin{aligned}
\mathbb E_{i,q}Q_T
&=\sum_{t\ge0}\mathbb E_{i,q}
  \left[\mathbf1_{\{T>t\}}\mathbb E_{i,q}(X_t\mid\mathcal F_t)\right]\\
&\le B(1-q)\sum_{t\ge0}\mathsf P_{i,q}(T>t)
=B(1-q)\mathbb E_{i,q}T.
\end{aligned}
\tag{25.11}
$$

The extra exposure of coins is for the proof of predictability and provides no memory to the controller. The summands refer to precisely those reads that occur, including the terminal actual read. They omit every unread suffix. $\square$

**Theorem 25.4 (The fixed finite-state paid-mean converse).** Fix the exact sources of Definitions 23.1–23.2 and $0<\alpha<1/2$. For every one fixed finite-state stochastic observer $\mathcal A$ satisfying Definition 23.3 and all of (23.8), there exist $c_{\mathcal A}>0$ and $s_{\mathcal A}>0$ such that

$$
\mathbb E_{i,e^{-s}}T\ge c_{\mathcal A}s^{-11}
\quad\text{for both }i=0,1\text{ and every }0<s<s_{\mathcal A}.
\tag{25.12}
$$

The constants and the neighborhood may depend on the entire fixed machine, including its transition probabilities and initialization, as well as on $H$ and $\alpha$.

Proof. Let $b_\alpha=1-2\alpha>0$. The two separate uniform risk bounds permit the particular comparison of $\mathsf P_{0,q}$ with $\mathsf P_{1,q}$, and give $p_1(q)-p_0(q)\ge b_\alpha$. This selected pair is allowed within the two nuisance families; the experiment does not promise that their unknown parameters are equal.

Apply Lemmas 25.1–25.3 and (24.7), separately with $i=0$ and $i=1$. Since $1-e^{-s}\le s$,

$$
\begin{aligned}
b_\alpha
&\le r(e^{-s})+\varepsilon(e^{-s})\mathbb E_{i,e^{-s}}N\\
&\le C_Rs^2+BC_Us^{10}(1-e^{-s})\mathbb E_{i,e^{-s}}T\\
&\le C_Rs^2+BC_Us^{11}\mathbb E_{i,e^{-s}}T.
\end{aligned}
\tag{25.13}
$$

Choose $s_{\mathcal A}\le s_*$ small enough that $C_Rs^2\le b_\alpha/2$ throughout that interval, and take

$$
c_{\mathcal A}=\frac{b_\alpha}{2BC_U}>0.
\tag{25.14}
$$

This proves (25.12) under each family. A positive $C_U$ can always be chosen as an upper-bound constant; no division by the actual value of $\varepsilon(q)$ is involved.

The initial interval enters through its exact kernel, and its actual reads remain in $T$. A terminal gap interrupted by stopping contributes only its observed prefix to (25.11). Thus no full expected gap length has been charged to an interrupted gap. The only truncations in the argument were the finite sums in (25.5), whose limits were justified using the pointwise finite mean. $\square$

## 26. A deterministic finite observer attaining the eleventh-power mean

**Definition 26.1 (Fixed marks and retention of short gaps).** Define the fixed rational constants

$$
\begin{aligned}
C_i&=F_i(2)^2+2F_i(1)F_i(3),&
\theta_i&=\frac{F_i(2)^2}{C_i},\\
\Delta_\theta&=\theta_0-\theta_1,&
V&=\max_{i=0,1}\theta_i(1-\theta_i).
\end{aligned}
\tag{26.1}
$$

The exact sum-four certificate in Theorem 20.2 of the owning source states $0<\theta_1<\theta_0<1$. Equivalently, writing $r_k=H(k)/k^9$, it supplies

$$
r_1r_3-r_2^2
=\frac{520040714516414119558257878908551006355871}
       {331776\cdot10^{48}}>0.
\tag{26.2}
$$

In particular $\Delta_\theta>0$ and $V>0$; also $C_0=301510$. This finite certificate and the resulting conditional Bernoulli statistic are used as established source results.

For the prescribed $0<\alpha<1/2$, choose once a rational $0<\alpha_0\le\alpha$ and set

$$
M=\left\lceil\frac{8V}{\alpha_0\Delta_\theta^2}\right\rceil,
\qquad
b_M=\left\lceil\frac{M(\theta_0+\theta_1)}2\right\rceil.
\tag{26.3}
$$

These are fixed finite integers determined by the shapes and the chosen risk, independent of the unknown parameter. When $\alpha$ is rational one can take $\alpha_0=\alpha$.

The observer first reads to the first actual tick. Thereafter it reads every subsequent gap through its closing tick and retains a category only for a completed gap of length $1$, $2$ or $3$. It pairs consecutive retained categories, leaving no retained category unused between pairs. A retained first category is preserved through any number of intervening gaps of length at least four. A retained pair is accepted exactly when its two categories sum to four. Its mark is one for $(2,2)$ and zero for $(1,3)$ or $(3,1)$. All other retained pairs are rejected. After each pair, accepted or rejected, the pending category is cleared.

At the closing tick that supplies the $M$th accepted pair, let $v$ be the accumulated number of marks equal to one. The observer stops there, emitting zero if $v\ge b_M$ and one otherwise. The operational meaning of a gap category is a saturated zero count updated on actual consecutive reads; it is not a response supplying a gap length. Long gaps are read in their entirety even when their category is already known to be ineligible.

**Lemma 26.2 (A complete finite-state realization).** The observer in Definition 26.1 is a single deterministic machine independent of $q$. It has a realization with at most

$$
10M(M+1)+3
\tag{26.4}
$$

states, including its first-tick waiting state and both decision states. No elapsed-read counter, unbounded gap counter, rejected-pair counter or retained history is needed.

Proof. Use one waiting state $w$, two absorbing states $d_0,d_1$, and active states

$$
(z,p,m,v),\qquad
z\in\{0,1,2,3,4\},\quad
p\in\{\varnothing,1,2,3\},\quad
0\le m<M,\quad 0\le v\le m.
\tag{26.5}
$$

Here $z$ counts zeros since the last tick, saturated at four; $p$ is the pending retained category; $m$ is the number of accepted pairs; and $v$ counts their one marks. Every nonabsorbing state orders a next-bit read. The waiting state loops on zero and moves on one to $(0,\varnothing,0,0)$.

In an active state, zero replaces $z$ by $\min(z+1,4)$ and leaves the other coordinates fixed. On one, the following cases define the new state, with the current zero count reset to zero in every nonterminal case:

1. If $z=4$, retain $p,m,v$ without change.
2. If $z\in\{1,2,3\}$ and $p=\varnothing$, set $p=z$ and retain $m,v$.
3. If $z\in\{1,2,3\}$ and $p\ne\varnothing$, form the retained pair $(p,z)$. When $p+z\ne4$, clear $p$ and retain $m,v$. When $p+z=4$, set $m'=m+1$ and $v'=v+\mathbf1_{\{p=z=2\}}$. If $m'<M$, move to $(0,\varnothing,m',v')$. If $m'=M$, move directly to $d_0$ for $v'\ge b_M$ and to $d_1$ otherwise.
4. If $z=0$, leave $p,m,v$ unchanged and set $z=0$; this defines the transition on the impossible successive-tick input as well.

Both decision states absorb on both bits. Every intermediate category and decision in these rules is determined by the old state and the bit. Thus the rules are a finite transition table, not an arithmetic process with an additional uncounted program state. In particular the terminal label is selected on the terminal paid read itself. The two thresholds in (26.3) are compiled into this fixed table; there are no mutable parameter-description registers outside (26.5).

The number of listed active states is at most

$$
5\cdot4\sum_{m=0}^{M-1}(m+1)=10M(M+1).
\tag{26.6}
$$

Some of them are unreachable, which only improves this upper bound. Adding $w,d_0,d_1$ proves (26.4). Encoding this state set uses at most $\lceil\log_2(10M(M+1)+3)\rceil$ mutable state bits. The fixed transition-table description is a separate fixed finite description; this construction makes no claim that its description is free, short or optimal. $\square$

**Lemma 26.3 (Paid thinning preserves the conditional mark).** For analysis at a fixed $i,q$, let

$$
\begin{aligned}
A_i^{\rm sh}(q)&=\sum_{k=1}^3F_i(k)q^k,&
\rho_i(q)&=\frac{A_i^{\rm sh}(q)}{Z_i(q)},\\
g_{i,q}(k)&=\frac{F_i(k)q^k}{A_i^{\rm sh}(q)}\quad(k=1,2,3),&
\zeta_i(q)&=\frac{C_iq^4}{A_i^{\rm sh}(q)^2}.
\end{aligned}
\tag{26.7}
$$

After the first actual tick, the retained categories are iid with law $g_{i,q}$. Successive retained pairs are iid; each is accepted with probability $\zeta_i(q)>0$, and its conditional one-mark probability is $\theta_i$, independent of $q$. The successive accepted marks are iid Bernoulli variables with that mean. The observer of Definition 26.1 consequently satisfies

$$
\sup_{0<q<1}\mathsf P_{0,q}(D=1)\le\alpha_0/2\le\alpha,
\qquad
\sup_{0<q'<1}\mathsf P_{1,q'}(D=0)\le\alpha_0/2\le\alpha.
\tag{26.8}
$$

Proof. Each raw gap independently belongs to $\{1,2,3\}$ with probability $\rho_i(q)>0$. Let $W_r$ be the number of raw gaps since the preceding retained gap, including retained gap $r$, and let $J_r\in\{1,2,3\}$ be its category. For the first block, and identically for each subsequent independent block,

$$
\begin{aligned}
\mathsf P_{i,q}(W_r=n,J_r=k)
&=(1-\rho_i(q))^{n-1}f_{i,q}(k)\\
&=(1-\rho_i(q))^{n-1}\rho_i(q)g_{i,q}(k)
\quad(n\ge1, k\in\{1,2,3\}).
\end{aligned}
\tag{26.9}
$$

Independence of the raw gaps factors the joint probabilities for any finite sequence of these blocks. Hence the $W_r$ are iid geometric variables of mean $1/\rho_i(q)$ and are independent of the entire iid category sequence $(J_r)$. This statement concerns only the number of gaps per block, not their paid durations; those durations need not be independent of categories.

For a retained pair, each ordered composition $(k,4-k)$ has probability

$$
g_{i,q}(k)g_{i,q}(4-k)
=\frac{F_i(k)F_i(4-k)q^4}{A_i^{\rm sh}(q)^2}
\quad(k=1,2,3).
\tag{26.10}
$$

Their sum is $\zeta_i(q)$, and conditioning on acceptance gives exactly the conditional distribution in Theorem 20.2 of the owning source. Disjoint retained pairs are independent, so accepting successive pairs gives the same iid Bernoulli marks as that theorem and the confidence construction of Theorem 20.3. In particular the midpoint threshold and variance estimate there apply with the risk input $\alpha_0$: each wrong-decision probability is at most

$$
\frac{4V}{M\Delta_\theta^2}\le\frac{\alpha_0}{2}.
\tag{26.11}
$$

The threshold is the integer ceiling in (26.3), just as in that construction. Since the conditional mark law does not involve the actual nuisance value, the two suprema in (26.8) are separate full-family bounds. Retention alters how these marks are acquired; it does not alter the supplied shape certificate or the confidence calculation. $\square$

**Theorem 26.4 (Exact actual mean, finite termination and positive leading constants).** The deterministic observer of Definition 26.1 terminates almost surely and has finite mean paid cost at every $q\in(0,1)$ in either family. Its exact mean is

$$
\mathbb E_{i,q}T
=1+\beta_i(q)
+\frac{2M\mu_i(q)Z_i(q)A_i^{\rm sh}(q)}{C_iq^4}.
\tag{26.12}
$$

It satisfies all of (23.8), with the state bound (26.4), and for both $i=0,1$,

$$
\mathbb E_{i,e^{-s}}T\sim\kappa_i s^{-11},
\qquad
\kappa_i=\frac{20M\,9!\,A_i^{\rm sh}(1)}{C_i}>0.
\tag{26.13}
$$

Here $A_0^{\rm sh}(1)=20196$, while $A_1^{\rm sh}(1)=H(1)+H(2)+H(3)$ is the exact positive rational value specified by (23.1). Thus (26.13) gives an explicit positive leading constant for each family.

Proof. At a fixed $i,q$, both retention and retained-pair acceptance have positive probabilities. Consequently every finite number of retained categories and accepted pairs is acquired almost surely. More quantitatively, let $J_M^*$ be the number of retained pairs through the $M$th acceptance. The independent acceptance indicators give

$$
\mathbb E_{i,q}J_M^*=\frac{M}{\zeta_i(q)}<\infty.
\tag{26.14}
$$

This follows by summing the means $1/\zeta_i(q)$ of the $M$ successive geometric waiting counts for accepted pairs. Let $G_M$ be the number of raw post-first-tick gaps actually read through termination. In terms of the blocks of (26.9),

$$
G_M=\sum_{r=1}^{2J_M^*}W_r.
\tag{26.15}
$$

The integer $J_M^*$ is determined by the retained categories alone. Their independence from the whole sequence of waiting counts in Lemma 26.3 and Tonelli yield

$$
\mathbb E_{i,q}G_M
=\frac{2M}{\rho_i(q)\zeta_i(q)}
=\frac{2MZ_i(q)A_i^{\rm sh}(q)}{C_iq^4}<\infty.
\tag{26.16}
$$

Every one of these raw gaps is actually completed. On each path the paid cost is therefore exactly

$$
T=1+\tau+\sum_{n=1}^{G_M}(K_n+1).
\tag{26.17}
$$

This includes all rejected short pairs, all intervening long gaps, the initial stationary zeros and their first tick, and the final closing tick. For each $n\ge1$, the event $\{G_M\ge n\}$ is determined by the preceding raw gaps: it says that the observer has not yet completed its $M$th acceptance. It is independent of the next iid gap $K_n$. Thus

$$
\begin{aligned}
\mathbb E_{i,q}\sum_{n=1}^{G_M}(K_n+1)
&=\sum_{n\ge1}\mathbb E_{i,q}
       [(K_n+1)\mathbf1_{\{G_M\ge n\}}]\\
&=\mu_i(q)\sum_{n\ge1}\mathsf P_{i,q}(G_M\ge n)
=\mu_i(q)\mathbb E_{i,q}G_M.
\end{aligned}
\tag{26.18}
$$

No independence between a gap's length and the acceptance decision made after that gap is asserted. Predictable inclusion, rather than such an independence claim, is the reason for (26.18).

The initial wait is almost surely finite and has mean $\beta_i(q)$. Equations (26.16)–(26.18) prove (26.12), its finiteness, and almost-sure actual termination. Correctness is (26.8), and the fixed deterministic finite realization is Lemma 26.2.

Finally $A_i^{\rm sh}(e^{-s})\to A_i^{\rm sh}(1)>0$, $e^{-4s}\to1$, and (23.7) applies to the other factors in (26.12). The initial term is $O_H(s^{-1})$, whereas the acquisition term has asymptotic value

$$
\frac{2M\,(10/s)\,(9!s^{-10})\,A_i^{\rm sh}(1)}{C_i}
=\kappa_i s^{-11}.
\tag{26.19}
$$

All factors in $\kappa_i$ are strictly positive, proving (26.13). $\square$

## 27. The scope of the fixed-machine order and its suppliers

**Corollary 27.1 (Attained fixed-machine order and the growing-counter comparison).** For the exact sources and any fixed $0<\alpha<1/2$, every observer in Definition 23.3 satisfying (23.8) pays $\Omega_{\mathcal A,H,\alpha}(s^{-11})$ in each family, and one fixed deterministic observer pays $\Theta_{H,\alpha_0}(s^{-11})$ in each. In particular no one fixed finite-state stochastic observer in this experiment can have an $O(s^{-3})$ paid mean near one, even under just one of the two families while retaining the full contract.

Theorem 22.3 of the owning source supplies a deterministic parameter-free observer on the same stationary families with the same consecutive paid-read actions, separate uniform family errors and pointwise finite means, whose achieved mean is $\Theta_{H,\alpha}(s^{-3})$ under both families. Its unbounded gap and pair counters and its growing dyadic precision, described in Proposition 22.6 there, place it outside Definition 23.3. Hence these two achieved orders give a separation between one fixed finite controller and that growing-memory procedure for this exact testing experiment.

Proof. The lower assertion is Theorem 25.4 and the matching finite-state upper assertion is Theorem 26.4. If such a fixed finite controller had $\mathbb E_{i,e^{-s}}T\le Cs^{-3}$ for either fixed $i$ throughout a sufficiently small neighborhood, (25.12) would force $c_{\mathcal A}\le Cs^8$ there, a contradiction as $s\downarrow0$. The cited source theorem provides the other procedure and its actual-read order. Proposition 22.6 specifies persistent control of $O(D_L)$ bits and temporary exact-arithmetic workspace of $O(D_L^2)$ bits after $L$ reads, where, for fixed model and risk descriptions,

$$
D_L=O_{H,\alpha}(1+\log(L+2)).
\tag{27.1}
$$

These are growing bounds over possible histories, not a fixed finite set of configurations. Its arbitrary possible gap lengths and counters cannot be treated as finitely many states merely because there are finitely many named integer registers. $\square$

**Proposition 27.2 (Why the machine cannot vary with the endpoint).** Let $r\in(0,1)$ index a three-state observer with an active state $u$ and absorbing labels $d_0,d_1$. From $u$, a zero preserves $u$ with probability $r$ and otherwise leads to $d_0$; a one leads to $d_1$. This specifies one fixed stochastic machine for each fixed $r$. The analytical completed-gap kernel has the row entry

$$
U_i(q)(u,d_1)=\sum_{k\ge1}f_{i,q}(k)r^k
=\frac{Z_i(qr)}{Z_i(q)}.
\tag{27.2}
$$

For any fixed $r<1$, Lemma 24.2 applies. It does not give an $O(s^{10})$ difference uniform in $r$ as $r\uparrow1$. In fact along the changing-machine diagonal $r=q=e^{-s}$,

$$
\frac{Z_1(e^{-2s})}{Z_1(e^{-s})}
-\frac{Z_0(e^{-2s})}{Z_0(e^{-s})}
=\frac{a}{9\cdot2^{10}}s+O_H(s^2).
\tag{27.3}
$$

Proof. The coefficient $a$ in (23.2) and the polynomial power sums imply

$$
\frac{Z_1(e^{-s})}{Z_0(e^{-s})}
=1+\frac a9s+O_H(s^2),\qquad
\frac{Z_0(e^{-2s})}{Z_0(e^{-s})}=2^{-10}+O(s).
\tag{27.4}
$$

Divide the first ratio at $2s$ by the first ratio at $s$, subtract one, and multiply by the second ratio to obtain (27.3). Thus a row-coordinate difference alone prevents a bound $C s^{10}$ with one $C$ for all these matrices. The transient zero eigenvalue $r$ approaches one, so the analytic bounds used in (24.8) need not remain uniform. $\square$

This construction is a counterexample to a uniform kernel estimate over changing machines. It is not asserted to satisfy the two uniform error bounds in (23.8), and therefore supplies neither an efficient tuned classifier nor a counterexample to Theorem 25.4.

**Definition 27.3 (Quantifiers and distinct resource coordinates).** The asymptotic assertion of Theorem 25.4 has quantifier order

$$
\begin{gathered}
\forall\mathcal A\ \exists c_{\mathcal A}>0\ \exists s_{\mathcal A}>0\\
\forall s\in(0,s_{\mathcal A})\ \forall i\in\{0,1\}:
\mathbb E_{i,e^{-s}}T\ge c_{\mathcal A}s^{-11}.
\end{gathered}
\tag{27.5}
$$

where $\mathcal A$ ranges over the full-contract fixed machines. It does not exchange the first quantifier with an infimum over machines chosen separately at each $s$. In particular it supplies no uniform converse for machines retuned to a band width $\epsilon$, even if their numbers of states are bounded while their transition probabilities or transition-description precision vary. Proposition 27.2 demonstrates an obstruction to that exchange in the kernel argument, without settling the testing performance of such retuned machines.

The upper bound (26.4) is an achieved number of states, not a minimum. The comparison with Section 22 neither gives a sharp state or bit lower bound nor proves that cubic mean is optimal among all growing-memory rules. Its statement is that fixed total persistent state cannot realize the published cubic order under this contract, while the specified growing-memory procedure does realize it. A lower bound for deterministic deadlines on supplied bands is a different optimization from a lower bound for expected unbounded stopping and is not substituted for one here.

All the assertions refer to the one fixed $H_c$, its ninth-degree comparison shape and the stated stationary read/stop experiment. A changing residual, a generic family of residual polynomials, hidden-state observations, exact probability responses, external elapsed-time decisions or source resets would require other hypotheses. The producer dimension $D=6$, finite observer states, retained transition descriptions, growing arithmetic workspace and number of paid reads remain different resources. No all-lag discrete-tree memory assertion is a premise or conclusion of this experiment; neither is a physical memory or elapsed-time assertion.

**Definition 27.4 (Mathematical supplier correspondence).** The source-specific deductions here are the stopped finite-observer converse of Theorem 25.4 and the retained-category paid construction of Theorem 26.4, with their comparison in Corollary 27.1. The classical stochastic-matrix representation, spectral and geometric-series identities, bounded stopped telescoping, conditional expectation, geometric waiting counts and predictable-sum identities are proof suppliers. They are not claimed as new principles.

| Supplier | Mathematical input and scope of its use |
| --- | --- |
| [Real renewal instruments and detector rank](FIB_REAL_RENEWAL_INSTRUMENTS_AND_DETECTOR_RANK.md), Definition 12.1, Theorems 15.5 and 17.4, equation (19.7), Definition 20.1, Theorems 20.2–20.3 and equations (18.13), (20.29) | The exact rational-center shape, its positive envelope, its own stationary renewal history, polynomial-geometric moment asymptotics, and the strict parameter-free sum-four mark with its confidence threshold. Those polynomial and confidence proofs are reused. The retention law and its fully paid acquisition mean are established in Section 26. |
| The same source, Theorem 22.3 and Proposition 22.6 | The existing parameter-free cubic-mean procedure and its unbounded counters and growing arithmetic precision. Corollary 27.1 compares that particular achieved mean with the fixed-state converse; it does not assert optimal expected stopping over growing-memory rules. |
| R. A. Flower and M. E. Hellman, “Hypothesis Testing With Finite Memory in Finite Time,” *IEEE Transactions on Information Theory* **18**, 429–431 (1972), introductory model and “Problem Statement,” [primary paper](https://ee.stanford.edu/~hellman/publications/10.pdf) | A finite-valued statistic with a time-invariant, possibly randomized update, a decision depending on that statistic, and stochastic matrices for observation-dependent updates. Their observations are iid and their criterion is error at a specified finite horizon. Here the raw bits are renewal-dependent, labels are absorbing at an actual stopping time, and (24.5), (25.3), (25.7) provide the additional renewal, stopping and payment arguments. No expected-stopping renewal lower bound is attributed to that paper. |
| S. Marzen and J. P. Crutchfield, *Informational and Causal Architecture of Discrete-Time Renewal Processes*, [arXiv:1408.6876v2](https://arxiv.org/html/1408.6876v2), renewal-process definitions and Appendix A | Their interevent zero-count distribution $F(k)$ corresponds to $f_{i,q}(k)$, their survival $w(b)$ to $S_{i,q}(b)$, and their mean zero count plus one to $\mu_i(q)$. The stationary normalized survival and gap-mass-over-survival hazard are the classical conventions behind (23.5), (25.8) and (25.9). The uniform bound $B(1-q)$ and its use for this observer's actual reads are the deductions of Lemma 25.3. |

The supplier correspondences concern those specified mathematical inputs. They imply neither an exhaustive classification of finite-memory testing results nor a claim of worldwide priority for these deductions.

## 追加锚（本行以下为增补区）

## 28. A rounded conditional-product observer on a known band

**Definition 28.1 (Risk inputs, band and rational compilation).** The source is exactly Definition 23.2, with $F_0(k)=k^9$ and the fixed rational-center $F_1(k)=H_c(k)$. Fix a real target $0<\alpha<1/2$. For the fixed-$\alpha$ existence assertion choose once a rational $\rho\in[\alpha/2,\alpha]$. Such a choice needs no real-number oracle: choose an integer $s$ with $2^{-s}<\alpha/2$, and an integer $a$ with $\alpha/2\le a2^{-s}\le\alpha$, by the Archimedean property and the integer ceiling. A finite compiler receives the chosen fraction $\rho$, not an arbitrary real encoding of $\alpha$. The relationship with $\alpha$ is a mathematical certificate on that supplied choice.

The supplied rational risk is denoted by $\rho=\alpha_0$. The more general independent input domain $0<\rho\le\alpha$ is also allowed. All finite constructions and inequalities below hold on that domain, with constants depending on $H_c,\rho$. Constants denoted by dependence on $H_c,\alpha$ alone refer to the once-chosen controlled surrogate, or uniformly to choices in $[\alpha/2,\alpha]$. There is no uniform upper-resource assertion as an independent $\rho$ tends to zero.

Let $h$ be the least nonnegative integer with $2^{-h}\le\rho/2$, and put

$$
b=h+1,\qquad \kappa=1/32,\qquad R=h+2+2\delta_9.
$$

Supply a rational $0<\varepsilon<1/4$, and put $u=1-2\varepsilon$, $v=1-\varepsilon$, $I_\varepsilon=[u,v]$. Reuse the finite rational certificate and moment evaluations (22.28)–(22.32) of the owning volume to obtain

$$
\begin{aligned}
d_{\min}&=\underline d_{u,v}>0,&
\bar\mu&=\max_i\mu_i(v),&\bar\beta&=\max_i\beta_i(v),\\
\mathcal B&=1+\bar\beta+\frac{2\bar\mu R}{d_{\min}},&
W&=\left\lceil\frac{2\mathcal B}{\rho}\right\rceil.
\end{aligned}
\tag{28.1}
$$

These are rational calculations; $R$ is rational as well. The supplier proves $\mathfrak d_i(q)\ge d_{\min}$ on the band, and (22.34) gives $d_{\min}=\Theta_H(\varepsilon^2)$, $\bar\mu,\bar\beta=O_H(\varepsilon^{-1})$. Thus $\mathcal B,W=O_{H,\rho}(\varepsilon^{-3})$; with the controlled surrogate these bounds are $O_{H,\alpha}(\varepsilon^{-3})$. Neither $q$ nor $q'$ is an input.

**Definition 28.2 (Paid pair score and deadline).** Read consecutive actual source bits until the first observed one, and thereafter close every gap and partition consecutive gaps into disjoint pairs. For complete pair $(k,l)=(K_{2j-1},K_{2j})$, set

$$
t_j=k+l,\qquad
\ell_j=\frac{F_1(k)F_1(l)A_0(t_j)}{F_0(k)F_0(l)A_1(t_j)}
       =\frac{c_{1,t_j}(k)}{c_{0,t_j}(k)},\qquad
U^{-1}\le\ell_j\le U=(1+\delta_9)^2<2.
\tag{28.2}
$$

The quantities $A_i,c_{i,t}$ and these bounds are exactly the suppliers (22.2)–(22.3). Let $c_j=\lceil\log_2(j+1)\rceil$, $p_0=0$, and $p_j=b+2c_j+7$ for $j\ge1$. Store the positive dyadic score $G_0=1$. At an active pair update round $G_{j-1}\ell_j$ to the nearest multiple of $2^{-p_j}$, with an exact half-way tie rounded upward, obtaining $G_j$. Emit label one if $G_j\ge2^b$ and label zero if $G_j\le2^{-b}$; otherwise continue.

The capped rule permits at most $W$ reads. On the $W$-th read, if a pair closes, finish its internal arithmetic and give the ordinary threshold decision priority. If no ordinary decision results, emit default zero. A first tick, a zero, or the closing tick of a first gap at the deadline goes to that default after its ordinary bookkeeping. No arithmetic step reads the source. Both terminal labels are internally emitted and absorbing. Write $N,L_\infty$ for the uncapped pair stopping index and paid count, and $L_\varepsilon$ for the capped paid count. All initial zeros, all intervening zeros and ones, and a final incomplete gap or pair are paid. No complete pair is discarded; if a deadline leaves an unscored partial pair, all of its reads remain in $L_\varepsilon$.

**Lemma 28.3 (Error at active and deciding updates).** On every finite sequence of positive gap lengths processed while active, including its deciding update,

$$
G_j>0,\qquad
\left|\log G_n-S_n\right|<\kappa,\qquad
S_n=\sum_{j=1}^n\log\ell_j.
\tag{28.3}
$$

Proof. The predecessor has $2^{-b}<G_{j-1}<2^b$, including $G_0=1$. Hence $x_j=G_{j-1}\ell_j>2^{-b-1}$ and nearest rounding gives

$$
\frac{|G_j-x_j|}{x_j}\le2^{b-p_j}
\le\frac1{128(j+1)^2}=:e_j<1/2.
\tag{28.4}
$$

It follows that $G_j>0$ and the absolute logarithmic error at that update is at most $e_j/(1-e_j)<2e_j$. Since $\sum_{j\ge1}(j+1)^{-2}<1$, their total is below $1/64<\kappa$. The predecessor of a deciding update is active, so the argument includes that update. It is a pathwise error bound, not a claim that the rounded product is a martingale. $\square$

**Theorem 28.4 (Separate risks, finite mean and fully paid band order).** The uncapped rounded rule has each full-family error at most $\rho/2$, terminates almost surely, and has finite paid mean at every fixed parameter. On the supplied band its mean is at most $\mathcal B$. The capped rule satisfies

$$
\begin{gathered}
\sup_{q\in I_\varepsilon}\mathsf P_{0,q}(D=1)\le\rho\le\alpha,
\qquad
\sup_{q'\in I_\varepsilon}\mathsf P_{1,q'}(D=0)\le\rho\le\alpha,\\
L_\varepsilon=\min\{L_\infty,W\}\le W,\qquad
c_{H,\alpha}\varepsilon^{-3}
\le\mathbb E_{i,q}L_\varepsilon\le\mathcal B
\quad(i=0,1,\ q\in I_\varepsilon)
\end{gathered}
\tag{28.5}
$$

for all sufficiently small rational $\varepsilon$, where $c_{H,\alpha}>0$. The upper constants have the dependencies in Definition 28.1.

Proof. Reuse the pair-time conditional cancellation and Ville argument of Theorem 22.3: $e^{S_n}$ is a mean-one nonnegative martingale under each $\mathsf P_{0,q}$, and $e^{-S_n}$ under each $\mathsf P_{1,q'}$. These are separate assertions under the two laws' own pair-sum distributions, not an unconditional likelihood ratio between equal nuisance parameters. Lemma 28.3 puts each erroneous rounded crossing inside the corresponding true-product crossing of height $2^be^{-\kappa}$. Either error is therefore at most

$$
e^\kappa2^{-b}\le e^{1/32}\rho/4<\rho/2.
\tag{28.6}
$$

For the stopped-mean argument set $Z_n=-S_n$ in family zero and $Z_n=+S_n$ in family one. The supplier (22.2) gives $\mathbb E_{0,q}\log\ell=-\mathfrak d_0(q)$ and $\mathbb E_{1,q'}\log\ell=+\mathfrak d_1(q')$. Thus the directed increments have positive mean $\mathfrak d_i$ and absolute size at most $2\delta_9$. Before exit, $|S_n|<b\log2+\kappa<h+2$; the last increment adds at most $2\delta_9$. Consequently $|Z_{N\wedge n}|\le R$ pathwise. The inclusion event $\{N\ge j\}$ is determined before pair $j$. Independence of that pair, followed only by a finite sum, yields

$$
\mathbb E_{i,q}Z_{N\wedge n}
=\mathfrak d_i(q)\sum_{j=1}^n\mathsf P_{i,q}(N\ge j)
=\mathfrak d_i(q)\mathbb E_{i,q}(N\wedge n)\le R.
\tag{28.7}
$$

Monotone convergence proves $\mathbb E N\le R/\mathfrak d_i(q)<\infty$, and hence $N<\infty$ almost surely. Every acquired gap and the stationary initial interval are finite almost surely by the source supplier. Reuse the predictable acquisition identity (22.24), with this rule's predictable inclusion events: a pair duration need not be independent of its own score. It gives

$$
\begin{aligned}
L_\infty&=1+\tau+\sum_{j=1}^N(K_{2j-1}+K_{2j}+2),\\
\mathbb E_{i,q}L_\infty
&=1+\beta_i(q)+2\mu_i(q)\mathbb E_{i,q}N
\le\mathcal B\quad(q\in I_\varepsilon).
\end{aligned}
\tag{28.8}
$$

This counts the stationary first interval and every complete acquired pair. Couple the capped and uncapped rules on the same history. They agree through the deadline, including completion of any pair computation on its last read. Their decisions can differ only when $L_\infty>W$, whose probability is at most $\mathcal B/W\le\rho/2$. Adding (28.6) proves the separate capped risks. Their paid counts obey the minimum identity in (28.5), also on histories timing out in the initial wait or a partial pair. The controller is consequently in the band class of owner Corollary 22.11; its uniform per-family, per-parameter mean lower bound applies directly at risk $\alpha$. No fixed-machine eleventh-order bound is used across band retuning. $\square$

## 29. A bounded bit-transition construction

**Definition 29.1 (Integer words and slack).** Clear the fixed coefficient denominators by a positive integer $D$, and set $\bar F_i=DF_i$, $\bar A_i=D^2A_i$. These four integer polynomials have degree at most nineteen by the owning source's (22.7). Pad them to twenty coefficient slots each. Choose an integer $B\ge8$ so every coefficient has absolute value below $2^B$. Define

$$
\begin{aligned}
m&=\lceil\log_2(2W+2)\rceil,&L_0&=B+8+19m,\\
\lambda&=3L_0+4,&P&=b+2m+7,\\
w&=8(b+P+\lambda+B+m+32),&
a&=8+\lceil\log_2(w+1)\rceil.
\end{aligned}
\tag{29.1}
$$

In particular $w\ge128$, $a\le w$, and

$$
2W+2\le2^m<4W+4.
\tag{29.2}
$$

A word has exactly $w$ bits, numbered from zero at the least significant bit. A signed value uses a magnitude word and a sign bit, with zero assigned positive sign. Every loop bound and stored constant below is an integer fitting a word. A pointer has a cell selector in $\{0,\ldots,255\}$ and a position in $\{0,\ldots,w\}$, costing at most $a$ bits. Position $w$ is a sentinel and is never dereferenced. End tests and moves concern these finite domains; there is no external time coordinate.

**Definition 29.2 (Local transitions and primitive contracts).** Use 256 word cells, 32 pointers, 64 Boolean flags, one input bit and a three-valued output latch. A local internal transition inspects or writes at most four addressed tape bits, changes finite control and flags, and moves at most four heads by one neighboring position, or changes a head's selector to a specified cell. Selector changes preserve its position. A finite sequence of such moves implements a reset or seek. At a boundary a head reverses or exits as specified; it never moves outside $\{0,\ldots,w\}$. Reading or writing a word is a sweep, not one transition. All heads, selectors, flags and intermediate modes are configuration coordinates. For binary encodings of these coordinates charge at most $128w$ internal bit inspections or changes per local transition: $32a+64+30+16\le128w$. This deliberately charges the whole pointer and finite-control encoding, rather than treating a growing address as one bit operation.

The following relations define bounded primitive graphs. Inputs remain protected for a primitive unless an in-place output is explicitly specified. Distinct scratch words receive all other outputs. Copies between operands and scratch are themselves sweeps. Each displayed digit recurrence is one local full-adder or full-subtractor relation on Boolean inputs; it invokes no integer arithmetic on a word.

A zero or copy sweep writes respectively zero or the corresponding input digit for positions $0,\ldots,w-1$. A comparison scans from position $w-1$ down to zero, retaining a flag in $\{<,=,>\}$; the first unequal high digit fixes the flag, which subsequent lower digits preserve. Its invariant is comparison of the already scanned high prefixes. Addition scans upward with carry $c_0=0$ and relations

$$
x_r+y_r+c_r=z_r+2c_{r+1},\qquad z_r,c_{r+1}\in\{0,1\}.
\tag{29.3}
$$

At position $s$ its invariant is $x\bmod2^s+y\bmod2^s=z\bmod2^s+2^sc_s$. The final carry is zero whenever the promised sum is below $2^w$. Subtraction, called only after comparison has certified $x\ge y$, uses borrow $e_0=0$ and

$$
x_r-y_r-e_r=z_r-2e_{r+1},\qquad z_r,e_{r+1}\in\{0,1\}.
\tag{29.4}
$$

The analogous low-prefix identity proves its result and zero final borrow. During either sweep every partially written output is a $w$-bit word; carries and borrows are single flags. Increment, decrement and adding a fixed small integer use these same relations with copied constant operands. A signed addition first compares magnitudes: equal signs select addition; unequal signs select larger minus smaller with the larger operand's sign; equality yields positive zero. This proves its exact signed contract, including cancellation, without two's-complement overflow assumptions.

A one-place left shift sweeps downward, copying each old digit to its upper neighbor and writing zero in bit zero; a one-place right shift sweeps upward and clears the top bit. A bit latch protects the digit when needed. A shift by a supplied $s\in\{0,\ldots,w\}$ repeats this sweep, with a separate loop word initially $s$ decreased by (29.4) after each sweep. Its invariant is the requested partial shift after the completed repetitions. Left shift is called only when the exact final value is below $2^w$, so every discarded high bit is zero. A power word $2^s$, $0\le s<w$, is obtained by shifting the word one. Thus even data-dependent shift lengths are bounded loops with charged counters.

For multiplication of nonnegative words $x,y$ with $xy<2^w$, initialize output $z=0$ and scan the multiplier at positions $r=0,\ldots,w-1$. If $y_r=0$ the row is skipped. If $y_r=1$, form a zeroed row with $x$ shifted by $r$, then add it in place to $z$ by (29.3). Here row formation needs no loop of $r$ shifts: temporarily change the multiplier head's selector to a marker word, mark position $r$, and return its selector. Seek a row head to that marker by a sweep; copy the digits of $x$ upward starting there, then erase the marker. Each copy advances its two heads by one square. Digits of $x$ beyond the row boundary are zero because the selected row $2^rx$ is at most $xy<2^w$. The row invariant is its copied low prefix; the outer invariant is

$$
z=x\sum_{s<r}y_s2^s.
\tag{29.5}
$$

The pending row and every completed accumulation are at most $xy$. Low-digit carry propagation is justified by (29.3), also for the in-place accumulator since its old digit is latched before replacement. No two-word or unbounded product is silently used.

For division of a dividend $A<2^w$ by a positive divisor $V$ with $2V<2^w$, initialize quotient and remainder to zero and scan the dividend downward. For each digit $\xi$, form $r'=2r+\xi$, compare it with $V$, and retain $r'$ or subtract $V$ accordingly; append quotient digit zero or one. If $A_s$ is the dividend prefix already scanned, the invariant is

$$
A_s=Vq_s+r_s,\qquad 0\le r_s<V.
\tag{29.6}
$$

Indeed $0\le2r_s+\xi<2V$, so at most one subtraction restores the invariant. The applications below have $2V<2^w$; the shifted transient therefore fits. Quotient append is an exact one-place shift and bit insertion, and the quotient prefix never exceeds the final quotient. Comparison and subtraction are the preceding sweeps, with their carry/borrow flags reset at entry. These relations prove the division contract, not merely its terminal numerical identity.

All scans use separate heads for the outer digit, inner digit and marker seek. Marker words start and finish zero. Remaining-iteration words use the preceding ripple relations; no loop counter is an uncounted integer. Sentinel entry ends a scan before any dereference. Descending scans enter at sentinel $w$ and first move to $w-1$; ascending scans enter at zero and exit on reaching $w$. Fixed boundary checks and neighboring head moves are finite tape relations, not calls to an arithmetic oracle.

**Lemma 29.3 (Bounded primitive realization and control).** Each contract of Definition 29.2 has a graph with fewer than $2^{14}$ local modes, at most sixteen working pointers and sixteen scratch words, and at most $2^{16}w^2$ local transitions. Its internal bit work, including pointer/control encoding, is at most $2^{23}w^3$. Every bit inspection is of a designated operand, output, scratch or marker cell, or a counted control coordinate; it never inspects the source latch.

Proof. A sweep has entry, seek/reset, digit, end-test and exit modes, with at most two carry/borrow or comparison flags. Each return to the next sweep is a fixed edge. Copy, zero, comparison, addition and subtraction each use at most eight such modes. A repeated shift adds entry/test/decrement/return modes to its two sweeps. Multiplication has outer test, bit choice, row clear, marker set/seek, row copy, marker erase, add, head reset and outer advance. Division has outer test, remainder shift, comparison, conditional subtraction, quotient shift/insertion, reset and outer advance. Include the counter-decrement and zero-test sweeps in the shift graph. Each primitive has at most 32 constituent sweep or connecting types: the ten multiplication types just listed, the eight division types including its digit insertion, and the repeated-shift types each stay within that allowance, including all resets. Allocate sixteen local positions to each type, covering its entry, two seek/reset directions, digit relation, end/sentinel tests and exits. Even allowing all sixteen valuations of four local Boolean branch flags gives $32\cdot16\cdot16=8192$ modes. An additional 1024 connecting/entry/exit positions still leave the total below $2^{14}$. The loop-control words are decremented or tested by their own sweeps in these types, not by extra calls. Signed addition is expanded into comparison and unsigned branches at the caller and is not a recursive primitive.

Eight heads suffice for protected inputs, output, row/remainder, marker and seek scans; allowing sixteen includes saved outer heads while an inner sweep runs. The live scratch consists of row or remainder, quotient, marker, operand copies and loop words; sixteen words exceed the twelve needed even with disjoint outputs. An inner sweep cannot reset the saved outer head. In multiplication the outer scan has $w$ iterations, each with at most sixteen sweeps or resets of length at most $2w+2$; row construction is by marker alignment, not repeated shifting. Division has $w$ such iterations. Repeated shift has at most $w$ repetitions, each with a shift and loop-decrement sweep. Thus $2^{16}w^2$ bounds all moves, flag handling and selector changes, including resets and loop tests, for $w\ge128$. Multiplication's outer invariant (29.5), division's (29.6), and the digit invariants prove the result by induction on their respective scans. They also prove that each loop ends and each promised no-overflow precondition suffices throughout it. Multiplying the local-transition bound by $128w$ proves the bit-work bound. Every transition mentioned concerns tape bits or finite coordinates already counted. $\square$

**Definition 29.4 (Bank allocation and composition).** Cells 0–79 hold the eighty coefficient magnitudes; their signs are fixed branches of the immutable graph. Cells 80–95 hold compiled constants: in order $W,b,m,P,L_0,\lambda,w,0,1,2,7,B$, followed by four zeros. Logical cells 96–115 hold, in order,

$$
r,z,k,l,t,j,p,v,c,M,p_{\rm new},\Delta p,v_s,n,d,A,V,v_{\rm new},H_+,H_-.
\tag{29.7}
$$

Here $r$ is paid reads, $z$ the current zero count, $M=2^c$ the precision comparison word, and $v2^{-p}$ the retained score. Cell 116 holds the disjoint pair-sum output $\sigma$; cells 117–127 are reserved. Cells 128–133 retain the six evaluations $\bar F_1(k),\bar F_1(l),\bar A_0(t),\bar F_0(k),\bar F_0(l),\bar A_1(t)$. Cells 134–143 are signed Horner magnitudes, signs, coefficient copies and outputs; 144–159 are reserved. Cells 160–175 hold factor and rounding product outputs; within that bank cells 164–166 hold respectively the temporary words $J=j+1$, $e_+=p_{\rm new}+b$ and $e_-=p_{\rm new}-b$. Cells 176–191 are reserved. Cells 192–207 are the primitive scratch, including marker and loop words; 208–223 are additional disjoint copies. Cells 224–255 are reserved control scratch. A sign word is always zero or one. Input, output, seen-first-tick, retained-first-gap, carry, borrow and comparison flags belong to the separate latch/flag coordinates, whose allowance of 64 flags also covers primitive branches. Eight pointers are protected caller/initialization heads, sixteen are primitive heads, and eight are spare; there is no hidden tape head.

The second-gap closing-one exit first finishes the copy from $z$ to $l$ and the reset of $z$. Its sole successor is an unsigned addition occurrence with protected inputs $k,l$ in cells 98,99 and disjoint output $\sigma$ in cell 116. Reset the carry at that occurrence's entry and use (29.3) at each digit. Its exit leads only to a copy sweep from cell 116 to $t$ in cell 100; that copy's exit leads only to the first Horner occurrence. Neither exit is read-enabled or tests the deadline. Thus a completed pair produces its actual sum before any evaluation: $\sigma=t=k+l$. Cells 98–100 are protected through all six evaluations and the ensuing score computation. Cell 116 is not primitive scratch and cannot be reused before its copy finishes. Between pairs an old value of $t$ or $\sigma$ has no consumer; every next completed pair traverses these same two occurrences before either $\bar A_i(t)$ call.

Every invocation has fixed operand cell selectors. Copies produce disjoint outputs before a logical cell is overwritten. Coefficient signs and the six argument choices are fixed by call-site identity. No indirect coefficient index is required: for each of the six evaluations unroll the twenty coefficient positions from degree nineteen to zero. At a Horner position, multiply the current magnitude by its nonnegative argument, retain its sign, and signed-add the next coefficient using the branches of Definition 29.2. Starting at signed zero, the invariant is the exact polynomial suffix evaluated at that argument. The output of each evaluation is copied to its protected cell before scratch is reused. Positive final signs follow from $F_i(k)>0$ and $A_i(t)>0$ for $k,l\ge1$, $t=k+l\ge2$, not from coefficient signs.

After the pair-sum copy and all six evaluations, a completed pair obtains the two positive words

$$
n=\bar F_1(k)\bar F_1(l)\bar A_0(t),\qquad
d=\bar F_0(k)\bar F_0(l)\bar A_1(t).
\tag{29.8}
$$

The two-factor outputs use cells 160,161, and are multiplied by their respective third evaluations before copying into $n,d$. These cells and the rounding-product cells are disjoint from 164–166. The factors $D^4$ cancel, so after incrementing $j$ the identity $n/d=\ell_j$ holds for that new pair index. Initially $c=0,M=1$; after the increment produce $J=j+1$ in cell 164 by addition with the stored one, and compare that output with $M$. If larger, double $M$ and increment $c$ once. Initially $J=2$; subsequently the previous $j+1$ was at most $M$, so its increase is at most $M+1\le2M$. Hence one doubling suffices and $c=\lceil\log_2(j+1)\rceil$ exactly. Calculate $p_{\rm new}=b+2c+7$ and $\Delta p=p_{\rm new}-p\ge0$ by protected additions/subtraction. Shift $v$ by $\Delta p$ to $v_s$, and form and divide

$$
A=2v_sn+d,\qquad V=2d,\qquad
v_{\rm new}=\left\lfloor\frac A V\right\rfloor.
\tag{29.9}
$$

This is nearest rounding with upward ties at denominator $2^{p_{\rm new}}$. Produce $e_+$ in cell 165 by addition and $e_-$ in cell 166 by subtraction, then generate the threshold words $H_+=2^{e_+}$ and $H_-=2^{e_-}$ by bounded shifts of one. Compare $v_{\rm new}$ first with $H_+$ and then with $H_-$, and take the specified label if either comparison crosses. Otherwise copy the new numerator and precision to $v,p$, clear the pair-retention flag, and apply the deadline check. A terminal threshold or deadline output enters its absorbing label without another read.

The producer order within a completed-pair path is the following. An exit connects only to its listed next stage, with the fixed branch alternatives already specified. No operand is consumed during a partially completed producing sweep.

| Produced live value | Producing contract and protected inputs | First consumer and required lifetime |
| --- | --- | --- |
| $k,l$ | Closing-one copy sweeps from the exact zero counts; $k$ survives the second-gap reads | Pair-sum addition, followed by all six evaluations; both stay protected until score completion |
| $\sigma,t$ | Addition (29.3) on $k,l$, then the complete copy $\sigma\to t$ | Horner calls on $t$; $t$ stays protected throughout pair arithmetic |
| Six cells 128–133 | Twenty signed Horner positions each, on protected $k,l,t$ and fixed coefficients | Two-factor and third-factor products; all six outputs are written for the current pair before any factor product |
| $n,d$ | Two protected two-factor products, then their third-factor products and copies | Precision-shifted dividend and divisor; neither is overwritten during rounding |
| $j,J,c,M,p_{\rm new},\Delta p$ | Pair-index increment, addition for $J$, comparison/optional doubling, precision additions and subtraction using old $p$ | Exact shift $v_s=2^{\Delta p}v$; old $v,p$ remain protected until score commitment |
| $v_s,A,V$ | Precision shift, product $v_sn$, one-place doubling and addition of $d$; separately double $d$ | Division (29.6), entered only after both $A,V$ are complete and positive |
| $v_{\rm new},e_+,e_-,H_+,H_-$ | Completed quotient, two exponent operations, then bounded power shifts | Threshold comparisons, followed only by a label or score commitment and the deadline check |

The remaining product outputs use cells 162,163 and 167–175, and protective copies use 208–223; each primitive's other scratch stays in 192–207. In particular the dividend and divisor remain protected throughout division, its quotient is copied to cell 113 before division scratch is reused, and the two threshold words remain protected through their comparisons. All disjoint copies and exponent operations in this order belong to the existing precision and factor/rounding occurrence allowances. The pair-sum addition and its copy are two additional primitive occurrences. There is no additional latch, head, flag, stored return address or shift in that pair-sum stage.

There are three read-enabled entry types: initial wait, first-gap collection and second-gap collection. Exactly one next source bit is read into the latch, and control immediately enters a source-disabled bookkeeping graph. Increment $r$ once there. In initial wait a zero changes no gap data, and a one sets seen-first-tick and resets $z$. Thereafter a zero increments $z$; a one copies $z$ into $k$ or $l$, resets $z$, and respectively retains the first gap or enters completed-pair arithmetic. At a non-pair read apply the deadline check after bookkeeping. At a pair read apply it only after the arithmetic and both ordinary comparisons. Only if $r<W$ and no label was produced does control return to a read-enabled entry. The input latch is inspected only in the immediate bookkeeping choice, never by arithmetic. On an impossible adjacent-one input after the first tick, halt with zero; this completes the graph outside the legitimate no11 domain without scoring a zero gap.

Calls are static expansions, not runtime recursion: give every primitive occurrence its own disjoint copy of its local modes and connect its exits directly to its specified successor. A completed inner sweep returns by that fixed edge. There is no return-address stack. A signed Horner position needs at most sixteen primitive occurrences: one coefficient copy, one magnitude product and its protective copy, one magnitude comparison on the unequal-sign branch, at most one addition or one of two subtraction branches, and at most eight copies, clears or sign normalizations on the branch alternatives. Allowing 32 per position also includes entry/exit and both sign choices. The non-Horner stages use fewer than 32 arithmetic/copy occurrences each: the precision stage has one pair-index increment, one $J=j+1$ addition, one comparison, one possible doubling and increment, three precision additions/shifts and a subtraction; the factor/rounding stage has four factor products, one precision shift, three dividend operations, one divisor shift, one division, two exponent operations, two power shifts, two comparisons and the resulting copies. Allowing 128 for each such stage includes disjoint operands, all branches and counter/flag handling. Read bookkeeping needs only increment, zero test, gap copy/reset and deadline comparison on its alternatives. For an explicit graph budget, initialization uses at most 512 primitive occurrences (256 clears, 96 descriptor copies and at most 160 constant/flag/head preparations); read bookkeeping at most 128; pair-sum production exactly two; precision scheduling at most 128; each of 120 Horner positions at most 32 (including all signed branches and protective copies); and factor formation, rounding, comparisons and halts at most 128. Their sum is 4738, below 8192. Branch alternatives count as separate occurrences in this total. One completed read path traverses at most that many occurrences, since the only outer loops are the next-read edge and the one bounded precision doubling; polynomial positions are unrolled. Primitive loops are already counted in Lemma 29.3. The pair-sum stage adds fewer than $2^{15}$ local modes and at most 32 connecting nodes. Adding all read nodes, branch nodes and label nodes to $8192\cdot2^{14}$ local modes fits a control set $Q$ with $|Q|=2^{30}$. Call-site identity and every return edge therefore fit the counted 30-bit control coordinate.

**Lemma 29.5 (All reachable histories and transient widths).** From the initialization below, every legitimate no11 stream has the exact read/score semantics of Definition 28.2. Every transient arithmetic configuration obeys the primitive preconditions in its counted bank; every run halts after at most $W$ paid reads and finite internal work, even on an infinite all-zero stream.

Proof. Initialization sets $r=z=k=l=t=j=p=c=\sigma=0$, $M=v=1$, both source-history flags false, and output empty. Induct on the number of paid reads, inserting the terminating primitive inductions of Lemma 29.3 between reads. At every active read-enabled state, stored $j$ counts the already scored pairs, $p=p_j$ and $v2^{-p}=G_j$; initialization supplies this at $j=0$. Before the first observed one no zeros contribute to a complete-gap statistic. After that one, $z$ is exactly the number of zeros actually read since the last observed one. In first-gap collection no old $k,l,t$ is consumed. Its closing one finishes the copy of $z$ to $k$ before setting retention and entering second-gap collection; subsequent reads protect $k$. The second closing one finishes the copy to $l$ before resetting $z$ and entering pair-sum production. Thus its $k,l$ are the next two exact positive gap lengths. The retention flag determines which, so no partial or discarded interval is substituted for a complete gap. The bookkeeping counter is exactly $r$, with $0\le r\le W$. At every read-enabled state it is below $W$, and every current or completed gap count is at most $W$.

Let $\nu$ denote the current pair's index in this induction; before the precision-stage increment the stored $j$ is $\nu-1$. This is a proof index, with no additional stored coordinate. At the pair-sum addition, $k+l\le2W<2^m<2^w$. Its partial-output invariant is precisely $k\bmod2^s+l\bmod2^s=\sigma\bmod2^s+2^sc_s$ from (29.3). At $s=w$ there is zero final carry, so its completed output is the exact $k+l$. The next copy has the invariant that its written digits of $t$ equal the corresponding digits of that protected $\sigma$; only its completed exit enables Horner. Consequently, at every polynomial-argument consumer,

$$
k=K_{2\nu-1},\qquad l=K_{2\nu},\qquad t=\sigma=k+l,\qquad 2\le t\le2W<2^m.
$$

No read or deadline edge can intervene in these producer paths, and the bank partition prevents scratch from changing $k,l,t$ afterward. This proves the argument invariant for every completed pair, including one closing when $r=W$; it imposes no assertion on an unused stale $t$ between pairs. The subsequent index increment gives stored $j=\nu\le W$ before its precision consumers, while $v,p$ still encode $G_{\nu-1}$. An active score commitment restores $p=p_\nu$, $v2^{-p}=G_\nu$ before any next read. These statements hold on every legitimate stream, irrespective of its probability.

For an argument $1\le x<2^m$, every signed Horner suffix and each multiplication just before coefficient addition have magnitude bounded by

$$
20\,2^B(2^m)^{19}<2^{L_0}.
\tag{29.10}
$$

This bound follows by expanding at most twenty terms, and also bounds a prefix of the Horner recurrence before adding its next coefficient; the maximum exponent reached is nineteen. Same-sign additions and intermediate magnitudes in a signed subtraction satisfy the same envelope. All six positive evaluation outputs are below $2^{L_0}$. The two-factor partial products and the three-factor outputs in (29.8) are positive and below $2^{3L_0}<2^\lambda$. The multiplication primitive's selected rows and accumulated sums are bounded by these exact products. Subtractor partial words need only the full $w$-bit bound, and their borrow is explicitly retained; no assertion that each partially written word satisfies the final polynomial envelope is needed.

The precision induction in Definition 29.4, after producing $J=j+1\le W+1<2^m$, proves $c\le m$, $M\le2^m$, $p_{\rm new}\le P$. Each exponent word is produced before its power shift. The stored $p$ is the previous precision, so its subtraction gives $\Delta p\ge0$; the old score numerator $v$ is still protected at that shift. Initially $p=0,v=1$. Before a later active update $G=v2^{-p}<2^b$, so after the exact precision shift $0<v_s<2^{b+P}$. Thus

$$
0<A=2v_sn+d<2^{b+P+\lambda+2}<2^w,
\qquad 0<V=2d<2^{\lambda+1}.
\tag{29.11}
$$

The rounding product and its partial accumulations fit the same slack. Division restores $0\le r_{\rm div}<V=2d$ after every digit, and its shifted transient satisfies

$$
0\le2r_{\rm div}+\xi<2V=4d<2^{\lambda+2}<2^w.
\tag{29.12}
$$

In particular the restored remainder need not be below $d$. This divisor-specific invariant includes $n=d$, where the final remainder in (29.9) is $d$. The quotient prefix and its append operations fit since the final quotient is at most $A<2^w$.

For the deciding score as well as an active one, nearest rounding and $U<2$ give the safe bound with its additive slack

$$
G_j\le G_{j-1}U+2^{-p_j-1}
<2^{b+1}+2^{-p_j-1}<3\cdot2^b.
\tag{29.13}
$$

Hence $v_{\rm new}<3\cdot2^{b+P}<2^{b+P+2}<2^w$. The thresholds have exponents $p_j\pm b$ in $[0,P+b]$, strictly below $w$; the first update has $p_j\ge b$, so no negative shift occurs. All shift counts, precision sums and subtraction operands consequently meet their primitive contracts. Loop words and head positions are at most $w$; $w$, $w^2$, $256w$ and the fixed allocation/selector constants are below $2^w$ for the chosen $w\ge128$. All copies, arithmetic scratch, signs and pending carries are therefore within their complete coordinate domains.

Protected cells are not overwritten until the corresponding exact output has been proved. In the producer order of Definition 29.4, the current pair's six evaluation outputs are all positive by the just-established $k,l\ge1,t\ge2$ invariant and the owner's defining sums. Hence both products $n,d$ are positive before their dividend/divisor consumers, and division receives the promised positive $V=2d$, rather than an initialized or previous pair's word. The temporary $\sigma,J,e_+,e_-$ fit their bounds above; their fixed cells lie outside primitive scratch. The primitive scratch and pointer partition preserves all suspended caller data. This proves composition by induction on graph edges, not by assuming that membership in a Cartesian set implies correctness. All primitive loops terminate by their scan/repetition bounds. A completed pair's exact quotient (29.9) and threshold tests are precisely Definition 28.2. No arithmetic return edge is read-enabled. Finally, when the last read closes a second gap, its gap copies, sum production, six evaluations, factor products, precision, division and both ordinary comparisons all finish before the deadline consumer; a crossing emits its ordinary label, otherwise the score commit leads to default zero. A last read in any other phase reaches default only after its prescribed bookkeeping. Thus $r=W$ forces a label and no next-read edge is reachable, even on a history with no first tick or no closing pair. $\square$

**Theorem 29.6 (Complete configurations and online work).** The deterministic transducer just constructed has at most

$$
2^{30}\,2^{256w+32a+67}
=2^{256w+32a+97}
\tag{29.14}
$$

complete configurations, and can be encoded by $256w+32a+97$ mutable bits. This includes all operands, constants copied into the bank, scratch, heads, selectors, input and output, flags, modes, call sites and halts. Its paid count is at most $W$ and its internal online work is at most $2^{40}Ww^3$ bit operations, with a separate initialization allowance $2^{34}w^3$.

Proof. There are 256 word cells, 32 pointers, 64 Boolean flags, one input bit, at most two bits for the output latch, and 30 control bits. Lemma 29.5 proves reachability and exact refinement within those domains; multiplying their cardinalities gives (29.14), allowing unused encodings. The pair-sum output occupies one of the already counted cleared words; $J,e_+,e_-$ occupy existing product-bank words. Their lives require no extra coordinates. Per read, at most 8192 primitive occurrences and their connecting edges are traversed. Specifically the two pair-sum occurrences cost at most $2^{17}w^2$ local transitions and $2^{24}w^3$ bit work, with at most $32\cdot128w=4096w$ additional bit work for their connections. This is below $2^{25}w^3$ per completed pair. No shift is added there; the precision and threshold shifts retain their proved counts below $w$. Lemma 29.3 charges $2^{23}w^3$ per occurrence; $2^{40}w^3$ leaves slack for all 4738 occurrences, read nodes, phase/selector/flag setting and the threshold/timeout output. Initialization has fewer than 512 occurrences; its corresponding $2^{34}w^3$ allowance includes every clear and copy, including cell 116 and the temporary product-bank words. No operations before the first source read are omitted from that separate charge. For fixed $H,\rho$, (29.1)–(29.2) give $w=O_{H,\rho}(1+\log(W+2))$ and $a=O(1+\log(w+1))$. Thus the complete online bit bound is logarithmic in $W+2$ and its configuration count is polynomial in $W+2$. Under the controlled surrogate the constants depend only on $H,\alpha$. $\square$

**Proposition 29.7 (Compiler, deployed descriptor and initialization).** Let $B_{\rm in}$ be the total binary length of the supplied rational band and risk descriptions, including any unreduced or padded representation. Fixed-model preparation and rational compilation are outside the deployed bank and are separately paid. The compiler retains only a bounded compiled descriptor for deployment; it never copies an arbitrary input fraction into a $w$-only online word.

Proof. Apply owner Proposition 22.6 explicitly as follows. Its fixed-degree preparation computes $A_i$, the polynomials (22.28), and the doubling certificate $T_0$; coefficient clearing supplies the four integer polynomials and the fixed $B$ here. If $B_{\rm mod}$ counts those fixed descriptions, that supplier charges the coefficient generation separately and the doubling search by

$$
O\!\left((1+\log(T_0+2))(B_{\rm mod}+\log(T_0+2))^2\right)
$$

bit work and $O(B_{\rm mod}+\log(T_0+2))$ workspace, up to its absolute fixed-degree constants. Thereafter its band preprocessing (22.57) applies with this input's $u,v,\rho$:

$$
K_{\rm pre}=O\!\left(B_{\rm mod}+(T_0+20)(B_{\rm in}+\log(T_0+2))+1\right),
\qquad
\text{work}=O\!\left((1+\log(T_0+2))K_{\rm pre}^2\right).
\tag{29.15}
$$

The correspondence is exact: evaluate the same $G_{17}(u,T_0)$ and moment rational functions, compute $h$ by risk comparisons, and replace $R_\alpha$ by the identical rational expression $h+2+2\delta_9=R$. Equation (28.1) then uses the same positive-denominator rational operations and integer ceiling. From $W$ the compiler obtains $m$ by power-of-two comparisons, and then $b,P,L_0,\lambda,w$ by fixed integer operations. These extra shifts/comparisons and descriptor padding take $O(K_{\rm pre}^2)$ work and $O(K_{\rm pre})$ workspace after increasing the supplier's fixed constants: $h=O(B_{\rm in}+1)$ and the binary length of $W$ is already bounded by $K_{\rm pre}$. No logarithm of a real quantity is evaluated by an oracle. The existence choice of a rational surrogate is separate from these finite rational-input compilation costs.

The deployed immutable description is the fixed local-transition schema and its static call graph, together with exactly 96 $w$-bit words: the eighty coefficient magnitudes and the sixteen compiled fields in Definition 29.4. Coefficient signs are fixed graph branches. The schema describes width and endpoint domains using the stored integer $w$; it is not an explicitly printed exponentially large transition table. The fixed schema can be encoded with a numerical constant $C_{\rm graph}=2^{48}$ bits: fewer than $2^{30}$ mode records, each of at most $2^{12}$ bits specifying its Boolean guards, at most four head/bit actions and its fixed successor labels, leave space for all graph headers and fixed coefficient-sign branches within that constant. Endpoint tests use the width symbol, whose integer value is in the compiled fields. Its description length therefore satisfies

$$
D_{\rm dep}\le C_{\rm graph}+96w.
\tag{29.16}
$$

Here $C_{\rm graph}$ is independent of the band and risk, since the graph has the fixed bounds in Definition 29.4, fixed cell selectors and fixed polynomial degree. Width-dependent scalar fields are among the 96 words. Raw fractions, $d_{\min}$, moments and other compiler intermediates are discarded; their construction is charged by (29.15). A redundant long encoding of a fixed numerical band therefore affects preprocessing, without becoming hidden online storage.

Initialization first clears the 256 cells by bounded sweeps. It then copies the 96 immutable words, one bit at a time, into their corresponding bank cells; its call sites for the 96 fields are unrolled. The descriptor address is a field in $\{0,\ldots,95\}$ and a bit position in $\{0,\ldots,w\}$, so it needs at most $7+\lceil\log_2(w+1)\rceil\le a$ bits, using an already counted initialization pointer. That pointer has an immutable-source role during copying, fixed by the mode; the destination pointer has the bank role. Thus no extra uncounted memory-kind selector is required. The fixed graph is selected by the counted 30-bit control label and is never addressed as mutable data. Each field's sentinel ends its copy before dereference. An optional serial descriptor counter is at most $96w<2^w$ and fits a reserved word. No raw input-description address is needed. The same head/selector budget covers clears, copies and resets; endpoint-dependent constants are read-only until copied, and every copied field fits because of (29.1), (29.10) and $w\ge128$. Finally set $M=v=1$, clear the logical cells and flags as in Lemma 29.5, and enter initial wait. Preparation of known word one or zero is a bounded sweep. This is the initialization already counted by $2^{34}w^3$; it uses the complete bank and heads of (29.14). The graph itself remains immutable and is charged in $D_{\rm dep}$, rather than copied to an uncounted program tape. After initialization no mutable descriptor address persists outside the bank and no descriptor access carries a source observation. $\square$

## 30. The implementation theorem and its scope

**Corollary 30.1 (Fixed-risk complete-memory existence).** For the fixed stationary renewal families with polynomial $H_c$ and every fixed real $0<\alpha<1/2$, choose once a rational $\rho\in[\alpha/2,\alpha]$ as in Definition 28.1. For every sufficiently small supplied rational $\varepsilon>0$ there exists the deterministic controller of Section 29, compiled from that band and risk fraction, with source-independent initialization, satisfying

$$
\begin{gathered}
\sup_{q\in[1-2\varepsilon,1-\varepsilon]}\mathsf P_{0,q}(D=1)\le\alpha,
\qquad
\sup_{q'\in[1-2\varepsilon,1-\varepsilon]}\mathsf P_{1,q'}(D=0)\le\alpha,\\
L_\varepsilon\le W=O_{H,\alpha}(\varepsilon^{-3}),\qquad
\mathbb E_{i,q}L_\varepsilon=\Theta_{H,\alpha}(\varepsilon^{-3})
\quad(i=0,1,\ q\in I_\varepsilon),\\
\text{complete online mutable bits}\le256w+32a+97
=O_{H,\alpha}(1+\log(1/\varepsilon)),\\
\text{internal online bit work}\le2^{40}Ww^3,
\qquad
\text{initialization bit work}\le2^{34}w^3.
\end{gathered}
\tag{30.1}
$$

Its complete configuration count is (29.14), polynomial in $\varepsilon^{-1}$. The same construction accepts every independent rational $0<\rho\le\alpha$ with the exact bounds (28.1), (29.1), (29.14)–(29.16); for that larger input domain the upper asymptotic constants are $H,\rho$ dependent. The lower mean constant can still be taken from the target-risk $\alpha$ supplier. No actual nuisance value is supplied, estimated for compilation, or used as an immutable transition parameter.

Proof. Theorem 28.4 gives the risks, paid cap, fully priced mean upper bound and the direct owner 22.11 mean lower. Lemma 29.5 proves exact agreement for every legal capped history, not only in distribution or on selected examples. Theorem 29.6 gives all mutable coordinates and internal work; Proposition 29.7 supplies the separately charged compiler and bounded descriptor initialization. These apply simultaneously to this one controller at each band. $\square$

**Definition 30.2 (Supplier correspondence and evidential boundary).** The exact fixed source, positive envelope, stationary initial wait and iid post-tick gaps come from owner Definition 20.1, Theorems 15.5 and 17.4, and continuation Definition 23.2. The finite pair-sum cancellation, factor orientation and bounded increments are (22.2)–(22.3); positive drift and the rational band certificate are Theorems 22.2 and 22.4, especially (22.28)–(22.34). The predictable duration identity and the Ville crossing argument are reused from Theorem 22.3, including its cited Howard–Ramdas–McAuliffe–Sekhon Lemma 1, (2.11). The compiler accounting is Proposition 22.6, especially (22.57). The mean lower is precisely Corollary 22.11, uniform over band-retuned protocols and separately for each family and each parameter on the band. Those analytic and preprocessing suppliers are applied here, not reproved. The added mathematical content is the summably rounded positive product and its complete bounded bit-transition refinement.

The background correspondences have narrower scope. Flower and Hellman, “Hypothesis Testing With Finite Memory in Finite Time,” *IEEE Transactions on Information Theory* 18, 429–431, use iid observations, a finite statistic, time-invariant possibly randomized updates, and a decision at a fixed horizon. That supplies background for finite-valued observers, not this dependent-renewal stopping or memory theorem. Marzen and Crutchfield, *Informational and Causal Architecture of Discrete-Time Renewal Processes*, arXiv:1408.6876v2, supply the classical iid interevent-count and stationary-survival conventions used by the owner. Broniatowski and Caron, *Conditional inference in parametric models*, arXiv:1202.0944v1, Section 4.1, (9)–(11), give background on nuisance conditioning by sufficient statistics; the discrete pair-sum identity used here is already the exact owner calculation. No approximation theorem from that paper enters the controller proof. These limited attributions do not assert that any external paper supplies the complete construction.

Compiler workspace/work, deployed immutable description, initialization, complete online mutable bits, internal bit operations, paid reads and emitted labels are distinct coordinates. The construction has no fresh or retained random inputs. It uses one consecutive actual history, pays every initial and partial interval, emits its own labels, and has no free age, clock, probability query, source copy, reset, skip or archive. Its bit-transition model and numerical charges imply no physical elapsed-time, energy or device claim. This is an ordinary-paper construction, with no kernel-verification, worldwide-priority, sharp-constant or minimum-memory assertion. The necessity established by the supplier concerns paid mean; no memory necessity or converse uniform over band-retuned finite machines is inferred from the fixed-machine results of Sections 23–27. Varying $H_c$ or sending its residual to zero is outside the theorem.

## 追加锚（本行以下为增补区）
