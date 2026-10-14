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
