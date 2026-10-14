# Retuned bounded-memory uniform renewal converse

## 1. The source-conditional result and its scope

This companion volume concerns one exact pair of stationary binary renewal sources. At each known common parameter $q$, an observer may be redesigned arbitrarily, but its complete persistent configuration set has a fixed bound $M$. Under the source premises stated in Section 2, both of its paid means are bounded below by a positive constant times $(-\log q)^{-11}$ near $q=1$. The constant and endpoint neighborhood depend only on $M$, the fixed polynomial $H_c$ and the risk allowance, and are chosen before the observer. The result therefore permits changing transition probabilities and initialization as $q$ changes.

The source-specific premises and existing upper construction belong to [Real renewal instruments and detector rank: finite observer memory](FIB_REAL_RENEWAL_INSTRUMENTS_AND_DETECTOR_RANK_CONTINUATION.md), revision `303bcf74526bab511d2175d5e302205d43654ab6`, Definitions 23.1–23.2 through Definition 27.4. The unrestricted cubic-mean comparison belongs to [Real renewal instruments and detector rank](FIB_REAL_RENEWAL_INSTRUMENTS_AND_DETECTOR_RANK.md), revision `07123ef6f510e6df2d990240c55e29ed9d7c2485`, only the supplied append consisting of Definition 22.8 through Definition 22.12, source lines 4803–4922. The first supplied text consists of 663 lines through its final append anchor; the second consists of 120 lines through its final append anchor. References to earlier chapters inside these texts are supplier attributions, not additional independently established premises.

The new deductions relative to these source texts are the finite-chain multiplicative hitting bound, the uniform stationary initial-law comparison, the short-weight clipping relation, and their combination into the observer-uniform converse. Their proofs are given below. The upper observer and unrestricted cubic results retain their source ownership. Nonnegative state elimination, first-step equations, total-variation contraction, stopped telescoping, conditional expectation and geometric waiting counts are classical intermediate methods. No worldwide-priority claim accompanies this source-relative addition.

This is ordinary handwritten mathematical exposition conditional on fallible handwritten source premises. It is reference theory, not a Lean kernel certificate. In particular the all-integer polynomial envelope and the exact sum-four certificate are explicitly supplied premises; their nested proofs are outside this volume's evidence. Source identification with particular generating instruments is unnecessary for the theorem about the specified output laws.

## 2. Exact polynomial premises and stationary observations

**Definition 2.1 (The fixed rational-center shapes).** For a real argument $x$, keep exactly

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
\delta=\frac{2749658638697}{10^{24}}>0,
\qquad B=1+\delta,
\qquad a=\frac{43377331415040}{35\cdot10^{24}}>0.
\tag{2.2}
$$

The credited premise from the continuation's equation (23.3), attributed there to the owning source's Theorem 15.5, is

$$
k^9\le F_i(k)\le Bk^9\quad(i=0,1),
\qquad 1\le\frac{H(k)}{k^9}\le1+\frac\delta k
\quad\text{for every integer }k\ge1.
\tag{2.3}
$$

The polynomial is the rational-center shape, not a limiting residual-zero coefficient vector. Its degree-eight coefficient is $a$, and both shapes are monic of degree nine. Throughout the volume $H$, $\delta$ and $B$ are fixed, independently of $q$ and of every observer.

**Definition 2.2 (The stationary consecutive-read law).** For $i\in\{0,1\}$ and $0<q<1$, put

$$
\begin{aligned}
Z_i(q)&=\sum_{k\ge1}F_i(k)q^k,
& f_{i,q}(k)&=\frac{F_i(k)q^k}{Z_i(q)}\quad(k\ge1),
& f_{i,q}(0)&=0,\\
S_{i,q}(b)&=\sum_{k\ge b}f_{i,q}(k)\quad(b\ge0),
&\mu_i(q)&=\sum_{k\ge1}(k+1)f_{i,q}(k),\\
\beta_i(q)&=\frac{\sum_{k\ge1}k(k+1)f_{i,q}(k)}{2\mu_i(q)}.
\end{aligned}
\tag{2.4}
$$

The law $\mathsf P_{i,q}$ on $X_0,X_1,\ldots$ is specified as follows. Draw the first tick time $\tau$ with

$$
\mathsf P_{i,q}(\tau=b)=\frac{S_{i,q}(b)}{\mu_i(q)}\quad(b\ge0).
\tag{2.5}
$$

Place zeros before $\tau$ and a one at $\tau$. Independently draw iid zero counts $K_1,K_2,\ldots$ with law $f_{i,q}$, and put further ones at

$$
\tau_0=\tau,
\qquad \tau_n=\tau+\sum_{r=1}^n(K_r+1)\quad(n\ge1).
\tag{2.6}
$$

All remaining bits are zero. This is exactly the continuation's stationary forward-wait convention (23.4)–(23.6). In particular $S_{i,q}(0)=S_{i,q}(1)=1$. The first wait has the survival-normalized law (2.5), rather than the complete-gap law $f_{i,q}$.

The normalization and mean follow from nonnegative summation:

$$
\sum_{b\ge0}S_{i,q}(b)=\sum_{k\ge1}(k+1)f_{i,q}(k)=\mu_i(q),
\qquad
\mathbb E_{i,q}\tau
=\frac1{\mu_i(q)}\sum_{k\ge1}\frac{k(k+1)}2f_{i,q}(k)
=\beta_i(q).
\tag{2.7}
$$

Each moment is finite at every interior $q$. We use the source's polynomial-geometric moment estimates (23.7), attributed there to equations (18.13) and (20.29): with $s=-\log q$,

$$
Z_i(e^{-s})=9!s^{-10}(1+O_H(s)),
\qquad \mu_i(e^{-s})=\frac{10}{s}+O_H(1),
\qquad \beta_i(e^{-s})=\frac{11}{2s}+O_H(1).
\tag{2.8}
$$

For parameter correspondence, if $R_j(q)=\sum_{k\ge1}k^jq^k$, the ordinary power-sum identity is $R_j(e^{-s})=(-d/ds)^j(1/(e^s-1))$. Its leading term is $j!s^{-j-1}$. The monic degree-nine terms therefore yield the three leading orders in (2.8); the lower-degree coefficients contribute lower orders. No numerical evaluation or finite sampling supplies an all-integer premise here.

## 3. Retuning and the complete state budget

**Definition 3.1 (A compliant observer at a known common parameter).** Fix an integer $M\ge2$, a risk $0<\alpha<1/2$ and $q\in(0,1)$. A machine may depend arbitrarily on $(q,H,\alpha,M)$, including in its state set, initialization and real transition probabilities. Its initialization is independent of the source and its design is the same under the two true labels. Every action reads the next actual bit or stops with an internally emitted label $D\in\{0,1\}$. Updates use the current configuration, the bit just read and fresh independent randomness. There is no continuity assumption across $q$, bound on immutable transition-description precision, spectral gap, or positive lower bound on nonzero transitions.

The total number of persistent configurations is at most $M$. This counts initialization configurations, active states, both decision labels, all control phases, registers and retained random choices. A stored seed or a counter selecting random updates belongs to the configuration. A supply of fresh independent coins supplies no additional retained information. Known $q$ is an immutable design input; every mutable use of information still passes through the counted configuration set.

The only source access is the single consecutive history in Definition 2.2. There is no external clock, time, age, action counter, program counter, archive, read-length decoder, hidden true label, skipped bit, free gap, reset, second source or probability response. In particular the mathematical cost tally is not an input, and an external recipient does not decode $D$ from the time of stopping.

The paid cost is $T$ when the machine reads $X_0,\ldots,X_{T-1}$. It includes initial zeros, ticks, every subsequent zero and any terminal partial gap. Initial stopping has $T=0$. Compliance requires just the two selected risks and the two separate pointwise termination and mean conditions:

$$
\begin{gathered}
\mathsf P_{0,q}(D=1)\le\alpha,
\qquad \mathsf P_{1,q}(D=0)\le\alpha,\\
\mathsf P_{i,q}(T<\infty)=1,
\qquad \mathbb E_{i,q}T<\infty\quad(i=0,1).
\end{gathered}
\tag{3.1}
$$

Write $\mathfrak A_M(q,\alpha)$ for this class. Unlike the source's one fixed $q$-free observer over two separate nuisance families, an element of this class may be chosen anew at each known common $q$. Full-family correctness is a sufficient stronger condition and is not required for the converse.

**Lemma 3.2 (Normal form within the same state budget).** At a fixed $q$, the read-ready reduction of the continuation's Lemma 23.4 gives a row distribution $\eta$ and row-stochastic zero and one matrices $A,C$ on a state set $\mathcal S$ with $|\mathcal S|\le M$. It has two absorbing labels $d_0,d_1$ fixed by both matrices. Each other state is ready for its next paid read. This preserves $(T,D)$ under both source laws.

Proof. Compose initialization with the ensuing current-state read/stop choice. Following a read, compose the bit update with the ensuing read/stop choice. Send all stopping probability to its actual label; merge terminal configurations carrying the same label. The remaining read configurations are the existing active configurations, and all retained control and random information is already counted. Thus composition adds no persistent state. The same $\eta,A,C$ serve both hypotheses at this fixed $q$. Fixing a label on subsequent bits supplies only an analytical continuation after the actual stop, with no change to the paid actions or emitted label. This is the source's normal-form argument applied pointwise to the retuned machine. $\square$

Use total variation $\|u-v\|_{\rm TV}=\tfrac12\sum_x|u(x)-v(x)|$. Suppress $q$ in the matrices and in $f_i,S_i$ when no ambiguity arises. The analytical completed-gap and stationary initial rows are

$$
U_i=\sum_{k\ge1}f_i(k)A^kC,
\qquad \nu_i=\sum_{b\ge0}\frac{S_i(b)}{\mu_i}\eta A^bC.
\tag{3.2}
$$

They are stochastic averages including the absorbing rows. All subsequent comparisons use the same actual $\eta,A,C$ at the selected $q$.

## 4. Multiplicative comparison of finite-chain hitting probabilities

**Lemma 4.1 (A state-budget bound without an exit-probability threshold).** Let $P,Q$ be row-stochastic matrices on the same finite state set of size at most $M$, with common absorbing labels $d_0,d_1$. Suppose $\gamma\ge1$ and

$$
\gamma^{-1}P(x,y)\le Q(x,y)\le\gamma P(x,y)
\quad\text{for all }x,y.
\tag{4.1}
$$

Let $h_P(x),h_Q(x)$ be their probabilities of ever reaching $d_1$, without assuming absorption from every state. Set $K_M=2\cdot3^M$. Then

$$
\gamma^{-K_M}h_P(x)\le h_Q(x)\le\gamma^{K_M}h_P(x),
\qquad
\sup_x|h_Q(x)-h_P(x)|\le\gamma^{K_M}-1.
\tag{4.2}
$$

Proof. The entrywise comparison gives identical directed supports. Let $\mathcal Z$ be the common set of vertices with no directed path to $d_1$. Their hitting values are zero. Replace both rows at each such vertex by an identity row. This preserves the hitting probabilities: once such a vertex is reached, $d_1$ can never be reached. Comparison survives the replacement. The boundary now consists of $d_1$, with hitting value one, and the vertices of $\mathcal Z$, with hitting value zero; it uses only existing vertices.

Fix a vertex $x$ outside this boundary. Every remaining nonboundary vertex has a path to $d_1$. To eliminate another such vertex $z$, for either current matrix $p$ put

$$
e_z=\sum_{v\ne z}p(z,v)=1-p(z,z)>0,
\qquad
p'(u,v)=p(u,v)+\frac{p(u,z)p(z,v)}{e_z}
\quad(u,v\ne z).
\tag{4.3}
$$

The positive exit sum follows from the path to $d_1$. Each new row sums to $(1-p(u,z))+p(u,z)e_z/e_z=1$, and boundary rows remain identity rows. Formula (4.3) preserves actual hitting probabilities on surviving vertices: at a visit to $z$, its self-loop excursions exit almost surely, with exit law $p(z,v)/e_z$. Observe the chain only when it is outside $z$. Its next-state distribution is exactly (4.3). Reaching the surviving target $d_1$ is unchanged. Countably many visits to $z$ introduce no positive probability of remaining there forever, since the conditional probability of such a permanent self-loop excursion at each visit is zero. Equivalently, the first-step identity

$$
h(z)=\frac{\sum_{v\ne z}p(z,v)h(v)}{e_z}
\tag{4.4}
$$

substitutes into the identities at surviving states, and the excursion interpretation identifies the preserved solution with the actual hitting probabilities. This avoids relying on uniqueness of harmonic solutions in nonabsorbing classes.

Positive paths through $z$ become positive shortcuts in (4.3). A path with no repeated vertices shows that every surviving nonboundary vertex still has a path to $d_1$. Thus the next elimination again has a positive exit sum.

Suppose the current pair of matrices is entrywise comparable by $\kappa\ge1$. Its two $e_z$ values, being nonnegative sums of off-diagonal entries, are comparable by the same factor. Consequently the excursion terms in (4.3) are comparable by $\kappa^3$. The direct terms are comparable by $\kappa$, hence also by $\kappa^3$. Addition of nonnegative terms preserves the latter bound, including at zero entries. After $r$ eliminations the comparison factor is at most $\gamma^{3^r}$. No lower bound on $e_z$ is used; comparison of a nonnegative sum, rather than subtraction of nearly equal self-loop probabilities, controls its denominator.

Eliminate all nonboundary vertices except $x$. In the final chain every other vertex is boundary, and a path to $d_1$ remains. Therefore

$$
h(x)=\frac{p(x,d_1)}{\sum_{v\ne x}p(x,v)}.
\tag{4.5}
$$

The denominator is positive. Both numerator and denominator are comparable by $\gamma^{3^r}$, so the quotient is comparable by $\gamma^{2\cdot3^r}$, bounded by $\gamma^{K_M}$ because fewer than $M$ vertices were eliminated. A zero numerator is zero in both chains. Boundary vertices already have equal values. This proves the multiplicative inequalities for every $x$.

If two numbers in $[0,1]$ are comparable by a factor $G\ge1$, subtract the smaller from the larger and bound the result by $(G-1)$ times the smaller, hence by $G-1$. Take $G=\gamma^{K_M}$ to finish (4.2). Reducibility, periodicity, unreachable closed classes and arbitrarily small exits are all included. $\square$

## 5. A uniform initial comparison and short-weight clipping

**Lemma 5.1 (The stationary initial mixture bound).** With the actual initial rows (3.2), define

$$
R_j(q)=\sum_{k\ge1}k^jq^k,
\qquad
r_H(q)=\delta\frac{R_9(q)+R_8(q)}{R_{10}(q)+R_9(q)}.
\tag{5.1}
$$

For every retuned observer at the selected $q$,

$$
\|\nu_0-\nu_1\|_{\rm TV}\le r_H(q)\le\frac{2\delta}{\mu_0(q)}.
\tag{5.2}
$$

Proof. Put

$$
g_i(b)=\sum_{k\ge\max(1,b)}F_i(k)q^k,
\qquad \mathcal W_i=\sum_{k\ge1}(k+1)F_i(k)q^k=Z_i\mu_i.
\tag{5.3}
$$

Each $k$ occurs in $g_i(b)$ for exactly $b=0,\ldots,k$, so $\sum_b g_i(b)=\mathcal W_i$. The exact first-tick law is $g_i(b)/\mathcal W_i$. Premise (2.3) gives $g_1(b)\ge g_0(b)$ and

$$
0\le\mathcal W_1-\mathcal W_0
\le\delta\sum_{k\ge1}(k+1)k^8q^k
=\delta(R_9+R_8),
\qquad \mathcal W_0=R_{10}+R_9.
\tag{5.4}
$$

If $\mathcal W_1>\mathcal W_0$, normalizing $g_1-g_0$ exhibits the label-one first-tick law as a mixture containing $\mathcal W_0/\mathcal W_1$ times the label-zero law. Its total-variation distance is at most $(\mathcal W_1-\mathcal W_0)/\mathcal W_1$, which is at most $r_H(q)$ by (5.4). If the normalizers agree, the laws agree.

Passing each first-tick law through the common stochastic map $b\mapsto\eta A^bC$ contracts total variation. Indeed each finite-state event has conditional probability in $[0,1]$ under that map, so its two averages differ by at most the input variation. This proves the first bound. Since $R_8\le R_9$ and $\mu_0=(R_{10}+R_9)/R_9$, it proves the second. By (2.8) this is $O_H(s)$ uniformly over machines. Initialization may depend on $q$ and may stop immediately; the contraction still uses the same map under both labels. $\square$

**Lemma 5.2 (Additive target perturbation and multiplicative opponent comparison).** For an integer $L\ge1$, put

$$
\begin{aligned}
\pi_i&=\pi_i(q,L)=\sum_{k=1}^Lf_i(k),\\
\mathcal J_i^L&=\pi_i^{-1}\sum_{k=1}^Lf_i(k)A^kC,
&\mathcal V_i^L&=(1-\pi_i)^{-1}\sum_{k>L}f_i(k)A^kC,\\
\gamma_L&=1+\frac\delta{L+1}.
\end{aligned}
\tag{5.5}
$$

For a chosen target $i$ and opponent $j=1-i$, define the analytical comparison matrix

$$
W=\pi_j\mathcal J_j^L+(1-\pi_j)\mathcal V_i^L.
\tag{5.6}
$$

Then, for every row and every entry respectively,

$$
\|U_i(x,\cdot)-W(x,\cdot)\|_{\rm TV}\le\pi_i+\pi_j,
\qquad
\gamma_L^{-1}U_j(x,y)\le W(x,y)\le\gamma_L U_j(x,y).
\tag{5.7}
$$

Proof. Positivity of all $f_i(k)$ at an interior $q$ gives $0<\pi_i<1$ for finite $L$, so all matrices in (5.5) are stochastic and preserve both label rows. On $k>L$, let $t(k)=F_1(k)/F_0(k)$. Premise (2.3) places $t(k)$ in $[1,\gamma_L]$. The ratio of the two conditional tail laws is

$$
\frac{f_1(k)/(1-\pi_1)}{f_0(k)/(1-\pi_0)}
=\frac{t(k)}{\displaystyle\sum_{\ell>L}\frac{f_0(\ell)}{1-\pi_0}t(\ell)}.
\tag{5.8}
$$

The denominator also lies in $[1,\gamma_L]$. Thus the conditional tails are comparable by $\gamma_L$ in both directions; their $Z_i$ normalizations have cancelled. Averaging common nonnegative entries of $A^kC$ preserves this comparison for $\mathcal V_i^L$ and $\mathcal V_j^L$. Adding the common short term $\pi_j\mathcal J_j^L$ gives the entrywise inequalities in (5.7). In particular $W$ retains the entire support of $U_j$, including zeros in the transition matrices.

For the other comparison use $U_i=\pi_i\mathcal J_i^L+(1-\pi_i)\mathcal V_i^L$. Subtraction gives

$$
U_i-W=\pi_i(\mathcal J_i^L-\mathcal V_i^L)
-\pi_j(\mathcal J_j^L-\mathcal V_i^L).
\tag{5.9}
$$

Each difference of probability rows has total variation at most one. The triangle inequality proves the first part of (5.7). $\square$

The matrix $W$ is a proof object for one target. It does not supply a new operational source, skip any actual short gap, or acquire any tail gap for free. A tail-only replacement can lose transitions enabling absorption; no termination claim about that replacement is used. Keeping the opponent's short term gives the support comparison needed by Lemma 4.1.

## 6. Unbounded stopping and the price of actual consecutive reads

**Lemma 6.1 (Analytical epochs and a per-target stopped comparison).** Couple the actual observer to the full source history and hold its label fixed after the actual stop. Let $Y_n$ be its analytical state just after the tick at $\tau_n$, and define

$$
N=\inf\{n\ge0:Y_n\in\{d_0,d_1\}\},
\qquad Q_T=\sum_{t\ge0}\mathbf1_{\{T>t\}}X_t,
\qquad p_i=\mathsf P_{i,q}(D=1).
\tag{6.1}
$$

For a compliant machine, $Y_0$ has row $\nu_i$, its transition kernel is $U_i$ under family $i$, and

$$
Y_N=d_D,
\qquad N\le Q_T\le T.
\tag{6.2}
$$

For each target $i$ separately, with the target's $W$ from (5.6),

$$
|p_i-p_j|\le r_H(q)+\chi_{M,L}+(\pi_i+\pi_j)\mathbb E_{i,q}N,
\qquad \chi_{M,L}=\gamma_L^{K_M}-1,
\quad j=1-i.
\tag{6.3}
$$

Proof. The epoch representation and pathwise inequality (6.2) are the continuation's Lemma 25.1 applied at this fixed $q$. Independence of the future gaps and fresh update randomness gives (3.2). If the machine stops before or at the first tick, $N=0$. Otherwise, each live state $Y_0,\ldots,Y_{N-1}$ is immediately after an actually read tick and commits to a further read. These are $N$ distinct paid ticks, proving $N\le Q_T$. Each tick counted in $Q_T$ is one of the $T$ actual reads.

If stopping occurs during zeros, the next analytical tick merely records the frozen label. It need not have been read, and is not charged in $Q_T$. All source intervals are finite almost surely, so actual termination ensures $N<\infty$ and $Y_N=d_D$. The finite paid mean gives $\mathbb E_iN<\infty$.

Let $h$ be the probability of ever reaching $d_1$ for $W$, and let $h_j$ be that probability for $U_j$. First-step conditioning gives

$$
0\le h,h_j\le1,
\qquad Wh=h,
\qquad U_jh_j=h_j,
\qquad h(d_0)=h_j(d_0)=0,
\quad h(d_1)=h_j(d_1)=1.
\tag{6.4}
$$

These hitting functions are defined even at abstract states with nonabsorbing classes. By Lemmas 4.1 and 5.2,

$$
\sup_x|h(x)-h_j(x)|\le\chi_{M,L}.
\tag{6.5}
$$

For an integer $n\ge1$, stopped conditional expectation along the actual target chain gives

$$
\mathbb E_i h(Y_{N\wedge n})-\nu_i h
=\mathbb E_i\sum_{r=0}^{(N\wedge n)-1}
  [(U_i-W)h](Y_r).
\tag{6.6}
$$

Indeed a live increment has conditional mean $(U_i-I)h=(U_i-W)h$, and after $N$ the increment vanishes. Because $h$ takes values in $[0,1]$, (5.7) bounds each summand by $\pi_i+\pi_j$ in absolute value. Bounded convergence on the left and domination by $(\pi_i+\pi_j)N$ on the right justify $n\to\infty$. Using $h(Y_N)=D$ yields

$$
|p_i-\nu_i h|\le(\pi_i+\pi_j)\mathbb E_iN.
\tag{6.7}
$$

The opponent terminates from its actual initial law, so $p_j=\nu_jh_j$. Decompose

$$
p_i-p_j=(p_i-\nu_i h)+\nu_i(h-h_j)+(\nu_i-\nu_j)h_j.
\tag{6.8}
$$

Bounds (6.7), (6.5) and (5.2) prove (6.3). Repeating with the other target changes only the analytical comparison $W$; it uses the same actual $\eta,A,C$ and gives the other expectation separately. Neither global absorption from every abstract state nor a bound on the sum of the two means replaces these two inequalities. $\square$

**Lemma 6.2 (Predictable tick payment, including the stationary first wait).** Every legal read/stop rule for Definition 2.2, including a retuned observer, satisfies

$$
\mathbb E_{i,q}Q_T\le B(1-q)\mathbb E_{i,q}T.
\tag{6.9}
$$

Proof. This is the pointwise payment bound of the continuation's Lemma 25.3. Its argument is retained to identify the exact access filtration and the paid actions. After an observed tick and $b\ge1$ ensuing zeros, the probability that the next bit is one is

$$
\frac{f_i(b)}{S_i(b)}
=\frac{F_i(b)q^b}{\sum_{k\ge b}F_i(k)q^k}
\le\frac{Bb^9q^b}{\sum_{k\ge b}b^9q^k}
=B(1-q).
\tag{6.10}
$$

At $b=0$ it is zero because $K\ge1$. Earlier complete gaps are independent of the current gap, so the bound holds conditional on the entire preceding bit history.

Before the first observed tick, $b$ zeros give the event $\tau\ge b$. The next-one hazard is

$$
\frac{S_i(b)}{\sum_{v\ge b}S_i(v)}.
\tag{6.11}
$$

For integers $k\ge1$ and $r\ge0$, premise (2.3) gives $F_i(k+r)\ge(k+r)^9\ge k^9\ge B^{-1}F_i(k)$. Shifting tail terms therefore gives

$$
S_i(b+r)\ge B^{-1}q^rS_i(b)\quad(b,r\ge0).
\tag{6.12}
$$

For $b=0$, the shifted terms begin at $r+1$ and are a subset of the tail defining $S_i(r)$; this suffices for the same inequality. Sum (6.12) over $r$ to bound (6.11) by $B(1-q)$. The stationary first wait has thus been treated with its own law.

Expose an independent supply of observer coins on the analytical probability space and let $\mathcal F_t$ contain those coins and the prefix $X_0,\ldots,X_{t-1}$. They leave the source hazards unchanged. The event $\{T>t\}$ that the next read is undertaken is $\mathcal F_t$-measurable. By Tonelli and the conditional hazard bound,

$$
\begin{aligned}
\mathbb E_iQ_T
&=\sum_{t\ge0}\mathbb E_i\left[
 \mathbf1_{\{T>t\}}\mathbb E_i(X_t\mid\mathcal F_t)\right]\\
&\le B(1-q)\sum_{t\ge0}\mathsf P_i(T>t)
=B(1-q)\mathbb E_iT.
\end{aligned}
\tag{6.13}
$$

Only actual reads appear, including the terminal read. Exposed proof coins are not a retained machine register. No unread closing tick or full mean gap is charged to an interrupted gap. $\square$

## 7. The reusable finite-parameter inequality and uniform endpoint theorem

**Theorem 7.1 (Finite-$q$ converse for either paid mean).** Under the exact source premises of Section 2, for every $M\ge2$, $0<\alpha<1/2$, $q\in(0,1)$, $\mathcal A\in\mathfrak A_M(q,\alpha)$, integer $L\ge1$ and $i\in\{0,1\}$, set $b_\alpha=1-2\alpha$. Then

$$
b_\alpha\le r_H(q)+\chi_{M,L}
+[\pi_0(q,L)+\pi_1(q,L)]B(1-q)\mathbb E_{i,q}^{\mathcal A}T,
\tag{7.1}
$$

and consequently

$$
\mathbb E_{i,q}^{\mathcal A}T
\ge\frac{[b_\alpha-r_H(q)-\chi_{M,L}]_+}
 {B(1-q)[\pi_0(q,L)+\pi_1(q,L)]}.
\tag{7.2}
$$

Here $[x]_+=\max(x,0)$, $r_H$ is (5.1), $\pi_i$ is (5.5), and $\chi_{M,L}=(1+\delta/(L+1))^{2\cdot3^M}-1$. The denominator is strictly positive at every interior $q$.

Proof. The two selected risks give $p_0\le\alpha$, $p_1\ge1-\alpha$ and hence $p_1-p_0\ge b_\alpha$. Apply Lemma 6.1 for target $i$ and use (6.2) and Lemma 6.2 to obtain $\mathbb E_iN\le B(1-q)\mathbb E_iT$. This proves (7.1). Positivity of $B$, $1-q$ and both short masses permits division. Nonnegativity of the paid mean gives the positive-part version (7.2). These steps apply for either target to the same actual machine. $\square$

**Theorem 7.2 (Observer-uniform fixed-budget eleventh-power converse).** Keep the exact fixed $H_c$, the source premises and the observation contract. For every fixed integer $M\ge2$ and $0<\alpha<1/2$, there exist $c(M,H_c,\alpha)>0$ and $s_0(M,H_c,\alpha)>0$ such that

$$
\begin{gathered}
\forall s\in(0,s_0)\ \forall\mathcal A\in
 \mathfrak A_M(e^{-s},\alpha)\ \forall i\in\{0,1\}:\\
\mathbb E_{i,e^{-s}}^{\mathcal A}T\ge c\,s^{-11}.
\end{gathered}
\tag{7.3}
$$

The constants are chosen before every machine and are independent of the true label and of the selected $q$ in this neighborhood. They permit arbitrary retuning across $q$.

Proof. All choices below use only $M,H_c,\alpha$. Put

$$
\begin{aligned}
b_\alpha&=1-2\alpha,
&K_M&=2\cdot3^M,\\
L&=\max\left\{1,\left\lceil\frac{8K_M\delta}{b_\alpha}\right\rceil\right\},
&S_L&=\sum_{k=1}^Lk^9,
&C_L&=\frac{4BS_L}{9!}.
\end{aligned}
\tag{7.4}
$$

These are finite and positive. With $x=K_M\delta/(L+1)$, the choice of $L$ gives $0\le x\le b_\alpha/8<1/2$. The elementary inequalities $\log(1+u)\le u$ and $e^x\le(1-x)^{-1}$ for $0\le x<1$ yield

$$
\chi_{M,L}
\le e^x-1
\le\frac{x}{1-x}
\le2x
\le\frac{b_\alpha}{4}.
\tag{7.5}
$$

For completeness the exponential inequality follows by comparing the nonnegative series $\sum_{n\ge0}x^n/n!$ with $\sum_{n\ge0}x^n$. Thus (7.5) uses no transition-specific estimate.

Choose $s_H>0$, depending only on the fixed source, so that the source moment estimates (2.8) give

$$
Z_0(e^{-s})\ge\frac{9!}{2}s^{-10},
\qquad \mu_0(e^{-s})\ge\frac5s
\quad(0<s<s_H).
\tag{7.6}
$$

Because $Z_i\ge Z_0$, $F_i(k)\le Bk^9$ and $q^k\le1$, at $q=e^{-s}$ we have

$$
\pi_i(q,L)\le\frac{BS_L}{Z_0(q)}
\le\frac{2BS_L}{9!}s^{10},
\qquad \pi_0+\pi_1\le C_Ls^{10},
\qquad r_H(e^{-s})\le\frac{2\delta}{5}s.
\tag{7.7}
$$

Take

$$
s_0=\min\left\{s_H,1,\frac{5b_\alpha}{8\delta}\right\},
\qquad c=\frac{b_\alpha}{2BC_L}
=\frac{b_\alpha\,9!}{8B^2S_L}>0.
\tag{7.8}
$$

For $0<s<s_0$, (7.5) and (7.7) each consume at most $b_\alpha/4$ of the decision separation. The per-target inequality (6.3), with the selected risks, therefore gives

$$
\frac{b_\alpha}{2}
\le C_Ls^{10}\mathbb E_{i,e^{-s}}N
\le BC_Ls^{10}(1-e^{-s})\mathbb E_{i,e^{-s}}T
\le BC_Ls^{11}\mathbb E_{i,e^{-s}}T.
\tag{7.9}
$$

Division proves (7.3) with (7.8), separately for both families. None of $L,C_L,c,s_0$ uses $A,C,\eta$, spectral projections, a transition lower bound or machine-description precision. Every comparison was at the fixed selected $q$; no derivative or limiting continuity of a retuned matrix enters. $\square$

The two distinct relations in (5.7) explain the power. For the fixed cutoff $L$, clipping gives an $O_{H,L}(s^{10})$ additive change relative to the target, uniformly over observers, while its multiplicative change relative to the opponent has a fixed small hitting-probability effect controlled by the state budget. A fixed decision separation consequently requires order $s^{-10}$ live epochs under each target. Actual-read hazards price those epochs at a further order $s^{-1}$. Uniform additive $O(s^{10})$ closeness of the two original kernels is not a premise of this argument.

## 8. Conditional nonempty-class attainment and small budgets

**Definition 8.1 (The credited finite upper observer).** The continuation's Definition 26.1 and Lemmas 26.2–26.3 supply a deterministic $q$-free observer with the following exact constants and realization. Define

$$
\begin{aligned}
C_i&=F_i(2)^2+2F_i(1)F_i(3),
&\theta_i&=\frac{F_i(2)^2}{C_i},\\
\Delta_\theta&=\theta_0-\theta_1,
&V&=\max_{i=0,1}\theta_i(1-\theta_i).
\end{aligned}
\tag{8.1}
$$

Its supplied exact sum-four premise, attributed there to Theorem 20.2, is, with $r_k=H(k)/k^9$,

$$
r_1r_3-r_2^2
=\frac{520040714516414119558257878908551006355871}
 {331776\cdot10^{48}}>0,
\qquad 0<\theta_1<\theta_0<1.
\tag{8.2}
$$

This equality is credited rather than independently recalculated. In particular $\Delta_\theta,V>0$. Choose once a rational $0<\alpha_0\le\alpha$ and set

$$
n_\alpha=\left\lceil\frac{8V}{\alpha_0\Delta_\theta^2}\right\rceil,
\qquad b_{n_\alpha}=\left\lceil\frac{n_\alpha(\theta_0+\theta_1)}2\right\rceil,
\qquad S_\alpha=10n_\alpha(n_\alpha+1)+3.
\tag{8.3}
$$

The sample-count integer called $M$ in the source's (26.3) is $n_\alpha$ here; it is distinct from this volume's total state budget $M$.

The supplied observer reads through the first actual tick, then reads every raw gap through its closing tick. It retains categories $1,2,3$ only, preserves a pending category across all intervening long gaps, and pairs consecutive retained categories. A pair is accepted when its categories sum to four; its mark is one for $(2,2)$ and zero for $(1,3)$ or $(3,1)$. Pending memory is cleared after each retained pair. At the $n_\alpha$th accepted pair it emits zero if its one-mark count is at least $b_{n_\alpha}$, and one otherwise.

The full source state set comprises a first-tick waiting state, both labels, and active configurations

$$
(z,p,m,v),\qquad z\in\{0,1,2,3,4\},\quad
p\in\{\varnothing,1,2,3\},\quad
0\le m<n_\alpha,\quad0\le v\le m.
\tag{8.4}
$$

Here $z$ is the zero count saturated at four, $p$ the pending category, $m$ the accepted-pair count and $v$ the one-mark count. Updates and the terminal threshold are compiled into the fixed deterministic table. There is no additional program state or elapsed-read counter. The supplied bound counts all of these configurations:

$$
5\cdot4\sum_{m=0}^{n_\alpha-1}(m+1)+3
=10n_\alpha(n_\alpha+1)+3=S_\alpha.
\tag{8.5}
$$

The following are the exact source-owned laws and paid-mean identities used for this application, not new upper-construction claims. Put

$$
A_i^{\rm sh}(q)=\sum_{k=1}^3F_i(k)q^k,
\qquad \rho_i(q)=\frac{A_i^{\rm sh}(q)}{Z_i(q)},
\qquad \zeta_i(q)=\frac{C_iq^4}{A_i^{\rm sh}(q)^2}.
\tag{8.6}
$$

Retained categories have iid law $F_i(k)q^k/A_i^{\rm sh}(q)$ for $k=1,2,3$. Retention waiting counts are iid geometric of mean $1/\rho_i$ and independent of the entire retained category sequence. Acceptance probabilities are $\zeta_i>0$, and accepted marks are iid Bernoulli$(\theta_i)$: every accepted composition contributes the same factor $q^4$. The supplied midpoint confidence calculation gives both separate full-family errors at most

$$
\frac{4V}{n_\alpha\Delta_\theta^2}\le\frac{\alpha_0}{2}\le\alpha.
\tag{8.7}
$$

The continuation's Theorem 26.4 supplies almost-sure termination and finite pointwise means at every $q$. If $G$ denotes the number of raw post-first-tick gaps read to completion, its identities are

$$
\mathbb E_iG=\frac{2n_\alpha}{\rho_i\zeta_i}
=\frac{2n_\alpha Z_iA_i^{\rm sh}}{C_iq^4},
\qquad T=1+\tau+\sum_{r=1}^G(K_r+1),
\tag{8.8}
$$

and

$$
\begin{aligned}
\mathbb E_{i,q}T
&=1+\beta_i(q)+\frac{2n_\alpha\mu_i(q)Z_i(q)A_i^{\rm sh}(q)}{C_iq^4},\\
\mathbb E_{i,e^{-s}}T
&\sim\kappa_i s^{-11},
\qquad \kappa_i=\frac{20n_\alpha\,9!\,A_i^{\rm sh}(1)}{C_i}>0.
\end{aligned}
\tag{8.9}
$$

For exact correspondence, the same source supplies $C_0=301510$ and $A_0^{\rm sh}(1)=20196$; $A_1^{\rm sh}(1)=H(1)+H(2)+H(3)$ is fixed by (2.1). The displayed leading coefficients are therefore the source's exact positive coefficients, with its sample-count symbol replaced by $n_\alpha$.

These source identities include all discarded long gaps, rejected pairs, the initial wait and the terminal tick. Their payment justification is predictable inclusion: $\{G\ge r\}$ depends only on preceding raw gaps and is independent of $K_r$. Thus the source prices the completed sum by $\mu_i\mathbb E_iG$, without assuming that a gap duration is independent of the acceptance decision made after that gap. No raw gap is skipped when its saturated category becomes ineligible. The fixed transition description is separate from the mutable state count; no optimal description-length claim is used.

**Corollary 8.2 (Attained order for sufficiently large fixed budgets).** Conditional also on the supplied upper-observer premise (8.2) and the source results in Definition 8.1, for every fixed $M\ge S_\alpha$ the class $\mathfrak A_M(q,\alpha)$ is nonempty at every $q\in(0,1)$. For each $i$, define

$$
\mathfrak m_{i,M}(q)=\inf_{\mathcal A\in\mathfrak A_M(q,\alpha)}
\mathbb E_{i,q}^{\mathcal A}T.
\tag{8.10}
$$

Then

$$
\mathfrak m_{i,M}(e^{-s})=\Theta_{M,H_c,\alpha}(s^{-11})
\quad(i=0,1),
\tag{8.11}
$$

with one common observer attaining this order under both hypotheses.

Proof. The supplied observer has at most $S_\alpha$ complete states by (8.5), both required errors by (8.7), and almost-sure termination and finite means by (8.9). It is admissible at known $q$ by ignoring $q$, so it proves nonemptiness. Theorem 7.2 bounds each infimum below uniformly over all retuned machines. The same supplied observer bounds each infimum above by (8.9), with positive leading coefficients. This proves the order statement and simultaneous order attainment. The source construction has not become a new construction by this application, and an order bound does not identify an exact optimizer. $\square$

**Proposition 8.3 (The two-state class is empty; intermediate budgets are unclassified).** For $M=2$ and $0<\alpha<1/2$, $\mathfrak A_2(q,\alpha)$ is empty at every $q$. No emptiness classification or matching upper construction for $2<M<S_\alpha$ is supplied by the present argument.

Proof of the emptiness assertion. The two required absorbing labels exhaust the state budget; no active configuration remains. If the initial label is one with probability $p$, the risks require both $p\le\alpha$ and $1-p\le\alpha$, contradicting $\alpha<1/2$. For intermediate budgets Theorem 7.2 still bounds every compliant observer whenever the class is nonempty, but the upper construction fits only at the stated sufficient threshold. These facts neither prove emptiness nor provide an upper bound there. $\square$

## 9. The earlier fixed-machine result and the unrestricted cubic comparison

The continuation's Theorem 25.4 has quantifier order

$$
\begin{gathered}
\forall\mathcal A\ \exists c_{\mathcal A}>0\ \exists s_{\mathcal A}>0\\
\forall s\in(0,s_{\mathcal A})\ \forall i\in\{0,1\}:
\mathbb E_{i,e^{-s}}^{\mathcal A}T\ge c_{\mathcal A}s^{-11}.
\end{gathered}
\tag{9.1}
$$

for one fixed finite $q$-free full-contract machine. Its Lemma 24.2 uses the non-one spectral resolvent of a fixed zero matrix $A$ to obtain $O_{\mathcal A,H}(s^{10})$ completed-gap closeness and $O_{\mathcal A,H}(s^2)$ initial-row closeness. The resolvent neighborhood and constants depend on $A$. A transition eigenvalue approaching one under retuning can invalidate uniform versions of those estimates. Formula (7.3) instead places $c,s_0$ before the observer; its initial estimate is the machine-uniform $O_H(s)$ bound (5.2).

The source's Proposition 27.2 makes the additive obstruction concrete. In its three-state machine, zero preserves the live state $u$ with probability $r$ and otherwise emits $d_0$; one emits $d_1$. The completed-gap coordinate is

$$
U_i(q)(u,d_1)=\frac{Z_i(qr)}{Z_i(q)}.
\tag{9.2}
$$

For fixed $r<1$ the source's fixed-machine estimates apply. On the changing diagonal $r=q=e^{-s}$ the source proves

$$
\frac{Z_1(e^{-2s})}{Z_1(e^{-s})}
-\frac{Z_0(e^{-2s})}{Z_0(e^{-s})}
=\frac{a}{9\cdot2^{10}}s+O_H(s^2).
\tag{9.3}
$$

Since $a>0$, this rules out one additive $Cs^{10}$ bound for all retuned matrices. The example is a counterexample to that kernel estimate, not a compliant classifier counterexample: it is not supplied as satisfying both testing risks. It neither disproves Theorem 7.2 nor establishes efficient tuned testing. The present proof uses a different pair of comparisons (5.7).

The supplied unrestricted append's Theorem 22.9 and Corollaries 22.10–22.11 give the cubic paid-mean lower order and matching unrestricted upper order for the same $H_c$ and stationary consecutive-read experiment. Its paid length $L$ corresponds to $T$ here. Its full-family observer is $q$-free and may have arbitrary persistent memory; its common-band version may be retuned to the supplied band. The matching procedure and prefix-KL suppliers cited inside that append are nested source claims. They are credited comparisons, not dependencies of the eleventh-power proof.

In the source's band notation $I_\varepsilon=[1-2\varepsilon,1-\varepsilon]$, its Corollary 22.11 supplies both separate worst-band mean infima and the joint worst-band mean infimum of order $\Theta_{H_c,\alpha}(\varepsilon^{-3})$, with $\varepsilon\le-\log q\le4\varepsilon$ on sufficiently small bands. This is a source-owned unrestricted-memory statement; it is not used to assert any fixed-$M$ upper bound.

The source's lower argument also applies pointwise when common $q$ is known and only its two selected risks are required. To see the parameter correspondence, put $\rho=(1-2\alpha)/4$, $\beta=\alpha+\rho$ and

$$
b_{\rm ent}=(1-2\beta)\log\frac{1-\beta}{\beta}>0.
\tag{9.4}
$$

For a fixed target $i$ with mean $m_i$, its proof-fixed cap is $W=\max\{1,\lceil m_i/\rho\rceil\}$. Retain an ordinary label if the protocol stops by read $W$, and otherwise default to $1-i$. Markov's bound increases only the target error, by at most $\rho$, while the opponent error cannot increase. Both capped errors are therefore at most $\beta<1/2$. The index $i$ selects this proof comparison; it is not supplied as a true label to the original observer. At this fixed $q$, the capped label remains one common measurable function of the prefix and a common independent seed, even if the design depends on known $q$. The source's forward data-processing and prefix envelope give the first inequality below, using its quantities $A_{\rm src}(q),B_{\rm src}(q)$ from (22.60). Since $W\le m_i/\rho+1$ and $B_{\rm src}(q)>0$, rearrangement gives the second:

$$
b_{\rm ent}\le A_{\rm src}(q)+WB_{\rm src}(q),
\qquad
m_i\ge\rho\frac{[b_{\rm ent}-A_{\rm src}(q)-B_{\rm src}(q)]_+}
 {B_{\rm src}(q)}.
\tag{9.5}
$$

The source's (22.64) has $A_{\rm src}(e^{-s})=O_H(s^2)$ and $B_{\rm src}(e^{-s})=\Theta_H(s^3)$, which yields the cubic lower order with constants before the protocol. These prefix premises are not independently established here. The supplied $q$-free cubic upper procedure is also allowed in the unrestricted known-$q$ class by ignoring $q$. Conditional on those suppliers, its per-family infima consequently have cubic order as well.

A cubic information lower bound does not imply the fixed-budget eleventh-power bound. The supplied cubic procedure has unbounded possible gap and pair counters and growing arithmetic precision; finitely many named integer registers are not a finite configuration set. For any fixed $M$ admitting a classifier, (7.3) precludes a paid $O(s^{-3})$ mean under even one family while retaining both risks and both mean conditions. For $M\ge S_\alpha$, (8.11) makes the comparison nonvacuous. This is a separation of the specified resource classes, conditional on their respective suppliers, rather than a statement about physical storage.

## 10. Correspondence, evidence limits and open resource questions

**Definition 10.1 (Source-relative content and supplier map).** The mathematical dependencies and ownership are as follows.

| Input or deduction | Exact correspondence and status |
| --- | --- |
| Continuation, Definition 23.1 and equation (23.3) | Equations (2.1)–(2.3) retain the exact rational-center $H_c$ and integer ratio envelope. The nested all-integer envelope proof is a supplied premise. |
| Continuation, Definition 23.2 and equation (23.7) | Definitions (2.4)–(2.6) retain the stationary first-tick law and iid subsequent gaps; (2.8) retains the moment orders. $K$ counts zeros and $K+1$ counts a complete post-tick paid interval. |
| Continuation, Lemma 23.4 and Lemmas 25.1–25.3 | Lemma 3.2 and Section 6 apply the credited representation, epoch accounting, stopped-telescope and predictable-payment methods at one selected $q$. Their roles are explicit in the clipped proof; their classical methods are not claimed as inventions. |
| Continuation, Theorem 25.4 and Proposition 27.2 | Section 9 credits the machine-dependent converse and the changing-machine obstruction. Neither is substituted for the uniform quantifiers in Theorem 7.2. |
| Lemmas 4.1, 5.1, 5.2 and 6.1; Theorems 7.1–7.2 | Source-relative derived content: finite-chain multiplicative hitting stability, the initial-law mixture, target-specific clipping, the reusable finite-$q$ inequality and the fixed-$M$ known-common-$q$ uniform converse. The complete structural derivation is in Sections 4–7. |
| Continuation, Definition 26.1, Lemmas 26.2–26.3 and Theorem 26.4 | Definition 8.1 states the exact credited upper observer, positive sum-four premise, complete state bound, risks and paid means. Source sample count $M$ is renamed $n_\alpha$; its total state count is $S_\alpha$. |
| Corollary 8.2 | Source-relative derived application: the uniform lower bound and the same credited common upper observer establish order for every fixed $M\ge S_\alpha$. No new upper construction is claimed. |
| Owning source's supplied mean append, Theorem 22.9 and Corollaries 22.10–22.11 | Section 9 credits the unrestricted cubic order and retuned-band order, conditional on that append's nested prefix and upper suppliers. Its proof-local timeout uses only selected risks and therefore gives the stated known-common-$q$ application. |

The derived entries are `repo-derived` in the sense of ordinary source-relative inference. There is no external literature search establishing a priority claim or a `suspected-novel` classification. The continuation itself attributes finite-statistic stochastic models to Flower and Hellman and stationary renewal conventions to Marzen and Crutchfield. Those are secondary supplier attributions here; this volume does not independently certify those papers' exact scopes or attribute the present renewal paid-mean converse to them.

The main converse uses (2.3), the specified renewal law, its moment orders, the complete finite state count, both selected risks and separate finite paid means. The additional sum-four certificate is needed for the supplied nonempty-class upper construction, and is not needed for Theorems 7.1–7.2. The continuation's producer dimension $D=6$ and its identification with particular instruments are separate nested claims, unnecessary to either the state-budget comparison or the result for the laws defined in Section 2. They do not establish a finite-bit producer model.

**Open question 10.2 (Dependence on the state budget).** The exponent $K_M=2\cdot3^M$ in the elimination comparison is a coarse sufficient bound. The optimal dependence of absorption stability and of the resulting paid-mean constants on $M$ is unresolved here. A sharper estimate would require a proved uniform bound replacing this elimination loss; the existing positive constants do not assert sharpness.

**Open question 10.3 (Nonempty budgets and growing memory).** The minimum nonempty complete state budget and the performance classification for $2<M<S_\alpha$ are unresolved. For memory budgets $M=M(s)$ growing toward the endpoint, the finite-$q$ inequality (7.2) can still be applied at each finite budget, but the constants and cutoff in (7.4) change. No fixed positive constant uniform over such growth follows from Theorem 7.2. Determining the transition toward the credited unrestricted cubic order requires additional estimates and constructions; neither the sufficient upper threshold nor the fixed-$M$ theorem supplies them.

The theorem has no varying-$H$, residual-uniform, hidden-$N$, general-parity, exact-optimizer or sharp-constant conclusion. Its output laws, access model and payment convention are explicit mathematical assumptions. It establishes no empirical machine-learning behavior, physical memory law, external elapsed-time decision bound or broader project completion. Extra persistent channels, reset access, hidden-state observations or changes to the stationary start require a different theorem with their own hypotheses. Full source authorship and verification of the exact authored source are distinct evidentiary acts; the handwritten statements here do not claim kernel verification or a consensus certificate.

## 追加锚（本行以下为增补区）
