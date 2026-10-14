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

## 11. The growing-budget suppliers in the present observation contract

**Definition 11.1 (Credited results and common hypotheses).** Write $G$ for [Growing state budgets in the renewal paid-mean tradeoff](FIB_GROWING_STATE_BUDGET_RENEWAL_TRADEOFF.md), and $C$ for [Real renewal instruments and detector rank: finite observer memory](FIB_REAL_RENEWAL_INSTRUMENTS_AND_DETECTOR_RANK_CONTINUATION.md). The forest comparison, strengthened finite-parameter converse, simultaneous endpoint bound and configuration-growth implication used below are the existing results of $G$, Sections 4–5 and Theorems 8.1, 9.1 and 10.1. They are not additional discoveries of this append. The further consequence concerns complete fixed-width binary memory and its comparison with the supplied band controller of $C$, Sections 28–30.

The correspondence is literal. Definitions 2.1–2.2 of $G$ use the same $F_0(k)=k^9$, $F_1(k)=H_c(k)$, rational-center polynomial (2.1), positive constant $\delta$ and $B=1+\delta$ as Sections 2–3 here. Its integer envelope is precisely (2.3), its first wait is (2.5), its subsequent zero counts are (2.6), and its moment premise is (2.8). Its Definition 3.1 is $\mathfrak A_M(q,\alpha)$ here, with the same source-independent initialization, the same machine under both labels at the same known common $q$, and arbitrary retuning at each $q$. In particular all persistent control, register, label and retained-randomness configurations count toward $M$; the actual consecutive-read cost is $T$, including the stationary initial interval and the terminal partial interval. Both selected risks, both almost-sure stops and both separate finite paid means in (3.1) remain required. There is no extra age, clock, archive, reset, skipped bit, source copy, parameter, probability or sample query. The normal form of $G$, Lemma 3.2, has exactly the $\eta,A,C,U_i,\nu_i$ of (3.2). Neither a fixed observer across parameters nor a lower bound on its positive transition probabilities is required.

For the finite-chain input, take any row-stochastic $P,Q$ on the same set $\mathcal S$, $|\mathcal S|\le M$, with the distinct common absorbing labels $d_0,d_1$ and the entrywise comparison (4.1) for a finite $\gamma\ge1$. These are exactly $G$, Definition 4.1; reducible chains with additional closed classes are permitted. In the common positive support put

$$
\mathcal Z=\{x:\text{no directed path from }x\text{ to }d_1\},
\qquad \partial=\mathcal Z\cup\{d_1\},
\qquad V=\mathcal S\setminus\partial,
\qquad n=|V|\le M-2.
\tag{11.1}
$$

Here paths may have length zero, so $d_1\notin\mathcal Z$, whereas $d_0\in\mathcal Z$. The common boundary is the whole zero-target set together with the target. The row replacement on $\mathcal Z$ in that definition preserves the actual hitting probabilities and entrywise comparison without adding a state. This is not a single-root tree calculation on the original reducible chain.

Apply $G$, Definition 4.2 and Lemma 4.3, with its target $t=d_1$, interior $V$, and boundary $\partial$. Its forests have roots exactly $\partial$, one outgoing non-self edge at each vertex of $V$, and no interior cycle. With the supplier's notation for denominator, target-marked numerator and complementary numerator, for $R=P,Q$ and $x\in V$ the supplied identities are

$$
\mathcal D_R=\mathcal A_R(x)+\mathcal C_R(x)>0,
\qquad
\det(I-R_{VV})=\mathcal D_R,
\qquad
h_R(x)=\frac{\mathcal A_R(x)}{\mathcal D_R}.
\tag{11.2}
$$

All sums are nonnegative sums of monomials of the same degree $n$. The supplier's positive distance-decreasing forest proves $\mathcal D_R>0$ and uniqueness of this finite Dirichlet problem; first-step conditioning identifies its solution with the actual hitting function. Its proof does not assert uniqueness of unconstrained harmonic functions on the original chain. Common support gives the same forest families for $P,Q$, so $G$, Theorem 5.1, applies directly and gives

$$
\gamma^{-2n}h_P(x)\le h_Q(x)\le\gamma^{2n}h_P(x),
\qquad
|h_Q(x)-h_P(x)|\le\frac{\gamma^n-1}{\gamma^n+1}
\quad(x\in\mathcal S).
\tag{11.3}
$$

The boundary values are zero on $\mathcal Z$ and one at $d_1$. Thus zero hitting probabilities are handled without dividing by them. A zero complementary sum makes both hitting values one. If $n=0$, the empty forest has weight one and every state is boundary; if $\gamma=1$, the additive bound is zero. Zero edges contribute zero in both kernels. Self-loops are accounted for by the supplier's row identity $1-R(u,u)=\sum_{v\ne u}R(u,v)$, rather than omitted from the stochastic experiment. Additional closed classes lie in $\mathcal Z$. Arbitrarily small positive exits can make forest sums small but do not affect their termwise comparison. These are precisely the degeneracies covered in $G$, Lemma 4.3 and Theorem 5.1; no global absorption assumption or uniform exit threshold is added here.

To identify the renewal application, fix the actual machine and one selected $q$. For target $i$ put $j=1-i$, and retain $\pi_i,\mathcal J_i^L,\mathcal V_i^L,\gamma_L$ from (5.5). The supplier's $J_i^L,V_i^L$ are these $\mathcal J_i^L,\mathcal V_i^L$. Its comparison is exactly

$$
W_i=\pi_j\mathcal J_j^L+(1-\pi_j)\mathcal V_i^L,
\qquad
\gamma_L=1+\frac\delta{L+1}.
\tag{11.4}
$$

By $G$, Lemma 6.2, equivalently Lemma 5.2 here, $W_i$ has the entire support of $U_j$, fixes both labels, and differs from $U_i$ by row variation at most $\pi_i+\pi_j$. Consequently (11.3) applies to $P=U_j,Q=W_i$ on the same complete state set. The opponent's short component in (11.4) is retained; a tail-only replacement is not an admissible substitute. The initial-row term is precisely $r_H(q)$ of (5.1), by $G$, Lemma 6.1 and Lemma 5.1 here, including source-independent immediate stopping and the stationary first row $\nu_i$.

For completeness, the stopped identity supplied by $G$, Lemma 7.1, is the identity (6.6) with this $W_i$ and its actual hitting function $h$:

$$
\mathbb E_i h(Y_{N\wedge m})-\nu_i h
=\mathbb E_i\sum_{r=0}^{(N\wedge m)-1}[(U_i-W_i)h](Y_r).
\tag{11.5}
$$

The target's finite mean gives $\mathbb E_iN<\infty$, which justifies the supplier's bounded-convergence and dominated-convergence limits. The opponent's actual termination gives $p_j=\nu_jh_j$. No termination from arbitrary abstract states of $W_i$ or $U_j$ is needed. The same supplier gives $N\le Q_T\le T$, and $G$, Lemma 7.2, is exactly the predictable actual-tick payment (6.9), including the separate pre-first-tick hazard. Its independent proof coins are used for payment, not as an accessible tape or as the filtration for the live-chain identity (11.5).

It follows by direct application of $G$, Theorem 8.1, that for every finite $M\ge2$, every interior $q$, every finite integer $L\ge1$, every $\mathcal A\in\mathfrak A_M(q,\alpha)$ and each $i$ separately,

$$
\begin{aligned}
b&\le r_H(q)+\chi^*_{M,L}
+B(1-q)[\pi_0(q,L)+\pi_1(q,L)]\mathbb E_{i,q}^{\mathcal A}T,\\
b&=1-2\alpha>0,
\qquad
\chi^*_{M,L}=\frac{\gamma_L^{M-2}-1}{\gamma_L^{M-2}+1}.
\end{aligned}
\tag{11.6}
$$

This also permits replacing the coarse loss in (7.1) by $\gamma_L^{2(M-2)}-1$: for $v=\gamma_L^{M-2}\ge1$, $(v-1)/(v+1)\le v^2-1$, including $v=1$. Either loss therefore gives the corresponding positive-part inequality (7.2), whose denominator is positive since $0<\pi_i<1$. Applying (11.4) for the other target changes only the analytical $W_i$, not the actual machine. The conclusion bounds each paid mean, rather than their sum.

The common endpoint is the one in $G$, Theorem 9.1. Choose a source-only $s_H>0$ so that both inequalities (7.6) hold, and define

$$
\begin{aligned}
s_*&=\min\left\{s_H,1,\frac{5b}{8\delta}\right\},
&L_M&=\max\left\{1,\left\lceil\frac{2\delta(M-2)}b\right\rceil\right\},\\
S_L&=\sum_{k=1}^Lk^9,
&c_0&=\frac{b\,9!}{8B^2}.
\end{aligned}
\tag{11.7}
$$

The supplier's moment premise is the same (2.8), so its selection of $s_H$ is source-only. Its explicit estimates (9.6)–(9.10) read here as

$$
\chi^*_{M,L_M}\le b/4,
\qquad r_H(e^{-s})\le b/4,
\qquad \pi_0(e^{-s},L)+\pi_1(e^{-s},L)
\le\frac{4BS_L}{9!}s^{10},
\qquad L_M\le1+\frac{2\delta(M-2)}b.
\tag{11.8}
$$

The short-mass estimate holds for every finite $L\ge1$ on the same $0<s<s_*$, even when its right side exceeds one. There is no fixed-$L$ asymptotic or restriction on $sL_M$. With $1-e^{-s}\le s$, the exact conclusion of that theorem is

$$
\begin{gathered}
\forall M\in\mathbb Z,\ M\ge2\quad
\forall s\in(0,s_*)\quad
\forall\mathcal A\in\mathfrak A_M(e^{-s},\alpha)\quad
\forall i\in\{0,1\}:\\
\mathbb E_{i,e^{-s}}^{\mathcal A}T
\ge\frac{c_0}{S_{L_M}}s^{-11}
\ge\frac{c_0s^{-11}}{[1+(2\delta/b)(M-2)]^{10}}.
\end{gathered}
\tag{11.9}
$$

In particular (11.9) implies the weaker denominator $[1+(16\delta/b)(M-2)]^{10}$. The same $s_*$ serves every finite varying $M=M(s)$ and every retuned observer. This simultaneous result and all its constants are credited to $G$, not obtained by exchanging a fixed-$M$ limit with an observer-dependent limit.

## 12. Complete configurations and fixed-width binary memory

**Definition 12.1 (Actual configurations and complete binary width).** For a deployed observer let $m(s)$ be the cardinality of the union of its reachable persistent configurations, over all legal finite source histories, all possible retained random outcomes when used, and both source labels at the selected common $q=e^{-s}$. Include initialization, read-ready, source-disabled intermediate and terminal configurations, with every mutable control mode, head, selector, flag, register, input latch and emitted label. A Cartesian domain containing these configurations is an upper bound for $m(s)$, rather than its actual count. When intermediate computation is used, it must terminate before its next read or stop, use no other source access and retain no information outside these coordinates. Composing such computations into the read-ready normal form preserves $(T,D)$ and uses at most $m(s)$ configurations.

A complete fixed-width binary representation of width $K(s)$ is an injective encoding of those complete configurations into $\{0,1\}^{K(s)}$. Its width is an integer fixed for the deployed design, uniformly over histories, including transient arithmetic and initialization. Unused bit strings are allowed. Thus $m(s)\le2^{K(s)}$. Counting only a statistic at renewal epochs, counting only named registers, or bounding an expected or typical number of bits does not establish this condition. Immutable source-independent design data can remain separate, but every mutable address, copied constant and control position used with it is counted.

**Theorem 12.2 (Complete-bit necessity under a cubic mean).** Fix the source premises of Section 2 and $0<\alpha<1/2$. Suppose that for every sufficiently small $s>0$ a deployed observer as in Definition 12.1 belongs, after the same-budget read-ready reduction, to $\mathfrak A_{m(s)}(e^{-s},\alpha)$, with $m(s)<\infty$. Suppose for one fixed target $i_\star$ there is a constant $0<C_T<\infty$, independent of $s$, such that

$$
\mathbb E_{i_\star,e^{-s}}T\le C_Ts^{-3}.
\tag{12.1}
$$

Keep both selected risks, both almost-sure stops and both separate finite paid means at every selected parameter. Put

$$
A_T=\left(\frac{9!b^{11}}{8B^2C_T}\right)^{1/10},
\qquad b=1-2\alpha.
\tag{12.2}
$$

For all sufficiently small $s$, the existing configuration consequence of $G$, Theorem 10.1, applied to the actual count is

$$
m(s)\ge2+\frac{A_Ts^{-4/5}-b}{2\delta}.
\tag{12.3}
$$

Every complete fixed-width binary representation then satisfies

$$
K(s)\ge\frac45\log_2\frac1s+\log_2\frac{A_T}{4\delta}
=\frac45\log_2\frac1s-O_{H_c,\alpha,C_T}(1).
\tag{12.4}
$$

Proof. The count $m(s)$, rather than an arbitrarily padded budget, is a permissible choice of the supplier's $M(s)$: it contains both labels and every read-ready configuration of the reduction. All its remaining hypotheses are exactly those stated above. Thus (12.3) is the direct credited application, requiring no cubic benchmark supplier. Restrict further to $A_Ts^{-4/5}\ge2b$. For instance, intersect the neighborhood where (12.1) holds with $0<s<\min\{s_*,(A_T/(2b))^{5/4}\}$. Then (12.3) gives

$$
m(s)\ge2+\frac{A_T}{4\delta}s^{-4/5}
\ge\frac{A_T}{4\delta}s^{-4/5}.
\tag{12.5}
$$

Injectivity of the binary representation gives $K(s)\ge\log_2m(s)$. Taking base-two logarithms in (12.5) proves (12.4). Its constant is uniform over the observers with this $C_T$, and depends on neither their descriptions nor their positive exit probabilities. Only one target needs the cubic upper bound; the opposing risk, termination and finite mean remain hypotheses. If both targets have uniform cubic bounds, either gives this conclusion with its own constant. $\square$

The configuration implication (12.3) belongs to $G$. The additional assertion (12.4) uses the complete encoding hypothesis and is a source-relative consequence, not a sharp memory coefficient. In particular a growing allowed budget alone does not prove that an implementation uses many configurations: the application above deliberately uses its actual complete count. Nor do finitely many unbounded integer registers supply a finite width $K(s)$.

## 13. Comparable rational bands and the endpoint scale

**Proposition 13.1 (Uniform band correspondence).** Let $0<\varepsilon<1/4$ be rational, $I_\varepsilon=[1-2\varepsilon,1-\varepsilon]$, and $q\in I_\varepsilon$. With $x=1-q$ and $s=-\log q$,

$$
\varepsilon\le x\le2\varepsilon,
\qquad x\le s\le\frac{x}{1-x}\le2x,
\qquad \varepsilon\le s\le4\varepsilon.
\tag{13.1}
$$

Consequently, uniformly on the whole band,

$$
s^{-3}\le\varepsilon^{-3}\le64s^{-3},
\qquad
\log_2(1/s)\le\log_2(1/\varepsilon)
\le\log_2(1/s)+2.
\tag{13.2}
$$

Two such bands containing the same $q$ have widths within a factor two. Every sufficiently small $x>0$ admits a dyadic rational width with $x/2<\varepsilon\le x$, so these supplied bands cover the endpoint as an existence family.

Proof. The first inequalities are the definition of the band. Since $x\le2\varepsilon<1/2$,

$$
s=\int_0^x\frac{du}{1-u},
\qquad x\le s\le\frac{x}{1-x}\le2x.
\tag{13.3}
$$

These prove (13.1), and reciprocation and logarithms give (13.2). Any width whose band contains $q$ lies in $[x/2,x]$, proving the factor-two comparison. For coverage choose an integer $j$ with $2^{-j}\le x<2^{-j+1}$ and take $\varepsilon=2^{-j}$. Such an integer exists by the Archimedean property; the chosen width is rational and has the asserted inequalities. $\square$

The logarithm and this dyadic selection are mathematical scale correspondences. They are not instructions to a running observer. A band and risk fraction are supplied before deployment; an existence choice of a comparable band at a given $q$ supplies no mechanism for discovering an unknown $q$. One compiled observer below serves every $q$ in its supplied band and receives neither $q$ nor $s$ as an online input. Likewise this family does not assert the existence of a single finite-width controller with cubic means over all bands simultaneously.

## 14. Inclusion of the supplied controller and logarithmic order

**Definition 14.1 (Matched band contract and upper suppliers).** Fix the same $H_c$ and $\alpha$, and choose once a rational $\rho\in[\alpha/2,\alpha]$ as in $C$, Definition 28.1. The matched contract uses a supplied rational band $I_\varepsilon$, one source-blind design on that band, the stationary consecutive-read laws of Section 2, the two separate risk bounds at level $\alpha$, internally emitted labels, and complete fixed-width mutable configurations as in Definition 12.1. All source-disabled computations terminate. A uniform cubic paid-mean promise under a selected target means an upper constant independent of the band and of the parameter within it; both targets still have almost-sure stopping and finite means. No bound on compilation or immutable-description resources is part of this mutable-bit lower condition.

The supplied deterministic controller is exactly the one in $C$, Definitions 28.1–28.2, Lemma 29.5, Theorem 29.6, Proposition 29.7 and Corollary 30.1, with no reconstruction here. Their paid count $L_\varepsilon$ is $T$ here. Their polynomial $H_c$, source (23.4)–(23.6), initial wait, decision labels and target risks are those in Sections 2–3 here. Their $b=h+1$ is a score threshold, distinct from our $b=1-2\alpha$; their coefficient-size integer $B$ is distinct from our envelope $B=1+\delta$. Their $\delta_9$ remains their pair-score envelope constant and is not identified with our $\delta$. Their fixed rational $\rho$ is an immutable risk input, not a label, observed parameter or random choice. With the controlled surrogate, their upper constants depend only on the fixed source and target risk.

Here is the complete resource correspondence needed for this application. Symbols $W,w,a$ in this table are exactly $C$, (28.1) and (29.1).

| Coordinate | Credited bound and role |
| --- | --- |
| Paid source reads | $C$, Theorem 28.4 and Corollary 30.1: $T=L_\varepsilon\le W=O_{H_c,\alpha}(\varepsilon^{-3})$, with $\mathbb E_{i,q}T=\Theta_{H_c,\alpha}(\varepsilon^{-3})$ separately for $i=0,1$ and every $q\in I_\varepsilon$. Every initial, partial and terminal read is included. |
| Complete mutable binary width | $C$, Theorem 29.6: $K_\varepsilon=256w+32a+97$ bits, including the 256 words, 32 heads and selectors, 64 flags, input and output latches, 30 control bits, all static call-site modes, initialization, temporary arithmetic and halts. Its configuration domain has at most $2^{K_\varepsilon}$ elements; this is not an assertion that all encodings are reachable. |
| Source-disabled local computation | $C$, Lemmas 29.3 and 29.5: the bounded local computations terminate on every legal history, including a last read closing a pair and a stream with no first tick. The internal online bit work is separately bounded by $2^{40}Ww^3$. |
| Source-independent initialization | $C$, Proposition 29.7: initialization uses the same counted bank, heads and control, with separate bit-work allowance $2^{34}w^3$. Every mutable descriptor address is counted. |
| Deployed immutable description | $C$, Proposition 29.7, (29.16): the fixed graph and 96 compiled $w$-bit words have length at most $2^{48}+96w$. Copied words reside in the counted mutable bank. |
| Fixed-model preparation and rational compilation | $C$, Proposition 29.7, (29.15), applies owner Proposition 22.6 to the supplied rational band and risk descriptions. Its workspace and work depend on their full input length and remain separately charged, even for padded input descriptions. These compiler coordinates are not included in a claim about online mutable-bit optimality. |

The controller has no fresh or retained random inputs, no unpaid source observations and no second source. Its read counter is in the bank, rather than an external clock. Its arithmetic inspects no additional source sample, and the ordinary threshold decision at the last read precedes the prescribed timeout. The statements above retain the supplier's exact refinement and width premises, rather than inferring correctness from a Cartesian state count alone.

**Theorem 14.2 (Conditional logarithmic complete-bit order on matched bands).** Conditional on the lower suppliers identified in Section 11 and the upper suppliers of Definition 14.1, the supplied deterministic controller family realizes uniform cubic paid means with $O_{H_c,\alpha}(1+\log(1/\varepsilon))$ complete mutable bits. Every family in the matched contract with a uniform cubic mean upper bound under either fixed target requires

$$
K_\varepsilon\ge\frac45\log_2(1/\varepsilon)-O(1).
\tag{14.1}
$$

Thus logarithmic mutable-bit order is necessary and attained within this contract. The upper controller is source-blind throughout each band and is an element of the known-common-$q$ lower class at every selected $q$ in that band. This is an order comparison, with no assertion that the necessary configuration exponent $4/5$ or the displayed bit coefficient is attained.

Proof. Fix a sufficiently small supplied rational $\varepsilon$. The supplier initializes from immutable band and risk data without reading the source. After each read it performs only the source-disabled finite computations covered by $C$, Lemma 29.5, then either emits its own label or reaches a next read-ready state. For this fixed width and descriptor, composing those deterministic finite paths gives deterministic bit kernels $A,C$ and a common initial row $\eta$. All mutable intermediate modes already belong to the counted configuration domain. No step of this composition introduces a stored elapsed-work index, another read, or an external program counter. Identifying terminal states with the same emitted label can only reduce the state count. This is the same-budget normal-form reduction of Lemma 3.2, with internal source-disabled computations composed as in Definition 12.1.

Let $m_\varepsilon$ be the actual complete configuration count of this controller. It is finite and at most $2^{K_\varepsilon}$. At each selected $q\in I_\varepsilon$, both separate band risk bounds from $C$, Theorem 28.4, imply (3.1) for that same $q$. The finite cap and terminating internal work give both almost-sure stops and both finite paid means. The source law and all access restrictions agree by Definition 14.1. Therefore the controller, with its read-ready reduction, belongs to $\mathfrak A_{m_\varepsilon}(q,\alpha)$. The lower class allows immutable knowledge of $q$; a design which ignores it is included. Restricting the supplier's two nuisance parameters to the same chosen $q$ loses none of these conditions.

The following necessity argument applies equally to any family in the matched contract. If its target mean is at most $C_{\rm band}\varepsilon^{-3}$ uniformly on the band, (13.2) bounds it by $C_Ts^{-3}$ with $C_T=64C_{\rm band}$, uniformly before selecting $q$ or the band. If $4\varepsilon<s_*$, every point of the band lies in the common lower neighborhood. Apply (11.9) pointwise with the actual complete count as budget and this target upper bound. The same positive-root rearrangement supplied by $G$, Theorem 10.1, yields (12.3), with $A_T$ from (12.2), for each selected pair $(\varepsilon,q)$. This application uses a simultaneous inequality, so it does not require the family to select a unique observer as a function of $s$ across overlapping bands. For sufficiently small $\varepsilon$, $s\le4\varepsilon$ makes $A_Ts^{-4/5}\ge2b$ throughout the band. Hence

$$
m_\varepsilon\ge\frac{A_T}{4\delta}s^{-4/5}
\ge\frac{A_T}{4\delta}\,4^{-4/5}\varepsilon^{-4/5},
\qquad
K_\varepsilon\ge\frac45\log_2(1/\varepsilon)
+\log_2\frac{A_T}{4\delta}-\frac85.
\tag{14.2}
$$

This is (14.1); both means are used for compliance, while only the selected mean needs the uniform cubic upper constant. An upper constant depending without bound on the band would not suffice.

For attainment, the single supplied controller at each band has the uniform cubic upper constant just used, and its separate mean lower constants are exactly the credited owner Corollary 22.11 through $C$, Theorem 28.4. No new prefix-information bound is asserted. For its complete width, $C$, (29.1) and Theorem 29.6, give, at fixed $H_c,\alpha$ and controlled $\rho$,

$$
w=O(1+\log(W+2)),\qquad
 a=O(1+\log(w+1)),\qquad
K_\varepsilon=256w+32a+97
=O_{H_c,\alpha}(1+\log(1/\varepsilon)).
\tag{14.3}
$$

Here $W=O_{H_c,\alpha}(\varepsilon^{-3})$ and all small-band constants are uniform. The complete width includes transient and initialization configurations, so (14.3) meets precisely the encoding hypothesis used in (14.2). Proposition 13.1 converts these logarithmic orders to $\log(1/s)$ on comparable bands, with only a bounded additive difference. Its dyadic coverage is an offline existence statement; the compiler still receives only the rational band and risk, and the deployed controller never queries a real parameter. These facts prove the stated order comparison. $\square$

The mutable-bit lower bound and supplied upper configuration estimate leave a genuine distinction: necessity is $m_\varepsilon=\Omega(\varepsilon^{-4/5})$, whereas the supplied complete domain is only bounded above by $2^{K_\varepsilon}$ with $K_\varepsilon=O(\log(1/\varepsilon))$. The unspecified upper polynomial exponent need not be $4/5$. Taking logarithms permits an order match without matching either that exponent or its coefficient. Likewise there are no matching lower bounds here for compiler workspace, immutable description, initialization or internal bit work. Allowing arbitrary independent $\rho\downarrow0$, changing $H_c$, or changing the stationary start does not preserve the uniform constants asserted above.

## 15. Classical attribution and the remaining resource questions

**Definition 15.1 (Attribution and conditional mathematical scope).** The directly applicable classical fixed-root identities are Jim Pitman and Wenpin Tang, “Tree formulas, mean first passage times and Kemeny’s constant of a Markov chain,” *Bernoulli* 24(3), 1942–1972, DOI [10.3150/16-BEJ916](https://doi.org/10.3150/16-BEJ916), [arXiv:1603.09017](https://arxiv.org/abs/1603.09017): Theorem 1.2, especially (1.4), is the forest denominator with the root set fixed exactly; the harmonic tree formula (1.9) is the probability of first entering that root set at a specified root, when its forest weight is positive. The correspondence is $S=\mathcal S$, $R=\partial$, $i=x$, $j=d_1$. Positivity in the present reducible setting is supplied by $G$, Lemma 4.3. With the boundary made absorbing, entering $\partial$ at $d_1$ is exactly ever hitting $d_1$. Their roots may include isolated vertices, as needed for additional zero-target states. The row-transition convention directs nonroot edges toward their roots. This specifies the applicable primary-source formulas without substituting a varying-root $I+L$ forest sum or an irreducible stationary tree formula.

Seth Chaiken, “A Combinatorial Proof of the All Minors Matrix Tree Theorem,” *SIAM Journal on Algebraic Discrete Methods* 3(3), 319–329, DOI [10.1137/0603033](https://doi.org/10.1137/0603033), is classical all-minors background. The exact original full-text scope is not independently certified here and is not a premise of any inference in this append. The applicable fixed-root formulas above and the complete proof already supplied in $G$, Sections 4–5, carry that role. No additional literature survey or priority conclusion is implicit in these attributions.

The source-relative additions here are the complete encoding consequence of Theorem 12.2 and the parameter-and-resource bridge proving Theorem 14.2. The forest argument, its complementary-sum improvement, the finite-$q$ inequality, the simultaneous budget bound and the actual configuration lower implication retain their ownership in $G$. The rounded-product controller and its complete bounded bit-transition realization retain their ownership in $C$. These uses are `repo-derived` ordinary-paper consequences of credited mathematical suppliers, with the classical forest identities `literature-attested` at the exact scope just specified. The fixed integer envelope and moment premises remain those of Section 2. The upper also retains $C$, Definition 30.2's conditional pair-score, drift, rational-certificate, stopping/payment and preprocessing suppliers; the claimed cubic mean lower order retains its owner prefix-information supplier. The configuration and binary lower implications need no cubic benchmark premise beyond the hypothesized uniform cubic upper mean.

For Open question 10.2, the sufficient exponential comparison has the supplied replacement (11.3), with exponent $2n\le2(M-2)$ and the stronger complementary-sum additive bound. For the growing-budget part of Open question 10.3, the supplied simultaneous inequality is (11.9) and actual configuration necessity is (12.3). Under the complete binary encoding hypothesis, Theorem 12.2 adds necessity (12.4). Conditional on the upper suppliers, Theorem 14.2 and Proposition 13.1 also give finite-width cubic-mean sufficiency and the logarithmic mutable-bit order comparison on supplied bands. Each conclusion retains the same fixed $H_c$, fixed risk, stationary start and consecutive paid-read convention.

The optimal hitting-comparison dependence in the constrained stochastic class, the optimal complete-configuration growth exponent for cubic means, a sharp binary coefficient, the exact performance tradeoff at intermediate growing budgets, and the minimum nonempty budget remain unresolved by these results. In particular $2<M<S_\alpha$ is still unclassified, and no observer attaining configuration order $s^{-4/5}$ is supplied. There is no exact optimizer or matching theorem for all resource coordinates. The conclusions concern abstract complete mutable configurations and binary encodings, not physical storage, elapsed time, energy, producer dimension or neural hidden dimension. They have no varying-$H_c$, residual-uniform, hidden-state-access, reset-access, worldwide-priority or Lean/kernel-verification conclusion.

## 追加锚（本行以下为增补区）
