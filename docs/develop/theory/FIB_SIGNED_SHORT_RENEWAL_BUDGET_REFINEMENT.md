# Signed-short refinement of the renewal paid-mean budget bound

## 1. Scope, ownership and status

For one fixed pair of stationary binary renewal laws, this companion refines a paid-mean lower bound for observers with finitely many complete persistent configurations. The common parameter $q$ is known, and the observer may be redesigned arbitrarily at each $q$. Both selected testing risks, both almost-sure stops and both finite pointwise paid means remain required. Writing $q=e^{-s}$, the refinement gives one lower inequality simultaneously for every finite budget $M$ on one source/risk-only endpoint neighborhood. An eventual bound $C_Ts^{-3}$ under one fixed target, with one fixed constant $C_T$, then requires $M(s)=\Omega(s^{-8/9})$.

The mathematical contribution belongs to the supplied **signed-short proposal**, `refinement-proposal.json`, titled “Signed short-component clipping yields necessary Omega(s^(-8/9)) complete-state growth for an eventual cubic paid mean,” results F1–F4 and G1–G3. Its supplied **independent check**, `refinement-check.json`, titled “The signed short-component refinement passes this independent handwritten check under the unchanged contract,” checks those deductions. This manuscript supplies their standalone ordinary exposition and complete proofs relative to the explicitly credited premises below. The proposal's independent handwritten check concerns that proposal; it is not approval of the exact text of this manuscript.

Three supplied mathematical sources fix the premises and prior results. The **lower source**, `lower-source.md`, is *Growing state budgets in the renewal paid-mean tradeoff*. Its Sections 4–5 supply the positive-forest hitting comparison, Sections 6–7 supply the initial, clipping, epoch and payment interfaces, and Theorems 9.1 and 10.1 supply the prior simultaneous lower bound and necessary exponent $4/5$. The **uniform source**, `uniform-source.md`, is *Retuned bounded-memory uniform renewal converse*. Its Definition 3.1 and Lemma 3.2 supply the precise known-common-$q$ class and same-budget normal form; its Sections 5–7 supply the uniform initial and actual-stopping interface and fixed-budget eleventh-power converse. The **fixed-observer source**, `fixed-observer-source.md`, is *Real renewal instruments and detector rank: finite observer memory*, Definitions 23.1–23.2 through Definition 27.4. It supplies the exact shapes, envelope, stationary law, moment estimates and original actual-read conventions. Their parameter correspondence is stated explicitly in Sections 2–4.

The separate supplied `upper-proposal.json` and `upper-check.json` concern a geometric-mark and lazy-walk sufficient construction with order $s^{-1}$ complete configurations and cubic means. They provide comparison context only. Neither their proof nor a final upper manuscript is an input to the lower deduction here. The necessary exponent $8/9$ and supplied sufficient exponent $1$ remain nonmatching.

All mathematical claims here are ordinary handwritten deductions conditional on fallible supplied mathematical premises. In particular the all-integer envelope and source moments retain their supplier status. There is no Lean kernel verification, final-source approval or external-priority certification. Total-variation contraction, directed forests, summation by parts, harmonic first-step equations and stopped telescoping are classical methods; their use is not claimed as invention.

## 2. The fixed shapes and stationary paid history

**Definition 2.1 (Exact rational-center source).** Fix the polynomial

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

Throughout put

$$
\begin{gathered}
H=H_c,\qquad F_0(x)=x^9,\qquad F_1(x)=H(x),\\
\delta=\frac{2749658638697}{10^{24}}>0,\qquad
B=1+\delta,\qquad
a=\frac{43377331415040}{35\cdot10^{24}}>0.
\end{gathered}
\tag{2.2}
$$

The supplied all-integer envelope is exactly

$$
\begin{gathered}
k^9\le F_i(k)\le Bk^9\quad(i=0,1),\\
1\le\frac{H(k)}{k^9}\le1+\frac\delta k
\quad\text{for every integer }k\ge1.
\end{gathered}
\tag{2.3}
$$

These are fixed-observer-source Definition 23.1, equations (23.1)–(23.3), and lower-source and uniform-source Definition 2.1. The fixed-observer source attributes the envelope to its owning source's Theorem 15.5 and the rational center to that source's Definition 12.1 and equation (19.7). Those nested proofs are supplied premises, not independently established here. The shape is the displayed rational-center polynomial, not a limiting residual-zero vector. Neither its coefficients nor $\delta,B,a$ vary with the observer or with $q$.

**Definition 2.2 (The actual stationary history).** For $i\in\{0,1\}$ and $q\in(0,1)$ define

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

All indices in these sums are integers. At each interior $q$ the polynomial-geometric sums are finite, $Z_i>0$, and every $f_{i,q}(k)$ for $k\ge1$ is positive. In particular $S_{i,q}(0)=S_{i,q}(1)=1$.

The law $\mathsf P_{i,q}$ first draws a tick time $\tau$ with

$$
\mathsf P_{i,q}(\tau=b)=\frac{S_{i,q}(b)}{\mu_i(q)}
\quad(b=0,1,\ldots).
\tag{2.5}
$$

It places zeros before $\tau$ and a one at $\tau$. Independently of $\tau$, subsequent zero counts $K_1,K_2,\ldots$ are iid with law $f_{i,q}$. The further tick times are

$$
\tau_0=\tau,\qquad
\tau_n=\tau+\sum_{r=1}^n(K_r+1)\quad(n\ge1),
\tag{2.6}
$$

and every other bit of $X_0,X_1,\ldots$ is zero. Thus $K_r$ counts zeros; $K_r+1$ is a full post-tick interval through its next tick. The first wait is survival-normalized, not a draw from $f_{i,q}$.

The supplied stationary normalization and mean identities are

$$
\sum_{b\ge0}S_{i,q}(b)=\mu_i(q),\qquad
\mathbb E_{i,q}\tau=\beta_i(q).
\tag{2.7}
$$

Their parameter correspondence is exact: a fixed $k$ contributes to the survival sum for $b=0,\ldots,k$, with total multiplicity $k+1$, and contributes total first-moment weight $k(k+1)/2$. These identities are part of fixed-observer-source Definition 23.2, equations (23.4)–(23.6), and Definition 2.2 of the lower and uniform sources. They specify the history without giving its unobserved age to an observer.

**Assumption 2.3 (Supplied moment estimates).** With $s=-\log q\downarrow0$, retain

$$
Z_i(e^{-s})=9!s^{-10}(1+O_H(s)),\qquad
\mu_i(e^{-s})=\frac{10}{s}+O_H(1),\qquad
\beta_i(e^{-s})=\frac{11}{2s}+O_H(1).
\tag{2.8}
$$

These are fixed-observer-source equation (23.7) and equation (2.8) of both companions, credited there to polynomial-geometric moment results. They are unchanged source premises. Only the lower consequences for $Z_0$ and $\mu_0$ will select the endpoint neighborhood in Section 8. No finite sampling is substituted for (2.3) or (2.8).

## 3. Known common parameter and complete configurations

**Definition 3.1 (The pointwise compliant observer class).** Fix a finite integer $M\ge2$, a risk allowance $0<\alpha<1/2$ and a known common $q\in(0,1)$. The observer may depend arbitrarily on $(q,H,\alpha,M)$, including in its state set, transition probabilities and source-independent initialization. Its design and initialization are the same under both true labels. The true label and source-dependent advice are unavailable.

At most $M$ complete persistent configurations are permitted. The count includes initialization configurations, every active configuration, both internally emitted decision labels, every control phase and register, all retained randomness and every stored seed. An update-selection counter is persistent information and is counted. Fresh independent random choices are allowed; any retained consequence of such a choice belongs to the configuration set. Known $q$ and the fixed transition description are immutable design information. Their real precision is permitted and unpriced by this abstract contract; it is not an extra mutable channel. No continuity across $q$ or lower bound on positive transition probabilities is required.

At each action the observer reads the next actual bit or stops and emits $D\in\{0,1\}$. A choice uses its current configuration, the bit just read when applicable and fresh randomness independent of the source and previous fresh randomness. Source access is to the one uninterrupted consecutive history of Definition 2.2. There is no external time, age, clock, action count, program counter, archive, skipped bit, free gap, reset, second source, hidden-state observation, parameter response, probability response or source oracle. The cost tally is not an input. The emitted label is the decision; there is no decoder using stop time or read length.

Reading $X_0,\ldots,X_{T-1}$ costs $T$. Every read zero and one, the initial stationary wait and any terminal partial gap are paid. Initial stopping costs zero. Write $\mathfrak A_M(q,\alpha)$ for the observers satisfying all six conditions

$$
\begin{gathered}
\mathsf P_{0,q}(D=1)\le\alpha,\qquad
\mathsf P_{1,q}(D=0)\le\alpha,\\
\mathsf P_{i,q}(T<\infty)=1,\qquad
\mathbb E_{i,q}T<\infty\quad(i=0,1).
\end{gathered}
\tag{3.1}
$$

This is uniform-source Definition 3.1, also lower-source Definition 3.1. The risks concern the two selected laws at a known common $q$. Correctness over separate unknown nuisance families is a stronger, different promise. The two stops and two means are pointwise; no uniform mean on the whole parameter interval is assumed.

**Supplied interface 3.2 (Same-budget normal form).** Uniform-source Lemma 3.2 and lower-source Lemma 3.2 apply fixed-observer-source Lemma 23.4 at the selected $q$. They give a row distribution $\eta$ and row-stochastic bit matrices $A,C$ on one set $\mathcal S$, $|\mathcal S|\le M$. There are distinct labels $d_0,d_1$, both absorbing under both matrices, and every other configuration is ready for its next paid read. The reduction preserves the joint law of $(T,D)$ and uses the same $\eta,A,C$ under the two labels. Composition of read/stop choices and merging terminal configurations do not add persistent states.

For analysis put $\mathcal K_k=A^kC$ and, suppressing $q$ in weights,

$$
U_i=\sum_{k\ge1}f_i(k)\mathcal K_k,\qquad
\nu_i=\sum_{b\ge0}\frac{S_i(b)}{\mu_i}\eta A^bC.
\tag{3.2}
$$

These are respectively the completed-gap kernel and stationary first-tick row of the same actual machine. Every $\mathcal K_k$ and $U_i$ is stochastic and fixes both labels. Holding an already emitted label fixed on an unused continuation defines these quantities without changing actual payment or providing any further observation to the observer. They are not operational gap queries.

## 4. Supplied forest, initial and actual-payment interfaces

The following premises are reused with their original mathematical ownership. The new signed-short proofs begin in Section 5. Stating these interfaces in full identifies what those proofs consume; it does not claim a new proof of the supplied forest or payment results.

**Supplied interface 4.1 (Positive-forest hitting comparison).** Lower-source Theorem 5.1, proved there from the positive directed forests in Section 4 and the marked and complementary forest sums in Section 5, has this form. Let $P,Q$ be stochastic on the same $\mathcal S$ with the two common absorbing labels, and suppose $\gamma\ge1$ satisfies

$$
\gamma^{-1}P(x,y)\le Q(x,y)\le\gamma P(x,y)
\quad(x,y\in\mathcal S).
\tag{4.1}
$$

They have the same positive-edge support. Let $\mathcal Z$ be its vertices with no positive directed path to $d_1$, and let

$$
V=\mathcal S\setminus(\mathcal Z\cup\{d_1\}),\qquad
n=|V|\le |\mathcal S|-2\le M-2.
\tag{4.2}
$$

For the actual probabilities $h_P,h_Q$ of ever hitting $d_1$, including time zero,

$$
\gamma^{-2n}h_P(x)\le h_Q(x)\le\gamma^{2n}h_P(x),\qquad
|h_P(x)-h_Q(x)|\le\frac{\gamma^n-1}{\gamma^n+1}.
\tag{4.3}
$$

Here $d_0\in\mathcal Z$ supplies the second excluded boundary label in (4.2). The hitting functions are zero on $\mathcal Z$ and one at $d_1$. Closed non-target classes are included in $\mathcal Z$; making their rows identities analytically preserves the hitting values. The forest proof uses $n$ edges per forest, and the common positive marked and complementary sums give (4.3). It requires no global absorption, irreducibility, aperiodicity, spectral gap or lower bound on positive exits. Zero edges, self-loops, hitting values zero and one and an empty interior $n=0$ are included. We use this supplied theorem, rather than the coarser elimination exponent of uniform-source Lemma 4.1.

**Supplied interface 4.2 (Actual stationary initial row).** Define

$$
R_r(q)=\sum_{k\ge1}k^rq^k,\qquad
r_H(q)=\delta\frac{R_9(q)+R_8(q)}{R_{10}(q)+R_9(q)}.
\tag{4.4}
$$

For the actual $\nu_i$ in (3.2), lower-source Lemma 6.1 and uniform-source Lemma 5.1 give

$$
\|\nu_0-\nu_1\|_{\rm TV}\le r_H(q)\le\frac{2\delta}{\mu_0(q)},
\qquad
\|u-v\|_{\rm TV}=\frac12\sum_x|u(x)-v(x)|.
\tag{4.5}
$$

The supplier compares the first-wait weights $g_i(b)=\sum_{k\ge\max(1,b)}F_i(k)q^k$, whose normalizers are $Z_i\mu_i$. Its excess normalizer is bounded by $\delta(R_9+R_8)$, with $Z_0\mu_0=R_{10}+R_9$. The common map $b\mapsto\eta A^bC$ then contracts variation. This uses the actual stationary first wait and common initialization, including initial stopping, even for arbitrary retuning. It does not import the machine-dependent $O(s^2)$ initial estimate of fixed-observer-source Lemma 24.2.

**Supplied interface 4.3 (Actual live epochs).** Follow the full history while holding an actually emitted label fixed thereafter. If $Y_n$ is the state just after the tick at $\tau_n$, define

$$
N=\inf\{n\ge0:Y_n\in\{d_0,d_1\}\},\qquad
Q_T=\sum_{t\ge0}\mathbf1_{\{T>t\}}X_t.
\tag{4.6}
$$

Under the actual target $i$, $Y_0$ has law $\nu_i$ and the epoch kernel is $U_i$. For a compliant observer the supplied identities and inequalities are

$$
N<\infty\ \text{almost surely},\qquad Y_N=d_D,\qquad
N\le Q_T\le T,\qquad \mathbb E_iN<\infty.
\tag{4.7}
$$

These are fixed-observer-source Lemma 25.1, lower-source Lemma 7.1 and uniform-source Lemma 6.1. If stopping is before or at the first tick, $N=0$. Otherwise each live $Y_0,\ldots,Y_{N-1}$ follows an actually read tick and commits to a next read: the $N$ live epochs are charged to those distinct paid ticks. If a zero run contains the actual stop, the next analytical tick only records the frozen label; it is not added to $Q_T$. Thus (4.7) does not charge an unread closing tick or assert that every undertaken epoch is completed operationally.

**Supplied interface 4.4 (Predictable actual-bit payment).** Fixed-observer-source Lemma 25.3, lower-source Lemma 7.2 and uniform-source Lemma 6.2 give

$$
\mathbb E_iQ_T\le B(1-q)\mathbb E_iT.
\tag{4.8}
$$

The source-history hazards used there are $f_i(b)/S_i(b)$ after a tick and $b\ge1$ ensuing zeros, zero just after a tick, and $S_i(b)/\sum_{v\ge b}S_i(v)$ before the first tick. The envelope bounds each by $B(1-q)$, including the stationary first-wait hazard. With independent proof coins exposed for predictability, $\{T>t\}$ is known before $X_t$, and the supplier sums $\mathbf1_{\{T>t\}}X_t$ over precisely the undertaken reads. Those coins are not retained observer information. That enlarged payment filtration is not used to condition epoch drifts on future update coins.

Consequently (4.7)–(4.8) give, separately under each actual source,

$$
\mathbb E_iN\le B(1-q)\mathbb E_iT.
\tag{4.9}
$$

This is the only conversion from epochs to reads used below. It neither multiplies a random number of interrupted epochs by a full mean gap nor assumes independence between a terminal decision and its current gap duration. The initial interval and terminal partial interval remain paid through the actual $T$.

## 5. Lawful clipping and the exact signed short discrepancy

**Definition 5.1 (Target-specific analytical comparison).** At any interior $q$ and finite integer $L\ge1$, put

$$
\begin{aligned}
\pi_i&=\sum_{k=1}^Lf_i(k),
&J_i^L&=\pi_i^{-1}\sum_{k=1}^Lf_i(k)\mathcal K_k,\\
V_i^L&=(1-\pi_i)^{-1}\sum_{k>L}f_i(k)\mathcal K_k,
&\gamma_L&=1+\frac\delta{L+1}.
\end{aligned}
\tag{5.1}
$$

For target $i$ and opponent $j=1-i$, define

$$
W_i=\pi_jJ_j^L+(1-\pi_j)V_i^L.
\tag{5.2}
$$

The split and the target-specific $W_i$ are the supplied lower-source Lemma 6.2 and uniform-source Lemma 5.2. The following proof retains their exact opponent comparison so that the refined additive estimate applies to the same object.

**Lemma 5.2 (Comparison to the actual opponent).** Every matrix in (5.1) is stochastic and fixes both labels. The same holds for $W_i$, and

$$
\gamma_L^{-1}U_j(x,y)\le W_i(x,y)\le\gamma_L U_j(x,y)
\quad(x,y\in\mathcal S).
\tag{5.3}
$$

Proof. Since every $f_i(k)>0$, finite $L$ gives $0<\pi_i<1$: there is positive mass both in $\{1,\ldots,L\}$ and beyond $L$. Hence $J_i^L,V_i^L$ are probability-weighted averages of stochastic matrices fixing the labels, and so is $W_i$.

For $k>L$, put $t(k)=H(k)/k^9$. By (2.3), $t(k)\in[1,\gamma_L]$. The exact ratio of the two conditional tail masses is

$$
\frac{f_1(k)/(1-\pi_1)}{f_0(k)/(1-\pi_0)}
=\frac{t(k)}{\displaystyle\sum_{\ell>L}
             \frac{f_0(\ell)}{1-\pi_0}t(\ell)}.
\tag{5.4}
$$

The denominator is an average of values in $[1,\gamma_L]$, hence lies in that interval. The ratio lies in $[\gamma_L^{-1},\gamma_L]$, as does its reciprocal. This comparison has cancelled the full $Z_i$ normalizers, rather than treated their ratio as one. Averaging the common nonnegative entries of $\mathcal K_k$ proves the same comparison between $V_0^L$ and $V_1^L$ in either direction.

Now $U_j=\pi_jJ_j^L+(1-\pi_j)V_j^L$, whereas $W_i$ has exactly the same short term $\pi_jJ_j^L$. For nonnegative numbers $c,a,b$ with $\gamma^{-1}a\le b\le\gamma a$, one has $\gamma^{-1}(c+a)\le c+b\le\gamma(c+a)$ because $\gamma^{-1}c\le c\le\gamma c$. Apply this entrywise with the common short term as $c$. This proves (5.3), including zero entries. In particular $W_i$ and the actual opponent $U_j$ have identical positive supports. $\square$

No operational source is replaced in this construction. Both the opponent's whole short term and its mixing weight remain present. There is no tail-only access, skipped paid interval or claim that $W_i$ absorbs from all states.

**Definition 5.3 (Normalized coefficients, drift and scalar variation).** Write

$$
\begin{aligned}
\Delta_H(k)&=H(k)-k^9,\qquad
G=Z_1-Z_0=\sum_{k\ge1}\Delta_H(k)q^k,\qquad
\varepsilon=\frac{G}{Z_0},\\
R_r^L(q)&=\sum_{k=1}^Lk^rq^k,\qquad
G_L=\sum_{k=1}^L\Delta_H(k)q^k,\\
w_k&=f_1(k)-f_0(k)
=\frac{[\Delta_H(k)-\varepsilon k^9]q^k}{Z_1},\\
m_L&=\sum_{k=1}^Lw_k=\pi_1-\pi_0
=\frac{G_L-\varepsilon R_9^L}{Z_1},\\
\kappa_L&=\frac12\left(\sum_{k=1}^L|w_k|+|m_L|\right).
\end{aligned}
\tag{5.5}
$$

Here $Z_0=R_9$ and $Z_1=(1+\varepsilon)Z_0$. In particular the exact, entirely source-defined coefficient is

$$
\kappa_L=
\frac{\displaystyle\sum_{k=1}^L
 |\Delta_H(k)-\varepsilon k^9|q^k
 +|G_L-\varepsilon R_9^L|}{2Z_1}.
\tag{5.6}
$$

The normalizing subtraction $\varepsilon k^9$ and the short-total drift $m_L$ are retained. Nonnegativity of $\Delta_H(k)$ does not give nonnegativity of $w_k$ or of $m_L$.

**Lemma 5.4 (Both target row bounds).** For each target $i\in\{0,1\}$, its own $W_i$ from (5.2), and every row $x$,

$$
\|U_i(x,\cdot)-W_i(x,\cdot)\|_{\rm TV}\le\kappa_L.
\tag{5.7}
$$

If

$$
P_L=\sum_{k=1}^L(w_k)_+,\qquad
N_L=\sum_{k=1}^L(-w_k)_+,\qquad (v)_+=\max\{v,0\},
\tag{5.8}
$$

then $\kappa_L=\max\{P_L,N_L\}$. It is the exact variation of a collapsed scalar signed measure, and only an upper bound for the actual output-row variation.

Proof. First,

$$
\begin{aligned}
f_1(k)-f_0(k)
&=\left(\frac{k^9+\Delta_H(k)}{Z_1}
       -\frac{k^9}{Z_0}\right)q^k\\
&=\frac{[\Delta_H(k)-\varepsilon k^9]q^k}{Z_1},
\end{aligned}
\tag{5.9}
$$

which verifies the normalization in (5.5). Summing the finite short part gives its drift formula. Subtract the two exact short/tail decompositions at each target, without separately estimating their terms:

$$
\begin{aligned}
U_1-W_1&=\sum_{k=1}^Lw_k\mathcal K_k-m_LV_1^L,\\
U_0-W_0&=-\sum_{k=1}^Lw_k\mathcal K_k+m_LV_0^L.
\end{aligned}
\tag{5.10}
$$

For example the tail coefficient in the first line is $(1-\pi_1)-(1-\pi_0)=-m_L$; in the second line it is $m_L$. Thus the tail compensation follows from the actual normalization and cannot be omitted.

On the finite symbol set $\{1,\ldots,L,*\}$ define a signed measure $\lambda$ by $\lambda(k)=w_k$ and $\lambda(*)=-m_L$. It has total mass zero. Its positive and negative masses therefore agree, and each is

$$
\frac12\sum_z|\lambda(z)|=\kappa_L.
\tag{5.11}
$$

For any function $g$ on this symbol set with $0\le g\le1$, its positive part contributes at most $\kappa_L$ and its negative part at least $-\kappa_L$. Consequently $|\sum_z\lambda(z)g(z)|\le\kappa_L$.

Fix a row $x$ and a target $i$. Map symbol $k$ to the stochastic row $\mathcal K_k(x,\cdot)$ and symbol $*$ to $V_i^L(x,\cdot)$. For a state event $E\subseteq\mathcal S$, the resulting conditional values $g(k)=\mathcal K_k(x,E)$ and $g(*)=V_i^L(x,E)$ lie in $[0,1]$. By (5.10) the target row difference on $E$ is the image of $\lambda$, or its negative. Its absolute value is at most $\kappa_L$. Taking the supremum over events proves (5.7), since a finite zero-mass row has total variation equal to that supremum. The same argument, replacing an event indicator by any state function in $[0,1]$, also bounds the difference of its two row averages by $\kappa_L$.

Finally $m_L=P_L-N_L$ and $\sum_{k\le L}|w_k|=P_L+N_L$. Hence

$$
\kappa_L=\frac{P_L+N_L+|P_L-N_L|}{2}
=\max\{P_L,N_L\}.
\tag{5.12}
$$

No sign was assumed for an individual $w_k$ or for the drift. Distinct symbols may map to the same row, so contraction can be strict, even zero. Equality with actual output-row variation is neither needed nor asserted. $\square$

## 6. Source-only bounds for every parameter and every finite cutoff

**Lemma 6.1 (The full finite-$q$ coefficient chain).** For every $q\in(0,1)$ and every finite integer $L\ge1$,

$$
\begin{aligned}
\kappa_L
&\le\frac{\max\{G_L,\varepsilon R_9^L\}}{Z_1}\\
&\le\frac\delta{Z_1}
       \max\left\{R_8^L,\frac{R_8}{R_9}R_9^L\right\}\\
&\le\frac\delta{Z_0}\max\{R_8^L,(1-q)R_9^L\}\\
&\le\frac\delta{Z_0}L^9\max\{1,(1-q)L\}.
\end{aligned}
\tag{6.1}
$$

In particular $R_8/R_9\le1-q$ holds at every interior $q$, independently of $L$.

Proof. The envelope (2.3) gives

$$
0\le\Delta_H(k)\le\delta k^8,\qquad G\ge0,\qquad
\varepsilon\ge0.
\tag{6.2}
$$

In (5.5) both $\Delta_H(k)$ and $\varepsilon k^9$ are nonnegative. Thus

$$
(w_k)_+\le\frac{\Delta_H(k)q^k}{Z_1},\qquad
(-w_k)_+\le\frac{\varepsilon k^9q^k}{Z_1}.
\tag{6.3}
$$

Sum these separately, then use (5.12). This proves the first line of (6.1). It is the maximum of the two bounds, not their sum. The same envelope gives

$$
G_L\le\delta R_8^L,\qquad G\le\delta R_8,\qquad
\varepsilon=\frac{G}{Z_0}\le\delta\frac{R_8}{R_9},
\tag{6.4}
$$

proving the second line.

To control the normalization term without any cutoff asymptotic, absolute convergence of the polynomial-geometric series permits an index shift:

$$
\begin{aligned}
(1-q)R_9(q)
&=\sum_{k\ge1}\bigl(k^9-(k-1)^9\bigr)q^k.
\end{aligned}
\tag{6.5}
$$

The $k=1$ term uses $0^9=0$. For every integer $k\ge1$,

$$
(k-1)^9=(k-1)(k-1)^8\le(k-1)k^8,
\qquad k^9-(k-1)^9\ge k^8.
\tag{6.6}
$$

The latter inequality holds also at $k=1$. Sum it in (6.5) to get $R_8\le(1-q)R_9$. Since $R_9>0$, division proves the asserted ratio bound with the needed direction. Also $Z_1\ge Z_0>0$. Insert both facts into the second line of (6.1) to obtain its third line.

For the last line there are exactly $L$ short summands, each with $q^k\le1$, $k^8\le L^8$ and $k^9\le L^9$. Therefore

$$
R_8^L\le L^9,\qquad R_9^L\le L^{10}.
\tag{6.7}
$$

Their maximum gives the last line of (6.1). Every step was a finite-$q$ identity or inequality valid for all finite $L$. In particular $L=1$ is included. No premise that $(1-q)L$ is small was used. If the upper coefficient exceeds one it remains a valid upper bound; it is not being identified with a probability. $\square$

The term $(1-q)L$ records the cost of retaining normalization drift when the cutoff is large. Removing that term would not follow from (6.1). This is why the simultaneous theorem below carries a maximum rather than only $L^9$.

## 7. Actual-target stopped comparison and the finite-parameter converse

**Theorem 7.1 (Refined finite-$q$ bound for each target).** Under the exact source and observer premises above, fix any finite $M\ge2$, $0<\alpha<1/2$, $q\in(0,1)$, $\mathcal A\in\mathfrak A_M(q,\alpha)$ and finite integer $L\ge1$. Put

$$
b=1-2\alpha>0,\qquad
\chi_{M,L}=\frac{\gamma_L^{M-2}-1}{\gamma_L^{M-2}+1}.
\tag{7.1}
$$

For each $i\in\{0,1\}$ separately,

$$
b\le r_H(q)+\chi_{M,L}
       +\kappa_L B(1-q)\mathbb E_{i,q}^{\mathcal A}T.
\tag{7.2}
$$

If $\kappa_L>0$, then

$$
\mathbb E_{i,q}^{\mathcal A}T
\ge\frac{[b-r_H(q)-\chi_{M,L}]_+}
          {B(1-q)\kappa_L}.
\tag{7.3}
$$

If $\kappa_L=0$ and $b>r_H(q)+\chi_{M,L}$, no compliant observer exists at these parameters. If $\kappa_L=0$ and the residual is nonpositive, this interface provides only the nonnegative mean bound.

Proof. Fix the target $i$, let $j=1-i$, and use its own lawful $W_i$. Let $h(x)$ be the actual probability of ever hitting $d_1$ for $W_i$ started at $x$, including time zero. Let $h_j$ be that hitting probability for the actual opponent $U_j$. These definitions make sense even on reducible supports or states with a positive chance of never reaching either label. First-step conditioning gives

$$
\begin{gathered}
0\le h,h_j\le1,\qquad W_ih=h,\qquad U_jh_j=h_j,\\
h(d_0)=h_j(d_0)=0,\qquad h(d_1)=h_j(d_1)=1.
\end{gathered}
\tag{7.4}
$$

The two label conditions are explicit: both kernels fix $d_0,d_1$, so their actual hitting probabilities have these values regardless of other recurrent classes. By (5.3) the hypotheses of supplied interface 4.1 hold for $P=U_j$, $Q=W_i$, $\gamma=\gamma_L$, on the same configuration set. Its interior size $n$ is at most $M-2$. Since $(v-1)/(v+1)$ is increasing for $v\ge1$, (4.3) gives

$$
\sup_{x\in\mathcal S}|h(x)-h_j(x)|\le\chi_{M,L}.
\tag{7.5}
$$

This identifies a comparison to the actual opponent hitting function. It does not assume that $W_i$ terminates from the target's initial law or from every abstract state.

Now use the actual target epoch chain $Y_r$, with $Y_0\sim\nu_i$ and kernel $U_i$, and its stopping epoch $N$ from (4.6). For a positive integer $m$, finite stopped conditional expectation gives

$$
\mathbb E_i h(Y_{N\wedge m})-\nu_i h
=\mathbb E_i\sum_{r=0}^{(N\wedge m)-1}
       [(U_i-W_i)h](Y_r).
\tag{7.6}
$$

Indeed, in the ordinary epoch filtration containing the past gaps and update randomness already used, $\{N>r\}$ is measurable. On that event the next epoch has conditional kernel $U_i$, because the next source gap and future fresh update choices are independent of that past. Its conditional drift is $(U_i-I)h=(U_i-W_i)h$ by (7.4). After $N$ the increment is zero. Summing these $m$ finite conditional identities proves (7.6). No filtration exposing future update coins is used for this step.

Lemma 5.4, applied to the $[0,1]$-valued function $h$, bounds every summand in absolute value by $\kappa_L$. Under the actual target, (4.7) gives $N<\infty$ almost surely and $\mathbb E_iN<\infty$. The terminal values in (7.6) are bounded by one, and the absolute drift sum is bounded by the integrable variable $\kappa_LN$. Bounded convergence on the left and dominated convergence on the right therefore allow $m\to\infty$. Since $Y_N=d_D$, the boundary values in (7.4) give $h(Y_N)=D$. Writing $p_i=\mathsf P_i(D=1)$, we obtain

$$
|p_i-\nu_i h|\le\kappa_L\mathbb E_iN.
\tag{7.7}
$$

The opponent's actual almost-sure stop, from its actual initial row $\nu_j$, gives $p_j=\nu_jh_j$. No assertion about stopping from other initial configurations is needed. Decompose the same actual decision probabilities as

$$
p_i-p_j=(p_i-\nu_i h)+\nu_i(h-h_j)+(\nu_i-\nu_j)h_j.
\tag{7.8}
$$

The first term is bounded by (7.7), the second by (7.5), and the third by (4.5) since $h_j\in[0,1]$. Hence

$$
|p_i-p_j|\le\kappa_L\mathbb E_iN+\chi_{M,L}+r_H(q).
\tag{7.9}
$$

Both selected risks imply $p_0\le\alpha$ and $p_1\ge1-\alpha$, and therefore $p_1-p_0\ge b$. Inserting the actual payment inequality (4.9) into (7.9) proves (7.2). Repeating the argument with the other target changes its analytical $W_i$ and its expectation, while preserving the same actual $\eta,A,C$ and both decision probabilities. Thus the result bounds each mean individually, rather than the sum of means.

If $\kappa_L>0$, the denominator $B(1-q)\kappa_L$ is strictly positive. Division and nonnegativity of the mean prove (7.3). If $\kappa_L=0$, use (7.2) directly to obtain the two stated alternatives; no division by zero is taken. In that case (5.5) also gives every short $w_k=0$ and $m_L=0$, so (5.10) has zero actual target perturbation. $\square$

All stopping and payment in this proof refer to the same real source history and observer. A future analytical tick recording a frozen decision is not an extra paid or accessible bit. The proof uses neither a full-gap price for an interrupted terminal interval nor independence of that interval from the terminal decision. It imposes no global absorption, exit threshold, continuity of the retuned table or spectral assumption.

## 8. One neighborhood for all finite configuration budgets

**Theorem 8.1 (Simultaneous growing-budget lower bound).** Fix the exact $H_c$ and all source premises of Section 2. Choose $s_H>0$ from (2.8), using only the fixed source, such that

$$
Z_0(e^{-s})\ge\frac{9!}{2}s^{-10},\qquad
\mu_0(e^{-s})\ge\frac5s
\quad(0<s<s_H).
\tag{8.1}
$$

For a fixed $0<\alpha<1/2$, put

$$
b=1-2\alpha,\qquad
s_\alpha=\min\left\{s_H,1,\frac{5b}{8\delta}\right\}>0.
\tag{8.2}
$$

For every finite integer $M\ge2$ define

$$
\begin{aligned}
n_M&=M-2,\\
L_M&=\max\left\{1,\left\lceil\frac{2\delta(M-2)}b\right\rceil\right\},\\
X_M&=1+\frac{2\delta(M-2)}b.
\end{aligned}
\tag{8.3}
$$

Then simultaneously for every such $M$, every $0<s<s_\alpha$, every $\mathcal A\in\mathfrak A_M(e^{-s},\alpha)$ and each $i\in\{0,1\}$,

$$
\begin{aligned}
\mathbb E_{i,e^{-s}}^{\mathcal A}T
&\ge\frac{b\,9!}{4B\delta}\,
       \frac{s^{-11}}{L_M^9\max\{1,sL_M\}}\\
&\ge\frac{b\,9!}{4B\delta}\,
       \frac{s^{-11}}{X_M^9\max\{1,sX_M\}}.
\end{aligned}
\tag{8.4}
$$

The neighborhood $s_\alpha$ depends only on the source and risk, and is chosen before every budget and machine. No upper bound on $sL_M$ or $sX_M$ is assumed.

Proof. The moment premise selects (8.1) independently of all observers and budgets. After fixing $\alpha$, (8.2) selects a single neighborhood. Fix any finite $M$ and any $s$ in it. The integer $L=L_M$ is finite, positive and chosen independently of the actual machine at these parameters.

For $u\ge0$ let $g(u)=(e^u-1)/(e^u+1)$. Then $g(0)=0$ and

$$
g'(u)=\frac{2e^u}{(e^u+1)^2}\le\frac12,
\tag{8.5}
$$

because $(e^u-1)^2\ge0$. Integration gives $g(u)\le u/2$. Also $\log(1+v)\le v$ for $v\ge0$, by integrating $(1+v)^{-1}\le1$. Using $u=n_M\log\gamma_L$, we obtain

$$
\chi_{M,L}
\le\frac{n_M}{2}\log\left(1+\frac\delta{L+1}\right)
\le\frac{n_M\delta}{2(L+1)}\le\frac b4.
\tag{8.6}
$$

For $n_M=0$ the left side is exactly zero. For $n_M>0$, the definition gives $L\ge2\delta n_M/b$, hence $L+1\ge2\delta n_M/b$, which proves the last inequality. The maximum with one therefore causes no exception at small budgets.

The actual stationary initial comparison obeys, on this same neighborhood,

$$
r_H(e^{-s})\le\frac{2\delta}{\mu_0(e^{-s})}
\le\frac{2\delta}{5}s\le\frac b4.
\tag{8.7}
$$

To bound the signed coefficient, use (6.1), (8.1) and $1-e^{-s}\le s$:

$$
\begin{aligned}
\kappa_L(e^{-s})
&\le\frac\delta{Z_0(e^{-s})}L^9
        \max\{1,(1-e^{-s})L\}\\
&\le\frac{2\delta}{9!}s^{10}L^9\max\{1,sL\}.
\end{aligned}
\tag{8.8}
$$

This is an inequality for every finite $L$ on the same neighborhood, not an asymptotic for a fixed cutoff. Even when $L$ grows faster than $s^{-1}$, all its terms retain their stated directions.

Theorem 7.1 with (8.6)–(8.8) leaves at least $b/2$ of decision separation to be paid under each target:

$$
\begin{aligned}
\frac b2
&\le\kappa_L B(1-e^{-s})\mathbb E_iT\\
&\le\frac{2B\delta}{9!}s^{11}L^9
         \max\{1,sL\}\mathbb E_iT.
\end{aligned}
\tag{8.9}
$$

The final coefficient is strictly positive: $B,\delta,s,L$ are positive. Divide by that coefficient to get the first line of (8.4). We have not divided by $\kappa_L$; a zero actual coefficient with the positive residual separation would instead make a compliant observer impossible, as Theorem 7.1 states.

For $x\ge0$ one has $\lceil x\rceil\le x+1$, and $1\le x+1$. Consequently the full ceiling and maximum in (8.3) satisfy

$$
1\le L_M\le1+\frac{2\delta n_M}b=X_M,
\tag{8.10}
$$

including $n_M=0$. For fixed $s>0$, $z^9\max\{1,sz\}$ is increasing on positive $z$: it is $z^9$ for $sz\le1$ and $sz^{10}$ for $sz\ge1$, and these formulas agree at the boundary. Thus

$$
L_M^9\max\{1,sL_M\}\le X_M^9\max\{1,sX_M\}.
\tag{8.11}
$$

Taking reciprocals reverses this denominator comparison, which gives the second lower bound in (8.4). Every threshold used only the fixed source or risk. All estimates hold for the same actual machine through the supplied interfaces and for all finite cutoffs. This proves the simultaneous quantifiers without exchanging a fixed-$M$ limit with a growing-budget limit. $\square$

**Remark 8.2 (The large-cutoff regimes remain present).** Write $C_{\rm low}=b\,9!/(4B\delta)$. The first lower bound of (8.4) reads exactly

$$
\mathbb E_iT\ge
\begin{cases}
C_{\rm low}s^{-11}L_M^{-9},&sL_M\le1,\\
C_{\rm low}s^{-12}L_M^{-10},&sL_M>1.
\end{cases}
\tag{8.12}
$$

It is valid for bounded, unbounded and oscillating $sL_M$, including the boundary value one. The affine-budget version has the identical two formulas with $X_M$ replacing $L_M$. Since $L_M\le X_M$, it is possible that $sL_M\le1<sX_M$; the second line of (8.4) remains a weaker valid lower bound in that case by (8.11). No assertion that these regimes coincide is used. A large-cutoff lower bound may be weak, but it remains part of the universal statement and cannot be replaced by its small-cutoff formula.

**Proposition 8.3 (The two-state endpoint class).** For every $q\in(0,1)$ and $0<\alpha<1/2$, $\mathfrak A_2(q,\alpha)=\varnothing$.

Proof. Both internally emitted labels are counted. With two configurations they exhaust the budget, so no active configuration remains in the supplied same-budget normal form. The output is a source-independent initial label. If its probability of being one is $p$, the two risks require $p\le\alpha$ and $1-p\le\alpha$, implying $1\le2\alpha$, a contradiction. This is the already supplied lower-source Proposition 11.1 and uniform-source Proposition 8.3. $\square$

At $M=2$, (8.3) gives $n_M=0$, $L_M=X_M=1$ and $\chi_{M,L_M}=0$. The universal lower statement is then over an empty class; it does not assert a two-state classifier. No minimum nonempty budget or classification of intermediate budgets follows. The supplied fixed finite upper observer in fixed-observer-source Section 26 remains a separate sufficient construction.

## 9. Necessary growth for one fixed cubic target

**Theorem 9.1 (Necessary $8/9$ growth, with all budget regimes).** Keep exactly the source of Section 2 and one fixed $0<\alpha<1/2$. Suppose that for every sufficiently small $s>0$ there is a finite integer budget $M(s)\ge2$ and an observer

$$
\mathcal A_s\in\mathfrak A_{M(s)}(e^{-s},\alpha).
\tag{9.1}
$$

Thus both selected risks, both almost-sure stops and both finite pointwise means hold at every such $s$. Suppose additionally that one fixed $i_\star\in\{0,1\}$ and one fixed $0<C_T<\infty$, independent of $s$, satisfy

$$
\mathbb E_{i_\star,e^{-s}}^{\mathcal A_s}T\le C_Ts^{-3}
\quad\text{for every sufficiently small }s.
\tag{9.2}
$$

Put

$$
K=\frac{b\,9!}{4B\delta C_T}>0,\qquad
c_T=\min\{1,K^{1/9}\}>0,\qquad b=1-2\alpha.
\tag{9.3}
$$

Then eventually

$$
M(s)\ge2+\frac{b}{2\delta}
                \left(c_Ts^{-8/9}-1\right).
\tag{9.4}
$$

In particular, once also $c_Ts^{-8/9}\ge2$,

$$
M(s)-2\ge\frac{bc_T}{4\delta}s^{-8/9},
\tag{9.5}
$$

and hence $M(s)=\Omega_{H_c,\alpha,C_T}(s^{-8/9})$. The opposing source retains its risk, almost-sure stop and finite pointwise mean, but needs no cubic upper bound.

Proof. Intersect the eventual neighborhoods of (9.1) and (9.2) with the single neighborhood $(0,s_\alpha)$ of Theorem 8.1. At each $s$ in that intersection take its actual finite budget and actual observer, and apply the affine-budget lower bound to the fixed target $i_\star$. Write

$$
X=X_{M(s)}=1+\frac{2\delta(M(s)-2)}b\ge1.
\tag{9.6}
$$

Comparing (8.4) to (9.2) and multiplying only positive factors gives

$$
C_Ts^{-3}\ge\frac{b\,9!}{4B\delta}
                    \frac{s^{-11}}{X^9\max\{1,sX\}},
\qquad
X^9\max\{1,sX\}\ge Ks^{-8}.
\tag{9.7}
$$

There are two exhaustive cases at this selected $s$.

If $sX\le1$, the maximum is one, and the increasing ninth root gives

$$
X\ge K^{1/9}s^{-8/9}\ge c_Ts^{-8/9}.
\tag{9.8}
$$

This case is equivalently

$$
M(s)-2\le\frac{b}{2\delta}(s^{-1}-1).
\tag{9.9}
$$

It includes equality $sX=1$; it is a case of the proof, not a restriction imposed on the family.

If $sX>1$, then immediately $X>s^{-1}$. Throughout the chosen neighborhood $s<1$, so

$$
X>s^{-1}\ge s^{-8/9}\ge c_Ts^{-8/9}.
\tag{9.10}
$$

This case is equivalently the strict reverse of (9.9), and already forces the required growth without dropping the maximum from (9.7). It includes every arbitrarily large value of $sX$ and imposes no bound on $sL_{M(s)}$. The family may switch between the two cases at any sequence of parameters.

Thus in both cases $X\ge c_Ts^{-8/9}$ with the same constant. Substitute (9.6) and divide by $2\delta/b>0$ to obtain (9.4). Since $c_T>0$, eventually $c_Ts^{-8/9}\ge2$, and then $c_Ts^{-8/9}-1\ge(c_T/2)s^{-8/9}$. This proves (9.5) and the stated order.

The source, risk, target and cubic constant are fixed throughout. Only the machines and their finite budgets may vary with $s$, without regularity. The proof uses the target inequality of Theorem 8.1 at each actual $s$ and makes no fixed-budget limiting interchange. The opposing cubic mean was never assumed; its separate compliance conditions remain those in (9.1). $\square$

Pointwise finiteness of a mean does not by itself supply the fixed eventual $C_T$ in (9.2). Nor does the theorem allow a target label changing with $s$ or a risk allowance tending to $1/2$. Such alterations are different hypotheses. The budget counts all possible persistent configurations of the selected machine, not an expectation or a count along typical histories.

## 10. Exact gain over the credited $4/5$ result and upper context

**Proposition 10.1 (Source-relative improvement).** The refined scalar discrepancy can be used in the same target-specific interface as the mass bound of lower-source Lemma 6.2. It reduces the cutoff dependence from tenth power to ninth power with the explicit large-cutoff maximum, yielding the necessary exponent $8/9$ instead of the credited $4/5$. No matching exponent is established.

Proof. Lower-source equation (6.10) and uniform-source equation (5.9) subtract the same target-specific clipped kernel, then bound its variation by $\pi_0+\pi_1$. Equations (5.5) and (5.10) keep that subtraction signed, including its normalized tail drift. In fact the coefficients also obey

$$
P_L\le\pi_1,\qquad N_L\le\pi_0,\qquad
\kappa_L\le\max\{\pi_0,\pi_1\}\le\pi_0+\pi_1,
\tag{10.1}
$$

since $(f_1-f_0)_+\le f_1$ and $(f_0-f_1)_+\le f_0$ termwise. Thus the new additive coefficient fits the old proof object and assumptions, while retaining additional information.

The old short-total estimate uses $\sum_{k\le L}k^9\le L^{10}$. The retained positive and negative masses instead use $\Delta_H(k)\le\delta k^8$ and $\varepsilon\le\delta R_8/R_9$, giving (6.1). Near the endpoint their bound is $s^{10}L^9\max\{1,sL\}$ rather than a constant times $s^{10}L^{10}$. The price of live epochs still contributes one more factor $s$; no payment or source law changes. In the regime $sL\le1$ this makes the cutoff power nine. In the other regime (8.12) explicitly retains the normalization cost.

For comparison, lower-source Theorem 9.1 gives on its same source/risk-only neighborhood the credited affine-budget estimate

$$
\mathbb E_iT\ge\frac{b\,9!}{8B^2}\frac{s^{-11}}{X_M^{10}},
\tag{10.2}
$$

and its Theorem 10.1 derives necessary growth $\Omega(s^{-4/5})$ for the same fixed-target cubic hypothesis. Those prior results and their forest proof retain their ownership. The new consequence comes from the signed coefficient; it does not reclassify the old lower result as a new discovery.

To see the distinction in excluded growth rates, let a compliant family satisfy $M(s)=O(s^{-\beta})$ for some $0\le\beta<8/9$. Then $X_{M(s)}=O(s^{-\beta})$, so $sX_{M(s)}\to0$. The affine-budget bound in (8.4) consequently gives a fixed positive multiple of $s^{-11+9\beta}$ as a target lower bound eventually. Since $11-9\beta>3$, this contradicts a fixed cubic upper constant. This excludes, in particular, growth exponents $4/5\le\beta<8/9$ that the prior necessary $4/5$ statement alone does not exclude. Theorem 9.1 gives the full quantitative $\Omega(s^{-8/9})$ consequence without assuming a power law or remaining in this regime. Finally $8/9>4/5$ follows from $8\cdot5>4\cdot9$. $\square$

**Supplied comparison 10.2 (Sufficient exponent one).** The supplied upper proposal is titled “A paid geometric-mark controller with O(s^(-1)) complete states and O(s^(-3)) mean under both exact renewal sources.” Its independent check is titled “The finite geometric-mark and lazy-walk cubic upper proposal passes this bounded independent handwritten check.” These are supplied proposal-and-check statements, not final-source approval. They describe a source-blind survival-flag realization on fully read gaps, followed by a bounded midpoint-calibrated lazy walk, at the known common $q$.

For exact correspondence, their public design constants are

$$
p_i(q)=\frac{Z_i(q^2)}{Z_i(q)},\quad
\Delta(q)=p_1(q)-p_0(q),\quad
\ell=\log\frac{1-\alpha}{\alpha},\quad
c=\frac{a}{9\cdot2^{10}}>0.
\tag{10.3}
$$

They reuse fixed-observer-source Proposition 27.2 for $\Delta(e^{-s})=cs+O_H(s^2)$. With walk threshold $L^{\rm up}=\lceil2\ell/\Delta(q)\rceil$, distinct from the lower-proof cutoff $L_M$, the supplied controller lists $4L^{\rm up}+1$ complete configurations, including its first-wait state and both labels. On a source-only endpoint neighborhood, the proposal and check supply

$$
\begin{gathered}
4L^{\rm up}+1\le(16\ell/c+5)s^{-1},\\
\mathbb E_{i,e^{-s}}T\le
 (176\ell/c^2+44/c+7)s^{-3}\quad(i=0,1),
\end{gathered}
\tag{10.4}
$$

together with both selected risks, both almost-sure stops and both finite means. Their optional design outside the positive-separation branch uses the already credited fixed finite classifier. Its source credits, additional hypotheses and exact real-probability allowance remain those of the supplied upper proposal and check. No upper final manuscript is being approved or used here.

Equations (10.3)–(10.4) are comparison context, not premises of Theorems 7.1–9.1. Those lower proofs do not use a geometric mark, the upper walk, its source separation, its fallback certificate or an unrestricted cubic benchmark. The cubic target bound in Theorem 9.1 is simply a hypothesis about a proposed compliant family. The source-relative necessary exponent $8/9$ and separately supplied sufficient exponent $1$ therefore leave a gap; neither a sharp exponent nor a minimum budget follows.

## 11. Supplier map and applicability boundaries

**Definition 11.1 (Exact roles of the seven supplied inputs).** Source-relative ownership is as follows. The supplied filenames identify the seven inputs; theorem numbers below refer to those complete supplied texts.

| Supplier | Mathematical role and limit |
| --- | --- |
| `fixed-observer-source.md`, *Real renewal instruments and detector rank: finite observer memory*, Definitions 23.1–23.2, equations (23.1)–(23.7) | The exact fixed rational-center $H_c$, $\delta,B,a$, all-integer envelope, stationary survival-normalized first wait, independent subsequent zero counts and moment estimates in Section 2. Nested polynomial, envelope, stationary-identification and moment proofs remain supplied premises. |
| The same fixed-observer source, Lemma 23.4 and Lemmas 25.1–25.3 | Read-ready stochastic representation, analytical live epochs, actual hitting/telescoping discipline and predictable tick payment. Its original fixed-$q$-free/full-family quantifiers are distinct from the retuned class supplied by the uniform source. |
| `uniform-source.md`, *Retuned bounded-memory uniform renewal converse*, Definition 3.1 and Lemma 3.2; Lemmas 5.1–5.2 and 6.1–6.2 | The exact known-common-$q$ source-blind class and same-budget normal form, common stationary initial comparison, target-specific clipped kernel, actual-target stopping and payment. Its fixed-budget Theorem 7.2 remains credited. Its coarser elimination exponent is not substituted for the forest comparison. |
| `lower-source.md`, *Growing state budgets in the renewal paid-mean tradeoff*, Sections 4–5, Theorem 5.1 | The positive directed-forest and complementary-sum comparison (4.3), with interior $n\le M-2$ and no global absorption or positive-exit threshold. This is a reused theorem, not new forest content of this manuscript. |
| The same lower source, Lemmas 6.1–6.2 and 7.1–7.2; Theorem 8.1 | The initial, clipping, actual-epoch and actual-payment interfaces used here. The target-specific $W_i$ is unchanged; its mass-based additive estimate is refined by the signed coefficient. |
| The same lower source, Theorems 9.1 and 10.1; Proposition 11.1 | The prior simultaneous tenth-power-cutoff lower bound, necessary exponent $4/5$ and empty two-state class. Their complete results remain credited, as do that source's conditional fixed-budget upper and unrestricted comparisons. |
| `refinement-proposal.json`, results F1–F4 and G1–G3 | The source-relative signed-short content exhibited in Sections 5–10: exact normalized $w_k$ and short drift, collapsed scalar $\kappa_L$, its all-$q$/all-finite-$L$ bounds, insertion into the supplied actual-target interface, simultaneous maximum-factor lower bound and necessary $8/9$ consequence. This is the mathematical supplier of the refinement. |
| `refinement-check.json`, approved statement and checks F1–F4/G1–G3 | One supplied fallible independent handwritten check of that proposal, including zero discrepancy, actual supports, both targets, common neighborhood and both affine-budget regimes. It supplies no approval of this exact manuscript and no kernel certificate. |
| `upper-proposal.json`, geometric-mark/lazy-walk construction, and `upper-check.json`, its independent handwritten check | The separate sufficient order-$s^{-1}$ complete-state proposal and both cubic paid means quoted in Section 10. They are context only and do not prove a step of the lower refinement or approve a final upper source. |

The lower and uniform sources identify the fixed-observer continuation at revision `303bcf74526bab511d2175d5e302205d43654ab6`. Their unrestricted comparison refers to Definition 22.8 through Definition 22.12 of *Real renewal instruments and detector rank*, revision `07123ef6f510e6df2d990240c55e29ed9d7c2485`. These are supplier attributions, not additional independently inspected mathematical inputs. In particular no nested prefix-divergence, instrument realization, sum-four certificate or unrestricted-memory implementation is needed to deduce Theorems 7.1–9.1.

The deductions are classified as `repo-derived`: ordinary consequences relative to the supplied handwritten premises, with the signed-short proposal retaining mathematical credit. No external literature search supplies a `suspected-novel` or worldwide-priority designation. Classical total variation, summation by parts, stochastic first-step equations, forests, finite stopped conditional sums, convergence theorems and elementary calculus are proof methods rather than inventions of this companion. The fixed-observer source's attributions to Flower and Hellman for finite-statistic stochastic updates and to Marzen and Crutchfield for renewal conventions remain secondary attributions here; their primary papers' exact scopes are not independently certified.

**Open question 11.2 (The unresolved state tradeoff).** The optimal necessary exponent for a fixed cubic target, sufficiency at exponent $8/9$, optimal constants, the minimum nonempty complete budget and the behavior of intermediate small budgets are unresolved here. The supplied sufficient exponent one does not match the necessary exponent $8/9$. Neither lower inequality provides an observer or an exact optimizer.

**Boundary 11.3 (What resources and promises are covered).** The theorems concern one fixed exact $H_c$, one fixed risk allowance, the specified stationary history, and complete configurations at each known common $q$. Arbitrary retuning, unpriced immutable real transition precision, arbitrarily small positive exits, reducible supports and both-label pointwise finite means are included. All mutable control, registers and retained randomness, including both decision labels, remain counted. A finite number of named integer registers with unbounded possible values is not a finite configuration set.

There is no new $q$-free or separate-unknown-nuisance-family guarantee, varying-$H$ or residual-uniform theorem, sharpness claim, exact-coin implementation or immutable-description-size bound. The proofs supply no physical-memory, neural-dimension, finite-bit producer, empirical machine-learning, external elapsed-time or broader-project conclusion. Producer dimension is a different resource and is unnecessary for the explicitly defined output laws. Changing the stationary start, adding a clock or archive, skipping bits, receiving free gaps, resetting the source, observing another source or hidden state, or decoding a decision from stopping time changes the experiment and requires different hypotheses. No such channel is present in these deductions.

## 追加锚（本行以下为增补区）
