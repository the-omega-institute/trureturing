# Growing state budgets in the renewal paid-mean tradeoff

## 1. Scope and mathematical ownership

This volume studies a fixed pair of stationary binary renewal laws and observers whose finite sets of complete persistent configurations may grow as a known common parameter approaches one. The source assumptions and the observation contract are stated in full below. The resulting lower bound holds simultaneously for every finite configuration budget, on one endpoint neighborhood independent of that budget. With a fixed risk allowance, both almost-sure stops and both finite pointwise means, an eventual paid-mean upper bound $C_Ts^{-3}$ under even one fixed source, with $C_T$ independent of $s$, consequently requires at least order $s^{-4/5}$ complete configurations, where $q=e^{-s}$.

The exact source and the existing fixed-machine theory are supplied by [Real renewal instruments and detector rank: finite observer memory](FIB_REAL_RENEWAL_INSTRUMENTS_AND_DETECTOR_RANK_CONTINUATION.md), revision `303bcf74526bab511d2175d5e302205d43654ab6`, Definitions 23.1–23.2 through Definition 27.4. The pointwise retuned observer class, stationary initial-law comparison, target-specific clipping, and paid stopping interface are supplied by [Retuned bounded-memory uniform renewal converse](FIB_RETUNED_BOUNDED_MEMORY_UNIFORM_RENEWAL_CONVERSE.md), Sections 2–7. Its fixed-budget eleventh-power theorem is an existing result. The unrestricted comparison is supplied only by Definition 22.8 through Definition 22.12 of [Real renewal instruments and detector rank](FIB_REAL_RENEWAL_INSTRUMENTS_AND_DETECTOR_RANK.md), revision `07123ef6f510e6df2d990240c55e29ed9d7c2485`.

The additions relative to these supplied texts are the positive-forest comparison with exponent $2n\le2(M-2)$, its complementary-sum additive bound, their insertion into the existing paid-observer interface, and the simultaneous budget and necessary-growth consequences. Directed matrix-tree and forest expansions, determinant multilinearity, column replacement, first-step equations, stopped telescoping and predictable payment are classical methods. Their use here does not claim invention of those methods or worldwide priority for the resulting source-relative deductions.

All assertions are ordinary handwritten mathematics conditional on the stated source premises. In particular, the all-integer polynomial envelope and the source moment estimates are credited assumptions. The supplied upper observer and unrestricted cubic benchmark have their own additional premises; neither supplies a step in the new lower-bound proof. References made inside the supplied texts retain their status as supplier attributions. This volume gives no Lean kernel certificate or external novelty certification.

## 2. The fixed source premises

**Definition 2.1 (Exact rational shapes and their envelope).** Fix, for a real argument $x$,

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

Write $H=H_c$, $F_0(x)=x^9$, $F_1(x)=H(x)$, and set

$$
\delta=\frac{2749658638697}{10^{24}}>0,
\qquad B=1+\delta,
\qquad a=\frac{43377331415040}{35\cdot10^{24}}>0.
\tag{2.2}
$$

The integer-envelope premise is exactly

$$
\begin{gathered}
k^9\le F_i(k)\le Bk^9\quad(i=0,1),\\
1\le\frac{H(k)}{k^9}\le1+\frac\delta k
\qquad(k\in\mathbb Z,\ k\ge1).
\end{gathered}
\tag{2.3}
$$

This is the rational-center polynomial, with degree-eight coefficient $a$, rather than a limiting residual-zero vector. The continuation's Definition 23.1 and equation (23.3) supply (2.1)–(2.3), attributing the envelope to its owning source's Theorem 15.5. The envelope is used for every positive integer, not inferred from finitely many evaluations. The polynomial and all its constants stay fixed throughout.

**Definition 2.2 (Stationary start and consecutive renewal bits).** For $i\in\{0,1\}$ and $0<q<1$, define

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

The indices $k,b$ in these laws are integers. All these sums are finite at each interior $q$. The stationary one-sided law $\mathsf P_{i,q}$ first draws a tick time $\tau$ with

$$
\mathsf P_{i,q}(\tau=b)=\frac{S_{i,q}(b)}{\mu_i(q)}
\quad(b=0,1,\ldots).
\tag{2.5}
$$

It puts zeros before $\tau$ and a one at $\tau$. Independently of $\tau$, let $K_1,K_2,\ldots$ be iid with mass function $f_{i,q}$, and place the remaining ones at

$$
\tau_0=\tau,
\qquad \tau_n=\tau+\sum_{r=1}^n(K_r+1)\quad(n\ge1).
\tag{2.6}
$$

Every other bit of $X_0,X_1,\ldots$ is zero. Thus $K_r$ counts zeros, while $K_r+1$ is a full interval after a tick through the next tick. The first wait has the survival-normalized law (2.5), not the complete-gap law $f_{i,q}$.

Indeed $S_{i,q}(0)=S_{i,q}(1)=1$, and nonnegative summation gives

$$
\begin{aligned}
\sum_{b\ge0}S_{i,q}(b)
&=\sum_{k\ge1}(k+1)f_{i,q}(k)=\mu_i(q),\\
\mathbb E_{i,q}\tau
&=\frac1{\mu_i(q)}\sum_{k\ge1}\frac{k(k+1)}2f_{i,q}(k)
=\beta_i(q).
\end{aligned}
\tag{2.7}
$$

Each fixed $k$ contributes to the survival sum for $b=0,\ldots,k$ and to its first moment with total weight $0+\cdots+k$. These identities justify the normalization and mean in the stated observation law without supplying a hidden age to the observer.

**Assumption 2.3 (Source moment estimates).** With $s=-\log q\downarrow0$, retain the supplied estimates

$$
Z_i(e^{-s})=9!s^{-10}(1+O_H(s)),
\qquad \mu_i(e^{-s})=\frac{10}{s}+O_H(1),
\qquad \beta_i(e^{-s})=\frac{11}{2s}+O_H(1).
\tag{2.8}
$$

These are equation (23.7) of the continuation, also equation (2.8) of the uniform companion. The source attributes them to its polynomial-geometric moment suppliers. The source-only threshold used below will require only the consequences $Z_0(e^{-s})\ge(9!/2)s^{-10}$ and $\mu_0(e^{-s})\ge5/s$ on a sufficiently small neighborhood.

## 3. Known common parameter and complete configuration budgets

**Definition 3.1 (The pointwise compliant class).** Fix an integer $M\ge2$, a number $0<\alpha<1/2$, and a known common $q\in(0,1)$. An observer may be designed separately for this $q$; its state set, source-independent initialization and real transition probabilities may depend arbitrarily on $(q,H,\alpha,M)$. The same design and initialization are used under $\mathsf P_{0,q}$ and $\mathsf P_{1,q}$. Neither the true label nor source-dependent advice is supplied.

The observer has at most $M$ complete persistent configurations. They include initialization configurations, all active configurations, both internally emitted decision labels, every control phase, register, retained random choice and stored seed. A counter selecting random updates is persistent information and is counted. Fresh independent randomness may be used in updates, but retaining any part of it requires a counted configuration. Known $q$ and the fixed transition description are immutable design data; every mutable use of information must pass through the configuration set. No bound is imposed on the precision of immutable transition probabilities, no continuity across $q$ is assumed, and positive transitions may be arbitrarily small.

At an action the observer reads the next actual bit or stops and emits $D\in\{0,1\}$. Its choices use only its current configuration, the bit just read when applicable, and fresh randomness independent of the source and previous fresh randomness. Access is to the one uninterrupted consecutive history of Definition 2.2. There is no external time, age, clock, action count, program counter, archive, skipped bit, free gap, reset, second source, hidden-state observation, probability response or parameter query. The cost tally is not an input. The decision is the emitted label, with no external decoding from stopping time or read length.

If $X_0,\ldots,X_{T-1}$ are read, the paid cost is $T$. It includes every read zero, tick, initial wait and terminal partial gap. Initial stopping has cost zero. The class $\mathfrak A_M(q,\alpha)$ consists of these observers satisfying all six conditions

$$
\begin{gathered}
\mathsf P_{0,q}(D=1)\le\alpha,
\qquad \mathsf P_{1,q}(D=0)\le\alpha,\\
\mathsf P_{i,q}(T<\infty)=1,
\qquad \mathbb E_{i,q}T<\infty
\quad(i=0,1).
\end{gathered}
\tag{3.1}
$$

The risks here concern just this selected pair with known common $q$. The two separate termination and mean conditions are pointwise. A full-family guarantee is stronger and is not required. This is the uniform companion's Definition 3.1; it differs from the continuation's single fixed $q$-free observer across separate nuisance families.

**Lemma 3.2 (A common normal form at the selected parameter).** A compliant observer has a row distribution $\eta$ and row-stochastic bit matrices $A,C$ on a set $\mathcal S$ with $|\mathcal S|\le M$. There are distinct states $d_0,d_1$ absorbing for both matrices; each other state is ready for a next paid read. The same $\eta,A,C$ serve both source labels, and this representation preserves the joint law of $(T,D)$.

Proof. Compose initialization with the current-state choice between stopping and undertaking a read. Put stopping probability on its emitted label and the rest on the existing read-ready configurations. After each read, compose the bit update with the ensuing choice to stop or undertake another read. All retained information in that choice is already a counted part of the current configuration, so the composed kernels introduce no additional persistent state. Terminal configurations with the same label can be identified. Make each resulting label fixed under both bit matrices.

Before the first label is reached, these composed kernels reproduce the original read and stop actions. Thereafter fixing the label on unused future bits changes neither the actual cost nor the decision. Independent update randomness is marginalized into stochastic rows; it is not replaced by an accessible retained random tape. This is the same-budget reduction of the uniform companion's Lemma 3.2, using the continuation's Lemma 23.4 pointwise. $\square$

Suppress $q$ when convenient. The analytical complete-gap kernels and first-tick rows are

$$
U_i=\sum_{k\ge1}f_i(k)A^kC,
\qquad
\nu_i=\sum_{b\ge0}\frac{S_i(b)}{\mu_i}\eta A^bC.
\tag{3.2}
$$

They are stochastic averages and retain both absorbing labels. The unused continuation after an actual stop serves only to define these analytical quantities. At every comparison the matrices come from the same actual machine at the same $q$.

## 4. Positive directed forests and actual hitting probabilities

**Definition 4.1 (Common support and boundary).** Let $P,Q$ be row-stochastic matrices on the same finite set $\mathcal S$, with $|\mathcal S|\le M$ and common distinct absorbing labels $d_0,d_1$. Suppose $\gamma\ge1$ and

$$
\gamma^{-1}P(u,v)\le Q(u,v)\le\gamma P(u,v)
\quad(u,v\in\mathcal S).
\tag{4.1}
$$

Let $t=d_1$ and let $h_P,h_Q$ denote the actual probabilities of ever reaching $t$, allowing time zero. Comparison makes the directed positive-edge supports identical. In that common support set

$$
\mathcal Z=\{u:\text{there is no positive directed path from }u\text{ to }t\},
\qquad \partial=\mathcal Z\cup\{t\},
\qquad V=\mathcal S\setminus\partial,
\qquad n=|V|.
\tag{4.2}
$$

Here $d_0\in\mathcal Z$, so $n\le|\mathcal S|-2\le M-2$. Both hitting functions vanish on $\mathcal Z$ and equal one at $t$. The zero assertion follows because hitting is a countable union of finite-time hitting events, each requiring a positive finite path. Conversely a positive path gives a positive hitting probability. Replacing each row in $\mathcal Z$ by its identity row preserves every hitting probability: once that set is reached, $t$ is inaccessible. Perform this same replacement in $P$ and $Q$. It preserves (4.1), uses no new vertex, and makes every vertex of $\partial$ absorbing. Rows on $V$ are untouched.

**Definition 4.2 (Forest sums).** A directed forest $\phi$ chooses one successor $\phi(u)\in\mathcal S\setminus\{u\}$ for each $u\in V$, using common positive-support edges, with no directed cycle contained in $V$. Iteration must then terminate in $\partial$. Each forest selects exactly $n$ edges. For $P$ put

$$
\begin{aligned}
w_P(\phi)&=\prod_{u\in V}P(u,\phi(u)),
&\mathcal D_P&=\sum_\phi w_P(\phi),\\
\mathcal A_P(x)&=\sum_{\substack{\phi:\text{the path from }x\text{ ends at }t}}w_P(\phi),
&\mathcal C_P(x)&=\sum_{\substack{\phi:\text{the path from }x\text{ ends in }\mathcal Z}}w_P(\phi)
\quad(x\in V).
\end{aligned}
\tag{4.3}
$$

Thus $\mathcal D_P=\mathcal A_P(x)+\mathcal C_P(x)$, with all three quantities positive sums except that the complementary sum may be zero. Use the identical forest family for $Q$. The symbols $\mathcal A_P,\mathcal C_P$ are forest sums, distinct from the bit matrices $A,C$.

**Lemma 4.3 (Denominator, marked numerator and hitting identity).** For $V\ne\varnothing$, index coordinates by $V$ and define

$$
L_P=I-P_{VV},\qquad r_P(u)=P(u,t).
\tag{4.4}
$$

If $L_P^{[x]}$ replaces column $x$ of $L_P$ by $r_P$, then

$$
\det L_P=\mathcal D_P>0,
\qquad \det L_P^{[x]}=\mathcal A_P(x)>0,
\qquad h_P(x)=\frac{\mathcal A_P(x)}{\mathcal D_P}
\quad(x\in V).
\tag{4.5}
$$

The corresponding identities hold for $Q$. These are the positive directed-forest and marked-column identities for this boundary problem; their determinant methods are classical.

Proof. First, every $u\in V$ has a path to $t$ which stays outside $\mathcal Z$. Choose for each $u$ the first edge of a shortest such path. Distances to $t$ strictly decrease along chosen edges. This gives a positive forest in which every path terminates at $t$. Consequently the forest denominator and each marked sum are strictly positive for either kernel.

For the determinant formula, let $e_u^\mathsf T$ be the coordinate row at $u$. Stochastic row sums give the exact row decomposition

$$
L_P(u,\cdot)=
\sum_{v\ne u}P(u,v)
\bigl(e_u^\mathsf T-\mathbf1_{\{v\in V\}}e_v^\mathsf T\bigr).
\tag{4.6}
$$

In particular, its diagonal coefficient is $1-P(u,u)=\sum_{v\ne u}P(u,v)$. Self-loops have been accounted for by this equality, not removed from the stochastic experiment.

Expand the determinant multilinearly in its rows. A term chooses a successor $v\ne u$ for each $u\in V$ with coefficient $\prod_u P(u,v)$. A zero edge gives zero contribution. If a successor choice contains an internal directed cycle, the rows belonging to that cycle sum to zero, so its determinant vanishes. For an acyclic choice $\phi$, every path ends in the boundary. Order coordinates by increasing length of their $\phi$-path to the boundary, permuting rows and columns together. Each row has diagonal entry one and its only possible other entry, minus one, in an earlier column. Its matrix $L_\phi$ is triangular with determinant one. A simultaneous row and column permutation has no net sign. Therefore the surviving terms are exactly the forest weights with positive coefficient one. This proves $\det L_P=\mathcal D_P$.

Now replace column $x$ by $r_P$. The same row expansion uses the same successor coefficients. In a successor-choice matrix the entry in the replaced column is $\mathbf1_{\{\phi(u)=t\}}$, while all other columns have the entries of the row in (4.6). Rows on an internal cycle again sum to zero: in unreplaced columns they telescope, and in the replaced column every one of them is zero. Cyclic terms therefore still vanish.

For a forest $\phi$, let $z_\phi(u)$ be one if its path ends at $t$, and zero if it ends in $\mathcal Z$. Set $r_\phi(u)=\mathbf1_{\{\phi(u)=t\}}$. Checking an interior edge or a boundary edge gives

$$
L_\phi z_\phi=r_\phi.
\tag{4.7}
$$

Express $r_\phi$ as the sum of column $v$ of $L_\phi$ weighted by $z_\phi(v)$. Multilinearity in the replaced column annihilates every term $v\ne x$ because it duplicates column $v$. The $v=x$ term is $z_\phi(x)\det L_\phi=z_\phi(x)$. Thus this forest contributes its weight precisely when its path from $x$ ends at $t$. Summing proves the marked-numerator identity in (4.5), including its sign.

Finally the actual hitting function satisfies $h_P=Ph_P$ by first-step conditioning and has the boundary values in Definition 4.1. Its restriction to $V$ therefore obeys

$$
L_P(h_P|_V)=r_P.
\tag{4.8}
$$

The positive determinant makes this boundary problem uniquely solvable. Applying the same replaced-column argument to (4.8) gives $h_P(x)\det L_P=\det L_P^{[x]}$, proving the quotient. We have identified the actual hitting function, without assuming uniqueness of arbitrary harmonic functions on the original reducible chain or absorption from all its states. The proof for $Q$ is identical. If $V$ is empty, all states already have the specified boundary values; one may take the empty forest denominator to be one. $\square$

## 5. Multiplicative and complementary-sum comparison

**Theorem 5.1 (Finite-state hitting comparison).** Under Definition 4.1, for every $x\in\mathcal S$,

$$
\gamma^{-2n}h_P(x)\le h_Q(x)\le\gamma^{2n}h_P(x),
\qquad
|h_Q(x)-h_P(x)|\le\frac{\gamma^n-1}{\gamma^n+1},
\qquad n\le M-2.
\tag{5.1}
$$

No global absorption, irreducibility, aperiodicity, spectral gap or lower bound on positive exits is assumed.

Proof. Each positive forest has exactly $n$ comparable edges, so

$$
\gamma^{-n}w_P(\phi)\le w_Q(\phi)\le\gamma^n w_P(\phi).
\tag{5.2}
$$

Sum term by term over all forests, over forests marked at $x$, or over their complementary subfamily. The same factors compare $\mathcal D$, $\mathcal A(x)$ and $\mathcal C(x)$ respectively. Using (4.5) for $\mathcal A/\mathcal D$ proves the multiplicative assertion on $V$ with exponent $2n$. Boundary values agree and give it there too.

For the additive assertion, if $\mathcal C_P(x)=0$, termwise comparison gives $\mathcal C_Q(x)=0$ and both hitting values equal one. Otherwise both complementary sums and both marked sums are strictly positive. Put

$$
z=\frac{\mathcal A_P(x)}{\mathcal C_P(x)}>0,
\qquad
r=\frac{\mathcal A_Q(x)/\mathcal A_P(x)}
        {\mathcal C_Q(x)/\mathcal C_P(x)}.
\tag{5.3}
$$

Then $\gamma^{-2n}\le r\le\gamma^{2n}$, and

$$
h_P(x)=\frac z{1+z},\qquad h_Q(x)=\frac{rz}{1+rz}.
\tag{5.4}
$$

If $r<1$, interchange $P$ and $Q$; the new ratio is $1/r$ and lies in $[1,\gamma^{2n}]$. It suffices to consider $r\ge1$. The difference is

$$
h_Q(x)-h_P(x)=\frac{(r-1)z}{(1+z)(1+rz)}.
\tag{5.5}
$$

The nonnegative square $(z^{-1/2}-\sqrt r\,z^{1/2})^2$ yields

$$
\frac{(1+z)(1+rz)}z
=z^{-1}+rz+1+r
\ge2\sqrt r+1+r=(1+\sqrt r)^2.
\tag{5.6}
$$

Hence the difference is at most

$$
\frac{r-1}{(1+\sqrt r)^2}
=\frac{\sqrt r-1}{\sqrt r+1}
\le\frac{\gamma^n-1}{\gamma^n+1}.
\tag{5.7}
$$

The last inequality uses that $(v-1)/(v+1)$ increases for $v\ge1$. The case $r=1$ is included. Boundary states have zero difference, and if $n=0$ every state is boundary. This proves (5.1). $\square$

The proof uses a common positive family for both the marked and complementary sums. Estimating a signed difference of determinants would not give that comparison. Reducible supports and closed non-target classes are included: such classes lie in $\mathcal Z$ even if they were nonabsorbing before the analytical row replacement. Zero edges contribute zero in both kernels. Self-loops remain accounted for in (4.6); a very small positive exit may make forest sums small, but does not change their termwise ratios. Hitting values zero, one and the empty interior $V$ have all been treated explicitly. For $\gamma=1$ the additive bound is zero. The exponent $2n\le2(M-2)$ improves the supplied elimination exponent $2\cdot3^M$; no optimality of either the new exponent or the additive bound within this stochastic class is asserted.

## 6. The existing initial-law and clipping interface

The next two estimates reproduce the uniform companion's Lemmas 5.1–5.2 with their full argument, so that the forest comparison can be applied to the specified source and actual machine. They are supplied interfaces rather than additional source-relative discoveries.

**Lemma 6.1 (Uniform stationary initial comparison).** Define

$$
R_j(q)=\sum_{k\ge1}k^jq^k,
\qquad r_H(q)=\delta\frac{R_9(q)+R_8(q)}{R_{10}(q)+R_9(q)}.
\tag{6.1}
$$

For the rows in (3.2), using $\|u-v\|_{\rm TV}=\tfrac12\sum_x|u(x)-v(x)|$,

$$
\|\nu_0-\nu_1\|_{\rm TV}\le r_H(q)\le\frac{2\delta}{\mu_0(q)}.
\tag{6.2}
$$

Proof. The unnormalized first-wait weights and their sums are

$$
g_i(b)=\sum_{k\ge\max(1,b)}F_i(k)q^k,
\qquad \mathcal W_i=\sum_{k\ge1}(k+1)F_i(k)q^k=Z_i\mu_i.
\tag{6.3}
$$

Each $k$ contributes for $b=0,\ldots,k$, so $\sum_b g_i(b)=\mathcal W_i$ and the first-wait law is $g_i/\mathcal W_i$. By (2.3), $g_1\ge g_0$ pointwise and

$$
0\le\mathcal W_1-\mathcal W_0
\le\delta\sum_{k\ge1}(k+1)k^8q^k
=\delta(R_9+R_8),
\qquad \mathcal W_0=R_{10}+R_9.
\tag{6.4}
$$

When the difference is positive, normalize $g_1-g_0$ to a probability row $v$. Then

$$
\frac{g_1}{\mathcal W_1}
=\frac{\mathcal W_0}{\mathcal W_1}\frac{g_0}{\mathcal W_0}
+\frac{\mathcal W_1-\mathcal W_0}{\mathcal W_1}v.
\tag{6.5}
$$

Its variation distance from $g_0/\mathcal W_0$ is at most $(\mathcal W_1-\mathcal W_0)/\mathcal W_1\le r_H(q)$. If the difference is zero the two laws agree. Applying the common stochastic map $b\mapsto\eta A^bC$ cannot increase variation: for each finite-state event its conditional probability is in $[0,1]$, and the difference of its two averages is bounded by the input variation. This proves the first inequality. Finally $R_8\le R_9$ and $\mu_0=(R_{10}+R_9)/R_9$ give the second. The map is common under both labels even when its design and initialization depend on $q$. $\square$

**Lemma 6.2 (Per-target clipping).** For every finite integer $L\ge1$, define

$$
\begin{aligned}
\pi_i&=\sum_{k=1}^Lf_i(k),
&J_i^L&=\pi_i^{-1}\sum_{k=1}^Lf_i(k)A^kC,\\
V_i^L&=(1-\pi_i)^{-1}\sum_{k>L}f_i(k)A^kC,
&\gamma_L&=1+\frac\delta{L+1}.
\end{aligned}
\tag{6.6}
$$

For target $i$ and opponent $j=1-i$, put

$$
W=\pi_jJ_j^L+(1-\pi_j)V_i^L.
\tag{6.7}
$$

Every displayed kernel is stochastic and fixes both labels, and

$$
\begin{gathered}
\|U_i(x,\cdot)-W(x,\cdot)\|_{\rm TV}\le\pi_i+\pi_j,\\
\gamma_L^{-1}U_j(x,y)\le W(x,y)\le\gamma_L U_j(x,y).
\end{gathered}
\tag{6.8}
$$

Proof. Positivity of $f_i(k)$ for every $k\ge1$ gives $0<\pi_i<1$ at each interior $q$ and finite $L$. On $k>L$, let $t(k)=F_1(k)/F_0(k)$, which lies in $[1,\gamma_L]$. The conditional tail ratio is exactly

$$
\frac{f_1(k)/(1-\pi_1)}{f_0(k)/(1-\pi_0)}
=\frac{t(k)}{\displaystyle\sum_{\ell>L}\frac{f_0(\ell)}{1-\pi_0}t(\ell)}.
\tag{6.9}
$$

The denominator lies in the same interval. Thus both conditional tails are entrywise comparable by $\gamma_L$ in either direction. Their full $Z_i$ normalizers have cancelled. Averaging the common nonnegative entries of $A^kC$ proves that comparison for $V_0^L,V_1^L$. Adding the common nonnegative short term $\pi_jJ_j^L$ proves the second line of (6.8), and in particular gives $W$ and $U_j$ exactly the same support.

For the first line, use $U_i=\pi_iJ_i^L+(1-\pi_i)V_i^L$ to write

$$
U_i-W=\pi_i(J_i^L-V_i^L)-\pi_j(J_j^L-V_i^L).
\tag{6.10}
$$

Each difference of probability rows has variation at most one. The triangle inequality proves the claim. $\square$

These are two comparisons with different roles: an additive comparison to the actual target and a multiplicative comparison to the opponent. The opponent's whole short term remains present in $W$. The comparison neither discards a paid gap nor supplies a tail-only operational source. No termination of $W$ from arbitrary states is claimed or needed.

## 7. Unbounded stopping and actual-bit payment

**Lemma 7.1 (Analytical live epochs and per-target telescoping).** Follow the full source history while holding an actually emitted label fixed thereafter. Let $Y_n$ be the observer state just after the source tick at $\tau_n$, and put

$$
N=\inf\{n\ge0:Y_n\in\{d_0,d_1\}\},
\qquad Q_T=\sum_{t\ge0}\mathbf1_{\{T>t\}}X_t,
\qquad p_i=\mathsf P_{i,q}(D=1).
\tag{7.1}
$$

Under the actual source $i$, $Y_0$ has law $\nu_i$ and the epoch kernel is $U_i$. For a compliant observer,

$$
N<\infty\ \text{almost surely},\qquad Y_N=d_D,
\qquad N\le Q_T\le T,\qquad \mathbb E_iN<\infty.
\tag{7.2}
$$

For each target $i$ separately, with its own analytical $W$ in (6.7), let

$$
\chi^*_{M,L}=\frac{\gamma_L^{M-2}-1}{\gamma_L^{M-2}+1}.
\tag{7.3}
$$

Then

$$
|p_i-p_j|\le r_H(q)+\chi^*_{M,L}+(\pi_i+\pi_j)\mathbb E_iN,
\qquad j=1-i.
\tag{7.4}
$$

Proof. The stationary first wait and the independent subsequent gaps give exactly (3.2) for the epoch process, using the ordinary fresh update randomness along that process. If stopping is before or at the first tick then $N=0$. Otherwise every live state $Y_0,\ldots,Y_{N-1}$ is immediately after an actually read tick and commits to another read. Those are $N$ distinct paid ticks, so $N\le Q_T\le T$. If a zero run contains the actual stop, the next analytical tick records the frozen decision and need not itself have been read. It is not added to $Q_T$. All source waits and gaps are finite almost surely, so actual almost-sure stopping gives finite $N$ and $Y_N=d_D$. The target's finite paid mean gives finite $\mathbb E_iN$. These are the epoch-accounting facts of the continuation's Lemma 25.1 and the uniform companion's Lemma 6.1.

Let $h$ and $h_j$ be actual hitting probabilities of $d_1$ for $W$ and $U_j$, respectively. First-step conditioning gives

$$
0\le h,h_j\le1,\qquad Wh=h,\qquad U_jh_j=h_j,
\qquad h(d_0)=h_j(d_0)=0,\quad h(d_1)=h_j(d_1)=1.
\tag{7.5}
$$

By the entrywise comparison in (6.8), Theorem 5.1 applies on the same configuration set, with its interior size at most $M-2$. Since $(v-1)/(v+1)$ increases for $v\ge1$,

$$
\sup_x|h(x)-h_j(x)|\le\chi^*_{M,L}.
\tag{7.6}
$$

For a positive integer $m$, sum the stopped live increments of $h(Y_r)$ under the actual target chain. Conditional expectation gives

$$
\mathbb E_i h(Y_{N\wedge m})-\nu_i h
=\mathbb E_i\sum_{r=0}^{(N\wedge m)-1}[(U_i-W)h](Y_r).
\tag{7.7}
$$

Indeed on $r<N$ the conditional drift is $(U_i-I)h=(U_i-W)h$, and after $N$ it is zero. A $[0,1]$-valued function has average difference bounded by the row variation, so each summand has absolute value at most $\pi_i+\pi_j$ by (6.8). Bounded convergence for the terminal value and domination by $(\pi_i+\pi_j)N$ for the sum justify $m\to\infty$. Since $h(Y_N)=D$,

$$
|p_i-\nu_i h|\le(\pi_i+\pi_j)\mathbb E_iN.
\tag{7.8}
$$

The opponent's almost-sure stop from its actual initial row gives $p_j=\nu_jh_j$. Decompose the same actual decision probabilities as

$$
p_i-p_j=(p_i-\nu_i h)+\nu_i(h-h_j)+(\nu_i-\nu_j)h_j.
\tag{7.9}
$$

Equations (7.8), (7.6) and (6.2) prove (7.4). Both hitting functions remain meaningful at nonabsorbing abstract states, so no global-absorption condition was used. Repeating the argument for the other target changes only $W$ and the target expectation. It yields two separate bounds for the same machine, rather than a bound on the sum of means. The stopped-telescope interface is the supplied one; (7.6) is its improved comparison input. $\square$

**Lemma 7.2 (Predictable price of ticks).** For the source law of Definition 2.2, every legal read/stop rule satisfies

$$
\mathbb E_{i,q}Q_T\le B(1-q)\mathbb E_{i,q}T.
\tag{7.10}
$$

Proof. Retain the actual-history hazard argument of the continuation's Lemma 25.3 and the uniform companion's Lemma 6.2. After a tick has been read and exactly $b\ge1$ subsequent zeros have been read, the next-one probability is

$$
\frac{f_i(b)}{S_i(b)}
=\frac{F_i(b)q^b}{\sum_{k\ge b}F_i(k)q^k}
\le\frac{Bb^9q^b}{\sum_{k\ge b}b^9q^k}
=B(1-q).
\tag{7.11}
$$

At $b=0$ the probability is zero because $K\ge1$. Previous complete gaps are independent of the current gap, so conditioning on the entire preceding bit history gives the same bound.

Before any tick has been read, $b$ zeros say $\tau\ge b$. Under its actual stationary law the next-one probability is

$$
\frac{S_i(b)}{\sum_{v\ge b}S_i(v)}.
\tag{7.12}
$$

For integers $k\ge1$ and $r\ge0$, (2.3) gives

$$
F_i(k+r)\ge(k+r)^9\ge k^9\ge B^{-1}F_i(k).
\tag{7.13}
$$

Shift every tail term by $r$ to obtain $S_i(b+r)\ge B^{-1}q^rS_i(b)$ for $b,r\ge0$. For $b=0$ the shifted terms start at $r+1$ and are contained in the tail defining $S_i(r)$, which suffices for this inequality. Summing over $r$ bounds the denominator of (7.12) below by $B^{-1}S_i(b)/(1-q)$. Thus (7.12) also is at most $B(1-q)$. This handles the stationary first wait with its own distribution.

For payment alone, expose an independent supply of all observer coins on the analytical probability space. Let $\mathcal F_t$ contain those coins and the prefix $X_0,\ldots,X_{t-1}$. Independence leaves the next-bit source hazards unchanged, while the event $\{T>t\}$ that read $t+1$ is undertaken is $\mathcal F_t$-measurable. Tonelli and conditional expectation now give

$$
\begin{aligned}
\mathbb E_iQ_T
&=\sum_{t\ge0}\mathbb E_i\left[
\mathbf1_{\{T>t\}}\mathbb E_i(X_t\mid\mathcal F_t)\right]\\
&\le B(1-q)\sum_{t\ge0}\mathsf P_i(T>t)
=B(1-q)\mathbb E_iT.
\end{aligned}
\tag{7.14}
$$

This enlarged filtration is used for predictable payment, not to replace the ordinary live-chain filtration in (7.7) or to give a coin tape to the observer. The sum charges exactly the reads undertaken, including the terminal read. It charges no unread closing tick and no full mean gap in place of an interrupted gap. $\square$

## 8. The strengthened finite-parameter converse

**Theorem 8.1 (Finite-$q$ bound for each paid mean).** Under Definitions 2.1–2.2 and (2.3), fix any $M\ge2$, $0<\alpha<1/2$, $q\in(0,1)$ and $\mathcal A\in\mathfrak A_M(q,\alpha)$. For every finite integer $L\ge1$ and each $i\in\{0,1\}$, put $b_\alpha=1-2\alpha$ and use $r_H,\pi_i,\gamma_L,\chi^*_{M,L}$ from (6.1), (6.6) and (7.3). Then

$$
b_\alpha\le r_H(q)+\chi^*_{M,L}
+[\pi_0(q,L)+\pi_1(q,L)]B(1-q)\mathbb E_{i,q}^{\mathcal A}T,
\tag{8.1}
$$

and therefore

$$
\mathbb E_{i,q}^{\mathcal A}T
\ge\frac{[b_\alpha-r_H(q)-\chi^*_{M,L}]_+}
 {B(1-q)[\pi_0(q,L)+\pi_1(q,L)]},
\qquad [x]_+=\max\{x,0\}.
\tag{8.2}
$$

Proof. Both selected risks imply $p_0\le\alpha$, $p_1\ge1-\alpha$, and $p_1-p_0\ge b_\alpha$. Apply (7.4) with the chosen target, then use $\mathbb E_iN\le\mathbb E_iQ_T\le B(1-q)\mathbb E_iT$. This is (8.1). Its denominator in (8.2) is strictly positive because $B>0$, $q<1$ and $0<\pi_i<1$. Division and nonnegativity of the mean give (8.2). The same reasoning applies to the other target without changing the actual machine. $\square$

The uniform companion's Theorem 7.1 already supplies this clipping and payment structure. Here its comparison loss $(1+\delta/(L+1))^{2\cdot3^M}-1$ is replaced by

$$
\chi^*_{M,L}
=\frac{(1+\delta/(L+1))^{M-2}-1}
       {(1+\delta/(L+1))^{M-2}+1}.
\tag{8.3}
$$

No additive $O(s^{10})$ comparison of the original kernels $U_0,U_1$ uniformly over retuned machines is assumed. The continuation's Proposition 27.2 and the uniform companion's Section 9 already explain why such an estimate cannot simply be imported from a fixed matrix.

## 9. A simultaneous bound for every finite budget

**Theorem 9.1 (Joint budget and endpoint bound).** Fix the exact $H_c$ and all source premises of Section 2. Choose $s_H>0$ from (2.8), depending only on that fixed source, such that

$$
Z_0(e^{-s})\ge\frac{9!}{2}s^{-10},
\qquad \mu_0(e^{-s})\ge\frac5s
\quad(0<s<s_H).
\tag{9.1}
$$

For $0<\alpha<1/2$, put

$$
b=1-2\alpha,
\qquad s_\alpha=\min\left\{s_H,1,\frac{5b}{8\delta}\right\}.
\tag{9.2}
$$

For each finite integer $M\ge2$, set

$$
n_M=M-2,
\qquad L_M=\max\left\{1,\left\lceil\frac{2\delta n_M}{b}\right\rceil\right\},
\qquad S_L=\sum_{k=1}^L k^9.
\tag{9.3}
$$

Then simultaneously

$$
\begin{gathered}
\forall M\in\mathbb Z,\ M\ge2\quad
\forall s\in(0,s_\alpha)\quad
\forall\mathcal A\in\mathfrak A_M(e^{-s},\alpha)\quad
\forall i\in\{0,1\}:\\
\mathbb E_{i,e^{-s}}^{\mathcal A}T
\ge\frac{b\,9!}{8B^2S_{L_M}}s^{-11}
\ge\frac{9!b^{11}}{8B^2\bigl(b+2\delta(M-2)\bigr)^{10}}s^{-11}.
\end{gathered}
\tag{9.4}
$$

In particular, $s_\alpha$ is independent of all finite budgets and all machines. The constants and cutoffs are chosen before the machine. Discontinuous retuning, unbounded immutable description precision and arbitrarily small positive transitions are included.

Proof. The moment premise first selects $s_H$ using only $H_c$. Fixing $\alpha$ then selects $b,s_\alpha$. For any finite $M$, (9.3) selects a finite positive integer cutoff before the observer.

To bound the hitting loss, for $u\ge0$ let $f(u)=(e^u-1)/(e^u+1)$. It satisfies $f(0)=0$ and

$$
f'(u)=\frac{2e^u}{(e^u+1)^2}\le\frac12,
\tag{9.5}
$$

since $(e^u-1)^2\ge0$. Integration gives $f(u)\le u/2$. Also $\log(1+v)\le v$ for $v\ge0$, by integrating $1/(1+v)\le1$. Take $u=n_M\log(1+\delta/(L_M+1))$. Then

$$
\chi^*_{M,L_M}
\le\frac{n_M}{2}\log\left(1+\frac\delta{L_M+1}\right)
\le\frac{n_M\delta}{2(L_M+1)}
\le\frac b4.
\tag{9.6}
$$

When $n_M=0$ the left side is exactly zero. Otherwise the last inequality follows from $L_M\ge2\delta n_M/b$.

For any finite integer $L\ge1$, (2.3), $Z_i\ge Z_0$ and $e^{-sk}\le1$ give

$$
\pi_i(e^{-s},L)
\le\frac{BS_L}{Z_0(e^{-s})}
\le\frac{2BS_L}{9!}s^{10}
\quad(0<s<s_H).
\tag{9.7}
$$

This inequality is valid for every such $L$ on the same neighborhood; it is not a fixed-cutoff asymptotic. It remains an upper bound when its right side exceeds one. It therefore applies to $L=L_M$, including any choices $M=M(s)$ for which the cutoff grows without a bound on $sL_M$. Summing its two instances gives $\pi_0+\pi_1\le(4BS_{L_M}/9!)s^{10}$.

On $0<s<s_\alpha$, the initial comparison obeys

$$
r_H(e^{-s})\le\frac{2\delta}{\mu_0(e^{-s})}
\le\frac{2\delta}{5}s\le\frac b4.
\tag{9.8}
$$

Thus (8.1), (9.6) and (9.8) leave at least $b/2$ of separation to be paid under each target separately. With $1-e^{-s}\le s$ and (9.7),

$$
\frac b2
\le[\pi_0+\pi_1]B(1-e^{-s})\mathbb E_iT
\le\frac{4B^2S_{L_M}}{9!}s^{11}\mathbb E_iT.
\tag{9.9}
$$

Division proves the first bound in (9.4). To expose its budget dependence, each of the $L$ summands in $S_L$ is at most $L^9$, so $S_L\le L^{10}$. The ceiling inequality $\lceil x\rceil\le x+1$ for $x\ge0$, together with the maximum in (9.3), gives

$$
L_M\le1+\frac{2\delta n_M}{b}
\quad\text{including }n_M=0.
\tag{9.10}
$$

Consequently

$$
\frac{b\,9!}{8B^2S_{L_M}}
\ge\frac{b\,9!}{8B^2(1+2\delta n_M/b)^{10}}
=\frac{9!b^{11}}{8B^2(b+2\delta n_M)^{10}},
\tag{9.11}
$$

which proves the second bound. Every estimate used the selected actual observer through the same interface, while every source threshold was independent of its budget. No exchange of a fixed-$M$ limit with $M\to\infty$ occurred. $\square$

The eleventh-power order at each fixed $M$ was already supplied by the uniform companion's Theorem 7.2. Formula (9.4) adds explicit polynomial deterioration with the complete budget and a single endpoint neighborhood for all finite $M$. The short-mass estimate (9.7) is what permits every growing cutoff; imposing a hidden $sL_M$ restriction would not yield this statement.

## 10. Necessary configuration growth for a cubic target mean

**Theorem 10.1 (A necessary finite-budget growth rate).** Keep one exact source pair from Section 2 and one fixed $0<\alpha<1/2$. Suppose that for every sufficiently small $s>0$ there is a finite integer budget $M(s)$ and an observer

$$
\mathcal A_s\in\mathfrak A_{M(s)}(e^{-s},\alpha).
\tag{10.1}
$$

Thus both selected risks, both almost-sure stops and both finite pointwise paid means hold at each $s$. Suppose in addition that for one fixed target $i_\star\in\{0,1\}$ there is a constant $0<C_T<\infty$, independent of $s$, with

$$
\mathbb E_{i_\star,e^{-s}}^{\mathcal A_s}T\le C_Ts^{-3}
\quad\text{for all sufficiently small }s.
\tag{10.2}
$$

Define

$$
A_T=\left(\frac{9!b^{11}}{8B^2C_T}\right)^{1/10}>0,
\qquad b=1-2\alpha.
\tag{10.3}
$$

Then, throughout a sufficiently small neighborhood,

$$
M(s)\ge2+\frac{A_Ts^{-4/5}-b}{2\delta}.
\tag{10.4}
$$

In particular $M(s)=\Omega_{H_c,\alpha,C_T}(s^{-4/5})$. The cubic upper bound need hold only under the fixed target; the opponent retains all its compliance conditions.

Proof. Apply Theorem 9.1 at each selected $s$ in its common neighborhood, taking $M=M(s)$ and using the actual $\mathcal A_s$. Comparing its target lower bound with (10.2) gives

$$
C_Ts^{-3}
\ge\frac{9!b^{11}}{8B^2\bigl(b+2\delta(M(s)-2)\bigr)^{10}}s^{-11}.
\tag{10.5}
$$

All divided factors are strictly positive. Hence

$$
\bigl(b+2\delta(M(s)-2)\bigr)^{10}
\ge\frac{9!b^{11}}{8B^2C_T}s^{-8}.
\tag{10.6}
$$

The increasing tenth root on nonnegative numbers gives $b+2\delta(M(s)-2)\ge A_Ts^{-4/5}$. Division by $2\delta>0$ proves (10.4). Once $A_Ts^{-4/5}\ge2b$, it also gives

$$
M(s)-2\ge\frac{A_T}{4\delta}s^{-4/5},
\tag{10.7}
$$

with a positive constant independent of $s$. This proves the stated order. The exponent is the ratio $8/10$ in (10.6). No cubic lower or upper supplier is used in this implication; (10.2) is simply an additional hypothesis about the proposed family. $\square$

The theorem excludes $M(s)=o(s^{-4/5})$ for such a family. It neither supplies an observer with $M(s)$ proportional to $s^{-4/5}$ nor proves that the exponent is sharp. Pointwise finite means alone do not imply the uniform cubic upper constant in (10.2). Allowing $\alpha$ to vary with $s$, allowing a changing polynomial, or dropping the opposing risk or mean would change the hypotheses. The budget counts all possible persistent configurations at the selected parameter; it is not an expected or typical-history memory measure.

## 11. Nonempty budgets and credited upper comparisons

**Proposition 11.1 (Two labels exhaust a two-state budget).** For $0<\alpha<1/2$, $\mathfrak A_2(q,\alpha)=\varnothing$ at every $q\in(0,1)$.

Proof. Both decision labels are included in the complete budget, so no active configuration remains. The emitted label is a source-independent initial choice. If its probability of being one is $p$, the two risks require $p\le\alpha$ and $1-p\le\alpha$, which would imply $1\le2\alpha$. This is impossible. This is also the empty-class assertion of the uniform companion's Proposition 8.3. Thus (9.4) at $M=2$ is a universal statement over an empty class, not a nonemptiness assertion. $\square$

**Assumption 11.2 (The source-owned sufficient fixed budget).** The continuation's Definition 26.1, Lemmas 26.2–26.3 and Theorem 26.4 supply an upper observer for these exact source laws. To state its sufficient budget without confusing the sample count with $M$, write

$$
\begin{aligned}
C_i&=F_i(2)^2+2F_i(1)F_i(3),
&\theta_i&=\frac{F_i(2)^2}{C_i},\\
\Delta_\theta&=\theta_0-\theta_1,
&V_\theta&=\max_i\theta_i(1-\theta_i).
\end{aligned}
\tag{11.1}
$$

The supplied additional sum-four certificate is, for $r_k=H(k)/k^9$,

$$
r_1r_3-r_2^2
=\frac{520040714516414119558257878908551006355871}
       {331776\cdot10^{48}}>0,
\qquad 0<\theta_1<\theta_0<1.
\tag{11.2}
$$

This certificate is credited, not recalculated here. Choose a fixed rational $0<\alpha_0\le\alpha$ and let

$$
n_\alpha=\left\lceil\frac{8V_\theta}{\alpha_0\Delta_\theta^2}\right\rceil,
\qquad b_{n_\alpha}=\left\lceil\frac{n_\alpha(\theta_0+\theta_1)}2\right\rceil,
\qquad S_\alpha=10n_\alpha(n_\alpha+1)+3.
\tag{11.3}
$$

The supplied machine waits through the first actual tick and then reads every raw gap through its closing tick. It retains categories $1,2,3$, keeps a pending retained category across intervening long gaps, pairs consecutive retained categories, and clears the pending category after each pair. It accepts a pair exactly when its categories sum to four, with mark one on $(2,2)$ and zero on $(1,3),(3,1)$. At the $n_\alpha$th acceptance it emits zero for at least $b_{n_\alpha}$ one marks, and one otherwise.

Its supplied complete realization has one first-tick waiting state, both labels, and active configurations

$$
(z,p,m,v),\qquad z\in\{0,1,2,3,4\},\quad
p\in\{\varnothing,1,2,3\},\quad
0\le m<n_\alpha,\quad0\le v\le m.
\tag{11.4}
$$

Here the zero count $z$ saturates at four, $p$ is the pending category, $m$ counts accepted pairs and $v$ counts their one marks. The thresholds and control are in its fixed deterministic table; there is no extra mutable program state. The count is $5\cdot4\sum_{m=0}^{n_\alpha-1}(m+1)+3=S_\alpha$. Long gaps are still fully read after their category becomes ineligible.

For exact correspondence put

$$
A_i^{\rm sh}(q)=\sum_{k=1}^3F_i(k)q^k,
\qquad \rho_i=\frac{A_i^{\rm sh}}{Z_i},
\qquad \zeta_i=\frac{C_iq^4}{(A_i^{\rm sh})^2}.
\tag{11.5}
$$

The source supplies iid retained categories with law $F_i(k)q^k/A_i^{\rm sh}$, geometric retention counts of mean $1/\rho_i$ independent of those categories, and iid accepted Bernoulli$(\theta_i)$ marks. Its two separate full-family errors are at most $4V_\theta/(n_\alpha\Delta_\theta^2)\le\alpha_0/2\le\alpha$. With $G$ its number of completed raw post-first-tick gaps, its supplied paid identities are

$$
\begin{aligned}
\mathbb E_iG&=\frac{2n_\alpha}{\rho_i\zeta_i}
=\frac{2n_\alpha Z_iA_i^{\rm sh}}{C_iq^4},
&T&=1+\tau+\sum_{r=1}^G(K_r+1),\\
\mathbb E_{i,q}T
&=1+\beta_i(q)+\frac{2n_\alpha\mu_i(q)Z_i(q)A_i^{\rm sh}(q)}{C_iq^4},\\
\mathbb E_{i,e^{-s}}T
&\sim\frac{20n_\alpha\,9!\,A_i^{\rm sh}(1)}{C_i}s^{-11}.
\end{aligned}
\tag{11.6}
$$

Both leading coefficients are positive; the supplied constants include $C_0=301510$ and $A_0^{\rm sh}(1)=20196$. The source proves almost-sure termination and finite pointwise means at every interior $q$ under both laws. Its predictable inclusion $\{G\ge r\}$ depends on preceding gaps and is independent of the next $K_r$, which prices the completed sum by $\mu_i\mathbb E_iG$. It does not assert independence between a gap's duration and the acceptance decision after that gap. Rejected pairs, discarded long gaps, the stationary first wait and the final tick are all paid. Equations (11.1)–(11.6) remain supplied upper-construction statements; the construction is not a new result of this volume.

**Corollary 11.3 (Conditional nonvacuous fixed-budget comparison).** Conditional also on Assumption 11.2, every fixed budget $M\ge S_\alpha$ admits a compliant observer at every interior $q$. For each $i$,

$$
\inf_{\mathcal A\in\mathfrak A_M(e^{-s},\alpha)}
\mathbb E_{i,e^{-s}}^{\mathcal A}T
=\Theta_{M,H_c,\alpha}(s^{-11}).
\tag{11.7}
$$

Proof. The supplied $q$-free machine may ignore known $q$; its complete count, two risks, two terminations and two finite means put it in the class whenever $M\ge S_\alpha$. Formula (11.6) supplies the upper order for both labels with the same machine. Formula (9.4), or the already supplied fixed-budget theorem, gives the uniform lower order for each infimum. This is the same attained fixed-budget order credited in the uniform companion's Corollary 8.2; it does not identify an exact optimizer. $\square$

The threshold $S_\alpha$ is sufficient, not minimal. Neither the source upper construction nor the new lower bound classifies nonemptiness or supplies a matching upper for $2<M<S_\alpha$. The universal lower statements apply to any compliant machine there if such a machine exists.

**Assumption 11.4 (Unrestricted cubic context).** The supplied append's Theorem 22.9 and Corollaries 22.10–22.11 give cubic paid-mean lower and matching upper order for the same exact stationary consecutive-read laws, with its paid length $L$ corresponding to $T$. Its unrestricted $q$-free protocols may have arbitrary persistent memory and a common independent seed, with two separate full-family risk promises and both almost-sure stops and finite pointwise means. The append also supplies the retuned common-band statement on $I_\varepsilon=[1-2\varepsilon,1-\varepsilon]$, where $\varepsilon\le-\log q\le4\varepsilon$ on sufficiently small bands: each separate worst-band mean infimum and the joint worst-band mean infimum have order $\Theta_{H_c,\alpha}(\varepsilon^{-3})$.

These are conditional benchmark statements. Their nested prefix-divergence and unrestricted upper-implementation suppliers are not established here. In particular the append's symbol $\delta_9$ is not silently identified with the polynomial-envelope $\delta$ in (2.2). Its proof-local timeout uses only the two selected risks at a common $q$, so the supplied lower argument also applies pointwise when that common parameter is known. The supplied unrestricted $q$-free upper rule is admissible in that larger known-$q$ class by ignoring $q$.

Unbounded possible gap counters, pair counters and growing arithmetic precision in the supplied unrestricted procedure are not a finite set of complete configurations. Finitely many names for integer registers do not supply a finite $M(s)$ over all histories, even when a typical run uses little memory. Consequently the cubic benchmark does not realize any finite growing budget in Theorem 10.1. It motivates the additional cubic hypothesis there but is not a dependency of its lower-bound proof.

## 12. Supplier correspondence and unresolved resource boundaries

**Definition 12.1 (Dependency and credit map).** The mathematical roles are as follows.

| Supplier or deduction | Exact role and boundary |
| --- | --- |
| Continuation, Definition 23.1, equation (23.3); uniform companion, Definition 2.1 | Fixed rational $H_c$, $\delta,B,a$ and the all-integer envelope in Section 2. The nested envelope proof remains a credited premise. |
| Continuation, Definition 23.2, equations (23.4)–(23.7); uniform companion, Definition 2.2 | The stationary first wait, independent iid subsequent zero counts, payment convention and moment premises (2.4)–(2.8). |
| Uniform companion, Definition 3.1 and Lemma 3.2; continuation, Lemma 23.4 | The exact known-common-$q$ retuned class and same-budget normal form in Section 3. The continuation's original full-family fixed-machine quantifiers remain distinct. |
| Uniform companion, Lemma 4.1 | Common entrywise comparison hypotheses; its coarse elimination exponent is replaced by the positive-forest argument of Sections 4–5. The new argument does not rely on that elimination loss. |
| Uniform companion, Lemmas 5.1–5.2 | Uniform initial mixture and target-specific short/tail clipping, fully exhibited in Section 6. These are reused suppliers. |
| Continuation, Lemmas 25.1–25.3; uniform companion, Lemmas 6.1–6.2 and Theorem 7.1 | Actual epochs, stopped telescoping and predictable actual-bit payment. Sections 7–8 retain that interface with the new hitting comparison. |
| Continuation, Theorem 25.4; uniform companion, Theorem 7.2 | Existing fixed-machine and observer-uniform fixed-budget eleventh-power results. The new Section 9 contribution is simultaneous budget dependence and one neighborhood for all finite budgets. |
| Continuation, Definition 26.1, Lemmas 26.2–26.3 and Theorem 26.4; uniform companion, Section 8 | Conditional sum-four certificate, sufficient complete state threshold $S_\alpha$ and the source-owned finite upper observer. Its sample count is $n_\alpha$ here, separate from total budget $M$. |
| Owning source, supplied Definition 22.8 through Definition 22.12; uniform companion, Section 9 | Conditional unrestricted cubic and common-band benchmarks. Their paid length $L$ is $T$ here; nested prefix and upper suppliers remain conditional. |
| Sections 4–5 and Theorems 8.1, 9.1, 10.1 of this volume | Source-relative derived comparison, strengthened finite-$q$ converse, simultaneous joint lower bound and necessary finite-budget growth. No additional upper construction is supplied. |

The additions are classified as `repo-derived`, meaning deductions relative to the supplied handwritten sources and explicit premises. No external literature search establishes a `suspected-novel` or global-priority claim. Directed forest and matrix-tree methods and column-replacement determinant identities are classical proof inputs. The continuation's references to Flower and Hellman for finite-statistic stochastic updates, and to Marzen and Crutchfield for stationary renewal conventions, remain secondary source attributions; no exact scope of those external papers is independently certified here.

**Open question 12.2 (Sufficiency and sharpness).** The optimal hitting-comparison dependence within the constrained stochastic class, the optimal budget dependence for these renewal observers, and the optimal necessary growth exponent for a cubic mean are unresolved here. A sufficient finite growing budget, a matching construction and a sharp transition would require additional realization and performance proofs. The lower inequality (10.4) alone supplies none of them.

**Open question 12.3 (Small and intermediate complete budgets).** Apart from the two-label impossibility at $M=2$ and the conditional sufficient threshold $S_\alpha$, the minimum nonempty budget and the performance of intermediate budgets remain unclassified. A lower bound on a possibly empty class does not provide an observer.

The conclusions concern complete configurations for one fixed source pair and the specified consecutive paid-read experiment. They do not identify immutable transition-description precision with mutable memory, count growing registers as finitely many states, or treat proof objects as accessible channels. There is no varying-$H$, residual-uniform, general-parity, hidden-state, reset-access, exact-optimizer or sharp-constant conclusion. The supplied producer dimension is a different resource and is unnecessary to the argument for the explicit laws. No physical-storage, neural hidden-dimension, empirical machine-learning, external elapsed-time decision or broader-project conclusion follows. Changing the stationary start, permitting an unpaid archive or clock, or decoding the label from stop time would require a different theorem.

## 追加锚（本行以下为增补区）
