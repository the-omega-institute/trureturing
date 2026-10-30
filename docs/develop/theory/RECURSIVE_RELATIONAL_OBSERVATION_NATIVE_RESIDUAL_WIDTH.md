# Native residual width from a common branch-time coordinate

## 1. Physical depths and their domains

**Definition 1.1 (source and immutable descriptors).** Use the single alpha-origin source of [GPO, Definition 27.1][GPO]: persistent physical links $a<b$, one actual root, total paid literal presence, simultaneous old-leaf substitution, and beta-leaf births committed in physical lexicographic order. At the $j$th birth the actuator consumes $z_j$, placing beta at $a$ exactly when $z_j=1$. Old branches persist; a newborn leaf is not updated in its birth update. The only observer operations are the original serial localStep, applyRho, presence-Read and stop, with their actual binding, grants, backing, completion and stationarity premises.

Write $F_0=0,F_1=1,F_{i+2}=F_{i+1}+F_i$ and $B_t=F_{t+1}-1$ for the total births by cut $t$. For a physical node $p$, its creation update $b_p$ and initial label $\sigma_p$ remain immutable even after its label changes. [ACR, Definitions 2.1 and 10.1][ACR] give

$$
 \tau_p=b_p+2-\mathbf1_{\sigma_p=\beta},\qquad
 q_p=\kappa_n(p)=n-b_p+\mathbf1_{\sigma_p=\beta}.
 \tag{NRW.1}
$$

Here $\tau_p$ is the branch update, the root has descriptor $(0,\alpha)$, and both children are created at $\tau_p$. A present cone of rank zero or one is terminal. A branch of rank $q\ge2$ has child ranks $q-1,q-2$, the larger at $a$ precisely when its birth bit is one. Prefixes, ranks and descriptors are mathematical coordinates, not extra observations or acquired address records.

**Definition 1.2 (complete depth and physical encoding).** Encode physical words by $\eta(a)=0,\eta(b)=1$, extended by concatenation. For a present $p$ and a tape $u\in\{0,1\}^L$, perform [ACR Definition 13.1][ACR]'s walk: start at $p$, submit the full literal $pa$ to the actual root, stop if absent, otherwise follow $a$ for the next bit zero and $b$ for one, and repeat at the reached node. The final absent-child test is paid. Write $D_{n,p}^{L}(u)$ for the number of traversed edges. Take $L\ge\max(q_p-1,0)$, so every path reaches a terminal node using at most $L$ directions; the terminal test consumes no direction bit. The complete residual is this function on the entire tape cube. Set $H_n=2n-1$ for $n\ge2$ and $D_{n,p}=D_{n,p}^{H_n}$.

**Lemma 1.3 (padding and root offset).** Every path in a rank-$q$ cone has at most $\max(q-1,0)$ edges. If $L'\ge L\ge\max(q-1,0)$, then

$$
 D_{n,p}^{L'}(uv)=D_{n,p}^{L}(u)
 \quad(u\in\{0,1\}^L,\ v\in\{0,1\}^{L'-L}).
 \tag{NRW.2}
$$

For every present $p$ of length $h$, every $u\in\{0,1\}^{H_n-h}$ and every $v\in\{0,1\}^h$,

$$
 D_{n,\varepsilon}^{H_n}(\eta(p)u)
 =h+D_{n,p}^{H_n-h}(u)
 =h+D_{n,p}^{H_n}(uv).
 \tag{NRW.3}
$$

*Proof.* At a branch each edge reduces rank by one or two, and ranks zero and one are terminal. Induction gives the depth bound, also attained at $q\ge1$ by always taking the larger-rank child. After termination later tape bits are unused, proving (NRW.2). Since $p$ is present, the root walk follows its first $h$ directions without early termination. The root rank is $n$, and along this present path $q_p\le n-h$; hence $H_n-h\ge\max(q_p-1,0)$. Its remaining procedure is exactly the local walk, including the same terminal test. This proves both equalities for every padding word. In particular, equality or inequality of complete local residuals transfers to the shorter suffix domain in (NRW.3). $\square$

**Lemma 1.4 (observable orientations).** A complete depth function determines the ordered finite tree of its terminal and branch positions. At any reached branch of rank $r\ge3$, it determines its orientation bit. A branch of rank two has two terminal children and its orientation is not determined this way.

*Proof.* Restricting the function to tapes beginning with a direction word $w$ and subtracting $|w|$ gives the local depth function at the reached node. It is identically zero exactly at a terminal node, and strictly positive at a branch. Induction reconstructs the ordered tree. The maximum local depth at rank $j\ge1$ is $j-1$, and at rank zero is zero. Thus the two child maxima at rank $r\ge3$ are $r-2,r-3$. Their order identifies the rank-$r-1$ child and its bit. At $r=3$ they are one and zero; at rank two both are zero. All restrictions have sufficient remaining horizon by the rank decrease along $w$. $\square$

## 2. Common branch time and consecutive global outputs

**Lemma 2.1 (beta-origin synchronization for all descriptors).** Every rank-$q\ge2$ cone at cut $n$ has the same branch time

$$
 \tau=n-q+2.
 \tag{NRW.4}
$$

At update $\tau-1$ it consists of a single beta leaf. Measured from that cut, its entire future follows the same beta-origin substitution rule, regardless of its initial descriptor. After $k\ge0$ further updates its number of beta leaves is $F_{k+1}$. The beta leaves immediately before its $k$th further update, $k\ge1$, therefore number $F_k$.

*Proof.* Add the two equations (NRW.1). For initial alpha, $(b_p,\sigma_p)=(n-q,\alpha)$: the node changes to beta at $b_p+1=\tau-1$ and branches at $\tau=b_p+2$. For initial beta, $(b_p,\sigma_p)=(n-q+1,\beta)$: it is created at $\tau-1$ and branches at $\tau$. Thus both cases have the identical one-beta initial tree at the common cut. Alpha changes to beta, beta branches into one alpha and one beta, and neither rule updates newborns twice. Induction on further updates gives the local substitution and Fibonacci masses, with all physical letters retained. These two cases exhaust (NRW.1); a later beta label never replaces the immutable initial label. $\square$

**Definition 2.2 (one residual-only block decoder).** Fix positive $d$, an integer $s\ge1$ with $F_s\ge d$, and rank $q$ satisfying $q-s+1\ge3$. The decoder $\mathcal B_{q,s,d}$ takes only a complete rank-$q$ depth function. Start a local leaf roster with beta at the empty address, at normalized time zero. For normalized updates $k=1,\ldots,s$, enumerate its current beta leaves in physical lexicographic order. At each such address read the orientation from the complete function by Lemma 1.4; keep old branches, change old alpha to beta, and replace each old beta by the two initial child labels dictated by its decoded bit. Output the ordered bits at the first $d$ beta parents in update $s$. No creation descriptor, global index, prefix identity or source law is an input to this map. Its complete-function input is a mathematical argument, not a supplied observer register or a free physical observation; this definition imposes no acquisition-cost bound.

**Lemma 2.3 (full-domain chronological correspondence).** For every actual rank-$q$ cone $p$ at cut $n$ satisfying Definition 2.2, $\mathcal B_{q,s,d}(D_{n,p})$ is exactly a consecutive global output block

$$
 (z_{J_p},z_{J_p+1},\ldots,z_{J_p+d-1})
 \quad\text{born in update }t=n-q+s+1.
 \tag{NRW.5}
$$

Every decoded orientation has final rank at least $q-s+1$. For prefix-incomparable cones of the same rank, their intervals in (NRW.5) are disjoint and their $J_p$ differ. In particular, equality of complete residuals forces equality of these blocks even for mixed creation descriptors.

*Proof.* Lemma 2.1 identifies normalized time zero with the actual cut $\tau-1=n-q+1$. Induct on normalized updates, asserting equality of the decoder's labelled leaf roster with the actual old leaves in the cone, at the same relative physical addresses. The assertion holds at time zero. If a beta parent branches in normalized update $k$, its actual branch time is $\tau-1+k$, and its final rank, by (NRW.4), is

$$
 r=n-(\tau-1+k)+2=q+1-k\ge q+1-s\ge3.
 \tag{NRW.6}
$$

Its complete-function orientation is consequently its actual birth bit. Updating all and only the old leaves gives exactly the next actual roster. All parents exist at the final cut because their branch times are at most $n-1$. This proves the induction for every allowed descriptor and orientation history. Immediately before update $s$ there are $F_s\ge d$ beta leaves. All global beta leaves beginning with $p$ form one lexicographic interval, since beta leaves are prefix-incomparable. The actuator consumes one consecutive stream segment on this interval during that actual update; selecting its first $d$ entries gives (NRW.5). No other cone's entries interleave it. Prefix-incomparable cones give disjoint intervals at the same update $t$. Finally the decoder has one input domain and one rule, so equal input functions give equal output blocks. $\square$

**Theorem 2.4 (same-source phase separation).** Let

$$
 g(X)=X^d+\sum_{i=0}^{d-1}c_iX^i
 \tag{NRW.7}
$$

be primitive over $\mathbb F_2$, and let $z$ be the nonzero stream satisfying $z_{j+d}=\sum_{i<d}c_i z_{j+i}$ for every $j\ge1$, aligned to the first birth. Let $T=2^d-1$. For any one actual cut $n$ with $B_n<T$, any $s$ with $F_s\ge d$, and prefix-incomparable rank-$q$ cones with $q-s+1\ge3$, their complete integer residuals are pairwise distinct.

*Proof.* The companion state is the ordered consecutive window $(z_j,\ldots,z_{j+d-1})$. A primitive characteristic polynomial has nonzero constant term, so the shift is invertible. On every nonzero seed its orbit has period $T$ and visits each nonzero state exactly once. These are the nonsingular primitive-LFSR facts in Menezes–van Oorschot–Vanstone, [*Handbook of Applied Cryptography*, Chapter 6][HAC], §6.2.1, Facts 6.9, 6.11–6.12; its connection-polynomial convention may use the reciprocal of (NRW.7), also primitive. Thus two equal length-$d$ consecutive output windows have starting indices congruent modulo $T$. Lemma 2.3 makes equal residuals give equal such windows. Their distinct starts satisfy $1\le J_p\le J_p+d-1\le B_n<T$, which precludes that congruence. The polynomial, seed, actual source and cut are the same for all cones. $\square$

## 3. One mature cut and a common physical layer

**Lemma 3.1 (all-degree numerical slack).** For every integer $d\ge32$, put

$$
 s_d=\min\{s\ge4:F_s\ge d\},\quad
 h_d=\lfloor d/8\rfloor,\quad
 n_d=d+2h_d+4.
 \tag{NRW.8}
$$

Then

$$
 \begin{gathered}
 s_d\le2\lceil\log_2d\rceil+2,\qquad s_d\le d-4,\qquad n_d\le5d/4+4,\\
 B_{n_d}=F_{n_d+1}-1<2^d-1,\qquad F_{n_d}-1\ge2d,\\
 q\ge d+4\ \Longrightarrow\ q-s_d+1\ge9.
 \end{gathered}
 \tag{NRW.9}
$$

*Proof.* $F_{m+2}\ge2F_m$ for $m\ge1$, so $F_{2k+2}\ge2^k$ for $k\ge0$. Take $k=\lceil\log_2d\rceil$. Also $F_{28}=317811\ge32$, and $F_{m+1}\ge F_m+1$ for $m\ge2$. Induction gives $F_{d-4}\ge d$ for all $d\ge32$, proving the second bound and then the rank margin. The bound on $n_d$ follows from $\lfloor d/8\rfloor\le d/8$.

For the period bound, $\varphi=(1+\sqrt5)/2<13/8$ since $\sqrt5<9/4$, and $F_m<\varphi^m$ for $m\ge1$ follows by the Fibonacci recurrence. Write $a_d=n_d+1=d+2\lfloor d/8\rfloor+5$. The base rational inequality is

$$
 \begin{aligned}
 13^{45}
 &=134106816713249934153658112422086110743809315028093\\
 &<187072209534799430564191535264372276764693034434560
 =(2^{32}-1)8^{45}.
 \end{aligned}
 \tag{NRW.10}
$$

For $32\le d\le39$, $a_d=45+(d-32)$; increasing $d$ multiplies the left rational power by $13/8<2$ and the right side $2^d-1$ by more than two. This proves those eight base cases. For every $d$, $a_{d+8}=a_d+10$, and

$$
 13^{10}=137858491849<274877906944=2^8\,8^{10},\qquad
 2^{d+8}-1>2^8(2^d-1).
 \tag{NRW.11}
$$

Induction in each residue class modulo eight proves $(13/8)^{a_d}<2^d-1$ for all $d\ge32$, and hence the stated period slack. Finally $F_{32}=2178309\ge65$ and $F_{d+1}\ge F_d+2$ for $d\ge32$, so $F_d\ge2d+1$ by induction. Since $n_d\ge d$, maturity follows. $\square$

**Theorem 3.2 (exponential integer residuals in one native layer).** For every $d\ge32$, fix any one primitive degree-$d$ polynomial and any nonzero seed, giving one actual source from Definition 1.1. Use (NRW.8), set $k_d=\lfloor h_d/2\rfloor$ and

$$
 q_d=n_d-h_d-k_d,\qquad
 \mathcal P_d=\{p\in\{a,b\}^{h_d}:\kappa_{n_d}(p)=q_d\},\qquad
 N_d=\binom{h_d}{k_d}.
 \tag{NRW.12}
$$

At this one mature cut all length-$h_d$ words are branches, and

$$
 |\mathcal P_d|=N_d\ge\left\lceil\frac{2^{h_d}}{h_d+1}\right\rceil,
 \qquad q_d\ge d+4,
 \qquad D_{n_d,p}\ne D_{n_d,p'}\quad(p\ne p').
 \tag{NRW.13}
$$

Both immutable descriptor types occur in $\mathcal P_d$: $(n_d-q_d,\alpha)$ occurs $\binom{h_d-1}{k_d-1}$ times, and $(n_d-q_d+1,\beta)$ occurs $\binom{h_d-1}{k_d}$ times.

*Proof.* Primitive degree-$d$ polynomials exist for every $d$: a generator of the cyclic group $\mathbb F_{2^d}^{\times}$ has degree $d$ over $\mathbb F_2$ and primitive minimal polynomial. Fix one such polynomial and one nonzero seed throughout. Along any direction prefix of length at most $h_d$, rank is at least $n_d-2h_d=d+4$, so every such position is a branch. At each edge the choices of rank drop one or two are in bijection with the two physical letters at that actual branch. This gives a bijection from all physical words of length $h_d$ to all sequences of $h_d$ rank drops. Exactly $\binom{h_d}{k}$ of them have $k$ drops of two, and final rank $n_d-h_d-k$. The central coefficient gives (NRW.13)'s count. If the last drop is two the final initial label is alpha; if it is one the initial label is beta. Counting the preceding drops gives the two stated descriptor counts, which are positive since $h_d\ge4$ and $1\le k_d<h_d$.

Lemma 3.1 supplies maturity, $B_{n_d}<2^d-1$, and $q_d-s_d+1\ge9$. All selected cones are prefix-incomparable and have the common branch time $n_d-q_d+2$. Apply Theorem 2.4 with $s=s_d$. The beta/alpha mixture is inside the domain of the single decoder, with no class removed. $\square$

**Proposition 3.3 (identical fair-tape depth laws).** At any rank $q$, the probability generating polynomial of depth on an independent fair tape of sufficient length is

$$
 G_0(x)=G_1(x)=1,\qquad
 G_q(x)=\frac{x}{2}\bigl(G_{q-1}(x)+G_{q-2}(x)\bigr)\quad(q\ge2).
 \tag{NRW.14}
$$

Consequently all $N_d$ residuals of Theorem 3.2 have the same law, despite being pointwise distinct.

*Proof.* At each reached branch the next fair physical direction chooses the two child ranks equiprobably. Swapping their physical order changes neither this sum nor the independent suffix law. Induction with the two terminal ranks proves (NRW.14). Its first derivative at one agrees with [ACR Theorem 13.2][ACR]'s rank-only mean. $\square$

## 4. A bounded deficit and one fixed threshold

**Lemma 4.1 (first differing update and its depth deficit).** For any two distinct $p,p'\in\mathcal P_d$, there are a normalized update $k\le s_d$, a common relative beta-parent address $v$ with $|v|\le k-1$, and a tape $u$ such that, in one order of the pair,

$$
 D_{n_d,p}(u)=q_d-1-c,
 \qquad D_{n_d,p'}(u)\le q_d-2-c,
 \qquad 0\le c\le |v|\le s_d-1.
 \tag{NRW.15}
$$

Here $c$ is exactly the number of rank drops of two along the common prefix $v$.

*Proof.* The two length-$d$ blocks from normalized update $s_d$ have different global starts below one primitive period, so they differ. If every orientation assigned during normalized updates $1,\ldots,s_d$ agreed on the common beta rosters, the roster induction of Lemma 2.3 would make these two ordered blocks equal. Therefore choose the first differing normalized update $k\le s_d$. Agreement through update $s_d-1$ alone would not suffice for that implication; the selected block is assigned in update $s_d$ itself.

All earlier rosters and orientations agree at common physical addresses. Choose a beta parent $v$ whose bit differs in update $k$. Starting from a single beta at normalized time zero, each update can increase relative physical depth by at most one, since it does not revisit newborns. A parent before update $k$ thus has depth at most $k-1$. Along the proper prefixes of $v$, the two final ranked trees agree: those branches were created in earlier updates. If $c$ edges of $v$ drop rank by two, its rank in both trees is $r=q_d-|v|-c=q_d+1-k\ge q_d+1-s_d\ge9$.

Choose at $v$ the physical child of rank $r-1$ in the first cone, which has rank $r-2$ in the second. In the first cone continue by its larger-rank child at every later branch. The tail after this chosen edge has exactly $r-2$ edges there; any tail in the second has at most $r-3$. Thus the first complete path has length $|v|+1+(r-2)=q_d-1-c$, and the second at most $q_d-2-c$. Extend the chosen direction word arbitrarily to the common horizon; Lemma 1.3 makes the extension immaterial. This proves (NRW.15), including differences first assigned in the selected update itself. $\square$

**Definition 4.2 (fixed Boolean profiles).** For an integer $t$, let

$$
 \Theta_{p,t}(u)=\mathbf1\{D_{n_d,p}(u)\ge t\},\qquad
 \mathcal T_d=\{q_d-1-c:0\le c<s_d\}.
 \tag{NRW.16}
$$

Each $t$ defines one Boolean function on direction tapes. It is a fixed parameter of that function, not a coordinate supplied with a suffix.

**Theorem 4.3 (one fixed threshold has superpolynomial width).** In the one source, cut and physical layer of Theorem 3.2, there exist a single $t_d\in\mathcal T_d$ and a subset $\mathcal Q_d\subseteq\mathcal P_d$ such that

$$
 \begin{gathered}
 |\mathcal Q_d|\ge N_d^{1/s_d}
 \ge2^{(h_d-\log_2(h_d+1))/s_d},\\
 \Theta_{p,t_d}\ne\Theta_{p',t_d}\quad(p,p'\in\mathcal Q_d,\ p\ne p').
 \end{gathered}
 \tag{NRW.17}
$$

For every $d\ge64$ this implies the explicit lower bound

$$
 |\mathcal Q_d|\ge2^{d/(96\log_2d)}.
 \tag{NRW.18}
$$

*Proof.* Lemma 4.1 shows that the tuple $(\Theta_{p,t})_{t\in\mathcal T_d}$ is injective on the entire mixed-descriptor set $\mathcal P_d$. If $M_t$ counts its distinct profiles at threshold $t$, then

$$
 N_d\le\prod_{t\in\mathcal T_d}M_t.
 \tag{NRW.19}
$$

Since $|\mathcal T_d|=s_d$, some $M_{t_d}\ge N_d^{1/s_d}$. Choose one prefix for each of those profiles. The threshold is then fixed across every prefix and continuation of this instance. No threshold input is introduced.

For $d\ge64$, $h_d\ge8$ and $h_d\ge d/16$. The integer inequality $\log_2(h+1)\le h/2$ holds for $h\ge6$: its base is $7\le8$, and $\sqrt2(h+1)\ge h+2$ gives its induction step. Moreover Lemma 3.1 gives $s_d\le2\log_2d+4\le3\log_2d$. Therefore $(h_d-\log_2(h_d+1))/s_d\ge d/(96\log_2d)$. The bound dominates every fixed power of $d$, since $d/(\log_2d)^2$ tends to infinity. $\square$

**Proposition 4.4 (integer separation alone is insufficient).** For each $m\ge1$, the $2^m$ integer functions

$$
 A_x(j,c)=2j+(c\mathbin{\mathsf{xor}}x_j),\qquad
 x\in\{0,1\}^m,\quad 1\le j\le m,\ c\in\{0,1\},
 \tag{NRW.20}
$$

are pairwise distinct with identical uniform distributions. For each fixed threshold their Boolean profiles number at most two. Thus a conclusion like (NRW.17) needs additional structure beyond distinct integer residuals and equal laws.

*Proof.* For each $j$, changing $x_j$ interchanges the two values $2j,2j+1$. This preserves their multiplicities and changes the function. A threshold can separate these two values for at most one $j$; all other pairs lie wholly on one side. Only that one bit of $x$ affects the threshold profile. This family is an abstract counterexample to the generic inference, not an alternative native source. The native implication uses Lemma 4.1's small set of depth deficits. $\square$

## 5. Sequential output contracts and bit bounds

**Definition 5.1 (direction-order sequential representation).** For the fixed source and cut of Theorem 3.2, consider a deterministic sequential machine that consumes a length-$H_{n_d}$ tape in order. Its complete retained state after $h_d$ directions includes every mutable field that can affect the output, including control position, counters, accessible prefix summaries and any retained work. The transition after that layer depends only on this state and the remaining directions; it has no new source reply or auxiliary threshold input. Let $w_{h_d}$ be the number of distinct such states reached at that layer. For a retained binary encoding using $b_{h_d}$ bits, $2^{b_{h_d}}\ge w_{h_d}$. Source-specific constant code is allowed, but any prefix-dependent code position is part of the state.

There are two output contracts. The integer contract outputs $D_{n_d,\varepsilon}^{H_{n_d}}$. The fixed Boolean contract outputs

$$
 F_d(u)=\mathbf1\{D_{n_d,\varepsilon}^{H_{n_d}}(u)\ge h_d+t_d\},
 \tag{NRW.21}
$$

where the one threshold is fixed by Theorem 4.3 before any input tape is supplied. A strict pointwise approximation to a specified contract $F$ is a real output $A(u)$ satisfying $|A(u)-F(u)|<1/2$ for every tape $u$.

**Theorem 5.2 (native state and bit consequences).** Under the integer contract, exact output or strict pointwise approximation to that integer depth requires

$$
 w_{h_d}\ge N_d,\qquad
 b_{h_d}\ge\lceil\log_2N_d\rceil
 \ge\left\lceil h_d-\log_2(h_d+1)\right\rceil.
 \tag{NRW.22}
$$

Under the single fixed Boolean contract (NRW.21), exact output or strict pointwise approximation to that Boolean output requires

$$
 \begin{gathered}
 w_{h_d}\ge |\mathcal Q_d|\ge N_d^{1/s_d},\\
 b_{h_d}\ge\left\lceil\frac{\log_2N_d}{s_d}\right\rceil
 \ge\left\lceil\frac{h_d-\log_2(h_d+1)}{s_d}\right\rceil,\\
 d\ge64\ \Longrightarrow\quad
 w_{h_d}\ge2^{d/(96\log_2d)},\qquad
 b_{h_d}\ge\left\lceil\frac{d}{96\log_2d}\right\rceil.
 \end{gathered}
 \tag{NRW.23}
$$

*Proof.* After the prefixes $\eta(p)$ at the common layer, (NRW.3) identifies root integer cofactors with $h_d$ plus the local residuals on the shorter suffix domain. Two distinct members of $\mathcal P_d$ have a common suffix on which these integers differ, by Theorem 3.2 and padding independence. If their retained states merged, their outputs on that same suffix would agree, contradicting exactness. For real approximation, the open intervals of radius $1/2$ around two distinct integer answers are disjoint, giving the same contradiction. Thus there are at least $N_d$ states.

For (NRW.21), the common offset cancels in the comparison: the root cofactor at $\eta(p)$ is exactly $\Theta_{p,t_d}$ on the shorter suffix domain. Distinct members of $\mathcal Q_d$ therefore need distinct states. Pointwise error strictly below $1/2$ is now error to these Boolean values: the open intervals about zero and one are disjoint. Taking binary logarithms and integer ceilings proves (NRW.22)–(NRW.23). This is the fixed-order residual principle underlying Bryant, [*Graph-Based Algorithms for Boolean Function Manipulation*][BRYANT], §§1.1–2 and Theorem 1, applied to these native cofactors. The Boolean state lower bound is superpolynomial; its bit consequence is $\Omega(d/\log d)$. The stronger integer contract has the separate $\Omega(d)$ bit bound (NRW.22). Neither bound asserts exponentially many bits. $\square$

**Definition 5.3 (unresolved acquisition and normalization).** Retain the full all-index class $\mathscr R_d$ and unknown mature cut of [GPO §§29,34][GPO] and [ACR §§9–14][ACR]. The acquisition question asks for authentic $P=z_1\cdots z_{2d}$, the actual $n,B_n$, and the original fixed $K_d(P)$, with uniform polynomial TOTAL preparation, local bit work, literal traffic, writes and owned backing on every allowed input. Theorems 3.2–5.2 concern a direction-order representation at one cut inside this class. They do not decide whether adaptive presence acquisition, different variable orders, arithmetic evaluation or sign-correct comparison methods attain that acquisition bound. Sign correctness of a difference of estimated means is a different requirement from either pointwise contract of Definition 5.1; the hypotheses and conclusions are not identified. Necessity of the $4^d$ source catalogue, general polynomial acquisition, and polynomial computation of the original canonical $K_d$ remain unresolved.

## 6. Exact representations and a chronological example

**Proposition 6.1 (adequacy of finite signatures).** For sufficient horizon, a complete integer depth residual can be represented by the finite signature

$$
 S(\text{terminal})=\bot,\qquad
 S(\text{branch with children }A,B)=(S(A),S(B)).
 \tag{NRW.24}
$$

Equality of these signatures is equivalent to equality of the complete depth functions. A Boolean threshold cofactor has an exact finite representation obtained by recursively retaining the current direction position and its two child cofactors, replacing equal child cofactors by their common value and retaining constants zero and one. For a fixed direction order, equality of the resulting signatures is equivalent to equality of the complete Boolean functions. Leaf-depth multiplicities $a_j$ represent the fair law exactly by $\Pr(D=j)=a_j2^{-j}$.

*Proof.* The forward implication for integer signatures follows by evaluating the same tree on each tape. Conversely the complete depth function determines the finite ordered terminal/branch tree by Lemma 1.4; induction gives its signature. For Boolean functions, apply Shannon's two-cofactor identity at each remaining position. Equal children remove an irrelevant position; distinct children retain both their values and the actual position, so functions with different relevant positions are not conflated. Induction on the remaining horizon proves canonicity and adequacy. These are the usual reduced fixed-order cofactors of [Bryant][BRYANT]; no enumeration of a $2^H$ tape cube is needed for this representation. Finally the independent fair tape reaches each depth-$j$ leaf with probability $2^{-j}$, giving the law formula. $\square$

**Proposition 6.2 (agreement before an update does not fix that update).** Use the degree-five recurrence $z_{j+5}=z_j+z_{j+2}$ with initial outputs $(1,0,0,0,0)$, and its actual lexicographic source. At cut $n=16$ the physical prefixes $p=\mathrm{aaaba}$ and $p'=\mathrm{ababa}$ both have immutable descriptor $(8,\alpha)$ and rank eight. Their common branch time is ten, and their beta-origin time is nine. Their complete orientation records through normalized update three agree; in normalized update four the records differ. At global update fourteen, the first five beta-parent birth bits below them are respectively $00111$ and $10001$, starting at global indices $385$ and $453$.

*Proof.* For every parent $w$, its actual index is [GPO Proposition 39.2][GPO]'s

$$
 j_w=F_{\tau_w}-1+1+
 \sum_{\substack{vc\preceq w\\c=b}}
 \lambda_{\sigma_{va}}(\tau_w-1-\tau_v),
 \quad\lambda_\alpha(e)=F_e,\quad\lambda_\beta(e)=F_{e+1}.
 \tag{NRW.25}
$$

The recurrence can equivalently be evaluated as $z_j=[X^0](X^{j-1}\bmod(X^5+X^2+1))$. At each traversed branch use its resulting bit to place beta at $a$ exactly for one, alpha at the other child. Applying (NRW.25) to the proper prefixes gives

$$
 \begin{array}{c|ccccc}
 w&\varepsilon&a&aa&aaa&aaab\\\hline
 (b_w,\sigma_w)&(0,\alpha)&(2,\beta)&(3,\alpha)&(5,\alpha)&(7,\beta)\\[2pt]
 w&\varepsilon&a&ab&aba&abab\\\hline
 (b_w,\sigma_w)&(0,\alpha)&(2,\beta)&(3,\beta)&(4,\alpha)&(6,\alpha)
 \end{array}
 \tag{NRW.26}
$$

Both final alpha children are created at eight. The following pairs $(v,z_{j_{pv}})$ specify the whole normalized records in each indicated update, in physical order:

$$
 \begin{array}{c|c|c}
 k&\text{below }p&\text{below }p'\\\hline
 1&(\varepsilon,0)&(\varepsilon,0)\\
 2&(b,0)&(b,0)\\
 3&(a,1),(bb,1)&(a,1),(bb,1)\\
 4&(aa,0),(ba,0),(bba,1)&(aa,1),(ba,0),(bba,0)
 \end{array}
 \tag{NRW.27}
$$

For the next update $k=5$, the first parent lists are $(aab,ab,bab,bbaa,bbb)$ and $(aaa,ab,bab,bbab,bbb)$. Since $F_{14}-1=376$, the sibling-mass sums in (NRW.25) for their first entries are respectively eight and seventy-six, giving $J_p=385$ and $J_{p'}=453$. Prefix intervals make the next four indices consecutive. The recurrence gives $(z_{385},\ldots,z_{389})=00111$ and $(z_{453},\ldots,z_{457})=10001$. The records (NRW.27) prove the pre-update agreement and next-update difference; they are an indexing example at degree five, not a replacement for the all-$d\ge32$ theorem. $\square$

**Definition 6.3 (supplier correspondence).** The beta-origin synchronization, its residual-only consecutive-block correspondence, and the bounded-deficit native consequence (NRW.17) are repo-derived statements with proofs above. The LFSR and fixed-order cofactor principles used in their proofs are literature-attested by [HAC §6.2.1][HAC] and [Bryant §§1.1–2][BRYANT]. Their standard forms alone do not state the native-source correspondence proved in Lemmas 2.1–2.3. No claim of global literature novelty is attached to this source-specific consequence.

The existing formal source [GenealogicalFiberTransport.lean](../../../D5/S3/Arith/FibonacciAtomic/GenealogicalFiberTransport.lean), especially `substitution`, `decompose`, `assemble` and `sourceEquiv`, supplies ordered semantic leaf substitution and its labelled-shape correspondence. [ActualFibonacciSupportChain.lean](../../../D5/S3/Arith/FibonacciAtomic/Observer/ActualFibonacciSupportChain.lean), `actual_fibonacci_support_chain`, supplies the actual ordered-support recurrence and finite-prefix limitation in its semantic address domain. These declarations do not identify those ordered semantic ports with the hidden local physical ports here. Equations (NRW.1), (NRW.25) use the physical correspondence of GPO §§27,39 and ACR §§2,10,13 instead. The direction-order residuals retain that physical order; neither the semantic suppliers nor their mathematical inverses acquire a missing source binding, label sensor, generator state, law or cut.

[GPO]: RECURSIVE_RELATIONAL_OBSERVATION_ATOMIC_GLOBAL_PORT_ORIENTATION.md
[ACR]: RECURSIVE_RELATIONAL_OBSERVATION_ACTUAL_CUT_REINSTATEMENT.md
[HAC]: https://cacr.uwaterloo.ca/hac/about/chap6.pdf
[BRYANT]: https://www.cs.cmu.edu/~bryant/pubdir/ieeetc86.pdf

## 追加锚（本行以下为增补区）
