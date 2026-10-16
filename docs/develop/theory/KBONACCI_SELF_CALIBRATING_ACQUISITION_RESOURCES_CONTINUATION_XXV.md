# Self-calibrating acquisition resources XXV: final-label capacity and necessary blind stock

## 384. Complete allocations at literal affine mass

**Definition 384.1 (Finite and original objects).** Use the original source $X$, replies $q_i$, first absence $n(x)$, distinct carrier marks $\theta_j$, and classes $\mathcal N_2,\mathcal O_2$ of [XXIII 368.1](KBONACCI_SELF_CALIBRATING_ACQUISITION_RESOURCES_CONTINUATION_XXIII.md#368-original-resources-complete-cells-and-signed-scores). Thus $X$ is the countable Fibonacci-window divisibility source, every finite Boolean pattern has an actual witness, and the selected target for an entire profile $1\ge a_1\ge a_2\ge\cdots>0$, $a_i\to0$, is

$$
\lambda_x^a=(1-a_{n(x)})\delta_{\theta_0}+a_{n(x)}\delta_{\theta_{n(x)}},
\qquad e_a(A)=\sup_{x\in X}\operatorname{TV}(\nu_{A,x},\lambda_x^a).
$$

Both original classes have zero advice, one source-independent seed fixing the whole schedule and every counterfactual terminal output before replies, and measurable sourcewise almost-sure finite handoff. The hard bound is two actual requests, counting repetitions and acquired replies later ignored. In $\mathcal N_2$ the entire preselected schedule is acquired; in $\mathcal O_2$ the preselected increasing schedule stops at its first queried zero or exhaustion. Addresses and full-carrier outputs of original competitors are unrestricted. Source-dependent information consists only of the acquired replies; terminal choice uses those replies and the seed. The unchanged consumer receives the original handed tape on the same source. These are the interfaces of [108–110](KBONACCI_SELF_CALIBRATING_ACQUISITION_RESOURCES_CONTINUATION.md#108-common-probability-vector-kernels-and-stopped-schedules) and [Source-Correlated Laws 45](KBONACCI_SELF_CALIBRATING_SOURCE_CORRELATED_LAWS.md#45-lawful-acquisition-through-one-inherited-seed).

For an integer $L\ge3$, let $B_L=\{0,1\}^L$ and $J_L=\{0,\ldots,L\}$. The complete catalog in either class contains the empty schedule, every singleton, and every pair $i<j$. An $N$ pair has cells $00,01,10,11$; an $O$ pair has cells $0,10,11$, where $0$ means $w_i=0$ regardless of $w_j$. Write $c_s(w)$ for the cell visited by $w$ in schedule $s$. A complete allocation consists of vectors $X_{s,c}\ge0$ on $J_L$ and owning masses $m_s\ge0$ satisfying

$$
\sum_{z=0}^L X_{s,c}(z)=m_s\quad\text{for every cell }c\text{ of }s,
\qquad \sum_s m_s=M,\qquad
p_w=\sum_sX_{s,c_s(w)}.
\tag{384.1}
$$

Every word, cell and label is retained, including multiple-zero words, unqueried output labels and zero-mass schedules. At $M=1$ the common-interval-seed realization of XXIII 368.2 turns these vectors into an original procedure. At other finite masses $M\ge0$ they are literal affine allocations.

For real $b_j\ge0$ and $e\ge0$, feasibility means the separate inequalities $p_w(0)\ge d_A(w)$, $p_w(n(w))\ge d_C(w)$, $p_w(0)+p_w(n(w))\ge d_P(w)$ at every zero word, and $p_{1^L}(0)\ge d_T$, with

$$
\begin{array}{c|cc}
 &d_A(w)&d_C(w)\\ \hline
n(w)\le2&1-b_{n(w)}-e&M-1+b_{n(w)}-e\\
3\le n(w)\le L&M-b_{n(w)}-e&b_{n(w)}-e
\end{array}
\qquad d_P(w)=d_T=M-e.
\tag{384.2}
$$

These are exactly $d(b,e)+(M-1)r$ for the anchor $R=O(1,2;1,2,0)$, $r=z(R)$ of XXIII 368.3. Singleton floors remain signed and the union floor is independent. Division by $M$ is not part of this definition.

**Definition 384.2 (Collapsed allocations and simultaneous stock).** Put $w^*=1^{L-1}0$, $w^+=1^L$, and $c_s^*=c_s(w^*)$. For $\mathcal C=N,O$, let $K_{\mathcal C}=K_{\mathcal C}(b_{<L},e,M)$ be the complete mass-$M$ allocations $k$ on all $L$ addresses with output labels $0,\ldots,L-1$ which satisfy every row of (384.2) at every word with $n(w)<L$, and

$$
k_{w^*}(0)\ge M-e,\qquad k_{w^+}(0)\ge M-e.
\tag{384.3}
$$

No cell, mass or output law in this set is fixed in advance. In particular both last-bit endpoints occur among its earlier-word constraints. For one such whole allocation put

$$
\begin{aligned}
a_s&=k_{s,c_s^*}(0),& I_s(w)&=\mathbf1_{c_s(w)=c_s^*},\\
s_w(k)&=\min\{k_w(0)-d_A(w),\ k_w(0)+k_w(n(w))-d_P(w)\}
&& (n(w)<L),\\
s_+(k)&=k_{w^+}(0)-(M-e).
\end{aligned}
$$

Let $\operatorname{cap}(k)$ be the maximum of $\sum_s x_s$ subject to

$$
0\le x_s\le a_s,\qquad
\sum_s I_s(w)x_s\le s_w(k)\quad(n(w)<L),\qquad
\sum_s I_s(w^+)x_s\le s_+(k).
\tag{384.4}
$$

Define $\nu_{\mathcal C}=\max_{k\in K_{\mathcal C}}\operatorname{cap}(k)$, with $\nu_{\mathcal C}=-\infty$ when $K_{\mathcal C}$ is empty. Every loss in (384.4) uses the same $k$ and the same stock vector $x$.

The distinguished cells are the empty cell, an old singleton's $1$ cell, an old pair's $11$ cell, singleton $L$'s $0$ cell, and pair $(i,L)$'s $10$ cell. Their indicators $I_s$ agree in the two catalogs. Schedules omitting $L$ may therefore fund label $L$ in their positive cells; no query-$L$ restriction is imposed.

## 385. Whole-allocation capacity and the hull slice

**Theorem 385.1 (Final-label capacity equivalence).** For every finite $L\ge3$, $\mathcal C\in\{N,O\}$, finite real $M\ge0$, $b_j\ge0$ and $e\ge0$, complete $\mathcal C$ feasibility for (384.2) is equivalent to

$$
\nu_{\mathcal C}(b_{<L},e,M)\ge\delta,
\qquad \delta=(b_L-e)_+.
\tag{385.1}
$$

If $K_{\mathcal C}$ is nonempty, its capacity belongs to $[0,M]$ and is attained by one whole allocation and one stock vector.

*Proof.* Start with a feasible allocation $p$. Move every label-$L$ entry in a cell other than $c_s^*$ to label $0$. Such a cell is never visited by the unique first-zero-$L$ word $w^*$. At every earlier zero word this leaves its correct coordinate unchanged and increases its base and union coordinates. The positive base also increases. Thus all rows remain feasible and every owning mass is unchanged.

Let $t$ be the remaining label-$L$ mass at $w^*$. Its correct row and nonnegativity give $t\ge\delta$. If $t>0$, retain the fraction $\delta/t$ of every remaining label-$L$ entry and move the rest to base. If $t=0$, then $\delta=0$ and no division is needed. Earlier rows again improve. At $w^*$ the union is unchanged, the correct mass becomes $\delta\ge b_L-e$, and base increases, so feasibility persists.

Collapse the remaining label $L$ into base and call the resulting allocation $k$. At $w^*$ its base is the preceding union, at least $M-e$, so $k\in K_{\mathcal C}$. Let $x_s$ be the label-$L$ entry just collapsed in $c_s^*$. Then $x_s\le a_s$ and $\sum_sx_s=\delta$. At an earlier word the allocation before collapse had base and union

$$
k_w(0)-\sum_sI_s(w)x_s,\qquad
k_w(0)+k_w(n(w))-\sum_sI_s(w)x_s.
$$

Their two independent floors imply (384.4); the positive row gives its last inequality. This proves necessity with one common stock.

Conversely, suppose a jointly admissible $(k,x)$ has stock total $t\ge\delta$. Use $x=0$ if $\delta=0$; otherwise $t>0$ and replace $x$ by $(\delta/t)x$. Every loss weakly decreases. In each $c_s^*$ move this stock from label $0$ to label $L$. The bound $x_s\le a_s$ preserves nonnegativity and every cell retains its owning mass. At earlier words correct coordinates are unchanged, while (384.4) pays both the base and union losses and the positive loss. At $w^*$ correct mass is $\delta$, union is $k_{w^*}(0)\ge M-e$, and base is at least

$$
M-e-\delta\ge M-b_L-e,
$$

since $\delta\le b_L$. These are all remaining rows, proving sufficiency.

For attainment, write the constraints jointly in all cell entries, owning masses and stocks. They are finitely many closed linear equalities and inequalities. Every entry lies in $[0,M]$, and $\sum_sx_s\le\sum_sm_s=M$. If $K_{\mathcal C}$ is nonempty, $x=0$ is admissible; hence the joint set is nonempty and compact, and its linear objective attains its maximum. In particular this proves the outer maximum asserted in Definition 384.2. At $M=0$ every entry is zero, so the capacity is either $0$ or $-\infty$ and the same proof applies without division. When $b_L\le e$, feasibility means precisely $K_{\mathcal C}\ne\varnothing$; empty feasibility is not zero capacity.

The transfers use the signed actual-slack principle of [XV 258](KBONACCI_SELF_CALIBRATING_ACQUISITION_RESOURCES_CONTINUATION_XV.md#258-signed-event-transfer-actual-slack-and-universal-common-input-maps) and [XXIII 371](KBONACCI_SELF_CALIBRATING_ACQUISITION_RESOURCES_CONTINUATION_XXIII.md#371-a-one-pass-normal-form-for-every-finite-complete-catalog). Unlike the fixed-complement calculation XXIII 372, the outer optimization here varies every complementary cell and mass. Completing stopped first cells into equal $00,01$ cells also gives $\nu_O\le\nu_N$, but the identical distinguished-cell incidence alone supplies no reverse inequality. $\square$

**Theorem 385.2 (Exact clipping of the remaining comparison).** Fix $L\ge4$, a real prefix and cap

$$
1\ge b_1\ge\cdots\ge b_{L-1}\ge e\ge0,\qquad b_2=b_3,
$$

and finite $M\ge1$. For the hull $H_L$ of XXIII (368.12), set

$$
S=\sum_{j=3}^{L-1}b_j,\qquad
\ell=\max\{0,Le-S\},\qquad
u=\min\{b_{L-1}-e,\ 1-b_1-S+Le\}.
\tag{385.2}
$$

If $\ell\le u$, same-mass $N$-to-$O$ feasibility inclusion on this entire last-coordinate slice is equivalent to the scalar condition

$$
\nu_N\ge\ell\quad\Longrightarrow\quad
\nu_O\ge\min\{\nu_N,u\}.
\tag{385.3}
$$

If $\ell>u$, the slice is empty. For a fixed $L\ge4$, imposing (385.3) for every such real prefix, cap and finite $M\ge1$ is equivalent to the clipped affine comparison $\rho_O(b,e)\le\max\{1,\rho_N(b,e)\}$ on every $(b,e)\in H_L$ with finite $\rho_N$, where $\rho_{\mathcal C}$ is minimum literal affine mass, or $+\infty$ for infeasibility. The validity of (385.3) for all required parameters at $L\ge8$ remains an open assertion.

*Proof.* Write $b_L=e+\delta$. Order gives $0\le\delta\le b_{L-1}-e$. The hull inequalities

$$
(L+1)e\le S+b_L,\qquad b_1+S+b_L-(L+1)e\le1
$$

give respectively $\delta\ge Le-S$ and $\delta\le1-b_1-S+Le$. Thus its exact last-demand interval is $[\ell,u]$. All remaining hull conditions concern only the fixed prefix and cap.

By Theorem 385.1 the feasible demands in class $\mathcal C$ are exactly $\{\delta\in[\ell,u]:\delta\le\nu_{\mathcal C}\}$, empty when $\nu_{\mathcal C}=-\infty$. If $\nu_N<\ell$ there is nothing to transfer. Otherwise the greatest feasible $N$ demand is $t=\min\{\nu_N,u\}$ and is attained. Inclusion forces $\nu_O\ge t$; conversely this inequality and stock scaling transfer every feasible $N$ demand. At $t=0$ it still forces $K_O\ne\varnothing$. No capacity above $u$ has to be transferred.

A finite minimum defining $\rho_{\mathcal C}$ is attained: bound the schedule mass by any feasible incumbent, making its finite complete-allocation set compact. Adding $tR$, $t\ge0$, raises mass by $t$ while preserving $z(p)-Mr$ and the same profile. Hence the clipped comparison supplies an $O$ witness of mass at most $M$ for every $N$ witness of mass $M\ge1$, and anchor padding makes its mass exactly $M$. Conversely pad a minimum-mass $N$ witness to $\max\{1,\rho_N\}$ and apply same-mass inclusion. This proves the claimed equivalence, including $\rho_N<1$ and $\rho_N=0$ without normalization.

The existing full signed Farkas bridge [VI 199.3–199.4](KBONACCI_SELF_CALIBRATING_ACQUISITION_RESOURCES_CONTINUATION_VI.md) connects this fully quantified clipped comparison to unrestricted shared score certificates. This use neither proves (385.3) nor chooses its missing certificate. At $L=3$, Theorem 385.1 still holds, but the free-last-coordinate hull interval must additionally be intersected with $\{b_2-e\}$ because $b_3=b_2$. $\square$

## 386. A charged last-label inequality

**Definition 386.1 (The fixed profile and blind stock).** Put

$$
b^*=\frac1{64}(43,34,34,29,27,25,22,20),\qquad
c=\frac{2867}{11856},\qquad E=\frac{421}{1728}.
\tag{386.1}
$$

The unrestricted original $N$ and $O$ optimum $c$ at this prefix, for every entire positive ordered vanishing tail with $a_9\le c$, is the inherited result [XXIV 375–379](KBONACCI_SELF_CALIBRATING_ACQUISITION_RESOURCES_CONTINUATION_XXIV.md#375-the-eight-active-profiles). For a complete $L=8$ stopped allocation of finite mass $M$, define

$$
g_8(p)=\sum_{s:\,8\notin s}X_{s,+}(8),
\tag{386.2}
$$

where $+$ is the cell of $s$ visited by $1^8$. At mass one this is the probability on that word of outputting label $8$ with no query to address $8$.

**Theorem 386.2 (Necessary stock at every affine mass).** Every complete stopped allocation satisfying (384.2) at $L=8$, arbitrary $b_j\ge0$, $e\ge0$ and finite $M\ge0$ obeys

$$
4b_2+26b_3+34b_4+28b_5+34b_6+28b_7+54b_8
\le4+324e+20g_8(p).
\tag{386.3}
$$

In particular, at $b=b^*$ and $e\le c$, every such allocation has $g_8(p)\ge465/15808$. This stock is part of the same positive-word nonbase mass, which is at most $e$; the stock lower bound is not asserted sharp or sufficient for feasibility.

*Proof.* Use the nonnegative full score $Y$ whose only nonzero rows are the following $29$ entries. Row types and rewards are those of XXIII 368.4; every unlisted row retains weight zero.

$$
\begin{array}{c|c|r@{\qquad}c|c|r}
P&00110100&2&P&00111000&2\\
P&01001110&3&P&01010100&7\\
P&01011000&2&P&01011010&10\\
P&01100100&2&P&01100110&10\\
P&01101000&7&P&01110010&1\\
C&10000010&4&P&10001100&8\\
P&10001110&3&P&10010010&6\\
P&10010100&5&P&10100010&6\\
P&10101000&5&P&10110010&3\\
C&11000010&26&P&11000110&4\\
P&11001010&4&C&11100000&34\\
C&11110000&28&P&11110000&6\\
C&11111000&34&C&11111100&28\\
P&11111100&6&C&11111110&54\\
T&11111111&14&&&
\end{array}
\tag{386.4}
$$

Their totals are $\beta=(0,4,26,34,28,34,28,54)$, $K=324$, $C_0=116$ and $W_Y=120$. For each stopped cell let

$$
H_{s,d}(z)=\sum_{w:\,c_s(w)=d}f_Y(w,z)
 -20\mathbf1_{\{8\notin s,\ d=+,\ z=8\}}.
\tag{386.5}
$$

The following table gives $\max_{0\le z\le8}H_{s,d}(z)$ in every cell. The indexed rows enumerate all $37$ schedules; cell order is the empty cell, singleton $0,1$, or pair $0,10,11$.

$$
\begin{array}{c|c|c}
s&\text{charged cell maxima}&\text{sum}\\ \hline
\varnothing&(116)&116\\
(1)&(46,70)&116\\
(2)&(40,76)&116\\
(i),\ 3\le i\le7&(52,64)&116\\
(8)&(102,14)&116\\
(1,2)&(46,40,34)&120\\
(1,j),\ 3\le j\le7&(46,34,40)&120\\
(1,8)&(46,56,14)&116\\
(2,j),\ 3\le j\le7&(40,34,46)&120\\
(2,8)&(40,62,14)&116\\
(i,j),\ 3\le i<j\le7&(52,34,34)&120\\
(i,8),\ 3\le i\le7&(52,54,14)&120
\end{array}
\tag{386.6}
$$

These are finite integer identities from (386.4)–(386.5): a $P$ entry contributes its weight to labels $0,n(w)$ in its visited cell, a $C$ entry only to $n(w)$, and $T$ only to label $0$ in the positive cell; then the displayed charge is subtracted. Maximizing includes every one of the nine labels, including labels absent from the queried schedule. For example, in the empty cell the uncharged totals at labels $0,\ldots,8$ are $(116,46,40,34,34,34,34,34,54)$; its charged maximum is $116$.

Each cell's mass is its owning $m_s$, so (386.6) gives, for this same allocation,

$$
Y\cdot z(p)-20g_8(p)
=\sum_{s,d,z}H_{s,d}(z)X_{s,d}(z)\le120M.
$$

Pairing its same literal demands with $Y\ge0$ gives

$$
Y\cdot z(p)\ge116+\beta\cdot b-324e+120(M-1)
=120M-4+\beta\cdot b-324e.
$$

Cancellation proves (386.3), including $M=0$ with all signed floors retained. At $b^*$, $\beta\cdot b^*=1327/16$, so

$$
324e+20g_8(p)\ge\frac{1263}{16},\qquad
g_8(p)\ge\frac{1263/16-324c}{20}=\frac{465}{15808}
\quad(e\le c).
$$

Finally $p_{1^8}(0)\ge M-e$ and total word mass $M$ give $\sum_{j=1}^8p_{1^8}(j)\le e$, containing the very stock in (386.2).

This is a label-specific heterogeneous constraint. The plateau theorem [XIII 224.1–224.2](KBONACCI_SELF_CALIBRATING_ACQUISITION_RESOURCES_CONTINUATION_XIII.md) already forces total numerical exhaustion reserve, but does not force a particular last label to be guessed. Indeed for its $k\ge4$ and $s=3/(k+1)$, put mass $s$ uniformly on triples $\{i,k,\infty\}$ with $i<k$ and mass $1-s$ uniformly on triples among $1,\ldots,k-1$. Every old inclusion marginal is $[s+3(1-s)]/(k-1)=s$, and the $k,\infty$ marginals are $s$. Its inherited triple rule always queries $k$ when it outputs $k$. Thus that plateau reserve conclusion does not supply the last-label bound above. $\square$

## 387. Blind stock on actual sources

**Theorem 387.1 (Marked original-source consequence).** Let $a$ be any entire positive nonincreasing vanishing profile with $(a_1,\ldots,a_8)=b^*$ and $a_9\le c$. Every original $A\in\mathcal O_2$ with $e_a(A)\le c$ satisfies

$$
\sup_{x\in X:\,n(x)>8}
\mathsf P_A\{\text{output }\theta_8\text{ and no actual request to address }8\}
\ge\frac{465}{15808}.
\tag{387.1}
$$

No source attaining this supremum is required.

*Proof.* Refine the original-to-finite construction of Theorem 110.2 by retaining the acquired low schedule with its terminal table. Countability of $X$ supplies one conull seed event on which all actual executions obey their hard bound and hand off finitely. The whole preselected increasing schedule has length at most two and finite maximum address $A_S$ almost surely, by the original schedule normalization used in 110.2. Consequently $\gamma_m=\mathsf P(A_S>m)\to0$.

For each integer $m\ge9$, fix before seeds an actual witness $x_{w,m}$ for each $w\in B_8$, with low word $w$ and replies zero at addresses $9,\ldots,m$. Their existence is exactly [Boundaries 35.2](KBONACCI_SELF_CALIBRATING_BOUNDARIES.md#35-exact-finite-divisibility-fibres-in-canonical-fibonacci-windows), as used in 110.2; in particular $n(x_{1^8,m})=9$. For this finite witness family choose one transition cutoff $t_m$ whose late-handoff probability is at most $1/m$ on each member.

Simulate the rule with variable low word $w$ and these fixed higher replies, outputting base before an address above $m$, a third request or a transition beyond $t_m$. At a genuine handoff apply the measurable projection $\pi_8$ fixing $\theta_1,\ldots,\theta_8$ and sending every other tape to $\theta_0$. The coupling argument of 110.2 gives one common finite simulation with cap at most $c+\eta_m$ at all low words, where $\eta_m=\gamma_m+1/m\to0$.

The additional event must be preserved as well. For each seed keep the low acquired prefix along the positive low path and its table, rather than replacing the output function by an arbitrary law-equivalent schedule. Low addresses precede all higher addresses. A low zero stops before any higher request, and after a positive low exhaustion all remaining supplied replies are fixed. If a cutoff or early handoff shortens the positive path, omit its unperformed suffix. This yields one empty, singleton or increasing-pair low schedule: every word stopping earlier belongs to its usual stopped cell, and words continuing positively share its prescribed continuation. The deterministic simulation therefore has a complete stopped representation with its actual low requests retained. All these schedule/table possibilities form a finite measurable catalog, as in Source-Correlated Laws 45.3 and 110.2. Original repeated or ignored requests remain charged; their deletion from redundant static information is not a refund to the original rule.

On the agreement event at the positive witness, label $8$ is preserved exactly by $\pi_8$, and whether address $8$ was actually requested agrees with the retained low execution. Cutoff outputs are base and create no label-$8$ event. Thus the simulation's blind stock $g_m$ satisfies

$$
\left|g_m-\mathsf P_A\{\text{output }\theta_8,
\ \text{no request }8\mid x_{1^8,m}\}\right|\le\eta_m.
$$

The notation after the bar means execution at the specified source, not conditioning a source distribution. Applying (386.3) at mass one and cap $c+\eta_m$ yields

$$
g_m\ge\frac{465}{15808}-\frac{324}{20}\eta_m.
$$

The actual witness event is therefore at least $465/15808-(1+324/20)\eta_m$. Take the supremum over actual $n(x)>8$ and then let $m\to\infty$. Only actual finite witnesses occur; neither an infinite all-positive source nor attainment of the source supremum has been used. $\square$

## 388. The sharp query-8-only subclass

**Definition 388.1 (Only label $8$ requires its own query).** Let $\mathcal O_2^{[8]}$ consist of original $\mathcal O_2$ procedures for which, on every source almost surely, an output $\theta_8$ is preceded in that execution by an actual request to address $8$. No restriction is imposed on any other output label or on full-carrier outputs.

**Theorem 388.2 (Exact restricted optimum).** For every entire profile in Theorem 387.1,

$$
\min_{A\in\mathcal O_2^{[8]}}e_a(A)=E=\frac{421}{1728},
\qquad E-c=\frac{775}{426816}>0.
\tag{388.1}
$$

The minimum is attained by one complete normalized $23$-schedule rule. This is a restricted-class gap above the inherited unrestricted optimum $c$.

*Proof.* For the lower bound, let a competitor in this subclass have error $\varepsilon$. Apply the marked finite reduction in the proof of Theorem 387.1, with cap $\varepsilon+\eta_m$. Projection fixes $\theta_8$, and no simulation emits label $8$ before its retained actual query to $8$; cutoffs emit base. Its positive blind stock is consequently zero. Theorem 386.2 gives $324(\varepsilon+\eta_m)\ge1263/16$. Letting $m\to\infty$ gives $\varepsilon\ge421/1728$. Equivalently, compactness of the finite marked schedule/table simplex retains this restriction and the closed cap. This argument uses no assumption that other labels were queried, and applies to arbitrary original addresses and full-carrier outputs.

For attainment let $D=1728$. Every entry in the following table is an integer numerator over $D$, including the owning mass. Cells are in stopped order $0,10,11$, and $e_j$ is the unit label vector. All omitted schedules and cells have mass zero.

$$
\begin{array}{c|r|l|l|l}
s&Dm_s&DX^0&DX^{10}&DX^{11}\\ \hline
12&436&436e_1&436e_2&197e_0+103e_3+100e_4+36e_5\\
13&197&9e_0+188e_1&197e_3&197e_0\\
14&47&47e_1&47e_4&47e_0\\
15&36&36e_1&36e_5&36e_0\\
16&25&25e_1&25e_6&25e_0\\
17&8&8e_1&8e_7&8e_0\\
23&197&136e_0+61e_2&197e_3&197e_0\\
24&47&47e_0&47e_4&47e_0\\
25&36&36e_0&36e_5&36e_0\\
26&25&25e_0&25e_6&25e_0\\
27&8&8e_0&8e_7&8e_0\\
34&168&168e_0&168e_4&62e_0+80e_5+26e_6\\
35&51&51e_0&51e_5&51e_0\\
36&40&40e_0&40e_6&40e_0\\
37&23&23e_0&23e_7&23e_0\\
45&69&69e_0&69e_5&51e_0+11e_6+7e_7\\
46&40&40e_0&40e_6&40e_0\\
47&23&23e_0&23e_7&23e_0\\
56&87&87e_0&87e_6&29e_0+58e_7\\
57&23&23e_0&23e_7&23e_0\\
67&23&23e_0&23e_7&23e_0\\
68&65&65e_0&65e_8&65e_0\\
78&54&54e_0&54e_8&54e_0
\end{array}
\tag{388.2}
$$

All numerators are nonnegative, each cell sums to its owning mass, and the masses sum to $D$. Label $8$ occurs only in middle cells of $(6,8),(7,8)$, where address $8$ is actually queried. For every first-zero-$n$ word, summing its correct coordinate gives the constant $C_n/D$ in the following table. The base minima over the whole first-zero fiber, and hence the union minima, are also displayed in integer units of $1/D$.

$$
\begin{array}{c|r|r|r|c}
n&\min Dp_w(0)&C_n=Dp_w(n)&\min D(p_w(0)+p_w(n))&\text{a base minimizer}\\ \hline
1&567&740&1307&00101100\\
2&810&497&1307&10001100\\
3&810&497&1307&11000110\\
4&960&362&1322&11100010\\
5&999&308&1307&11110000\\
6&1063&254&1317&11111000\\
7&1134&173&1307&11111100\\
8&1188&119&1307&11111110
\end{array}
\tag{388.3}
$$

Here is an explicit finite expression for the minima, including all suffix zero patterns. Let

$$
A=(9,252,282,132,110,88,54,0),\qquad
B_{ij}=DX^{11}_{ij}(0),
$$

where $B_{ij}=0$ for an omitted pair and the other $B_{ij}$ are the base coefficients in (388.2). Every middle cell has zero base, so

$$
Dp_w(0)=\sum_{i=1}^8 A_i(1-w_i)+\sum_{i<j}B_{ij}w_iw_j.
\tag{388.4}
$$

For a first zero $n$, substitute $w_1=\cdots=w_{n-1}=1,w_n=0$ in (388.4). Its constant term is $\sum_{i\ge n}A_i+\sum_{i<j<n}B_{ij}$, its coefficient of $w_j$, $j>n$, is $\sum_{i<n}B_{ij}-A_j$, and its remaining pair coefficients are $B_{ij}$ for $n<i<j$. Successive Boolean minimization uses exactly $\min_{t\in\{0,1\}}(U+tV)=U+\min\{0,V\}$, pointwise in the remaining bits. These substitutions give the eight minima in (388.3); the listed words attain them. Correct coordinates are constant because every nonzero entry at label $n$ is visited identically on its first-zero fiber. Thus the union minimum is the sum of the first two numerical columns, rather than an independently chosen output law.

In units of $1/D$ the eight amplitudes are $(1161,918,918,783,729,675,594,540)$ and the cap is $421$. The correct demands are exactly $(740,497,497,362,308,254,173,119)$, the base demands are $1307$ minus those amplitude numerators, and the union demand is $1307$. Every row of (388.3) meets all three floors. The positive law is

$$
p_{1^8}=\frac{1307e_0+103e_3+100e_4+116e_5+37e_6+65e_7}{1728},
\tag{388.5}
$$

whose base is $1-E$. This proves every finite cap row in one complete allocation.

Realize (388.2) by the inherited interval-seed construction: the seed first selects a schedule interval and, within it, fixes all cell-label partitions by their common refinement before replies. Execute the chosen increasing pair on the actual primes and stop at its first queried zero. No second seed or free reply is used, and there are at most two actual paid requests. The label-$8$ restriction holds on every cell. For actual $n(x)\le8$, its entire low word satisfies the checked cap rows. For every actual $n(x)>8$, (388.5) emits no $\theta_{n(x)}$, and the inherited exact tail identity XXIII (373.1) gives

$$
\operatorname{TV}(p_{1^8},\lambda_x^a)
=\max\{1-p_{1^8}(0),a_{n(x)}\}
=\max\{E,a_{n(x)}\}=E.
$$

This uses the entire positive ordered vanishing tail $a_9\le c<E$, permits $a_9=c$ and all later ties, and requires no summability. It proves attainment and the matching lower bound. $\square$

## 389. The unrestricted assertion

**Definition 389.1 (The remaining comparison).** Retain the full scores, anchor excesses $\Delta_N,\Delta_O$, quotient map $Q$ and signed hull support $\sigma_{H_L}$ of XXIII 368.4. The unresolved universal assertion is: for every finite $L\ge8$ and every full $y\ge0$ with $\Delta_O(y)=1$, there exist one unrestricted full $V\ge0$ and the same $\theta\in[0,1]$ such that

$$
\Delta_N(V)+\theta\le1,\qquad
\sigma_{H_L}(Q(y)-Q(V))\le\theta.
\tag{389.1}
$$

Equivalently in the inherited clipped primal formulation, the still-missing step is (385.3) for every required real prefix, cap and finite $M\ge1$ at every $L\ge8$. Signed residuals, both $\theta$ endpoints and nonzero zero-$N$-excess $V$ remain permitted. Neither a fixed old allocation nor fixed endpoint laws or separately optimized stock coordinates constrain this assertion.

Its alternative is one entire positive ordered vanishing profile, one complete original common-seed $A_N\in\mathcal N_2$ attaining $c_0=e_a(A_N)$, and one $\varepsilon>0$ such that every original arbitrary-address/full-carrier $A_O\in\mathcal O_2$ has $e_a(A_O)\ge c_0+\varepsilon$. The necessary inequality (386.3) and the restricted optimum (388.1) establish neither alternative: the unrestricted stopped attainer of XXIV 376–379 remains feasible at $c$ on the very profile used here.

Original nonatomic-target accuracy and complete paid-$M1$ acquisition remain separate questions with their unchanged conditions. In particular a finite marked output law has TV distance one from an unchanged nonatomic target on the same carrier; none of the selected-law conclusions implies nonatomic accuracy.

The mathematical dependencies of the new capacity and stock deductions are the complete-table and original-source interfaces 108–110 and Source-Correlated Laws 45, the signed score/anchor definitions IX 207 and XXIII 368, the signed transfers XV 258 and XXIII 371, the fixed-complement tool XXIII 372, and the full clipped alternative VI 199.3–199.4. The unrestricted optimum and its attainer are reused from XXIV 375–379. Compactness, finite nonnegative score pairing and coordinate elimination are standard ingredients; compare Volker Kaibel, [*Basic Polyhedral Theory*, arXiv:1001.2161v1, Theorems 12 and 18](https://arxiv.org/abs/1001.2161v1). They are used inside these deductions, with no claim of a new general duality theorem or of literature priority for their methods.

## 追加锚（本行以下为增补区）
