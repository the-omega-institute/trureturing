# KBONACCI self-calibrating acquisition resources XXI: odd-list replacement and one-partition bounds

## 357. Original objects and complete allocations

Retain the source and resources of [Acquisition Resources 73.1 and 90.1](KBONACCI_SELF_CALIBRATING_ACQUISITION_RESOURCES.md#90-adaptive-preselected-and-increasing-first-zero-stop-acquisitions) and [Continuation 110.1–110.2](KBONACCI_SELF_CALIBRATING_ACQUISITION_RESOURCES_CONTINUATION.md#110-exact-closed-cap-transport-on-the-original-countable-source). Explicitly,

$$
\begin{aligned}
F_0&=0,\quad F_1=1,\quad F_{k+2}=F_{k+1}+F_k,\\
X&=\{(r,g):r\text{ prime},\ g\in\mathbb Z,
       \ \lceil F_r/10\rceil\le g\le\lfloor F_r/5\rfloor\},\\
N(r,g)&=1+F_rg,\qquad q_i(x)=\mathbf1_{p_i\mid N(x)},\qquad
n(x)=\min\{i:q_i(x)=0\},
\end{aligned}
\tag{357.1}
$$

where $p_i$ is the $i$th prime. The source has no probability law. Every finite word of replies, including several zeros, has an actual witness by [Boundaries 35.2](KBONACCI_SELF_CALIBRATING_BOUNDARIES.md#35-exact-finite-divisibility-fibres-in-canonical-fibonacci-windows). Its hypotheses apply to these same windows: for finitely many probe primes, choose a prime index above their Fibonacci entry ranks, so that $F_r$ is invertible modulo their product. CRT imposes $g=-F_r^{-1}$ at positive probes and $g=0$ at negative probes. Fibonacci growth makes the legal window contain a representative of every resulting residue class. This is a source-existence argument, not an observation supplied to an acquisition.

The full carrier is the Borel disjoint union of interval copies $B_j,P_j$, $j\ge1$. The unchanged consumer returns unknown on $B_j$ and proposes $j$ on $P_j$. Put $\theta_j=(B_1,1/(j+2))$ for $j\ge0$. For an entire sequence

$$
1\ge a_1\ge a_2\ge\cdots>0,\qquad a_j\longrightarrow0,
\qquad
\lambda_x^a=(1-a_{n(x)})\delta_{\theta_0}+a_{n(x)}\delta_{\theta_{n(x)}},
\tag{357.2}
$$

the targets $\lambda_x^a$ are separately selected marked laws. They do not replace the original nonatomic targets $(1-h_0)\nu_x+h_0\pi_{\Omega(x)}$.

There is zero advice and one source-independent seed. Once that seed is fixed, one deterministic rule applies to every actual source and hands off an original tape after sourcewise almost surely finitely many transitions. Class $N$ preselects its entire schedule and obtains all its replies. Class $O$ preselects an increasing schedule and stops at its first **queried** zero or exhaustion. The hard bound is two actual requests, counting repeats and ignored calls. The next address is never selected from a reply. No source label, reset, copy, additional observation or mean-budget relaxation is available. Original competitors may use arbitrary addresses and output anywhere in the full carrier.

**Definition 357.1 (Complete finite mass allocation).** Fix an integer $L\ge0$, labels $J=\{0,\ldots,L\}$ and a finite mass $M\ge0$. Write $m(v)=\sum_{z\in J}v(z)$; positive parts and vector maxima are coordinatewise. A complete $N$ allocation has one nonnegative empty vector, two nonnegative vectors for each singleton, and four nonnegative vectors $(a_{ij},b_{ij},d_{ij},e_{ij})$ for each $i<j$, in cell order $00,01,10,11$. All cells of a schedule have its same mass. Schedule masses, each counted once, sum to $M$. A stopped allocation instead has pair cells $0,10,11$ of equal mass. At $M=1$ these are probability allocations. Neither labels nor independent counterfactual cells are required to have separate budgets.

The entire kernel has the multilinear expansion

$$
p(w)=c+\sum_{i=1}^L\ell_iw_i+\sum_{i<j}Q_{ij}w_iw_j,
\qquad w\in\{0,1\}^L,
\qquad m(c)=M,\quad m(\ell_i)=m(Q_{ij})=0.
\tag{357.3}
$$

Every word and label is included. For mass one and a word with first zero $n$, the cap-$e$ rows are independently

$$
p_w(0)\ge1-a_n-e,\qquad p_w(n)\ge a_n-e,
\qquad p_w(0)+p_w(n)\ge1-e;
\qquad p_{1^L}(0)\ge1-e.
\tag{357.4}
$$

These are the exact TV rows of 110.2. In particular the union row is not inferred from its singleton rows, and a negative singleton demand remains literal. The finite positive word is a table endpoint, not an infinite all-positive source.

**Convention 357.2 (The reused complete coefficient criterion).** For one zero-sum vector $g_{ij}$ at **every** pair, including $Q_{ij}=0$, put

$$
\begin{aligned}
r_{ij}&=(-g_{ij})_+,&s_{ij}&=(-g_{ij}-Q_{ij})_+,&
t_{ij}&=\max\{m(r_{ij}),m(s_{ij})\},\\
D_i&=\ell_i-\sum_{h<i}g_{hi},&R_i&=\sum_{j>i}r_{ij},&
S_i&=\sum_{j>i}s_{ij},\\
T_i&=\sum_{j>i}t_{ij},&U_i&=\max\{R_i,S_i-D_i\},&u_i&=m(U_i).
\end{aligned}
\tag{357.5}
$$

The two conditions

$$
c\ge\sum_iU_i\quad\text{coordinatewise},\qquad
\sum_i\max\{u_i,T_i\}\le M
\tag{357.6}
$$

must hold for the **same whole family** $g$. [XIX 341.2](KBONACCI_SELF_CALIBRATING_ACQUISITION_RESOURCES_CONTINUATION_XIX.md#341-the-complete-preselected-coefficient-cone) supplies exactly the complete allocation and constructive inverse under (357.6), with $b_{ij}-a_{ij}=g_{ij}$ and $e_{ij}-d_{ij}=Q_{ij}+g_{ij}$. Both budgets and all zero-$Q$ variables are retained. The inverse and the independent scalar-budget obstruction XIX 342 are reused results.

## 358. Alternating odd-list replacement

**Definition 358.1 (Admissible aggregate).** An edge $i<j$ contributes $-B$ to $g_{ij}$, where $m(B)=0$ and $B(z)\ge0$ for $0\le z\le i$. For any increasing odd list
$I=(i_1<\cdots<i_{2h+1})$, $h\ge1$, put $b_t=(-1)^{t+1}$. An odd-list contribution is

$$
g_{i_si_t}\mathrel{+}=b_sb_tV\quad(s<t),
\qquad m(V)=0,\qquad V(z)\ge0\quad(0\le z<i_{2h+1}).
\tag{358.1}
$$

Take any finite sum of these contributions. Lists may overlap; the funding conditions (357.6) apply to their aggregate. Length three is exactly the edge/triangle criterion T of [XX 351.1](KBONACCI_SELF_CALIBRATING_ACQUISITION_RESOURCES_CONTINUATION_XX.md#351-t-one-g-triangle-certificates-with-both-budgets): a triangle contributes $+V$ at $ik$ and $-V$ at $ij,jk$. No assumption is made on later label coordinates beyond their total sum.

**Theorem 358.2 (One allocation with the same schedule masses).** For every $L,M$ and data (357.3), suppose one family $g$ satisfies both (357.6) and Definition 358.1. There is one complete stopped allocation of mass $M$ whose entire law is

$$
q(w)=c+\sum_iD_iw_i+\sum_{i<j}(Q_{ij}+g_{ij})w_iw_j.
\tag{358.2}
$$

For every zero word with first zero $n$,

$$
q_w(0)\ge p_w(0),\qquad q_w(n)\ge p_w(n),\qquad
q_w(0)+q_w(n)\ge p_w(0)+p_w(n),
\tag{358.3}
$$

and $q_{1^L}=p_{1^L}$ as a whole vector. Each schedule keeps the mass of the complete $N$ allocation supplied by XIX 341.2. If an actual complete allocation with this $g$ is supplied instead, each of its schedule masses can be kept. The statement does not require preservation of an arbitrary different representation of $p$.

*Proof.* Apply XIX 341.2 once, with the same $g$ and both budgets. Keep its empty and singleton cells. For each pair replace its four cells $(a,b,d,e)$ by the stopped cells $(a,d,e)$. The retained vectors are nonnegative, each has the old owning schedule mass, and the sum of schedule masses is still $M$. Thus one complete stopped law already exists; no separate assembly of event witnesses or second budget is needed. Coefficient subtraction gives, on the entire cube,

$$
p(w)-q(w)=\sum_{i<j}g_{ij}(1-w_i)w_j,
\tag{358.4}
$$

and therefore gives (358.2).

For one list set $S=\sum_{t=1}^{2h+1}b_tw_{i_t}\in\mathbb Z$. The alternating prefix before $t$ sums to zero for odd $t$ and one for even $t$. Consequently

$$
\begin{aligned}
\Psi_I(w)
&=\sum_{s<t}b_sb_t(1-w_{i_s})w_{i_t}\\
&=-\sum_{t\text{ even}}w_{i_t}
   -\frac{S^2-\sum_tw_{i_t}}2
 =\frac{S(1-S)}2\le0.
\end{aligned}
\tag{358.5}
$$

The last inequality uses integrality, not a bound on a continuous quadratic. If the first zero $n$ is at or beyond $k=i_{2h+1}$, the first $2h$ selected bits are one; their alternating sum is zero. Thus $S$ is zero or one and $\Psi_I=0$. Otherwise $n<k$, so both $V(0)$ and $V(n)$ are nonnegative. The contribution $\Psi_I V$ to (358.4) is therefore nonpositive at both protected labels. An active edge factor $(1-w_i)w_j$ has $w_i=0$, hence $n\le i$; its contribution $-B(1-w_i)w_j$ has the same sign at these labels. Sum all contributions before using the two coordinate inequalities. Adding them transfers the *already imposed* independent union row from its actual old value. All factors in (358.4) vanish at $1^L$, proving whole-vector equality there.

Empty sums cover $L=0,1,2$, where no odd list of length at least three need exist. At $M=0$, (357.6) forces $c=U_i=0$ and $T_i=0$. Then $r=s=0$; zero sums force $g=Q=0$, and $U_i=(-D_i)_+=0$ forces $D_i=\ell_i=0$. The zero allocation needs no division. Zero summands, zero schedule masses, multiple-zero words and equality endpoints require no change to the argument. $\square$

**Corollary 358.3 (Literal affine and original-source consumers).** Suppose the input in Theorem 358.2 satisfies prescribed base, correct, union and positive rows. Then its one output $q$ satisfies the same rows with the same demands, even when some demands are negative.

For the canonical full-score consumer, restrict to $L\ge3$. Let $R=O(1,2;1,2,0)$ in stopped-cell order, $\alpha=(1,1,0,\ldots)$, and $r=z_R=d(\alpha,0)$. A mass-$M$ demand means literally

$$
p_w(E)\ge d_{w,E}(b,e)+(M-1)r_{w,E},
\tag{358.6}
$$

for all the independent event rows. If (358.6) holds for $p$, it holds for $q$. Put $h=d-r$ and $G_O=(z_D-r)_D$ over complete deterministic stopped tables. For every full nonnegative score $Y=(A_w,C_w,P_w;T)$, define

$$
\begin{aligned}
Q(Y)&=(\beta,K),&
\beta_n&=\sum_{w:n(w)=n}(C_w-A_w),\\
K&=\sum_w(A_w+C_w+P_w)+T,&
\Delta_O(Y)&=\max_D Y(z_D-r),\\
F_{Q(Y)}(b,e)&=\sum_n\beta_n(b_n-\alpha_n)-Ke=Yh(b,e).
\end{aligned}
\tag{358.7}
$$

The same allocation $\lambda^\sharp$ of mass $M$ gives simultaneously

$$
F_{Q(Y)}(b,e)\le YG_O\lambda^\sharp\le M\Delta_O(Y).
\tag{358.8}
$$

At mass one, for any entire sequence (357.2) and positive cap $e$, set
$L=\max(\{i:a_i>e\}\cup\{0\})$. A complete feasible finite representative with the theorem's certificate gives an original $O$ rule at that same cap, with its schedule masses unchanged by the replacement.

*Proof.* Equation (358.3) and positive-vector equality transfer every row of (358.6), retaining its literal mass and anchor. Subtracting $Mr$ gives $G_O\lambda^\sharp\ge h$, and nonnegative pairing gives (358.8). This uses one allocation for all words, events and scores. If $M>0$, division would change the profile to $b'=\alpha+(b-\alpha)/M$ and $e'=e/M$; no such division is used. At $M=0$ the premise is $h\le0$, and the same inequality remains valid. No canonical score assertion is made for $L<3$; their finite polynomial and event statements stand separately.

For mass one, partition one uniform seed into the schedule intervals. In each interval use its rescaled coordinate for all terminal-label partitions, refining their intersections into complete deterministic tables before any reply. Select a single table and execute its fixed increasing empty, singleton or pair schedule. This gives zero advice, finite measurable handoff and at most two actual calls. The first zero refers to a queried address, and every executed call is charged. An $N$ completion obtains the ignored second reply as an actual additional call within the same bound. The algebraic lists are not successive source executions. Output the actual mark $\theta_j$ to the unchanged consumer on the same source.

For actual $n\le L$, every possible full low word satisfies all three independent rows. For actual $n>L$ no tail mark is emitted and the low word is $1^L$. For a probability vector $v$ on $J$ the exact identity is

$$
\operatorname{TV}\left(\sum_{j=0}^Lv(j)\delta_{\theta_j},
                  (1-a_n)\delta_{\theta_0}+a_n\delta_{\theta_n}\right)
 =\max\{1-v(0),a_n\}.
\tag{358.9}
$$

The positive row and $a_n\le e$ prove the tail claim, including $a_{L+1}=e$ and all later ties. No summability of the tail is needed. This is the class-feasibility transport of 110.2, rather than arbitrary individual-law preservation. At $L=0$ immediate base output supplies the finite rule. Exact cap zero for a strictly positive entire sequence remains subject to the separate endpoint impossibility of Acquisition Resources 73.3. $\square$

## 359. Strictness against every T representation

**Proposition 359.1 (Five addresses with positive singleton stock).** For every $0<\varepsilon<1/11$, there is a normalized complete five-address kernel satisfying Theorem 358.2 for which no alternative family $g$ satisfies both (357.6) and the T edge/triangle condition. Thus the sufficient finite-kernel domain is strictly enlarged, even when the T representation may change.

Put

$$
\tau=\frac{1-\varepsilon}{10},\qquad \sigma=\frac\varepsilon5,
\qquad v=e_0-e_5,\qquad (b_1,b_2,b_3,b_4,b_5)=(1,-1,1,-1,1).
\tag{359.1}
$$

Give each of the ten pairs mass $\tau$, with $N$ cell labels
$(5,0,0,5)$ for equal signs and $(0,5,5,0)$ for opposite signs. Give each singleton $i$ mass $\sigma$ and labels $(i,0)$. These fifteen tables define $p$. Its stopped partner keeps these masses and singletons and uses pair labels $(5,0,5)$ or $(0,5,0)$, respectively.

*Proof.* The masses sum to $10\tau+5\sigma=1$. Their gauge is
$g_{ij}=\tau b_ib_jv$, one five-list generator, and $Q_{ij}=-2g_{ij}$. For (357.5),

$$
D_i=\sum_{j>i}g_{ij}+\sigma(e_0-e_i),\qquad
U_i=R_i+\sigma e_i,\qquad
\sum_iU_i=c,\qquad
\sum_i\max\{u_i,T_i\}=10\tau+5\sigma=1.
\tag{359.2}
$$

Indeed $s_{ij}=(g_{ij})_+$ and $S_i-D_i=R_i-\sigma e_0+\sigma e_i$, giving the formula for $U_i$. Also $u_i=(5-i)\tau+\sigma$ and $T_i=(5-i)\tau$. Thus the same gauge meets both budgets. Theorem 358.2 gives the displayed stopped law.

Now take *any* alternative gauge satisfying (357.6). Its inverse supplies a complete representation of this same whole kernel. Let $m_{ij}$ be its aggregate pair mass. The coefficient at label zero is
$Q_{ij}(0)=-2\tau b_ib_j$. Since each scalar cell lies in $[0,m_{ij}]$,
$|Q_{ij}(0)|\le2m_{ij}$. Write $m_{ij}=\tau+\delta_{ij}$; then
$\delta_{ij}\ge0$ and the one schedule budget gives $\sum_{i<j}\delta_{ij}\le\varepsilon$. If its four scalar cells are $a,b,d,e$, then $g'_{ij}(0)=b-a$ and $Q_{ij}(0)=e-d-g'_{ij}(0)$, so both $g'$ and $Q+g'$ lie in $[-m_{ij},m_{ij}]$. Intersect these two intervals to obtain

$$
\left|g'_{ij}(0)-\tau b_ib_j\right|\le\delta_{ij}.
\tag{359.3}
$$

This covers all empty, singleton and pair allocations, including unused labels; the quadratic coefficient of a pair receives no contribution from any other schedule type.

Set $u_{ij}=2$ for equal signs and $u_{ij}=1$ otherwise. All forward triangle inequalities $u_{ik}\le u_{ij}+u_{jk}$ hold: the only largest left side is two and both terms on the right are at least one. Therefore every T edge and triangle has nonpositive $u$-pairing at label zero. Every T gauge must have $\sum u_{ij}g'_{ij}(0)\le0$. But there are four equal-sign pairs and six opposite-sign pairs, and (359.3) yields

$$
\sum_{i<j}u_{ij}g'_{ij}(0)
\ge2\tau-2\sum_{i<j}\delta_{ij}
\ge2\tau-2\varepsilon=\frac{1-11\varepsilon}{5}>0.
\tag{359.4}
$$

This contradiction excludes every T-certified representation of $p$, not just the displayed gauge. Every T certificate is already a special case of Definition 358.1, proving strict inclusion. $\square$

**Example 359.2 (Complete original consumer of the strictness family).** Set

$$
e=1-3\sigma,\qquad a_1=\cdots=a_5=1-\varepsilon/2,
\qquad 0<a_{n+1}\le a_n,\quad a_n\longrightarrow0,\quad a_6\le e.
\tag{359.5}
$$

Both preparations in Proposition 359.1 satisfy the complete original selected-law cap $e$ for every such tail. The input preparation attains this cap. For example $\varepsilon=1/100$ gives $a_i=199/200$ for $i\le5$, $e=497/500$, and the strictly positive all-representation margin $89/500$ in (359.4).

*Proof.* Let $S=w_1-w_2+w_3-w_4+w_5$ and $\Psi=S(1-S)/2$. The pair contribution to $p_0$ is $6\tau+2\tau\Psi$ and that to $q_0$ is $6\tau+\tau\Psi$. The possible values of $\Psi$ are $0,-1,-3$; the last occurs exactly at $01010$ and $10101$. On a first-zero-$n$ word with $n<5$, singleton contributions to the union $\{0,n\}$ total $\sigma(\#\text{ones}+1)$. At those two exceptional words this is respectively $3\sigma$ and $4\sigma$. At every other word the pair base is at least $4\tau>3\sigma$. For $n=5$, all pair outputs and all singleton outputs belong to $\{0,5\}$. Thus every union mass is at least $3\sigma=1-e$. Every correct mass is at least $\sigma\ge a_n-e=\sigma/2$. The base demand $1-a_n-e=-1+11\varepsilon/10<0$ is satisfied literally. The positive base is $6\tau+5\sigma\ge3\sigma$. The stopped law inherits every row from Theorem 358.2.

Every execution uses the original seed and actual prime calls described in Corollary 358.3. For actual $n>5$, the shared positive law has exact error $\max\{4\tau,a_n\}\le e$, including tail equality. At $01010$ the input union mass is exactly $3\sigma$, so its error is $e$. This word is actual: $F_{19}=4181$, $g=430$ lies in $[419,836]$, and $1+4181\cdot430=1797831$ has replies $01010$ at $2,3,5,7,11$. The other exceptional word is also actual, using $g=659$ and $N=2755280$. All other finite words use Boundaries 35.2.

This profile already has simpler stopped attainments: the constant law
$(1-\varepsilon/2)e_0+(\varepsilon/10)\sum_{i=1}^5e_i$ meets the same prefix cap and every stated tail. The result concerns certificate coverage of the specified whole kernel, not a new profile or an $N$ versus all-$O$ separator. No optimality among all preparations is asserted. $\square$

## 360. Complete finite bounds for one fixed partition

Let

$$
b=(43,34,34,29,27,25,22)/64.
\tag{360.1}
$$

The inherited unrestricted optimum at this prefix is $15/64$, by [XIX 346.1](KBONACCI_SELF_CALIBRATING_ACQUISITION_RESOURCES_CONTINUATION_XIX.md#346-a-complete-original-attainer-at-error-fifteen-sixty-fourths). The result below concerns a smaller class.

**Definition 360.1 (One global partition).** Partition all positive integer addresses as $R\sqcup D$, independently of both seed and source. Every positive-mass two-address schedule $i<j$ of the entire rule must have $i\in R,j\in D$. Empty and singleton schedules, arbitrary degrees, arbitrary high addresses and arbitrary full-carrier outputs are allowed. Let $\mathcal B_2$ be the union of these classes over the choice of a single partition. A partition chosen separately at different seeds is outside this definition. The finite seven-address class has the identical restriction on $[7]$.

**Lemma 360.2 (Common-mass score bound).** For a finite stopped catalog, assign nonnegative weights $A_w,C_w,P_w,T$ to all rows of (357.4). Let $f_w(z)$ be their label reward, namely
$A_w\mathbf1_{z=0}+C_w\mathbf1_{z=n(w)}+P_w\mathbf1_{z\in\{0,n(w)\}}$ at a zero word and $T\mathbf1_{z=0}$ at $1^7$. For a schedule $S$ and its stopped cell $c$, set

$$
H_{S,c}=\max_{0\le z\le7}\sum_{w:\,\operatorname{cell}_S(w)=c}f_w(z),
\qquad B=\max_S\sum_cH_{S,c}.
\tag{360.2}
$$

Put $C_0=\sum_w(A_w+P_w)+T$, $K=\sum_w(A_w+C_w+P_w)+T$, and $\beta_n=\sum_{n(w)=n}(C_w-A_w)$. Every normalized complete allocation in the catalog satisfying the prefix rows at cap $e$ obeys

$$
C_0+\beta\cdot b-Ke\le B.
\tag{360.3}
$$

*Proof.* Let $X_{S,c}(z)$ be its cell vectors, with $\sum_zX_{S,c}(z)=t_S$ for every owning cell and $\sum_St_S=1$. Its reward is at most $\sum_St_S\sum_cH_{S,c}\le B$. Pair the *same* allocation with all independent row demands; their weighted sum is $C_0+\beta\cdot b-Ke$. Comparing the two expressions proves (360.3). All labels enter each maximum, including earlier and unqueried labels. $\square$

**Proposition 360.3 (Exhaustive one-partition lower bound).** Every seven-address complete stopped allocation using one fixed partition and satisfying all rows at (360.1) has $e\ge137/512$.

*Proof.* Moving vertex $1$ into $R$ and vertex $7$ into $D$ cannot remove an allowed increasing edge. It suffices to consider the following 32 larger catalogs:

$$
R_m=\{1\}\cup\{i+2:0\le i<5,\ \operatorname{bit}_i(m)=1\},
\qquad D_m=[7]\setminus R_m,\qquad 0\le m<32.
\tag{360.4}
$$

Each catalog contains the empty schedule, every singleton and every increasing pair $i\in R_m,j\in D_m$. In the table, a token $P:w:t$ assigns weight $t$ to the independent union row of the seven-bit word $w$; $C:w:t$ assigns it to the correct row; $T:1111111:t$ assigns it to the positive row. All other weights are zero. These zeros do not delete any feasibility demand.

The arithmetic in the table is specified entirely by (360.2). More explicitly, in each stopped cell the reward at zero is the sum of its $P$ and $T$ weights, and at label $z>0$ it is the sum of its $C$ and $P$ weights whose first zero is $z$. Take the maximum of these eight integers. For pair $(i,j)$ the three word conditions are $w_i=0$, $w_i=1,w_j=0$, and $w_i=w_j=1$; a singleton has conditions $w_i=0,1$, and the empty schedule contains all words. This supplies every cell used in the finite sums, without an optimization over unidentified kernels.

| Mask | $B=C_0$ | $K$ | $\beta\cdot b/K$ | Nonzero score tokens |
| ---: | ---: | ---: | ---: | --- |
| 0 | 2 | 7 | $137/448$ | `P:1000000:1 C:1100000:1 C:1110000:1 C:1111000:1 C:1111100:1 C:1111110:1 T:1111111:1` |
| 1 | 2 | 6 | $103/384$ | `P:1100000:1 C:1110000:1 C:1111000:1 C:1111100:1 C:1111110:1 T:1111111:1` |
| 2 | 2 | 6 | $103/384$ | `P:1010000:1 C:1110000:1 C:1111000:1 C:1111100:1 C:1111110:1 T:1111111:1` |
| 3 | 12 | 33 | $105/352$ | `P:0001000:6 C:1000101:2 C:1001000:1 C:1010010:1 C:1011011:1 C:1011110:1 C:1100010:3 C:1101101:3 P:1110000:3 C:1111000:3 C:1111100:3 C:1111110:3 T:1111111:3` |
| 4 | 2 | 6 | $9/32$ | `P:1001000:1 C:1101001:1 C:1111000:1 C:1111100:1 C:1111110:1 T:1111111:1` |
| 5 | 4 | 10 | $173/640$ | `P:0000000:2 C:1010100:1 C:1011011:1 C:1110000:1 C:1110111:1 P:1111000:1 C:1111100:1 C:1111110:1 T:1111111:1` |
| 6 | 4 | 10 | $173/640$ | `P:0000000:2 C:1100000:1 C:1100111:1 C:1110000:1 C:1110111:1 P:1111000:1 C:1111100:1 C:1111110:1 T:1111111:1` |
| 7 | 4 | 12 | $241/768$ | `P:0000000:2 C:1000000:1 C:1000111:1 C:1100101:1 C:1101010:1 C:1110000:1 C:1110111:1 P:1111000:1 C:1111100:1 C:1111110:1 T:1111111:1` |
| 8 | 4 | 11 | $101/352$ | `P:1000001:1 P:1000010:1 C:1100000:2 C:1110000:2 C:1111000:2 P:1111100:1 C:1111110:1 T:1111111:1` |
| 9 | 3 | 8 | $137/512$ | `P:0100100:1 P:1000000:1 C:1100000:1 C:1110000:1 C:1111000:1 C:1111100:1 C:1111110:1 T:1111111:1` |
| 10 | 3 | 8 | $137/512$ | `P:0010100:1 P:1000000:1 C:1100000:1 C:1110000:1 C:1111000:1 C:1111100:1 C:1111110:1 T:1111111:1` |
| 11 | 4 | 11 | $53/176$ | `P:0000000:2 C:1001000:1 C:1001011:1 C:1101000:1 C:1101011:1 C:1111001:1 C:1111010:1 P:1111100:1 C:1111110:1 T:1111111:1` |
| 12 | 4 | 11 | $101/352$ | `P:1000001:2 C:1100000:1 C:1100011:1 C:1110000:1 C:1110001:1 C:1111000:1 C:1111011:1 P:1111100:1 C:1111110:1 T:1111111:1` |
| 13 | 4 | 11 | $101/352$ | `P:0000010:2 C:1010000:1 C:1010011:1 C:1110001:1 C:1110010:1 C:1111000:1 C:1111011:1 P:1111100:1 C:1111110:1 T:1111111:1` |
| 14 | 4 | 11 | $101/352$ | `P:0000000:2 C:1100000:1 C:1100111:1 C:1110000:1 C:1110011:1 C:1111000:1 C:1111011:1 P:1111100:1 C:1111110:1 T:1111111:1` |
| 15 | 4 | 13 | $135/416$ | `P:0000000:2 C:1000000:1 C:1000011:1 C:1100000:1 C:1100011:1 C:1110001:1 C:1110110:1 C:1111000:1 C:1111011:1 P:1111100:1 C:1111110:1 T:1111111:1` |
| 16 | 2 | 6 | $115/384$ | `P:1000000:1 C:1100100:1 C:1110000:1 C:1111000:1 C:1111100:1 T:1111111:1` |
| 17 | 3 | 8 | $137/512$ | `P:0000000:1 C:1000001:1 P:1100010:1 C:1110000:1 C:1111000:1 C:1111100:1 C:1111110:1 T:1111111:1` |
| 18 | 3 | 8 | $137/512$ | `P:0010010:1 P:1000000:1 C:1100000:1 C:1110000:1 C:1111000:1 C:1111100:1 C:1111110:1 T:1111111:1` |
| 19 | 4 | 11 | $105/352$ | `P:0000000:2 C:1000100:1 C:1001001:1 C:1100001:1 C:1101100:1 P:1110010:1 C:1111000:1 C:1111100:1 C:1111110:1 T:1111111:1` |
| 20 | 2 | 5 | $11/40$ | `P:1000001:1 C:1100010:1 C:1110000:1 C:1111100:1 P:1111110:1` |
| 21 | 2 | 5 | $11/40$ | `P:0000000:1 C:1011100:1 C:1110100:1 C:1111100:1 P:1111110:1` |
| 22 | 2 | 5 | $11/40$ | `P:0000000:1 C:1100101:1 C:1110101:1 C:1111101:1 T:1111111:1` |
| 23 | 2 | 6 | $61/192$ | `P:0000000:1 C:1011101:1 C:1100101:1 C:1110101:1 C:1111101:1 T:1111111:1` |
| 24 | 2 | 6 | $115/384$ | `P:1000000:1 C:1100000:1 C:1110000:1 C:1111000:1 C:1111101:1 T:1111111:1` |
| 25 | 2 | 5 | $43/160$ | `P:0000000:1 C:1011000:1 C:1111000:1 C:1111100:1 P:1111110:1` |
| 26 | 2 | 5 | $43/160$ | `P:0000000:1 C:1101000:1 C:1111000:1 C:1111100:1 P:1111110:1` |
| 27 | 2 | 6 | $5/16$ | `P:0000000:1 C:1011000:1 C:1101000:1 C:1111000:1 C:1111100:1 P:1111110:1` |
| 28 | 2 | 6 | $115/384$ | `P:1000001:1 C:1100000:1 C:1110000:1 C:1111000:1 C:1111100:1 P:1111110:1` |
| 29 | 2 | 6 | $115/384$ | `P:0000000:1 C:1010001:1 C:1110001:1 C:1111001:1 C:1111101:1 T:1111111:1` |
| 30 | 2 | 6 | $115/384$ | `P:0000000:1 C:1100000:1 C:1110000:1 C:1111000:1 C:1111100:1 P:1111110:1` |
| 31 | 2 | 7 | $149/448$ | `P:0000000:1 C:1000001:1 C:1100001:1 C:1110001:1 C:1111001:1 C:1111101:1 T:1111111:1` |

For completeness, the maximal support among empty schedules is $C_0$ in every row; the maximal support among all seven singletons is also $C_0$, and among all allowed pairs is also $C_0$. These three equalities result by the eight-integer cell formula above. Thus the displayed $B$ bounds every schedule, not a selected list of deterministic laws. Each $K$ is positive, and every displayed fraction is at least $137/512$; equality occurs at masks $9,10,17,18$. Lemma 360.2 now gives $e\ge\beta\cdot b/K\ge137/512$ for whichever one of the 32 catalogs contains the allocation. This is a finite disjunction over every partition, not a convex combination of partition-specific bounds.

For instance mask $9$ has roots $\{1,2,5\}$. Its eight unit rows give $C_0=B=3$, $K=8$, and $\beta=(0,0,1,1,1,1,1)$, so its bound is
$(34+29+27+25+22)/(64\cdot8)=137/512$. The other rows are needed to cover the other partitions. $\square$

**Proposition 360.4 (Matching whole allocation).** The bound $137/512$ is attained by a complete stopped allocation with roots $\{1,2,5\}$ and all other addresses leaves.

*Proof.* In the following table all masses and cell vectors are integer numerators over $512$. A pair's columns are its first-zero, middle and exhaustion cells; a singleton's first two columns are its replies zero and one. Each cell sums to its own schedule mass.

| Schedule | Mass | First cell | Second cell | Third cell |
| --- | ---: | --- | --- | --- |
| empty | 168 | $168e_0$ | — | — |
| $(1)$ | 72 | $72e_1$ | $72e_0$ | — |
| $(1,3)$ | 135 | $135e_1$ | $135e_3$ | $58e_0+77e_5$ |
| $(2,4)$ | 95 | $95e_2$ | $95e_4$ | $35e_0+21e_6+39e_7$ |
| $(2,6)$ | 40 | $40e_2$ | $40e_6$ | $40e_0$ |
| $(5,6)$ | 2 | $2e_5$ | $2e_6$ | $2e_0$ |

The masses sum to $512$. The complete law is explicitly

$$
\begin{aligned}
512p_0&=168+72w_1+58w_1w_3+35w_2w_4+40w_2w_6+2w_5w_6,\\
512p_1&=207(1-w_1),&512p_2&=135(1-w_2),\\
512p_3&=135w_1(1-w_3),&512p_4&=95w_2(1-w_4),\\
512p_5&=77w_1w_3+2(1-w_5),\\
512p_6&=21w_2w_4+40w_2(1-w_6)+2w_5(1-w_6),\\
512p_7&=39w_2w_4.
\end{aligned}
\tag{360.5}
$$

These nonnegative expressions sum to $512$ at every word. At first zero $n=1,\ldots,7$, the correct numerators are respectively

$$
(207,135,135,95,79,63,39)=512b-137.
\tag{360.6}
$$

Substituting the fixed prefix into $512(1-p_0-p_n)$ gives the complete suffix formulas

$$
\begin{array}{c|l}
n&512(1-p_0-p_n)\\ \hline
1&137-35w_2w_4-40w_2w_6-2w_5w_6\\
2&137-58w_3-2w_5w_6\\
3&137-35w_4-40w_6-2w_5w_6\\
4&119-40w_6-2w_5w_6\\
5&100-40w_6\\
6&116\\
7&98
\end{array}
\tag{360.7}
$$

Every subtracted term is nonnegative; each constant is attained by a suffix. Thus every independent union deficit is at most $137/512$. The correct deficit is exactly $137/512$, and the base deficit is the wrong mass minus $137/512$, hence is nonpositive. This proves each row at every multiple-zero word as well. At $1^7$ the law is

$$
p_{1^7}=(375e_0+77e_5+21e_6+39e_7)/512,
\tag{360.8}
$$

whose positive-base deficit is exactly $137/512$. $\square$

## 361. Original sharpness, compulsory chains and stability

**Theorem 361.1 (Sharp original one-partition optimum).** For every entire sequence (357.2) with $a_i=b_i$ for $1\le i\le7$ and $a_8\le15/64$, the attained minimum selected-law error over $\mathcal B_2$ is $137/512$. The inherited unrestricted original $N$ and $O$ minima are both $15/64$. The strict difference between this subclass optimum and the unrestricted optimum is $17/512$.

*Proof of necessity.* Fix any original $\mathcal B_2$ competitor of cap $e$, with its one partition. The class-preserving proof of 110.2 applies with an additional invariant: every retained low pair uses that same partition. Here is the full reduction needed for that assertion, including caps smaller than the tail amplitudes.

The countability of $X$ gives one conull seed event on which the executions are lawful, finite and within the hard bound at every actual source. The entire preselected schedule has at most two addresses; on a null complement replace it by the empty schedule. If $M_S$ is its finite maximum address, with value zero for the empty schedule, then

$$
\gamma_m=\mathsf P\{M_S>m\}\longrightarrow0.
\tag{361.1}
$$

For every $m\ge8$ and every $w\in\{0,1\}^7$, choose before seeds an actual source $x_{w,m}$ with this low word and zero replies at every address $8,\ldots,m$. Boundaries 35.2 supplies the entire finite family. Project all tapes except $\theta_1,\ldots,\theta_7$ to $\theta_0$. This measurable projection contracts TV. Its projected target is $(1-b_n)e_0+b_ne_n$ for a low zero word and $e_0$ for the positive low word, regardless of whether its actual tail amplitude exceeds $e$.

Choose a finite transition cutoff $t_m$ for this finite witness family with handoff failure probability at most $1/m$ at each witness. Sourcewise almost-sure finite handoff supplies it. Simulate the seed-fixed rule with low replies $w$ and high replies zero up to $m$, using output zero upon exceeding the address or transition cutoff. Finite-record transport from [Source-Correlated Laws 45.3](KBONACCI_SELF_CALIBRATING_SOURCE_CORRELATED_LAWS.md#45-lawful-acquisition-through-one-inherited-seed) couples this simulation with each actual witness on a common seed event of complement at most $\gamma_m+1/m$. Thus its low laws meet all exact target rows with cap at most $e+\gamma_m+1/m$.

For a retained two-low-address schedule its pair is still root-to-leaf in the same partition. A low zero stops before any high continuation. A positive low exhaustion has a fixed high continuation, because all high replies are fixed and larger addresses follow low addresses. Removing the high requests therefore produces only singleton or empty schedules. A transition cutoff is constant on each stopped low cell, since the seed and acquired transcript agree there. Consequently no new low pair edge is introduced. The projected output functions belong to the finite catalog for the original partition restricted to $[7]$. Choose representatives *within that catalog*, rather than unrestricted representatives of the same functions. Finite-record measurability gives one common weight vector on this finite catalog.

Its probability simplex is compact. A subsequence of these common weight vectors converges to one allocation in the same catalog. Finitely many law coordinates and row inequalities are continuous, so the limit satisfies every closed-cap row exactly at $e$. Proposition 360.3 gives $e\ge137/512$. This argument retains arbitrary original addresses, full-carrier outputs and all actual finite witnesses. If an exact zero-error competitor existed, it would be feasible at any smaller positive cap and would give the same contradiction. Necessity transports feasibility, not an arbitrary competitor's entire laws.

*Proof of attainment.* Execute the single allocation of Proposition 360.4 on actual primes. Partition one uniform seed into the stated schedule masses and refine all counterfactual label partitions as in Corollary 358.3. Each seed selects a complete table before replies; a pair stops at its first queried zero or exhaustion. There are at most two actual requests, zero advice and finite handoff, with the actual marks emitted to the unchanged consumer. All pairs use roots $\{1,2,5\}$. For actual $n\le7$, Propositions 360.3–360.4 give precisely the prefix rows. For actual $n>7$, (358.9) and (360.8) give

$$
\operatorname{TV}(p_{1^7},\lambda_x^a)
=\max\{137/512,a_n\}=137/512,
\tag{361.2}
$$

since $a_n\le15/64<137/512$. This proves attainment for every allowed tail.

Finally, XIX 346.1 already supplies the fourteen-schedule original $O$ attainer at $15/64$ and the matching full-$N$ lower at the same entire profile. Its lower has $\beta=(1,0,4,5,5,5,5)$, $K=42$, $C_0=17$, and full-$N$ support $B_N=18$; its inequality is
$b_1+4b_3+5(b_4+b_5+b_6+b_7)\le1+42e$. Its upper has positive law $(49e_0+5e_3+5e_4+5e_7)/64$, hence exact tail error $\max\{15/64,a_n\}$. These are reused suppliers, not new optimum or profile claims. Subtracting the two optima gives $137/512-15/64=17/512$. $\square$

**Corollary 361.2 (Every successful seven-coordinate stopped kernel has a chain).** Every normalized stopped kernel on all seven-bit words satisfying the rows at $b$ and any cap $e<137/512$ has whole-vector coefficients $Q_{ij}\ne0$ and $Q_{jk}\ne0$ for some $i<j<k$. In particular this holds for every stopped representative at the inherited optimum $15/64$. No choice of a feasible seven-coordinate $N$ representative at that cap can satisfy all the parent-cancellation criterion P hypotheses of XX 352.1.

*Proof.* Suppose no such chain exists. Let $R$ be the vertices with a nonzero outgoing whole-vector coefficient, and let $D$ be its complement. A vertex in $R$ cannot have a nonzero incoming coefficient, since that would give the excluded chain. Thus every nonzero $Q$ goes from $R$ to $D$. The canonical stopped inverse of 109.1 realizes the *same* kernel using pair mass $m((-Q_{ij})_+)$. That mass is zero whenever $Q_{ij}=0$, so all its positive-mass pairs use this one fixed partition; its remaining schedules are singleton or empty. Proposition 360.3 gives a contradiction.

Under criterion P the output polynomial has interactions only from its one root set to leaves. Its constructive stopped realization, or the same canonical inverse, lies in one fixed-partition catalog. Thus any feasible input representative satisfying all P hypotheses at $15/64$ would yield the stopped kernel just excluded. This is an exclusion of every P-compatible representative in that seven-coordinate setting, not a refutation of its conditional theorem or a restriction on arbitrary invariant stopped remainders. $\square$

**Corollary 361.3 (A stable strict subclass gap).** Let $0\le\delta<17/1024$. Suppose $a'$ is an entire positive nonincreasing vanishing sequence with

$$
\max_{1\le i\le7}|a'_i-b_i|\le\delta,
\qquad a'_8\le15/64+\delta.
\tag{361.3}
$$

Its original fixed-partition error infimum is at least $137/512-\delta$, whereas the inherited unrestricted $O$ law has error at most $15/64+\delta$. The difference of these infima is at least $17/512-2\delta>0$.

*Proof.* In every score of Proposition 360.3, $\sum_n|\beta_n|\le K$, since each unit row weight contributes at most one to that sum. Replacing $b$ by its perturbed prefix changes $\beta\cdot b/K$ by at most $\delta$. The same 32 scores, and the partition-preserving original necessity argument, therefore retain the lower $137/512-\delta$. For $n\le7$, the selected targets at amplitudes $a'_n$ and $b_n$ differ in TV by exactly $|a'_n-b_n|$. The triangle inequality bounds the inherited law's error by $15/64+\delta$ there. For $n>7$ its positive law gives exact error $\max\{15/64,a'_n\}\le15/64+\delta$. Subtract the lower bound for the subclass infimum and the upper bound for the unrestricted infimum in the appropriate directions to obtain the stated difference. $\square$

Mixing partitions by the seed removes the restriction in Definition 360.1: every individual stopped table belongs to some root/leaf partition, and their mixtures form the full stopped class. The inherited $15/64$ law is already a concrete counterexample to an all-$O$ interpretation of the $137/512$ lower. The compulsory-chain result concerns the coefficients of finite seven-coordinate stopped laws, not the graphical appearance of one chosen table representation of an arbitrary original rule.

## 362. Reuse and the unresolved unrestricted obligations

The scalar inequality behind (358.5) is classical hypermetric geometry. Deza and Dutour Sikirić, [*The hypermetric cone on 8 vertices and some generalizations*, arXiv:1503.04554v1, §1](https://arxiv.org/abs/1503.04554v1), use integer $b$ with $\sum b_i=1$ and $\sum_{i<j}b_ib_jd(i,j)\le0$, including the odd-gonal specializations. Here $d(i,j)=|w_i-w_j|$ is a cut metric. For alternating signs, the linear orientation correction cancels, so its evaluation is twice (358.5). The proof above explicitly gives this specialization; no cut-facet classification, completeness of odd lists, or acquisition theorem is assumed from the literature. The consecutive-integer product argument also occurs in IX 207.10.

The complete $N$ inverse, the stopped inverse and original transport are XIX 341.2 and 109.1–110.2. The original seed/finite-record interface is Source-Correlated Laws 45.1–45.3, and complete-table coupling is II 140.2–140.3. T is XX 351.1; length-three lists and the earlier outward-star mechanism of XV 258.3–258.4 keep their prior scopes. P is XX 352.1. The normalized H7 classification of XIX 344–345 remains a mass-one result and is not transported by affine division. The seven-coordinate unrestricted optimum is precisely the supplier XIX 346.1. The additional conclusions here are the labelled odd-list replacement with its funded aggregate, strictness for every T representation of one whole kernel, and the sharp one-global-partition exclusion with its chain and stability consequences. Neither the scalar cut inequality, the inverses nor the already attained profiles acquire new-result credit. No global priority or exhaustive classification is asserted.

The original universal score obligation remains: for every finite horizon in its original domain and every full nonnegative score $y$ with $\Delta_O(y)=1$, find one unrestricted full $V\ge0$ and the **same** $\theta\in[0,1]$ jointly satisfying

$$
\Delta_N(V)+\theta\le1,\qquad
\sigma_{H_L}\bigl(Q(y)-Q(V)\bigr)\le\theta,
\tag{362.1}
$$

where $\Delta_N$ is the full preselected support excess, and $\sigma_{H_L}(q)=\max_{(b,e)\in H_L}F_q(b,e)$ uses the unchanged hull of IX 207.3:

$$
\begin{aligned}
H_L=\{(b,e):\;&1\ge b_1\ge\cdots\ge b_L\ge e\ge0,\quad b_2=b_3,\\
 &(L+1)e\le\sum_{j=3}^Lb_j,\quad
 b_1+\sum_{j=3}^Lb_j-(L+1)e\le1\}.
\end{aligned}
\tag{362.2}
$$

The residual in (362.1) is signed, and a nonzero zero-cost $V$ at $\theta=1$ is admissible. Theorem 358.2 assumes a suitably funded and decomposable representative; it does not select such a representative or a pair $(V,\theta)$ for every required score. Theorem 361.1 bounds one fixed-partition subclass, while unrestricted $O$ already attains its profile at a smaller cap. Thus neither theorem supplies the alternative complete original $N$ attainer with a uniform strict lower against **all** original arbitrary-address, full-carrier $O$ rules.

The original nonatomic target and complete paid M1 acquisition obligations remain unresolved here. Indeed every constructed marked preparation has finite support, which has zero mass under an unchanged nonatomic target, so its TV distance from that target is one. The selected-law conclusions neither assert a physical acquisition realization nor change the source, the common-seed contract or the original cost model.

## 追加锚（本行以下为增补区）
