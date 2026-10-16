# FIB native ninth-amplitude obstruction and complete-law interpolation

## 1. The unchanged original family

**Definition 1.1 (Arithmetic source, full carrier and selected targets).**
Let $F_0=0$, $F_1=1$, $F_{k+2}=F_{k+1}+F_k$, and let $p_i$ be
the increasing primes. Retain the actual countable source

$$
X=\{(r,g):r\text{ prime},\ g\in\mathbb Z,\
 \lceil F_r/10\rceil\le g\le\lfloor F_r/5\rfloor\},\qquad
N(r,g)=1+F_rg,\quad q_i(x)=[p_i\mid N(x)],\quad
n(x)=\min\{i:q_i(x)=0\}.
$$

Replies are static. The full carrier is the Borel disjoint union
$\Theta=\bigsqcup_{j\ge1}B_j\sqcup\bigsqcup_{j\ge1}P_j$, each block a
copy of $(0,1)$. The unchanged consumer makes no prime requests,
returns unknown on $B_j$, and proposes $j$ on $P_j$. The actual
distinct marks and selected accuracy targets are

$$
\theta_j=(B_1,1/(j+2))\quad(j\ge0),\qquad
\lambda_x^a=(1-a_{n(x)})\delta_{\theta_0}
                  +a_{n(x)}\delta_{\theta_{n(x)}},\qquad
e_a(A)=\sup_{x\in X}\operatorname{TV}(\mathcal L(A(x)),\lambda_x^a).
$$

There is no block indexed zero. The original nonatomic targets remain
a different family. Explicitly, for $0<h_0<1$, put
$t_x=\sum_i3^{-i}q_i(x)$, $Z_t=\int_0^1e^{tz}\,dz$, let $\nu_x$
have density $e^{t_xz}/Z_{t_x}$ on $B_{n(x)}$, let $\pi_j$ be
uniform on $P_j$, and let $\Omega(x)$ count distinct prime divisors of
$N(x)$. Then $\mu_x^{\rm orig}=(1-h_0)\nu_x+h_0\pi_{\Omega(x)}$.
Accuracy below always means accuracy against $\lambda_x^a$.

**Definition 1.2 (Full head and entire actual continuation).**
Throughout,

$$
\begin{gathered}
0<\tau\le1/24,\qquad0\le v\le u\le\tau,\qquad
a_1=a_2=1-11\tau,\\
(a_3,a_4,a_5,a_6,a_7)=(13,10,9,8,6)\tau,\qquad
a_8=5\tau+u,\quad a_9=5\tau+v,\\
a_{10}\ge a_{11}\ge\cdots>0,\qquad a_{10}\le5\tau,\qquad
a_n\longrightarrow0.
\end{gathered}
$$

Every such entire continuation is included: ties, nonsummable tails and
arbitrarily slow decay are permitted. Actual $a_9$ at $v=0$ is
$5\tau>0$. These amplitudes are positive, nonincreasing and at most
one, since $1-24\tau\ge0$ and $a_8\le6\tau=a_7$.

**Definition 1.3 (Hard two actual requests and full finite catalogs).**
An original acquisition has one source-independent seed, zero advice
and sourcewise almost-sure finite measurable handoff to the unchanged
consumer. In $\mathcal N_2$ the whole schedule is preselected and all
its replies are acquired. In $\mathcal O_2$ an increasing schedule is
preselected and execution stops at its first queried zero or exhaustion.
The second address cannot depend on a reply. At most two actual
requests are allowed, including repetitions and ignored replies.
Competitors retain arbitrary addresses and arbitrary Borel outputs in
$\Theta$. There is no source distribution, free source label, free
$r,g,N,n$, free reply prefix, address bound, runtime bound or
mean-request relaxation. Outputs depend on seed and acquired transcript.

For $K$ finite bits the complete $N$ catalog contains constants,
singletons and every $N(i,j;r_{00},r_{01},r_{10},r_{11})$ with four
independent output labels in $\{0,\ldots,K\}$. The complete $O$
catalog contains constants, singletons and every $O(i,j;f,m,z)$,
$i<j$, on stopped cells $0,10,11$. Earlier and unqueried output
labels remain legal. Static reversal permutes cells, and repetition
gives singleton information. Finite contraction does not refund any
original actual request.

A stopped table has counted completion $N(i,j;f,f,m,z)$, which
acquires the ignored second reply after an early zero. This embeds
stopped laws in $N$ without converting an arbitrary competing $N$
law into $O$.

**Proposition 1.4 (Independent TV rows and exact later-tail identity).**
Let $\Omega_n=\{w:w_1=\cdots=w_{n-1}=1,w_n=0\}$ and $+=1^K$.
For a probability law $p_w$ on labels $0,\ldots,K$, cap-$e$
feasibility at $w\in\Omega_n$ retains all three rows

$$
\begin{array}{c|c|c}
\text{row}&\text{event}&\text{demand}\\\hline
A&\{0\}&1-b_n-e\\
C&\{n\}&b_n-e\\
P&\{0,n\}&1-e
\end{array}
\qquad p_+(0)\ge1-e.
$$

They hold on every word, including all multiple-zero suffixes.
Negative singleton demands remain literal. If $c_n=p_w(n)$ and
$D_n=1-p_w(0)-p_w(n)$, exact TV is

$$
\max\{c_n+D_n-b_n,\ b_n-c_n,\ D_n\}.
$$

For a law $p$ on labels at most $K$ and an actual $n>K$, put
$r=1-p(0)$. Then

$$
\operatorname{TV}(p,(1-a_n)e_0+a_ne_n)
 =\frac{|a_n-r|+a_n+r}{2}=\max\{r,a_n\}.
$$

Proof. Split the signed difference at zero, $n$, and the other labels.
The resulting masses give both formulas. The union deficit is
independent of the two singleton deficits and must be bounded
separately. $\square$

## 2. Actual words and original necessity

**Lemma 2.1 (Every finite pattern is actual).**
Every specification of finitely many prime replies has an actual
witness in $X$. Every actual first absence is finite.

Proof. Modulo a prime $p$, the Fibonacci matrix
$M=\left(\begin{smallmatrix}1&1\\1&0\end{smallmatrix}\right)$ is
invertible and, for $k\ge1$,

$$
M^k=\begin{pmatrix}F_{k+1}&F_k\\F_k&F_{k-1}\end{pmatrix}.
$$

Its power is scalar exactly when $p\mid F_k$: the off-diagonal
entries give one direction and $F_{k+1}=F_k+F_{k-1}$ gives the
other. Its class in the finite group
$\operatorname{PGL}_2(\mathbb F_p)$ has order $z(p)\ge3$, since
$F_1=F_2=1$. Thus $p\mid F_k$ iff $z(p)\mid k$.

For specified primes of product $D$, choose a prime index $r$
larger than all these ranks, with $F_r\ge10(D+2)$. No rank divides
$r$, so $F_r$ is invertible modulo $D$. Prescribe
$g=-F_r^{-1}\pmod p$ at desired ones and $g=0\pmod p$ at zeros.
CRT gives a residue modulo $D$. The legal interval for $g$ has
width at least $F_r/10-2\ge D$ and contains a representative.
This proves every finite pattern, including multiple-zero words,
positive prefixes and each later first-zero fibre. Every actual
positive integer $N(x)$ has finite prime support, hence finite first
absence. A finite positive prefix is not an infinite all-positive
actual source. $\square$

**Theorem 2.2 (One complete representative at a closed cap).**
For any finite $K\ge2$, an arbitrary original rule in class $C=N,O$
meeting a positive closed cap $c\le1$ supplies some normalized
complete $K$-bit allocation in its own class satisfying every row of
1.4 at $(a_1,\ldots,a_K;c)$, including the positive row.

Proof. Countability of $X$ gives one probability-one seed event on
which finite handoff and the hard request bound hold on every actual
source. On that event a preselected $O$ schedule cannot have a
potentially executed third request: an actual finite pattern with its
earlier queried replies positive would execute it. Its relevant whole
schedule therefore has at most two finite addresses, as does an $N$
schedule. Every consistent counterfactual cell has an actual witness
by 2.1, so its output is defined on this same event. Inconsistent
repeat-query cells may be filled arbitrarily. The observation rule in
1.3 makes outputs depend on seed and acquired transcript, independently
of the chosen witness. Countably many schedules and finite transcripts
permit fixed witness choices with measurable outputs.

Project the full carrier measurably onto labels $0,\ldots,K$ by
retaining $\theta_j$, $j\le K$, and sending every other point to zero.
This retains each low target and sends every higher first-zero target
to $e_0$. Let $\eta_M$ be the seed probability that a relevant
address exceeds $M$; then $\eta_M\to0$.

For $M\ge K+1$, on seeds with addresses at most $M$ fix all queried
replies above $K$ to zero and contract those constant observations.
On exceptional seeds use constant zero. Push the same seed forward to
the finite complete $K$-bit catalog, with all counterfactual outputs.
This is one normalized allocation in its own class. In $O$, removed
higher observations follow lower ones, preserving increasing
first-queried-zero stopping. In $N$, the four static cells remain
independent. Repeats and reversals are covered by contraction or
cell permutation.

For each low word choose an actual source with that word and with bits
$K+1,\ldots,M$ zero. A low first-zero target projects to itself; a
positive low word has actual first zero $K+1$ and projects to $e_0$.
On nonexceptional seeds the projected output agrees with the finite
representative. Projection contracts TV, while exceptional probability
costs at most $\eta_M$, uniformly over the finitely many words.
Hence every independent row and the positive row holds at
$c+\eta_M$ for that single allocation.

Compactness of the finite catalog simplex gives a convergent
subsequence as $M\to\infty$. Continuity of every row gives one
normalized allocation at the exact closed cap $c$. This proves
existence of class feasibility, without preserving an arbitrary
starting law or coupling. It retains arbitrary original addresses,
Borel outputs, closed ties and smaller caps activating more tail
coordinates. Fixed high replies in this proof are never free actual
observations. $\square$

**Reference frame 2.3 (Credits and visible premises).**
The original objects, arithmetic realization and closed-cap
correspondence are mature results collected in
[DEV XVIII, 315 and 331](KBONACCI_SELF_CALIBRATING_ACQUISITION_RESOURCES_CONTINUATION_XVIII.md).
The direct proof above exposes the observation premises used here;
no unseen earlier proof body is an additional premise.

| Ingredient | Credit |
| --- | --- |
| Complete $253$ score, full head allowance and nineteen-schedule law | DEV XVIII 336–339 |
| Complete $128$ score | DEV XVIII 318 |
| Genuine $P^0,P^\star$ and full Boolean endpoint bounds | DEV XVIII 319–320 |
| $Q$ transfer and old attained unequal wedge | DEV XVIII 324–327; [Unequal Two-tail Frontier, 3–6](FIB_NATIVE_UNEQUAL_TWO_TAIL_ATTAINED_FRONTIER.md) |
| Base-to-eight $217$ law and original counterexample | Unequal Two-tail Frontier 10–17 |
| $256$ lift and intermediate complete-law synthesis | Supplied full-head investigation; its independent ordinary check supplies expanded verification |

The local support calculations and endpoint data below make the new
lift and synthesis reviewable. Their exposition and verification do
not rediscover the credited endpoints.

## 3. Complete ninth-coordinate support

**Definition 3.1 (The entire credited score $Y_{253}$).**
A $P$ weight at a zero word with first zero $n$ rewards labels $0,n$;
a $C$ weight rewards label $n$. A $T$ weight at the positive word
rewards only zero. All $A$ and all unlisted coefficients vanish.
The following are all thirty-eight nonzero rows. Zero coefficients
delete no feasibility constraints.

| Word | Event | Weight |
| --- | --- | ---: |
| $00110000$ | $P$ | 3 |
| $01000100$ | $P$ | 2 |
| $01001000$ | $P$ | 7 |
| $01001010$ | $P$ | 4 |
| $01010000$ | $P$ | 3 |
| $01010100$ | $P$ | 8 |
| $01100000$ | $P$ | 4 |
| $01100010$ | $P$ | 1 |
| $01100100$ | $P$ | 3 |
| $10000100$ | $P$ | 1 |
| $10001010$ | $P$ | 2 |
| $10001100$ | $P$ | 5 |
| $10010001$ | $P$ | 1 |
| $10010010$ | $P$ | 9 |
| $10011000$ | $P$ | 6 |
| $10100000$ | $P$ | 3 |
| $10100010$ | $P$ | 5 |
| $10100100$ | $P$ | 2 |
| $10101000$ | $P$ | 3 |
| $11100000$ | $P$ | 3 |
| $10110000$ | $C$ | 3 |
| $11000000$ | $C$ | 18 |
| $11001001$ | $C$ | 1 |
| $11001100$ | $C$ | 2 |
| $11011000$ | $C$ | 3 |
| $11011010$ | $C$ | 3 |
| $11100000$ | $C$ | 19 |
| $11100010$ | $C$ | 2 |
| $11101011$ | $C$ | 1 |
| $11101100$ | $C$ | 2 |
| $11110000$ | $C$ | 23 |
| $11110001$ | $C$ | 1 |
| $11110111$ | $C$ | 3 |
| $11111000$ | $C$ | 24 |
| $11111011$ | $C$ | 1 |
| $11111100$ | $C$ | 24 |
| $11111110$ | $C$ | 24 |
| $11111111$ | $T$ | 24 |

**Lemma 3.2 (Complete all-label support data).**
For pair $i<j$ and cell $ab$, maximize the sum of rewards on
$\{w:(w_i,w_j)=ab\}$ over all labels independently. In the next
table $B$ is the label-zero quadruple, $H$ maximizes over labels
$3,\ldots,8$, and $M$ is the full maximum over all nine labels.
Cell order is $00,01,10,11$.

| Pair | $B$ | $H$ | $M$ |
| --- | --- | --- | --- |
| $12$ | $(3,32,37,27)$ | $(0,0,0,27)$ | $(3,32,40,27)$ |
| $13$ | $(24,11,24,40)$ | $(0,0,27,27)$ | $(24,11,27,40)$ |
| $14$ | $(21,14,24,40)$ | $(0,0,27,27)$ | $(21,14,27,40)$ |
| $15$ | $(24,11,24,40)$ | $(0,0,27,25)$ | $(24,11,27,40)$ |
| $16$ | $(22,13,32,32)$ | $(0,0,25,24)$ | $(22,13,32,32)$ |
| $17$ | $(30,5,24,40)$ | $(0,0,24,24)$ | $(30,5,24,40)$ |
| $18$ | $(35,0,39,25)$ | $(0,0,26,4)$ | $(35,0,39,25)$ |
| $23$ | $(24,16,24,35)$ | $(0,0,27,27)$ | $(24,16,27,35)$ |
| $24$ | $(21,19,24,35)$ | $(0,0,27,27)$ | $(21,19,27,35)$ |
| $25$ | $(24,16,24,35)$ | $(0,0,27,25)$ | $(24,16,27,35)$ |
| $26$ | $(32,8,22,37)$ | $(0,0,25,24)$ | $(32,8,25,37)$ |
| $27$ | $(24,16,30,29)$ | $(0,0,24,24)$ | $(24,16,30,29)$ |
| $28$ | $(39,1,35,24)$ | $(0,0,26,4)$ | $(39,1,35,24)$ |
| $34$ | $(21,27,24,27)$ | $(21,6,27,27)$ | $(21,27,27,27)$ |
| $35$ | $(24,24,24,27)$ | $(18,9,27,25)$ | $(24,24,27,27)$ |
| $36$ | $(32,16,22,29)$ | $(25,2,25,24)$ | $(32,16,25,29)$ |
| $37$ | $(33,15,21,30)$ | $(24,3,24,24)$ | $(33,15,24,30)$ |
| $38$ | $(47,1,27,24)$ | $(26,1,26,4)$ | $(47,1,27,24)$ |
| $45$ | $(24,21,24,30)$ | $(24,3,27,25)$ | $(24,21,27,30)$ |
| $46$ | $(32,13,22,32)$ | $(25,2,25,24)$ | $(32,13,25,32)$ |
| $47$ | $(33,12,21,33)$ | $(24,3,24,24)$ | $(33,12,24,33)$ |
| $48$ | $(45,0,29,25)$ | $(26,1,24,4)$ | $(45,1,29,25)$ |
| $56$ | $(32,16,22,29)$ | $(24,3,25,24)$ | $(32,16,25,29)$ |
| $57$ | $(33,15,21,30)$ | $(24,3,24,24)$ | $(33,15,24,30)$ |
| $58$ | $(47,1,27,24)$ | $(24,4,24,1)$ | $(47,4,27,24)$ |
| $67$ | $(33,21,21,24)$ | $(24,3,24,24)$ | $(33,21,24,24)$ |
| $68$ | $(53,1,21,24)$ | $(24,1,24,3)$ | $(53,1,24,24)$ |
| $78$ | $(53,1,21,24)$ | $(24,1,24,3)$ | $(53,1,24,24)$ |

Every full quadruple sums to at most $102$. Exact singleton maxima,
in address order, are $(35,64),(40,59),(48,51),(45,54),(48,51),
(54,45),(54,45),(74,25)$, each totaling $99$. The constant maximum
is $99$.

Proof. The $P$ class totals are $(35,37,0,3,0,0,0,0)$, summing
to $75$; the $C$ totals are $(0,3,27,24,27,25,24,24)$, summing
to $154$; $T=24$. In any cell, label zero earns its $P$ sum plus
$T$ if it contains the positive word, and label $n>0$ earns the
$P+C$ sum of class $n$. This gives all the displayed columns.

More explicitly, the $P$-positive one-bit totals are
$(40,35,27,30,27,21,21,1)$. For their pair-positive totals $t_{ij}$,

$$
B_{ij}=(75-t_i-t_j+t_{ij},\ t_j-t_{ij},\ t_i-t_{ij},\ t_{ij}+24).
$$

In the printed pair order, the $t_{ij}$ are
$(3,16,16,16,8,16,1,11,11,11,13,5,0,3,3,5,6,0,
6,8,9,1,5,6,0,0,0,0)$.
For $H$, the class-three reward group is $(18,1,2,3,3)$ on its
five words; the class-four group is $(22,2,1,2)$ on its four words,
with $22=19+3$ including $P$. The remaining groups are $(23,1,3)$,
$(24,1)$, $(24)$, $(24)$ on classes five through eight. Splitting
these explicitly specified groups by each pair gives $H$.
Label one is a subset of the base $P$ reward. Label two has its
class-two $P$ group plus $3$ at $10110000$; splitting it by each
pair is base-dominated except at pair $12$, cell $10$, where $40$
exceeds $37$. These facts give $M$ and cover every label.
For example, pair $27$ has $t_2=35,t_7=21,t_{27}=5$, giving
$B_{27}=(24,16,30,29)$, already the full maximum there.

For singletons, base rewards are $(75-t_i,t_i+24)$. The label-two
splits are $(0,40),(40,0),(24,16),(21,19),(24,16),(32,8),
(24,16),(39,1)$; maxima over labels three through eight are
$(0,27),(0,27),(27,27),(27,27),(27,25),(25,24),(24,24),(26,4)$.
All are base-dominated. The constant base reward is $99$, larger
than every constant nonbase reward.

The anchor $R=O(1,2;1,2,0)$ earns $75+24+3=102$.
Four-cell independence proves full $N$ support from the table.
Constants, singletons and repeats coarsen pair partitions; reversal
permutes cells. Stopped tables are included by counted completion.
Thus $B_N=B_O=W=102$, with both excesses zero, as in the credited
DEV XVIII 336 theorem. $\square$

**Theorem 3.3 (The complete $256$ lift and sharp added weight).**
Append bit one to every word of 3.1, preserving event, label and
weight; its $T$ row becomes $111111111$. Add one $C$ row of weight
$3$ at $111111110$. These are all thirty-nine nonzero rows of
$Y_{256}$. Its full $N$ and $O$ support remains $102$, equal to
its anchor reward. Its invariants are

$$
\sum P=75,\quad\sum C=157,\quad T=24,\quad K_Y=256,\qquad
\beta=(0,3,27,24,27,25,24,24,3).
$$

For one complete feasible affine allocation of any finite mass at a
real profile, it implies

$$
3b_2+27b_3+24b_4+27b_5+25b_6+24b_7+24b_8+3b_9
 \le3+256e.
$$

The weight $3$ is maximal for adding this one row to this lifted
score while retaining zero excess.

Proof. For every pair avoiding nine, the new row lies in cell $11$
and gives label nine reward $3$, with zero old reward. Every old
$M_{ij,11}\ge24$, so none of its four independent maxima changes.
These are all twenty-eight rows of 3.2. The remaining eight pair
rows, in $00,01,10,11$ order, are

$$
\begin{array}{c|c}
19&(0,35,3,64)\\
29&(0,40,3,59)\\
39&(0,48,3,51)\\
49&(0,45,3,54)\\
59&(0,48,3,51)\\
69&(0,54,3,45)\\
79&(0,54,3,45)\\
89&(0,74,3,25).
\end{array}
$$

All old scored words have ninth bit one; the added word has every
old bit one and ninth bit zero. Thus the old cells are singleton
cells of 3.2, the new cell has maximum three and the fourth is empty.
Every sum is $102$. This checks all thirty-six pairs with four
independent $N$ outputs. Coarsening, reversal and counted completion
cover all shorter, repeated and stopped rules. The anchor still
earns $102$. A singleton querying nine, outputting nine on zero
and zero on one, earns $99+w$ if the added weight is $w$.
Thus $w>3$ violates zero excess for this unchanged anchor.
This is sharpness of this lift, without an assertion about all scores.

For the affine statement let $z_D$ be full event incidence,
$r=z_R=d(\alpha,0)$ with $\alpha=(1,1,0,\ldots,0)$, and
$G_C=(z_D-r)_D$. Affine feasibility is
$G_C\lambda\ge d(b,e)-r$ for one $\lambda\ge0$. Then

$$
\begin{aligned}
\beta\cdot b-3-256e
 &=Y_{256}(d(b,e)-r)\\
 &\le Y_{256}G_C\lambda
 =\sum_D\lambda_D(Y_{256}z_D-102)\le0.
\end{aligned}
$$

No division by allocation mass is used. At a normalized law, the
required reward is $99+\beta\cdot b-256e$ and support is $102$.
For an ordered skeleton in any larger horizon, map numerical labels
along that skeleton and set nonskeleton bits to one on scored words.
Outside queries give constant or singleton information and outside
labels earn zero. The same full support proof covers every horizon
and ordered embedding, including earlier unqueried labels.
All unscored independent rows remain constraints. $\square$

**Corollary 3.4 (Original lower bounds and actual ninth obstruction).**
Put

$$
d_0=\frac{24u}{253},\qquad
d_{256}=\frac{24u+3v}{256},\qquad
d_{\rm sum}=\frac{11(u+v)}{128},\qquad E=5\tau+d_0.
$$

Every original competitor in either class has

$$
e_a(A)\ge5\tau+\max\{d_0,d_{256},d_{\rm sum}\}.
$$

When $253v>24u$, every competitor exceeds $E$ by at least
$3(253v-24u)/(253\cdot256)>0$.

Proof. The credited $253$ pairing gives
$3b_2+27b_3+24b_4+27b_5+25b_6+24b_7+24b_8\le3+253e$.
Its actual left side minus three is

$$
-33\tau+351\tau+240\tau+243\tau+200\tau+144\tau
       +120\tau+24u=1265\tau+24u.
$$

The new inequality adds the actual $3a_9=15\tau+3v$, giving
$256e\ge1280\tau+24u+3v$. Theorem 2.2 transfers both inequalities
to every original rule at each positive met cap. Decreasing caps gives
the error bounds, including exclusion of zero error. At error one
these lower bounds are immediate since they are below one.

The remaining lower is the credited complete $128$ theorem, DEV XVIII
318.2–318.3:

$$
2b_2+11b_3+13b_4+13b_5+12b_6+11b_7+11b_8+11b_9
 \le2+128e.
$$

Its forty-six-row score has total weight $1024$, full $N,O$ support
and anchor reward $368$, and zero excess in both complete catalogs.
That existing full theorem covers all ten labels, independent $N$
cells, constants, singletons, repeats, reversals and ordered embeddings.
Its original consequence uses the prefix transport proved in 2.2.
The actual amplitude contribution is
$-22\tau+552\tau+110\tau+11(u+v)=640\tau+11(u+v)$.
This is use of the credited theorem, without a new $128$ certificate.
Finally $d_{256}-d_0=3(253v-24u)/(253\cdot256)$.
Actual $a_9$ has not been replaced by a cap. $\square$

## 4. The credited full-head law at the low boundary

**Construction 4.1 (Every weight of the nineteen-schedule law $A$).**
Set $\kappa=u/253$ and $E=5\tau+24\kappa$. Each range below
supplies one copy for each named pair $(i,j)$; $m$ is that copy's
schedule mass. Terminal vectors are on stopped cells $0,10,11$.

| Schedule | $m$ | First vector $f$ | Middle vector $v$ | Exhaustion vector $z$ |
| --- | --- | --- | --- | --- |
| $(1,2)$ | $8\tau-85\kappa$ | $m e_1$ | $m e_2$ | $(4\tau-27\kappa)e_0+(2\tau-20\kappa)e_3+(\tau-35\kappa)e_4+(\tau-3\kappa)e_5$ |
| $(1,3),(2,3)$ | $3\tau-2\kappa$ | $m e_0$ | $m e_3$ | $m e_0$ |
| $(1,4),(2,4)$ | $\tau+13\kappa$ | $(\tau-48\kappa)e_0+61\kappa e_i$ | $m e_4$ | $m e_0$ |
| $(1,5),(2,5)$ | $21\kappa$ | $m e_0$ | $m e_5$ | $m e_0$ |
| $(3,4)$ | $2\tau-15\kappa$ | $m e_0$ | $m e_4$ | $(\tau+32\kappa)e_0+(\tau-47\kappa)e_5$ |
| $(3,5),(3,6),(4,5),(4,6),(5,6)$ | $\tau-8\kappa$ | $m e_0$ | $m e_j$ | $m e_0$ |
| $(3,7),(4,7),(5,7),(7,8)$ | $21\kappa$ | $m e_0$ | $m e_j$ | $m e_0$ |
| $(6,7)$ | $\tau-87\kappa$ | $m e_0$ | $m e_7$ | $(\tau-216\kappa)e_0+129\kappa e_8$ |
| $(6,8)$ | $79\kappa$ | $m e_0$ | $m e_8$ | $m e_0$ |

Add $R=O(1,2;1,2,0)$ with mass $1-24\tau$. For each positive-mass
row give its complete table $O(i,j;r,s,t)$ weight
$f(r)v(s)z(t)/m^2$. Omit zero-mass rows and add coincident table
weights. This specifies every complete-table weight of $A$.

**Lemma 4.2 (Normalization and the actual full head).**
The law is nonnegative and normalized, with one schedule budget per
row. It is precisely the credited DEV XVIII 337–339 construction at
the actual full head, with zero head transfer.

Proof. Each terminal vector has mass $m$, and every entry is
nonnegative for $0\le\kappa\le\tau/253$. In particular
$\tau-216\kappa\ge37\tau/253>0$.
The schedule-mass coefficients of $\tau$ total $8+6+2+2+5+1=24$;
those of $\kappa$ total
$-85-4+26+42-15-40+84-87+79=0$. Thus the core mass is $24\tau$
and the anchor completes mass one. Summing $f(r)v(s)z(t)/m^2$
over all three labels gives $m$; summing over two gives the remaining
terminal vector. Counterfactual cell masses are each $m$ and their
schedule mass is counted once.

The supplied sufficient head interval is
$a_2\le a_1\le1-7\tau-29\kappa$. Its upper endpoint exceeds the
actual $a_1=a_2=1-11\tau$ by
$4\tau-29\kappa\ge(4-29/253)\tau>0$. The optional transfer size
$a_1-a_2$ is zero. Thus no head is lowered or substituted.
$\square$

**Lemma 4.3 (All independent union rows on every word).**
For $A$, the mass outside $\{0,n\}$ is at most $E$ on every
entire first-zero fibre through eight.

Proof. Write $C(\tau,\kappa)$ for the unnormalized core vectors.
They obey the wordwise vector identity

$$
C(\tau,\kappa)=(\tau-253\kappa)C(1,0)+\kappa C(253,1).
$$

Both coefficients are nonnegative. These endpoint cores are measures,
without probability normalization at an unchanged target.
The following credited endpoint calculation retains all free suffixes.
Put $(h,s,t,x,y,z,b)=(w_2,w_3,w_4,w_5,w_6,w_7,w_8)$.
For $C(1,0)$ define

$$
B_0=2s(1-t)+st+(s+t)(2-x-y)+x(1-y)+y(1-z),\qquad
H_0=3(1-s)+(1-t).
$$

The exact outside masses are
$D_1=B_0+hH_0$, $D_2=B_0+H_0$,
$D_3=2+2(1-t)+t(2-x-y)+x(1-y)+y(1-z)$,
$D_4=5-xy-yz$, $D_5=5-y-yz$, and $D_6=D_7=D_8=5$.
For $q=s+t$, the suffix maximum of
$q(2-x-y)+x(1-y)+y(1-z)$ is $\max\{2q,q+1,1\}$.
For $st=00,01,10,11$, the maxima of $B_0$ are $1,2,4,5$
and $H_0$ is $4,3,1,0$, so $D_1,D_2\le5$.
In class three $t=0$ gives at most five and $t=1$ at most four.
All other displayed expressions are at most five.

For $C(253,1)$ put

$$
\begin{aligned}
B={}&491s(1-t)+206st+245[(s+t)(2-x-y)+x(1-y)]\\
 &+21(s+t+x)(1-z)+166y(1-z)+129yz
       +79y(1-b)+21z(1-b),\\
H={}&757(1-s)+266(1-t)+21(1-x).
\end{aligned}
$$

Direct addition of the same complete vectors gives

$$
\begin{aligned}
D_1&=B+hH+61(1-h),&D_2&=B+H,\\
D_3&=468+532(1-t)+42(1-x)+B(0,t,x,y,z,b),\\
D_4&=245+42(1-x)+B(1,0,x,y,z,b),\\
D_5&=8+B(1,1,0,y,z,b),\\
D_6&=1223-42z-21zb,&D_7&=1239-79b,&D_8&=1160.
\end{aligned}
$$

Substitutions into $B$ are literal substitutions in its six arguments.
Its $b$ coefficient is $-79y-21z\le0$, so its maximum has $b=0$.
The resulting $z$ coefficient is $21-21(s+t+x)-37y$; eliminating
$z$ adds its positive part. The complete sixteen maxima of $B$
at fixed $s,t,x,y$ are

| $st$ | $xy=00$ | $xy=01$ | $xy=10$ | $xy=11$ |
| --- | ---: | ---: | ---: | ---: |
| $00$ | 21 | 245 | 266 | 266 |
| $01$ | 511 | 511 | 532 | 287 |
| $10$ | 1002 | 1002 | 1023 | 778 |
| $11$ | 1228 | 983 | 1004 | 514 |

The maxima of $B+H$ by $st$ are $1289,1289,1289,1249$;
those of $B$ are $266,532,1023,1228$.
Since $H\ge0$, $D_1\le\max\{B+H,B+61\}\le1289$ and
$D_2\le1289$. The two $t$ cases of $D_3$ give $1287,1021$;
the two $x$ cases of $D_4$ give $1289,1268$; the two $y$ cases
of $D_5$ give $1236,991$. The last three formulas give maxima
$1223,1239,1160$. Thus all endpoint outside masses are at most
$1289$.

Outside mass is linear in the vectors for each fixed word. Hence it
is at most $5(\tau-253\kappa)+1289\kappa=5\tau+24\kappa=E$.
The anchor has no outside-$\{0,n\}$ mass on any first-zero fibre.
This proves every independent union row, including all multiple-zero
suffixes. The endpoint calculation is credited to DEV XVIII 338.
$\square$

**Theorem 4.4 (All rows and exact original error of $A$).**
Every $A,C,P$ and positive row through eight holds at $E$, and
for every continuation in 1.2 the law's exact original error is

$$
e_a(A)=5\tau+\max\{24u/253,v\}.
$$

Proof. Its core correct masses, constantly on entire first-zero fibres,
are

$$
(8\tau-24\kappa,8\tau-24\kappa,8\tau-24\kappa,
5\tau-24\kappa,4\tau-24\kappa,3\tau-24\kappa,
\tau-24\kappa,229\kappa).
$$

Nonzero first and middle outputs are their queried addresses, while
nonzero exhaustion outputs are later than both queries. Thus no
suffix bit changes a correct contribution. The anchor adds
$1-24\tau$ in classes one and two. With actual $u=253\kappa$,
this gives $c_n=a_n-E$ for every $n\le8$.
Each $C$ deficit equals $E$; separately, each $P$ deficit is
$D_n\le E$ by 4.3; each $A$ deficit is $D_n-E\le0$.
Negative singleton demands remain literal.

At the positive eight-word the same allocation is

$$
A_+=(1-E)e_0+(2\tau-20\kappa)e_3+(\tau-35\kappa)e_4
                  +(2\tau-50\kappa)e_5+129\kappa e_8.
$$

Its nonbase mass is exactly $E$ and no label above eight is emitted.
For actual $n>8$, Proposition 1.4 gives error $\max\{E,a_n\}$.
Actual $a_9=5\tau+v$ and all later amplitudes are at most $5\tau$.
This proves the uniform upper; actual first-zero-two and first-zero-nine
witnesses give equality with its larger term. Original execution of
these complete tables is specified in 6.2. $\square$

**Corollary 4.5 (Exact reduced value and sharp low original region).**
Let $\nu_C(\tau,u)$ be the complete eight-bit minimum in its own
catalog with the actual full head and all rows of 1.4. Then

$$
\nu_N(\tau,u)=\nu_O(\tau,u)=5\tau+24u/253.
$$

In the original family, cap $E=5\tau+24u/253$ is feasible in
either class exactly when $253v\le24u$. On this entire region,
both original minima equal $E$ and are attained.

Proof. The credited complete $253$ lower and the complete law of
4.1–4.4 match on eight bits. Its exact original error equals $E$
when $253v\le24u$. When $253v>24u$, Corollary 3.4 excludes
$E$ for every original competitor. Thus the boundary concerns actual
ninth obligations in the full classes. This evaluation uses the
credited $253$ certificate and full head allowance, without endpoint
rediscovery. $\square$

## 5. The complete credited endpoint at the old wedge boundary

**Construction 5.1 (Genuine $P^0,P^\star,Q$ and every table weight).**
Each row below is $O(i,j;f,m,z)$ with mass equal to its count
divided by $24$. This is precisely the genuine $P^0$.

| $i$ | $j$ | $f$ | $m$ | $z$ | Count |
| --- | --- | --- | --- | --- | ---: |
| 1 | 2 | 1 | 2 | 0 | 4 |
| 1 | 2 | 1 | 2 | 3 | 2 |
| 1 | 2 | 1 | 2 | 4 | 1 |
| 1 | 2 | 1 | 2 | 5 | 1 |
| 1 | 3 | 1 | 3 | 0 | 3 |
| 1 | 4 | 0 | 4 | 0 | 1 |
| 2 | 3 | 0 | 3 | 0 | 3 |
| 2 | 4 | 0 | 4 | 0 | 1 |
| 3 | 4 | 0 | 4 | 0 | 1 |
| 3 | 4 | 0 | 4 | 5 | 1 |
| 3 | 5 | 0 | 5 | 0 | 1 |
| 3 | 6 | 0 | 6 | 0 | 1 |
| 4 | 5 | 0 | 5 | 0 | 1 |
| 4 | 6 | 0 | 6 | 0 | 1 |
| 5 | 6 | 0 | 6 | 0 | 1 |
| 6 | 7 | 0 | 7 | 0 | 1 |

Its counts sum to $24$. Its $(1,4)$ first output is zero and its
class-one correct count is eleven; a different head-filled variant
with count twelve is not substituted. It ignores bits eight and nine.

The following sixteen deterministic rows of $P^\star$ have counts
divided by $3072$.

| $i$ | $j$ | $f$ | $m$ | $z$ | Count |
| --- | --- | --- | --- | --- | ---: |
| 1 | 3 | 0 | 3 | 0 | 391 |
| 1 | 4 | 1 | 4 | 0 | 110 |
| 1 | 5 | 1 | 5 | 0 | 27 |
| 2 | 4 | 0 | 4 | 0 | 110 |
| 2 | 5 | 0 | 5 | 0 | 27 |
| 3 | 5 | 0 | 5 | 0 | 132 |
| 3 | 6 | 0 | 6 | 0 | 125 |
| 3 | 7 | 0 | 7 | 0 | 15 |
| 3 | 8 | 0 | 8 | 0 | 15 |
| 4 | 5 | 0 | 5 | 0 | 117 |
| 4 | 6 | 0 | 6 | 0 | 110 |
| 5 | 6 | 0 | 6 | 0 | 127 |
| 5 | 7 | 0 | 7 | 0 | 17 |
| 5 | 8 | 0 | 8 | 0 | 17 |
| 7 | 8 | 0 | 8 | 0 | 17 |
| 8 | 9 | 0 | 9 | 0 | 17 |

Its five other schedule rows have these raw terminal vectors, also
divided by $3072$.

| Schedule | Count $m$ | First vector | Middle vector | Exhaustion vector |
| --- | ---: | --- | --- | --- |
| $(1,2)$ | 944 | $944e_1$ | $944e_2$ | $463e_0+220e_3+162e_4+99e_5$ |
| $(2,3)$ | 391 | $333e_0+58e_2$ | $391e_3$ | $391e_0$ |
| $(3,4)$ | 236 | $236e_0$ | $236e_4$ | $148e_0+88e_5$ |
| $(6,7)$ | 74 | $74e_0$ | $74e_7$ | $17e_0+4e_8+53e_9$ |
| $(6,8)$ | 53 | $53e_0$ | $53e_8$ | $17e_0+36e_9$ |

The deterministic counts total $1374$ and these schedule counts total
$1698$, with single total $3072$. Every terminal vector has its own
row count. For raw vectors $f,v,z$, assign complete table
$O(i,j;r,s,t)$ weight $f(r)v(s)z(t)/(3072m^2)$. It recovers all
cell marginals with one schedule budget, by 4.2.

Define $Q$ by changing only the $(6,7)$ exhaustion vector to
$17e_0+57e_8$. This replaces exactly the $53/3072$ mass of
$O(6,7;0,7,9)$ by $O(6,7;0,7,8)$. On the entire cube,

$$
Q_w-P^\star_w=\frac{53}{3072}w_6w_7(e_8-e_9).
$$

These are the credited complete laws; no ninth input is fixed or
projected in $P^\star$ or $Q$ here.

**Lemma 5.2 (Credited all-word endpoint bounds).**
On each whole core fibre $n\le7$, the correct counts of $P^0$ are
$(11,8,8,5,4,3,1)/24$ and its outside mass is at most $5/24$.
The correct counts of $P^\star,Q$ are
$(1081,1002,1002,618,490,362,106)/3072$, with outside mass at most
$662/3072$. Positive nonbase counts are $5$ and $662$ in the
respective denominators. On the entire later fibres their exact
$3072$-scaled correct and nonbase counts are

$$
\begin{array}{c|rrrr}
\text{law}&c_8&c_9&Z_8&Z_9\\\hline
P^\star&106&106&728&679\\
Q&159&53&728&679.
\end{array}
$$

Proof. For $P^0$, use $B_0,H_0$ from 4.3 with
$(s,t,x,y,z)=(w_3,w_4,w_5,w_6,w_7)$. Its outside counts are
$B_0+w_2H_0$, $B_0+H_0$,
$2+2(1-t)+t(2-x-y)+x(1-y)+y(1-z)$,
$5-xy-yz$, $5-y-yz$, $5$, $5$.
The suffix bounds in 4.3 give at most five. Correct counts follow
from the same tables. At a positive seven-prefix the law is
$(19e_0+2e_3+e_4+2e_5)/24$.

For $P^\star$, sum each first nonbase count times $(1-w_i)$,
middle nonbase count times $w_i(1-w_j)$ and exhaustion nonbase
count times $w_iw_j$. Its common nonbase polynomial is

$$
\begin{aligned}
Z={}&J+Lw_6+D(w_7+w_8)
       -17(w_6w_7+w_6w_8+w_7w_8+w_8w_9),\\
L={}&127-125w_3-110w_4-127w_5,\qquad D=17-15w_3-17w_5,\\
J={}&1139+391w_1+470w_2+523w_3+227w_4+161w_5\\
 &-463w_1w_2-391w_1w_3-110w_1w_4-27w_1w_5\\
 &-391w_2w_3-110w_2w_4-27w_2w_5
       -148w_3w_4-132w_3w_5-117w_4w_5.
\end{aligned}
$$

At fixed $w_1,\ldots,w_5$, its suffix maximum is
$J+\max\{0,L,D\}$. Indeed $D\le17$, take $w_9=0$; at $w_6=0$
the remaining maximum is $\max\{0,D,2D-17\}=\max\{0,D\}$,
while at $w_6=1$ further coefficients are nonpositive, giving $L$.
Subtracting the constant correct count and substituting lexicographic
free assignments through bit five gives all the credited grouped
outside maxima:

| First zero | Grouped maxima |
| --- | --- |
| 1 | $185,219,302,329,583,610,662,572,655,662,662,662,662,662,631,514$ |
| 2 | $655,662,662,662,662,662,631,514$ |
| 3 | $662,642,559,532$ |
| 4 | $662,635$ |
| 5 | $649$ |

For classes six and seven the restricted polynomials are
$995-15(w_7+w_8)-17(w_7w_8+w_8w_9)$ and
$760-32w_8-17w_8w_9$. Subtracting correct counts $362,106$ gives
outside maxima $633,654$. In classes eight and nine the nonbase
counts are constantly $728,679$; at the positive word it is $662$.

Correct counts are constant because nonzero first and middle outputs
are queried labels and nonzero exhaustion outputs are later than
both queries. The transfer defining $Q$ preserves every core
$A,C,P$ event and every base probability on all words. Both later
fibres have $w_6=w_7=1$, giving the displayed correct-count changes.
This is the credited complete endpoint calculation of DEV XVIII
319–320 and the $Q$ transfer, retaining all multiple-zero suffixes.
$\square$

**Theorem 5.3 (The credited one-budget law and old attained wedge).**
For $x,y\ge0$, $W=x+y\le24\tau$, set

$$
\mathcal B(x,y)=(1-24\tau)R+(24\tau-W)P^0+yP^\star+xQ.
$$

Its exact original error is

$$
\max\left\{
5\tau+\frac{22W}{3072},\
5\tau+u-\frac{159x+106y}{3072},\
5\tau+v-\frac{53x+106y}{3072}\right\}.
$$

On $181v\ge75u$, the complete law with

$$
x=\frac{1536}{53}(u-v),\qquad
y=\frac{12}{53}(181v-75u),\qquad W=12(u+v)
$$

attains the old common original minimum $5\tau+d_{\rm sum}$ in
both classes. On $181v\le75u$, the old choice $x=3072u/181$,
$y=0$ remains a lawful upper with exact error $5\tau+22u/181$.

Proof. All branch weights are nonnegative and sum to one.
Put $t=W/3072$ and $h=5\tau+22t$.
On every core word, the independent outside mass is at most
$5(\tau-128t)+662t=h$ by 5.2. Correct deficits in classes two
through seven equal $h$; the class-one deficit is $2\tau+327t\le h$
because $305t\le305\tau/128<3\tau$.
These correct masses are at most actual targets, so base deficits
are at most the separately bounded outside masses.

On the entire class-eight and class-nine fibres,

$$
\begin{aligned}
c_8&=(159x+106y)/3072,&D_8&=5\tau-(71x+18y)/3072,\\
c_9&=(53x+106y)/3072,&D_9&=5\tau-(14x+67y)/3072.
\end{aligned}
$$

Both outside masses are at most $5\tau$, and
$c_n\le159W/3072\le159\tau/128<5\tau\le a_n$ in these classes.
Their base deficits are bounded by their outside deficits, while
their correct deficits give the last two error entries. Positive
nonbase mass equals $h$. For actual $n>9$, the exact tail identity
gives error $h$ since $a_n\le5\tau$. Actual class-two, class-eight
and class-nine witnesses give equality with the maximum. Each row
uses this same whole law.

On the wedge the displayed $x,y$ are nonnegative and $W\le24\tau$.
The identities $181x+128y=3072u$ and $75x+128y=3072v$ make
all three error entries $5\tau+11(u+v)/128$. The credited $128$
lower of 3.4 matches against every original competitor. This is
exactly the DEV XVIII 324–327 wedge under
$t'=(u+v)/2$, $\delta=(u-v)/2$: its donor condition
$\delta\le53t'/128$ is $75u\le181v$, and
$\delta\le\tau-t'$ is $u\le\tau$.

For $x=3072u/181$, $y=0$, nonnegativity follows from $3072/181<24$.
The three errors are $5\tau+22u/181$, the same value, and
$5\tau+v-53u/181$. The last is at most the first exactly when
$181v\le75u$. This evaluates the old construction without asserting
a full-class complementary lower plane. $\square$

## 6. One complete intermediate law

**Theorem 6.1 (Interpolation with the actual ninth amplitude).**
For $u>0$, put

$$
v_0=\frac{24u}{253},\qquad v_W=\frac{75u}{181},\qquad
v_0\le v\le v_W,\qquad
\theta=\frac{181(253v-24u)}{14631u}.
$$

Let $A$ be exactly Construction 4.1, regarding it as a nine-bit law
that ignores input nine, and let $B=\mathcal B(3072u/181,0)$ from
5.3. Define one complete-table allocation by

$$
\Lambda_D=(1-\theta)A_D+\theta B_D,\qquad
H(u,v)=\frac{1272u+1222v}{14631}.
$$

Every table weight is specified by 4.1, 5.1 and this formula; unlisted
weights are zero and coincident weights add. This is a nonnegative
normalized law with original realizations in both classes and exact
original error

$$
e_a(\Lambda)=5\tau+H(u,v)
$$

for every entire continuation in 1.2. It is an attained upper bound;
its optimality on the open intermediate interval is not established.

Proof. Since $v_W-v_0=14631u/(181\cdot253)>0$,
$\theta=(v-v_0)/(v_W-v_0)\in[0,1]$.
At the first endpoint, 4.4 gives cap $5\tau+d_0$ with actual
ninth amplitude $5\tau+v_0$. At the second, 5.3 gives cap
$5\tau+22u/181$ with actual ninth amplitude $5\tau+v_W$.
The endpoint targets have the same actual full head, the same
$a_3,\ldots,a_8$, and any fixed continuation from ten onward.

Their same affine combination has actual ninth amplitude
$5\tau+(1-\theta)v_0+\theta v_W=5\tau+v$, with every other
amplitude unchanged. For each fixed word and each independent event
$A,C,P$, both its probability and its demand are affine in these
same weights. The complete endpoint inequalities therefore prove
every row, including every multiple-zero suffix, for this one
$\Lambda$. The positive row also interpolates. The same complete
law combination preserves normalization; different events and cells
never receive different budgets.

The mixed cap increment is

$$
(1-\theta)\frac{24u}{253}+\theta\frac{22u}{181}
 =\frac{1272u+1222v}{14631}=H(u,v).
$$

Both endpoint positive nonbase masses equal their caps. Both
class-two correct masses are $1-16\tau$ minus their respective cap
increments, constantly on the whole fibre. Hence the mixed positive
nonbase mass and class-two correct deficit both equal $5\tau+H$.
An actual class-two source attains that value. Every actual
$n>9$ has exact error $5\tau+H$ by 1.4, since no label $n$
is emitted and $a_n\le5\tau$. All actual first zeros through nine
are covered by their complete rows. This proves the exact original
error with the unchanged actual continuation. $\square$

**Proposition 6.2 (One seed and hard two actual requests).**
All complete laws in 4–6 have original stopped executions and counted
$N$ completions with identical output laws, zero advice and finite
measurable handoff for every seed and source.

Proof. Partition one source-independent uniform seed in $[0,1)$
into the finitely many complete-table intervals. For $\Lambda$ one
may first select its endpoint branch and then its complete table,
using the corresponding rescaled coordinate of that same seed.
Half-open intervals specify endpoints and zero intervals are omitted.
Before replies, the seed fixes the whole schedule and all
counterfactual terminal labels. The product weights in 4.1 and 5.1
are explicit finite complete-table probabilities.

In $O$, execute the selected increasing pair to its first queried
zero or exhaustion, emit its actual $\theta_j$, and hand it to
the unchanged consumer. In $N$, acquire both actual addresses on
that same source and seed and reconstruct the stopped output on
$00,01,10,11$. An ignored second reply counts as an actual request.
Constants and singletons use their declared calls. Every execution is
finite and measurable, with at most two actual calls and zero advice.
Only the selected schedule's replies are observed; the proof's
actual witnesses give no free source label or full word.
This couples these constructed rules without replacing an arbitrary
competing $N$ law by a stopped one. $\square$

**Proposition 6.3 (Closed boundaries and all degeneracies).**
At $v=v_0$ the mixture is $A$; at $v=v_W$ it is $B$, which also
equals the old wedge law there. At $u=0$, necessarily $v=0$;
use 4.1 with $\kappa=0$, without dividing by $u$. At $\tau=1/24$
the anchor vanishes. At $u=\tau$ the stock
$\tau-216\kappa$ remains strictly positive. Head ties, $a_8=a_7$,
$a_{10}=5\tau$, later ties and zero branch weights are all included.
The algebraic $\tau=0$ point is outside the positive original domain.

Proof. The endpoint values follow from $\theta$. At the wedge
boundary, $y=0$ and $x=12(u+75u/181)=3072u/181$, so complete
allocations agree. The other cases follow from the explicit
nonnegative stocks and omission of zero-mass rows; no sampler or
weight formula divides by a vanishing mass.

Under the active convention $a_i>c$, the low optimum with $u>0$
has horizon eight, since $a_8-E=229u/253>0$ and $a_9\le E$.
The equality $a_9=E$ at $v_0$ is inactive. At $u=v=0$ the optimum
has horizon seven. In the open intermediate sector,

$$
v-H(u,v)=\frac{53(253v-24u)}{14631}>0,
$$

so the constructed cap has horizon nine. The old wedge with $u>0$
also has horizon nine because
$a_9-(5\tau+d_{\rm sum})=(117v-11u)/128>0$ there.
Every later amplitude is inactive at all the constructed caps.
These statements use actual amplitudes and retain closed ties.
$\square$

## 7. Exact solved regions and the remaining positive interval

**Theorem 7.1 (Separate compact minima and entire-tail independence).**
For $C=N,O$, let $\Delta_C^9$ be its own complete nine-bit catalog
simplex and put

$$
\begin{aligned}
f_C(\lambda)=\max\bigl(&
\{1-a_n-p_w(0),\ a_n-p_w(n),\ 1-p_w(0)-p_w(n):
                  w\in\Omega_n,\ n\le9\}\\
&\cup\{1-p_+(0)\}\bigr),\qquad
m_C=\min_{\lambda\in\Delta_C^9}f_C(\lambda).
\end{aligned}
$$

Each minimum exists, equals its own original attained minimum and
depends only on $a_1,\ldots,a_9$ among all continuations in 1.2.
Its positive closed caps are feasible exactly when $c\ge m_C$.
Counted completion gives $m_N\le m_O$.

Proof. Both catalogs are finite, retaining every independent $N$
label choice. A finite maximum of continuous affine functions has a
minimum on its compact simplex, separately for each class.
The complete $253$ certificate on the first eight coordinates gives
$m_C\ge5\tau+d_0\ge5\tau>0$. The explicit common upper laws give
$m_C\le331\tau/64\le331/1536<1$.

For any original competitor, 2.2 supplies a complete nine-bit law
at every positive met cap $c\le1$. Decreasing caps to its error
shows that $m_C$ is at most that error; at error one use $m_C<1$.
Conversely, execute a finite minimizer in its own class by one
uniform seed partition of complete tables. In $N$, acquire its
whole preselected schedule and use its independent cell output; in
$O$, execute its increasing schedule with the prescribed stop.
Low-word rows give cap $m_C$ for actual $n\le9$. For every
actual $n>9$ the exact tail error is

$$
\max\{1-p_+(0),a_n\}\le m_C,
$$

since the positive row holds and $a_n\le5\tau\le m_C$.
This finite minimizer is therefore an original attainer.
The two comparisons establish equality of finite and original minima,
separately, and the proof works for every allowed entire continuation.
Its objective uses only the first nine amplitudes, proving tail
independence. The attainer meets every larger cap, and a smaller cap
contradicts minimality. Counted completion gives the class inequality;
compactness gives no reverse class comparison. $\square$

**Theorem 7.2 (The exact established parameter map).**
Define a common upper increment by

$$
\mathcal H(u,v)=
\begin{cases}
24u/253,&253v\le24u,\\
(1272u+1222v)/14631,
 &u>0,\quad24u/253\le v\le75u/181,\\
11(u+v)/128,&181v\ge75u.
\end{cases}
$$

At $u=v=0$ set $\mathcal H=0$; overlapping boundary formulas agree.
For every fixed actual profile and every entire continuation in 1.2,

$$
5\tau+\max\{d_0,d_{256},d_{\rm sum}\}
 \le m_N\le m_O\le5\tau+\mathcal H(u,v).
$$

The established exact and open regions are as follows.

| Parameters | Original conclusion established here |
| --- | --- |
| $u=v=0$ | $m_N=m_O=5\tau$ |
| $u>0$, $253v\le24u$ | $m_N=m_O=5\tau+24u/253$ |
| $u>0$, $181v\ge75u$ | $m_N=m_O=5\tau+11(u+v)/128$ |
| $u>0$, $24u/253<v<75u/181$ | Both values remain unevaluated; the displayed necessary/achievable interval has strictly positive width |

In every solved region the common law attains the minimum and every
positive closed cap is feasible exactly when it is at least that
value. In the open intermediate sector, equality or separation of the
two minima is unproved.

Proof. The lowers are 3.4. The upper uses, respectively, the complete
law 4.1, the single mixture 6.1, or the old complete wedge law 5.3.
Thus one whole law supplies each upper, without combining independent
event optima. On the low region, $d_{256}\le d_0$, and for $u>0$,

$$
d_{\rm sum}(u,v)\le d_{\rm sum}(u,24u/253)
 =d_0-\frac{25u}{128\cdot253}<d_0.
$$

The matching $253$ bound proves equality there. The old wedge has
the matching $128$ lower. At $u=v=0$ both reduce to $5\tau$.
Closed-cap equivalence follows from 7.1, including every boundary.

In the open intermediate sector $d_{256}>d_0$, and

$$
d_{256}-d_{\rm sum}=\frac{2u-19v}{256}.
$$

The effective lower is $d_{256}$ when $19v\le2u$ and
$d_{\rm sum}$ when $19v\ge2u$. Exact upper-minus-lower differences are

$$
\begin{aligned}
\mathcal H-d_{256}
 &=\frac{1063(253v-24u)}{14631\cdot256}>0,\\
\mathcal H-d_{\rm sum}
 &=\frac{25(75u-181v)}{14631\cdot128}>0.
\end{aligned}
$$

Both are strictly positive throughout the open sector, including the
internal lower-bound switch. The strip $24u/253<v<2u/19$ is
nonempty for $u>0$ and is precisely where the $256$ lower improves
both other displayed lowers. Positive necessary/achievable width
proves neither upper optimality nor an $N/O$ separation. $\square$

**Proposition 7.3 (Retained $217$ law and original counterexample).**
The credited law $K$ remains a common original law with exact error
$5\tau+\max\{22u/217,v\}$. For every $0<\tau\le1/24$ and
$0<u\le\tau$, its permitted $v=0$ member with every allowed
continuation still refutes the universal complementary original lower
plane $5\tau+22u/181$. The sharper reduced evaluation in 4.5 does
not invalidate that law or its error computation.

Proof. The following local specification retains the relevant scope.
Define $Q_8$ from the genuine $Q$ of 5.1 by fixing input nine to
zero and sending label nine to zero. This defines a new finite law;
it supplies no free observation of an actual reply. Its former
count-$17$ $(8,9)$ branch becomes constant zero and its $(6,8)$
exhaustion vector becomes $53e_0$. Put $s=u/217$,

$$
\begin{aligned}
L&=(1-24\tau)R+24(\tau-128s)P^0+3072sQ_8,\\
K&=L+36s\{O(6,7;0,7,8)-O(6,7;0,7,0)\}.
\end{aligned}
$$

The transfer uses existing $P^0$ stock, whose remainder is
$\tau-164s\ge53\tau/217>0$. It preserves normalization and changes
the whole cube by $36s\,w_6w_7(e_8-e_0)$.
On the full activation set $w_6=w_7=1$, the $P^0$ outside counts
in the first two classes are at most four: for
$(w_3,w_4)=00,01,10,11$, $B_0+H_0$ is
$4,4-w_5,4-w_5,3-2w_5$. Class three gives
$4-w_4-w_4w_5$, class four $4-w_5$, class five three; classes
six and seven cannot activate. Active core outside mass is therefore
at most $4(\tau-128s)+662s+36s=4\tau+186s$.
Its slack below $h=5\tau+22s$ is at least $\tau-164s>0$.
On the inactive set, the bound is $5(\tau-128s)+662s=h$.

Core correct masses are
$(1-13\tau-327s,1-16\tau-22s,8\tau-22s,5\tau-22s,
4\tau-22s,3\tau-22s,\tau-22s)$, and $c_8=195s$.
Correct deficits equal $h$ except class one's $2\tau+327s\le h$.
All correct masses are at most targets, so their base deficits are
bounded by the independently checked outside deficits.
Class-eight outside mass is $5\tau-71s$; its transfer stays inside
$\{0,8\}$. The positive $Q_8$ nonbase count is $626$, so $K$'s
positive nonbase mass is $5(\tau-128s)+626s+36s=h$.
These checks include every multiple-zero suffix. The exact later-tail
identity and actual witnesses give the stated original error, with
lawful execution as in 6.2.

At $v=0$ the strict improvement over the old plane is
$792u/(181\cdot217)>0$. For general allowed $v$, this same law
improves it exactly when $v<22u/181$. The plane still correctly
evaluates its own old law in 5.3, without full-class necessity.
The folded $128$ lower $5\tau+11u/117$ remains valid; the $253$
lower exceeds it by $25u/(253\cdot117)>0$ for $u>0$.

For an actual comparison, at $\tau=u=1/24$, $v=0$, take
$a_n=(5/24)2^{-(n-9)}$ for $n\ge9$, retaining actual $a_9=5/24$.
The old $K$ error is $369/1736$ and the exact value from 4.5 is
$1289/6072$, with positive difference $179/658812$.
The legal source $(r,g)=(19,419)$ has $F_{19}=4181$,
$419\le g\le836$, and $N=1751840$. This integer is even and has
digit sum $26$, so its first absence is two. The new law's
correct-two mass is $2000/6072$ against target
$13/24=3289/6072$, giving exact deficit $1289/6072$.
Its all-word upper proves TV equality there. No source information
is granted to the acquisition by using this proof witness. $\square$

## 8. Remaining original obligations and scope

**Proposition 8.1 (The surviving full-score face question).**
In either complete nine-bit catalog, feasibility at
$E_{\rm sum}=5\tau+d_{\rm sum}$ forces support on complete
$Y_{128}$-score-$368$ maximizers and tightness of every positively
scored row. All unscored independent $A,C,P$ and positive rows
remain constraints. Conversely one normalized allocation on that
support satisfying every full row is feasible.
For $u>0$, the $256$ lower excludes this cap for $v<2u/19$.
Feasibility for $2u/19\le v<75u/181$ is not settled here,
including the tie $v=2u/19$.

Proof. At this cap the demanded $128$ reward is $368$. For one
normalized feasible allocation,

$$
0=\sum_D\lambda_D(368-Y_{128}z_D)
 +\sum_r(Y_{128})_r
       [p(\text{event }r)-\text{demand }r].
$$

Complete support and full feasibility make every summand nonnegative,
giving the face restriction. Its converse is the all-row criterion;
7.1 supplies original realization. The exclusion follows from
$d_{256}-d_{\rm sum}=(2u-19v)/256$. A tie of lower bounds gives
no feasible allocation on their common face. $\square$

**Definition 8.2 (The unchanged universal signed-budget question).**
For a full score $y\ge0$, write $z_D$ for full event incidence,
$r=z_R$, $W_y=yr$, $B_C(y)=\max_D yz_D$,
$\Delta_C(y)=B_C(y)-W_y$, and
$F_{Q(y)}(b,e)=y(d(b,e)-r)$. Here $Q(y)$ is the affine score
quotient, distinct from the probability law $Q$ in 5.1. Put

$$
\begin{gathered}
H_L=\{1\ge b_1\ge\cdots\ge b_L\ge e\ge0,\ b_2=b_3,\
0\le\sum_{n=3}^Lb_n-(L+1)e\le1-b_1\},\\
\sigma_{H_L}(q)=\max_{(b,e)\in H_L}F_q(b,e).
\end{gathered}
$$

For every $L\ge3$ and every unrestricted full unit-$O$ score,
$\Delta_O(y)\le1$, the universal positive alternative still requires
one unrestricted full $V\ge0$ and one common
$\vartheta\in[0,1]$ jointly paying

$$
\Delta_N(V)+\vartheta\le1,\qquad
\sigma_{H_L}(Q(y)-Q(V))\le\vartheta.
$$

The residual is signed; nonzero zero-cost $V$ at $\vartheta=1$
remains allowed. The strict alternative requires the same actual
feasible profile in $H_N$, one complete $N$ allocation of mass
$M\ge1$, a full unit-$O$ score with $F_{Q(y)}(b,e)>M$, an
actual original $N$ attainer and a uniform strict lower against every
original arbitrary-address, full-carrier $O$ competitor. Here $H_N$
denotes the full-$N$ feasible part of the displayed hull, with the
same affine allocation convention as in 3.3. These are the original
obligations of DEV XVIII 323.3 and 340.4.

No regional common law here establishes either unrestricted
alternative. In the open fixed-family sector
$24u/253<v<75u/181$, a matching full-class lower, a better complete
law or another exact theorem is still required. Eliminating parameters
inside a restricted construction cannot supply full-catalog necessity.
In particular a fixed-base tail-relabeling restriction is not an
original competitor restriction; the $217$ transfer moves base stock,
and the nineteen-schedule law is a different complete law.

**Reference frame 8.3 (Whole procedures and bounded ordinary conclusions).**
The mathematical framework is finite convex allocation of whole
probability vectors, full nonnegative dual support and independent
TV event constraints. Blackwell's *Comparison of Experiments*,
sections 2–3 and Theorem 2, supplies the whole attainable loss-vector
viewpoint described in the supplied texts. Kaniewski, Lee and de Wolf's
*Query complexity in expectation*, Definitions 6 and 8 and Theorem 9,
concerns nonnegative scalar expectations with maximum supported path
cost. Coefficient sampling and scalar rescaling do not supply a
normalized joint output law, equal counterfactual schedule masses or
increasing stopping. Those properties have separate proofs here.
These are framework credits as supplied, without an external
literature body or exhaustive priority comparison as a premise.

The additional result is the complete $256$ lift, its full-class
actual ninth obstruction and one intermediate complete-law synthesis.
The exact reduced and low-region values apply the credited $253$
certificate and full-head law. The $128$ lower, old wedge,
$P^0,P^\star,Q$, $217$ counterexample, arithmetic realization and
compact transport retain their existing credits. Expanded audits are
proof verification, without endpoint discovery credit.

The stopping point is the strictly positive interval of 7.2 and the
unrestricted obligations of 8.2. Neither intermediate minimax value,
intermediate $N/O$ equality or separation, the universal signed-budget
alternative nor overall unrestricted acquisition is settled.
These are ordinary analytic proofs, without formal-kernel verification,
worldwide novelty, physical efficiency, general neural-network,
empirical-learning or quantum/classical-transfer claims. Their scope is
the explicit visible source, observation model, full carrier and actual
hard resource classes.

**Proposition 8.4 (No transfer to unchanged nonatomic accuracy).**
Every constructed finite marked output law has TV distance one from
every unchanged original nonatomic target.

Proof. Its finite support of actual marks has output mass one and
$\mu_x^{\rm orig}$ mass zero. TV is at least their difference one
and at most one. Thus the selected marked-target results give no
accuracy against those unchanged nonatomic targets. $\square$

## 追加锚（本行以下为增补区）
