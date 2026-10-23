# Self-calibrating acquisition resources: complete five-active projection and rational separation

> 本卷为普通理论参考输入，消化方言为 `generic-v1`；locator 由本文件字节决定。
> 卷首、既有正文与终端追加锚保持只增不减。新增章写在追加锚之后，并以同一追加锚结束。
> 证明采用普通数学与有限精确算术；本卷未经 Lean kernel 验证，不承担冻结、覆盖或机器状态。

## 140. Original sources and complete common-budget allocations

本卷的第一单元给出完整五活跃闭 cap 比较，包括正 $\kappa_3$ 区域与其残余互补区域；
第二单元给出任意固定有限活跃长度的条件有理严格 cap 分离范式。
两个单元都保留全部原始尾幅、单一公共种子与实际 hard-two 请求资源。
任意 $L\ge6$ 的包含关系仍为开放义务。

**Definition 140.1 (Actual source and selected comparison laws).** Retain
[Acquisition Resources, Definition 90.1](KBONACCI_SELF_CALIBRATING_ACQUISITION_RESOURCES.md#90-adaptive-preselected-and-increasing-first-zero-stop-acquisitions)
and [Continuation, Definition 110.1](KBONACCI_SELF_CALIBRATING_ACQUISITION_RESOURCES_CONTINUATION.md#110-exact-closed-cap-transport-on-the-original-countable-source).
In explicit notation,

$$
\begin{aligned}
F_0&=0,\quad F_1=1,\quad F_{r+2}=F_{r+1}+F_r,\\
X&=\{(r,g):r\text{ prime},\ g\in\mathbb Z,
       \lceil F_r/10\rceil\le g\le\lfloor F_r/5\rfloor\},\\
N(r,g)&=1+F_rg,\quad q_i(x)=\mathbf1_{p_i\mid N(x)},\quad
n(x)=\min\{i\ge1:q_i(x)=0\},
\end{aligned}
\tag{140.1}
$$

where $p_1<p_2<\cdots$ are the primes. The labels $(r,g)$, $N(x)$ and
$n(x)$ are not supplied observations. The prime answers are static.
The source is the actual countable set $X$, with finite prime support
at each source, and $n(x)$ is finite. Actual occupancy of every finite
answer pattern is supplied by
[Boundaries, Theorem 35.2](KBONACCI_SELF_CALIBRATING_BOUNDARIES.md#35-exact-finite-divisibility-fibres-in-canonical-fibonacci-windows).
It is not an independent Boolean source or a probability distribution on sources.

The original carrier is
$\Theta=(\bigsqcup_{j\ge1} B_j)\sqcup(\bigsqcup_{j\ge1}P_j)$,
with every block a copy of $(0,1)$ and its disjoint-union Borel sigma algebra $\mathcal F$.
The unchanged consumer is unknown on $B_j$ and proposes $j$ on $P_j$;
its original nonatomic targets $\mu_x$ remain fixed. Distinct measurable
marks are $\theta_r=(B_1,1/(r+2))$, $r\ge0$.
For an entire sequence

$$
1\ge a_1\ge a_2\ge\cdots>0,\qquad \lim_{i\to\infty}a_i=0,
\tag{140.2}
$$

separately declare the selected laws
$\lambda_x^a=(1-a_{n(x)})\delta_{\theta_0}+a_{n(x)}\delta_{\theta_{n(x)}}$.
They are the comparison targets here. Define

$$
e_a(A)=\sup_{x\in X}\operatorname{TV}(\widehat\lambda_{A,x},\lambda_x^a),
\qquad
\operatorname{TV}(\nu,\lambda)=\sup_{E\in\mathcal F}|\nu(E)-\lambda(E)|.
\tag{140.3}
$$

A source-independent common seed fixes one rule for all actual sources.
There is zero advice, no extra observation and sourcewise almost-sure
finite handoff. $\mathcal N_2$ preselects a sequence of at most two
actual requests and obtains its replies; addresses can be arbitrary
and can repeat. $\mathcal O_2$ preselects a strictly increasing sequence
of at most two and stops at its first queried zero or exhaustion.
A queried zero need not be the actual first absence, and an output need
not be its mark. Every actual request, including an ignored or repeated
request, counts. All original competitors may output any original tape.
Neither address, depth of an unexecuted computation, runtime, expected
count nor a distribution on $X$ replaces this resource.

At an original positive cap $0<e\le1$ its active length is
$L=\max(\{i:a_i>e\}\cup\{0\})$, finite by (140.2).
All original amplitudes after that length are retained.

**Definition 140.2 (Complete finite classes).** For each integer $L\ge1$,
write $B_L=\{0,1\}^L$, $J_L=\{0,\ldots,L\}$ and

$$
D_L=\{(a_1,\ldots,a_L,e):1\ge a_1\ge\cdots\ge a_L\ge e\ge0\}.
\tag{140.4}
$$

For a word $b$ with a zero put $n_L(b)=\min\{i:b_i=0\}$ and
$\eta_b=(1-a_{n_L(b)})e_0+a_{n_L(b)}e_{n_L(b)}$; put $\eta_{1^L}=e_0$.
These finite targets are algebraically defined on all of $D_L$, including
auxiliary $e=0$, $a_L=e$, zero amplitudes and ties. Original active
profiles instead have $0<e<a_L$ and retain a full tail with $a_{L+1}\le e$.
The finite word $1^L$ never denotes an infinite all-positive actual source.

Order the schedules as
$\mathcal S_L=(\varnothing,(1),\ldots,(L),(1,2),(1,3),\ldots,(L-1,L))$,
with pairs in lexicographic order. Empty and singleton cells are respectively
$\varnothing$ and $(0,1)$. For $N$ an increasing pair has cells
$(00,01,10,11)$; for $O$ it has $(0,10,11)$, and stopped cell $0$
is shared by acquired patterns $00,01$. Denote the selected cell by
$c_C(b,S)$ for $C=N,O$.
All labels in $J_L$ are allowed in every cell, including unqueried labels.

A complete allocation consists of nonnegative $w_S,T_{S,c,r}$ satisfying

$$
\sum_{r=0}^L T_{S,c,r}=w_S\quad\text{for every cell }c\text{ of }S,
\qquad \sum_{S\in\mathcal S_L}w_S=1.
\tag{140.5}
$$

Its probability-vector kernel is
$p_b(r)=\sum_S T_{S,c_C(b,S),r}$.
Let $K_{C,L}$ be all these allocations without cap constraints; their
kernel classes are $\mathscr N_L$ and $\mathscr O_L$, respectively.
There is one schedule mass shared by all counterfactual cells of that
schedule and one global schedule budget. No label, word or cell has an
independent probability normalization.
Writing each terminal cell as a vector, the two full pair contributions are

$$
\begin{aligned}
p^N_b&=T_{\varnothing}+\sum_i\bigl((1-b_i)T_i^0+b_iT_i^1\bigr)\\
 &\quad+\sum_{i<j}\bigl((1-b_i)(1-b_j)T_{ij}^{00}
 +(1-b_i)b_jT_{ij}^{01}+b_i(1-b_j)T_{ij}^{10}+b_ib_jT_{ij}^{11}\bigr),\\
p^O_b&=T_{\varnothing}+\sum_i\bigl((1-b_i)T_i^0+b_iT_i^1\bigr)\\
 &\quad+\sum_{i<j}\bigl((1-b_i)T_{ij}^{0}
                 +b_i(1-b_j)T_{ij}^{10}+b_ib_jT_{ij}^{11}\bigr).
\end{aligned}
\tag{140.8}
$$

In particular every additional zero in a low word is part of its actual
cell selection; it is not discarded in favor of a single-zero surrogate.
The terminal-coordinate counts, excluding explicit $w$ variables, are

$$
\begin{aligned}
d_N(L)&=(L+1)\left(1+2L+4\binom L2\right),\\
d_O(L)&=(L+1)\left(1+2L+3\binom L2\right).
\end{aligned}
\tag{140.6}
$$

At $L=5$ there are 16 schedules, 51 $N$ cells and 41 $O$ cells,
with 306 and 246 terminal coordinates respectively.
Eliminating $w$ gives 36 independent $N$ equalities and 26 independent
$O$ equalities: compare every other cell mass to a chosen first cell in
its schedule, then normalize the sum of those first-cell masses.

**Proposition 140.3 (One shared seed realizes the complete models).**
The models (140.5) describe precisely the whole finite preselected and
increasing first-zero-stop classes at hard count two.

**Proof.** Static repeated queries in a finite $N$ schedule can be
replaced by one query and its repeated static reply; a reversed distinct
pair can be sorted with its table permuted. This represents its law,
without allowing an uncounted observation in the original execution.
For a seeded rule integrate each cell's predetermined output indicator
over the seed event choosing $S$. The resulting $T_{S,c,r}$ have common
mass $w_S$ in all cells, and the schedule events have total mass one.
An $O$ rule uses the same output on both patterns in its first-zero cell.

Conversely, for each $w_S>0$ put $\pi_{S,c}(r)=T_{S,c,r}/w_S$.
For every deterministic table $f:\operatorname{cells}_C(S)\to J_L$ put

$$
q_{S,f}=w_S\prod_{c\in\operatorname{cells}_C(S)}\pi_{S,c}(f(c)).
\tag{140.7}
$$

These nonnegative masses sum over tables to $w_S$ and over schedules to
one. Their marginal sum over $f(c)=r$ is $T_{S,c,r}$.
One partition of $U\in[0,1)$ into half-open intervals of masses
$q_{S,f}$ fixes the schedule and its entire table before replies.
Zero-mass schedules are omitted. The product is a chosen coupling of
counterfactual cells, not independent source-dependent random choices.
This supplies all word-law coordinates from one common seed.
For rational allocations all $q_{S,f}$ are rational.
Queries to $S$ and output of its table label are finite and measurable;
in $O$ execution stops at its first queried zero.
All allowed terminal labels and schedules remain in the model. $\square$

For real-parameter continuity a different interval realization using
absolute terminal masses is given in Section 147. The product construction
is especially useful for the rational normal form.
The already supplied [Theorem 109.1](KBONACCI_SELF_CALIBRATING_ACQUISITION_RESOURCES_CONTINUATION.md#109-an-exact-coefficient-criterion-with-one-common-probability-budget)
identifies $\mathscr O_L=\mathscr C_L\subseteq\mathscr N_L$ by its
coordinatewise coefficient criterion. The already supplied
[Theorem 110.2](KBONACCI_SELF_CALIBRATING_ACQUISITION_RESOURCES_CONTINUATION.md#110-exact-closed-cap-transport-on-the-original-countable-source)
transports both full original classes to these finite feasibility slices
at the exact closed cap, including arbitrary original addresses,
repetitions and full-carrier outputs. These suppliers are reused.

## 141. Every five-bit word and all 94 TV rows

**Definition 141.1 (Indexed event system).** Order $B_5$ lexicographically,
with $b_1$ the first digit. At each of its 31 zero-containing words list,
in order, the events $\{0\},\{n_L(b)\},\{0,n_L(b)\}$.
At $11111$ list $\{0\}$. Rows are indexed $j=0,\ldots,93$;
rows $3k,3k+1,3k+2$ belong to the $k$th zero-containing word, $0\le k<31$.
Set $d_j(a,e)=\eta_{b_j}(E_j)-e$. Every cap row is
$p_{b_j}(E_j)\ge d_j(a,e)$.
The following table gives each of the 94 separate rows, including all
multiple-zero words and all union events.

<!-- mathematical-data: tv94 -->

| Row $j$ | Word $b_j$ | Event $E_j$ | Lower bound $d_j$ |
| --- | --- | --- | --- |
| 0 | 00000 | $\{0\}$ | $1-a_1-e$ |
| 1 | 00000 | $\{1\}$ | $a_1-e$ |
| 2 | 00000 | $\{0,1\}$ | $1-e$ |
| 3 | 00001 | $\{0\}$ | $1-a_1-e$ |
| 4 | 00001 | $\{1\}$ | $a_1-e$ |
| 5 | 00001 | $\{0,1\}$ | $1-e$ |
| 6 | 00010 | $\{0\}$ | $1-a_1-e$ |
| 7 | 00010 | $\{1\}$ | $a_1-e$ |
| 8 | 00010 | $\{0,1\}$ | $1-e$ |
| 9 | 00011 | $\{0\}$ | $1-a_1-e$ |
| 10 | 00011 | $\{1\}$ | $a_1-e$ |
| 11 | 00011 | $\{0,1\}$ | $1-e$ |
| 12 | 00100 | $\{0\}$ | $1-a_1-e$ |
| 13 | 00100 | $\{1\}$ | $a_1-e$ |
| 14 | 00100 | $\{0,1\}$ | $1-e$ |
| 15 | 00101 | $\{0\}$ | $1-a_1-e$ |
| 16 | 00101 | $\{1\}$ | $a_1-e$ |
| 17 | 00101 | $\{0,1\}$ | $1-e$ |
| 18 | 00110 | $\{0\}$ | $1-a_1-e$ |
| 19 | 00110 | $\{1\}$ | $a_1-e$ |
| 20 | 00110 | $\{0,1\}$ | $1-e$ |
| 21 | 00111 | $\{0\}$ | $1-a_1-e$ |
| 22 | 00111 | $\{1\}$ | $a_1-e$ |
| 23 | 00111 | $\{0,1\}$ | $1-e$ |
| 24 | 01000 | $\{0\}$ | $1-a_1-e$ |
| 25 | 01000 | $\{1\}$ | $a_1-e$ |
| 26 | 01000 | $\{0,1\}$ | $1-e$ |
| 27 | 01001 | $\{0\}$ | $1-a_1-e$ |
| 28 | 01001 | $\{1\}$ | $a_1-e$ |
| 29 | 01001 | $\{0,1\}$ | $1-e$ |
| 30 | 01010 | $\{0\}$ | $1-a_1-e$ |
| 31 | 01010 | $\{1\}$ | $a_1-e$ |
| 32 | 01010 | $\{0,1\}$ | $1-e$ |
| 33 | 01011 | $\{0\}$ | $1-a_1-e$ |
| 34 | 01011 | $\{1\}$ | $a_1-e$ |
| 35 | 01011 | $\{0,1\}$ | $1-e$ |
| 36 | 01100 | $\{0\}$ | $1-a_1-e$ |
| 37 | 01100 | $\{1\}$ | $a_1-e$ |
| 38 | 01100 | $\{0,1\}$ | $1-e$ |
| 39 | 01101 | $\{0\}$ | $1-a_1-e$ |
| 40 | 01101 | $\{1\}$ | $a_1-e$ |
| 41 | 01101 | $\{0,1\}$ | $1-e$ |
| 42 | 01110 | $\{0\}$ | $1-a_1-e$ |
| 43 | 01110 | $\{1\}$ | $a_1-e$ |
| 44 | 01110 | $\{0,1\}$ | $1-e$ |
| 45 | 01111 | $\{0\}$ | $1-a_1-e$ |
| 46 | 01111 | $\{1\}$ | $a_1-e$ |
| 47 | 01111 | $\{0,1\}$ | $1-e$ |
| 48 | 10000 | $\{0\}$ | $1-a_2-e$ |
| 49 | 10000 | $\{2\}$ | $a_2-e$ |
| 50 | 10000 | $\{0,2\}$ | $1-e$ |
| 51 | 10001 | $\{0\}$ | $1-a_2-e$ |
| 52 | 10001 | $\{2\}$ | $a_2-e$ |
| 53 | 10001 | $\{0,2\}$ | $1-e$ |
| 54 | 10010 | $\{0\}$ | $1-a_2-e$ |
| 55 | 10010 | $\{2\}$ | $a_2-e$ |
| 56 | 10010 | $\{0,2\}$ | $1-e$ |
| 57 | 10011 | $\{0\}$ | $1-a_2-e$ |
| 58 | 10011 | $\{2\}$ | $a_2-e$ |
| 59 | 10011 | $\{0,2\}$ | $1-e$ |
| 60 | 10100 | $\{0\}$ | $1-a_2-e$ |
| 61 | 10100 | $\{2\}$ | $a_2-e$ |
| 62 | 10100 | $\{0,2\}$ | $1-e$ |
| 63 | 10101 | $\{0\}$ | $1-a_2-e$ |
| 64 | 10101 | $\{2\}$ | $a_2-e$ |
| 65 | 10101 | $\{0,2\}$ | $1-e$ |
| 66 | 10110 | $\{0\}$ | $1-a_2-e$ |
| 67 | 10110 | $\{2\}$ | $a_2-e$ |
| 68 | 10110 | $\{0,2\}$ | $1-e$ |
| 69 | 10111 | $\{0\}$ | $1-a_2-e$ |
| 70 | 10111 | $\{2\}$ | $a_2-e$ |
| 71 | 10111 | $\{0,2\}$ | $1-e$ |
| 72 | 11000 | $\{0\}$ | $1-a_3-e$ |
| 73 | 11000 | $\{3\}$ | $a_3-e$ |
| 74 | 11000 | $\{0,3\}$ | $1-e$ |
| 75 | 11001 | $\{0\}$ | $1-a_3-e$ |
| 76 | 11001 | $\{3\}$ | $a_3-e$ |
| 77 | 11001 | $\{0,3\}$ | $1-e$ |
| 78 | 11010 | $\{0\}$ | $1-a_3-e$ |
| 79 | 11010 | $\{3\}$ | $a_3-e$ |
| 80 | 11010 | $\{0,3\}$ | $1-e$ |
| 81 | 11011 | $\{0\}$ | $1-a_3-e$ |
| 82 | 11011 | $\{3\}$ | $a_3-e$ |
| 83 | 11011 | $\{0,3\}$ | $1-e$ |
| 84 | 11100 | $\{0\}$ | $1-a_4-e$ |
| 85 | 11100 | $\{4\}$ | $a_4-e$ |
| 86 | 11100 | $\{0,4\}$ | $1-e$ |
| 87 | 11101 | $\{0\}$ | $1-a_4-e$ |
| 88 | 11101 | $\{4\}$ | $a_4-e$ |
| 89 | 11101 | $\{0,4\}$ | $1-e$ |
| 90 | 11110 | $\{0\}$ | $1-a_5-e$ |
| 91 | 11110 | $\{5\}$ | $a_5-e$ |
| 92 | 11110 | $\{0,5\}$ | $1-e$ |
| 93 | 11111 | $\{0\}$ | $1-e$ |

**Proposition 141.2 (Exact event-TV equivalence).** For every probability
vector $p_b$ the 94 rows are equivalent to the closed cap
$\operatorname{TV}(p_b,\eta_b)\le e$ on every word.

**Proof.** For a target on $\{0,n\}$,

$$
\begin{aligned}
\operatorname{TV}(p,(1-a)e_0+ae_n)
 &=1-\min\{p(0),1-a\}-\min\{p(n),a\}\\
 &=\max\{0,1-a-p(0),a-p(n),1-p(0)-p(n)\}.
\end{aligned}
\tag{141.1}
$$

The maximum of the last three expressions is already nonnegative for a
probability vector, but the explicit zero makes the nonnegative form
unambiguous. Thus each of the three listed rows is necessary, and
jointly they are sufficient when $e\ge0$.
At $11111$ the distance to $e_0$ is $1-p_{11111}(0)$.
This reuses the TV identity in Acquisition Resources (84.2) and
Continuation (110.6). The pair row is not replaced by adding singleton
deficits. $\square$

## 142. Thirteen full preselected weighted-event scores

**Definition 142.1 (Full score coefficients).** For each of the 13 names
$C3,C2,K1,K2,K3,K4,K5,R1,R2,R3,R4,R5,R6$ let $y^{(q)}_j$ be the
nonnegative integer weights listed below; unlisted row weights are zero.
Define the entire score, including its full terminal-coordinate expansion,
by

$$
\begin{aligned}
S_q(p)&=\sum_{j=0}^{93}y^{(q)}_j p_{b_j}(E_j),\\
h^{(q)}_{S,c}(r)&=\sum_{j=0}^{93}y^{(q)}_j
 \mathbf1_{c_N(b_j,S)=c}\mathbf1_{r\in E_j},\\
M^{(q)}_{S,c}&=\max_{0\le r\le5}h^{(q)}_{S,c}(r),\qquad
B^{(q)}_S=\sum_cM^{(q)}_{S,c},\qquad B_q=\max_S B^{(q)}_S,\\
W_q&=\sum_jy^{(q)}_j,\qquad
\sum_jy^{(q)}_j\eta_{b_j}(E_j)=T_{q,0}+\sum_{i=1}^5T_{q,i}a_i.
\end{aligned}
\tag{142.1}
$$

The formulas and sparse weights specify all 306 coefficients of every
full $N$ score, not only a scalar inequality. Each maximum is over all
six labels. Pair cells remain distinct and no saturated support mask is
imposed. Within a maxima tuple use empty, singleton $(0,1)$ and pair
$(00,01,10,11)$ cell order. The schedule order is the declared order in Definition 140.2. The summary table supplies all target polynomials.

<!-- mathematical-data: score-summary -->

| Score $q$ | Cut | Weight $W_q$ | Upper $B_q$ | Constant $T_{q,0}$ | $(T_{q,1},\ldots,T_{q,5})$ |
| --- | --- | --- | --- | --- | --- |
| C3 | 9 | 29 | 15 | 13 | (0,2,4,5,5) |
| C2 | 10 | 18 | 9 | 7 | (0,2,3,3,3) |
| K1 | 11 | 45 | 24 | 22 | (0,2,5,8,8) |
| K2 | 12 | 22 | 12 | 11 | (0,1,3,4,3) |
| K3 | 13 | 7 | 4 | 4 | (0,0,1,1,1) |
| K4 | 14 | 19 | 10 | 9 | (0,1,2,3,4) |
| K5 | 15 | 46 | 24 | 21 | (0,3,7,7,8) |
| R1 | 16 | 4 | 3 | 3 | (0,0,1,0,0) |
| R2 | 17 | 9 | 6 | 6 | (0,0,2,0,1) |
| R3 | 18 | 10 | 6 | 5 | (0,1,2,2,0) |
| R4 | 19 | 45 | 24 | 21 | (0,3,8,6,7) |
| R5 | 20 | 11 | 6 | 5 | (0,1,2,2,1) |
| R6 | 21 | 52 | 27 | 23 | (0,4,9,7,9) |

### Primitive score C3

<!-- mathematical-data: weights-C3 -->

| Row $j$ | Integer weight $y^{(C3)}_j$ |
| --- | --- |
| 14 | 1 |
| 20 | 1 |
| 26 | 1 |
| 32 | 1 |
| 38 | 1 |
| 50 | 1 |
| 56 | 1 |
| 61 | 1 |
| 62 | 1 |
| 67 | 1 |
| 73 | 2 |
| 74 | 1 |
| 79 | 2 |
| 85 | 5 |
| 91 | 5 |
| 93 | 4 |

<!-- mathematical-data: maxima-C3 -->

| Schedule index | Schedule | Cell maxima $M^{(C3)}_{S,c}$ | Total $B^{(C3)}_S$ |
| --- | --- | --- | --- |
| 0 | () | (13) | 13 |
| 1 | (1) | (5,8) | 13 |
| 2 | (2) | (5,8) | 13 |
| 3 | (3) | (5,8) | 13 |
| 4 | (4) | (6,7) | 13 |
| 5 | (5) | (9,4) | 13 |
| 6 | (1,2) | (2,3,5,5) | 15 |
| 7 | (1,3) | (2,3,5,5) | 15 |
| 8 | (1,4) | (3,2,5,5) | 15 |
| 9 | (1,5) | (5,0,5,4) | 14 |
| 10 | (2,3) | (2,3,5,5) | 15 |
| 11 | (2,4) | (3,2,5,5) | 15 |
| 12 | (2,5) | (5,0,5,4) | 14 |
| 13 | (3,4) | (3,2,5,5) | 15 |
| 14 | (3,5) | (5,0,5,4) | 14 |
| 15 | (4,5) | (6,0,5,4) | 15 |

### Primitive score C2

<!-- mathematical-data: weights-C2 -->

| Row $j$ | Integer weight $y^{(C2)}_j$ |
| --- | --- |
| 8 | 1 |
| 14 | 1 |
| 26 | 1 |
| 50 | 1 |
| 55 | 1 |
| 61 | 1 |
| 73 | 2 |
| 79 | 1 |
| 85 | 3 |
| 91 | 3 |
| 93 | 3 |

<!-- mathematical-data: maxima-C2 -->

| Schedule index | Schedule | Cell maxima $M^{(C2)}_{S,c}$ | Total $B^{(C2)}_S$ |
| --- | --- | --- | --- |
| 0 | () | (7) | 7 |
| 1 | (1) | (3,4) | 7 |
| 2 | (2) | (3,4) | 7 |
| 3 | (3) | (3,4) | 7 |
| 4 | (4) | (3,4) | 7 |
| 5 | (5) | (4,3) | 7 |
| 6 | (1,2) | (2,1,3,3) | 9 |
| 7 | (1,3) | (2,1,3,3) | 9 |
| 8 | (1,4) | (2,1,3,3) | 9 |
| 9 | (1,5) | (3,0,3,3) | 9 |
| 10 | (2,3) | (2,1,3,3) | 9 |
| 11 | (2,4) | (2,1,3,3) | 9 |
| 12 | (2,5) | (3,0,3,3) | 9 |
| 13 | (3,4) | (2,1,3,3) | 9 |
| 14 | (3,5) | (3,0,3,3) | 9 |
| 15 | (4,5) | (3,0,3,3) | 9 |

### Primitive score K1

<!-- mathematical-data: weights-K1 -->

| Row $j$ | Integer weight $y^{(K1)}_j$ |
| --- | --- |
| 20 | 2 |
| 26 | 1 |
| 32 | 2 |
| 38 | 3 |
| 50 | 1 |
| 56 | 2 |
| 62 | 3 |
| 67 | 2 |
| 73 | 2 |
| 74 | 2 |
| 79 | 3 |
| 85 | 8 |
| 91 | 8 |
| 93 | 6 |

<!-- mathematical-data: maxima-K1 -->

| Schedule index | Schedule | Cell maxima $M^{(K1)}_{S,c}$ | Total $B^{(K1)}_S$ |
| --- | --- | --- | --- |
| 0 | () | (22) | 22 |
| 1 | (1) | (8,14) | 22 |
| 2 | (2) | (8,14) | 22 |
| 3 | (3) | (8,14) | 22 |
| 4 | (4) | (10,12) | 22 |
| 5 | (5) | (16,6) | 22 |
| 6 | (1,2) | (2,6,8,8) | 24 |
| 7 | (1,3) | (3,5,7,9) | 24 |
| 8 | (1,4) | (4,4,8,8) | 24 |
| 9 | (1,5) | (8,0,8,6) | 22 |
| 10 | (2,3) | (3,5,7,9) | 24 |
| 11 | (2,4) | (4,4,8,8) | 24 |
| 12 | (2,5) | (8,0,8,6) | 22 |
| 13 | (3,4) | (4,4,8,8) | 24 |
| 14 | (3,5) | (8,0,8,6) | 22 |
| 15 | (4,5) | (10,0,8,6) | 24 |

### Primitive score K2

<!-- mathematical-data: weights-K2 -->

| Row $j$ | Integer weight $y^{(K2)}_j$ |
| --- | --- |
| 14 | 1 |
| 26 | 1 |
| 32 | 1 |
| 38 | 1 |
| 50 | 1 |
| 56 | 1 |
| 61 | 1 |
| 62 | 1 |
| 73 | 1 |
| 74 | 1 |
| 79 | 2 |
| 85 | 4 |
| 91 | 3 |
| 93 | 3 |

<!-- mathematical-data: maxima-K2 -->

| Schedule index | Schedule | Cell maxima $M^{(K2)}_{S,c}$ | Total $B^{(K2)}_S$ |
| --- | --- | --- | --- |
| 0 | () | (11) | 11 |
| 1 | (1) | (4,7) | 11 |
| 2 | (2) | (4,7) | 11 |
| 3 | (3) | (5,6) | 11 |
| 4 | (4) | (6,5) | 11 |
| 5 | (5) | (8,3) | 11 |
| 6 | (1,2) | (1,3,4,4) | 12 |
| 7 | (1,3) | (2,2,4,4) | 12 |
| 8 | (1,4) | (3,1,4,4) | 12 |
| 9 | (1,5) | (4,0,4,3) | 11 |
| 10 | (2,3) | (2,2,4,4) | 12 |
| 11 | (2,4) | (3,1,4,4) | 12 |
| 12 | (2,5) | (4,0,4,3) | 11 |
| 13 | (3,4) | (3,2,4,3) | 12 |
| 14 | (3,5) | (5,0,4,3) | 12 |
| 15 | (4,5) | (6,0,3,3) | 12 |

### Primitive score K3

<!-- mathematical-data: weights-K3 -->

| Row $j$ | Integer weight $y^{(K3)}_j$ |
| --- | --- |
| 32 | 1 |
| 38 | 1 |
| 50 | 1 |
| 79 | 1 |
| 85 | 1 |
| 91 | 1 |
| 93 | 1 |

<!-- mathematical-data: maxima-K3 -->

| Schedule index | Schedule | Cell maxima $M^{(K3)}_{S,c}$ | Total $B^{(K3)}_S$ |
| --- | --- | --- | --- |
| 0 | () | (4) | 4 |
| 1 | (1) | (2,2) | 4 |
| 2 | (2) | (1,3) | 4 |
| 3 | (3) | (2,2) | 4 |
| 4 | (4) | (2,2) | 4 |
| 5 | (5) | (3,1) | 4 |
| 6 | (1,2) | (0,2,1,1) | 4 |
| 7 | (1,3) | (1,1,1,1) | 4 |
| 8 | (1,4) | (1,1,1,1) | 4 |
| 9 | (1,5) | (2,0,1,1) | 4 |
| 10 | (2,3) | (1,0,1,2) | 4 |
| 11 | (2,4) | (1,0,1,2) | 4 |
| 12 | (2,5) | (1,0,2,1) | 4 |
| 13 | (3,4) | (1,1,1,1) | 4 |
| 14 | (3,5) | (2,0,1,1) | 4 |
| 15 | (4,5) | (2,0,1,1) | 4 |

### Primitive score K4

<!-- mathematical-data: weights-K4 -->

| Row $j$ | Integer weight $y^{(K4)}_j$ |
| --- | --- |
| 20 | 1 |
| 32 | 1 |
| 38 | 1 |
| 56 | 1 |
| 62 | 1 |
| 67 | 1 |
| 74 | 1 |
| 79 | 2 |
| 85 | 3 |
| 91 | 4 |
| 93 | 3 |

<!-- mathematical-data: maxima-K4 -->

| Schedule index | Schedule | Cell maxima $M^{(K4)}_{S,c}$ | Total $B^{(K4)}_S$ |
| --- | --- | --- | --- |
| 0 | () | (9) | 9 |
| 1 | (1) | (3,6) | 9 |
| 2 | (2) | (3,6) | 9 |
| 3 | (3) | (3,6) | 9 |
| 4 | (4) | (3,6) | 9 |
| 5 | (5) | (6,3) | 9 |
| 6 | (1,2) | (1,2,3,4) | 10 |
| 7 | (1,3) | (1,2,3,4) | 10 |
| 8 | (1,4) | (1,2,3,4) | 10 |
| 9 | (1,5) | (3,0,4,3) | 10 |
| 10 | (2,3) | (1,2,3,4) | 10 |
| 11 | (2,4) | (1,2,3,4) | 10 |
| 12 | (2,5) | (3,0,4,3) | 10 |
| 13 | (3,4) | (1,2,3,4) | 10 |
| 14 | (3,5) | (3,0,4,3) | 10 |
| 15 | (4,5) | (3,0,4,3) | 10 |

### Primitive score K5

<!-- mathematical-data: weights-K5 -->

| Row $j$ | Integer weight $y^{(K5)}_j$ |
| --- | --- |
| 14 | 2 |
| 20 | 1 |
| 26 | 2 |
| 32 | 2 |
| 38 | 1 |
| 50 | 2 |
| 56 | 2 |
| 61 | 2 |
| 62 | 1 |
| 67 | 1 |
| 73 | 3 |
| 74 | 1 |
| 79 | 4 |
| 85 | 7 |
| 91 | 8 |
| 93 | 7 |

<!-- mathematical-data: maxima-K5 -->

| Schedule index | Schedule | Cell maxima $M^{(K5)}_{S,c}$ | Total $B^{(K5)}_S$ |
| --- | --- | --- | --- |
| 0 | () | (21) | 21 |
| 1 | (1) | (8,13) | 21 |
| 2 | (2) | (8,13) | 21 |
| 3 | (3) | (9,12) | 21 |
| 4 | (4) | (9,12) | 21 |
| 5 | (5) | (14,7) | 21 |
| 6 | (1,2) | (3,5,8,8) | 24 |
| 7 | (1,3) | (4,4,8,8) | 24 |
| 8 | (1,4) | (5,3,7,9) | 24 |
| 9 | (1,5) | (8,0,8,7) | 23 |
| 10 | (2,3) | (4,4,8,8) | 24 |
| 11 | (2,4) | (5,3,7,9) | 24 |
| 12 | (2,5) | (8,0,8,7) | 23 |
| 13 | (3,4) | (5,4,7,8) | 24 |
| 14 | (3,5) | (9,0,8,7) | 24 |
| 15 | (4,5) | (9,0,8,7) | 24 |

### Primitive score R1

<!-- mathematical-data: weights-R1 -->

| Row $j$ | Integer weight $y^{(R1)}_j$ |
| --- | --- |
| 26 | 1 |
| 50 | 1 |
| 73 | 1 |
| 93 | 1 |

<!-- mathematical-data: maxima-R1 -->

| Schedule index | Schedule | Cell maxima $M^{(R1)}_{S,c}$ | Total $B^{(R1)}_S$ |
| --- | --- | --- | --- |
| 0 | () | (3) | 3 |
| 1 | (1) | (1,2) | 3 |
| 2 | (2) | (1,2) | 3 |
| 3 | (3) | (2,1) | 3 |
| 4 | (4) | (2,1) | 3 |
| 5 | (5) | (2,1) | 3 |
| 6 | (1,2) | (0,1,1,1) | 3 |
| 7 | (1,3) | (1,0,1,1) | 3 |
| 8 | (1,4) | (1,0,1,1) | 3 |
| 9 | (1,5) | (1,0,1,1) | 3 |
| 10 | (2,3) | (1,0,1,1) | 3 |
| 11 | (2,4) | (1,0,1,1) | 3 |
| 12 | (2,5) | (1,0,1,1) | 3 |
| 13 | (3,4) | (2,0,0,1) | 3 |
| 14 | (3,5) | (2,0,0,1) | 3 |
| 15 | (4,5) | (2,0,0,1) | 3 |

### Primitive score R2

<!-- mathematical-data: weights-R2 -->

| Row $j$ | Integer weight $y^{(R2)}_j$ |
| --- | --- |
| 26 | 2 |
| 50 | 1 |
| 56 | 1 |
| 73 | 2 |
| 86 | 1 |
| 91 | 1 |
| 93 | 1 |

<!-- mathematical-data: maxima-R2 -->

| Schedule index | Schedule | Cell maxima $M^{(R2)}_{S,c}$ | Total $B^{(R2)}_S$ |
| --- | --- | --- | --- |
| 0 | () | (6) | 6 |
| 1 | (1) | (2,4) | 6 |
| 2 | (2) | (2,4) | 6 |
| 3 | (3) | (4,2) | 6 |
| 4 | (4) | (4,2) | 6 |
| 5 | (5) | (5,1) | 6 |
| 6 | (1,2) | (0,2,2,2) | 6 |
| 7 | (1,3) | (2,0,2,2) | 6 |
| 8 | (1,4) | (2,0,2,2) | 6 |
| 9 | (1,5) | (2,0,3,1) | 6 |
| 10 | (2,3) | (2,0,2,2) | 6 |
| 11 | (2,4) | (1,1,3,1) | 6 |
| 12 | (2,5) | (2,0,3,1) | 6 |
| 13 | (3,4) | (3,1,1,1) | 6 |
| 14 | (3,5) | (4,0,1,1) | 6 |
| 15 | (4,5) | (4,0,1,1) | 6 |

### Primitive score R3

<!-- mathematical-data: weights-R3 -->

| Row $j$ | Integer weight $y^{(R3)}_j$ |
| --- | --- |
| 14 | 1 |
| 26 | 1 |
| 50 | 1 |
| 61 | 1 |
| 73 | 2 |
| 85 | 2 |
| 92 | 1 |
| 93 | 1 |

<!-- mathematical-data: maxima-R3 -->

| Schedule index | Schedule | Cell maxima $M^{(R3)}_{S,c}$ | Total $B^{(R3)}_S$ |
| --- | --- | --- | --- |
| 0 | () | (5) | 5 |
| 1 | (1) | (2,3) | 5 |
| 2 | (2) | (2,3) | 5 |
| 3 | (3) | (2,3) | 5 |
| 4 | (4) | (3,2) | 5 |
| 5 | (5) | (4,1) | 5 |
| 6 | (1,2) | (1,1,2,2) | 6 |
| 7 | (1,3) | (1,1,2,2) | 6 |
| 8 | (1,4) | (2,0,2,2) | 6 |
| 9 | (1,5) | (2,0,2,1) | 5 |
| 10 | (2,3) | (1,1,2,2) | 6 |
| 11 | (2,4) | (2,0,2,2) | 6 |
| 12 | (2,5) | (2,0,2,1) | 5 |
| 13 | (3,4) | (2,0,2,2) | 6 |
| 14 | (3,5) | (2,0,2,1) | 5 |
| 15 | (4,5) | (3,0,1,1) | 5 |

### Primitive score R4

<!-- mathematical-data: weights-R4 -->

| Row $j$ | Integer weight $y^{(R4)}_j$ |
| --- | --- |
| 14 | 3 |
| 26 | 3 |
| 32 | 2 |
| 50 | 3 |
| 56 | 2 |
| 61 | 3 |
| 73 | 6 |
| 79 | 2 |
| 85 | 6 |
| 86 | 1 |
| 91 | 7 |
| 93 | 7 |

<!-- mathematical-data: maxima-R4 -->

| Schedule index | Schedule | Cell maxima $M^{(R4)}_{S,c}$ | Total $B^{(R4)}_S$ |
| --- | --- | --- | --- |
| 0 | () | (21) | 21 |
| 1 | (1) | (8,13) | 21 |
| 2 | (2) | (8,13) | 21 |
| 3 | (3) | (10,11) | 21 |
| 4 | (4) | (10,11) | 21 |
| 5 | (5) | (14,7) | 21 |
| 6 | (1,2) | (3,5,8,8) | 24 |
| 7 | (1,3) | (5,3,8,8) | 24 |
| 8 | (1,4) | (6,2,7,9) | 24 |
| 9 | (1,5) | (8,0,8,7) | 23 |
| 10 | (2,3) | (5,3,8,8) | 24 |
| 11 | (2,4) | (6,2,7,9) | 24 |
| 12 | (2,5) | (8,0,8,7) | 23 |
| 13 | (3,4) | (6,4,7,7) | 24 |
| 14 | (3,5) | (10,0,7,7) | 24 |
| 15 | (4,5) | (10,0,7,7) | 24 |

### Primitive score R5

<!-- mathematical-data: weights-R5 -->

| Row $j$ | Integer weight $y^{(R5)}_j$ |
| --- | --- |
| 14 | 1 |
| 26 | 1 |
| 50 | 1 |
| 61 | 1 |
| 73 | 2 |
| 85 | 2 |
| 91 | 1 |
| 92 | 1 |
| 93 | 1 |

<!-- mathematical-data: maxima-R5 -->

| Schedule index | Schedule | Cell maxima $M^{(R5)}_{S,c}$ | Total $B^{(R5)}_S$ |
| --- | --- | --- | --- |
| 0 | () | (5) | 5 |
| 1 | (1) | (2,3) | 5 |
| 2 | (2) | (2,3) | 5 |
| 3 | (3) | (2,3) | 5 |
| 4 | (4) | (3,2) | 5 |
| 5 | (5) | (4,1) | 5 |
| 6 | (1,2) | (1,1,2,2) | 6 |
| 7 | (1,3) | (1,1,2,2) | 6 |
| 8 | (1,4) | (2,0,2,2) | 6 |
| 9 | (1,5) | (2,0,2,1) | 5 |
| 10 | (2,3) | (1,1,2,2) | 6 |
| 11 | (2,4) | (2,0,2,2) | 6 |
| 12 | (2,5) | (2,0,2,1) | 5 |
| 13 | (3,4) | (2,0,2,2) | 6 |
| 14 | (3,5) | (2,0,2,1) | 5 |
| 15 | (4,5) | (3,0,2,1) | 6 |

### Primitive score R6

<!-- mathematical-data: weights-R6 -->

| Row $j$ | Integer weight $y^{(R6)}_j$ |
| --- | --- |
| 14 | 3 |
| 20 | 1 |
| 26 | 3 |
| 32 | 2 |
| 50 | 3 |
| 56 | 2 |
| 61 | 3 |
| 67 | 1 |
| 73 | 6 |
| 79 | 3 |
| 85 | 7 |
| 86 | 1 |
| 91 | 9 |
| 93 | 8 |

<!-- mathematical-data: maxima-R6 -->

| Schedule index | Schedule | Cell maxima $M^{(R6)}_{S,c}$ | Total $B^{(R6)}_S$ |
| --- | --- | --- | --- |
| 0 | () | (23) | 23 |
| 1 | (1) | (9,14) | 23 |
| 2 | (2) | (9,14) | 23 |
| 3 | (3) | (10,13) | 23 |
| 4 | (4) | (10,13) | 23 |
| 5 | (5) | (15,8) | 23 |
| 6 | (1,2) | (4,5,9,9) | 27 |
| 7 | (1,3) | (5,4,9,9) | 27 |
| 8 | (1,4) | (6,3,8,10) | 27 |
| 9 | (1,5) | (9,0,9,8) | 26 |
| 10 | (2,3) | (5,4,9,9) | 27 |
| 11 | (2,4) | (6,3,8,10) | 27 |
| 12 | (2,5) | (9,0,9,8) | 26 |
| 13 | (3,4) | (6,4,8,9) | 27 |
| 14 | (3,5) | (10,0,9,8) | 27 |
| 15 | (4,5) | (10,0,9,8) | 27 |

**Theorem 142.2 (All thirteen unrestricted necessary cuts).** Any complete
$N$ allocation satisfying the five-bit cap rows satisfies

$$
\sum_{i=1}^5T_{q,i}a_i-W_q e\le B_q-T_{q,0}
\quad\text{for every one of the 13 scores }q.
\tag{142.2}
$$

This requires neither the residual strip nor $\kappa_3=0$.

**Proof.** For every complete allocation, substituting its law gives

$$
\begin{aligned}
S_q(p)&=\sum_{S,c,r}h^{(q)}_{S,c}(r)T_{S,c,r}\\
 &\le\sum_{S,c}M^{(q)}_{S,c}w_S
 =\sum_S B^{(q)}_S w_S\le B_q.
\end{aligned}
\tag{142.3}
$$

Equal masses of all cells in each schedule and global normalization
are used in the last two steps. From the nonnegative weighted cap rows,
$S_q(p)\ge T_{q,0}+\sum_iT_{q,i}a_i-W_qe$.
This proves (142.2). The sparse integers in the tables reconstruct all
3978 full $h$ coefficients, 663 cell maxima, 208 schedule totals and 13
target polynomials; their displayed maxima are exact integer maxima.
The argument applies to any complete $N$ witness, hence to every $O$
witness through completion. $\square$

**Proposition 142.3 (Loss compatible with every positive slack).** Put
$\kappa_3=2+29e-2a_2-4a_3-5a_4-5a_5$.
Every cap-feasible $N$ allocation obeys

$$
\begin{aligned}
15-S_{C3}(p)
 &=\sum_S(15-B^{(C3)}_S)w_S
 +\sum_{S,c,r}(M^{(C3)}_{S,c}-h^{(C3)}_{S,c}(r))T_{S,c,r},\\
0\le15-S_{C3}(p)&\le\kappa_3,\\
2w_{\mathrm{deg}}+w_{(1,5)}+w_{(2,5)}+w_{(3,5)}&\le\kappa_3,
\end{aligned}
\tag{142.4}
$$

where $w_{\mathrm{deg}}$ is the sum of empty and singleton schedule masses.

**Proof.** Subtract the full terminal expansion in (142.3) from
$15\sum_Sw_S$ and insert the cell maxima. Every summand is nonnegative.
The cap-score lower bound for $C3$ is $15-\kappa_3$.
Its schedule totals are 13 for degenerate schedules, 14 for the three
listed pairs and 15 for the remaining pairs. Discarding the nonnegative
cell losses proves the final inequality. $\square$

At $\kappa_3>0$ this permits positive deficient schedule or label masses;
it does not force their removal. At $\kappa_3=0$ every positive mass must
have zero relevant loss. The full model and lifts use the loss identity
without importing a saturated mask into positive-$\kappa_3$ cases.
The $C3,C2,K$ suppliers, $R1$, $R3$ and $R6$ scalars are attributed in
Section 153; completeness of the projected feasible region and one
simultaneous stopped lift is the result established here.

## 143. The closed residual domain and 22 ordered halfspaces

**Definition 143.1 (Whole closed parameter polytope).** Write
$x=(a_1,a_2,a_3,a_4,a_5,e)$, $S=a_3+a_4+a_5$ and

$$
Q=\{x\in D_5:6e\le S,\ a_1+S-6e\le1\}.
\tag{143.1}
$$

For the following ordered rows $k=0,\ldots,21$, let $A_k$ be the listed
normal and $b_k$ the right-hand side, with slack
$s_k(x)=b_k-A_k\cdot x$. Define
$P=\{x:A_k\cdot x\le b_k\ (0\le k\le21)\}$.
Rows 0--6 are $D_5$, rows 7--8 complete $Q$, and rows 9--21 are all 13
cuts of Theorem 142.2, including $C3$. All inequalities are closed.

<!-- mathematical-data: halfspaces22 -->

| Index $k$ | Name | Normal $A_k$ | Right side $b_k$ |
| --- | --- | --- | --- |
| 0 | a1<=1 | (1,0,0,0,0,0) | 1 |
| 1 | order0 | (-1,1,0,0,0,0) | 0 |
| 2 | order1 | (0,-1,1,0,0,0) | 0 |
| 3 | order2 | (0,0,-1,1,0,0) | 0 |
| 4 | order3 | (0,0,0,-1,1,0) | 0 |
| 5 | order4 | (0,0,0,0,-1,1) | 0 |
| 6 | e>=0 | (0,0,0,0,0,-1) | 0 |
| 7 | head | (1,0,1,1,1,-6) | 1 |
| 8 | strip | (0,0,-1,-1,-1,6) | 0 |
| 9 | C3 | (0,2,4,5,5,-29) | 2 |
| 10 | C2 | (0,2,3,3,3,-18) | 2 |
| 11 | K1 | (0,2,5,8,8,-45) | 2 |
| 12 | K2 | (0,1,3,4,3,-22) | 1 |
| 13 | K3 | (0,0,1,1,1,-7) | 0 |
| 14 | K4 | (0,1,2,3,4,-19) | 1 |
| 15 | K5 | (0,3,7,7,8,-46) | 3 |
| 16 | R1 | (0,0,1,0,0,-4) | 0 |
| 17 | R2 | (0,0,2,0,1,-9) | 0 |
| 18 | R3 | (0,1,2,2,0,-10) | 1 |
| 19 | R4 | (0,3,8,6,7,-45) | 3 |
| 20 | R5 | (0,1,2,2,1,-11) | 1 |
| 21 | R6 | (0,4,9,7,9,-52) | 4 |

**Definition 143.2 (Initial simplex and exact ordering).** The rows 0--6
form the ordered six-simplex with these seven vertices. The index $k$
means $k$ initial ones followed by $6-k$ zeros.

<!-- mathematical-data: simplex7 -->

| Index | Initial vertex |
| --- | --- |
| 0 | (0,0,0,0,0,0) |
| 1 | (1,0,0,0,0,0) |
| 2 | (1,1,0,0,0,0) |
| 3 | (1,1,1,0,0,0) |
| 4 | (1,1,1,1,0,0) |
| 5 | (1,1,1,1,1,0) |
| 6 | (1,1,1,1,1,1) |

Use increasing exact lexicographic order of the six rational coordinates
after every cut, including when a new intersection coincides with another
vertex. No numeric tolerance defines a tie.
A strict interior point and its ordered slacks are supplied below.
All its 22 slacks are positive, with minimum $1/36$. Thus $P$ is
six-dimensional; every prefix of the 22 halfspaces is also full-dimensional.
All prefixes are bounded because they lie in $D_5$.

<!-- mathematical-data: strict-center -->

| Coordinate | Value |
| --- | --- |
| 0 | 6590836349/9012079440 |
| 1 | 2878571719/4506039720 |
| 2 | 2753403949/4506039720 |
| 3 | 923069047/1802415888 |
| 4 | 1240164407/3004026480 |
| 5 | 2042516029/9012079440 |

<!-- mathematical-data: strict-center-slacks -->

| Halfspace | Slack |
| --- | --- |
| 0 | 2421243091/9012079440 |
| 1 | 277897637/3004026480 |
| 2 | 1/36 |
| 3 | 1088477/11003760 |
| 4 | 71099/716040 |
| 5 | 209747149/1126509930 |
| 6 | 2042516029/9012079440 |
| 7 | 277897637/3004026480 |
| 8 | 79377509/450603972 |
| 9 | 10031591/44394480 |
| 10 | 7531127/38845170 |
| 11 | 1400782057/3004026480 |
| 12 | 227444927/1001342160 |
| 13 | 76247/1510320 |
| 14 | 41448503/160929990 |
| 15 | 35649743/103587120 |
| 16 | 190232587/643719960 |
| 17 | 912133811/2253019860 |
| 18 | 572631671/1502013240 |
| 19 | 388804217/901207944 |
| 20 | 878906417/4506039720 |
| 21 | 557105/1294839 |

## 144. Complete clipping geometry and all 36 vertices

**Lemma 144.1 (Exact edge criterion and one-cut enumeration).** In each
prefix polytope, distinct vertices $v,w$ form an edge exactly when the
normals of their common active halfspaces have rank five. Cutting a prefix
by one further halfspace produces precisely its retained vertices and the
cut intersections of its positive-negative crossing edges.

**Proof.** At an interior point of the open segment $(v,w)$, a previously
imposed inequality is tight exactly when it is tight at both endpoints.
The common tight inequalities therefore define the minimal face containing
the segment. In a full-dimensional six-dimensional polytope its dimension
is six minus their normal rank. Dimension one is exactly an edge; two
distinct vertices cannot share rank six.

Let a vertex $z$ after cutting not be an old vertex. If $z$ were strictly
inside the new halfspace it would still be nonextreme in its old minimal
face. Thus it is on the cutting plane. In the relative interior of its
old minimal face $F$ of dimension $d\ge1$, a single new equality can leave
an isolated point only when $d=1$: if $d>1$ its nullspace has a nonzero
tangent direction in $F$, contradicting extremality. A plane containing
$F$ also cannot isolate $z$. Thus $z$ lies on an old edge with endpoint
slacks $s_v>0>s_w$. The intersection is

$$
z=\frac{s_v w-s_w v}{s_v-s_w}.
\tag{144.1}
$$

If an endpoint is tight it is already retained; intersections at tight
endpoints add nothing. Conversely an interior crossing of an edge has
five independent common active normals and the independent cut equation,
so is a new vertex. Old vertices on the permitted side remain vertices.
This proves exact one-cut enumeration. $\square$

**Definition 144.2 (Complete fifteen-cut trace).** At cut $k$, indices
refer to the lexicographically ordered vertex list before that cut.
Retain exactly the listed nonnegative-slack indices. Each ordered edge
$(i,j)$ has strictly positive slack at $i$ and strictly negative slack at
$j$. Apply (144.1) to every listed edge, then deduplicate and sort exactly.
The table contains every crossing edge, including all degenerate cuts
whose new intersections are already retained.

<!-- mathematical-data: clip15 -->

| Cut $k$ | Old count | Kept indices | All crossing edges $(i,j)$ | New count |
| --- | --- | --- | --- | --- |
| 7 | 7 | [0,1,2,6] | [[0,3],[0,4],[0,5],[6,3],[6,4],[6,5]] | 10 |
| 8 | 10 | [0,1,2,3,4,5,6,7,8] | [] | 9 |
| 9 | 9 | [0,4,5,6,7,8] | [[0,1],[0,2],[0,3],[4,1],[4,2],[4,3],[6,3],[7,2],[8,1]] | 15 |
| 10 | 15 | [0,1,2,3,4,5,6,10,11,12,13,14] | [[1,9],[2,8],[3,7],[4,9],[5,8],[6,7]] | 18 |
| 11 | 18 | [0,4,8,9,10,11,12,13,14,15,16,17] | [[0,1],[0,2],[0,3],[4,3],[8,2],[9,1],[10,7],[11,6],[12,5],[13,5],[13,6],[13,7]] | 24 |
| 12 | 24 | [0,1,6,10,13,16,18,19,20,21,22,23] | [[0,2],[0,3],[1,2],[1,3],[6,4],[6,5],[10,7],[10,8],[13,11],[13,12],[16,9],[16,15],[18,14],[18,17],[19,11],[19,12],[21,7],[21,14],[22,8],[22,17]] | 32 |
| 13 | 32 | [0,8,11,12,13,22,24,25,26,27,28,29,30,31] | [[8,1],[8,6],[8,7],[11,7],[11,9],[12,9],[13,3],[13,10],[22,16],[22,17],[22,20],[24,20],[24,21],[25,21],[26,18],[26,23],[29,10],[29,23]] | 32 |
| 14 | 32 | [0,1,2,3,4,6,7,8,9,10,11,12,13,14,15,16,17,19,20,21,22,23,24,25,26,27,28,29,30,31] | [[3,5],[11,5],[14,18],[24,18]] | 34 |
| 15 | 34 | [0,1,2,3,4,5,6,7,9,10,11,12,13,14,15,16,17,18,19,21,22,23,24,25,26,27,28,29,30,31,32,33] | [[12,8],[18,8],[26,20],[28,20]] | 36 |
| 16 | 36 | [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,20,21,22,23,24,25,26,27,28,29,31,32,33,34,35] | [[11,19],[26,30]] | 36 |
| 17 | 36 | [0,1,2,3,4,5,6,7,8,9,10,11,12,13,15,16,17,18,19,20,21,22,23,24,25,26,27,28,30,31,32,33,34,35] | [[2,14],[8,14],[10,14],[16,29],[21,29],[24,29]] | 40 |
| 18 | 40 | [0,1,2,3,4,5,6,7,8,9,10,12,13,14,16,18,19,20,21,22,23,24,25,26,27,29,30,31,33,35,36,37,38,39] | [[0,17],[8,11],[9,15],[14,17],[23,28],[25,32],[31,34],[35,34]] | 42 |
| 19 | 42 | [0,1,2,3,4,5,6,7,8,9,10,12,13,15,19,20,21,22,23,24,25,26,28,29,30,31,36,37,38,39,40,41] | [[0,14],[2,14],[4,11],[12,18],[13,11],[19,32],[28,35],[29,27],[30,27],[37,32]] | 42 |
| 20 | 42 | [0,1,2,3,4,5,6,7,8,9,10,11,13,15,17,18,19,20,21,22,23,24,25,26,27,30,31,33,34,35,36,37,38,39,40,41] | [] | 36 |
| 21 | 36 | [0,1,2,3,4,5,6,8,9,10,11,12,13,15,16,17,18,19,20,21,23,24,25,26,28,29,30,31,32,33,34,35] | [[2,7],[9,7],[16,22],[29,22]] | 36 |

The exact common-active sets for all positive-negative pairs at these cuts
are the following 225 distinct sets. They are determined by the initial
simplex, halfspaces and trace. Of these, 71 contain at least five normals:
70 have rank five and the set $\{2,5,13,16,17\}$ has rank four.
The other 154 contain fewer than five normals, so cannot define crossing
edges. In particular, cardinality five is not itself an edge test. For the
exception,

$$
A_{17}=2A_{16}-A_5,
\qquad \operatorname{rank}(A_2,A_5,A_{13},A_{16})=4.
\tag{144.2}
$$

The independent coordinates $a_2,a_4,a_3,a_5$ witness the latter rank.
This accounts for every excluded pair, rather than assuming that a list
of rank-five pairs already proves exhaustion. Across the cuts there are
1348 positive-negative pair tests and 109 crossing edges. The rank table
is an exact finite geometry certificate, with rank defined over $\mathbb Q$.

<!-- mathematical-data: rank225 -->

| Common active halfspace indices | Normal rank |
| --- | --- |
| [0,1,2,3,4] | 5 |
| [0,1,2,3,5] | 5 |
| [0,1,2,4,5] | 5 |
| [1,2] | 2 |
| [1,2,3] | 3 |
| [1,2,3,4] | 4 |
| [1,2,3,4,6] | 5 |
| [1,2,3,4,7] | 5 |
| [1,2,3,4,9] | 5 |
| [1,2,3,4,11] | 5 |
| [1,2,3,5] | 4 |
| [1,2,3,5,6] | 5 |
| [1,2,3,5,7] | 5 |
| [1,2,3,5,9] | 5 |
| [1,2,3,5,10] | 5 |
| [1,2,3,5,12] | 5 |
| [1,2,3,6,11] | 5 |
| [1,2,3,7] | 4 |
| [1,2,3,9] | 4 |
| [1,2,3,9,10] | 5 |
| [1,2,3,9,11] | 5 |
| [1,2,3,9,12] | 5 |
| [1,2,3,10] | 4 |
| [1,2,3,10,12] | 5 |
| [1,2,3,11] | 4 |
| [1,2,3,12] | 4 |
| [1,2,4] | 3 |
| [1,2,4,5] | 4 |
| [1,2,4,5,6] | 5 |
| [1,2,4,5,7] | 5 |
| [1,2,4,5,9] | 5 |
| [1,2,4,5,10] | 5 |
| [1,2,4,6,11] | 5 |
| [1,2,4,7] | 4 |
| [1,2,4,9] | 4 |
| [1,2,4,9,10] | 5 |
| [1,2,4,9,11] | 5 |
| [1,2,4,10] | 4 |
| [1,2,4,10,13] | 5 |
| [1,2,4,10,15] | 5 |
| [1,2,4,11] | 4 |
| [1,2,4,13] | 4 |
| [1,2,4,13,15] | 5 |
| [1,2,4,13,17] | 5 |
| [1,2,4,13,19] | 5 |
| [1,2,4,15] | 4 |
| [1,2,4,17] | 4 |
| [1,2,4,19] | 4 |
| [1,2,5] | 3 |
| [1,2,5,7] | 4 |
| [1,2,5,9] | 4 |
| [1,2,5,10] | 4 |
| [1,2,5,10,12] | 5 |
| [1,2,5,10,13] | 5 |
| [1,2,5,12] | 4 |
| [1,2,5,13] | 4 |
| [1,2,5,13,16,17] | 5 |
| [1,2,9] | 3 |
| [1,2,9,10] | 4 |
| [1,2,9,10,12] | 5 |
| [1,2,9,12] | 4 |
| [1,2,9,13] | 4 |
| [1,2,10] | 3 |
| [1,2,10,12] | 4 |
| [1,2,10,12,13] | 5 |
| [1,2,10,12,18] | 5 |
| [1,2,10,13] | 4 |
| [1,2,10,13,15] | 5 |
| [1,2,10,13,17] | 5 |
| [1,2,10,15] | 4 |
| [1,2,10,17] | 4 |
| [1,2,10,18] | 4 |
| [1,2,10,19] | 4 |
| [1,2,12] | 3 |
| [1,2,12,13] | 4 |
| [1,2,12,13,18] | 5 |
| [1,2,13] | 3 |
| [1,2,13,15] | 4 |
| [1,2,13,17] | 4 |
| [1,2,13,18] | 4 |
| [1,2,13,19] | 4 |
| [1,2,19] | 3 |
| [2] | 1 |
| [2,3] | 2 |
| [2,3,4] | 3 |
| [2,3,4,6] | 4 |
| [2,3,4,6,7] | 5 |
| [2,3,4,7] | 4 |
| [2,3,4,7,9] | 5 |
| [2,3,4,7,11] | 5 |
| [2,3,4,9] | 4 |
| [2,3,4,11] | 4 |
| [2,3,5] | 3 |
| [2,3,5,6] | 4 |
| [2,3,5,6,7] | 5 |
| [2,3,5,7] | 4 |
| [2,3,5,7,9] | 5 |
| [2,3,5,7,10] | 5 |
| [2,3,5,7,12] | 5 |
| [2,3,5,9] | 4 |
| [2,3,5,12] | 4 |
| [2,3,6,7,11] | 5 |
| [2,3,6,11] | 4 |
| [2,3,7] | 3 |
| [2,3,7,9] | 4 |
| [2,3,7,9,10] | 5 |
| [2,3,7,9,11] | 5 |
| [2,3,7,9,12] | 5 |
| [2,3,7,10] | 4 |
| [2,3,7,10,12] | 5 |
| [2,3,7,11] | 4 |
| [2,3,7,12] | 4 |
| [2,3,9] | 3 |
| [2,3,9,10] | 4 |
| [2,3,9,11] | 4 |
| [2,3,9,12] | 4 |
| [2,3,10] | 3 |
| [2,3,10,12] | 4 |
| [2,3,11] | 3 |
| [2,3,12] | 3 |
| [2,4] | 2 |
| [2,4,5] | 3 |
| [2,4,5,6] | 4 |
| [2,4,5,6,7] | 5 |
| [2,4,5,7] | 4 |
| [2,4,5,7,9] | 5 |
| [2,4,5,7,10] | 5 |
| [2,4,5,9] | 4 |
| [2,4,6,7,11] | 5 |
| [2,4,6,11] | 4 |
| [2,4,7] | 3 |
| [2,4,7,9] | 4 |
| [2,4,7,9,10] | 5 |
| [2,4,7,9,11] | 5 |
| [2,4,7,10] | 4 |
| [2,4,7,10,13] | 5 |
| [2,4,7,10,15] | 5 |
| [2,4,7,11] | 4 |
| [2,4,7,13] | 4 |
| [2,4,7,13,15] | 5 |
| [2,4,7,13,17] | 5 |
| [2,4,7,13,19] | 5 |
| [2,4,7,15] | 4 |
| [2,4,7,17] | 4 |
| [2,4,7,19] | 4 |
| [2,4,9] | 3 |
| [2,4,9,10] | 4 |
| [2,4,9,11] | 4 |
| [2,4,10] | 3 |
| [2,4,10,13] | 4 |
| [2,4,10,15] | 4 |
| [2,4,11] | 3 |
| [2,4,13] | 3 |
| [2,4,13,15] | 4 |
| [2,4,13,17] | 4 |
| [2,4,13,19] | 4 |
| [2,4,15] | 3 |
| [2,4,17] | 3 |
| [2,4,19] | 3 |
| [2,5,7] | 3 |
| [2,5,7,9] | 4 |
| [2,5,7,10] | 4 |
| [2,5,7,10,12] | 5 |
| [2,5,7,10,13] | 5 |
| [2,5,7,12] | 4 |
| [2,5,7,13] | 4 |
| [2,5,7,13,16,17] | 5 |
| [2,5,9] | 3 |
| [2,5,10] | 3 |
| [2,5,10,12] | 4 |
| [2,5,10,13] | 4 |
| [2,5,12] | 3 |
| [2,5,13] | 3 |
| [2,5,13,16,17] | 4 |
| [2,7] | 2 |
| [2,7,9] | 3 |
| [2,7,9,10] | 4 |
| [2,7,9,10,12] | 5 |
| [2,7,9,12] | 4 |
| [2,7,9,13] | 4 |
| [2,7,10] | 3 |
| [2,7,10,12] | 4 |
| [2,7,10,12,13] | 5 |
| [2,7,10,12,18] | 5 |
| [2,7,10,13] | 4 |
| [2,7,10,13,15] | 5 |
| [2,7,10,13,17] | 5 |
| [2,7,10,15] | 4 |
| [2,7,10,17] | 4 |
| [2,7,10,18] | 4 |
| [2,7,10,19] | 4 |
| [2,7,12] | 3 |
| [2,7,12,13] | 4 |
| [2,7,12,13,18] | 5 |
| [2,7,13] | 3 |
| [2,7,13,15] | 4 |
| [2,7,13,17] | 4 |
| [2,7,13,18] | 4 |
| [2,7,13,19] | 4 |
| [2,7,19] | 3 |
| [2,9] | 2 |
| [2,9,10] | 3 |
| [2,9,10,12] | 4 |
| [2,9,12] | 3 |
| [2,9,13] | 3 |
| [2,10] | 2 |
| [2,10,12] | 3 |
| [2,10,12,13] | 4 |
| [2,10,12,18] | 4 |
| [2,10,13] | 3 |
| [2,10,13,15] | 4 |
| [2,10,13,17] | 4 |
| [2,10,15] | 3 |
| [2,10,17] | 3 |
| [2,10,18] | 3 |
| [2,10,19] | 3 |
| [2,12] | 2 |
| [2,12,13] | 3 |
| [2,12,13,18] | 4 |
| [2,13] | 2 |
| [2,13,15] | 3 |
| [2,13,17] | 3 |
| [2,13,18] | 3 |
| [2,13,19] | 3 |
| [2,19] | 2 |

**Theorem 144.3 (Exact whole polytope).** $P$ is the convex hull of precisely
the following 36 rational vertices in exact lexicographic order. Its 22
listed inequalities define exactly 18 distinct facets.

**Proof.** Begin with the seven vertices in Definition 143.2. Inductively
apply Lemma 144.1 using the complete trace, retaining all permitted old
vertices and all edge-plane intersections. The ranks for every possible
positive-negative pair are specified above; none of the rank-below-five
pairs is an edge. The table's kept indices and new intersections are
obtained by rational slack and (144.1), so exact deduplication yields the
listed counts at each of the fifteen steps. The final list is below,
and every vertex has rank-six active normals. Thus it is an exhaustive
vertex enumeration, not a parameter scan. Boundedness gives the
convex-hull statement: a nonvertex in its minimal face lies on a chord
whose endpoints are in faces of smaller dimension; induction decomposes
it into vertices.

A tight face of an inequality is the convex hull of its listed tight
vertices. The affine dimensions in the second table are calculated from
those exact vertices. Rows 0,6,16,18 have dimensions 4,2,4,4 respectively;
all other 18 rows have dimension five and distinct hyperplanes. Each facet
of a full-dimensional halfspace intersection is carried by a defining
hyperplane, so there are no unlisted facets. $\square$

<!-- mathematical-data: vertices36 -->

| Vertex index $v$ | $(a_1,a_2,a_3,a_4,a_5,e)$ | Active halfspaces |
| --- | --- | --- |
| 0 | (0,0,0,0,0,0) | [1,2,3,4,5,6,8,13,16,17] |
| 1 | (7/13,7/13,7/13,7/13,7/13,3/13) | [1,2,3,4,11,13,14] |
| 2 | (10/17,10/17,10/17,9/17,9/17,4/17) | [1,2,4,9,11,13,14,15] |
| 3 | (10/17,10/17,10/17,10/17,8/17,4/17) | [1,2,3,9,11,13] |
| 4 | (3/5,3/5,3/5,3/5,1/5,1/5) | [1,2,3,5,12,13,18,20] |
| 5 | (3/5,3/5,3/5,3/5,4/7,9/35) | [1,2,3,9,11,14] |
| 6 | (8/13,8/13,8/13,8/13,5/13,3/13) | [1,2,3,9,12,13] |
| 7 | (28/45,28/45,28/45,7/15,7/15,2/9) | [1,2,4,13,15,21] |
| 8 | (9/14,9/14,9/14,9/14,9/14,2/7) | [1,2,3,4,9,14] |
| 9 | (20/31,20/31,20/31,11/31,11/31,6/31) | [1,2,4,13,19,21] |
| 10 | (11/17,11/17,11/17,5/17,5/17,3/17) | [1,2,4,13,17,19] |
| 11 | (2/3,2/3,2/3,1/3,1/6,1/6) | [1,2,5,13,16,17,18,19,20] |
| 12 | (2/3,2/3,2/3,5/9,1/3,2/9) | [1,2,9,10,12,13,15,19,20,21] |
| 13 | (19/28,19/28,19/28,19/28,5/14,1/4) | [1,2,3,9,10,12,20] |
| 14 | (20/29,20/29,20/29,17/29,17/29,8/29) | [1,2,4,9,10,15,21] |
| 15 | (22/31,22/31,22/31,22/31,22/31,10/31) | [1,2,3,4,9,10] |
| 16 | (13/17,10/17,10/17,9/17,9/17,4/17) | [2,4,7,9,11,13,14,15] |
| 17 | (13/17,10/17,10/17,10/17,8/17,4/17) | [2,3,7,9,11,13] |
| 18 | (10/13,7/13,7/13,7/13,7/13,3/13) | [2,3,4,7,11,13,14] |
| 19 | (10/13,8/13,8/13,8/13,5/13,3/13) | [2,3,7,9,12,13] |
| 20 | (27/35,3/5,3/5,3/5,4/7,9/35) | [2,3,7,9,11,14] |
| 21 | (7/9,28/45,28/45,7/15,7/15,2/9) | [2,4,7,13,15,21] |
| 22 | (7/9,2/3,2/3,5/9,1/3,2/9) | [2,7,9,10,12,13,15,19,20,21] |
| 23 | (11/14,9/14,9/14,9/14,9/14,2/7) | [2,3,4,7,9,14] |
| 24 | (11/14,19/28,19/28,19/28,5/14,1/4) | [2,3,7,9,10,12,20] |
| 25 | (23/29,20/29,20/29,17/29,17/29,8/29) | [2,4,7,9,10,15,21] |
| 26 | (4/5,3/5,3/5,3/5,1/5,1/5) | [2,3,5,7,12,13,18,20] |
| 27 | (25/31,20/31,20/31,11/31,11/31,6/31) | [2,4,7,13,19,21] |
| 28 | (25/31,22/31,22/31,22/31,22/31,10/31) | [2,3,4,7,9,10] |
| 29 | (14/17,11/17,11/17,5/17,5/17,3/17) | [2,4,7,13,17,19] |
| 30 | (5/6,2/3,2/3,1/3,1/6,1/6) | [2,5,7,13,16,17,18,19,20] |
| 31 | (1,0,0,0,0,0) | [0,2,3,4,5,6,7,8,13,16,17] |
| 32 | (1,1,0,0,0,0) | [0,1,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21] |
| 33 | (1,1,1,1/4,1/4,1/4) | [0,1,2,4,5,7,8,10,16,17,18,19,20,21] |
| 34 | (1,1,1,1,2/5,2/5) | [0,1,2,3,5,7,8,10,18,20] |
| 35 | (1,1,1,1,1,1/2) | [0,1,2,3,4,7,8,10] |

<!-- mathematical-data: facets22 -->

| Row | Tight vertices | Affine dimension |
| --- | --- | --- |
| 0 | [31,32,33,34,35] | 4 |
| 1 | [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,32,33,34,35] | 5 |
| 2 | [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,33,34,35] | 5 |
| 3 | [0,1,3,4,5,6,8,13,15,17,18,19,20,23,24,26,28,31,32,34,35] | 5 |
| 4 | [0,1,2,7,8,9,10,14,15,16,18,21,23,25,27,28,29,31,32,33,35] | 5 |
| 5 | [0,4,11,26,30,31,32,33,34] | 5 |
| 6 | [0,31,32] | 2 |
| 7 | [16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35] | 5 |
| 8 | [0,31,32,33,34,35] | 5 |
| 9 | [2,3,5,6,8,12,13,14,15,16,17,19,20,22,23,24,25,28,32] | 5 |
| 10 | [12,13,14,15,22,24,25,28,32,33,34,35] | 5 |
| 11 | [1,2,3,5,16,17,18,20,32] | 5 |
| 12 | [4,6,12,13,19,22,24,26,32] | 5 |
| 13 | [0,1,2,3,4,6,7,9,10,11,12,16,17,18,19,21,22,26,27,29,30,31,32] | 5 |
| 14 | [1,2,5,8,16,18,20,23,32] | 5 |
| 15 | [2,7,12,14,16,21,22,25,32] | 5 |
| 16 | [0,11,30,31,32,33] | 4 |
| 17 | [0,10,11,29,30,31,32,33] | 5 |
| 18 | [4,11,26,30,32,33,34] | 4 |
| 19 | [9,10,11,12,22,27,29,30,32,33] | 5 |
| 20 | [4,11,12,13,22,24,26,30,32,33,34] | 5 |
| 21 | [7,9,12,14,21,22,25,27,32,33] | 5 |

All 22 inequalities are retained in the description. In particular $R1$
and $R3$ remain valid necessary rows even though they are not facets of
this six-dimensional polytope. Rows $R2,R4,R5,R6$ each carry a
five-dimensional face. Counting these faces does not assert a new scalar
result or external literary priority.

## 145. Thirty-six full stopped allocations

**Definition 145.1 (Reconstructible coordinate order).** In each cell
order labels $r=0,\ldots,5$, and put coordinate index $z=6c+r$ where $c$
is the cell's zero-based index. All six outputs in every one of the 41
$O$ cells and 51 $N$ cells belong to their complete models.
The following table supplies the first cell index of each schedule in
both orders. Singleton cells follow in order $0,1$; $O$ pair cells follow
in order $0,10,11$ and $N$ pair cells in order $00,01,10,11$.

<!-- mathematical-data: cell-offsets -->

| Schedule index | Schedule | First $O$ cell | First $N$ cell | $O$ / $N$ cell count |
| --- | --- | --- | --- | --- |
| 0 | () | 0 | 0 | 1 |
| 1 | (1) | 1 | 1 | 2 |
| 2 | (2) | 3 | 3 | 2 |
| 3 | (3) | 5 | 5 | 2 |
| 4 | (4) | 7 | 7 | 2 |
| 5 | (5) | 9 | 9 | 2 |
| 6 | (1,2) | 11 | 11 | 3 / 4 |
| 7 | (1,3) | 14 | 15 | 3 / 4 |
| 8 | (1,4) | 17 | 19 | 3 / 4 |
| 9 | (1,5) | 20 | 23 | 3 / 4 |
| 10 | (2,3) | 23 | 27 | 3 / 4 |
| 11 | (2,4) | 26 | 31 | 3 / 4 |
| 12 | (2,5) | 29 | 35 | 3 / 4 |
| 13 | (3,4) | 32 | 39 | 3 / 4 |
| 14 | (3,5) | 35 | 43 | 3 / 4 |
| 15 | (4,5) | 38 | 47 | 3 / 4 |

**Definition 145.2 (Primitive full-coordinate endpoint lifts).** For each
vertex $v$, the denominator $d_v$ is a positive integer. Divide its six
profile numerators and every listed terminal numerator by the same
$d_v$. Unlisted terminal coordinates among all 246 coordinates are zero.
The sparse list specifies the whole vector; it forbids no schedule or
label in the model. The profile row agrees with vertex $v$ of Theorem
144.3. There are 723 nonzero terminal entries across the 36 lifts, and
the largest denominator is 45.

<!-- mathematical-data: endpoint-profiles -->

| Vertex $v$ | Denominator $d_v$ | Six profile numerators |
| --- | --- | --- |
| 0 | 1 | (0,0,0,0,0,0) |
| 1 | 13 | (7,7,7,7,7,3) |
| 2 | 17 | (10,10,10,9,9,4) |
| 3 | 17 | (10,10,10,10,8,4) |
| 4 | 5 | (3,3,3,3,1,1) |
| 5 | 35 | (21,21,21,21,20,9) |
| 6 | 13 | (8,8,8,8,5,3) |
| 7 | 45 | (28,28,28,21,21,10) |
| 8 | 14 | (9,9,9,9,9,4) |
| 9 | 31 | (20,20,20,11,11,6) |
| 10 | 17 | (11,11,11,5,5,3) |
| 11 | 6 | (4,4,4,2,1,1) |
| 12 | 9 | (6,6,6,5,3,2) |
| 13 | 28 | (19,19,19,19,10,7) |
| 14 | 29 | (20,20,20,17,17,8) |
| 15 | 31 | (22,22,22,22,22,10) |
| 16 | 17 | (13,10,10,9,9,4) |
| 17 | 17 | (13,10,10,10,8,4) |
| 18 | 13 | (10,7,7,7,7,3) |
| 19 | 13 | (10,8,8,8,5,3) |
| 20 | 35 | (27,21,21,21,20,9) |
| 21 | 45 | (35,28,28,21,21,10) |
| 22 | 9 | (7,6,6,5,3,2) |
| 23 | 14 | (11,9,9,9,9,4) |
| 24 | 28 | (22,19,19,19,10,7) |
| 25 | 29 | (23,20,20,17,17,8) |
| 26 | 5 | (4,3,3,3,1,1) |
| 27 | 31 | (25,20,20,11,11,6) |
| 28 | 31 | (25,22,22,22,22,10) |
| 29 | 17 | (14,11,11,5,5,3) |
| 30 | 6 | (5,4,4,2,1,1) |
| 31 | 1 | (1,0,0,0,0,0) |
| 32 | 1 | (1,1,0,0,0,0) |
| 33 | 4 | (4,4,4,1,1,1) |
| 34 | 5 | (5,5,5,5,2,2) |
| 35 | 2 | (2,2,2,2,2,1) |

### Stopped lift 0

<!-- mathematical-data: lift-0 -->

| Full $O$ coordinate $z$ | Terminal numerator $t^v_z$ |
| --- | --- |
| 54 | 1 |
| 60 | 1 |

### Stopped lift 1

<!-- mathematical-data: lift-1 -->

| Full $O$ coordinate $z$ | Terminal numerator $t^v_z$ |
| --- | --- |
| 66 | 2 |
| 67 | 2 |
| 74 | 4 |
| 78 | 3 |
| 83 | 1 |
| 85 | 2 |
| 93 | 2 |
| 96 | 2 |
| 102 | 1 |
| 112 | 1 |
| 114 | 1 |
| 138 | 2 |
| 147 | 2 |
| 150 | 2 |
| 156 | 1 |
| 166 | 1 |
| 168 | 1 |
| 192 | 2 |
| 202 | 2 |
| 209 | 2 |
| 228 | 1 |
| 239 | 1 |
| 240 | 1 |

### Stopped lift 2

<!-- mathematical-data: lift-2 -->

| Full $O$ coordinate $z$ | Terminal numerator $t^v_z$ |
| --- | --- |
| 66 | 3 |
| 67 | 2 |
| 74 | 5 |
| 78 | 3 |
| 83 | 2 |
| 85 | 3 |
| 93 | 3 |
| 96 | 3 |
| 103 | 1 |
| 112 | 1 |
| 114 | 1 |
| 138 | 3 |
| 147 | 3 |
| 150 | 3 |
| 158 | 1 |
| 166 | 1 |
| 168 | 1 |
| 192 | 3 |
| 202 | 3 |
| 204 | 1 |
| 209 | 2 |
| 228 | 1 |
| 239 | 1 |
| 240 | 1 |

### Stopped lift 3

<!-- mathematical-data: lift-3 -->

| Full $O$ coordinate $z$ | Terminal numerator $t^v_z$ |
| --- | --- |
| 67 | 5 |
| 74 | 5 |
| 78 | 3 |
| 82 | 1 |
| 83 | 1 |
| 84 | 3 |
| 93 | 3 |
| 96 | 3 |
| 103 | 1 |
| 112 | 1 |
| 114 | 1 |
| 138 | 3 |
| 147 | 3 |
| 150 | 3 |
| 158 | 1 |
| 166 | 1 |
| 168 | 1 |
| 192 | 3 |
| 202 | 3 |
| 204 | 1 |
| 209 | 2 |
| 228 | 1 |
| 239 | 1 |
| 240 | 1 |

### Stopped lift 4

<!-- mathematical-data: lift-4 -->

| Full $O$ coordinate $z$ | Terminal numerator $t^v_z$ |
| --- | --- |
| 67 | 2 |
| 74 | 2 |
| 78 | 1 |
| 82 | 1 |
| 85 | 1 |
| 93 | 1 |
| 96 | 1 |
| 138 | 1 |
| 147 | 1 |
| 150 | 1 |
| 192 | 1 |
| 202 | 1 |
| 204 | 1 |

### Stopped lift 5

<!-- mathematical-data: lift-5 -->

| Full $O$ coordinate $z$ | Terminal numerator $t^v_z$ |
| --- | --- |
| 67 | 9 |
| 74 | 9 |
| 78 | 6 |
| 83 | 3 |
| 84 | 3 |
| 85 | 3 |
| 93 | 6 |
| 96 | 6 |
| 102 | 3 |
| 112 | 3 |
| 114 | 2 |
| 119 | 1 |
| 138 | 6 |
| 147 | 6 |
| 150 | 6 |
| 158 | 3 |
| 166 | 3 |
| 168 | 2 |
| 173 | 1 |
| 192 | 6 |
| 202 | 6 |
| 204 | 2 |
| 209 | 4 |
| 228 | 2 |
| 239 | 2 |
| 240 | 2 |

### Stopped lift 6

<!-- mathematical-data: lift-6 -->

| Full $O$ coordinate $z$ | Terminal numerator $t^v_z$ |
| --- | --- |
| 67 | 4 |
| 74 | 4 |
| 78 | 2 |
| 81 | 1 |
| 82 | 1 |
| 84 | 2 |
| 93 | 2 |
| 96 | 2 |
| 103 | 1 |
| 112 | 1 |
| 114 | 1 |
| 138 | 1 |
| 140 | 1 |
| 147 | 2 |
| 150 | 2 |
| 156 | 1 |
| 166 | 1 |
| 168 | 1 |
| 192 | 2 |
| 202 | 2 |
| 204 | 1 |
| 209 | 1 |
| 228 | 1 |
| 239 | 1 |
| 240 | 1 |

### Stopped lift 7

<!-- mathematical-data: lift-7 -->

| Full $O$ coordinate $z$ | Terminal numerator $t^v_z$ |
| --- | --- |
| 66 | 4 |
| 67 | 11 |
| 74 | 15 |
| 78 | 7 |
| 81 | 4 |
| 83 | 4 |
| 85 | 7 |
| 93 | 7 |
| 96 | 7 |
| 102 | 3 |
| 112 | 3 |
| 114 | 3 |
| 138 | 4 |
| 140 | 3 |
| 147 | 7 |
| 150 | 7 |
| 156 | 3 |
| 166 | 3 |
| 168 | 3 |
| 192 | 5 |
| 202 | 5 |
| 204 | 3 |
| 209 | 2 |
| 210 | 2 |
| 221 | 2 |
| 222 | 2 |
| 228 | 3 |
| 239 | 3 |
| 240 | 3 |

### Stopped lift 8

<!-- mathematical-data: lift-8 -->

| Full $O$ coordinate $z$ | Terminal numerator $t^v_z$ |
| --- | --- |
| 67 | 4 |
| 74 | 4 |
| 78 | 2 |
| 83 | 2 |
| 84 | 1 |
| 85 | 1 |
| 93 | 2 |
| 96 | 2 |
| 102 | 1 |
| 112 | 1 |
| 114 | 1 |
| 138 | 2 |
| 147 | 2 |
| 150 | 2 |
| 158 | 1 |
| 166 | 1 |
| 168 | 1 |
| 192 | 2 |
| 195 | 1 |
| 202 | 3 |
| 204 | 1 |
| 209 | 2 |
| 228 | 1 |
| 239 | 1 |
| 240 | 1 |

### Stopped lift 9

<!-- mathematical-data: lift-9 -->

| Full $O$ coordinate $z$ | Terminal numerator $t^v_z$ |
| --- | --- |
| 67 | 13 |
| 74 | 13 |
| 78 | 9 |
| 81 | 4 |
| 84 | 4 |
| 85 | 1 |
| 93 | 5 |
| 96 | 5 |
| 102 | 1 |
| 112 | 1 |
| 114 | 1 |
| 138 | 4 |
| 140 | 1 |
| 147 | 5 |
| 150 | 5 |
| 156 | 1 |
| 166 | 1 |
| 168 | 1 |
| 192 | 3 |
| 202 | 3 |
| 204 | 1 |
| 209 | 2 |
| 210 | 2 |
| 221 | 2 |
| 222 | 2 |
| 228 | 1 |
| 239 | 1 |
| 240 | 1 |

### Stopped lift 10

<!-- mathematical-data: lift-10 -->

| Full $O$ coordinate $z$ | Terminal numerator $t^v_z$ |
| --- | --- |
| 66 | 3 |
| 67 | 5 |
| 74 | 8 |
| 78 | 6 |
| 81 | 2 |
| 85 | 3 |
| 93 | 3 |
| 96 | 3 |
| 138 | 3 |
| 147 | 3 |
| 150 | 3 |
| 192 | 2 |
| 202 | 2 |
| 204 | 1 |
| 209 | 1 |
| 210 | 1 |
| 221 | 1 |
| 222 | 1 |

### Stopped lift 11

<!-- mathematical-data: lift-11 -->

| Full $O$ coordinate $z$ | Terminal numerator $t^v_z$ |
| --- | --- |
| 67 | 3 |
| 74 | 3 |
| 78 | 2 |
| 81 | 1 |
| 84 | 1 |
| 93 | 1 |
| 96 | 1 |
| 138 | 1 |
| 147 | 1 |
| 150 | 1 |
| 192 | 1 |
| 202 | 1 |
| 204 | 1 |

### Stopped lift 12

<!-- mathematical-data: lift-12 -->

| Full $O$ coordinate $z$ | Terminal numerator $t^v_z$ |
| --- | --- |
| 67 | 3 |
| 74 | 3 |
| 78 | 1 |
| 81 | 2 |
| 84 | 1 |
| 93 | 1 |
| 96 | 1 |
| 103 | 1 |
| 112 | 1 |
| 114 | 1 |
| 140 | 1 |
| 147 | 1 |
| 150 | 1 |
| 156 | 1 |
| 166 | 1 |
| 168 | 1 |
| 192 | 1 |
| 202 | 1 |
| 204 | 1 |
| 228 | 1 |
| 239 | 1 |
| 240 | 1 |

### Stopped lift 13

<!-- mathematical-data: lift-13 -->

| Full $O$ coordinate $z$ | Terminal numerator $t^v_z$ |
| --- | --- |
| 67 | 8 |
| 74 | 8 |
| 78 | 3 |
| 81 | 4 |
| 82 | 1 |
| 84 | 3 |
| 85 | 1 |
| 93 | 4 |
| 96 | 3 |
| 100 | 1 |
| 103 | 3 |
| 112 | 3 |
| 114 | 3 |
| 140 | 4 |
| 147 | 4 |
| 150 | 3 |
| 154 | 1 |
| 156 | 3 |
| 166 | 3 |
| 168 | 3 |
| 192 | 3 |
| 202 | 3 |
| 204 | 3 |
| 228 | 3 |
| 239 | 3 |
| 240 | 3 |

### Stopped lift 14

<!-- mathematical-data: lift-14 -->

| Full $O$ coordinate $z$ | Terminal numerator $t^v_z$ |
| --- | --- |
| 67 | 7 |
| 74 | 7 |
| 78 | 3 |
| 81 | 2 |
| 83 | 2 |
| 85 | 5 |
| 93 | 5 |
| 96 | 3 |
| 101 | 2 |
| 102 | 3 |
| 112 | 3 |
| 114 | 3 |
| 138 | 3 |
| 140 | 2 |
| 147 | 5 |
| 150 | 3 |
| 155 | 2 |
| 158 | 3 |
| 166 | 3 |
| 168 | 3 |
| 192 | 3 |
| 202 | 3 |
| 204 | 3 |
| 228 | 3 |
| 239 | 3 |
| 240 | 3 |

### Stopped lift 15

<!-- mathematical-data: lift-15 -->

| Full $O$ coordinate $z$ | Terminal numerator $t^v_z$ |
| --- | --- |
| 67 | 8 |
| 74 | 8 |
| 78 | 3 |
| 81 | 1 |
| 83 | 4 |
| 84 | 3 |
| 85 | 1 |
| 93 | 4 |
| 96 | 3 |
| 101 | 1 |
| 103 | 3 |
| 112 | 3 |
| 114 | 3 |
| 140 | 4 |
| 147 | 4 |
| 150 | 3 |
| 155 | 1 |
| 156 | 3 |
| 166 | 3 |
| 168 | 3 |
| 192 | 3 |
| 195 | 3 |
| 202 | 6 |
| 204 | 3 |
| 209 | 3 |
| 228 | 3 |
| 239 | 3 |
| 240 | 3 |

### Stopped lift 16

<!-- mathematical-data: lift-16 -->

| Full $O$ coordinate $z$ | Terminal numerator $t^v_z$ |
| --- | --- |
| 67 | 5 |
| 74 | 5 |
| 78 | 3 |
| 83 | 2 |
| 85 | 3 |
| 93 | 3 |
| 96 | 3 |
| 103 | 1 |
| 112 | 1 |
| 114 | 1 |
| 138 | 2 |
| 140 | 1 |
| 147 | 3 |
| 150 | 3 |
| 156 | 1 |
| 166 | 1 |
| 168 | 1 |
| 192 | 3 |
| 202 | 3 |
| 204 | 1 |
| 209 | 2 |
| 228 | 1 |
| 239 | 1 |
| 240 | 1 |

### Stopped lift 17

<!-- mathematical-data: lift-17 -->

| Full $O$ coordinate $z$ | Terminal numerator $t^v_z$ |
| --- | --- |
| 67 | 5 |
| 74 | 5 |
| 78 | 3 |
| 82 | 1 |
| 83 | 1 |
| 85 | 3 |
| 93 | 3 |
| 96 | 3 |
| 103 | 1 |
| 112 | 1 |
| 114 | 1 |
| 138 | 2 |
| 140 | 1 |
| 147 | 3 |
| 150 | 3 |
| 156 | 1 |
| 166 | 1 |
| 168 | 1 |
| 192 | 3 |
| 202 | 3 |
| 204 | 1 |
| 209 | 2 |
| 228 | 1 |
| 239 | 1 |
| 240 | 1 |

### Stopped lift 18

<!-- mathematical-data: lift-18 -->

| Full $O$ coordinate $z$ | Terminal numerator $t^v_z$ |
| --- | --- |
| 67 | 4 |
| 74 | 4 |
| 78 | 3 |
| 83 | 1 |
| 85 | 2 |
| 93 | 2 |
| 96 | 2 |
| 103 | 1 |
| 112 | 1 |
| 114 | 1 |
| 138 | 2 |
| 147 | 2 |
| 150 | 2 |
| 156 | 1 |
| 166 | 1 |
| 168 | 1 |
| 192 | 2 |
| 202 | 2 |
| 209 | 2 |
| 228 | 1 |
| 239 | 1 |
| 240 | 1 |

### Stopped lift 19

<!-- mathematical-data: lift-19 -->

| Full $O$ coordinate $z$ | Terminal numerator $t^v_z$ |
| --- | --- |
| 67 | 4 |
| 74 | 4 |
| 78 | 2 |
| 81 | 1 |
| 82 | 1 |
| 85 | 2 |
| 93 | 2 |
| 96 | 2 |
| 103 | 1 |
| 112 | 1 |
| 114 | 1 |
| 138 | 1 |
| 140 | 1 |
| 147 | 2 |
| 150 | 2 |
| 156 | 1 |
| 166 | 1 |
| 168 | 1 |
| 192 | 2 |
| 202 | 2 |
| 204 | 1 |
| 209 | 1 |
| 228 | 1 |
| 239 | 1 |
| 240 | 1 |

### Stopped lift 20

<!-- mathematical-data: lift-20 -->

| Full $O$ coordinate $z$ | Terminal numerator $t^v_z$ |
| --- | --- |
| 67 | 9 |
| 74 | 9 |
| 78 | 6 |
| 83 | 3 |
| 85 | 6 |
| 93 | 6 |
| 96 | 6 |
| 103 | 3 |
| 112 | 3 |
| 114 | 2 |
| 119 | 1 |
| 138 | 6 |
| 147 | 6 |
| 150 | 6 |
| 158 | 3 |
| 166 | 3 |
| 168 | 2 |
| 173 | 1 |
| 192 | 6 |
| 202 | 6 |
| 204 | 2 |
| 209 | 4 |
| 228 | 2 |
| 239 | 2 |
| 240 | 2 |

### Stopped lift 21

<!-- mathematical-data: lift-21 -->

| Full $O$ coordinate $z$ | Terminal numerator $t^v_z$ |
| --- | --- |
| 67 | 15 |
| 74 | 15 |
| 78 | 7 |
| 81 | 4 |
| 83 | 4 |
| 85 | 7 |
| 93 | 7 |
| 96 | 7 |
| 103 | 3 |
| 112 | 3 |
| 114 | 3 |
| 138 | 7 |
| 147 | 7 |
| 150 | 7 |
| 158 | 3 |
| 166 | 3 |
| 168 | 3 |
| 192 | 5 |
| 202 | 5 |
| 204 | 3 |
| 209 | 2 |
| 210 | 2 |
| 221 | 2 |
| 222 | 2 |
| 228 | 3 |
| 239 | 3 |
| 240 | 3 |

### Stopped lift 22

<!-- mathematical-data: lift-22 -->

| Full $O$ coordinate $z$ | Terminal numerator $t^v_z$ |
| --- | --- |
| 67 | 3 |
| 74 | 3 |
| 78 | 1 |
| 81 | 2 |
| 85 | 1 |
| 93 | 1 |
| 96 | 1 |
| 103 | 1 |
| 112 | 1 |
| 114 | 1 |
| 140 | 1 |
| 147 | 1 |
| 150 | 1 |
| 156 | 1 |
| 166 | 1 |
| 168 | 1 |
| 192 | 1 |
| 202 | 1 |
| 204 | 1 |
| 228 | 1 |
| 239 | 1 |
| 240 | 1 |

### Stopped lift 23

<!-- mathematical-data: lift-23 -->

| Full $O$ coordinate $z$ | Terminal numerator $t^v_z$ |
| --- | --- |
| 67 | 4 |
| 74 | 4 |
| 78 | 2 |
| 83 | 2 |
| 85 | 2 |
| 93 | 2 |
| 96 | 2 |
| 103 | 1 |
| 112 | 1 |
| 114 | 1 |
| 138 | 2 |
| 147 | 2 |
| 150 | 2 |
| 158 | 1 |
| 166 | 1 |
| 168 | 1 |
| 192 | 2 |
| 195 | 1 |
| 202 | 3 |
| 204 | 1 |
| 209 | 2 |
| 228 | 1 |
| 239 | 1 |
| 240 | 1 |

### Stopped lift 24

<!-- mathematical-data: lift-24 -->

| Full $O$ coordinate $z$ | Terminal numerator $t^v_z$ |
| --- | --- |
| 67 | 8 |
| 74 | 8 |
| 78 | 3 |
| 81 | 4 |
| 82 | 1 |
| 85 | 4 |
| 93 | 4 |
| 96 | 3 |
| 100 | 1 |
| 103 | 3 |
| 112 | 3 |
| 114 | 3 |
| 140 | 4 |
| 147 | 4 |
| 150 | 3 |
| 154 | 1 |
| 156 | 3 |
| 166 | 3 |
| 168 | 3 |
| 192 | 3 |
| 202 | 3 |
| 204 | 3 |
| 228 | 3 |
| 239 | 3 |
| 240 | 3 |

### Stopped lift 25

<!-- mathematical-data: lift-25 -->

| Full $O$ coordinate $z$ | Terminal numerator $t^v_z$ |
| --- | --- |
| 67 | 7 |
| 74 | 7 |
| 78 | 3 |
| 81 | 2 |
| 83 | 2 |
| 85 | 5 |
| 93 | 5 |
| 96 | 3 |
| 101 | 2 |
| 103 | 3 |
| 112 | 3 |
| 114 | 3 |
| 138 | 3 |
| 140 | 2 |
| 147 | 5 |
| 150 | 3 |
| 155 | 2 |
| 158 | 3 |
| 166 | 3 |
| 168 | 3 |
| 192 | 3 |
| 202 | 3 |
| 204 | 3 |
| 228 | 3 |
| 239 | 3 |
| 240 | 3 |

### Stopped lift 26

<!-- mathematical-data: lift-26 -->

| Full $O$ coordinate $z$ | Terminal numerator $t^v_z$ |
| --- | --- |
| 67 | 2 |
| 74 | 2 |
| 78 | 1 |
| 82 | 1 |
| 85 | 1 |
| 93 | 1 |
| 96 | 1 |
| 138 | 1 |
| 147 | 1 |
| 150 | 1 |
| 192 | 1 |
| 202 | 1 |
| 204 | 1 |

### Stopped lift 27

<!-- mathematical-data: lift-27 -->

| Full $O$ coordinate $z$ | Terminal numerator $t^v_z$ |
| --- | --- |
| 67 | 13 |
| 74 | 13 |
| 78 | 9 |
| 81 | 4 |
| 85 | 5 |
| 93 | 5 |
| 96 | 5 |
| 103 | 1 |
| 112 | 1 |
| 114 | 1 |
| 138 | 5 |
| 147 | 5 |
| 150 | 5 |
| 158 | 1 |
| 166 | 1 |
| 168 | 1 |
| 192 | 3 |
| 202 | 3 |
| 204 | 1 |
| 209 | 2 |
| 210 | 2 |
| 221 | 2 |
| 222 | 2 |
| 228 | 1 |
| 239 | 1 |
| 240 | 1 |

### Stopped lift 28

<!-- mathematical-data: lift-28 -->

| Full $O$ coordinate $z$ | Terminal numerator $t^v_z$ |
| --- | --- |
| 67 | 5 |
| 74 | 5 |
| 78 | 3 |
| 81 | 1 |
| 83 | 1 |
| 85 | 4 |
| 93 | 4 |
| 96 | 3 |
| 101 | 1 |
| 103 | 6 |
| 112 | 6 |
| 114 | 3 |
| 119 | 3 |
| 138 | 3 |
| 140 | 4 |
| 147 | 7 |
| 150 | 3 |
| 155 | 4 |
| 158 | 3 |
| 166 | 3 |
| 168 | 3 |
| 192 | 3 |
| 202 | 3 |
| 204 | 3 |
| 228 | 3 |
| 239 | 3 |
| 240 | 3 |

### Stopped lift 29

<!-- mathematical-data: lift-29 -->

| Full $O$ coordinate $z$ | Terminal numerator $t^v_z$ |
| --- | --- |
| 67 | 8 |
| 74 | 8 |
| 78 | 6 |
| 81 | 2 |
| 85 | 3 |
| 93 | 3 |
| 96 | 3 |
| 138 | 3 |
| 147 | 3 |
| 150 | 3 |
| 192 | 2 |
| 202 | 2 |
| 204 | 1 |
| 209 | 1 |
| 210 | 1 |
| 221 | 1 |
| 222 | 1 |

### Stopped lift 30

<!-- mathematical-data: lift-30 -->

| Full $O$ coordinate $z$ | Terminal numerator $t^v_z$ |
| --- | --- |
| 67 | 3 |
| 74 | 3 |
| 78 | 2 |
| 81 | 1 |
| 85 | 1 |
| 93 | 1 |
| 96 | 1 |
| 138 | 1 |
| 147 | 1 |
| 150 | 1 |
| 192 | 1 |
| 202 | 1 |
| 204 | 1 |

### Stopped lift 31

<!-- mathematical-data: lift-31 -->

| Full $O$ coordinate $z$ | Terminal numerator $t^v_z$ |
| --- | --- |
| 121 | 1 |
| 126 | 1 |
| 132 | 1 |

### Stopped lift 32

<!-- mathematical-data: lift-32 -->

| Full $O$ coordinate $z$ | Terminal numerator $t^v_z$ |
| --- | --- |
| 67 | 1 |
| 74 | 1 |
| 78 | 1 |

### Stopped lift 33

<!-- mathematical-data: lift-33 -->

| Full $O$ coordinate $z$ | Terminal numerator $t^v_z$ |
| --- | --- |
| 67 | 2 |
| 74 | 2 |
| 78 | 1 |
| 81 | 1 |
| 85 | 1 |
| 93 | 1 |
| 96 | 1 |
| 140 | 1 |
| 147 | 1 |
| 150 | 1 |

### Stopped lift 34

<!-- mathematical-data: lift-34 -->

| Full $O$ coordinate $z$ | Terminal numerator $t^v_z$ |
| --- | --- |
| 67 | 3 |
| 74 | 3 |
| 78 | 1 |
| 81 | 1 |
| 82 | 1 |
| 195 | 2 |
| 202 | 2 |
| 204 | 2 |

### Stopped lift 35

<!-- mathematical-data: lift-35 -->

| Full $O$ coordinate $z$ | Terminal numerator $t^v_z$ |
| --- | --- |
| 67 | 1 |
| 74 | 1 |
| 81 | 1 |
| 232 | 1 |
| 239 | 1 |
| 240 | 1 |

**Proposition 145.3 (Normalization, every word and the base equality).**
Every lift in Definition 145.2 is one complete stopped allocation at its
vertex profile, obeys all 94 TV rows, and satisfies
$p^v_{11111}(0)=1-e_v$.

**Proof.** Write $A^v_i,E^v$ for the six profile numerators and
$t^v_{S,c,r}$ for terminal numerators reconstructed from the sparse list.
For each schedule and each of its stopped cells, summation gives the same
integer $m^v_S=\sum_r t^v_{S,c,r}$. The 16 masses, in schedule order,
are in the table below. Their sum is $d_v$. Thus all 26 independent
common-mass and global-normalization equations hold; nonnegativity is
explicit in the sparse data.

For every word reconstruct

$$
u^v_b(r)=\sum_{S\in\mathcal S_5}t^v_{S,c_O(b,S),r},\qquad
p^v_b(r)=u^v_b(r)/d_v.
\tag{145.1}
$$

Each law has total numerator $d_v$. At every zero-containing word with
first zero $n$, its three exact integer row slacks are

$$
\begin{aligned}
\sigma^v_{b,0}&=u^v_b(0)-d_v+A^v_n+E^v,\\
\sigma^v_{b,n}&=u^v_b(n)-A^v_n+E^v,\\
\sigma^v_{b,\mathrm{pair}}&=u^v_b(0)+u^v_b(n)-d_v+E^v.
\end{aligned}
\tag{145.2}
$$

The last slack is $u^v_{11111}(0)-d_v+E^v=0$.
For the given integer tables all these slacks are nonnegative; the minimum
in each vertex's set of 94 is zero. Formula (145.2) and the 94-row ordering
reconstruct every entry without an additional law or slack archive.
Equivalently direct event-TV evaluation is
$[d_v-\min(u^v_b(0),d_v-A^v_n)-\min(u^v_b(n),A^v_n)]/d_v$.
This is at most $E^v/d_v$ by the same exact inequalities.
These finite integer identities establish feasibility at each vertex,
including plateaus, zero amplitudes, $E^v=0$ and $a_{5,v}=e_v$.
There are 1152 reconstructible word laws and 3384 separate row slacks;
they are consequences of the primitive tables and not further independent
data. Proposition 141.2 proves their TV sufficiency. $\square$

<!-- mathematical-data: schedule-masses36 -->

| Vertex $v$ | $(m^v_S)_{S=0}^{15}$ | Sum | Minimum row slack numerator |
| --- | --- | --- | --- |
| 0 | (0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0) | 1 | 0 |
| 1 | (0,0,0,0,0,0,4,2,1,0,2,1,0,2,0,1) | 13 | 0 |
| 2 | (0,0,0,0,0,0,5,3,1,0,3,1,0,3,0,1) | 17 | 0 |
| 3 | (0,0,0,0,0,0,5,3,1,0,3,1,0,3,0,1) | 17 | 0 |
| 4 | (0,0,0,0,0,0,2,1,0,0,1,0,0,1,0,0) | 5 | 0 |
| 5 | (0,0,0,0,0,0,9,6,3,0,6,3,0,6,0,2) | 35 | 0 |
| 6 | (0,0,0,0,0,0,4,2,1,0,2,1,0,2,0,1) | 13 | 0 |
| 7 | (0,0,0,0,0,0,15,7,3,0,7,3,0,5,2,3) | 45 | 0 |
| 8 | (0,0,0,0,0,0,4,2,1,0,2,1,0,3,0,1) | 14 | 0 |
| 9 | (0,0,0,0,0,0,13,5,1,0,5,1,0,3,2,1) | 31 | 0 |
| 10 | (0,0,0,0,0,0,8,3,0,0,3,0,0,2,1,0) | 17 | 0 |
| 11 | (0,0,0,0,0,0,3,1,0,0,1,0,0,1,0,0) | 6 | 0 |
| 12 | (0,0,0,0,0,0,3,1,1,0,1,1,0,1,0,1) | 9 | 0 |
| 13 | (0,0,0,0,0,0,8,4,3,0,4,3,0,3,0,3) | 28 | 0 |
| 14 | (0,0,0,0,0,0,7,5,3,0,5,3,0,3,0,3) | 29 | 0 |
| 15 | (0,0,0,0,0,0,8,4,3,0,4,3,0,6,0,3) | 31 | 0 |
| 16 | (0,0,0,0,0,0,5,3,1,0,3,1,0,3,0,1) | 17 | 0 |
| 17 | (0,0,0,0,0,0,5,3,1,0,3,1,0,3,0,1) | 17 | 0 |
| 18 | (0,0,0,0,0,0,4,2,1,0,2,1,0,2,0,1) | 13 | 0 |
| 19 | (0,0,0,0,0,0,4,2,1,0,2,1,0,2,0,1) | 13 | 0 |
| 20 | (0,0,0,0,0,0,9,6,3,0,6,3,0,6,0,2) | 35 | 0 |
| 21 | (0,0,0,0,0,0,15,7,3,0,7,3,0,5,2,3) | 45 | 0 |
| 22 | (0,0,0,0,0,0,3,1,1,0,1,1,0,1,0,1) | 9 | 0 |
| 23 | (0,0,0,0,0,0,4,2,1,0,2,1,0,3,0,1) | 14 | 0 |
| 24 | (0,0,0,0,0,0,8,4,3,0,4,3,0,3,0,3) | 28 | 0 |
| 25 | (0,0,0,0,0,0,7,5,3,0,5,3,0,3,0,3) | 29 | 0 |
| 26 | (0,0,0,0,0,0,2,1,0,0,1,0,0,1,0,0) | 5 | 0 |
| 27 | (0,0,0,0,0,0,13,5,1,0,5,1,0,3,2,1) | 31 | 0 |
| 28 | (0,0,0,0,0,0,5,4,6,0,7,3,0,3,0,3) | 31 | 0 |
| 29 | (0,0,0,0,0,0,8,3,0,0,3,0,0,2,1,0) | 17 | 0 |
| 30 | (0,0,0,0,0,0,3,1,0,0,1,0,0,1,0,0) | 6 | 0 |
| 31 | (0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0) | 1 | 0 |
| 32 | (0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0) | 1 | 0 |
| 33 | (0,0,0,0,0,0,2,1,0,0,1,0,0,0,0,0) | 4 | 0 |
| 34 | (0,0,0,0,0,0,3,0,0,0,0,0,0,2,0,0) | 5 | 0 |
| 35 | (0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,1) | 2 | 0 |

The finite endpoints at $e=0$ or $a_5=e$ are auxiliary affine certificates.
They are not invented original positive infinite-tail sources. The original
construction uses only strict active profiles, while convex combinations
of these endpoint tables prove all their closed boundaries.

## 146. Completion, counted replies and the coefficient interface

**Definition 146.1 (246-to-306 completion).** For every stopped allocation
keep the empty and singleton tables and define the completed pair tables by

$$
\begin{aligned}
T^N_{(i,j),00,r}=T^N_{(i,j),01,r}&=T^O_{(i,j),0,r},\\
T^N_{(i,j),10,r}&=T^O_{(i,j),10,r},\\
T^N_{(i,j),11,r}&=T^O_{(i,j),11,r}.
\end{aligned}
\tag{146.1}
$$

Thus the coordinate lookup $f$ is indexed by each of the 306 $N$
coordinates and returns one of the 246 $O$ coordinates:
$T^N_z=T^O_{f(z)}$. It is not a map indexed by $O$ coordinates.
For $z<66$ use $f(z)=z$. For pair index $t=0,\ldots,9$, $N$ pair-cell
index $k=0,1,2,3$ and label $r=0,\ldots,5$,

$$
f(66+24t+6k+r)=66+18t+6\phi(k)+r,\qquad
(\phi(0),\phi(1),\phi(2),\phi(3))=(0,0,1,2).
\tag{146.2}
$$

The following blocks give all 306 entries in their reconstructible order;
concatenating the blocks in the first column's order gives the full lookup.

<!-- mathematical-data: completion306 -->

| First $N$ coordinate $z$ | $(f(z),\ldots,f(z+5))$ |
| --- | --- |
| 0 | [0,1,2,3,4,5] |
| 6 | [6,7,8,9,10,11] |
| 12 | [12,13,14,15,16,17] |
| 18 | [18,19,20,21,22,23] |
| 24 | [24,25,26,27,28,29] |
| 30 | [30,31,32,33,34,35] |
| 36 | [36,37,38,39,40,41] |
| 42 | [42,43,44,45,46,47] |
| 48 | [48,49,50,51,52,53] |
| 54 | [54,55,56,57,58,59] |
| 60 | [60,61,62,63,64,65] |
| 66 | [66,67,68,69,70,71] |
| 72 | [66,67,68,69,70,71] |
| 78 | [72,73,74,75,76,77] |
| 84 | [78,79,80,81,82,83] |
| 90 | [84,85,86,87,88,89] |
| 96 | [84,85,86,87,88,89] |
| 102 | [90,91,92,93,94,95] |
| 108 | [96,97,98,99,100,101] |
| 114 | [102,103,104,105,106,107] |
| 120 | [102,103,104,105,106,107] |
| 126 | [108,109,110,111,112,113] |
| 132 | [114,115,116,117,118,119] |
| 138 | [120,121,122,123,124,125] |
| 144 | [120,121,122,123,124,125] |
| 150 | [126,127,128,129,130,131] |
| 156 | [132,133,134,135,136,137] |
| 162 | [138,139,140,141,142,143] |
| 168 | [138,139,140,141,142,143] |
| 174 | [144,145,146,147,148,149] |
| 180 | [150,151,152,153,154,155] |
| 186 | [156,157,158,159,160,161] |
| 192 | [156,157,158,159,160,161] |
| 198 | [162,163,164,165,166,167] |
| 204 | [168,169,170,171,172,173] |
| 210 | [174,175,176,177,178,179] |
| 216 | [174,175,176,177,178,179] |
| 222 | [180,181,182,183,184,185] |
| 228 | [186,187,188,189,190,191] |
| 234 | [192,193,194,195,196,197] |
| 240 | [192,193,194,195,196,197] |
| 246 | [198,199,200,201,202,203] |
| 252 | [204,205,206,207,208,209] |
| 258 | [210,211,212,213,214,215] |
| 264 | [210,211,212,213,214,215] |
| 270 | [216,217,218,219,220,221] |
| 276 | [222,223,224,225,226,227] |
| 282 | [228,229,230,231,232,233] |
| 288 | [228,229,230,231,232,233] |
| 294 | [234,235,236,237,238,239] |
| 300 | [240,241,242,243,244,245] |

**Proposition 146.2 (Same laws and the exact stopped region).** Completion
preserves every word law, common schedule masses and global normalization.
It gives all 36 independent $N$ equalities from the stopped lifts.
Their kernels lie in $\mathscr C_5$ of Theorem 109.1.

**Proof.** If $b_i=0$, either pair word $00$ or $01$ uses the same stopped
cell $0$; on $10,11$ the completed cells are unchanged. Thus each schedule
contributes the identical vector on every word. Every duplicated cell has
mass $w_S$, so normalization persists.
At the original-source execution level select the same schedule and table
using the identical $U$, acquire the whole schedule for $N$, reconstruct
where $O$ would stop, and emit the same original tape. If $O$ stopped at
its first requested zero, the acquired later reply in the $N$ completion
is ignored but counted. At most two actual requests are made.
This is exactly the law-preserving containment of Proposition 90.2.

For completeness, the already proved coefficient interface uses the
componentwise degree-at-most-two expansion

$$
p_b=c+\sum_i\ell_i b_i+\sum_{i<j}Q_{ij}b_i b_j,
\quad V_i=\sum_{j>i}(-Q_{ij})_+,\quad
h_i=(V_i-\ell_i)_+,\quad H=\sum_i h_i.
\tag{146.3}
$$

Theorem 109.1 states precisely $p\in\mathscr C_5$ if and only if
$c\ge H$ for such a probability-vector kernel. Normalization implies
$\sum_rH(r)\le1$. These are vector inequalities with one probability budget,
not independent scalar costs. Our displayed stopped tables directly place
the kernels in $\mathscr O_5=\mathscr C_5$; (146.3) is a reused interface,
not a new coefficient or transport result. $\square$

## 147. One simultaneous mixture on the whole continuum

**Theorem 147.1 (Entire closed $Q$ projection and continuous section).**
For every $x\in Q$, the following are equivalent: complete five-bit $N$
closed-cap feasibility; $x\in P$; complete five-bit $O$ closed-cap feasibility.
A stopped allocation on all of $P$ can be chosen continuously and piecewise
affinely, with $p_{11111}(0)=1-e$ throughout.

**Proof.** A feasible full $N$ kernel satisfies every cut by Theorem 142.2,
so its parameter point in $Q$ lies in $P$. By Theorem 144.3, for every
$x\in P$ choose $\lambda_v\ge0$ with $\sum_v\lambda_v=1$ and
$x=\sum_{v=0}^{35}\lambda_v x_v$. Set

$$
T_{S,c,r}(x)=\sum_{v=0}^{35}\lambda_v(x)T^v_{S,c,r},\qquad
w_S(x)=\sum_{v=0}^{35}\lambda_v(x)w^v_S.
\tag{147.1}
$$

The same weights are used for every schedule, cell, label, word and row.
Terminal nonnegativity, all common-mass equations and global normalization
are affine. The word-law formula is linear, and each target event is
affine in its fixed first-zero amplitude. Thus each TV row and the
all-positive base equality survives this one common convex mixture.
Consequently the mixture is a feasible $O$ allocation. Completion gives
$O\subseteq N$, proving the three-way equivalence at every closed endpoint.
No separately optimized event or coordinate is substituted for a joint law.

To choose the weights continuously, impose the index order on the 36
vertices and use its pulling triangulation. For each face $F$, select its
smallest vertex and cone it over the recursively triangulated facets of
$F$ not containing it. Every ray in $F$ from that vertex meets such a
facet; facets containing the vertex are covered as boundary faces.
Induction on dimension proves coverage with simplex interiors disjoint.
On any shared face the recursively imposed vertex order is the same,
so its induced triangulations agree. This gives a conforming finite
triangulation using the existing vertices.

On each simplex use its unique affine barycentric coordinates and assign
zero to the other vertices. On an intersection face, off-face coordinates
vanish and the remaining barycentric coordinates agree by uniqueness.
They therefore define 36 global continuous, piecewise affine nonnegative
weights summing to one and reproducing $x$. Formula (147.1) then gives the
asserted continuous section. At boundary points and zero weights the same
formulas apply without a division. $\square$

**Proposition 147.2 (Continuous absolute cutpoints and one measurable seed).**
The section can be realized by one $U\sim\operatorname{Uniform}[0,1)$,
common to all sources. Terminal masses, schedule weights and global seed
cutpoints are continuous; normalized conditional ratios and emitted labels
need not be continuous at zero schedule mass or interval boundaries.

**Proof.** In the schedule order put
$L_S(x)=\sum_{S'<S}w_{S'}(x)$ and
$I_S(x)=[L_S(x),L_S(x)+w_S(x))$.
Inside $I_S$ and for each counterfactual cell $c$, put the absolute cutpoints

$$
G_{S,c,k}(x)=L_S(x)+\sum_{r<k}T_{S,c,r}(x),
\qquad 0\le k\le6.
\tag{147.2}
$$

They begin at $L_S$, end at $L_S+w_S$, and subdivide $I_S$ into label
intervals of lengths $T_{S,c,r}$. The seed selects $S$ by $I_S$ and fixes
all terminal labels by these cell-specific subdivisions before replies.
All these finite inequality-defined events are Borel in $(x,U)$.
A zero-mass schedule has an empty interval and is never executed.
Global cutpoints remain continuous at it without assigning
$T_{S,c,r}/w_S$ any limiting value. No continuity of those ratios is needed
or inferred. At an interval endpoint the half-open convention specifies
one measurable label; the label itself is not pointwise continuous there.
Every chosen $O$ schedule has at most two requests and finite handoff at
every actual source and every seed. Arbitrary real amplitudes entail
ordinary measurable existence, not effective exact evaluation or a runtime
bound for computing real cutpoints. $\square$

## 148. The entire original five-active closed-cap comparison

**Theorem 148.1 (Complete original $L=5$ replacement).** For every entire
sequence (140.2) and every positive closed cap $e$ with
$a_5>e\ge a_6$, under exactly Definition 140.1's original acquisition
contract,

$$
\exists N\in\mathcal N_2:\ e_a(N)\le e
\quad\Longleftrightarrow\quad
\exists O\in\mathcal O_2:\ e_a(O)\le e.
\tag{148.1}
$$

Equivalently, at this actual active length,
$\mathcal F_N(a,e)\ne\varnothing$ implies
$\mathcal F_N(a,e)\cap\mathscr C_5\ne\varnothing$.
The stopped law can differ from the initially given $N$ law.
For profiles in $P$ the section in Theorem 147.1 has uniform actual error
exactly $e$, as does its same-seed $N$ completion.

**Proof.** The reverse implication is Proposition 90.2. For the forward
implication let $N$ be any original full-carrier arbitrary-address witness.
Its original repeated requests, one common seed and sourcewise almost-sure
finite handoff are retained in the necessary $N$ direction of Theorem
110.2, which supplies one full finite $N$ cap witness. We reuse this
transport at the exact closed cap and impose no finite mark-support
restriction on the original competitor.

At active length five put $S=a_3+a_4+a_5$ and
$D_3=\sum_{i\ge3}(a_i-e)_+=S-3e$.
If $D_3\le3e$, the stopped residual construction of
[Theorem 113.3](KBONACCI_SELF_CALIBRATING_ACQUISITION_RESOURCES_CONTINUATION.md#113-residual-demand-and-a-common-stopped-mixture)
supplies an original $O$ at the same cap, including equality.
This is the residual complement of the polytope argument, not an omitted
parameter region. If $D_3>3e$, the reused necessary
[Theorem 113.2](KBONACCI_SELF_CALIBRATING_ACQUISITION_RESOURCES_CONTINUATION.md#113-residual-demand-and-a-common-stopped-mixture)
gives $D_3\le3e+1-a_1$. Hence
$S>6e$ and $a_1+S-6e\le1$, so $x\in Q$.
All thirteen score cuts follow from the full finite $N$ witness.
In particular $C3$ gives $\kappa_3\ge0$, with no strict positivity
assumption. Thus $x\in P$, and Theorem 147.1 supplies a stopped table.
This applies equally when $\kappa_3=0$, at every tie and at every zero
schedule boundary.

Run the one-seed construction on the actual scheduled original primes,
stopping at its first queried zero or exhaustion, and hand off the
chosen original $\theta_r$. It has zero advice, at most two actual
requests and finite measurable handoff at every source and seed.
If $n(x)\le5$, its first five replies are one of all 32 checked words,
and its selected target is exactly $\eta_b$. Every later zero pattern,
including multiple zeros, is covered by the complete word rows.
If $n(x)>5$, its low word is $11111$; no tail mark is emitted and
$p_{11111}(0)=1-e$. The reused exact tail identity (110.9) is

$$
\operatorname{TV}\bigl(p_{1^5},(1-a_{n(x)})\delta_{\theta_0}
                         +a_{n(x)}\delta_{\theta_{n(x)}}\bigr)
 =\max\{1-p_{11111}(0),a_{n(x)}\}=e.
\tag{148.2}
$$

Every prescribed positive monotone vanishing tail has $a_{n(x)}\le e$
there. Equality $a_6=e$ is allowed, and all later positive amplitudes
remain unchanged. There are actual tail sources by finite-pattern
occupancy, so the uniform supremum is exactly $e$ in the polytope case.
Theorem 109.1 identifies the stopped table with $\mathscr C_5$;
Theorem 110.2 provides the original closed-cap feasibility implication.
Completion with the same $U$ obtains and counts any remaining scheduled
reply, reconstructs the stopped cell and hands off the same original tape,
so it has the same uniform error and hard-two bound.
The two residual cases exhaust every original five-active profile.
The law-replacement statement does not contradict the exact-law
obstruction of Theorem 112.2. $\square$

All constructed marks lie in $B_1$. The unchanged consumer is unknown
there, and their finitely supported laws have TV distance one from each
unchanged original nonatomic $\mu_x$, as in Acquisition Resources 82.1.
This does not certify any performance against $\mu_x$; the comparison is
solely to the separately selected $\lambda_x^a$.
The proof closes the bounded five-active case. It supplies no general
$L\ge6$ containment, actual separator or universal all-amplitude theorem.

## 149. General finite projections and the complete stopped event image

**Definition 149.1 (All-$L$ cap rows and extended polytopes).** Fix any
integer $L\ge1$, retain $D_L$, $B_L$, $J_L$, the complete allocations
$K_{N,L},K_{O,L}$ and all cell conventions of Definition 140.2.
Order words lexicographically with $b_1$ first. For every zero-containing
word $b$ with first zero $n$ list the distinct rows

$$
\begin{array}{c|c|c}
\text{row}&E_j&d_j(a,e)=\eta_b(E_j)-e\\\hline
(b,0)&\{0\}&1-a_n-e\\
(b,n)&\{n\}&a_n-e\\
(b,\mathrm{pair})&\{0,n\}&1-e
\end{array}
\tag{149.1}
$$

and finally the row at $1^L$ with event $\{0\}$ and lower bound $1-e$.
There are $m_L=3(2^L-1)+1$ rows. All words, all union rows and all
multiple-zero patterns are present even if their eventual score weight
is zero. Define

$$
\begin{aligned}
P_{C,L}&=\{(a,e,w,T):(a,e)\in D_L,\ (w,T)\in K_{C,L},
                   \ p_{b_j}(E_j)\ge d_j(a,e)\ (0\le j<m_L)\},\\
\Pi_{C,L}&=\{(a,e):\exists(w,T),\ (a,e,w,T)\in P_{C,L}\},
\qquad C=N,O.
\end{aligned}
\tag{149.2}
$$

Proposition 141.2's two-point TV calculation applies with $n=n_L(b)$
and makes (149.1) exactly the full closed TV-cap system.
A finite $N$ schedule with static repeated or reversed observations is
represented by Definition 140.2's normalization; original requests still
count repetitions, and arbitrary-address transport remains exclusively
Theorem 110.2. Every finite terminal cell permits every label, including
unqueried labels. At a strict active profile, the stopped feasibility slice
is $\mathcal F_N(a,e)\cap\mathscr C_L$ by Theorems 109.1 and 110.2, where
$\mathcal F_N(a,e)=\{p\in\mathscr N_L:
  \operatorname{TV}(p_b,\eta_b)\le e\text{ for every }b\in B_L\}$.

**Definition 149.2 (Joint event image and downward closure).** Put

$$
\begin{aligned}
R_{O,L}&=\{v\in\mathbb R^{m_L}:v_j=p_{b_j}(E_j)
                             \text{ for one }(w,T)\in K_{O,L}\},\\
U_{O,L}&=R_{O,L}-\mathbb R_{\ge0}^{m_L}.
\end{aligned}
\tag{149.3}
$$

These are images of one complete globally normalized allocation, rather
than independently attainable marginal events. At any $(a,e)\in D_L$,
$O$ cap feasibility is exactly $d(a,e)\in U_{O,L}$.
For $y\in\mathbb R_{\ge0}^{m_L}$ define

$$
\begin{aligned}
h^y_{S,c}(r)&=\sum_{j=0}^{m_L-1}y_j
             \mathbf1_{c_O(b_j,S)=c}\mathbf1_{r\in E_j},\\
B_{O,L}(y)&=\max_{S\in\mathcal S_L}
              \sum_{c\in\operatorname{cells}_O(S)}\max_{r\in J_L}h^y_{S,c}(r).
\end{aligned}
\tag{149.4}
$$

Its outer choice is one schedule, and its inner choices are one complete
predetermined table on that schedule's stopped cells. It is not a sum of
independent per-word upper envelopes.

**Proposition 149.3 (Rational compactness and exact projection).**
$K_{C,L}$ and $P_{C,L}$ are compact rational polytopes. Their parameter
projections $\Pi_{C,L}$ and $R_{O,L}$ are compact rational polytopes.
$U_{O,L}$ is nonempty, closed, convex, rational polyhedral and downward
closed. It is unbounded and is not a cone.

**Proof.** Every $w_S$ lies in $[0,1]$ and every terminal coordinate lies
in $[0,w_S]$. All common-mass equations and cap inequalities have rational
coefficients. Together with bounded closed $D_L$ they give compact
rational polyhedra. Equalities may be encoded in two inequality directions.
Coordinate projection preserves rational polyhedrality by Fourier-Motzkin
elimination, which combines rational rows by rational operations, and
preserves compactness by continuity. The same applies to the linear event
image. Nonemptiness follows, for example, from the joint stopped
strictifier of Proposition 150.2 below.

The difference (149.3) is convex and rational polyhedral, being the
projection of $v\in R_{O,L}, z\ge0, u=v-z$.
For direct closedness, if $v_k-z_k\to u$, with $v_k\in R_{O,L}$,
pass to a subsequence $v_k\to v$ by compactness. Then $z_k\to v-u\ge0$,
so $u\in U_{O,L}$. Its recession directions include every $-e_j$.
It is not a cone: the always-base empty schedule gives an event vector
$v\in R_{O,L}\subseteq U_{O,L}$ whose final all-positive-event coordinate
is one. Every member of $U_{O,L}$ has that coordinate at most one, so
$2v\notin U_{O,L}$. Downward closure, rather than homogeneity, is the
property needed for nonnegative separation. $\square$

## 150. A rational full lift and one joint strictifier

**Proposition 150.1 (Rational witness for failed containment).** If
$\Pi_{N,L}\not\subseteq\Pi_{O,L}$, there is a rational full extended $N$
lift outside $\Pi_{O,L}$ and a rational closed halfspace of $\Pi_{O,L}$
that its parameter point strictly violates.

**Proof.** Choose $x_0\in\Pi_{N,L}\setminus\Pi_{O,L}$.
From a finite rational closed halfspace description of $\Pi_{O,L}$,
select a violated row $g(x)\le\beta$, with $g,\beta$ rational.
If a defining equality fails, use its violated inequality orientation.
Maximize $g$ over the entire extended compact polytope $P_{N,L}$.
The maximizing face contains a vertex. A vertex of a rational polytope
is rational because an independent full-rank system of active rational
constraints uniquely determines it, and Cramer's rule gives rational
coordinates. This includes lower-dimensional polytopes: the affine-hull
equations occur among the active rows. Choose this rational vertex
$(x_v,w^v,T^v)$. Then

$$
\delta=g(x_v)-\beta\ge g(x_0)-\beta>0
\tag{150.1}
$$

is rational. The lift, not only its parameter projection, is rational.
This prevents rounding a parameter point while losing its full common
allocation. $\square$

**Proposition 150.2 (One globally feasible stopped strictifier).** For
every $L\ge1$, set

$$
e_z=\frac12,\qquad a_{i,z}=A_z=\frac12+\frac1{4L} (1\le i\le L),
\qquad p_z(0)=\frac12,\quad p_z(i)=\frac1{2L}.
\tag{150.2}
$$

Use only the empty schedule with $w^z_{\varnothing}=1$ and that output
vector; every other complete $w,T$ entry is zero. This is one rational
$O$ and $N$ allocation on all words, with
$0<e_z<a_{L,z}=A_z<1$, and cap at most $e_z$.

**Proof.** It is one normalized vector on one empty schedule, so all
common-mass equations hold. At any zero-containing word the overlap with
its target is $(1-A_z)+1/(2L)$: $1-A_z<1/2$ and $1/(2L)\le A_z$.
Thus its TV is $1/2-1/(4L)\le e_z$, independently of its first-zero index
or later zero pattern. At $1^L$ the TV is $1/2=e_z$.
By the exact TV-row calculation this checks all rows simultaneously.
The strict inequalities also hold at $L=1$, where $A_z=3/4$.
No event-specific or word-specific allocation is mixed into the construction.
$\square$

**Proposition 150.3 (Explicit rational mixing retains noncontainment).**
Under Proposition 150.1's premise there is a rational full $N$ lift with

$$
0<e<a_L\le\cdots\le a_1<1
\tag{150.3}
$$

whose parameter point still lies outside $\Pi_{O,L}$.

**Proof.** With $g_z=g(x_z)-\beta$, take the explicit positive rational

$$
t=\frac{\delta}{2(\delta+|g_z|)},\qquad 0<t\le\frac12,
\qquad
(x,w,T)=(1-t)(x_v,w^v,T^v)+t(x_z,w^z,T^z).
\tag{150.4}
$$

All rows and equalities are affine in the entire extended lift, so all
remain valid. Its violated-row excess satisfies

$$
g(x)-\beta=(1-t)\delta+t g_z
 \ge\delta-t(\delta+|g_z|)=\delta/2>0.
\tag{150.5}
$$

Order is preserved, while $e>0$,
$a_L-e=(1-t)(a_{L,v}-e_v)+t/(4L)>0$, and $a_1<1$ because
$a_{1,v}\le1$ and $a_{1,z}<1$. Every parameter, mass and terminal entry
is rational. Mixing changes the starting head, cap and law; the result
is an existential normal form, not an exact-law conversion or a statement
that the original starting data are preserved. $\square$

## 151. Nonnegative integer event separation and its exact stopped maximum

**Proposition 151.1 (Nonnegative rational then integer normal).** At the
strict rational profile in Proposition 150.3 there is a nonzero
$y\in\mathbb Z_{\ge0}^{m_L}$ such that

$$
\Delta=y\cdot d(a,e)-B_{O,L}(y)>0.
\tag{151.1}
$$

**Proof.** $O$ infeasibility is $d=d(a,e)\notin U_{O,L}$.
For the nonempty closed convex set $U_{O,L}$ choose a nearest point $u$.
Existence follows by restricting a minimizing sequence to a sufficiently
large bounded closed ball and taking a subsequence. Put $\alpha=d-u\ne0$.
Minimizing squared distance along the segment from $u$ to any
$z\in U_{O,L}$ gives

$$
\alpha\cdot(z-u)\le0.
\tag{151.2}
$$

Taking $z=u-se_j$ for $s\ge0$ proves $\alpha_j\ge0$ for every row.
Downward closure and nonnegativity therefore give

$$
\sup_{z\in U_{O,L}}\alpha\cdot z
 =\max_{v\in R_{O,L}}\alpha\cdot v=\alpha\cdot u,
\qquad
\alpha\cdot d-\max_v\alpha\cdot v=\|\alpha\|^2>0.
\tag{151.3}
$$

The event image is compact, although its downward closure is not.
This is the repository's downward-closure separation mechanism of
Acquisition Resources, Theorem 84.3, applied to the complete stopped
catalog rather than an unrestricted adaptive catalog.

Write $\delta_\alpha=\|\alpha\|^2$ and choose
$0<\varepsilon<\delta_\alpha/(4m_L)$.
Approximate $\alpha$ within $\varepsilon$ in the infinity norm by one
nonnegative rational vector $\rho$. The nonnegative rational orthant is
dense in the nonnegative real orthant, including its zero-coordinate
boundaries. Here $d_j\in[-1,1]$ and every $v_j\in[0,1]$, so

$$
|(\rho-\alpha)\cdot(d-v)|\le2m_L\varepsilon
\quad\text{uniformly for }v\in R_{O,L}.
\tag{151.4}
$$

Consequently $\rho\cdot(d-v)>\delta_\alpha/2>0$ for every $v$.
Multiply $\rho$ by a common positive denominator to obtain a nonzero
nonnegative integer vector $y$. This preserves strict separation and
all signs. It does not assume an arbitrary nearest-point normal was
rational. Proposition 151.2 supplies exactly
$\max_{v\in R_{O,L}}y\cdot v=B_{O,L}(y)$ and hence (151.1).
The finite integer vector is indexed by the complete row system,
including every zero-weight row. $\square$

**Proposition 151.2 (Exact joint support and simultaneous attainment).**
For every $y\ge0$,

$$
\max_{v\in R_{O,L}}y\cdot v=B_{O,L}(y).
\tag{151.5}
$$

For integer $y$, the right side is an integer and is attained by one
complete deterministic stopped table on one schedule.

**Proof.** A complete allocation satisfies

$$
\begin{aligned}
\sum_jy_jp_{b_j}(E_j)
 &=\sum_{S,c,r}h^y_{S,c}(r)T_{S,c,r}\\
 &\le\sum_S w_S\sum_c\max_r h^y_{S,c}(r)
 \le B_{O,L}(y).
\end{aligned}
\tag{151.6}
$$

Choose one schedule attaining the outer maximum, put its weight one and
all other weights zero, and in each of its stopped cells choose a label
attaining the corresponding inner maximum. Put unit mass at that label
in that cell. The resulting complete predetermined table has mass one
in every cell and simultaneously attains every term in the support value.
It is valid on every word, with no label support mask. Thus the upper
bound is attained, proving (151.5). Integer weights yield integer $h$
and integer maxima. $\square$

If a complete $O$ allocation met the cap at the strict profile, its
weighted row lower bound would be $y\cdot d=B_{O,L}(y)+\Delta$,
contradicting (151.5). The exact support is for the full class, not a
collection of separately attainable event estimates.

## 152. Conditional rational strict-cap normal form on every actual tail

**Theorem 152.1 (General rational strict-cap separator normal form).** Fix
$L\ge1$. If $\Pi_{N,L}\not\subseteq\Pi_{O,L}$, there exist a rational
profile satisfying (150.3), a rational complete $N$ allocation, a nonzero
$y\in\mathbb Z_{\ge0}^{m_L}$ and a rational $\gamma>0$ such that the
allocation satisfies every closed-cap row at $e$, (151.1) holds, and for
every extension by a positive nonincreasing vanishing actual tail with
$a_{L+1}\le e$, there is an original one-common-seed $N_2$ witness at cap
$e$, while every original full-carrier arbitrary-address $O_2$ competitor
has error strictly greater than $e+\gamma$. In particular,

$$
\exists N\in\mathcal N_2:\ e_a(N)\le e,
\qquad
\forall O\in\mathcal O_2:\ e_a(O)>e+\gamma,
\qquad
\inf_{O\in\mathcal O_2}e_a(O)\ge e+\gamma.
\tag{152.1}
$$

All classes are exactly Definition 90.1's original hard-two classes.
The premise is failed parameter containment, not a discovered counterexample.

**Proof.** Propositions 150.1--150.3 give a strict rational full $N$ lift;
Propositions 151.1--151.2 give its integer separator. Put

$$
W=\sum_{j=0}^{m_L-1}y_j>0,\qquad
\gamma=\min\left\{\frac{\Delta}{2W},\frac{a_L-e}{2},\frac{1-e}{2}\right\},
\qquad s=e+\gamma.
\tag{152.2}
$$

Every entry is rational and positive, so $0<e<s<a_L$ and $s<1$.
All rows change at the larger cap by the same amount:
$d_j(a,s)=d_j(a,e)-\gamma$. Hence

$$
y\cdot d(a,s)-B_{O,L}(y)=\Delta-W\gamma\ge\Delta/2>0.
\tag{152.3}
$$

No complete stopped allocation meets the larger closed cap $s$.
The head and both active lengths remain $L$; no active-set boundary was
crossed in obtaining the margin.

Keep this head and choose any entire tail as in the statement. One explicit
wholly rational sequence is

$$
a_{L+j}=\frac e{j+1}\qquad(j\ge1).
\tag{152.4}
$$

Every other permitted positive monotone vanishing tail, rational or
irrational and including $a_{L+1}=e$, works with exactly the same head,
allocation, seed rule and $\gamma$. Together with (150.3) it is (140.2),
and at both caps $e,s$ its actual active length is exactly $L$.

Use (140.7) to obtain rational masses $q_{S,f}$ over entire schedule/table
pairs. A common denominator gives one finite categorical partition of
$U\in[0,1)$ into half-open intervals selecting $S,f$ before any replies.
This is one source-independent common seed for every actual $x$.
It adds no advice, source law, source label observation or independent
per-source terminal randomization. Query precisely the selected original
prime addresses in $S$ and hand off the original tape $\theta_{f(c)}$.
The rule has zero advice, at most two actual requests and finite measurable
handoff for every actual source and seed. Actual source and static answers
are exactly (140.1), and their pattern witnesses remain supplied by 35.2.

If $n(x)\le L$, all its low words, including all multiple-zero suffixes,
satisfy the complete finite rows at cap $e$. If $n(x)>L$, its low word is
$1^L$ and no mark beyond $L$ is emitted. The exact identity (110.9) gives

$$
\operatorname{TV}(p_{1^L},\lambda_x^a)
 =\max\{1-p_{1^L}(0),a_{n(x)}\}\le e.
\tag{152.5}
$$

The infinite positive tail is not truncated. The all-positive finite row
provides the base deficit, and every tail amplitude is at most $e$.
This constructs the original $N$ attainer relative to its selected laws.

Now suppose any original $O_2$ competitor, with arbitrary addresses and
arbitrary original tapes, had uniform error at most $s$.
The necessary $O$ direction of the already proved exact closed-cap
Theorem 110.2 would give a finite stopped cap-feasible allocation at $s$;
Theorem 109.1 identifies its stopped region with $\mathscr C_L$.
Its original repetitions where allowed, common seed and sourcewise
almost-sure finite handoff are handled by that supplier, not weakened
here to a low-address or finite-support class. Formula (152.3) excludes
every such allocation, a contradiction. Thus each original competitor
has error $>s$ and their infimum is $\ge s$. An infimum might be approached,
so no strict infimum inequality is inferred from the strict inequalities
for individual competitors.

The original consumer and its nonatomic $\mu_x$ remain fixed. The
constructed finite set of $B_1$ marks restricts only our $N$ witness;
its error against each $\mu_x$ is one and the consumer is unknown there,
as in 82.1. All cap and lower-bound conclusions concern the separately
selected $\lambda_x^a$. This completes the conditional original-source
normal form. $\square$

**Corollary 152.2 (Finite certificate completeness, with no supplied separator).**
For each fixed $L\ge1$, failed containment $\Pi_{N,L}\not\subseteq\Pi_{O,L}$
is equivalent to existence of the strict rational profile, rational full
$N$ allocation and nonnegative integer full-row score with $\Delta>0$
in Theorem 152.1.

**Proof.** The forward implication is the theorem. Conversely such an
allocation puts its parameter point in $\Pi_{N,L}$, and its strictly
violated exact full $O$ support inequality excludes that point from
$\Pi_{O,L}$. $\square$

An actual refutation must still supply a concrete $L$, every rational
head/cap coordinate, every mass and terminal entry of a complete feasible
$N$ lift, the full indexed integer $y$, and its exact support $B$ and
strict rational $\Delta$. None is asserted by the conditional proof.
It yields no uniform encoding-size bound, efficient search, integer
allocation, total-unimodularity result or first failing $L$.

**Proposition 152.3 ($L=0$ vacuity).** For $L=0$, both finite classes have
the same one-coordinate cap domain, $0\le e\le1$: their only label is zero
and the empty schedule emits it. Hence noncontainment is impossible.

**Proof.** There is one empty word and one label, with its single normalized
probability equal to one. Its sole row is $1\ge1-e$.
The two complete allocations and their parameter projections coincide.
The strict-head formulation is therefore intentionally for $L\ge1$.
For an original active-zero positive cap, immediate base output has tail
error $a_{n(x)}\le e$. Caps at least one are trivial feasibility as well.
$\square$

## 153. Reused suppliers, primary literature and the remaining obligation

**Definition 153.1 (Mathematical scope of reuse).** Definition 90.1 and
Proposition 90.2 supply the full original resource contract and same-seed
completion. Sections 108--110 supply the common probability-vector classes,
the exact criterion $c\ge H$ and both exact closed-cap transports with the
actual tail identity. Theorems 113.2 and 113.3 supply, respectively, the
necessary residual strip and its stopped complement. Theorem 117.2
supplies the all-$m$ second-head inequalities. These are ordinary suppliers
with their own stated hypotheses; none is promoted to kernel evidence.
Theorem 112.2 obstructs preservation of one $N$ law but permits a different
stopped law at the same cap. Theorem 148.1 is such cap-existence replacement.

$R1:a_3\le4e$ reuses the late-mark supplier 85.1/97.3;
$R3:a_2+2a_3+2a_4-1\le10e$ reuses 97.2/117.2 at $m=4$.
$R6:4a_2+9a_3+7a_4+9a_5-4\le52e$ retains the $C4$ attribution of Section 122.
$C3,C2$ and the previous $K$ cuts of Sections 130--137 are retained
supplier scalars. The different full-score arrays above are a self-contained
finite projection certificate, not newly claimed scalar results.
The added bounded result is complete necessity and sufficiency of all
cuts together, exhaustive closed geometry, full common stopped lifts and
their continuous original-source replacement. The general normal form
uses mature rational projection and separation and the repository's
84.3 downward-closure score mechanism on the complete stopped image.

**Proposition 153.2 (An excluded profile is not a separator).** The
profile $(a_1,a_2,a_3,a_4,a_5,e)=(17,17,17,9,9,5)/26$, with actual tail
$a_{5+j}=5/(26j)$, $j\ge1$, is excluded from $N$ itself.

**Proof.** It is positive, monotone and vanishing and has active length
five, with $a_6=e$. For row $R4$ the left side minus right side in
$3a_2+8a_3+6a_4+7a_5-45e\le3$ is $1/26$;
for row $R6$ the corresponding excess over 4 is also $1/26$.
Theorem 142.2 excludes every $N$ allocation, and Theorem 110.2 excludes
every original $N_2$ cap witness. Thus it demonstrates incompleteness of
a smaller old cut list, with no $N/O$ separation. $\square$

For positive-$\kappa_3$ profiles, raw saturated $J5\le9$ is not used.
As in Section 137, pair $(3,5)$ with $N$ labels
$(00,01,10,11)\mapsto(0,0,5,0)$ has $C3=14$ and $J5=10$.
The retained full cut $K5=C3+J5\le24$ gives
$J5\le9+(15-C3)$, with compensation coefficient one sharp for that fixed
score correction. This concerns the score, not unrestricted exact-law
stopped realizability.

**Definition 153.3 (Primary source boundaries).** The following sources
support the specified mature ingredients or delimit resource comparisons.
The particular 13-score/36-lift projection and the source-specific rational
normal-form composition are repo-derived ordinary deductions. Bounded
textual overlap and primary-source checks do not establish exhaustive
novelty, worldwide absence or literary priority.

| Primary source | Exact result or passage used | Boundary here |
| --- | --- | --- |
| Andreas Löhne and Benjamin Weißing, [*Equivalence between polyhedral projection, multiple objective linear programming and vector linear programming*, arXiv:1507.00228v5](https://arxiv.org/html/1507.00228v5), problem (PP), Theorem 3 | A feasible projection $Y=\{y:\exists x,\ Gx+Hy\ge h\}$ is represented by a multiple-objective LP using one added objective $(y,-\sum y)$ and a finite point/direction description. | Hidden variables here are full common-budget allocations and projected variables are head amplitudes/cap. Our polytopes are bounded. This framework does not supply the particular full $N/O$ inclusion or a request-resource theorem. |
| Jędrzej Kaniewski, Troy Lee and Ronald de Wolf, [*Query complexity in expectation*, arXiv:1411.7280v1](https://arxiv.org/html/1411.7280v1), Definition 8, Theorem 9 | Randomized scalar nonnegative-output expectation query complexity equals nonnegative literal degree; the query cost is maximal positive-weight root-to-leaf depth. | Worst-path depth relates to hard requests, but scalar coefficient normalization does not supply equal cell masses for jointly normalized vector outputs or an increasing first-zero-stop replacement at a TV cap. |
| Lisa Hellerstein, Devorah Kletenik, Naifeng Liu and R. Teal Witter, [*Adaptivity Gaps for the Stochastic Boolean Function Evaluation Problem*, arXiv:2208.03810v1](https://arxiv.org/html/2208.03810v1), abstract and introduction | The task uses independent random input-bit probabilities and expected testing costs. | Those stochastic objectives differ from uniform every-actual-source law error and a hard two-actual-request bound. Their gaps do not give a separator for the present classes. |
| Volker Kaibel, [*Basic Polyhedral Theory*, arXiv:1001.2161v1](https://arxiv.org/html/1001.2161v1), Theorems 2, 13, 15, 18 and Section 1.6 | Cramer's rule, full-rank active subsystems at vertices, vertex attainment for pointed polyhedra, and coordinate projection by Fourier-Motzkin elimination. | Our finite nonempty bounded rational systems, with affine equalities in both orientations, satisfy these conditions. Rationality and projection are reused; no source or probability-vector conversion is imported. |
| Stephen Boyd and Lieven Vandenberghe, [*Convex Optimization*](https://web.stanford.edu/~boyd/cvxbook/bv_cvxbook.pdf), Section 2.5.1, Example 2.20, printed page 49 | A point outside a nonempty closed convex set admits strict separation. | $U_{O,L}$ is closed and convex but unbounded. The explicit nearest-point proof above derives nonnegative normals from downward recession directions, without assuming compactness of $U_{O,L}$. |

**Definition 153.4 (Verification and the unresolved universal intersection).**
The finite certificate here comprises the 94 indexed TV rows, all 13
nonnegative full $N$ scores, 22 halfspaces, seven initial vertices,
15 complete clipping transitions, 225 common-active rank sets, 36 final
vertices, all 36 full 246-coordinate stopped lifts and the 306-coordinate
completion lookup. Laws and row slacks are reconstructed from these
primitive formulas and integers. Ordinary clipping, convexity and
conforming triangulation provide continuum proofs, not extrapolation from
sampled feasible parameters. The general rational normal form is an
ordinary quantified deduction, not a scan or an actual separator.
Neither unit has Lean/kernel verification, ingestion, coverage or freeze
status assigned by this text.

The fixed remaining obligation is to prove for every full original
positive monotone vanishing sequence and every positive closed cap

$$
\mathcal F_N(a,e)\ne\varnothing
\quad\Longrightarrow\quad
\mathcal F_N(a,e)\cap\mathscr C_L\ne\varnothing
\tag{153.1}
$$

at its actual active length, or to refute it with an original one-common-seed
$N_2$ attainer and a uniform lower certificate against every original
full-carrier arbitrary-address $O_2$ competitor. Theorem 148.1 settles
all original five-active profiles. Theorem 152.1 identifies a complete
rational strict-cap certificate whenever a fixed finite-length inclusion
fails, but supplies no such failure. Whole $L\ge6$ comparisons and any
actual full-class rational separator remain unproved. No $L=6$ candidate
is a premise of either unit. Finite bounded completion does not complete
the universal or persistent long-term goal.

## 追加锚（本行以下为增补区）

