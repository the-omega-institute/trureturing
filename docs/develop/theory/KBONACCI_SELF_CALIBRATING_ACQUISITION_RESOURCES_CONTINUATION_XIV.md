# KBONACCI self-calibrating acquisition resources XIV

## 229. Complete event coordinates and a single residual

**定义 229.1（Words, labels and complete tables）。** Fix $L\ge3$.
Write $\Omega_n=\{w\in\{0,1\}^L:w_1=\cdots=w_{n-1}=1,w_n=0\}$,
and $n(w)=n$ on $\Omega_n$. The label set is $J_L=\{0,1,\ldots,L\}$.
The complete catalogs contain every constant table $E_\ell$, every
singleton table with arbitrary labels on answers $0,1$, and, for every
$i<j$, every table

$$
N(i,j;a,b,c,d),\qquad O(i,j;a,c,d).
$$

The $N$ labels are in $00,01,10,11$ order. The $O$ labels are in
stopped-cell $0,10,11$ order: the second address is not requested after
the first answer zero. Every terminal label can be any member of $J_L$.
In particular, an earlier unqueried label is legal. The $N$ completion
of $O(i,j;a,c,d)$ is $N(i,j;a,a,c,d)$, which acquires both replies.
Reversing an $N$ pair permutes its information cells; a repeated address
has singleton information. These information identities do not exempt
any actual request from the hard request count.

For each $w\in\Omega_n$ the three independent event demands at $(b,e)$
are

$$
d_{w,0}=1-b_n-e,\qquad d_{w,n}=b_n-e,\qquad
d_{w,\{0,n\}}=1-e.
$$

At $1^L$ the demand on label zero is $1-e$. All
$3(2^L-1)+1$ rows remain, including multiple-zero words, zero-scored
rows and negative singleton demands. A probability vector $p_w$ has
distance from $(1-b_n)\delta_0+b_n\delta_n$ equal to

$$
\operatorname{TV}(p_w,(1-b_n)\delta_0+b_n\delta_n)
=\max\{1-b_n-p_w(0),\ b_n-p_w(n),\ 1-p_w(0)-p_w(n)\}.
$$

Consequently the independent union row cannot be discarded after
checking the two singleton rows.

**定义 229.2（Scores, anchor and signed quotient）。** A full score is
the nonnegative array $y=(A_w,C_w,P_w;T)$, with zero-word reward

$$
g_y(w,\ell)=A_w[\ell=0]+C_w[\ell=n(w)]
                         +P_w[\ell\in\{0,n(w)\}],
\qquad g_y(1^L,\ell)=T[\ell=0].
$$

Here $[\cdot]$ is an indicator. Take the legal anchor
$R=O(1,2;1,2,0)$ and $\alpha=(1,1,0,\ldots,0;0)$. Put

$$
\begin{aligned}
W(y)&=\sum_{n(w)\ge3}A_w+\sum_{n(w)\le2}C_w+\sum_wP_w+T,\\
B_{\mathcal C}(y)&=\max_{D\in\mathcal D_{\mathcal C}}
                              \sum_wg_y(w,D(w)),\\
\Delta_{\mathcal C}(y)&=B_{\mathcal C}(y)-W(y)\ge0,
\qquad \mathcal C\in\{N,O\},\\
\beta_n(y)&=\sum_{\Omega_n}(C_w-A_w),\qquad
K_y=\sum_w(A_w+C_w+P_w)+T,\\
Q(y)&=(\beta_1,\ldots,\beta_L;K_y).
\end{aligned}
$$

For an arbitrary signed $q=(\beta;K)$ define
$F_q(b,e)=\sum_n\beta_n(b_n-\alpha_n)-Ke$. The score is nonnegative;
the difference of two quotients need not be nonnegative. These
definitions use the complete score coordinates of
[VI, 198–199](KBONACCI_SELF_CALIBRATING_ACQUISITION_RESOURCES_CONTINUATION_VI.md#199-完整事件锥的有符号替代零成本闭包与剩余原始比较).

Let $z_D$ be the event vector of a complete table,
$r=z_R=d(\alpha)$, $h(b,e)=d(b,e)-r$, and
$G_{\mathcal C}=(z_D-r)_{D\in\mathcal D_{\mathcal C}}$. Then
$F_{Q(y)}=y\cdot h$ and
$\Delta_{\mathcal C}(y)=\max_D y\cdot(z_D-r)$.

**定义 229.3（Hull and feasible conic configurations）。** Use the closed
domain of VI, Theorem 198.5,

$$
\begin{aligned}
H_L=\{(b,e):{}&1\ge b_1\ge\cdots\ge b_L\ge e\ge0,\quad b_2=b_3,\\
&(L+1)e\le\sum_{n=3}^Lb_n,\quad
b_1+\sum_{n=3}^Lb_n-(L+1)e\le1\}.
\end{aligned}
$$

Write $H_N$ for those members with one complete configuration
$\lambda\ge0$ satisfying $G_N\lambda\ge h(b,e)$. Its mass
$M=\sum_D\lambda_D$ can be any finite nonnegative number. It is a
probability law only when normalized appropriately; $H_L$ membership
alone does not supply $\lambda$. Define $H_O$ by the same condition
with $G_O$ in place of $G_N$. Define

$$
\sigma_H(q)=\max_{(b,e)\in H_L}F_q(b,e),\qquad
P_H=\{q:\sigma_H(q)\le0\}.
$$

For clarity the complete vertex formula from 198.5 is retained as an
interface. Let $B=\beta_1+\beta_2$, $S_k=\sum_{j=1}^k\beta_j$,
and $\kappa=K-S_L$. The vertices are $o=0$, $p=(1,0,\ldots,0;0)$,
and, for $3\le k\le L$, $u_k$ with first $k$ entries $1/(k-1)$ and
remaining entries and $e$ zero, and $v_k$ with first $k$ entries one
and all remaining entries and $e$ equal to $(k-2)/(k+1)$. Their readings
are, respectively,

$$
-B,\quad-\beta_2,\quad
\frac{S_k}{k-1}-B,\quad
\frac{3S_k-(k-2)\kappa}{k+1}-B.
$$

**命题 229.4（The reused one-budget pairing）。** A certificate for $q$
consists of one full $V\ge0$ and one $\theta\in[0,1]$ with

$$
\Delta_N(V)+\theta\le1,\qquad
\sigma_H(q-Q(V))\le\theta.
$$

For the same $(b,e)\in H_N$ and the same complete feasible $\lambda$,

$$
F_q(b,e)\le V\cdot h(b,e)+\theta
\le V\cdot G_N\lambda+\theta
\le M\Delta_N(V)+\theta\le\max\{1,M\}.
$$

证明。 The first inequality evaluates the whole signed residual at
$(b,e)$. The second uses all row inequalities and $V\ge0$; the third
sums the same table configuration. If $M\ge1$, the last bound is
$M(1-\theta)+\theta\le M$; if $M\le1$ it is at most one. This is
the pairing in VI, 199.3–199.4, not a new duality statement. At
$\theta=1$ every nonzero zero-cost $V$ remains allowed. $\square$

## 230. A twenty-six-atom cut at arbitrary five late addresses

**定义 230.1（The seven-coordinate score）。** Let $A=0$. The following
table gives all nonzero correct weights, and the next gives all
nonzero union weights. Set $T=4$. Every unspecified coefficient is zero.

| Word | $C_w$ |
| --- | ---: |
| $1101000$ | 2 |
| $1101111$ | 2 |
| $1110000$ | 3 |
| $1110010$ | 2 |
| $1110110$ | 3 |
| $1111000$ | 5 |
| $1111011$ | 2 |
| $1111100$ | 3 |
| $1111101$ | 5 |
| $1111110$ | 8 |

| Word | $P_w$ |
| --- | ---: |
| $0101011$ | 1 |
| $0101100$ | 3 |
| $0110001$ | 2 |
| $0110010$ | 1 |
| $0110100$ | 1 |
| $0111000$ | 1 |
| $1001010$ | 2 |
| $1001100$ | 1 |
| $1001101$ | 1 |
| $1010100$ | 2 |
| $1010110$ | 2 |
| $1011001$ | 2 |
| $1011010$ | 1 |
| $1100001$ | 2 |
| $1100110$ | 2 |

There are ten correct atoms, fifteen union atoms and one terminal
atom. The correct class totals are $(0,0,4,8,7,8,8)$; the union
total is $24$. Denote this score by $D$.

**定理 230.2（Complete support and zero excess）。** The complete
supports satisfy

$$
W(D)=B_N(D)=B_O(D)=28,\qquad
Q(D)=(0,0,4,8,7,8,8;63).
$$

证明。 For a cell $E$ in any schedule partition, put

$$
P(E)=\sum_{w\in E}P_w,
\quad P_n(E)=\sum_{w\in E\cap\Omega_n}P_w,
\quad C_n(E)=\sum_{w\in E\cap\Omega_n}C_w.
$$

Its exact maximum over all eight labels is

$$
\max\left\{P(E)+4[1^7\in E],\
                  \max_{1\le n\le7}(P_n(E)+C_n(E))\right\}.
$$

Adding the coefficients of 230.1 in this formula gives the following
complete cell maxima. The singleton order is $0,1$; pair columns
are $00,01,10,11$ for $N$ and $0,10,11$ for $O$.

| Schedule | $N$ cell maxima | $O$ cell maxima |
| --- | --- | --- |
| empty | $(28)$ | $(28)$ |
| $1$ | $(9,19)$ | $(9,19)$ |
| $2$ | $(11,17)$ | $(11,17)$ |
| $3$ | $(12,16)$ | $(12,16)$ |
| $4$ | $(12,16)$ | $(12,16)$ |
| $5$ | $(12,16)$ | $(12,16)$ |
| $6$ | $(15,13)$ | $(15,13)$ |
| $7$ | $(16,12)$ | $(16,12)$ |
| $1,2$ | $(0,9,11,8)$ | $(9,11,8)$ |
| $1,3$ | $(4,5,8,11)$ | $(9,8,11)$ |
| $1,4$ | $(4,5,8,11)$ | $(9,8,11)$ |
| $1,5$ | $(5,4,7,12)$ | $(9,7,12)$ |
| $1,6$ | $(7,2,8,11)$ | $(9,8,11)$ |
| $1,7$ | $(6,3,10,9)$ | $(9,10,9)$ |
| $2,3$ | $(4,7,8,9)$ | $(11,8,9)$ |
| $2,4$ | $(4,7,8,9)$ | $(11,8,9)$ |
| $2,5$ | $(5,6,7,10)$ | $(11,7,10)$ |
| $2,6$ | $(6,5,9,8)$ | $(11,9,8)$ |
| $2,7$ | $(8,3,8,9)$ | $(11,8,9)$ |
| $3,4$ | $(4,8,8,8)$ | $(12,8,8)$ |
| $3,5$ | $(5,7,7,9)$ | $(12,7,9)$ |
| $3,6$ | $(7,5,8,8)$ | $(12,8,8)$ |
| $3,7$ | $(8,4,8,8)$ | $(12,8,8)$ |
| $4,5$ | $(5,7,7,9)$ | $(12,7,9)$ |
| $4,6$ | $(7,5,8,8)$ | $(12,8,8)$ |
| $4,7$ | $(8,4,8,8)$ | $(12,8,8)$ |
| $5,6$ | $(7,5,8,8)$ | $(12,8,8)$ |
| $5,7$ | $(5,7,11,5)$ | $(12,11,5)$ |
| $6,7$ | $(8,7,8,5)$ | $(15,8,5)$ |

This table is a finite addition proof: each entry is specified by
the preceding maximum formula and the full literal atom lists. For
example, at pair $12$, the $00$ cell has no atom, the $01$ cell has
union mass nine and no correct atom, the $10$ cell has union mass
eleven and no correct atom, and the $11$ cell has union mass four,
terminal mass four and largest correct total eight. Its maxima are
$0,9,11,8$; the merged first cell has maximum nine. Every displayed
schedule sum is $28$. The anchor attains $24+4=28$, and the class
totals give $K=35+24+4=63$. Thus both excesses are zero. $\square$

**定理 230.3（Arbitrary ordered-five-late cut）。** For every
$3\le j_1<\cdots<j_5\le L$ and every profile $(b,e)$ admitting
one complete finite conic configuration $\lambda\ge0$ with
$G_N\lambda\ge h(b,e)$ or $G_O\lambda\ge h(b,e)$,

$$
4b_{j_1}+8b_{j_2}+7b_{j_3}+8b_{j_4}+8b_{j_5}\le63e.
\tag{230.1}
$$

In particular this holds throughout $H_N$ and $H_O$; membership
in $H_L$ is not needed for this pairing inequality.

For either original resource class, an attainer at any positive closed
cap $\varepsilon$ for a positive nonincreasing vanishing sequence
$a$ necessarily satisfies

$$
4a_{j_1}+8a_{j_2}+7a_{j_3}+8a_{j_4}+8a_{j_5}
                                                   \le63\varepsilon.
\tag{230.2}
$$

There is no active-horizon assumption in (230.2).

证明。 Embed the seven coordinates of 230.1 at
$(1,2,j_1,\ldots,j_5)$, setting every intervening or later coordinate
to one on every scored zero word and placing $T$ at $1^L$. Labels
are mapped to their actual addresses. Any additional queried
coordinate is constant one on this score support; it reduces the
partition to a legal singleton or empty schedule. Any added label
has zero reward. Every low schedule embeds with its order preserved.
Thus the embedded score, denoted $D_J$, has both supports and anchor
equal to $28$, and quotient equal to the displayed five coefficients
at their actual labels, with $K=63$. The ambient demands still contain
every word and label; only the dual support is sparse.

For the same complete feasible configuration of any finite mass $M$,

$$
F_{Q(D_J)}(b,e)=D_J\cdot h(b,e)
\le D_J\cdot G_N\lambda\le M\Delta_N(D_J)=0.
$$

This proves (230.1). The same argument holds for complete $O$
configurations. A normalized finite cap-feasible kernel paired with
$D_J$ gives $24+4+\sum_r\gamma_r a_{j_r}-63\varepsilon\le28$,
which is (230.2).

For original competitors at $0<\varepsilon<1$, let
$L_a=\max(\{n:a_n>\varepsilon\}\cup\{0\})$.
Use the full-carrier, arbitrary-address necessary direction of
[I, Theorem 110.2](KBONACCI_SELF_CALIBRATING_ACQUISITION_RESOURCES_CONTINUATION.md#110-exact-closed-cap-transport-on-the-original-countable-source).
If $L_a\ge j_5$, pair its normalized complete finite kernel with
$D_J$. If $L_a<j_5$, extend that kernel to horizon $j_5$, ignoring
the new coordinates and outputting no new label. For a word whose
first zero is new, its observed prefix is positive, so its base mass
is at least $1-\varepsilon$; its correct demand is
$a_n-\varepsilon\le0$, and the base and independent union demands
are at most $1-\varepsilon$. Old first-zero demands and the positive
row are unchanged. This also covers $L_a=0,1,2$. Pair the resulting
normalized kernel. For $\varepsilon\ge1$, the left side is at most
$35\le63\varepsilon$. Original competitors are not restricted to
the displayed addresses, words, labels or tape marks. $\square$

## 231. An attained seven-equal family at every small amplitude

**定义 231.1（One fourteen-table law）。** For $0<t\le1/2$, give each
following stopped table mass $tk/9$, where $k$ is its last column.
Give $E_0$ mass $1-2t$.

| Schedule | Labels $0,10,11$ | $k$ |
| --- | --- | ---: |
| $1,2$ | $(0,2,0)$ | 2 |
| $1,2$ | $(0,2,7)$ | 1 |
| $1,3$ | $(1,3,0)$ | 2 |
| $1,4$ | $(1,4,0)$ | 1 |
| $1,5$ | $(1,5,0)$ | 1 |
| $2,3$ | $(0,3,0)$ | 2 |
| $2,4$ | $(0,4,0)$ | 1 |
| $2,5$ | $(2,5,0)$ | 1 |
| $3,4$ | $(0,4,0)$ | 1 |
| $3,4$ | $(0,4,6)$ | 1 |
| $3,5$ | $(0,5,0)$ | 1 |
| $4,5$ | $(0,5,0)$ | 1 |
| $4,6$ | $(0,6,7)$ | 1 |
| $5,6$ | $(0,6,7)$ | 2 |

The integer sum is $18$, so the total mass is one, including at
$t=1/2$. Each $N$ completion uses $(u,u,v,z)$ for the printed
stopped outputs $(u,v,z)$, with exactly the same table-selection seed.

**引理 231.2（Every word and every independent row）。** On every
seven-bit word of first zero $n$, the law in 231.1 has

$$
p_w(n)=4t/9,\qquad p_w(0)\ge1-t,\qquad
1-p_w(0)-p_w(n)\le5t/9.
$$

At the positive word $p_{1^7}(0)=1-5t/9$. Its TV error against
$(1-t)\delta_0+t\delta_n$ on each zero word is exactly $5t/9$.

证明。 Work first with the integer counts $k$ in 231.1, whose total
is $18$. Write $x=w_2$, $y=w_3$, $z=w_4$, $u=w_5$. Adding the
fourteen terminal indicators on each actual first-zero fiber gives
correct count four and the following wrong-positive counts:

$$
\begin{aligned}
E_1&=1+3x+3y+2z+2u-2xy-xz-xu-yz-yu-zu,\\
E_2&=4+y+z+u-yz-yu-zu,\\
E_3&=5-zu,\qquad E_4=4-u,\qquad
E_5=3,\quad E_6=1,\quad E_7=1.
\end{aligned}
$$

These are terminal-indicator identities, not assumptions on
unobserved replies. If $x+y=0,1,2$, respectively, $E_1$ becomes
$1+2z+2u-zu$, $4+z+u-zu$, or $5-zu$, with maxima $4,5,5$.
For $k=y+z+u\in\{0,1,2,3\}$,
$E_2=4+k-k(k-1)/2\le5$. All later expressions are at most five.
The integer base count is $14-E_n$ and the union count $18-E_n$;
their separate minima on each whole fiber are therefore

| $n$ | Base minimum | Correct count | Union minimum |
| ---: | ---: | ---: | ---: |
| 1 | 9 | 4 | 13 |
| 2 | 9 | 4 | 13 |
| 3 | 9 | 4 | 13 |
| 4 | 10 | 4 | 14 |
| 5 | 11 | 4 | 15 |
| 6 | 13 | 4 | 17 |
| 7 | 13 | 4 | 17 |

For general $t$, multiply these counts by $t/9$ and add $1-2t$
to the base and union coordinates. This gives the three inequalities
claimed, simultaneously on every word, and hence all $382$ rows
at $e=5t/9$. The correct discrepancy is exactly
$t-4t/9=5t/9$, so the TV maximum is equal to that value.
At the positive word the integer label counts $0,\ldots,7$ are
$(13,0,0,0,0,0,1,4)$, giving the stated base mass. $\square$

**定理 231.3（Sharp original family, all positive vanishing tails）。**
Let $0<t\le1/2$, and let $a$ be any actual sequence satisfying

$$
a_1=\cdots=a_7=t,\qquad
0<a_8\le5t/9,\qquad a_{n+1}\le a_n,\qquad a_n\longrightarrow0.
$$

For the separately selected marked targets on the original source
and carrier, both original hard-two resource classes have attained
optimal uniform TV error exactly $5t/9$. Equivalently, for every
positive closed cap $\varepsilon$, either class is feasible exactly
when $\varepsilon\ge5t/9$.

证明。 Use one source-independent seed to select the whole table
of 231.1 before replies. Its stopped execution observes only the
first six addresses and outputs only labels $0,\ldots,7$; its $N$
completion obtains the full selected pair and uses the same seed
and output. The original interpretation of these labels and resources
is specified in 236.1–236.3.

Every actual first zero at most seven has the finite word law in
231.2 and error exactly $5t/9$. Every actual first zero $n\ge8$
has positive replies on all observed addresses and no possible
output $n$. Its exact error is therefore

$$
\max\{1-p_{1^7}(0),a_n\}
=\max\{5t/9,a_n\}=5t/9.
$$

This includes every allowed tail and every equality $a_n=5t/9$;
it neither replaces the tail by zero nor introduces an infinite
positive source. At this cap the strict active length is exactly
seven, even though no table needs address seven.

Conversely, every original $N$ or $O$ attainer at a positive cap
$\varepsilon$ obeys 230.2 with $j_r=r+2$, hence
$35t\le63\varepsilon$. No error smaller than $5t/9$ is possible:
such an error would also meet some positive closed cap strictly
between it and $5t/9$, contradicting that bound. In particular a
zero-error attainer is excluded. The construction attains the lower
bound, for each of the two classes, with uniform all-source/all-Borel
error. No exact-law preservation is required of competing rules.
$\square$

## 232. The associated relative hull nonimplication

**定义 232.1（The earlier weighted family）。** For nonnegative weights
$\gamma_j$ on any finite late label set, let
$G=\sum_j\gamma_j$, $\mu=\max_j\gamma_j$, with both zero for
empty support. Order their values $g_1\ge\cdots\ge g_s\ge g_{s+1}=0$,
write $\delta_k=g_k-g_{k+1}$, and put

$$
c_1=2,\quad c_2=3,\quad
c_k=4-2/\lceil k/2\rceil\ (k\ge3),\qquad
\Lambda(\gamma)=\sum_{k=1}^s c_k\delta_k.
$$

The family of
[VI, Corollary 201.5](KBONACCI_SELF_CALIBRATING_ACQUISITION_RESOURCES_CONTINUATION_VI.md#201-共享终端的加权割覆盖补偿与单一完整预算)
is $\sum_{j\ge3}\gamma_j b_j\le(G+\Lambda+\mu)e$. Sorting
weights in this definition does not relabel their addresses.

**定理 232.2（Relative nonimplication and an attained boundary）。**
For every $L\ge7$, the point

$$
b_1=\cdots=b_7=1/2,\qquad b_8=\cdots=b_L=e=3/11
$$

belongs to $H_L$ and satisfies the entire family 232.1, but belongs
to neither $H_N$ nor $H_O$. On the other hand, for every
$0<t\le1/2$, the point with first seven entries $t$ and later
entries $e=5t/9$ belongs to both $H_N$ and $H_O$, with one normalized
configuration supplied by 231.1 and its same-seed completion.

证明。 At the first point the lower and upper nontrivial hull
conditions reduce to $8e\le5/2$ and $3-8e=9/11\le1$.
The new cut reads

$$
35/2-63(3/11)=7/22>0.
$$

The zero-excess pairing in 230.3 excludes every complete conic
configuration at every finite mass, in either class.

To check all weights on the five plateau late coordinates, note

$$
G=\sum_{k=1}^5k\delta_k,\qquad
G+\Lambda+\mu=\sum_{k=1}^5(k+c_k+1)\delta_k.
$$

The maximum of $k/(k+c_k+1)$ over $k=1,\ldots,5$ is $15/28$:
the five values are $1/4,1/3,3/7,1/2,15/28$.
Thus $(1/2)G\le(15/56)(G+\Lambda+\mu)$ and
$15/56<3/11$. For arbitrary weights also on later labels, remove
the later coordinates first. This cannot increase $\Lambda$ or
$\mu$, since every layer-set cardinality decreases and $c_k$ is
nondecreasing. Adding those weights back adds exactly $e$ times
their sum to the left side, adds that same amount through $G$ on
the right, and cannot decrease the remaining right-side terms.
Hence the full weighted family holds, including empty or zero
weights and arbitrary late supports.

For the attained point, all ordering conditions hold. The lower
condition is $8e\le5t$; the upper is
$6t-8e=14t/9\le7/9<1$. For first zeros at most seven, 231.2 gives
all demands. For later first zeros the law is the positive-word
law: base $1-e$, correct zero and union $1-e$, which meet
$1-2e,0,1-e$. The positive row holds too. Thus the same complete
mass-one stopped law and its $N$ completion provide the witnesses.
$\square$

The nonimplication is relative to $H_L$ and exactly the entire
weighted family 201.5. It does not assert independence from every
older semantic consequence. The first point is outside $H_N$;
it supplies no original same-realization separation. The cut,
the sharp family and this relative diagnostic form one subject.

## 233. One-measure simultaneous prefix pullback

**定义 233.1（A joint finite measure and two full scores）。** For an
integer $m\ge4$ put

$$
d_m=\frac{m(m-3)}2,\quad b_m=d_m-m+2,\quad
s_m=d_m+m-1,\quad t_m=d_m-1,
$$

and set $\gamma_1=0$, $\gamma_2=b_m$, $\gamma_3=d_m-1$,
$\gamma_n=d_m$ for $4\le n\le m$. Within this section write
$d,b,s,t$ for these four parameters. This $b_m$ is a score
coefficient, not the $m$-th coordinate of a hull point.

Define one measure $\mu_m$ with unit mass at every word $(x,0)$
such that $x\in\{0,1\}^{m-1}$ has Hamming weight one or two,
except for the singleton $x=(0,\ldots,0,1)$. This measure is a
deterministic dual score measure, not a distribution of original
sources or an acquisition law.

Both scores below have $A=0$, $P=\mu_m$, and $T=t$.
The score $Y_m$ puts correct mass $\gamma_n$ at the absorbing-chain
word $1^{n-1}0^{m-n+1}$ for each $n$.

For the simultaneous score $Z_m$, define

$$
E_n=\{w\in\operatorname{supp}\mu_m:n(w)<n,\ w_n=0\},
\quad c_n=\mu_m(E_n),\quad
\tau_n(w)=(1,\ldots,1,w_n,\ldots,w_m).
$$

For every $n$ with $\gamma_n>0$, put correct measure
$C^{(n)}=(\gamma_n/c_n)(\tau_n)_*(\mu_m|_{E_n})$ on first-zero
class $n$. For $\gamma_n=0$, put $C^{(n)}=0$ without division.
Add all coinciding coefficients. Keep the same $P,T$.
Thus $Z_m$ is one full score defined jointly from the same $\mu_m$
for all labels; it is not a collection of independently chosen
cell or label optimizers.

For every $L\ge m$, append $1^{L-m}$ to every scored zero word
and retain $T$ at $1^L$. Denote the scores by $Y_m^L,Z_m^L$.
All ambient zero-word demands and output labels are still present.

**引理 233.2（Exact counts and capacities, uniformly in $m$）。**
The total mass and first-zero masses of $\mu_m$ are

$$
\mu_m(\{0,1\}^m)=s,\qquad
(p_1,p_2,p_3,p_4,\ldots,p_m)=(d,m-2,1,0,\ldots,0).
$$

Its zero marginals are $d$ for $i\le m-2$, $d+1$ for $i=m-1$,
and $s$ for $i=m$. For $i<j<m$,

$$
\mu_m(10)=m-2,\qquad\mu_m(11)=1.
$$

For $i<j=m$, the $01,11$ masses vanish, and the $10$ mass is
$m-1$ if $i\le m-2$, and $m-2$ if $i=m-1$. All correct-row
densities in 233.1 satisfy $0\le\gamma_n/c_n\le1$ whenever used.

证明。 There are $(m-1)+\binom{m-1}{2}-1=s$ atoms. A first zero
at one leaves one or two ones among $m-2$ positions, with the
excluded singleton deleted, giving
$(m-2)+\binom{m-2}{2}-1=d$. A first zero at two requires bit one
and allows at most one additional one after bit two: this gives
$1+(m-3)=m-2$. A first zero at three requires the unique pair of
ones at positions one and two. Three initial ones are impossible.

For a nonterminal coordinate $i$, the singleton at $i$ and the
$m-2$ pairs containing $i$ give one-marginal $m-1$, except at
$i=m-1$ where the removed singleton lowers it to $m-2$.
Subtracting from $s$ gives the stated zero marginals. For
$i<j<m$, the unique pair $\{i,j\}$ gives $11$ mass one; the
singleton at $i$ is not the removed singleton, and together with
the $m-3$ pairs through $i$ excluding $j$ gives $10$ mass $m-2$.
The terminal bit is always zero, which gives its pair statements.

Since $w_n=0$ implies $n(w)\le n$,
$c_n=\mu_m(w_n=0)-p_n$. In particular

$$
c_1=0,\quad c_2=d-m+2=b,\quad c_3=d-1,\quad
c_n=d\ (4\le n\le m-2),\quad c_{m-1}=d+1-p_{m-1},\quad c_m=s.
$$

The displayed value $c_3=d-1$ applies for $m\ge5$; at $m=4$,
the overlapping terminal-predecessor case is $c_3=d=2\ge\gamma_3=1$.
Comparison with $\gamma$ proves every capacity assertion. Each
push resets exactly the prefix before its own zero and preserves
the terminal zero, so its first zero is $n$, its total is
$\gamma_n$, and it is nonnegative. The single counting argument
works for every integer $m\ge4$; no choice of a fixed $m$ or
different measure for different labels is involved. $\square$

**引理 233.3（Simultaneous all-label cell domination）。** Fix any
pair $i<j\le m$. For every numerical label $n\le i$ and every
one of its four cells $E$, the actual score $Z_m$ satisfies

$$
C_n(E)+P_n(E)\le\mu_m(E).
\tag{233.1}
$$

For every $n>i$, its complete numerical reward is supported on
$w_i=1$ and its total mass is $\gamma_n+p_n=d$.

证明。 If $\gamma_n=0$, the correct contribution is zero and
$P_n(E)\le\mu_m(E)$ directly, with no division by $c_n$.
For $\gamma_n>0$ and $n\le i$, resetting the bits strictly before $n$
changes neither queried bit. Thus

$$
C_n(E)=\frac{\gamma_n}{c_n}\mu_m(E\cap E_n)
\le\mu_m(E\cap E_n),\qquad
P_n(E)=\mu_m(E\cap\Omega_n).
$$

The two subsets on the right are disjoint, because their first
zeros are respectively before $n$ and at $n$. This proves (233.1)
for every cell and every such label at once, including earlier
unqueried labels. If $n>i$, both the unchanged $P_n$ words and
the reset $C_n$ words have $w_i=1$. Their class totals give
$\gamma_n+p_n=d$, also for $n=2,3$. No equality of marginal
laws has been substituted for this common realization. $\square$

## 234. Full supports of the uniform construction

**定理 234.1（Exact quotient and complete zero-cost supports）。**
For every $L\ge m\ge4$,

$$
\begin{aligned}
Q(Y_m^L)=Q(Z_m^L)&=q_m^L
 =(0,b_m,d_m-1,\underbrace{d_m,\ldots,d_m}_{4,\ldots,m},
                  0,\ldots,0;(m+1)d_m-1),\\
W(Y_m^L)=W(Z_m^L)&=3d_m,\\
B_O(Y_m^L)=B_N(Z_m^L)=B_O(Z_m^L)&=3d_m.
\end{aligned}
\tag{234.1}
$$

In particular $\Delta_O(Y_m^L)=\Delta_N(Z_m^L)
=\Delta_O(Z_m^L)=0$. For the input score at $m=5$,
$\Delta_N(Y_5^L)\ge2$; for every $m\ge6$,
$\Delta_N(Y_m^L)\ge m-2$.

证明。 First take $L=m$ and write $d=d_m$. In $Z_m$, for a pair
$i<j<m$, the label-zero maxima in the first two cells are their
$\mu_m$ masses. By 233.3 these dominate every numerical label:
labels $n\le i$ are bounded by the same masses, and labels $n>i$
give zero there. Their sum is $\mu_m(w_i=0)=d$. The $10$ maximum
is at most $\max(m-2,d)=d$, by the same lemma. The $11$ baseline
is $1+T=d$, and dominates every numerical reward, again by 233.3.
Thus every such complete $N$ pair support is at most $3d$.

If $j=m$, all nonterminal scored atoms have terminal bit zero.
The $01$ cell is empty and the $11$ cell contains only $T=d-1$.
The other two maxima have sum at most

$$
\mu_m(w_i=0)+\max\{\mu_m(w_i=1),d\}.
$$

For $i\le m-2$, the whole support is at most
$d+\max(m-1,d)+d-1\le3d$, using $m-1\le d+1$.
For $i=m-1$, it is at most
$d+1+\max(m-2,d)+d-1=3d$.
Empty and singleton information coarsen some distinct $N$ pair,
so their maxima are also at most $3d$. Reversal and repetition
introduce no larger information support.

For $Y_m$, every numerical label has total $C_n+P_n=d$,
including label one, whose total comes entirely from $P$.
For an increasing pair $i<j<m$, its chain correct classes
$n\le i$, $i<n\le j$ and $n>j$ lie respectively in the stopped
cells $0,10,11$. The first baseline is $d$ and dominates every
numerical reward; the middle baseline is $m-2\le d$ and every
numerical reward is at most $d$; the last baseline is $1+T=d$
and dominates every numerical reward. Its support is at most
$3d$. At $j=m$, only $T$ is in the last cell, and the first and
middle maxima have exactly the same upper bounds just used for
the terminal $Z_m$ pair, since every numerical total is $d$.

The complete short stopped schedules require no refinement
assumption. For the empty schedule the zero baseline is
$s+t=2d+m-2\le3d$, and each numerical total is $d$.
For a singleton $i<m$, its zero-cell maximum is
$\mu_m(w_i=0)$, which is either $d$ or $d+1$ and dominates
each numerical total. Its one-cell maximum is at most
$\max\{\mu_m(w_i=1)+t,d\}$. If $i\le m-2$, their sum is
$d+\max(d+m-2,d)=2d+m-2\le3d$; if $i=m-1$, it is at most
$d+1+\max(d+m-3,d)\le3d$, using $m-2\le d$ and $d\ge1$.
For singleton $m$, the sum is $\max(s,d)+t=s+t\le3d$.
Thus the whole stopped catalog is bounded, including singleton
$m$, which need not refine an increasing two-address stop.

The anchor reward of both scores is
$s+b+t=(d+m-1)+(d-m+2)+(d-1)=3d$.
It attains every asserted global support, since it is in both
catalogs and $O\subseteq N$. The correct totals give
$\beta=\gamma$, and direct summation gives
$K=s+\sum_n\gamma_n+t=(m+1)d-1$.

For the diagnostic $N$ pair $34$ in $Y_m$ at $m\ge5$, the four
exact cell maxima are $(d,u,d,d)$, where $u=2$ for $m=5$
and $u=m-2$ for $m\ge6$. In $00$, correct label three has
$C_3=d-1$ and the first-zero-three union atom contributes one.
In $01$ there is no chain correct atom and its union baseline
is $u$: the removed singleton is in this cell precisely when
$m=5$. In $10$ the chain correct label four attains $d$.
In $11$ the zero baseline $T+\mu_m(11)=d$ attains $d$.
Every numerical total is at most $d$, so these are indeed the
cell maxima. Their sum is $3d+u$.

For every $L>m$, all added coordinates equal one on the full
score support, and added labels have zero reward. Any table
using an added coordinate reduces there to legal low singleton,
empty or pair information, preserving stopped order when relevant.
Every low table embeds. Thus all supports, quotients, anchors and
the lower diagnostic persist simultaneously for every $L\ge m$.
This is a dual support argument; it removes none of the ambient
event rows and restricts no original competitor. $\square$

**定理 234.2（Exact full hull support）。** For every $L\ge m\ge4$,

$$
\sigma_{H_L}(q_m^L)=m-3.
\tag{234.2}
$$

证明。 Write $d=d_m$, $b=b_m$. The quotient prefix sums and
terminal difference are

$$
S_k=(k-1)d-m+1\ (3\le k\le m),\qquad
S_k=S_m\ (k>m),\qquad \kappa=2d+m-2.
$$

The complete hull readings 229.3 at $o,p$ are both $-b$;
for $3\le k\le m$ they are

$$
F(u_k)=m-2-\frac{m-1}{k-1},\qquad
F(v_k)=-\frac3{k+1}.
$$

The first sequence increases to $m-3$ at $k=m$. Beyond $m$,
$S_m>0$ is constant, so the $u_k$ readings decrease. The
successive differences of the $v_k$ readings are
$-3K/((k+1)(k+2))<0$. All vertices have therefore been checked,
and $u_m$ attains the claimed maximum. $\square$

Thus for $m\ge5$, $V=Y_m^L$ and $V=0$ each fail the unit-budget
test for these inputs, while the actual score $V=Z_m^L$ has zero cost
and zero residual. These are diagnostics of two choices of
certificate. They do not obstruct the unrestricted certificate.

## 235. Joint signed cone, free extension, cuts and prefix hierarchy

**定理 235.1（One coefficient vector and one whole signed residual）。**
At a fixed $L\ge4$, choose one nonnegative vector
$(a_m)_{4\le m\le L}$ and any signed target $q$. Put

$$
V=\sum_{m=4}^L a_mZ_m^L,\qquad
r_q=q-\sum_{m=4}^L a_mq_m^L,\qquad
\theta=\max\{0,\sigma_H(r_q)\}.
$$

If $\theta\le1$, then $(V,\theta)$ is one full certificate.
Writing $r_q=(\eta;K_r)$, $B_r=\eta_1+\eta_2$,
$S_{r,k}=\sum_{n\le k}\eta_n$, $\kappa_r=K_r-S_{r,L}$,
the condition is the single finite system

$$
\begin{gathered}
0\le\theta\le1,\qquad -B_r\le\theta,\quad-\eta_2\le\theta,\\
\frac{S_{r,k}}{k-1}-B_r\le\theta,\qquad
\frac{3S_{r,k}-(k-2)\kappa_r}{k+1}-B_r\le\theta
\quad(3\le k\le L).
\end{gathered}
\tag{235.1}
$$

Existence of this one vector with (235.1) is exact for certificates
whose output score lies in the displayed cone. It is only a
sufficient condition for unrestricted certificates.

证明。 Subadditivity of complete support and linearity of the
anchor give $\Delta_N(V)\le\sum_ma_m\Delta_N(Z_m^L)=0$;
the anchor gives the reverse inequality. Linearity gives
$Q(V)=\sum_ma_mq_m^L$. The full vertex formula then gives
exactly (235.1) for the same $a_m$ in every row. All cancellations
are made before taking this single maximum. Conversely every
score in this cone is represented by one such vector and has
these same residual inequalities. Neither optimizing different
vertices with different vectors nor adding separately optimized
residual charges gives this statement. $\square$

**推论 235.2（Free additive extension of any existing certificate）。**
If a full $y\ge0$ has $\Delta_O(y)\le1$ and any unrestricted
certificate $(V_0,\theta_0)$, then for every one vector $a_m\ge0$,

$$
y'=y+\sum_{m=4}^La_mY_m^L,\qquad
V'=V_0+\sum_{m=4}^La_mZ_m^L
$$

satisfy $\Delta_O(y')\le1$, $\Delta_N(V')\le\Delta_N(V_0)$,
and $Q(y')-Q(V')=Q(y)-Q(V_0)$. The same $\theta_0$ works,
including $\theta_0=1$ and nonzero zero-cost $V_0$.

证明。 Apply the exact zero-cost and exact quotient identities of
234.1 and support subadditivity to these actual combined scores.
This is the zero-cost addition principle of VI, 199.6 applied to
the explicit uniform family; it supplies no new generic closure
principle and imposes no preserved baseline, unary or exact law
on the original unrestricted problem. $\square$

**定理 235.3（Necessary cuts from the same complete configuration）。**
For every $L\ge m\ge4$ and $(b,e)\in H_N$,

$$
F_{q_m^L}(b,e)\le0.
\tag{235.2}
$$

For an original $N$ cap attainer at actual active length $L_a\ge m$,

$$
b_m a_2+(d_m-1)a_3+d_m\sum_{n=4}^ma_n
              \le b_m+[(m+1)d_m-1]\varepsilon.
\tag{235.3}
$$

The same necessary bound holds for original $O$ attainers. Here
$b_m=d_m-m+2$ in both occurrences is the coefficient of 233.1.

证明。 For the same full feasible $\lambda$ at the same $(b,e)$,

$$
F_{q_m^L}(b,e)=Z_m^L\cdot h(b,e)
\le Z_m^L\cdot G_N\lambda\le M\Delta_N(Z_m^L)=0.
$$

The mass may be any finite $M$; no normalization is used here.
For the original statement use I, 110.2 at the stated actual
active length and pair its normalized complete event vector with
$Z_m^{L_a}$. The demand reward is
$s_m+t_m+\sum_n\gamma_na_n-[(m+1)d_m-1]\varepsilon$,
whereas the support is $s_m+t_m+b_m$. Rearranging gives (235.3).
Every independent union row is paid by its own $P$ weight. The
transport preserves arbitrary original addresses and full-carrier
outputs. These are necessary cuts, not a sufficiency theorem or
a seven-active classification. $\square$

**定义 235.4（The proper-prefix comparison family）。** For use only
in the relative cone comparison, define for each $k\ge4$

$$
d_k=k(k-3)/2,\quad b_k=d_k-k+2,\qquad
q_k^L=(0,b_k,d_k-1,d_k,\ldots,d_k,0,\ldots,0;(k+1)d_k-1),
$$

with $d_k$ in positions $4,\ldots,k$. The members at $k=4,5,6$
are reused members, not additional new constructions. Their
correspondence is given in 236.4.

**定理 235.5（Proper-prefix ordered hierarchy）。** For every $m\ge5$,

$$
q_m^m\notin\operatorname{cone}\{q_k^m:4\le k<m\}+P_{H_m}.
\tag{235.4}
$$

证明。 Set

$$
a=\frac{m+4}{4m-2},\qquad e=\frac{m-2}{4m-2},\qquad
b^*=(a,\ldots,a;e)\in\mathbb R^{m+1}.
$$

All order conditions hold and

$$
(m-1)a-(m+1)e=1,\qquad
(m-2)a-(m+1)e=\frac{3(m-2)}{4m-2}\ge0,
$$

so $b^*\in H_m$. Direct substitution of every prefix quotient,
with zeros after $k$, gives

$$
F_{q_k^m}(b^*)
=-\frac{3(k^2-4k+2)(m-k-1)}{4m-2}
\qquad(4\le k\le m).
\tag{235.5}
$$

For proper prefixes this is nonpositive, including zero at $k=m-1$;
for $k=m$ it is strictly positive. Every nonnegative combination
of the former readings plus any $P_{H_m}$ reading is nonpositive,
which proves (235.4). Its own actual zero-cost score $Z_m$ and
235.3 show that $b^*\notin H_N$, at every conic mass. Thus it
is a relative cone witness, never a same-$b$ original separator.
The comparison concerns exactly these proper-prefix directions
and $P_{H_m}$, not all earlier suppliers or their semantic closure.
$\square$

## 236. Original source, resources, closed tails and applicability

**定义 236.1（Actual labeled source and unchanged carrier）。** Retain
the source of I, 110.1 and the resource contract of 90.1:

$$
\begin{gathered}
F_0=0,\quad F_1=1,\quad F_{r+2}=F_{r+1}+F_r,\\
X=\{(r,g):r\text{ prime},\ g\in\mathbb Z,\
       \lceil F_r/10\rceil\le g\le\lfloor F_r/5\rfloor\},\\
N_x=1+F_rg,\quad q_i(x)=[p_i\mid N_x],\quad
n(x)=\min\{i:q_i(x)=0\}.
\end{gathered}
$$

The $p_i$ enumerate primes increasingly. Replies are static and
the actual first absence is finite. No probability distribution
on $X$ or infinite all-positive source is introduced.

The tape space is the full Borel disjoint union
$\mathcal T=\bigsqcup_{j\ge1}B_j\sqcup\bigsqcup_{j\ge1}P_j$,
each block a copy of $(0,1)$. The original consumer is unknown
on $B_j$ and proposes $j$ on $P_j$; it still runs on the same
actual source and delivered original tape. The original nonatomic
target remains

$$
\mu_x=(1-h_0)\nu_x+h_0\pi_{\omega(N_x)},\qquad
\frac{d\nu_x}{du}\bigg|_{B_{n(x)}}=
 \frac{e^{t(x)u}}{Z_{t(x)}},\qquad
t(x)=\sum_{i\ge1}3^{-i}q_i(x),\quad
Z_t=\int_0^1e^{tu}\,du,
$$

where $h_0\in(0,1)$ is the fixed original mixture parameter,
$\omega(N_x)$ is the number of distinct prime factors, and
$\pi_j$ is uniform on $P_j$. These targets and the consumer
are not modified by the constructions in this volume.

Separately choose the original tape marks
$\theta_j=(B_1,1/(j+2))$, $j\ge0$, and the marked targets

$$
\lambda_x^a=(1-a_{n(x)})\delta_{\theta_0}
                  +a_{n(x)}\delta_{\theta_{n(x)}},\qquad
1\ge a_1\ge a_2\ge\cdots>0,\quad a_n\longrightarrow0.
$$

Every accuracy claim in 231.3 concerns these separately selected
marked targets. A finite marked law has TV distance one from the
unchanged nonatomic $\mu_x$: its finite support has marked-law
mass one and $\mu_x$ mass zero. A score measure such as $\mu_m$
is neither of these two target families.

**命题 236.2（One common seed and two actual requests）。** Every
finite normalized table law displayed here defines an original
rule by one source-independent $U\sim\operatorname{Unif}[0,1)$.
Enumerate its complete tables $D$ and partition $[0,1)$ into fixed
half-open intervals of their masses. Before any replies, $U$
selects the whole table, its entire schedule and all terminal
outputs; output label $j$ means the actual tape $\theta_j$.
The stopped rule follows the increasing preselected schedule until
its first queried zero or exhaustion. The nonadaptive completion
acquires the complete preselected schedule and ignores any reply
not needed by the stopped table, using the same $U$ and output.

证明。 Interval lengths sum to one; zero masses have empty
intervals. A selected table is a deterministic measurable rule
with at most two requests. Finite schedules and finitely many
terminal outputs give a measurable finite handoff for every source
and seed in these constructions. On the first-zero cell the
completion outputs the same label in both $00,01$ cells, so it
agrees pointwise with the stopped rule. The ignored second reply
is nevertheless actually acquired and counted. Advice is zero,
and there is only this one common random seed, shared across all
sources. $\square$

The hard bound counts all actual requests, including repetitions
and ignored replies. It is not a bound on address, depth, runtime
or mean count. Original competitors retain arbitrary addresses,
the full carrier, and sourcewise almost-sure finite handoff. They
receive no source label, source prior, first absence, adaptive
second address, free probe or extra seed.

**命题 236.3（Full-source necessity and exact closed tails）。** The
necessary directions in 230.3 and 235.3 use the full original
feasibility transport I, 110.2, not an exact-law transport or a
restriction of original competitors. In that transport the
finite-pattern source supplier includes arbitrary finite
addresses fixed before the seed. In particular every multiple-zero
word used by the score or event demands has an actual source
witness. The original CRT/Fibonacci-window construction of
[Boundaries, 35.2](KBONACCI_SELF_CALIBRATING_BOUNDARIES.md#35-exact-finite-divisibility-fibres-in-canonical-fibonacci-windows)
is reused through 110.1–110.2.

证明。 The necessary transport first projects arbitrary
full-carrier outputs measurably onto marks without worsening
the selected-target cap. Countability of the labeled source
gives one common conull event for sourcewise finite handoff.
Cutting off the maximum address of the same whole preselected
schedule controls both requests together. Actual finite-pattern
witnesses, chosen before seeds, and finite-family handoff cutoffs
then give approximate finite catalog laws. The finite catalog
simplex is compact; its closed row constraints survive the limit
at the original cap. These are the ingredients of the complete
110.2 proof, and they preserve both resource classes. They do
not assert preservation of every original output law or runtime.

For a displayed law observing only addresses at most $H$ and
using labels $0,\ldots,H$, every actual first zero $n>H$ has
the same positive-word law and exact error

$$
\operatorname{TV}(p_x,\lambda_x^a)
=\max\{1-p_{1^H}(0),a_n\}.
$$

More generally, low output support alone gives
$\max\{1-p_x(0),a_n\}$ on each actual tail source. Replacing
$p_x$ by a common positive-word vector requires the additional
low-observation and seed/reply-only hypotheses, which hold for
231.1. Equality $a_n=\varepsilon$ is legal; the active length
is always the strict threshold
$\max(\{n:a_n>\varepsilon\}\cup\{0\})$.
No zero tail or infinite positive source is substituted. All
claims use the supremum over every actual source and every Borel
event, with small active lengths zero, one and two retained in
the original comparison. $\square$

The legal earlier-output control is literal: at word $0100$,
$N(3,4;1,0,0,0)$ outputs earlier unqueried label one. The actual
source $(r,g)=(19,436)$ has $N_x=1822917$ and realizes this
prefix. The base/correct/union vector is $(0,1,1)$; replacing
that output by zero gives $(1,0,1)$. Neither catalog nor the
all-label proof 233.3 prunes this output.

**注记 236.4（Reused members and precise intersections）。** The
uniform construction and hierarchy in 233–235 include every
$m\ge7$ with one parameterized proof. The members at $m=4,5,6$
are included for compatibility and receive zero repeated credit:
$q_4=(0,0,1,2;9)$ is a base member,
$q_5=(0,2,4,5,5;29)$ is already
[XI, 213.16](KBONACCI_SELF_CALIBRATING_ACQUISITION_RESOURCES_CONTINUATION_XI.md#213-terminal-normalization-coupled-reward-fibers-and-full-score-minima),
and $q_6=(0,5,8,9,9,9;62)$ is the coefficient direction in
[III, 156–157, row 54](KBONACCI_SELF_CALIBRATING_ACQUISITION_RESOURCES_CONTINUATION_III.md#156-sixty-five-full-class-event-scores).
The latter has anchor and full $N/O$ support $27$ and necessary
inequality $5a_2+8a_3+9a_4+9a_5+9a_6-62e\le5$.
No separate contribution is attached to those old members.

The parameters and count formulas of 233.1–233.2 extend to
$m=5,6$ with $c_{m-1}=d+1-p_{m-1}$; for the base $m=4$,
$c_3=2\ge\gamma_3=1$ and $c_1=\gamma_1=0$ involves no division.
Those boundary checks only identify the old members. The proper-prefix
proof includes all of them and gives no new individual credit to
their inequalities or zero-cost availability.

Generic hull geometry, full LP alternatives, duality and zero-cost
closure are VI, 198.5 and 199.3–199.6. Unit plateau existence
and triple laws are 87, 176 and 200.4; the whole normalized
unit-$O$ face is XIII, 224. None is a new assertion here. In
particular the seven-unit plateau has cap $5/8$, whose radial
mixture with $E_0$ gives $5t/8$, not the $5t/9$ law of 231.1.
The normalized equality-face hypotheses do not apply to
$a_1=\cdots=a_7=t<1$. The five- and six-active comparisons
148 and 161 retain their original scopes and do not classify
the present seven-active family.

The early-$P$ and half-density hypotheses of VII, 205.12–205.13
are not hypotheses of 233: here $P$ has first-zero-three mass
one and some reset densities equal one. The high-terminal
early-$P$ construction XI, 213.11 does not directly apply to
the terminal $t_m=d_m-1<\max_n\gamma_n=d_m$ used here.
These are comparisons of explicit hypotheses, not a claim of
exclusion from every older signed or conic consequence or of
worldwide priority. The derivations are ordinary finite score
and probability mathematics. Standard support subadditivity
and weak duality have no additional mathematical credit.

**开放问题 236.5（The unrestricted original comparison）。** It remains
open to prove, for every $L\ge3$ and every actual full $y\ge0$
with $\Delta_O(y)\le1$, existence of one unrestricted full
$V\ge0$ and one $\theta\in[0,1]$ satisfying

$$
\Delta_N(V)+\theta\le1,\qquad
\sigma_{H_L}(Q(y)-Q(V))\le\theta.
$$

No fixed anchor preservation, fixed unary profile, fixed quotient,
exact law, positive residual or membership in 235.1's cone is
imposed on this obligation. Nonzero zero-cost scores at
$\theta=1$ remain allowed.

The negative alternative requires the same actual $(b,e)\in H_N$,
one complete feasible $\lambda\ge0$ with $G_N\lambda\ge h(b,e)$
and mass $M\ge1$, and an actual unit-$O$ input $y$ with the
strict inequality $F_{Q(y)}(b,e)>M$. It further requires an
original common-seed $N_2$ attainer and a uniform lower bound
against every original arbitrary-address full-carrier $O_2$
competitor, retaining all actual positive vanishing tails and
positive closed caps. The hull points excluded from $H_N$ in
232.2 and 235.5 do not meet these conditions.

The sharp family 231.3 and the uniform construction 233–235
do not settle either alternative. Constructor failure, a
detector outside $H_N$, exact-law failure or finitely many
instances are not original separation. The original implication
for every positive monotone vanishing sequence and every
positive closed cap remains unclassified outside the stated
scopes.

## 追加锚（本行以下为增补区）
