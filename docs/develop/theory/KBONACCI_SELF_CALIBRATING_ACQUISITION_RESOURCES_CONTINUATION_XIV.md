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

## 237. Full-event conventions for coupled seven-coordinate laws

**Definition 237.1 (Complete rows and one common allocation).**
For $L\ge3$, words are literal reply vectors $w\in\{0,1\}^L$;
$0$ is a zero answer, $n(w)$ is the first zero, and $w_+=1^L$.
Every multiple-zero word is included. Write $\Omega_n=\{w:n(w)=n\}$.
Labels are all of $0,\ldots,L$, including earlier and unqueried labels.
A probability kernel $p_w$ meets a cap $e$ for amplitudes $a$ exactly when

$$
p_w(0)\ge1-a_n-e,\qquad p_w(n)\ge a_n-e,\qquad
p_w(0)+p_w(n)\ge1-e\quad(w\in\Omega_n),\qquad p_+(0)\ge1-e.
\tag{237.1}
$$

These are three independent rows, including negative singleton demands.
Indeed the total common mass of $p_w$ and $(1-a_n)e_0+a_ne_n$ is
$\min(p_w(0),1-a_n)+\min(p_w(n),a_n)$, so their TV distance is

$$
\max\{1-a_n-p_w(0),\ a_n-p_w(n),\ 1-p_w(0)-p_w(n)\}.
\tag{237.2}
$$

There are $3(2^L-1)+1$ rows. In particular there are 382 at $L=7$.
No row is removed when its score coefficient is zero.

A full nonnegative score has independent coefficients $A_w,C_w,P_w,T$,
with rewards

$$
g_V(w,\ell)=A_w[\ell=0]+C_w[\ell=n(w)]+P_w[\ell\in\{0,n(w)\}],
\qquad g_V(w_+,\ell)=T[\ell=0].
$$

The full N catalog includes empty schedules, singletons and all pairs;
a distinct pair $i<j$ has cells $00,01,10,11$. The O catalog uses
increasing preselected pairs with cells $0,10,11$. An O table
$(i,j;x,y,z)$ has those three outputs; its N completion has outputs
$(x,x,y,z)$. N reversals permute cells and repeats give singleton
information. Actual repeated or ignored requests still count.
For either catalog, $B_{\mathcal C}(V)$ is the maximum reward over
all its deterministic tables. Thus for any schedule with cells $E$ its
optimized reward is the sum of

$$
\max_{0\le\ell\le L}\sum_{w\in E}g_V(w,\ell).
\tag{237.3}
$$

The maximum includes every label, separately in each cell; it bounds
every whole table without postulating a probability law from those maxima.
Set

$$
\begin{aligned}
R&=(1,2;1,2,0),&\alpha&=(1,1,0,\ldots,0),\\
W_V&=\sum_{n\ge3}A_w+\sum_{n\le2}C_w+\sum_wP_w+T,
&\Delta_{\mathcal C}(V)&=B_{\mathcal C}(V)-W_V,\\
\beta_n&=\sum_{\Omega_n}(C_w-A_w),&K&=\sum_w(A_w+C_w+P_w)+T.
\end{aligned}
$$

The summation conditions on $A_w,C_w$ refer to $n(w)$.
Write $Q(V)=(\beta,K)$ and
$F_q(b,e)=\sum_n\beta_n(b_n-\alpha_n)-Ke$.
The anchor gives $0\le\Delta_O\le\Delta_N$.
The inherited hull and its actual feasible subdomain are

$$
\begin{aligned}
H_L=\{(b,e):&1\ge b_1\ge\cdots\ge b_L\ge e\ge0,\ b_2=b_3,\\
 &(L+1)e\le\sum_{n\ge3}b_n,\quad
 b_1+\sum_{n\ge3}b_n-(L+1)e\le1\},\\
H_N=\{(b,e)\in H_L:&\exists\lambda\ge0,\ G_N\lambda\ge h(b,e)\}.
\end{aligned}
\tag{237.4}
$$

Here $d$ is the full demand vector in (237.1), $r=z_R=d(\alpha,0)$,
$h=d-r$, and $G_N=(z_D-r)_D$ on whole full N tables. A conic
configuration $\lambda$ has mass $M=\sum_D\lambda_D$, which need
not be one. For the same full $\lambda$ and a full score,

$$
F_{Q(V)}(b,e)=V\cdot h\le V\cdot G_N\lambda\le M\Delta_N(V).
\tag{237.5}
$$

The vector inequality precedes score pairing, so it retains all rows.
In particular a zero-cost score gives a necessary cut for every mass.
If one unrestricted $V\ge0$ and one signed residual satisfy

$$
0\le\theta\le1,\qquad \Delta_N(V)+\theta\le1,\qquad
\sigma_{H_L}(q-Q(V))\le\theta,
\tag{237.6}
$$

then this same allocation gives
$F_q(b,e)\le M\Delta_N(V)+\theta\le\max(1,M)$.
The residual is paid once; $\theta=1$ permits nonzero zero-cost $V$.
These are the interfaces of §§198–199 and §229, reused here.

For clarity, their complete signed vertex test is also fixed here.
Put $B=\beta_1+\beta_2$, $S_k=\sum_{n\le k}\beta_n$,
$\kappa=K-S_L$. The vertices are $o=(0,\ldots,0;0)$,
$p=(1,0,\ldots,0;0)$, and, for $3\le k\le L$,
$u_k$ with first $k$ entries $1/(k-1)$ and remaining entries zero,
and $v_k$ with first $k$ entries one, remaining entries and cap
$(k-2)/(k+1)$. The cap at $u_k$ is zero. Consequently

$$
\begin{aligned}
F_q(o)&=-B,&F_q(p)&=-\beta_2,\\
F_q(u_k)&=S_k/(k-1)-B,&
F_q(v_k)&=\frac{3S_k-(k-2)\kappa}{k+1}-B.
\end{aligned}
\tag{237.7}
$$

The maximum of all these signed values is $\sigma_{H_L}(q)$;
it is not clipped to zero. Hull vertices alone do not establish $H_N$.

**Definition 237.2 (Whole-table terminal vectors).**
A row of schedule mass $m/D$ may display one terminal mass vector
$c_{s,k}(\ell)$ in each of its cells, each summing to $m$.
For a three-cell pair with $m>0$, assign its whole deterministic table
$(\ell_0,\ell_{10},\ell_{11})$ probability

$$
\frac{c_{s,0}(\ell_0)c_{s,10}(\ell_{10})c_{s,11}(\ell_{11})}{D m^2}.
\tag{237.8}
$$

Summing over the other two labels gives terminal marginal
$c_{s,k}(\ell)/D$; summing all labels gives $m/D$.
For a singleton use the corresponding two-factor formula $\prod c/(Dm)$,
and for an empty schedule its one vector divided by $D$.
Zero-mass rows are omitted. Thus rows whose masses sum to $D$ produce
one normalized distribution on complete tables. One uniform seed selects
the complete table, including all potential outputs, before any answers.
This is the common-law correspondence of §§108–109, rather than three
independently sampled procedures after observing a cell.

## 238. Two unequal heads above a low seven-coordinate plateau

**Theorem 238.1 (Head allocation at the sharp low cap).**
Let

$$
0<t\le\tfrac12,\qquad t\le v\le1-t,\qquad
v\le u\le1-\tfrac{2t}{3},\qquad
(a_1,\ldots,a_7)=(u,v,t,t,t,t,t).
\tag{238.1}
$$

Retain any positive nonincreasing vanishing actual tail with
$a_8\le5t/9$. On the original source and resource domain of §243,
both N and O have attained optimal uniform error $5t/9$.
For this entire sequence and every positive closed cap $c$, both
classes are feasible exactly when $c\ge5t/9$.
The increment is the head region in (238.1); the lower certificate
and the equal-head core in §§230–231 are reused.

Proof. Put $\tau=t/9$ and $B_0=1-2t$. Start with the core whose
rows below have probability $\tau$ times their integer weight, and
put the remaining mass $B_0$ on empty output zero.

| Schedule | Outputs $0,10,11$ | Weight |
| --- | --- | --- |
| $12$ | $(0,2,0)$ | 2 |
| $12$ | $(0,2,7)$ | 1 |
| $13$ | $(1,3,0)$ | 2 |
| $14$ | $(1,4,0)$ | 1 |
| $15$ | $(1,5,0)$ | 1 |
| $23$ | $(0,3,0)$ | 2 |
| $24$ | $(0,4,0)$ | 1 |
| $25$ | $(2,5,0)$ | 1 |
| $34$ | $(0,4,0)$ | 1 |
| $34$ | $(0,4,6)$ | 1 |
| $35$ | $(0,5,0)$ | 1 |
| $45$ | $(0,5,0)$ | 1 |
| $46$ | $(0,6,7)$ | 1 |
| $56$ | $(0,6,7)$ | 2 |

Their weights sum to 18. Every first-zero class has correct integer
count four, independent of its suffix. Let $E_n$ be the integer
count at positive labels other than the actual first-zero label.
With $x=w_2,y=w_3,z=w_4,q=w_5$ and $k=y+z+q$, direct expansion gives

$$
\begin{aligned}
E_1&=1+3x+3y+2z+2q-2xy-xz-xq-yz-yq-zq,\\
E_2&=4+k-k(k-1)/2,&E_3&=5-zq,&E_4&=4-q,\\
E_5&=3,&E_6&=1,&E_7&=1.
\end{aligned}
\tag{238.2}
$$

For $E_1$, $x=y=0$ gives $1+2z+2q-zq\le4$;
$x+y=1$ gives $4+z+q-zq\le5$; and $x=y=1$ gives $5-zq\le5$.
For $E_2$, $k=0,1,2,3$ gives $4,5,5,4$.
The other bounds follow from their displayed polynomials.
Thus every word has outside-pair mass at most $5\tau$.
At the positive word the core counts are 13 at zero, one at six and
four at seven. Including the empty branch, its base is $1-5\tau$.
This verifies the reused core on all words, rather than only chain words.

Set $d_1=u-t$, $d_2=v-t$ and

$$
r_1=(d_1-d_2-3\tau)_+,\qquad
s=d_1-d_2-r_1=\min(d_1-d_2,3\tau).
$$

The hypotheses give $0\le d_2\le B_0$, $d_1\ge d_2$,
$d_1\le B_0+3\tau$ and hence $d_2+r_1\le B_0$.
Replace $d_2$ of the empty mass by $R=(1,2;1,2,0)$,
and $r_1$ by the singleton $(1;1,0)$.
Of the first core row, change only its zero-cell output from zero to
one on mass $s_1=\min(s,2\tau)$. Make that same change on mass
$s_2=s-s_1$ of the second core row. The capacities
$s_1\le2\tau$, $s_2\le\tau$ make all masses nonnegative, including
$t=1/2$ when the empty branch vanishes. Total mass stays one.

Every changed output is from zero to the correct actual label:
$R$ changes only classes one and two, the singleton only class one,
and the two relabelings only $w_1=0$. Therefore the outside-pair
mass $\tau E_n$ is unchanged, class one gains $d_2+r_1+s=d_1$,
class two gains $d_2$, and later correct masses do not change.
For every zero word,

$$
p_w(n)=a_n-5\tau,\quad
p_w(0)=1-a_n+5\tau-\tau E_n,\quad
p_w(0)+p_w(n)=1-\tau E_n\ge1-5\tau.
\tag{238.3}
$$

These imply each independent row (237.1), and the correct event has
error exactly $5\tau$. The positive base stays $1-5\tau$.
Definition 237.2 gives one actual O law and its same-seed N completion.
Every actual tail has exact error $\max(5\tau,a_n)=5\tau$.

For the lower bound, the full zero-cost score of §230 has
$\beta=(0,0,4,8,7,8,8)$, $K=63$ and yields the necessary original
cut $4a_3+8a_4+7a_5+8a_6+8a_7\le63c$.
At (238.1) it is $35t\le63c$. If a competitor had smaller error,
a positive intermediate closed cap below $5t/9$ and the original
necessity of §110.2 would contradict this cut. This covers arbitrary
addresses and full-carrier outputs, even when additional tail entries
are active at the smaller cap. The constructed law attains equality;
larger caps use the same law. ∎

Only the subfamily $v=t$ lies in the displayed hull slice $b_2=b_3$.
There the lower hull slack is $5t/9$ and the upper expression is
$u+5t/9\le1-t/9\le1$. Its mass-one completed law witnesses $H_N$.
For $v>t$ the original cap theorem still holds, without asserting hull
membership. At $t=v=1/2,u=2/3$, both first zero-cell relabelings are
complete; the correct counts divided by 18 are seven for class one
and four otherwise. This closed endpoint is a legal head allocation.
No equal-head core, old plateau endpoint or generic transport is counted
as an additional mathematical region.

## 239. Simultaneous higher Hamming layers on one measure

**Definition 239.1 (A common layer and its two representatives).**
Let integers $m\ge6$, $3\le\rho\le m-3$, $L\ge m$ be fixed.
Take unit counting mass $\mu$ on the length-$m$ words $(x,0)$,
$x\in\{0,1\}^{m-1}$, $1\le|x|\le\rho$, excluding the singleton
whose sole one is at position $m-1$. Use binomial coefficients zero
outside their usual range, and empty sums zero. Put

$$
\begin{aligned}
d&=\sum_{a=1}^{\rho}\binom{m-2}{a}-1,&
u&=\sum_{a=0}^{\rho-1}\binom{m-3}{a},&
v&=\sum_{a=0}^{\rho-2}\binom{m-3}{a},\\
s&=d+u+v,&T&=d-v,&p_n&=\mu(\Omega_n),&\gamma_n&=d-p_n.
\end{aligned}
\tag{239.1}
$$

Explicitly $p_1=d$, $p_2=u$, $p_m=0$, and

$$
p_n=\sum_{a=0}^{\rho-n+1}\binom{m-1-n}{a}\quad(2\le n\le m-1).
\tag{239.2}
$$

Both scores below have $A=0$, $P=\mu$, terminal $T$ and correct
class totals $\gamma_n$. In $Y$, place $C_n=\gamma_n$ at the chain
word $1^{n-1}0^{m-n+1}$. For $Z$, set
$E_n=\{w:n(w)<n,w_n=0\}$, $c_n=\mu(E_n)$.
When $\gamma_n>0$, push $(\gamma_n/c_n)\mu|_{E_n}$ forward by
resetting all positions before $n$ to one. This defines its entire
$C_n$ measure together with all other classes, from the same $\mu$.
If $\gamma_n=0$, use zero without division.
Pad all scored words by ones to length $L$ and put terminal mass at $1^L$.

**Theorem 239.2 (Full support replacement and exact signed reading).**
At every parameter in Definition 239.1,

$$
\begin{gathered}
Q(Y)=Q(Z)=(\gamma_1,\ldots,\gamma_m,0,\ldots,0;(m+1)d-v),\quad
W_Y=W_Z=3d,\\
\Delta_O(Y)=\Delta_N(Z)=\Delta_O(Z)=0,\qquad
\Delta_N(Y)\ge u-[m=\rho+3]>1,\\
\sigma_{H_L}(Q(Y))=u-\frac{u+v}{m-1}>1.
\end{gathered}
\tag{239.3}
$$

For every real $c\ge0$, the actual full unit-O input $cY$ therefore
has the single unrestricted replacement $V=cZ$, $\theta=0$.

Proof. Counting subsets gives (239.2), $\mu(\{0,1\}^m)=s$ and

$$
\begin{gathered}
\mu(w_i=0)=d\ (i\le m-2),\quad\mu(w_{m-1}=0)=d+1,\quad
\mu(w_m=0)=s,\\
\mu(w_iw_j=10)=u,\quad\mu(w_iw_j=11)=v,\quad
\mu(w_iw_j=01)=u-[j=m-1]\quad(i<j<m).
\tag{239.4}
\end{gathered}
$$

The removed singleton has first zero one and changes only the indicated
marginals. Pascal's identity gives $s=d+u+v$,
$d-u=\sum_{a=1}^{\rho}\binom{m-3}{a}-1\ge0$, and $u\ge v\ge1$.
Thus $T\ge0$ and every $\gamma_n\ge0$.
Because $w_n=0$ implies first zero at most $n$,
$c_n=\mu(w_n=0)-p_n$. Consequently
$c_n=\gamma_n$ for $n\le m-2$,
$c_{m-1}=\gamma_{m-1}+1$ and $c_m=s\ge d=\gamma_m$.
All divisions in the reset constructor have positive denominator and
density at most one. Resetting preserves mass and gives first zero $n$.
Every positively scored nonterminal word still has its last bit zero.

Fix any queried $i<j$ and numerical label $n\le i$. Resetting before
$n$ changes neither queried bit. Within each cell the $C_n$ contribution
is at most the original $\mu$ mass with first zero below $n$ and
$w_n=0$. Its $P_n$ contribution uses the disjoint set with first zero
$n$. Hence their sum is at most the baseline $\mu$ mass of that cell.
For $i<n\le m$, both contributions have $w_i=1$ and their total mass is
$p_n+\gamma_n=d$. This proves the required simultaneous control of
all earlier unqueried as well as queried labels.

For $i<j<m$ the two $w_i=0$ N maxima sum to $d$: zero dominates
there. The 10 maximum is at most $d$, since its baseline is $u\le d$;
the 11 baseline is $v+T=d$, also dominating the upper bound $d$ on
later-label rewards. Thus the sum is at most $3d$.
For $j=m$ the 01 cell is empty, 11 has only $T$, and, writing
$d_i=\mu(w_i=0)$, the sum is at most

$$
d_i+\max(s-d_i,d)+d-v\le3d.
\tag{239.5}
$$

If $d_i=d$, this follows from $u\le d$; if $d_i=d+1$, it also
uses $v\ge1$. Empty and singleton N functions refine to distinct pairs,
so this bounds the complete N catalog of $Z$.

For $Y$, the O merged zero cell at $i<j<m$ has baseline $d$ and
every active numerical label has total reward $p_n+\gamma_n=d$;
padded numerical labels have zero reward.
Its 10 and 11 maxima are at most $d$ as above. Formula (239.5)
uses only totals and last-bit-zero support and therefore also bounds
$Y$ when $j=m$. This bounds all O tables.
Now $\sum C=md-s$ and the early correct total is
$\gamma_2=d-u$, so

$$
W=s+(d-u)+(d-v)=3d,\qquad K=s+(md-s)+(d-v)=(m+1)d-v.
$$

The anchor attains $W$ and the support bounds prove all zero-cost
claims and equal quotients.

To see the actual N gap of $Y$, query $i=\rho+1$, $j=\rho+2$.
Its 00 cell can output $i$, collecting $d$ from its sole $P_i$ atom
and chain correct atom; 01 can collect baseline $u-[j=m-1]$,
10 can collect $C_j=d$, and 11 collects $v+T=d$ at zero.
This is one full legal table. The excess is at least
$u-[m=\rho+3]>1$, since $u\ge m-2$.

For the exact signed support, put $P_k=\sum_{n\le k}p_n$ and
$S_k=\sum_{n\le k}\gamma_n$. One has $K-S_m=2d+u$.
Both $o,p$ read $-\gamma_2$. For $3\le k\le m$, (237.7) gives

$$
F_q(v_k)=\frac{3(d+u-P_k)}{k+1}\le0,
\qquad F_q(u_k)=\frac{S_k}{k-1}-\gamma_2.
\tag{239.6}
$$

Swapping adjacent bits $n,n+1$ injects first-zero class $n+1$ into
class $n$ for $n\ge2$. The removed singleton has first zero one,
so it does not disrupt this injection. Hence $p_n$ is nonincreasing
for $n\ge2$, $\gamma_2,\ldots,\gamma_m$ are nondecreasing, and
the displayed prefix averages are maximized at $m$.
That maximum equals $u-(u+v)/(m-1)$.
For padded $k>m$ the $u_k$ readings decrease; consecutive $v_k$
readings decrease by $3K/((k+1)(k+2))$. Finally
$u-(u+v)/(m-1)\ge(m-2)(m-3)/(m-1)>1$.
All unused bits are one and their labels have zero reward on this score;
querying them coarsens one of the checked partitions. Thus padding,
reversals and repetitions introduce no missing schedules or labels.
Homogeneity proves the assertion for all $c\ge0$. ∎

**Corollary 239.3 (Original cut and its exact relative scope).**
Every complete feasible conic N allocation, of any finite mass, obeys

$$
\sum_{n=1}^m\gamma_n b_n\le\gamma_2+[(m+1)d-v]e.
\tag{239.7}
$$

Every original N or O cap attainer obeys the same inequality with
$a_n,c$ in place of $b_n,e$, at all positive closed caps and without
requiring the chosen positions active. Indeed (237.5) with $Z$ gives
zero on the right for a conic allocation. For an original attainer,
§110.2 gives one full finite probability configuration. If its active
horizon is below $m$, extend it by ignoring added bits. New first-zero
classes have $a_n\le c$, correct probability zero and base and pair
probability at least $1-c$; old rows persist. Pairing with $Z$ proves
the cut. For $c\ge1$ it follows directly from amplitudes at most one.
O uses its counted N completion. ∎

At $m=7,\rho=3$ the counts are

$$
(d,u,v,s,T)=(24,11,5,40,19),\quad
q_*=(0,13,20,23,24,24,24;187),\quad W=72.
\tag{239.8}
$$

At the flat cap $e=5t/9$, (239.7) excludes both original classes
when $117/217<t\le27/49$: its reading is $(217t-117)/9>0$.
At the upper endpoint its lower error bound is
$2819/9163=15/49+2/1309$.
This displayed eliminated interval supplies no additional strength over
the necessary cut in §240: its flat lower bound is stronger there by

$$
\frac{29t-2}{45}-\frac{128t-13}{187}
 =\frac{211-337t}{8415}>0.
\tag{239.9}
$$

This comparison concerns necessary cuts, and does not extend §240's
attainment interval. The simultaneous replacement and the following
signed-cone statement remain distinct from that eliminated-profile reading.

Let $\mathcal C_{\rm old}$ be precisely the cone of the four reused
$\rho=2$ directions $q_{k,2}^7$, $k=4,5,6,7$, and the direction
$(0,0,4,8,7,8,8;63)$. Let
$P_H=\{p:\sigma_{H_7}(p)\le0\}$.
At $b_*=(27/49,\ldots,27/49;15/49)\in H_7$, their readings are
$-54/49,-101/49,-95/49,0,0$, while $F_{q_*}(b_*)=2/7$.
Therefore

$$
q_*\notin\mathcal C_{\rm old}+P_H.
\tag{239.10}
$$

For $c>7/2$ any proposed $Q(V)\in\mathcal C_{\rm old}$ leaves
residual reading at least $2c/7>1$ at that point. It cannot be paid by
one $\theta\le1$. Nevertheless the unrestricted choice $cZ$ works.
The same necessary cut proves $b_*\notin H_N$, so it is not an
original separator. The restriction to $\mathcal C_{\rm old}$ belongs
only to this relative comparison. The old $\rho=2$ family, its uniform
prefix pullback in §§233–235, and zero-cost closure under finite sums
are reused: adding these replacements to an already certified input
preserves that input's one residual and budget, without a new closure claim.

## 240. An ordered-five-late full cut and the upper equal-seven interval

**Theorem 240.1 (The complete 45-charge cut).**
For every $L\ge7$, every $3\le j_1<\cdots<j_5\le L$, and every
same full feasible N allocation of any finite mass,

$$
2b_2+4b_{j_1}+6b_{j_2}+5b_{j_3}+6b_{j_4}+6b_{j_5}\le2+45e.
\tag{240.1}
$$

Every original N or O cap attainer satisfies the identical necessary
inequality with $a,c$ in place of $b,e$, at every positive closed cap.
No active-horizon condition on the selected addresses is required.

Proof. On seven positions set $A=0$, $T=4$, with the following
nonzero $P,C$ coefficients; every unlisted coefficient is zero.

| Word | Event | Weight |
| --- | --- | --- |
| $0011000$ | $P$ | 1 |
| $0011110$ | $P$ | 1 |
| $0101000$ | $P$ | 1 |
| $0101100$ | $P$ | 1 |
| $0110010$ | $P$ | 1 |
| $0110100$ | $P$ | 1 |
| $1001010$ | $P$ | 1 |
| $1001100$ | $P$ | 1 |
| $1010000$ | $P$ | 1 |
| $1010100$ | $P$ | 1 |
| $1011000$ | $C$ | 1 |
| $1011110$ | $C$ | 1 |
| $1100000$ | $P$ | 1 |
| $1100110$ | $P$ | 1 |
| $1101000$ | $C$ | 1 |
| $1101010$ | $C$ | 1 |
| $1101100$ | $C$ | 2 |
| $1110000$ | $C$ | 3 |
| $1110100$ | $C$ | 1 |
| $1110110$ | $C$ | 2 |
| $1111000$ | $C$ | 4 |
| $1111010$ | $C$ | 1 |
| $1111100$ | $C$ | 6 |
| $1111110$ | $C$ | 6 |

The class totals are $C=(0,2,4,6,5,6,6)$ and
$P=(6,4,2,0,0,0,0)$. Thus $W=18$, $K=45$ and
$Q=(0,2,4,6,5,6,6;45)$. Here are all schedule cell maxima
from (237.3), with N cells $00,01,10,11$ and O cells $0,10,11$;
singletons use $0,1$. The maxima include all eight labels.

| Schedule | N maxima | O maxima |
| --- | --- | --- |
| $\varnothing$ | $(16)$ | $(16)$ |
| $1$ | $(6,10)$ | $(6,10)$ |
| $2$ | $(6,10)$ | $(6,10)$ |
| $3$ | $(6,10)$ | $(6,10)$ |
| $4$ | $(6,10)$ | $(6,10)$ |
| $5$ | $(6,10)$ | $(6,10)$ |
| $6$ | $(8,8)$ | $(8,8)$ |
| $7$ | $(12,4)$ | $(12,4)$ |
| $12$ | $(2,4,6,6)$ | $(6,6,6)$ |
| $13$ | $(2,4,6,6)$ | $(6,6,6)$ |
| $14$ | $(2,4,6,6)$ | $(6,6,6)$ |
| $15$ | $(3,3,5,7)$ | $(6,5,7)$ |
| $16$ | $(4,2,6,6)$ | $(6,6,6)$ |
| $17$ | $(6,0,6,4)$ | $(6,6,4)$ |
| $23$ | $(2,4,6,6)$ | $(6,6,6)$ |
| $24$ | $(2,4,6,6)$ | $(6,6,6)$ |
| $25$ | $(3,3,5,7)$ | $(6,5,7)$ |
| $26$ | $(4,2,6,6)$ | $(6,6,6)$ |
| $27$ | $(6,0,6,4)$ | $(6,6,4)$ |
| $34$ | $(2,4,6,6)$ | $(6,6,6)$ |
| $35$ | $(3,3,5,7)$ | $(6,5,7)$ |
| $36$ | $(4,2,6,6)$ | $(6,6,6)$ |
| $37$ | $(6,0,6,4)$ | $(6,6,4)$ |
| $45$ | $(3,3,5,7)$ | $(6,5,7)$ |
| $46$ | $(4,2,6,6)$ | $(6,6,6)$ |
| $47$ | $(6,0,6,4)$ | $(6,6,4)$ |
| $56$ | $(4,2,6,6)$ | $(6,6,6)$ |
| $57$ | $(6,0,6,4)$ | $(6,6,4)$ |
| $67$ | $(8,0,6,4)$ | $(8,6,4)$ |

This finite addition is a complete support proof: for each cell sum
its $P$ mass plus terminal mass at label zero, and compare with every
class's $C+P$ mass at its numerical label. The atoms above give precisely
the displayed maxima. Every schedule sum is at most 18, and the anchor
attains 18. Thus $B_N=B_O=W=18$ and both excesses are zero.
For arbitrary ordered selected late addresses use skeleton
$(1,2,j_1,j_2,j_3,j_4,j_5)$ and put one in every unselected bit.
Each scored class and its reward label is transported to its skeleton
address. A query outside that skeleton is constant on this score and
folds to an empty or singleton observation. Its numerical label has
zero reward. Reversals permute cells and repetitions coarsen them.
Thus the same support bound holds for the complete catalog at every $L$;
it restricts only this score, not competitors or unscored words.

Equation (237.5) now gives (240.1) for any mass on whole tables.
For original competitors, use the necessary direction of §110.2 and
extend a shorter active kernel by ignoring new bits as in Corollary
239.3. If the active horizon is longer than the score, pad the score
with ones, or restrict the finite comparison by fixing later bits zero
and projecting later labels to zero. The positive low word then has
base target, and TV contracts. These are finite representation operations,
not free source observations. Pairing the resulting single full
configuration with the score proves (240.1) on actual amplitudes.
At $c\ge1$ the coefficient sum 29 is below $2+45c$.
Counted same-seed N completion covers O competitors. ∎

**Theorem 240.2 (Attained upper equal-seven region).**
Suppose

$$
\tfrac12<t\le\tfrac{41}{77},\qquad a_1=\cdots=a_7=t,
\qquad e_t=\frac{29t-2}{45}.
\tag{240.2}
$$

For every positive nonincreasing vanishing actual tail with $a_8\le e_t$,
both original classes have attained optimal uniform error $e_t$ and
are feasible at a positive closed cap exactly when that cap is at least
$e_t$. The half endpoint is the reused law of §231; no attainment
beyond $41/77$ is asserted.

Proof. Use that half-endpoint whole law, namely the 14 core rows of
Theorem 238.1 divided by 18 without empty mass. Its cap is $5/18$.
For the upper endpoint use these whole deterministic rows, with mass
equal to the integer weight divided by 154:

| Schedule | Outputs $0,10,11$ | Weight |
| --- | --- | --- |
| $12$ | $(0,2,0)$ | 12 |
| $12$ | $(0,2,3)$ | 6 |
| $12$ | $(0,2,6)$ | 2 |
| $13$ | $(1,3,0)$ | 12 |
| $13$ | $(1,3,7)$ | 4 |
| $14$ | $(1,4,0)$ | 12 |
| $15$ | $(0,5,0)$ | 1 |
| $15$ | $(1,5,0)$ | 8 |
| $23$ | $(0,3,0)$ | 7 |
| $23$ | $(2,3,0)$ | 5 |
| $23$ | $(2,3,6)$ | 2 |
| $24$ | $(0,4,0)$ | 12 |
| $25$ | $(2,5,0)$ | 9 |
| $26$ | $(0,6,7)$ | 2 |
| $34$ | $(0,4,0)$ | 12 |
| $35$ | $(0,5,0)$ | 9 |
| $45$ | $(0,5,0)$ | 9 |
| $46$ | $(0,6,7)$ | 12 |
| $56$ | $(0,6,7)$ | 18 |

Their weights sum to 154. Every first-zero class has constant correct
count 36: count every occurrence of its queried output and each
exhaustion guess, whose two queried addresses precede that label.
Consequently later zeros do not affect that count.
For an explicit complete outside-pair verification, the following lists
give all wrong positive counts in each class. For $n\le6$, fix
$w_1=\cdots=w_{n-1}=1,w_n=0$ and list the free bits
$(w_{n+1},\ldots,w_6)$ in lexicographic binary order. Bit seven is
unqueried and does not alter the output. Class seven has one transcript.

| First zero | Wrong counts, in the specified order |
| --- | --- |
| 1 | $16,16,34,34,37,37,46,46,37,37,46,46,46,46,46,46,37,37,46,46,46,46,46,46,46,46,46,46,43,43,34,34$ |
| 2 | $37,37,46,46,46,46,46,46,46,46,46,46,43,43,34,34$ |
| 3 | $46,46,46,46,43,43,34,34$ |
| 4 | $43,43,34,34$ |
| 5 | $28,28$ |
| 6 | $10$ |
| 7 | $10$ |

Each entry follows from the explicit formula
$\sum_D k_D[\operatorname{out}_D(w)\notin\{0,n\}]$;
the table exhausts all suffixes. Its maxima are
$(46,46,46,43,28,10,10)$. The base counts are $154-36-E_n$,
so base is at least 72, correct is 36 and pair is at least 108.
At $1^7$ the label counts are $(108,0,0,6,0,0,4,36)$.
For $t=41/77=82/154$, $e=23/77=46/154$, these satisfy
all three independent demands and the positive demand. In particular
correct demand is 36, base demand is 26, and pair demand is 108.
The low endpoint is verified on every suffix by (238.2).

For $t\in[1/2,41/77]$ put $\eta=(154t-77)/5\in[0,1]$.
Take the convex combination of the entire low and high laws with
high weight $\eta$. Its amplitude and cap are the same convex
combinations of endpoint data, and that cap is $(29t-2)/45$.
All 382 rows are affine in this one kernel and in $(a,e)$, so every
row holds simultaneously, with correct mass $t-e_t$ and positive
base $1-e_t$. The correct event makes the low-word error exactly $e_t$.
Definition 237.2 and §243 give an actual O attainer and same-seed
counted N completion, with every actual tail error
$\max(e_t,a_n)=e_t$ including equality. Conversely (240.1) at
consecutive late positions gives $29t\le2+45c$ against every
original competitor. An intermediate cap below $e_t$ contradicts it.
This proves attained optimality and the assertion for every cap. ∎

The finite attainer has mass one in the full cone and lies in $H_7$:
the lower hull slack is $(16-7t)/45$ and the upper expression is
$(38t+16)/45\le62/77$. Its full same-seed completion proves $H_N$.
Relative to the old displayed directions, at
$(b,e)=(51/100,\ldots,51/100;17/60)$ the old 63-charge reading
is zero, the four old $\rho=2$ readings are nonpositive, and this
cut reads $1/25>0$. This point is outside $H_N$ by (240.1), so it
is not an original separator. At the former flat cap $5t/9$ this
cut reads $4t-2>0$ beyond the half endpoint, excluding both classes.
This necessary exclusion is distinct from the attained interval (240.2).

## 241. A full 117-charge cut and an unequal seventh coordinate

**Theorem 241.1 (Same-allocation cut at every ordered embedding).**
For $L\ge7$ and $3\le j_1<\cdots<j_5\le L$, every full feasible
N cone allocation, of any finite mass, satisfies

$$
10b_{j_1}+14b_{j_2}+13b_{j_3}+14b_{j_4}+14b_{j_5}\le117e.
\tag{241.1}
$$

Every original N or O cap attainer obeys the same necessary inequality
with its actual amplitudes and positive closed cap. The selected
addresses may be inactive and may have arbitrary gaps.

Proof. On seven bits take $A=0$, $T=10$ and exactly these atoms:

| Word | Event | Weight |
| --- | --- | --- |
| $1100110$ | $C$ | 6 |
| $1101101$ | $C$ | 4 |
| $1110000$ | $C$ | 4 |
| $1110110$ | $C$ | 10 |
| $1111000$ | $C$ | 3 |
| $1111010$ | $C$ | 10 |
| $1111100$ | $C$ | 4 |
| $1111101$ | $C$ | 10 |
| $1111110$ | $C$ | 14 |
| $0100110$ | $P$ | 3 |
| $0101000$ | $P$ | 1 |
| $0101001$ | $P$ | 1 |
| $0101100$ | $P$ | 5 |
| $0110000$ | $P$ | 3 |
| $0110010$ | $P$ | 4 |
| $0111000$ | $P$ | 2 |
| $1000100$ | $P$ | 2 |
| $1000110$ | $P$ | 1 |
| $1001001$ | $P$ | 3 |
| $1001010$ | $P$ | 4 |
| $1010001$ | $P$ | 2 |
| $1010100$ | $P$ | 3 |
| $1010101$ | $P$ | 2 |
| $1011000$ | $P$ | 2 |
| $1100010$ | $P$ | 2 |
| $1100101$ | $P$ | 2 |

Summing gives $C=(0,0,10,14,13,14,14)$, $P$ total 42,
$W=52$, $K=117$. The $P$ measure includes mass four in class three;
no early-P restriction is imposed on full competitors. The following
are all schedule cell maxima over all eight labels:

| Schedule | N maxima | O maxima |
| --- | --- | --- |
| $\varnothing$ | $(52)$ | $(52)$ |
| $1$ | $(19,33)$ | $(19,33)$ |
| $2$ | $(19,33)$ | $(19,33)$ |
| $3$ | $(24,28)$ | $(24,28)$ |
| $4$ | $(24,28)$ | $(24,28)$ |
| $5$ | $(24,28)$ | $(24,28)$ |
| $6$ | $(28,24)$ | $(28,24)$ |
| $7$ | $(32,20)$ | $(32,20)$ |
| $12$ | $(0,19,19,14)$ | $(19,19,14)$ |
| $13$ | $(10,9,14,19)$ | $(19,14,19)$ |
| $14$ | $(10,9,14,19)$ | $(19,14,19)$ |
| $15$ | $(11,8,13,20)$ | $(19,13,20)$ |
| $16$ | $(12,7,16,17)$ | $(19,16,17)$ |
| $17$ | $(18,1,14,19)$ | $(19,14,19)$ |
| $23$ | $(10,9,14,19)$ | $(19,14,19)$ |
| $24$ | $(10,9,14,19)$ | $(19,14,19)$ |
| $25$ | $(11,8,13,20)$ | $(19,13,20)$ |
| $26$ | $(14,5,14,19)$ | $(19,14,19)$ |
| $27$ | $(12,7,20,13)$ | $(19,20,13)$ |
| $34$ | $(10,14,14,14)$ | $(24,14,14)$ |
| $35$ | $(11,13,13,15)$ | $(24,13,15)$ |
| $36$ | $(14,10,14,14)$ | $(24,14,14)$ |
| $37$ | $(18,6,14,14)$ | $(24,14,14)$ |
| $45$ | $(11,13,13,15)$ | $(24,13,15)$ |
| $46$ | $(14,10,14,14)$ | $(24,14,14)$ |
| $47$ | $(18,6,14,14)$ | $(24,14,14)$ |
| $56$ | $(14,10,14,14)$ | $(24,14,14)$ |
| $57$ | $(18,6,14,14)$ | $(24,14,14)$ |
| $67$ | $(18,10,14,10)$ | $(28,14,10)$ |

For every cell, label zero collects its $P$ mass and any terminal mass;
label $n$ collects that cell's $C+P$ mass in class $n$. Taking the
maximum of these quantities gives each entry by integer addition.
Every schedule sum is 52. Constant zero and the anchor attain 52,
so $B_N=B_O=W=52$ and both costs are zero.
Embed the seven positions as $(1,2,j_1,\ldots,j_5)$ and fix other
scored bits to one. Inactive-bit observations coarsen the checked
partitions and inactive labels have zero reward on this score.
This proves the full all-label support for every embedding and horizon.
Pairing with the same full $\lambda$ in (237.5) proves (241.1),
regardless of mass. The original necessary statement follows from
§110.2 and the restriction/ignored-bit extension in Theorem 240.1,
retaining negative singleton and independent pair rows. For caps at
least one it follows from the coefficient sum $65<117$.
O completion counts every ignored acquired reply. ∎

**Theorem 241.2 (Attained unequal seventh-coordinate region).**
Let

$$
0<t\le\tfrac12,\qquad\tfrac9{10}\le r\le1,\qquad
(a_1,\ldots,a_7)=(t,t,t,t,t,t,rt),\quad
 e_{t,r}=\frac{(51+14r)t}{117}.
\tag{241.2}
$$

For every positive nonincreasing vanishing actual tail with
$a_8\le e_{t,r}$, both original classes attain optimal uniform error
$e_{t,r}$. At every positive closed cap, feasibility in either class
is equivalent to the cap being at least $e_{t,r}$.
The boundary $r=1$ reuses the equal-head low plateau.

Proof. Endpoint A is the 14-row law in §238 divided by 18:
$t=1/2,r=1,e=5/18$. Its correct counts are four, its wrong
counts are given by (238.2), and its positive base is 13/18.
Endpoint B has $t=1/2,r=9/10,e=53/195$. The following terminal
vectors have common denominator 780. A bare label means the entire
row mass at that label; braces list actual integer label masses.
Empty has a single cell. Every pair has cells $0,10,11$.

| Schedule | Row mass | Terminal vectors |
| --- | --- | --- |
| $\varnothing$ | 6 | $\{0:6\}$ |
| $12$ | 135 | $\{0:80,1:55\}; 2; \{0:80,3:18,4:15,6:12,7:10\}$ |
| $13$ | 80 | $1; 3; 0$ |
| $14$ | 43 | $0; 4; 0$ |
| $15$ | 43 | $1; 5; 0$ |
| $23$ | 80 | $0; 3; 0$ |
| $24$ | 43 | $2; 4; 0$ |
| $25$ | 43 | $0; 5; 0$ |
| $34$ | 77 | $0; 4; \{0:46,6:31\}$ |
| $35$ | 46 | $0; 5; 0$ |
| $36$ | 3 | $0; 6; 0$ |
| $45$ | 46 | $0; 5; 0$ |
| $46$ | 43 | $0; 6; \{0:3,7:40\}$ |
| $56$ | 89 | $0; 6; \{0:3,7:86\}$ |
| $67$ | 3 | $0; 7; 0$ |

Every cell mass equals its row mass, and the row masses sum to 780.
Formula (237.8) therefore provides one full stopped law. Correct
counts in classes one through seven are respectively

$$
\begin{gathered}
55+80+43=178,\quad135+43=178,\quad80+80+18=178,\\
43+43+77+15=178,\quad43+43+46+46=178,\\
3+43+89+12+31=178,\qquad3+10+40+86=139.
\end{gathered}
$$

The exhaustion guesses in those counts follow both queried addresses;
queried correct outputs have only preceding positive bits.
Thus these counts hold on every suffix, not only sole-zero words.
For a complete wrong-count proof put
$x=w_2,y=w_3,z=w_4,q=w_5,v=w_6,h=w_7$ and $k=y+z+q$.
Expansion of the same terminal vectors gives

$$
\begin{aligned}
E_1={}&43+123x+126y+89z+89q+3v-80xy-43xz-43xq\\
 &-46yz-46yq-3yv-46zq-3zv-3qv-3vh,\\
E_2={}&166+46k-46k(k-1)/2+3v(1-k-h),\\
E_3={}&209+3(z+q+v)-46zq-3v(z+q+h),\\
E_4={}&175-43q-3qv-3vh,\\
E_5={}&132-3v-3vh,\qquad E_6=43,\quad E_7=76.
\end{aligned}
\tag{241.3}
$$

For $E_1$, cases $(x,y)=00,10,01,11$ give respectively

$$
\begin{aligned}
43+89(z+q)-46zq+3v(1-z-q-h)&\le175,\\
166+46(z+q)-46zq+3v(1-z-q-h)&\le212,\\
169+43(z+q)-46zq-3v(z+q+h)&\le212,\\
212-46zq-3v(z+q+h)&\le212.
\end{aligned}
$$

In the first two lines split $z+q=0,1,2$: the potential positive
$3v$ occurs only at zero, where the constant is below the bound;
at one or two its coefficient is nonpositive. The other two lines
are immediate from the same split. For $E_2$, $k=0$ gives at most
169, $k=1,2$ at most 212, and $k=3$ at most 166.
For $E_3$, $z+q=0,1,2$ gives at most $212,212,169$.
The remaining polynomials give bounds $175,132,43,76$ directly.
Consequently the wrong maxima are $(212,212,212,175,132,43,76)$.
They are attained by suitable suffixes in each case. The minimum base
counts, obtained by subtracting the constant correct count and these
maxima from 780, are
$(390,390,390,427,470,559,565)$.

In units $1/780$, the correct demands are 178 for classes one to six,
139 for class seven; base demands are 178 and 217 respectively;
the independent pair demand is 568. The base minima just given and
correct counts meet these demands, and their sums are at least 568.
At the positive word the counts are
$(568,0,0,18,15,0,43,136)$, so its base is also 568.
All 382 rows hold at the closed cap $212/780=53/195$.

For general $r$, mix the entire endpoints A and B with B weight
$\lambda=10(1-r)\in[0,1]$. Then mix that entire law with empty
output zero, using law weight $2t$. Each row is affine in the one
kernel and in its amplitudes and cap. The resulting amplitudes are
$(t,\ldots,t,rt)$ and its cap is
$2t[(1-\lambda)5/18+\lambda53/195]=(51+14r)t/117$.
Correct mass equals $a_n-e_{t,r}$, and positive base equals
$1-e_{t,r}$. The actual source construction in §243 has low-word
error exactly $e_{t,r}$ and every tail error
$\max(e_{t,r},a_n)=e_{t,r}$, including equality.
The same whole law and seed give the counted N completion.
The cut (241.1) at consecutive late addresses gives the matching lower
bound $(51+14r)t\le117c$ against all original competitors;
an intermediate smaller positive cap excludes a smaller error.
This proves attainment and every closed-cap threshold. ∎

The attained point belongs to $H_7$: the lower slack is
$(60+5r)t/117$ and the upper expression is
$(177+5r)t/117\le91/117$. The full probability vector just constructed,
not this hull computation alone, supplies its mass-one $H_N$ witness.

For a precise relative comparison, at
$b=(1/2,\ldots,1/2,9/20)$, $e=19/70$, the old 63-charge cut
reads zero, (241.1) reads $3/70$, and (240.1) reads $-1/70$.
Every gapped placement of the old 63-charge weights has reading no
larger than its consecutive placement, by monotonicity of $b$.
The four old $\rho=2$ prefix directions at $m=4,5,6,7$ read
$-33/35,-131/70,-64/35,-29/35$.
For their longer prefixes, pad $b$ by $e$; for $m\ge7$ the reading is
$(-31m^2+233m-344)/280$, whose next difference is
$(101-31m)/140<0$. Thus all those specified prefix tests pass.
The new positive reading proves this hull point outside $H_N$.
These comparisons concern the displayed cuts, not semantic completeness
of all predecessor consequences or an original N/O separator.

## 242. Two coupled high regions with the exact head interpolation

**Theorem 242.1 (Exact union of the high seven-coordinate regions).**
Use the actual first amplitude $h=a_1$ and put

$$
H(t)=\frac{4t+1}{5},\qquad e_2(t)=\frac{29t-4}{40},\qquad
 e_1(t,h)=\frac{5t+h-1}{8}.
\tag{242.1}
$$

The other first-seven amplitudes are $a_2=\cdots=a_7=t$.
The two regions and their attained optimal uniform errors in both
original classes are

$$
\begin{array}{c|c}
28/33\le t\le1,\quad t\le h\le H(t)&e_2(t)\\
9/10\le t\le1,\quad t\le h\le1&\max(e_2(t),e_1(t,h)).
\end{array}
\tag{242.2}
$$

Each statement retains every positive nonincreasing vanishing actual
tail with $a_8$ at most its displayed optimum, including equality.
For every such entire sequence, both original classes are feasible
at a positive closed cap exactly when the cap is at least that optimum.
Thus the union consists of the lower wedge
$28/33\le t<9/10$, $t\le h\le H(t)$, and the entire high head region
$9/10\le t\le1$, $t\le h\le1$. There is no all-head assertion
below $9/10$. The intersection is one shared region.

Proof. First construct the lower-wedge endpoint. The following sixteen
rows give terminal integer masses with denominator 33; braces list
label and mass, and all three cell masses in a row agree.

| Schedule | Cell $0$ | Cell $10$ | Cell $11$ |
| --- | --- | --- | --- |
| $12$ | $\{0:1,1:6\}$ | $\{2:7\}$ | $\{0:1,7:6\}$ |
| $13$ | $\{1:1\}$ | $\{3:1\}$ | $\{0:1\}$ |
| $14$ | $\{1:1\}$ | $\{4:1\}$ | $\{0:1\}$ |
| $15$ | $\{1:2\}$ | $\{5:2\}$ | $\{0:1,6:1\}$ |
| $16$ | $\{1:1\}$ | $\{6:1\}$ | $\{0:1\}$ |
| $23$ | $\{0:1\}$ | $\{3:1\}$ | $\{0:1\}$ |
| $24$ | $\{2:1\}$ | $\{4:1\}$ | $\{0:1\}$ |
| $25$ | $\{2:2\}$ | $\{5:2\}$ | $\{0:1,6:1\}$ |
| $26$ | $\{2:1\}$ | $\{6:1\}$ | $\{0:1\}$ |
| $34$ | $\{3:6\}$ | $\{4:6\}$ | $\{0:1,5:3,6:2\}$ |
| $35$ | $\{3:3\}$ | $\{5:3\}$ | $\{0:1,7:2\}$ |
| $36$ | $\{0:1\}$ | $\{6:1\}$ | $\{0:1\}$ |
| $45$ | $\{0:1\}$ | $\{5:1\}$ | $\{0:1\}$ |
| $46$ | $\{4:3\}$ | $\{6:3\}$ | $\{0:1,7:2\}$ |
| $56$ | $\{0:1\}$ | $\{6:1\}$ | $\{0:1\}$ |
| $67$ | $\{0:1\}$ | $\{7:1\}$ | $\{0:1\}$ |

Their common row masses sum to 33, so (237.8) gives one normalized
full O law $J_0$. For every suffix, its correct integer count is eleven
in each class. The seven sums, read from the rows, are

$$
\begin{gathered}
6+1+1+2+1,\quad7+1+2+1,\quad1+1+6+3,\quad1+1+6+3,\\
2+2+3+1+3,\quad1+1+1+3+1+1+1+2,\quad1+6+2+2.
\end{gathered}
$$

Every sum is eleven. Queried correct outputs require only earlier
positive replies; every correct exhaustion guess follows both queries.
Therefore these equalities hold on all multiple-zero suffixes.
For $k=\sum_{i=1}^6w_i$, reading the zero entries gives

$$
33p^{J_0}_w(0)=6-k+\binom{k}{2}+w_6w_7.
\tag{242.3}
$$

Indeed the constant zero-cell terms are those of $12,23,36,45,56,67$;
every pair among the first six has one base exhaustion unit, with the
extra $67$ term. The first three terms at $k=0,\ldots,6$ are
$6,5,5,6,8,11,15$. On classes one through seven the exact minimum
base counts are $(5,5,5,6,8,11,15)$, and on $1^7$ the base count
is sixteen. Thus at $t_0=28/33,e_0=17/33$ all rows hold:
correct demand is eleven, pair demand is sixteen, and base demand is
$-12$ in integer units. The pair row is verified by adding the
independently computed base and correct counts, without discarding it.

For $0\le\sigma\le1$, change only the first cell of row $12$ from
$\{0:1,1:6\}$ to $\{0:1-\sigma,1:6+\sigma\}$.
This transfers $\sigma/33$ from base to correct only on $w_1=0$.
Its pair sum is unchanged, its base demand decreases by the same
amount and its correct demand increases by that amount. Every other
class and the positive word are unchanged. This proves feasibility
at head $(28+\sigma)/33$ with the same closed cap, including
$\sigma=1$ when that base entry is zero.

A reused unit law $U_{\rm p}$ has the following weighted triples in
$\{1,\ldots,7,\infty\}$:

$$
(1,3,6):2/8,\quad(1,3,7):1/8,\quad(2,4,5):1/8,\quad
(2,7,\infty):2/8,\quad(4,5,\infty):1/8,\quad(4,5,6):1/8.
\tag{242.4}
$$

Select the whole triple, query its two smallest finite indices, stop
at the first queried zero with that label, and on exhaustion emit the
third element ($\infty$ means zero). Each of the eight elements has
inclusion probability $3/8$. At first zero $n$, the output is $n$
exactly when the triple contains it, irrespective of later zeros.
At the positive word output zero has probability $3/8$.
Thus all unit-amplitude rows hold at cap $5/8$; pair follows already
from correct mass $3/8$, and the negative base demand is retained.
This is the existing balanced-triple supplier of §§87 and 176.

For $28/33\le t<1$ set

$$
\nu=\frac{33(1-t)}5,\qquad
\sigma=\frac{5(h-t)}{1-t},\qquad
J(t,h)=\nu J_\sigma+(1-\nu)U_{\rm p}.
\tag{242.5}
$$

Here $0\le\nu,\sigma\le1$ exactly on the first region of (242.2).
This is a convex combination of whole normalized laws on one seed.
The lower endpoint and unit amplitudes mix to $t$; the head increment
is $\nu\sigma/33=h-t$; the cap mixes to
$\nu(17/33)+(1-\nu)(5/8)=e_2(t)$.
All 382 rows are affine on that same mixture. Correct mass equals
$a_n-e_2(t)$ and positive base equals $1-e_2(t)$.
For $t=1$ necessarily $h=1$ and use the unit law directly.
This proves the entire first region.

For the second region use the following different endpoint $K_0$.
All displayed terminal masses have denominator 400, with every cell
summing to its row's schedule mass:

| Schedule | Row mass | Cell $0$ | Cell $10$ | Cell $11$ |
| --- | --- | --- | --- | --- |
| $12$ | 108 | $\{1:108\}$ | $\{2:108\}$ | $\{0:8,6:20,7:80\}$ |
| $13$ | 8 | $\{1:8\}$ | $\{3:8\}$ | $\{0:8\}$ |
| $14$ | 8 | $\{1:8\}$ | $\{4:8\}$ | $\{0:8\}$ |
| $15$ | 15 | $\{1:15\}$ | $\{5:15\}$ | $\{0:8,6:7\}$ |
| $16$ | 8 | $\{1:8\}$ | $\{6:8\}$ | $\{0:8\}$ |
| $23$ | 8 | $\{0:8\}$ | $\{3:8\}$ | $\{0:8\}$ |
| $24$ | 8 | $\{2:8\}$ | $\{4:8\}$ | $\{0:8\}$ |
| $25$ | 15 | $\{2:15\}$ | $\{5:15\}$ | $\{0:8,6:7\}$ |
| $26$ | 8 | $\{2:8\}$ | $\{6:8\}$ | $\{0:8\}$ |
| $34$ | 115 | $\{3:115\}$ | $\{4:115\}$ | $\{0:8,5:93,6:14\}$ |
| $35$ | 8 | $\{3:8\}$ | $\{5:8\}$ | $\{0:8\}$ |
| $36$ | 8 | $\{0:8\}$ | $\{6:8\}$ | $\{0:8\}$ |
| $45$ | 8 | $\{0:8\}$ | $\{5:8\}$ | $\{0:8\}$ |
| $46$ | 8 | $\{4:8\}$ | $\{6:8\}$ | $\{0:8\}$ |
| $56$ | 8 | $\{0:8\}$ | $\{6:8\}$ | $\{0:8\}$ |
| $67$ | 59 | $\{0:8,6:51\}$ | $\{7:59\}$ | $\{0:59\}$ |

The row masses sum to 400. Formula (237.8) gives its full joint law
before replies. Its correct counts are 147 on class one and 139 on
classes two through seven. Explicitly these are

$$
\begin{gathered}
108+8+8+15+8=147,\quad108+8+15+8=139,\\
8+8+115+8=139\quad(n=3,4),\qquad15+15+8+8+93=139,\\
51+5\cdot8+20+7+7+14=139,\qquad59+80=139.
\end{gathered}
$$

As above every contribution is independent of the free suffix.
The base polynomial, obtained by summing the same rows, is

$$
400p^{K_0}_w(0)=8\left[5-\sum_{i=2}^6w_i+\binom{k}{2}\right]+59w_6w_7,
\qquad k=\sum_{i=1}^6w_i.
\tag{242.6}
$$

Every pair among the first six has base eight on exhaustion, $67$ has
base 59 there, and the zero-cell contributions are
$8(1-w_i)$ for $i=2,\ldots,6$. This proves (242.6) on every word.
For class one, $w_1=0$ and the bracket is
$5-k+k(k-1)/2\ge4$. For $n\ge2$, $w_1=1$ and the bracket is
$6-k+k(k-1)/2$, with $k\ge n-1$. Its exact class minima are
$5,5,6,8,11,15$, with the last term zero on suitable suffixes.
The exact base minima are therefore
$(32,40,40,48,64,88,120)$; the positive base is $179$.
Adding correct counts gives pair minima
$(179,179,179,187,203,227,259)$.
At profile $(368,360,360,360,360,360,360)/400$ and cap $221/400$,
correct demands are exactly 147 or 139, pair demand is 179 and
base demands are negative ($-189$ or $-181$). Thus all 382 rows
hold at this endpoint, including every multiple-zero word.

Let $U$ be the reused uniform law on the 56 triples of
$\{1,\ldots,7,\infty\}$ with the same query/output rule as (242.4).
For every first-zero word, $p^U_w(n)=3/8$ by inclusion counting.
Base emission occurs on triples containing $\infty$ whose two finite
indices are positive, so

$$
p^U_w(0)=\frac{\binom{\sum_{i=1}^7w_i}{2}}{56},\qquad
p^U_+(0)=3/8.
\tag{242.7}
$$

This is the existing seven-unit plateau law. For $9/10\le t\le1$ put

$$
B_t=10(1-t)K_0+[1-10(1-t)]U.
\tag{242.8}
$$

Whole-law interpolation gives head $H(t)$, later amplitudes $t$,
cap $e_2(t)$ and positive base $1-e_2(t)$. At any smaller head
$t\le h\le H(t)$ the same $B_t$ works: its correct demand weakens,
its pair demand is unchanged, and $1-h-e_2(t)<0$ so its retained
base demand holds by nonnegativity. Other classes do not change.
Class two still has correct discrepancy exactly $e_2(t)$.

For $H(t)<h\le1$, use the existing saturated-head supplier

$$
D=(1,2;1,0,0),\qquad S_t=tU+(1-t)D.
\tag{242.9}
$$

It has head one, later amplitudes $t$ and cap $e_S=5t/8$.
At class one its correct mass is $1-t+3t/8=1-e_S$;
at every other class it is $3t/8=t-e_S$. $D$ emits only zero or
the actual correct label, while $U$ has outside-pair mass at most
$5/8$, so the independent pair row holds. Base demands are negative
in this region, and positive base is $1-t+3t/8=1-e_S$.
These facts reestablish the required supplier hypotheses without new
saturated-family credit.

For $t<1$ put $\xi=(h-H(t))/(1-H(t))\in(0,1]$ and take the single
whole-law mixture $(1-\xi)B_t+\xi S_t$.
The exact identities controlling its cap are

$$
\begin{aligned}
1-H(t)&=\frac{4(1-t)}5,\qquad
 e_S-e_2(t)=\frac{1-t}{10},\\
 e_2(t)+\xi(e_S-e_2(t))
 &=e_2(t)+\frac{h-H(t)}8
 =\frac{5t+h-1}{8}=e_1(t,h),\\
 e_1(t,h)-e_2(t)&=\frac{h-H(t)}8.
\end{aligned}
\tag{242.10}
$$

Thus the mixture gives exactly the maximum in (242.2), with every
row paid by that same normalized kernel. At $h=H(t)$ the two branches
agree. At $h=1$ use $S_t$; at $t=1$ necessarily $h=1$ and use $U$,
so no division by zero is required. This proves both upper constructions
and all their closed ties.

For the lower bounds, reuse the original all-competitor results
§117.2 at $m=7$ and §113.2, which state respectively

$$
40c\ge4a_2+5\sum_{n=3}^7a_n-4,\qquad
D_3(a,c):=\sum_{n\ge3}(a_n-c)_+\le3c+1-a_1.
\tag{242.11}
$$

The first gives $c\ge e_2(t)$. If an original rule had error below
the claimed optimum, choose an intermediate positive closed cap $c$
below that optimum. The optimum is at most $5t/8<t$, so $c<t$.
The first seven are then active and
$D_3(a,c)\ge5(t-c)$, giving $c\ge e_1(t,h)$.
This keeps all additional positive tail terms in $D_3$; none is removed.
The two inequalities exclude a smaller error in the high full-head
region. In the lower wedge $e_1\le e_2$, so the first alone matches
the construction. These suppliers include all original arbitrary-address
full-carrier N competitors; O has a counted N completion.

For the displayed optimum $e_*$, $0<e_*\le5t/8<t$ and every
allowed tail has $a_n\le e_*$ for $n>7$.
The actual one-seed realization in §243 has low-word error at most
$e_*$ and positive base exactly $1-e_*$. Its actual tail error is
$\max(e_*,a_n)=e_*$, including every equality plateau.
The lower bounds force the attained optimum in both classes.
Larger caps use the same law; smaller caps have no original attainer.
This completes the proof for every entire tail and every closed cap. ∎

At these attained profiles the full mass-one O law and its N completion
supply the same feasible allocations on all rows. For $e_*=e_2$,
the lower hull slack is $4(1-t)/5$ and the upper expression is
$h+4(1-t)/5\le1$. For $e_*=e_1$, the lower slack is $1-h$ and
the upper expression is one. Thus these are actual points of $H_N$,
including closed caps, rather than hull-only tests.
For every full unit-O score $y$, their one actual O probability vector
also gives $F_{Q(y)}(b,e_*)\le\Delta_O(y)\le1$.
This pointwise conclusion does not produce a universal single $V,\theta$.

The first lower cut in (242.11), its seven-coordinate zero-cost score
and its gapped embeddings are owned by §117 and supply no new lower
or zero-cost-direction increment here. The new upper data are the two
explicit endpoint kernels, their head modification and their coupled
interpolation under the exact identities (242.10). The high intersection
of the two constructions is counted once. The unit, saturated-head
and general source-transport suppliers retain their existing ownership.

## 243. Actual source correspondence, shared resources and unresolved comparison

**Definition 243.1 (The original carrier and separately selected targets).**
Let $F_0=0,F_1=1,F_{r+2}=F_{r+1}+F_r$, and let $p_i$ be the
increasing primes. The labeled source and its static replies are

$$
\begin{aligned}
X&=\{(r,g):r\text{ prime},\ g\in\mathbb Z,
       \lceil F_r/10\rceil\le g\le\lfloor F_r/5\rfloor\},\\
N(r,g)&=1+F_rg,\qquad q_i(x)=[p_i\mid N(x)],\qquad
n(x)=\min\{i:q_i(x)=0\}.
\end{aligned}
\tag{243.1}
$$

This is a countable source set with no source prior. Each integer has
finite prime support, so its first absence exists. The finite-pattern
interface of §110.2 and Boundaries 35.2 supplies every prescribed pattern
on finitely many arbitrary prime addresses. Its classical entry-rank
hypothesis permits a sufficiently large prime $r$ with $F_r$ invertible
modulo all specified primes. Prescribe $g=-F_r^{-1}$ modulo primes
whose desired answer is one, and $g=0$ modulo those whose desired
answer is zero. CRT gives a residue modulo their product. A sufficiently
large original Fibonacci window is longer than that product and contains
a representative of that residue. This proves the stated pattern
correspondence under the supplied entry-rank interface; no additional
entry-rank result is inferred here. Witnesses are fixed before seeds.
It includes arbitrary gaps, multiple zeros and an all-one finite prefix
followed by a prescribed later zero. The finite positive word is not
an additional infinite all-positive actual source.

The full tape carrier is the disjoint-union Borel space
$\Theta=\bigsqcup_{j\ge1}B_j\sqcup\bigsqcup_{j\ge1}P_j$,
each block a copy of $(0,1)$. The unchanged consumer returns unknown
on $B_j$ and proposes $j$ on $P_j$. The original nonatomic targets
of Source-Correlated Laws 67.5 remain as follows. For fixed
$0<h_0<1$, put $s(x)=\sum_{i\ge1}3^{-i}q_i(x)$;
let $\nu_x$ have density
$e^{s(x)u}/\int_0^1e^{s(x)v}\,dv$ on $B_{n(x)}$,
let $\pi_j$ be uniform on $P_j$, and let $\Omega(x)$ count the
distinct prime divisors of $N(x)$. Then
$\mu_x=(1-h_0)\nu_x+h_0\pi_{\Omega(x)}$.
These targets, carrier and consumer are unchanged.

The distinct original marks $\theta_j=(B_1,1/(j+2))$, $j\ge0$,
support the separately selected laws

$$
\lambda_x^a=(1-a_{n(x)})\delta_{\theta_0}
                       +a_{n(x)}\delta_{\theta_{n(x)}},\qquad
1\ge a_1\ge a_2\ge\cdots>0,\quad a_n\longrightarrow0.
\tag{243.2}
$$

The optimal errors in §§238, 240–242 concern (243.2).
A finite marked law has TV distance one from each original nonatomic
$\mu_x$: its finite Borel support has masses one and zero respectively.
Selected-law approximation therefore asserts no approximation of the
nonatomic targets and makes no correctness claim for the unchanged
consumer. Original competitors still permit the whole Borel carrier.

For an original rule $A$, its uniform error means
$e_a(A)=\sup_{x\in X}\operatorname{TV}(\mathcal L_U(A(x,U)),\lambda_x^a)$,
where TV is the supremum over all Borel events. The original classes
$\mathcal N_2,\mathcal O_2$ are those of §90.1, with the preselected
schedules, stopping and actual-request requirements stated below.
At the strict active horizon, $\mathcal F_N(a,c)$ denotes the complete
normalized N probability configurations satisfying (237.1), as in
§110.1; $\mathscr C_L$ is the region of normalized kernels represented
by one full O catalog law, identified by §109.1. The intersection in
(243.4) views such stopped kernels through their counted N completions.
The class-preserving equivalence with original feasibility is §110.2.

**Proposition 243.2 (One seed, complete words and closed tails).**
Each normalized table law above is an original zero-advice acquisition
with one source-independent seed and at most two actual requests.
It has finite handoff on every source and seed. The stopped law and
its N completion use the same seed and have identical output laws.
For every actual first absence $n>7$, each constructed seven-coordinate
attainer of cap $e_*$ has exact TV error $e_*$ for every allowed tail,
including $a_8=e_*$ and all later closed ties.

Proof. Partition a single uniform $U\in[0,1)$ into the complete-table
probabilities, using (237.8) for terminal-vector rows and flattening
whole-law mixtures into that one partition. This selects the entire
schedule and all its potential outputs before any replies. Execute the
scheduled prime queries and return its selected original mark.
O uses an increasing preselected schedule and stops at its first queried
zero or exhaustion. N acquires the entire same preselected schedule;
when O would stop after the first reply, N still acquires and ignores
the second reply and reconstructs the stopped output from the same $U$.
This is the counted completion of §90.2. Singleton and empty branches
use at most one and zero requests. No extra coin after answers, source
label, integer value, first absence or source law is observed.
Repeated requests, when present in competitors, and ignored replies
are actual counted requests. There is no free probe, restart, address,
depth, runtime or expected-count replacement for the hard bound.

On an actual low first-zero source its actual Boolean word is one of
all the words verified above, regardless of later zeros. Equation
(237.2) proves its all-Borel TV cap. On a tail source $n>7$, all seven
replies are positive and no mark $\theta_n$ is emitted. More generally,
for any finite law with labels through $H<n$ and positive-cell base
$p_+(0)$, direct calculation on the disjoint marks gives

$$
\begin{aligned}
\operatorname{TV}\left(\sum_{j=0}^Hp_+(j)\delta_{\theta_j},
     (1-a_n)\delta_{\theta_0}+a_n\delta_{\theta_n}\right)
 &=\tfrac12\bigl(|a_n-(1-p_+(0))|+1-p_+(0)+a_n\bigr)\\
 &=\max\{1-p_+(0),a_n\}.
\end{aligned}
\tag{243.3}
$$

Every constructed attainer has $p_+(0)=1-e_*$, and the theorem's
hypotheses retain $0<a_n\le e_*$ for all $n>7$.
Thus (243.3) equals $e_*$ on every actual tail, with no zero-tail
substitution and no exclusion of equality. The first seven amplitudes
strictly exceed $e_*$, so the strict active length at that cap is seven.
All errors are uniform over all actual sources and all Borel events.
Different constructions can use different partitions of the same uniform
seed, or their common finite refinement; this makes no assertion that
different laws have identical seedwise outputs. ∎

The lower bounds use exactly the necessary correspondence of §110.2,
with its original source-independent preselected schedules, source-free
readout, reachable-read discipline and measurable terminal extensions.
For $0<c\le1$ set $L_a=\max(\{i:a_i>c\}\cup\{0\})$.
Countability of $X$ gives one common probability-one seed event of
actual finite handoff and hard request count. The maximum address of
the whole preselected schedule has vanishing seed tails. Before choosing
seeds, the finite-pattern interface supplies actual witnesses for every
finite comparison word. For each finite witness family, sourcewise
almost-sure finite handoff also supplies finite execution cutoffs.
Whole-execution replay on equal acquired transcripts, followed by the
measurable projection fixing low marks and sending other tapes to zero,
produces same-class finite comparisons. One vanishing schedule/execution
error controls the finite family. Compactness of one finite catalog
simplex retains the closed cap in its limit. There is no asserted uniform
address or runtime bound on the original class.

This is the reused arbitrary-address/full-carrier necessity, not a
restriction of original competitors to the displayed tables. The two
horizon operations are those of §207.20: if a score extends beyond
$L_a$, ignore the new coordinates in the one kernel and use (243.3)
on the new first-zero classes; if its horizon is shorter, fix subsequent
finite replies zero and project subsequent labels to zero for the finite
comparison. The latter is a comparison, not an attainer on omitted
active tails. No algebraic operation grants an uncounted observation.
Caps at least one admit immediate base output; equality tails and the
empty active horizon remain included.

All-label legality is essential. The actual source $(r,g)=(19,436)$
has $F_{19}=4181$, $N=1822917$ and replies $0100$ through the first
four prime addresses. The legal N table $(3,4;1,0,0,0)$, in full
cell order, emits earlier unqueried label one on that word. Its
base/correct/pair readings are $(0,1,1)$; replacing that output by
zero gives $(1,0,1)$. No general pruning to zero or queried labels
is used. The score-specific cell maxima and inactive-bit arguments
retain this full original catalog, including multiple zeros.

**Definition 243.3 (Supplier boundaries and remaining universal goal).**
The full-score quotient, signed hull vertices, weak duality and
one-residual budget are owned by §§198–199 and §229.
The 63-charge lower and 14-row low core of §§230–231 are reused;
§238 adds their two-head capacity allocation. The old $\rho=2$
family and its uniform prefix pullback in §§233–235 are reused;
§239 adds higher simultaneous layers from one measure and their exact
signed-cone scope. Its flat displayed eliminated interval gives no
additional lower strength over §240. Sections 240 and 241 give their
full literal cuts, gapped embeddings and the stated attained regions;
the half and $r=1$ endpoints are reused. Section 242 uses the existing
§117 seven-coordinate lower and its gapped zero-cost direction,
§113.2 residual lower, §§87 and 176 unit laws and §§113–114
saturated-head supplier. Its new upper constructions have exactly the
union (242.2), with the high intersection counted once.
General tail transport and kernel realization carry no repeated credit.

The normalized degree-two kernel theorem §109.1 and its
StoppedCoefficientRealization statement require an actual normalized
probability vector on every Boolean word. For
$p_w=c+\sum_i l_iw_i+\sum_{i<j}Q^{\rm ker}_{ij}w_iw_j$, their
coordinate criterion is
$c\ge\sum_i(\sum_{j>i}(-Q^{\rm ker}_{ij})_+-l_i)_+$;
the common scalar schedule-mass bound follows from normalization.
They do not apply to a dual score quotient $Q(V)$.
The PreselectedResidualBound statement requires one common catalog law,
all-word TV bounds, $0\le c$ and the exact strict active cutoff;
it supplies the residual interface of §113.2 under those hypotheses.
These library correspondences are reuse, without a new compiled or
kernel-validated assertion. Exact-law obstruction §112.2 has another
O law at the same cap and remains an exact-law obstruction.

The ordinary finite cell, counting and polynomial arguments supply the
proofs here. Blackwell's *Comparison of Experiments*, §§2–5, compares
common decision rules and risk vectors; a generic postprocessor there
does not supply increasing first-zero schedules with two actual requests.
Kaibel's *Basic Polyhedral Theory*, Theorems 1(ii), 8 and 10, supplies
the finite polyhedral framework, while our vertices and cells retain
the specific original constraints. Zaev's *On the Monge–Kantorovich
Problem with Additional Linear Constraints*, arXiv:1404.4962v1,
Problem 1.3 and Theorem 2.1, uses one joint measure with its specified
marginals and linear constraints; separately optimal rows here are not
such a joint measure. Bertschinger–Rauh, *The Blackwell Relation Defines
No Lattice*, arXiv:1401.3146v1, Example 18, distinguishes conic
representations from stochastic common normalization. These are the
bounded source comparisons of §§213.21 and 219.10, rather than extra
load-bearing hard-two theorems. No exhaustive literature exclusion,
worldwide originality, or semantic nonoverlap with every older convex
consequence is asserted.

The unrestricted positive obligation remains: for every $L\ge3$ and
every actual full $y\ge0$ with $\Delta_O(y)\le1$, produce one
unrestricted full $V\ge0$ and one jointly paid signed residual as in
(237.6). Original competitors have no fixed quotient, law, anchor,
unary, canonical decomposition or positive-only-residual restriction.
The alternative negative obligation still requires the same actual
$(b,e)\in H_N$, one full feasible $\lambda\ge0$ with
$G_N\lambda\ge h(b,e)$ and $M=\sum\lambda\ge1$, an actual
full unit-O $y$, and strict $F_{Q(y)}(b,e)>M$, with the original
source, resource, positive-tail and closed-cap correspondence.
None of the off-$H_N$ detectors or relative cone failures supplies it.

Consequently the comparison for every entire positive nonincreasing
vanishing sequence and every positive closed cap remains open:

$$
\mathcal F_N(a,c)\ne\varnothing
\ \Longrightarrow\
\mathcal F_N(a,c)\cap\mathscr C_{L_a}\ne\varnothing.
\tag{243.4}
$$

The attained families above settle their precise domains. They neither
identify $H_N$ with $H_L$ nor give a universal one-budget certificate
or an original N/O separator.

## 追加锚（本行以下为增补区）

## 244. Joint triple capacities and sharp original attainment

**Definition 244.1 (The capacity domain).** Retain the complete rows,
full catalogs, scores and actual source of §§237 and 243. For an integer
$m\ge5$ choose

$$
0<t\le1,\qquad a_2=a_3=t\ge a_4\ge\cdots\ge a_m>0.
$$

Put

$$
\begin{aligned}
q&=\frac{1-t}{m-2},&S&=\sum_{n=3}^m a_n,&
e&=\frac{S-(m-3)q}{m+1},\\
H&=t+q,&R&=1-e-\binom{m-1}{2}q,&e_S&=\frac S{m+1},\\
d_1=d_2&=t-e-(m-3)q,\\
d_n&=a_n-e-(m-3)q&& (3\le n\le m-2),\\
d_{m-1}&=a_{m-1}-e-(m-3)q-R,&d_m&=a_m-e-R.
\end{aligned}
\tag{244.1}
$$

The capacity hypotheses are exactly

$$
e>0,\qquad R\ge q,\qquad
 a_n\ge t-\binom{n-2}{2}q\ (2\le n\le m),\qquad
0\le d_n\le e\ (1\le n\le m).
\tag{244.2}
$$

Choose any $h\in[t,1]$, set $a_1=h$ and define

$$
e_*(h)=\max\left\{e,\frac{S+h-1}{m+1}\right\}.
\tag{244.3}
$$

Append any entire positive nonincreasing vanishing sequence of actual
tail amplitudes with $a_{m+1}\le e_*(h)$. These are sufficient
hypotheses on the selected marked targets, without restrictions on the
original competitors.

**Theorem 244.2 (Joint capacity gives the attained original optimum).**
Under (244.1)–(244.2),

$$
0<e_*(h)\le e_S<a_m,\qquad
E_{\mathcal N}(2;a)=E_{\mathcal O}(2;a)=e_*(h).
\tag{244.4}
$$

Both infima are attained. One original stopped law and its counted N
completion use the same source-independent seed and return the same
tape at every source and seed. For every positive closed cap $c$, either
original class is feasible exactly when $c\ge e_*(h)$. Every actual tail
source has error exactly $e_*(h)$, including all closed tail ties.
For $e_*(h)\le c\le e_S$, the exhibited full mass-one allocations
witness $(h,t,t,a_4,\ldots,a_m;c)\in H_N\cap H_O$.

Proof. The definitions imply

$$
\sum_{n=1}^m d_n=3e,\qquad 1-H=(m-3)q,\qquad
 e_S-e=\frac{(m-3)q}{m+1}.
\tag{244.5}
$$

For example, the degree sum before substitution is
$2t+S-me-(m-1)(m-3)q-2R$; using
$2\binom{m-1}{2}=(m-1)(m-2)$ and
$S=(m+1)e+(m-3)q$ reduces it to $3e$.
If $q>0$, $d_m\ge0$ and $R\ge q$ give
$a_m\ge e+R>e+(m-3)q/(m+1)=e_S$.
If $q=0$, $t=1$ and the amplitude floors force all $a_2,\ldots,a_m$
to be one; then $e=e_S=(m-2)/(m+1)<a_m$.
Thus $e<t$, $t\le H\le1$, and (244.3) is $e$ below $H$ and
$(S+h-1)/(m+1)$ above $H$.

Use the rank-three hypersimplex fact to obtain one nonnegative measure
$x_T$ on three-subsets of $[m]$ with total $e$ and degrees $d_n$.
Here is a complete finite construction of that mature fact. Divide the
degrees by $e$, partition $[0,3)$ into consecutive half-open intervals
$I_n$ of lengths $d_n/e\le1$, and, for $z\in[0,1)$, let $T(z)$ be
the labels of the intervals containing $z,z+1,z+2$. They are distinct:
one half-open interval of length at most one cannot contain two of
these points. Set $x_T=e\,|\{z:T(z)=T\}|$. For each $n$, its inclusion
measure is
$\sum_{j=0}^2|\{z\in[0,1):z+j\in I_n\}|=|I_n|=d_n/e$.
Hence the degrees and total are as required. The finitely many interval
endpoint residues modulo one give finitely many constant choices of
$T$. This defines coefficients, not an additional acquisition seed.

Construct first the head-$H$ law. For each $i<j$, set

$$
\begin{aligned}
b_{ij}&=q&& (1\le i<j\le m-1),&b_{m-1,m}&=R,\\
c_{i,i+1}&=q&& (2\le i\le m-1),&
w_{ij}&=b_{ij}+\sum_{k>j}x_{\{i,j,k\}},
\end{aligned}
\tag{244.6}
$$

with other $b,c$ zero. Using $\mathbf e_r$ for unit output mass,
give the pair $(i,j)$ its three unnormalized stopped cell vectors

$$
\begin{aligned}
u^0_{ij}&=c_{ij}\mathbf e_0+(w_{ij}-c_{ij})\mathbf e_i,\\
u^{10}_{ij}&=w_{ij}\mathbf e_j,\\
u^{11}_{ij}&=b_{ij}\mathbf e_0+
                           \sum_{k>j}x_{\{i,j,k\}}\mathbf e_k.
\end{aligned}
\tag{244.7}
$$

Every vector is nonnegative, including the final transfer because
$R\ge q$. All three vectors in a row have the same mass $w_{ij}$,
and their schedule masses sum to
$\binom{m-1}{2}q+R+\sum_Tx_T=1$.
For $w_{ij}>0$ the whole deterministic output triple $(r_0,r_{10},r_{11})$
has mass
$u^0_{ij}(r_0)u^{10}_{ij}(r_{10})u^{11}_{ij}(r_{11})/w_{ij}^2$.
Summation recovers every cell vector and total schedule mass.
Zero rows are omitted. This is one full normalized law with all
counterfactual outputs fixed together, using the realization of §§109,
176 and 237.2.

A numerical triple $i<j<k$ emits the actual first-zero label $n$ exactly
when $n$ belongs to the triple: its selected preceding queries are
positive, including when $n=k$ is the unqueried exhaustion guess.
This holds with every suffix. Base-edge degrees are $(m-2)q$ through
$m-2$, $(m-2)q+R$ at $m-1$, and $R$ at $m$. First-cell transfers
subtract $q$ exactly at $2,\ldots,m-1$. Consequently (244.7) gives

$$
p_w(n)=a_n-e\quad(2\le n=n(w)\le m),\qquad
p_w(1)=H-e\quad(n(w)=1).
\tag{244.8}
$$

For an arbitrary Boolean word put $k=\sum_{i=1}^{m-1}w_i$.
Summing base contributions in this same law gives the exact polynomial

$$
p_w(0)=q\left[m-2-\sum_{i=2}^{m-1}w_i+\binom{k}{2}\right]
                         +R w_{m-1}w_m.
\tag{244.9}
$$

At first zero one, its bracket is $m-2-k+\binom{k}{2}\ge m-3$,
so $p_w(0)\ge1-H$. At first zero $n\ge2$, $w_1=1$ and
$k\ge n-1$; the bracket is
$m-1-k+\binom{k}{2}$ and is at least
$m-2+\binom{n-2}{2}$. For $n=2$ the tied minima are $k=1,2$;
for later $n$ the expression increases from $k=n-1$.
The amplitude floors therefore give $p_w(0)\ge1-a_n$.
Together with (244.8), these prove the base, correct and independent
pair rows separately: in particular $p_w(0)+p_w(n)\ge1-e$.
The literal base demand is $1-a_n-e$, even when negative.
At $1^m$, the base is $\sum b_{ij}=1-e$. Each zero-word correct
event has deficit $e$, so (237.2) gives exact TV $e$.

For $t\le h\le H$, in every first-query-one zero cell transfer the
fraction $(H-h)/(H-e)$ of its label-one mass to base. This fraction
lies in $[0,1]$ since $h\ge t>e$. All correct-one mass is in these
cells; the total transfer on every first-zero-one word is $H-h$.
Its correct mass becomes $h-e$, its base is at least $1-h$, and its
pair mass stays fixed. Every other word law and the positive law stay
fixed. Thus all rows hold at $e_*(h)=e$.

For $H<h\le1$, reuse §113.3 at head one and cap $e_S$.
To specify its whole law, put $r_n=a_n-e_S$ for $n\ge2$,
$r_{m+1}=0$. For $3\le k\le m$ give the uniform triple rule on
$\{1,\ldots,k,\infty\}$ mass
$v_k=(k+1)(r_k-r_{k+1})/3$. It queries the two smallest numerical
indices, returns a queried first zero, and otherwise its third label;
$\infty$ means zero. Telescoping gives

$$
\sum_{k=3}^m v_k=r_3+e_S=t,\qquad
\sum_{k=3}^m v_k\frac{k-2}{k+1}=e_S.
\tag{244.10}
$$

Put mass $1-t$ on $(1,2;1,0,0)$. Triple inclusion gives correct
mass $a_n-e_S$ for $n\ge2$ and $1-e_S$ at head one. The second
identity bounds outside-pair mass by $e_S$ on every word, so base
is at least $1-a_n$ and the independent pair probability at least
$1-e_S$. Positive base is $1-e_S$.
These are the residual supplier's actual common masses, without an
error constraint on individual branches.

For $q>0$, mix this whole saturated law with the head-$H$ law,
using saturated weight $\xi=(h-H)/(1-H)$. Equations (244.5) give

$$
(1-\xi)e+\xi e_S=e+\frac{h-H}{m+1}
                         =\frac{S+h-1}{m+1}.
\tag{244.11}
$$

All independent rows are affine in this one kernel, amplitudes and cap.
Correct masses are $a_n-e_*(h)$ and positive base is $1-e_*(h)$.
At $q=0$ only $h=H=1$ occurs and no division is used. This includes
all closed heads, zero masses and equal capacities.

Flatten the complete-table probabilities and the outer mixture into
one partition of a source-independent uniform seed. Execute the selected
increasing actual prime schedule and emit the original mark. Its counted
N completion uses that same table and seed and returns the same tape.
The construction has at most two actual requests and finite handoff on
every source and seed, as in §243.2. At any actual first absence $n>m$
the law is the positive-word law and has no output $n$. Its exact error is
$\max\{1-p_+(0),a_n\}=\max\{e_*(h),a_n\}=e_*(h)$ by (243.3).
Thus all positive actual tails and equality tails are retained.

For the matching lower bounds, §117.2 gives, against every original
arbitrary-address full-carrier N competitor,

$$
c\ge\frac{(m-3)t+(m-2)S-(m-3)}{(m-2)(m+1)}=e.
\tag{244.12}
$$

At any positive feasible cap $c<a_m$, §113.2 gives
$S-(m-2)c\le D_3(a,c)\le3c+1-h$, hence
$c\ge(S+h-1)/(m+1)$. If an original rule had error below $e_*(h)$,
choose an intermediate positive closed cap below $e_*(h)<a_m$.
These two bounds contradict that cap. Additional active tail terms
only strengthen the residual bound. Counted O completion gives the
same lower bound for O. This proves attained optimality and every
positive closed-cap threshold.

Finally, for $e_*(h)\le c\le e_S$, order, $b_2=b_3$,
$(m+1)c\le S$, and $h+S-(m+1)c\le1$ give hull membership.
The same full probability allocation meets every row at $c$, and its
completion supplies the N allocation. This proves actual feasible
membership, not just a hull inequality. For every full $y\ge0$ the same
allocation gives $F_{Q(y)}(b,c)\le\Delta_O(y)$, and in particular at
most one for every unit-O score. ∎

## 245. Explicit capacity subregions and unequal eight-coordinate laws

**Corollary 245.1 (High flat profiles at every length).** Set
$P_m=m^3-4m^2+7m+2$ and $t_m=1-6(m-2)/P_m$ for $m\ge5$.
For $t_m\le t\le1$, $t\le h\le1$, $a_1=h$ and
$a_2=\cdots=a_m=t$, the attained original optimum of both classes is

$$
e_* =\max\left\{
\frac{(m^2-3m+1)t-(m-3)}{(m-2)(m+1)},
\frac{(m-2)t+h-1}{m+1}\right\}.
\tag{245.1}
$$

Every entire positive nonincreasing vanishing tail with
$a_{m+1}\le e_*$ is allowed. The positive closed-cap threshold is
$e_*$, with the same-seed attainers of Theorem 244.2.

Proof. Each capacity inequality is affine in $\delta=1-t$, and the
amplitude floors are automatic. At $\delta=0$,
$e=(m-2)/(m+1)$, $R=3/(m+1)$, $q=0$; the first $m-2$ degrees are
$3/(m+1)$ and the last two zero. At $\delta=6(m-2)/P_m$,

$$
\begin{aligned}
q=R&=6/P_m,& e&=(m-1)(m^2-6m+10)/P_m,\\
d_A&=3(m^2-7m+14)/P_m,&d_B&=3(m-3)(m-4)/P_m,\\
d_C&=3(m-2)(m-3)/P_m,\\
e-d_A&=(m-4)(m^2-6m+13)/P_m,\\
e-d_B&=(m-4)(m^2-6m+13)/P_m+6/P_m,\\
e-d_C&=(m-4)(m^2-6m+7)/P_m.
\end{aligned}
\tag{245.2}
$$

Here $d_A$ is repeated $m-2$ times. All displayed quantities requiring
positivity are positive for $m\ge5$, and $R-q=0$ at this endpoint.
Affinity proves (244.2) throughout the interval. Substitution in
Theorem 244.2 proves the result for all lengths and real parameters.
The thresholds at $m=5,6,7,8$ are $22/31,23/29,28/33,139/157$.
The five- and six-active comparisons belong to §§148 and 161; the
flat-seven lower-head construction belongs to §242, and its upper-head
extension follows from (244.11) and the old saturated supplier.
The unit and saturated-head endpoints retain §§87, 113–114 ownership. ∎

**Corollary 245.2 (A nested near-unit domain).** For $m\ge7$, choose

$$
0\le\tau\le6/P_m,\quad t=1-(m-2)\tau,\quad
z_2=z_3=0,\quad0\le z_4\le\cdots\le z_m\le\tau.
\tag{245.3}
$$

Set $a_1=h\in[t,1]$, $a_n=t-z_n$ for $2\le n\le m$,
$S=\sum_{n=3}^m a_n$. The exact attained optimum of both original
classes is
$e_* =\max\{[S-(m-3)\tau]/(m+1),(S+h-1)/(m+1)\}$,
for every permitted entire actual tail $a_{m+1}\le e_*$ and every
positive closed cap as in Theorem 244.2.

Proof. Put $Z=\sum_{n=3}^m z_n$, and use subscript $f$ for the flat
values at this $t$. Set

$$
B=\frac{(m-3)(m-4)\tau}{2},\qquad
C=\frac{(m-2)(m-3)\tau}{2},\qquad
A=t-e-(m-3)\tau.
$$

The capacity degrees are $A-z_n$ through $m-2$ (with $z_1=0$),
$B-z_{m-1}$ and $C-z_m$. Direct substitution gives

$$
R_f-\tau=\frac{6-P_m\tau}{2(m+1)}\ge0,\quad
R=R_f+\frac Z{m+1},\quad A=R_f+B+\frac Z{m+1}.
\tag{245.4}
$$

Since $B\ge6\tau$, $C\ge10\tau$ and $z_n\le\tau$, all degrees
are nonnegative. For their upper bounds,

$$
\begin{aligned}
e-A&=\frac{(m-5)+(3m-7)\tau-2Z}{m+1}>0,\\
e-C&\ge\frac{(m-1)(m-5)(m^2-3m-2)}{(m+1)P_m}>0.
\end{aligned}
\tag{245.5}
$$

The first uses $Z\le(m-3)\tau$. The second follows by substituting
that same bound and $\tau\le6/P_m$ in $e-C$; its numerator
factorization is
$(m-2)P_m-3(m^3-2m^2-3m+2)=(m-1)(m-5)(m^2-3m-2)$.
Because $B\le C$, these bound every degree above by $e$ and imply
$e>0$. The amplitude floors follow from
$z_n\le\tau\le\binom{n-2}{2}\tau$ for $n\ge4$, with equalities
at two and three. Thus all hypotheses of Theorem 244.2 hold.
This is a subregion of that theorem, with no independent capacity
principle. The alternative transfer layout $c_{i,m-1}=\tau$ for
$2\le i\le m-2$ and $c_{m-1,m}=\tau$ has the same first-index
transfer totals, base polynomial and proof. ∎

For example, $m=8$, $\tau=3/157$, $h=142/157$,
$t=139/157$ and $z_4=\cdots=z_8=3/157$ give

$$
a=(142,139,139,136,136,136,136,136)/157,\qquad e_*=268/471,
$$

with degrees $(104,104,104,95,95,95,81,126)/471$.
Equations (244.6)–(244.7), with the finite interval triple measure,
specify every cell of a complete law at this point. Any actual tail
below $268/471$ is allowed, including equality at coordinate nine.

An explicit law at this same point uses the alternative transfer layout
of Corollary 245.2. Put $k=3/157$ and define the following unnormalized
exhaustion vectors:

$$
\begin{aligned}
E_{13}&=k\mathbf e_0+\frac{671}{55107}\mathbf e_6
 +\frac{1903}{140829}\mathbf e_7+\frac{26642}{1267461}\mathbf e_8,\\
E_{14}&=k\mathbf e_0+\frac{237595}{12343968}\mathbf e_6
 +\frac{673835}{31545696}\mathbf e_7
 +\frac{673835}{20279376}\mathbf e_8,\\
E_{16}&=k\mathbf e_0+\frac{2091}{202216}\mathbf e_7
 +\frac{697}{43332}\mathbf e_8,\\
E_{34}&=k\mathbf e_0+\frac{28975}{2057328}\mathbf e_6
 +\frac{82175}{5257616}\mathbf e_7+\frac{82175}{3379896}\mathbf e_8,\\
E_{36}&=k\mathbf e_0+\frac{765}{101108}\mathbf e_7
 +\frac{85}{7222}\mathbf e_8.
\end{aligned}
\tag{245.5a}
$$

In the table below $w$ is the schedule mass in that row; its occurrence
in a cell denotes that same mass. These are all twenty-two schedules.

| Pair | $w$ | Cell $0$ | Cell $10$ | Cell $11$ |
| --- | ---: | --- | --- | --- |
| $12$ | $k$ | $k\mathbf e_1$ | $k\mathbf e_2$ | $k\mathbf e_0$ |
| $13$ | $31/471$ | $w\mathbf e_1$ | $w\mathbf e_3$ | $E_{13}$ |
| $14$ | $4903/52752$ | $w\mathbf e_1$ | $w\mathbf e_4$ | $E_{14}$ |
| $15$ | $4903/52752$ | $w\mathbf e_1$ | $w\mathbf e_5$ | $E_{14}$ |
| $16$ | $1201/26376$ | $w\mathbf e_1$ | $w\mathbf e_6$ | $E_{16}$ |
| $17$ | $k$ | $k\mathbf e_1$ | $k\mathbf e_7$ | $k\mathbf e_0$ |
| $23$ | $31/471$ | $w\mathbf e_2$ | $w\mathbf e_3$ | $E_{13}$ |
| $24$ | $4903/52752$ | $w\mathbf e_2$ | $w\mathbf e_4$ | $E_{14}$ |
| $25$ | $4903/52752$ | $w\mathbf e_2$ | $w\mathbf e_5$ | $E_{14}$ |
| $26$ | $1201/26376$ | $w\mathbf e_2$ | $w\mathbf e_6$ | $E_{16}$ |
| $27$ | $k$ | $k\mathbf e_0$ | $k\mathbf e_7$ | $k\mathbf e_0$ |
| $34$ | $643/8792$ | $w\mathbf e_3$ | $w\mathbf e_4$ | $E_{34}$ |
| $35$ | $643/8792$ | $w\mathbf e_3$ | $w\mathbf e_5$ | $E_{34}$ |
| $36$ | $169/4396$ | $w\mathbf e_3$ | $w\mathbf e_6$ | $E_{36}$ |
| $37$ | $k$ | $k\mathbf e_0$ | $k\mathbf e_7$ | $k\mathbf e_0$ |
| $45$ | $k$ | $k\mathbf e_4$ | $k\mathbf e_5$ | $k\mathbf e_0$ |
| $46$ | $k$ | $k\mathbf e_4$ | $k\mathbf e_6$ | $k\mathbf e_0$ |
| $47$ | $k$ | $k\mathbf e_0$ | $k\mathbf e_7$ | $k\mathbf e_0$ |
| $56$ | $k$ | $k\mathbf e_5$ | $k\mathbf e_6$ | $k\mathbf e_0$ |
| $57$ | $k$ | $k\mathbf e_0$ | $k\mathbf e_7$ | $k\mathbf e_0$ |
| $67$ | $k$ | $k\mathbf e_0$ | $k\mathbf e_7$ | $k\mathbf e_0$ |
| $78$ | $14/471$ | $k\mathbf e_0+(5/471)\mathbf e_7$ | $w\mathbf e_8$ | $w\mathbf e_0$ |

For a direct ordinary verification, subtract base mass $k$ from each
$11$ cell inside $[7]$, and base mass $14/471$ on $78$.
The remaining masses are numerical triples, with total $268/471$
and inclusion degrees $(104,104,104,95,95,95,81,126)/471$.
For example, each term at label $r$ in $E_{ij}-k\mathbf e_0$
is the mass of triple $\{i,j,r\}$. Summing the displayed fractions
gives exactly those eight degrees. The base edges and transfers are
precisely the alternative layout of Corollary 245.2. Thus its all-word
correctness and base-polynomial proof applies verbatim to this law.
Every cell has its printed schedule mass, those masses sum to one,
and the whole-table coupling (244.7) fixes all counterfactual outputs
using the same source-independent seed. No additional feasibility
claim is attributed to this explicit instance.

**Corollary 245.3 (An unequal eight-coordinate continuum).** For
$0\le x\le1/200$, $9/10\le h\le1$, take

$$
a=(h,9/10,9/10,9/10-x,9/10-2x,9/10-3x,
                           9/10-4x,9/10-5x,\ldots).
$$

For every entire permitted actual tail, the exact attained optimum is

$$
e_*(x,h)=\max\left\{\frac{319}{540}-\frac{5x}{3},
                            \frac{22/5+h-15x}{9}\right\},
\qquad a_9\le e_*(x,h).
\tag{245.6}
$$

Proof. Here $q=1/60$, $R=8/135+5x/3$, $H=11/12$,
$e=319/540-5x/3$, $e_S=3/5-5x/3$, and the eight degrees are

$$
\left(\frac{61}{270}+\frac{5x}3,
\frac{61}{270}+\frac{5x}3,\frac{61}{270}+\frac{5x}3,
\frac{61}{270}+\frac{2x}3,\frac{61}{270}-\frac{x}3,
\frac{61}{270}-\frac{4x}3,\frac16-4x,\frac14-5x\right).
\tag{245.7}
$$

Their sum is $3e$; they are positive and at most $1/4$, while
$e\ge629/1080>1/2$. Each amplitude floor follows from
$(n-3)x\le\binom{n-2}{2}/60$. Thus Theorem 244.2 applies,
including $x=0$, all heads and every actual equality tail. ∎

**Proposition 245.4 (Two explicit unequal cores).** The following
prefixes have attained optimum in both original classes at the printed
cap, for every permitted entire actual tail bounded by that cap:

$$
\begin{aligned}
a^{(A)}&=(11/12,9/10,9/10,9/10,179/200,89/100,177/200,22/25),
&e_A&=79/135,\\
a^{(B)}&=(23/24,19/20,19/20,91/96,227/240,151/160,113/120,451/480),
&e_B&=2701/4320.
\end{aligned}
\tag{245.8}
$$

Proof. For A, $q=1/60$, $R=7/108$, $H=11/12$, and the degrees are
$(25/108,25/108,25/108,25/108,1223/5400,299/1350,91/600,23/100)$.
One common numerical triple measure is

| Triple | Mass |
| --- | ---: |
| $123$ | $25/108$ |
| $458$ | $119/900$ |
| $467$ | $67/675$ |
| $568$ | $377/5400$ |
| $678$ | $151/5400$ |
| $567$ | $11/450$ |

Its total is $79/135$ and its eight inclusion degrees are exactly the
listed values. They belong to $[0,e_A]$, $R\ge q$, and each floor
in (244.2) holds by substitution. Equations (244.6)–(244.7) now give
all terminal vectors and their whole-table probabilities.
For B, $q=1/120$, $R=863/4320$, $H=23/24$, and the degree numerators
over 4320 are $(1223,1223,1223,1214,1205,1196,324,495)$.
They sum to 8103, each lies between zero and 2701, and all floors
hold. The interval construction in Theorem 244.2 supplies a finite
triple measure and therefore the complete law, without an optimizer
existence assumption. The theorem proves both claims.
Neither A nor B is required to lie on the line (245.6).
The tails $a_{8+j}=e_A2^{1-j}$ and $a_{8+j}=e_B2^{1-j}$,
respectively, give concrete entire sequences with a closed first tie. ∎

## 246. A complementary unequal-seven sufficient region

**Definition 246.1 (Affine terminal stocks).** Choose
$0<z\le w\le v\le u\le t\le1$ and put

$$
\begin{aligned}
k&=(1-t)/5,&S&=t+u+v+w+z,\\
e&=\frac{9t+5(u+v+w+z)-4}{40},&h_0&=(1+4t)/5,\\
A&=6k+(t-v+z)/2-e,&B&=e+(t-v-z)/2,\\
C&=v-8k-e,&D&=(t+v-z)/2-8k,\\
F&=2e-1+3k,&G&=(u-w)/2-k,\\
H&=t-v-2k,&I&=e+(u+v-w-z-t)/2-3k.
\end{aligned}
\tag{246.1}
$$

These letters are terminal masses, distinct from the full score
coordinates. Define the region $\mathcal P$ by all of

$$
\begin{gathered}
e>0,\quad e\ge k,\quad S/8<z,\\
A\ge k,\quad B\ge k+G,\quad C\ge0,\quad D\ge H+I,\quad
F\ge k,\quad G\ge0,\quad H\ge k,\quad I\ge0,\\
u\ge v+2k,\qquad w\ge v-3k,\qquad z\ge v-7k.
\end{gathered}
\tag{246.2}
$$

**Theorem 246.2 (Exact original optimum throughout the region).**
For every tuple in $\mathcal P$, every $t\le h\le1$, and
$a_1=h,a_2=a_3=t,a_4=u,a_5=v,a_6=w,a_7=z$, put

$$
e_* =\max\{e,(h+S-1)/8\}.
\tag{246.3}
$$

For every entire positive nonincreasing vanishing actual tail with
$a_8\le e_*$, both original hard-two classes have attained optimum
$e_*$. Each is feasible at a positive closed cap exactly when that
cap is at least $e_*$. The stopped attainer and its counted N completion
use the same seed and tape on every source. The strict active horizon
at the optimum is seven, since $0<e_*\le S/8<z$.

Proof. At head $h_0$, use the following unnormalized terminal vectors.
Each entry $a\mathbf e_r$ means mass $a$ at actual label $r$;
unlisted schedules have zero mass.

| Pair | Cell $0$ | Cell $10$ | Cell $11$ |
| --- | --- | --- | --- |
| $12$ | $k\mathbf e_1$ | $k\mathbf e_2$ | $k\mathbf e_0$ |
| $13$ | $A\mathbf e_1$ | $A\mathbf e_3$ | $k\mathbf e_0+(A-k)\mathbf e_7$ |
| $14$ | $B\mathbf e_1$ | $B\mathbf e_4$ | $k\mathbf e_0+G\mathbf e_5+(B-k-G)\mathbf e_6$ |
| $15$ | $k\mathbf e_1$ | $k\mathbf e_5$ | $k\mathbf e_0$ |
| $16$ | $k\mathbf e_1$ | $k\mathbf e_6$ | $k\mathbf e_0$ |
| $17$ | $C\mathbf e_1$ | $C\mathbf e_7$ | $C\mathbf e_0$ |
| $23$ | $D\mathbf e_2$ | $D\mathbf e_3$ | $H\mathbf e_0+I\mathbf e_4+(D-H-I)\mathbf e_5$ |
| $24$ | $k\mathbf e_0+(A-k)\mathbf e_2$ | $A\mathbf e_4$ | $k\mathbf e_0+(A-k)\mathbf e_7$ |
| $25$ | $k\mathbf e_2$ | $k\mathbf e_5$ | $k\mathbf e_0$ |
| $26$ | $k\mathbf e_2$ | $k\mathbf e_6$ | $k\mathbf e_0$ |
| $34$ | $k\mathbf e_0$ | $k\mathbf e_4$ | $k\mathbf e_0$ |
| $35$ | $k\mathbf e_3$ | $k\mathbf e_5$ | $k\mathbf e_0$ |
| $36$ | $k\mathbf e_3$ | $k\mathbf e_6$ | $k\mathbf e_0$ |
| $45$ | $k\mathbf e_0$ | $k\mathbf e_5$ | $k\mathbf e_0$ |
| $46$ | $F\mathbf e_4$ | $F\mathbf e_6$ | $k\mathbf e_0+(F-k)\mathbf e_7$ |
| $56$ | $k\mathbf e_0$ | $k\mathbf e_6$ | $k\mathbf e_0$ |
| $67$ | $k\mathbf e_0$ | $k\mathbf e_7$ | $k\mathbf e_0$ |

Every terminal mass is nonnegative by (246.2). The three cell sums
are the same within each row, and the seventeen schedule masses sum to
$11k+2A+B+C+D+F=1$. Formula (237.8) therefore specifies one common
probability distribution on full deterministic tables.
Every numerical exhaustion guess is later than both queries.
Summing correct contributions on an entire first-zero class gives,
independently of all suffix zeros,

$$
\begin{aligned}
(p_w(n))_{n=1}^7
={}&(3k+A+B+C,\ 2k+A+D,\ 2k+A+D,\ A+B+k+F+I,\\
 &4k+G+D-H-I,\ 3k+F+B-G,\ C+2A+F-2k)\\
={}&(h_0,t,t,u,v,w,z)-e(1,1,1,1,1,1,1).
\end{aligned}
\tag{246.4}
$$

This counts the unqueried exhaustion labels as well as queried outputs.
For an arbitrary word let $r=\sum_{i=1}^6 w_i$. The same rows give

$$
p_w(0)=k\left[5-\sum_{i=2}^6w_i+\binom r2+w_6w_7\right]
                        +(H-k)w_2w_3+Cw_1w_7.
\tag{246.5}
$$

The first-cell base terms come from $24,34,45,56,67$.
Every pair inside $[6]$ has base exhaustion mass $k$, except $23$,
whose base is $H$; the other base edges are $17$ and $67$.
This proves the identity on every word.

Since $H-k,C\ge0$, the first-zero-one base is at least $4k$:
its bracket is $5-r+\binom r2+w_6w_7\ge4$.
For $n\ge2$, $w_1=1$ and $r\ge n-1$, so the core bracket is
$6-r+\binom r2$. Its minima for $n=2,\ldots,7$ are
$5,5,6,8,11,15$. For $n\ge4$, $w_2w_3=1$ forces the extra
$H-k$. Hence the seven base lower bounds are

$$
(4k,5k,5k,5k+H,7k+H,10k+H,14k+H).
\tag{246.6}
$$

They dominate $1-(h_0,t,t,u,v,w,z)$: classes one, two, three and five
are equalities; the other three comparisons are precisely the last
line of (246.2). Thus correct is amplitude minus $e$, base is at least
one minus amplitude, and their independent pair sum is at least $1-e$.
The original base demand $1-a_n-e$ remains in force, including negative
values. At the positive word the base is $15k+C+H=1-e$.
All 382 independent rows hold and correct deficit gives exact low-word
TV $e$ at head $h_0$.

For $t\le h\le h_0$, keep this whole law. Head correctness exceeds
its new demand, and the pair demand is unchanged. The base demand is
paid because $1-h-e\le5k-e\le4k$. Class two still has exact deficit
$e$. For $h>h_0$, use the head-one supplier of §113.3 at $e_S=S/8$.
All seven amplitudes exceed $e_S$, and
$\sum_{n=3}^7(a_n-e_S)=3e_S$. Its explicit uniform-triple masses
are those of (244.10), with $m=7$, plus mass $1-t$ on $(1,2;1,0,0)$.
It satisfies all rows and has positive base $1-e_S$.
The exact identities

$$
1-h_0=4k,\qquad e_S-e=k/2
\tag{246.7}
$$

give saturated mixture weight $(h-h_0)/(4k)$ and mixed cap
$e+(h-h_0)/8=(h+S-1)/8$. Every row uses this same whole mixture.
At $k=0$, $t=h=h_0=1$ and there is no division. All closed stock,
head and mixture endpoints are included.

For every original competitor, §117.2 at $m=7$ requires
$40c\ge4t+5S-4=40e$. Section 113.2 at any smaller positive cap
$c<z$ requires $8c\ge h+S-1$. Since $e_*\le S/8<z$, an
intermediate positive cap below $e_*$ contradicts these necessary
bounds. They retain all arbitrary-address full-carrier competitors and
all positive tail residuals. The whole law above, executed on the actual
source using one seed, attains $e_*$; its positive base is $1-e_*$.
Every actual $n>7$ has exact error $\max\{e_*,a_n\}=e_*$ by (243.3).
Counted same-seed N completion gives the other attainer. This proves
both optima and all positive closed-cap assertions. ∎

For every $L\ge7$, pad this finite profile by $e_*$ through coordinate
$L$. The same law ignores the added bits and emits no added label.
New first-zero classes have base and pair at least $1-e_*$ and correct
demand zero. Thus it is a full mass-one feasible O allocation at that
same padded point, and its N completion supplies the N allocation.
The hull inequalities reduce to $8e_*\le S$ and
$h+S-8e_*\le1$. For every full unit-O $y$, the same allocation gives
$F_{Q(y)}\le\Delta_O(y)\le1$ there. This is a pointwise consequence.

**Proposition 246.3 (A closed nonempty region and noncontainment).**
The independent closed box of radius $1/1000$ about

$$
(t,u,v,w,z)=(9/10,17/20,4/5,3/4,7/10)
\tag{246.8}
$$

belongs to $\mathcal P$. At its center, $h=h_0=23/25$, $e_*=49/100$,
and the stocks $(k,A,B,C,D,F,G,H,I)$ are
$(1/50,3/100,19/100,3/20,17/50,1/25,3/100,3/50,2/25)$.
The region (246.2) and the capacity region (244.2) do not contain one
another.

Proof. Every defining inequality is affine in the five box parameters.
For an affine form its minimum on this box is its central value minus
$\sum|\text{nonconstant coefficients}|/1000$. The terminal-stock
slacks are positive; the smallest is $A-k\ge321/40000$.
The final three slacks are at least $19/2500,37/5000,183/5000$,
respectively. Also $e\ge19571/40000$, $k\le101/5000$,
$S/8\le801/1600<699/1000\le z$; order gaps remain positive.
These calculations prove the whole closed box, not only its center.

At the center, the capacity floor at coordinate four would require
$u\ge t-k=22/25$, whereas $u=17/20$. Its capacity degree at six is
also $3/4-49/100-4/50-21/100=-3/100$. Thus an actual feasible law of
Theorem 246.2 lies outside the stated capacity hypotheses.
Conversely a flat capacity-seven point with $28/33\le t<1$ has
$u=w=t$ and $G=-k<0$, outside (246.2). These witnesses establish
noncontainment of the stated sufficient regions; they do not assert
that the regions are disjoint or prohibit a larger unifying theorem. ∎

## 247. Bounded comparisons with lower-dimensional suppliers

**Proposition 247.1 (An affine bound preserved by residual extension).**
Write $E(a,c)=D_3(a,c)-3c$. Every feasible core with at most six active
coordinates satisfies

$$
E(a,c)\le\tfrac34(1-a_2).
\tag{247.1}
$$

The family of §187 has the stronger coefficient $2/3$.
Any finite sequence of the residual extensions of §173 preserves each
of these bounds. At a fixed prefix of length $L$, convex mixtures of
such extended data satisfy

$$
\sum_{n=3}^L a_n-(L+1)c\le\tfrac34(1-a_2).
\tag{247.2}
$$

Proof. If the active length is $k\in\{3,4,5,6\}$, pad inactive finite
amplitudes to $c$ through coordinate six. The ignored-bit extension
retains every cap row, and §117.2 at six gives
$3a_2+4\sum_{n=3}^6a_n-3\le28c$, equivalent to (247.1).
For length below three, $E\le0$. Section 187.2 gives
$E=r/10$, $1-a_2=3r/20$, proving its coefficient $2/3$, including
$r=0$. Section 174.2 multiplies $E$ and $1-a_2$ by the same
nonnegative core coefficient under each residual extension. This proves
preservation by finite iteration. For actual prefix amplitudes,
$\sum_{n=3}^L a_n-(L+1)c\le D_3(a,c)-3c$; inactive entries
can only decrease the left side. The resulting inequality is affine
in prefix amplitudes and cap, so convex mixtures preserve it. ∎

The center (246.8), at head $23/25$ and cap $49/100$, has
$E=2/25$, whereas $3(1-a_2)/4=3/40$. Its excess above (247.2) is
$1/200$. Thus it is outside this precisely stated residual and convex
closure, including the entire old five- and six-active families of
§§148 and 161, and the full fixed-core family of §187.
For the direct six-to-seven recognition at this center, §174.1 gives
$g_7=21/100$, $W=14/25$, $E_{\rm ext}=7/20$, $r=11/25$,
$e_0=7/22$, and inverse core
$(A_2,A_3,A_4,A_5,A_6)=(17/22,17/22,29/44,6/11,19/44)$.
Section 117.2 requires core error $197/616>7/22=196/616$.
This excludes that direct inverse core, without excluding unrestricted
stopped feasibility, which Theorem 246.2 supplies.

**Proposition 247.2 (A larger specified convex comparison at seven).**
The center in Proposition 246.3 also lies outside the convex hull of
the following seven-prefix data: the families of §§238, 240–242;
the old unit plateaus and saturated-head profiles; and feasible cores
with at most six active coordinates or the fixed §187 core, with any
finite §173 residual extensions. All actual inactive amplitudes and
caps are retained in this comparison.

Proof. Put $E_7=\sum_{n=3}^7a_n-8c$. Each compared feasible datum
satisfies the two old head inequalities

$$
E_7\le1-a_1,\qquad E_7\le\tfrac45(1-a_2).
\tag{247.3}
$$

The center is tight in both and has $a_2=a_3$. All these slacks and
$a_2-a_3$ are nonnegative. Hence each positive-weight component of a
convex representation would be tight in all three.
The families with excess ratio at most $3/4$ (or $2/3$) can be tight
in the second inequality only at $a_2=1,E_7=0$; simultaneous tightness
in the first then gives $a_1=1$. They lie in the plateau face
$\operatorname{conv}\{v_3,\ldots,v_7\}$ of the full hull (237.7).
For an actual inactive seventh coordinate, $a_7\le c$ further removes
$v_7$ when applicable. The families §§238, 240–241 have strict
second-head slack: their respective excess ratios are at most
$5/9,7/12,5/9$, below $4/5$. Saturated-head and unit families have
zero excess and reduce to the same plateau face under tightness.

For §242, tightness in both inequalities forces
$a_1=H(t)=(4t+1)/5$ and $c=e_2(t)$. Its resulting tight data are
the segment from
$p_0=(29/33,28/33,\ldots,28/33;17/33)$ to $v_7$.
Thus every possible representation of the center reduces to $p_0$
and the plateau vertices $v_3,\ldots,v_7$.
The coordinate $a_2=9/10$ forces $p_0$ weight $33/50$, leaving total
plateau weight $17/50$. The four successive late gaps $1/20$ force
$v_3,v_4,v_5,v_6$ weights
$1/15,1/12,1/10,7/60$, because the respective vertex jumps are
$3/4,3/5,1/2,3/7$. Their sum is $11/30>17/50$, by $2/75$.
No nonnegative weight remains for $v_7$, a contradiction. ∎

**Proposition 247.3 (A strict eight-prefix comparison).** For each
lower-head point of (245.6), $h\le11/12$, define

$$
J(a,c)=\sum_{n=3}^8a_n-9c-\tfrac45(1-a_2).
\tag{247.4}
$$

Then $J=1/300>0$. The convex hull of the actual eight-prefix data from
the families in Proposition 247.2 and their finite §173 extensions has
$J\le0$.

Proof. For the new continuum, $S-9e=1/12$, $1-a_2=1/10$.
For every compared family $E\le4(1-a_2)/5$: the smaller ratios in the
preceding proof suffice, §242 has ratio at most $4/5$, and saturated
or unit data have $E=0$. Proposition 247.1 includes all five/six cores
and §187. Section 174.2 preserves this inequality under residual
extension. Every actual eight-prefix has $\sum_3^8a_n-9c\le E$.
Thus all compared data have $J\le0$, and its affineness preserves this
under convex mixtures. ∎

These are comparisons with exactly the named supplier families and
operations. They establish substantive additional feasible domains;
the new points have actual stopped and N witnesses. They are neither
original N/O separators nor exclusions from every semantic consequence
of the library. The common terminal-coupling framework of §176 and the
all-word base/pair minima of §178 remain the underlying framework.

## 248. Quantitative stopped repair of every full normalized N law

**Definition 248.1 (One decomposition, defects and a common repair).**
Fix $L\ge3$ and any ordered finite data
$1\ge a_1\ge\cdots\ge a_L\ge\varepsilon\ge0$.
Let $p\in\mathscr N_L$ satisfy every row (237.1) at cap $\varepsilon$,
and choose any common probability distribution $\pi$ on its complete
N tables. Every label in $J_L$ remains allowed. Sorting two distinct
queried indices merely permutes their acquired information cells;
repeated static requests have singleton information. These representation
operations do not exempt any actual repeated or ignored request from
counting. Use empty, singleton and sorted distinct-pair forms below.

Write $v^+=1^L$, let $v^i$ have its sole zero at $i$, and let $v^{ij}$
have zeros exactly at $i<j$. Define

$$
\begin{aligned}
\delta&=3-p_{v^+}(0)-\sum_{i=1}^L p_{v^i}(i),\\
s_0&=p_{v^+}(0)-(1-\varepsilon),&
s_i&=p_{v^i}(i)-(a_i-\varepsilon),\\
D(a,\varepsilon)&=2-\sum_{i=1}^L a_i+(L+1)\varepsilon,\\
B(p)&=\sum_{i=1}^{L-1}(L-i)s_i+3\delta,&
c_L&=\max\{3,L-1\}.
\end{aligned}
\tag{248.1}
$$

On the same selected pair table
$N(a,b;\ell_{00},\ell_{01},\ell_{10},\ell_{11})$, $a<b$, replace
its four outputs by
$(\ell_{01},\ell_{01},\ell_{10},\ell_{11})$. Execute this as the
stopped table $O(a,b;\ell_{01},\ell_{10},\ell_{11})$.
Keep all empty and singleton functions. Let $q$ be this pushforward of
the one whole-table law, and put

$$
\mu=\pi\{\text{distinct-pair tables with }\ell_{00}\ne\ell_{01}\}.
\tag{248.2}
$$

This is one changed-table seed event, common to every word.

**Theorem 248.2 (Full normalized repair and its all-word allowance).**
For every $p$ and every decomposition in Definition 248.1, $q\in\mathscr O_L$,

$$
\begin{gathered}
q_{v^+}=p_{v^+},\qquad q_{v^i}=p_{v^i}\quad(1\le i\le L),\\
\sup_{w\in\{0,1\}^L}\operatorname{TV}(p_w,q_w)
 \le\mu\le\min\{1,B(p)\}\le\min\{1,c_LD(a,\varepsilon)\}.
\end{gathered}
\tag{248.3}
$$

The equalities preserve the entire probability vectors.
The repaired kernel satisfies every independent TV row at cap
$\varepsilon+\mu$, hence at $\varepsilon+\min\{1,B(p)\}$.
If every affected base, correct and pair event has actual row slack
at least $\mu$, it is feasible at the original cap as well.
In particular $D=0$ implies $\mu=0$ in every decomposition and
$p\in\mathscr O_L$.

Proof. For a deterministic pair $T$ on $a<b$, put

$$
t_a=[\ell_{01}=a],\quad t_b=[\ell_{10}=b],\quad
z=[\ell_{11}=0\text{ or }\ell_{11}\in[L]\setminus\{a,b\}].
$$

Its positive-base indicator plus its number of correct sole-zero words
is exactly $t_a+t_b+z$. Indeed every unqueried sole-zero word has
transcript $11$, as does $v^+$; its one output can give at most one
unqueried correct label or the positive base. Thus its deterministic
defect

$$
d_T=3-T(v^+)(0)-\sum_i[T(v^i)=i]=3-t_a-t_b-z
\tag{248.4}
$$

is a nonnegative integer. Empty and singleton forms have this count at
most one and two, respectively, so their defects are positive.
Integrating the one normalized distribution gives
$\delta=\mathbb E_\pi d_T\ge0$.
Zero-defect tables are distinct pairs with
$\ell_{01}=a$, $\ell_{10}=b$, and $\ell_{11}$ zero or unqueried;
the $00$ output is not yet restricted.

For $i<j$, define the signed correctness loss

$$
g_{ij}(T)=[T(v^i)=i]-[T(v^{ij})=i].
\tag{248.5}
$$

On a zero-defect table every $g_{ij}\ge0$. If $i$ is queried, its
sole-zero correctness is already one. If it is unqueried, adding a
later queried zero can only replace exhaustion by an output equal to
that queried label, so cannot gain $i$. If neither zero is queried the
transcript stays fixed. In particular, for its own pair,
$g_{ab}=1-[\ell_{00}=a]$.

For an arbitrary pair table, all negative $g_{ij}$ have just three
possible forms. An earlier unqueried first zero $i$ can gain its one
label $\ell_{01}$ when a later zero at $a$ is added, requiring
$t_a=0$. It can similarly gain the one label $\ell_{10}$ when a later
zero at $b$ is added, requiring $t_b=0$. Finally, the own pair
$\{a,b\}$ can gain first-zero $a$ through $\ell_{00}=a$ only if
$t_a=0$. Each of the first two types has at most one index $i$,
since the output label is fixed. These exhaust transcript changes.
Consequently

$$
\sum_{i<j}(-g_{ij}(T))_+
 \le2(1-t_a)+(1-t_b)\le2d_T.
\tag{248.6}
$$

A singleton has at most one gain: a later zero at its queried index
can supply just one earlier unqueried label; its defect is at least
one. An empty table has no gain. Thus (248.6) holds throughout the
complete catalog, retaining earlier and unqueried numerical labels.

Let $\beta_{\rm bad}=\pi\{d_T\ge1\}\le\delta$, and let $\Lambda$
be the mass of zero-defect pairs with $\ell_{00}\ne a$.
Their own-pair loss and the nonnegativity of all their other losses give

$$
\Lambda\le\mathbb E_\pi\left[\mathbf1_{d_T=0}\sum_{i<j}g_{ij}(T)\right].
$$

For the full mixture, the correct row at $v^{ij}$ has first zero $i$,
so
$\mathbb E g_{ij}=p_{v^i}(i)-p_{v^{ij}}(i)\le s_i$.
Compensating only the possible gains from positive-defect tables,
(248.6) yields

$$
\begin{aligned}
\Lambda&\le\sum_i(L-i)s_i+
 \mathbb E_\pi\left[\mathbf1_{d_T\ge1}\sum_{i<j}(-g_{ij}(T))_+\right]\\
&\le\sum_i(L-i)s_i+2\delta,\\
\mu&\le\Lambda+\beta_{\rm bad}
 \le\sum_i(L-i)s_i+3\delta=B(p).
\end{aligned}
\tag{248.7}
$$

All terms use this same decomposition; no separate table optimizer
or independent marginal realization has been substituted.

The repair never changes a sole-zero or positive transcript, since
none visits pair cell $00$. Their outputs agree at each seed.
At every other word they can differ only on the single event (248.2).
For any output event $E$, coupling by that same seed gives
$|p_w(E)-q_w(E)|\le\mu$. Taking the supremum proves the TV bound
simultaneously on all words, including arbitrary multiple zeros.
The repaired first cell is measurable on the stopped transcript and
all three output choices were fixed before replies, so $q\in\mathscr O_L$.
Each independent base, correct and pair probability drops by at most
$\mu$ as its own event inequality. Hence all three rows hold at
$\varepsilon+\mu$; the positive row is unchanged. This also proves
the stated sufficient actual-slack condition at the original cap.

The original rows give $s_0,s_i\ge0$, and direct substitution gives

$$
\delta+s_0+\sum_i s_i=D(a,\varepsilon),\qquad
B(p)\le c_L(D-s_0)\le c_LD.
\tag{248.8}
$$

Together with $\mu\le1$, this proves (248.3). At $D=0$ all these
nonnegative quantities vanish, forcing $\mu=0$ in every decomposition.
The original full table functions are then already stopped almost surely.

The local gain coefficient two in (248.6) is sharp: at $L=3$ the legal
$N(2,3;2,1,3,0)$ has defect one and gains first-zero correctness on
$\{1,2\}$ and $\{2,3\}$, and nowhere else. Its gain sum is two.
This claims no sharpness of $c_L$ or the coefficient $3\delta$. ∎

**Proposition 248.3 (A charged earlier-label change on an actual source).**
The actual source $(r,g)=(19,436)$ has $F_{19}=4181$,
$N(r,g)=1822917$ and first-four reply word $0100$.
The legal table $N(3,4;1,0,0,0)$ returns earlier unqueried label one
there. Its repair returns zero. For this pure table the changed mass
is one, and its defect at $L=4$ is two.

Proof. The integer is divisible by three and by none of two, five,
seven; $419\le436\le836$ is in the original Fibonacci window.
The acquired pair $(3,4)$ sees $00$, whose original output is one.
The repair uses its old $01$ output, zero. The original
base/correct/pair vector is $(0,1,1)$ and the repaired vector
$(1,0,1)$. Every sole-zero correct indicator is zero, while the positive
base is one; hence (248.4) gives defect two. Its full probability mass
is included in (248.2), exactly as required by (248.7).
No pruning to base or queried labels is legitimate. ∎

## 249. The full normalized plateau face and same-allocation consequences

**Theorem 249.1 (Equality of the full normalized N and O plateau faces).**
For every $L\ge3$, at $a_1=\cdots=a_L=1$ and

$$
\varepsilon=(L-2)/(L+1),\qquad s=3/(L+1),
\tag{249.1}
$$

the entire normalized finite feasible N face equals the O face.
It consists exactly of probability mixtures on triples of
$[L]\cup\{\infty\}$ whose inclusion marginal at each of the $L+1$
labels is $s$. The triple queries its two smallest numerical labels,
stops at its first queried zero with that label, and otherwise emits
the third label, with $\infty$ meaning zero.
In any complete deterministic-table decomposition of a feasible N
kernel, every positive-mass table is, in sorted form,

$$
N(i,j;i,i,j,r),\qquad i<j<r\le L,
\quad\text{or}\quad N(i,j;i,i,j,0).
\tag{249.2}
$$

Empty, singleton and repeated-information forms have zero mass.

Proof. Here $D=0$. Equations (248.4) and (248.8) force zero defect,
positive base $s$, and sole-zero correct probability $s$ at every index.
Theorem 248.2 additionally forces $00=01$ in every positive-mass pair
of any decomposition. Therefore the zero-defect form is already
stopped, with $00=01=i$, $10=j$, and $11$ zero or an unqueried label.

If an exhaustion label $r<j$ had positive mass, choose a word with
first zero $r$ and also zero at the later queried index $j$.
That table loses correct $r$ relative to $v^r$. Every forced stopped
form has correct-$r$ indicator at most its sole-zero indicator: a
queried $r$ is correctly reached, and an unqueried exhaustion guess
can only be lost. Thus no other form can gain to compensate.
Since correctness at $v^r$ is already tight at $s$ and the all-word
correct row also requires $s$, this is impossible. Hence numerical
exhaustion guesses satisfy $r>j$, proving (249.2).

These tables correspond exactly to triples $\{i,j,r\}$ or
$\{i,j,\infty\}$. On every first-zero-$n$ word the output is $n$
exactly when its triple contains $n$; on the positive word output
zero is exactly inclusion of $\infty$. Thus all marginals must be $s$.
Conversely every probability triple mixture with those marginals has
correct mass $s$, pair mass at least $s=1-\varepsilon$, base at least
zero above its literal demand $-\varepsilon$, and positive base $s$.
Every independent row holds. Uniform triple weights supply existence.

The sole-zero equalities, exhaustion reserve and complete O-face
argument belong to §224; the implication forcing the N $00$ cell and
therefore the equality of full faces is supplied by Theorem 248.2.
This is a normalized finite-law classification. It does not classify
arbitrary conic mass or unprojected original full-carrier decompositions.
The numerical-exhaustion mass is $1-s=\varepsilon$, and the original
unit-plateau attainer and its closed-tail transport remain §§87,
110 and 176. ∎

**Corollary 249.2 (Original full-class repair with the allowance paid).**
For every entire original positive nonincreasing vanishing $a$ and every
positive closed cap $\varepsilon$ whose strict active length is $L\ge3$,
original N feasibility implies original O feasibility at cap

$$
\min\left\{1,\ \varepsilon+
 \min\left\{1,c_L\left[2-\sum_{i=1}^La_i+(L+1)\varepsilon\right]\right\}\right\}.
\tag{249.3}
$$

The chosen finite N representative and its repaired O rule use the
same seed. Every actual tail still has error at most $\varepsilon$.

Proof. Use the necessary direction of §110.2 at the exact original
cap to obtain one normalized full finite N law $p$. Apply Theorem
248.2 to any of its complete-table decompositions and execute the
repaired law on the actual low primes. Every active word has error at
most $\varepsilon+\mu$, bounded by (249.3) since TV is at most one.
Its entire positive-word law is unchanged. Thus every actual $n>L$
has error $\max\{1-p_{v^+}(0),a_n\}\le\varepsilon$, including
$a_{L+1}=\varepsilon$ and all later ties. One pre-reply seed selects
all outputs and the increasing schedule; execution has at most two
actual requests and finite handoff. The initial original competitor
need not retain its laws or seed coupling under §110.2; the same-seed
assertion is for its selected finite representative and this repair.
Small active lengths retain their existing suppliers.
The displayed positive allowance is part of the cap, so this corollary
does not establish the original same-cap implication when it is positive. ∎

**Theorem 249.3 (One full feasible conic allocation and the score correction).**
Fix the same $(b,e)\in H_L$ and one complete $\lambda\ge0$ satisfying
$G_N\lambda\ge h(b,e)$, of mass $M=\sum_T\lambda_T\ge1$.
Set $D_b=2-\sum_i b_i+(L+1)e$. For every full nonnegative score $y$,

$$
F_{Q(y)}(b,e)\le M\Delta_O(y)+K_y\min\{M,c_LD_b\}.
\tag{249.4}
$$

Thus a full unit-O score with strict $F_{Q(y)}(b,e)>M$ requires
$D_b>0$; its strict gap is at most $K_y\min\{M,c_LD_b\}$.
No such separator occurs on the feasible $D_b=0$ face.

Proof. Normalize this very allocation to $p_T=\lambda_T/M$ and put

$$
x=(1-1/M)(\alpha,0)+(b,e)/M,
\qquad \alpha=(1,1,0,\ldots,0).
\tag{249.5}
$$

Affineness of every full demand row gives
$Z_Np=r+G_N\lambda/M\ge r+h(b,e)/M=d(x)$.
The auxiliary amplitudes are ordered in $[0,1]$ and at least their cap
$e/M$; equality of the second and third coordinates is unnecessary.
All normalized rows hold, and $D(x)=D_b/M$, because $\sum\alpha_i=2$.
Theorem 248.2 applies even if this finite auxiliary point has zero cap,
inactive coordinates, or lies outside $H_L$.
Its single repaired law $q$ has
$\mu\le\min\{1,c_LD_b/M\}$. Every independent event changes by at
most $\mu$, so, using $y\ge0$,

$$
y\cdot d(x)\le y\cdot Z_Oq+K_y\mu\le B_O(y)+K_y\mu.
$$

But $y\cdot d(x)=W_y+F_{Q(y)}(b,e)/M$ and
$B_O(y)=W_y+\Delta_O(y)$. Multiplication by $M$ proves (249.4),
with the same $b$ and full $\lambda$ throughout. The independent pair
coefficient is counted once in $K_y$, as are all other full event
coefficients. No separately optimized row costs enter.
If $D_b=0$ the correction vanishes. If $K_y=0$ the full score is zero
and cannot strictly separate. The positive correction at $D_b>0$
is retained; it has not been financed by the original unit budget. ∎

## 250. Original correspondence, mathematical ownership and the open obligation

**Proposition 250.1 (Actual source and resource interpretation).** All
laws and cap statements in §§244–249 concern the original selected
marked laws of (243.2) on the actual labeled source (243.1), with no
source prior. The full Borel carrier, unchanged consumer, and original
nonatomic targets of §243.1 retain their definitions. Every displayed
finite marked law has TV one from each original nonatomic target.
The arbitrary-address/full-carrier necessity used for lower bounds is
exactly §110.2; no restriction of competitors to the displayed finite
marks, addresses or constructions is made.

Proof. The marks $\theta_j=(B_1,1/(j+2))$ are actual distinct tapes.
Any displayed complete law is one finite probability distribution on
whole tables. A half-open interval partition of one source-independent
$U\in[0,1)$ fixes its schedule and every potential output before any
reply, including the product coupling in (244.7), all seventeen rows
of §246 and any outer mixtures. The auxiliary interval construction
for triple coefficients is integrated before this execution.
There is no source-dependent coin or selection after a reply.
An O execution follows its increasing preselected schedule to its first
queried zero or exhaustion; N acquires its entire selected schedule
and reconstructs the stopped output. Ignored post-stop replies and
repeated requests are actual counted requests. The hard bound is two,
not a bound on address, depth, runtime or expected count. The finite
constructed rules hand off at every source and seed; original
competitors retain sourcewise almost-sure finite handoff.

The source supplier in §110.2, through Boundaries 35.2, realizes every
finite pattern on arbitrary finite prime addresses fixed before seeds.
Its entry-rank interface chooses a sufficiently large prime $r$ for
which $F_r$ is invertible modulo all prescribed primes. CRT chooses
$g=-F_r^{-1}$ at a desired positive address and $g=0$ at a desired zero;
a sufficiently long original Fibonacci window contains that residue.
This includes all multiple-zero words and any finite positive prefix
followed by a later zero, without an infinite all-positive source.
The entry-rank interface is the supplied classical hypothesis, not a
new theorem here.

For original necessity, countability gives one common conull seed event
of finite handoff and hard request count. The maximum of the whole
preselected schedule has vanishing seed tails. Actual witnesses for a
finite family of comparison words and their finite execution cutoffs
are fixed without inspecting seeds. Whole-execution replay on equal
acquired transcripts, measurable projection of the full carrier onto
low marks and base, and the vanishing common schedule/execution error
produce finite same-class comparisons. Compactness of the one finite
catalog simplex retains every row at the exact closed cap. These are
§110.2's hypotheses and proof, without an asserted uniform runtime or
address bound on original competitors.

If a lower score uses a longer horizon than the strict active cutoff,
ignore new coordinates in the finite kernel: new correct demands are
nonpositive and the retained positive base pays base and pair rows.
If it uses a shorter horizon, fix later finite replies zero and project
later labels to base for the comparison, as in §§117.2 and 207.20.
These are representation operations, not additional observations.
The actual tail identity is always (243.3). The sharp constructions
have positive base $1-e_*$ and hence error $e_*$ on every allowed
actual tail; the repair preserves the full positive law and hence its
old tail bound. Closed caps, zero schedule weights, repeated amplitude
values and all tail ties remain included. Finite support has mass one
under a marked law and zero under every original nonatomic target,
proving the stated TV-one distinction. ∎

The rank-three degree lemma is the classical hypersimplex or uniform
matroid base-polytope fact; the interval proof in §244 supplies it
without an additional hypothesis. Common terminal coupling is §§109,
140 and 176, and coupled all-word base/pair minima are §178. Both
sharp lower inequalities belong to §§113.2 and 117.2; their saturated
supplier is §§113.3–114. The entire five- and six-active comparisons
are §§148 and 161. The residual-extension identities are §§173–174,
and the fixed sharp-five residual family is §187. These facts and the
unit/flat-seven endpoints have their existing ownership. The capacity
construction is one sufficient-family theorem; its near-unit domain
and eight-coordinate examples are consequences of that construction.
The unequal-seven region has the explicit noncontainment and bounded
comparisons of §§246–247. The quantitative normalized-N repair supplies
the additional N $00$ equality beyond the stopped face of §224.
The score quotient, hull support and unrestricted one-residual pairing
are §§198–199 and 229, without another duality claim.

Blackwell, *Comparison of Experiments*, §§2–5, supplies the common
normalized decision-kernel and risk comparison framework; it does not
supply an increasing first-zero stopped schedule with two actual
requests. Kaniewski, Lee and de Wolf, *Query complexity in expectation*,
arXiv:1411.7280v1, Definition 8 and Theorem 9, concern nonnegative
scalar outputs in expectation and worst-path query depth. Their scalar
literal representation does not supply equal probability-vector masses
in all stopped cells. Kaibel, *Basic Polyhedral Theory*,
arXiv:1001.2161v1, Theorems 1, 8 and 10, supplies finite polyhedral
background, without these acquisition constraints. These are bounded
comparisons with the cited results. The elementary constructions and
counting proofs above are ordinary mathematics; no exhaustive
literature or repository nonderivability assertion is made.

**Open problem 250.2 (The same original unrestricted goal).** For every
entire positive nonincreasing vanishing actual amplitude sequence and
every positive closed cap, the general implication remains

$$
\mathcal F_N(a,c)\ne\varnothing
\ \Longrightarrow\
\mathcal F_N(a,c)\cap\mathscr C_{L_a}\ne\varnothing.
\tag{250.1}
$$

Its positive full-score obligation is still: for every $L\ge3$ and
every actual full $y\ge0$ with $\Delta_O(y)\le1$, find one
unrestricted full $V\ge0$ and one $\theta\in[0,1]$ with

$$
\Delta_N(V)+\theta\le1,\qquad
\sigma_{H_L}(Q(y)-Q(V))\le\theta.
\tag{250.2}
$$

No fixed law, anchor, unary profile, exact quotient, graph, mask,
canonical decomposition or positive-only residual is imposed;
nonzero zero-cost $V$ remains admissible at $\theta=1$.
The negative alternative still requires the same actual $(b,e)\in H_N$,
one full feasible $\lambda\ge0$ with $G_N\lambda\ge h(b,e)$ and
$M=\sum\lambda\ge1$, and an actual full unit-O $y$ with strict
$F_{Q(y)}(b,e)>M$, together with the original same-source/common-seed
N attainer and the uniform lower bound against every arbitrary-address
full-carrier O competitor, retaining positive actual tails and closed caps.

The sufficient regions and the $D_b=0$ consequence shrink this gap in
their exact scopes. Away from that face, (248.3) pays a positive repair
allowance and (249.4) retains $K_y\min\{M,c_LD_b\}$. Neither term
is an already paid signed residual in (250.2). Optional-constructor
failure, exact-law obstruction and a point outside $H_N$ do not provide
the negative alternative. No universal classification follows from
these finite laws or bounded supplier comparisons.

## 追加锚（本行以下为增补区）
