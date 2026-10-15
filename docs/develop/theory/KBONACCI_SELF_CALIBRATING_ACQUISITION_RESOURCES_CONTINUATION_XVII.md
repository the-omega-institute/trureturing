# KBONACCI self-calibrating acquisition resources XVII

## 297. Original acquisition objects and the complete finite interface

**Definition 297.1 (Source, carrier and the two target families).**
Let $F_0=0$, $F_1=1$, $F_{r+2}=F_{r+1}+F_r$, and let $p_i$ be the
increasing primes. The actual countable source is

$$
X=\{(r,g):r\text{ prime},\ g\in\mathbb Z,
\ \lceil F_r/10\rceil\le g\le\lfloor F_r/5\rfloor\},\qquad
N(r,g)=1+F_rg,\quad q_i(x)=[p_i\mid N(x)].
$$

Its replies are static, and $n(x)=\min\{i:q_i(x)=0\}$ is finite.
The full output carrier is the Borel disjoint union
$\Theta=\bigsqcup_{j\ge1}B_j\sqcup\bigsqcup_{j\ge1}P_j$ of copies
of $(0,1)$. The unchanged consumer returns unknown on $B_j$ and
proposes $j$ on $P_j$, without making prime requests.

The original nonatomic targets of
[273.3](KBONACCI_SELF_CALIBRATING_ACQUISITION_RESOURCES_CONTINUATION_XVI.md)
are retained: fix $h_0\in(0,1)$, put
$t_x=\sum_i3^{-i}q_i(x)$ and $Z_t=\int_0^1e^{tu}\,du$, let $\nu_x$
have density $e^{t_xu}/Z_{t_x}$ on $B_{n(x)}$, and let $\pi_j$ be
uniform on $P_j$. With $\Omega(x)$ the number of distinct prime
divisors of $N(x)$, their law is
$\mu_x^{\rm orig}=(1-h_0)\nu_x+h_0\pi_{\Omega(x)}$.

The targets compared below are instead the separately selected marked laws

$$
\lambda_x^a=(1-a_{n(x)})\delta_{\theta_0}
                  +a_{n(x)}\delta_{\theta_{n(x)}},\qquad
\theta_j=(B_1,1/(j+2)),\quad j\ge0,
\quad1\ge a_1\ge a_2\ge\cdots>0,\quad a_n\longrightarrow0.
\tag{297.1}
$$

For an acquisition $A$, write
$e_a(A)=\sup_{x\in X}\operatorname{TV}(\mathcal L(A(x)),\lambda_x^a)$.
A law supported on finitely many marks has TV distance one from every
$\mu_x^{\rm orig}$, since those targets give its finite support mass zero.
Thus marked-target estimates do not estimate the unchanged nonatomic targets.

**Definition 297.2 (Hard two actual requests).**
There is one source-independent common seed, zero advice and sourcewise
almost-sure finite handoff to the unchanged consumer. In $\mathcal N_2$
the whole schedule is preselected before replies and its replies are obtained.
In $\mathcal O_2$ an increasing schedule is preselected before replies and
execution stops at its first **queried** zero or exhaustion. Its second
address is not chosen from the first reply. Both classes allow at most two
actual requests, counting repetitions and ignored replies. Competitors may
query arbitrary addresses and output anywhere in $\Theta$. There is no
source distribution, bounded-address, runtime or mean-request assumption.
Completing a stopped schedule under the same seed produces an $N$ rule
with identical output laws; its ignored second request is counted.

**Reused source and transport facts 297.3.**
The arithmetic premise is the genuine
[Proposition 280.1](KBONACCI_SELF_CALIBRATING_ACQUISITION_RESOURCES_CONTINUATION_XVI.md).
For clarity, its finite-pattern argument is as follows. Modulo a prime $p$,
the invertible Fibonacci matrix
$Q=\left(\begin{smallmatrix}1&1\\1&0\end{smallmatrix}\right)$ satisfies
$Q^k=\left(\begin{smallmatrix}F_{k+1}&F_k\\F_k&F_{k-1}\end{smallmatrix}\right)$.
It is scalar exactly when $p\mid F_k$. The inverse image of the scalar
subgroup is $z(p)\mathbb Z$; finiteness of
$\operatorname{PGL}_2(\mathbb F_p)$ gives $z(p)>0$, and $F_1=F_2=1$
gives $z(p)\ge3$. Thus $p\mid F_k$ iff $z(p)\mid k$.
For any finite collection of primes with product $D$, choose a sufficiently
large prime index $r>\max z(p)$. Then $F_r$ is invertible modulo $D$.
Impose $g\equiv-F_r^{-1}\pmod p$ at prescribed ones and
$g\equiv0\pmod p$ at prescribed zeros. CRT gives a residue modulo $D$;
the actual interval $[\lceil F_r/10\rceil,\lfloor F_r/5\rfloor]$
contains $D$ consecutive integers for large $r$. It contains a legal $g$.
Every finite word, including multiple zeros and positive prefixes, is
therefore actual. Each actual positive integer $N(r,g)$ has only finitely
many prime divisors, proving finite first absence.

At a positive closed cap $e\le1$, put
$L_a=\max(\{i:a_i>e\}\cup\{0\})$. The class-feasibility equivalence
of [Theorem 110.2](KBONACCI_SELF_CALIBRATING_ACQUISITION_RESOURCES_CONTINUATION.md)
gives some complete normalized finite $N$ representative on $L_a$ bits
for every original cap-feasible $N$ rule. Its necessity uses countability
to obtain one probability-one seed event for termination at every source,
control of the entire preselected schedule, actual finite-pattern witnesses,
truncation and finite-simplex compactness. It does not assert preservation
of an arbitrary starting output law or coupling. Its stopped counterpart
uses the exact normalized criterion of
[Theorem 109.1](KBONACCI_SELF_CALIBRATING_ACQUISITION_RESOURCES_CONTINUATION.md):
for a probability-vector kernel
$p_w=c+\sum_i\ell_iw_i+\sum_{i<j}Q_{ij}w_iw_j$, set
$V_i=\sum_{j>i}(-Q_{ij})_+$ and $H=\sum_i(V_i-\ell_i)_+$.
Stopped realizability is exactly $c\ge H$ coordinatewise; normalization
makes its scalar schedule budget automatic. Degree at most two alone is
not that criterion.

For any probability law $p$ on marks $0,\ldots,L$ and actual $n>L$,

$$
\operatorname{TV}\left(\sum_{j=0}^Lp(j)\delta_{\theta_j},\lambda_x^a\right)
       =\max\{1-p(0),a_n\}.
\tag{297.2}
$$

This is the exact positive-tail formula, including $a_n=e$.
The prefix consequence used here is
[Lemma 280.3](KBONACCI_SELF_CALIBRATING_ACQUISITION_RESOURCES_CONTINUATION_XVI.md):
if a score uses a prefix of length $K\le L_a$, fix higher finite replies
to zero, project higher labels to zero and contract constant observations.
TV contracts, and at most two variable observations remain. If $L_a<K$,
ignore added inputs; on each added first-zero fibre use the old positive
law, whose error is (297.2), at most $e$. These operations establish
finite representation and grant no free actual query. Consequently a
zero-cost score on any finite prefix applies even to inactive selected
addresses, all multiple-zero words and closed ties.

**Definition 297.4 (Every word, label and independent event).**
Fix $L\ge3$, $B_L=\{0,1\}^L$ and labels $0,\ldots,L$. Write $+=1^L$
and $\Omega_n=\{w:\min\{i:w_i=0\}=n\}$. A deterministic
$N(i,j;u,v,s,t)$, $i<j$, outputs $u,v,s,t$ on $00,01,10,11$.
A deterministic $O(i,j;u,s,t)$ outputs $u,s,t$ on stopped cells
$0,10,11$. Constants and singletons are included. Every label is allowed,
including earlier and unqueried labels. Reversed static queries permute
cells; repeated queries give singleton information without refunding a call.

For a real finite profile $(b,e)\in\mathbb R^L\times\mathbb R$, at
every $w\in\Omega_n$ retain the three independent rows $A,C,P$ for
events $\{0\},\{n\},\{0,n\}$, with demands
$1-b_n-e,b_n-e,1-e$. The positive row has event $\{0\}$ and demand
$1-e$. Negative singleton demands are retained without clipping.
For probability kernels the exact error formula is

$$
\operatorname{TV}(p_w,(1-b_n)e_0+b_ne_n)
=\max\{1-b_n-p_w(0),\ b_n-p_w(n),\ 1-p_w(0)-p_w(n)\}
\tag{297.3}
$$

when $0\le b_n\le1$. In the unrestricted real-profile conic problem,
the stated linear rows, rather than probability targets outside this interval,
define feasibility.

**Definition 297.5 (One complete allocation and its score).**
Let $R=O(1,2;1,2,0)$, $\alpha=(1,1,0,\ldots,0)$,
$r=z_R=d(\alpha,0)$, $G_C=(z_D-r)_{D\in\mathcal D_C}$ and
$h=d(b,e)-r$, where $z_D$ is the incidence vector on all the rows of
297.4. One full feasible allocation is one vector
$\lambda_D\ge0$ of any finite mass $M=\sum_D\lambda_D$ satisfying
$G_C\lambda\ge h$. All word measures are supplied by this same vector.
Mass one is normalized acquisition feasibility. A conic vector is not
normalized at unchanged $(b,e)$ by dividing by $M$.

A full nonnegative score $Y=(A_w,C_w,P_w;T)$ rewards label $\ell$ by

$$
g_Y(w,\ell)=A_w[\ell=0]+C_w[\ell=n]+P_w[\ell\in\{0,n\}]
\quad(w\in\Omega_n),\qquad g_Y(+,\ell)=T[\ell=0].
$$

Its anchor, support, excess and quotient are

$$
\begin{gathered}
W_Y=Y r,\qquad B_C(Y)=\max_{D\in\mathcal D_C}Y z_D,
\qquad\Delta_C(Y)=B_C(Y)-W_Y\ge0,\\
\beta_n=\sum_{w\in\Omega_n}(C_w-A_w),\qquad
K_Y=\sum_{w\ne+}(A_w+C_w+P_w)+T,\qquad QY=(\beta;K_Y),\\
F_{QY}(b,e)=\sum_n\beta_n(b_n-\alpha_n)-K_Ye=Yh.
\tag{297.4}
\end{gathered}
$$

In particular, for this same allocation,

$$
F_{QY}(b,e)\le YG_C\lambda
 =\sum_D\lambda_D(Yz_D-W_Y)\le M\Delta_C(Y).
\tag{297.5}
$$

The first inequality follows from nonnegativity of $Y$ and all the full
rows. Thus zero excess gives $F_{QY}\le0$ at every finite mass, with
no order, normalization or auxiliary hull hypothesis.

## 298. Three complete supporting scores

**Definition 298.1 (The first-head score $Y_1$).**
On seven coordinates give precisely the following independent rows their
displayed weights. All unlisted coefficients, including every $A$, are zero.
Rows with coefficient zero elsewhere remain constraints.

| Row | Word | Weight |
| --- | --- | ---: |
| C | 0001110 | $1/3$ |
| C | 0111110 | $2/3$ |
| C | 1100000 | $2$ |
| C | 1110000 | $2$ |
| C | 1111000 | $2$ |
| C | 1111100 | $2$ |
| C | 1111110 | $2$ |
| P | 0100010 | $1/3$ |
| P | 0100100 | $1/3$ |
| P | 0101000 | $1/3$ |
| P | 0110000 | $1/3$ |
| P | 1000010 | $2/3$ |
| P | 1000100 | $2/3$ |
| P | 1001000 | $2/3$ |
| P | 1010000 | $2/3$ |
| T | 1111111 | $2$ |

**Definition 298.2 (One second-head score $Y_2$).**
Use exactly these 22 rows, with all other coefficients zero.

| Row | Word | Weight |
| --- | --- | ---: |
| P | 0011000 | $1$ |
| P | 0100100 | $1$ |
| P | 0101000 | $1$ |
| P | 0101100 | $1$ |
| P | 0110000 | $1$ |
| P | 0110010 | $1$ |
| P | 1000100 | $1$ |
| P | 1001000 | $1$ |
| P | 1001010 | $1$ |
| P | 1010000 | $1$ |
| P | 1010100 | $1$ |
| P | 1100010 | $1$ |
| C | 1011000 | $1$ |
| C | 1100000 | $2$ |
| C | 1101100 | $1$ |
| C | 1101111 | $1$ |
| C | 1110000 | $4$ |
| C | 1110100 | $1$ |
| C | 1111000 | $5$ |
| C | 1111100 | $5$ |
| C | 1111110 | $4$ |
| T | 1111111 | $4$ |

**Definition 298.3 (An additional score $Y_C$).**
The complete nonzero coefficients are these 31 integer rows.

| Row | Word | Weight |
| --- | --- | ---: |
| P | 0011000 | $4$ |
| P | 0100100 | $6$ |
| P | 0100101 | $1$ |
| P | 0101000 | $7$ |
| P | 0110001 | $3$ |
| P | 0110010 | $3$ |
| P | 1000010 | $1$ |
| P | 1000101 | $1$ |
| P | 1000110 | $1$ |
| P | 1001001 | $1$ |
| P | 1001010 | $5$ |
| P | 1001100 | $5$ |
| P | 1010000 | $2$ |
| P | 1010001 | $4$ |
| P | 1010100 | $4$ |
| C | 1011001 | $4$ |
| C | 1100000 | $6$ |
| P | 1100010 | $3$ |
| C | 1101001 | $1$ |
| C | 1101010 | $7$ |
| C | 1101100 | $4$ |
| C | 1110000 | $13$ |
| C | 1110001 | $3$ |
| P | 1110010 | $1$ |
| C | 1110100 | $4$ |
| C | 1111000 | $11$ |
| C | 1111001 | $10$ |
| C | 1111100 | $18$ |
| C | 1111101 | $3$ |
| C | 1111110 | $18$ |
| T | 1111111 | $17$ |

**Lemma 298.4 (Exact complete supports).**
For the preceding three scores,

$$
\begin{array}{c|c|r|r}
Y&\beta&K_Y&W_Y=B_N(Y)=B_O(Y)\\\hline
Y_1&(1,0,2,2,2,2,2)&17&7\\
Y_2&(0,1,4,5,5,5,4)&40&17\\
Y_C&(0,4,18,20,21,21,18)&171&73
\end{array}
\tag{298.1}
$$

**Proof.** Summing the correct weights in each first-zero class gives
$\beta$; summing all weights gives $K_Y$. For $Y_1$, the $P$ total is
$4$, the early $C$ total is $1$, and $T=2$, giving anchor $7$.
For $Y_2$ these totals are $12,1,4$, giving $17$; for $Y_C$ they are
$52,4,17$, giving $73$.

Here is an exact finite support certificate. For each pair $i<j$ and
cell $uv$, form, for every label $\ell=0,\ldots,7$,

$$
g^Y_{ij,uv}(\ell)=\sum_{w:(w_i,w_j)=(u,v)}g_Y(w,\ell),\qquad
m^Y_{ij,uv}=\max_{0\le\ell\le7}g^Y_{ij,uv}(\ell).
\tag{298.2}
$$

The four entries in each table cell below are in order $00,01,10,11$.
The first column of vectors is for $3Y_1$; the others are unscaled.
These are additions and maxima of the fully specified integer rewards,
including every label, rather than maxima over selected terminal outputs.

| Pair | $m^{3Y_1}$ | $m^{Y_2}$ | $m^{Y_C}$ |
| --- | --- | --- | --- |
| $1,2$ | $(1,6,8,6)$ | $(1,5,6,5)$ | $(4,20,28,21)$ |
| $1,3$ | $(4,3,6,8)$ | $(3,3,5,6)$ | $(14,10,21,28)$ |
| $1,4$ | $(3,4,6,8)$ | $(3,3,5,6)$ | $(13,11,21,28)$ |
| $1,5$ | $(3,4,6,8)$ | $(4,2,5,6)$ | $(17,7,21,28)$ |
| $1,6$ | $(3,4,6,8)$ | $(5,1,5,6)$ | $(21,3,21,28)$ |
| $1,7$ | $(7,0,8,6)$ | $(6,0,6,4)$ | $(20,4,22,23)$ |
| $2,3$ | $(6,2,6,7)$ | $(3,3,5,6)$ | $(14,14,21,24)$ |
| $2,4$ | $(6,2,6,7)$ | $(3,3,5,6)$ | $(13,15,21,24)$ |
| $2,5$ | $(6,2,6,7)$ | $(4,2,5,6)$ | $(17,11,21,24)$ |
| $2,6$ | $(6,2,6,7)$ | $(5,1,5,6)$ | $(21,7,21,24)$ |
| $2,7$ | $(8,0,6,6)$ | $(6,0,6,4)$ | $(22,10,20,21)$ |
| $3,4$ | $(6,3,6,6)$ | $(3,4,5,5)$ | $(13,18,21,21)$ |
| $3,5$ | $(6,3,6,6)$ | $(4,3,5,5)$ | $(17,14,21,21)$ |
| $3,6$ | $(6,3,6,6)$ | $(5,2,5,5)$ | $(21,10,21,21)$ |
| $3,7$ | $(9,0,6,6)$ | $(7,1,5,4)$ | $(28,3,18,24)$ |
| $4,5$ | $(6,3,6,6)$ | $(4,3,5,5)$ | $(17,13,21,22)$ |
| $4,6$ | $(6,3,6,6)$ | $(5,2,5,5)$ | $(21,9,21,22)$ |
| $4,7$ | $(9,0,6,6)$ | $(7,0,5,4)$ | $(21,9,21,18)$ |
| $5,6$ | $(6,3,6,6)$ | $(5,3,5,4)$ | $(21,13,21,18)$ |
| $5,7$ | $(9,0,6,6)$ | $(8,0,5,4)$ | $(26,10,18,19)$ |
| $6,7$ | $(9,0,6,6)$ | $(9,0,4,4)$ | $(28,10,18,17)$ |

For example, in the $00$ cell of pair $(1,2)$ all scored words have
first zero 1. For $Y_2$ only the unit $P$ row at 0011000 contributes,
giving reward one to labels 0 and 1; for $Y_C$ its weight is four.
The other entries use exactly the same rule (298.2), with correct rewards
only at the actual first-zero label and union rewards at both that label
and zero. Every vector sums to at most $21,17,73$, respectively.
An unrestricted $N$ table chooses one label independently in each cell,
so the sum of those four maxima bounds its complete score.

Empty or singleton information coarsens any distinct-pair partition;
repetition gives a singleton partition, and reversal permutes cells.
For nonnegative reward vectors, the maximum of their sum is at most the
sum of their maxima. This proves the same upper bounds for all those
tables. The stopped partition merges $00,01$ before choosing its first
output, so has at most the same bound. The anchor $R$ belongs to both
catalogs and attains $W_Y$, proving equality throughout (298.1).
No claim that zero maximizes every individual cell is needed. $\square$

## 299. Global head relations on the same allocation

**Theorem 299.1 (Three all-length, all-mass necessary relations).**
For every $L\ge7$, every ordered embedding
$3\le j_1<j_2<j_3<j_4<j_5\le L$, every real finite profile $(b,e)$,
and every one complete feasible $N$ allocation of any finite mass,

$$
\begin{aligned}
b_1+2\sum_{a=1}^5b_{j_a}&\le1+17e, &&(Y_1)\\
b_2+4b_{j_1}+5b_{j_2}+5b_{j_3}+5b_{j_4}+4b_{j_5}
 &\le1+40e, &&(Y_2)\\
4b_2+18b_{j_1}+20b_{j_2}+21b_{j_3}+21b_{j_4}+18b_{j_5}
 &\le4+171e. &&(C)
\end{aligned}
\tag{299.1}
$$

The same holds for a complete $O$ allocation. No monotonicity,
normalization or $H_L$ membership is required. Every original acquisition
in $\mathcal N_2$ or $\mathcal O_2$ at any positive closed cap $e$
satisfies these relations with its actual amplitudes $a$ in place of $b$,
including every ordered gap embedding and inactive chosen address.

**Proof.** Embed the seven score coordinates as
$(1,2,j_1,\ldots,j_5)$, and put all nonskeleton bits equal to one on
the scored support. Map numerical labels by the same embedding. A query
outside the skeleton is constant on that support. Two arbitrary queries
therefore produce either one of the core pair partitions or a coarsening.
An outside output label has reward zero; all active label rewards are
already covered by (298.2). Thus Lemma 298.4 proves zero excess in the
entire length-$L$ catalogs, including all arbitrary earlier, unqueried
and outside labels. The embedding changes neither quotient nor anchor.
Apply (297.5) separately to each score and the same given $\lambda$:
$F_{QY}\le M\Delta_N(Y)=0$. Expanding the three quotients gives
(299.1). All three independent event rows remain present throughout;
no independent marginal allocation is substituted.

For an original rule at $0<e\le1$, use 297.3 with prefix $j_5$ to
obtain one normalized complete representative satisfying all rows at
$(a_1,\ldots,a_{j_5};e)$. Apply the just proved embedded relations.
Counted $O$ completion gives the same conclusion for original $O$.
For $e\ge1$, the left sides are at most $11,24,102$, and the right
sides are at least $18,41,175$, so the statements follow directly from
$0<a_i\le1$. $\square$

**Proposition 299.2 (The exact comparison with the ratio face).**
Put $S_J=\sum_a b_{j_a}$, $R_J=(46/5)e-S_J$ and
$r^\star=(13,10,9,8,6)/5$. Write $F_1,F_2,F_C$ for the respective
left-minus-right expressions in (299.1). Then identically

$$
F_C=4F_2+2b_{j_1}+b_{j_3}+b_{j_4}+2b_{j_5}-11e.
\tag{299.2}
$$

On the ratio ray $b_J=\tau(13,10,9,8,6)$, $e=5\tau$, the last
five terms sum to zero. More generally they vanish on the feasible
equality face $R_J=0$: the reused stability theorem
[293.2](KBONACCI_SELF_CALIBRATING_ACQUISITION_RESOURCES_CONTINUATION_XVI.md)
gives $b_J=r^\star e$ there. Thus $F_C=4F_2$ on that face.

**Proof.** Subtract four times the coefficients of $F_2$ from those
of $F_C$. The remaining coefficients are $(2,0,1,1,2)$ on $J$ and
$-11$ on $e$, since $171-4\cdot40=11$. On $r^\star e$ their value is
$(26+9+8+12)e/5-11e=0$. This proves every assertion. In particular
the ray consequence of $C$ supplies no second scale restriction beyond
$Y_2$; its additional scope is the global relation away from that face.
$\square$

## 300. Exact coupled head projection and one common stopped law

**Theorem 300.1 (The entire positive-tail family).**
Let $\tau>0$ and let the entire sequence (297.1) satisfy

$$
\begin{gathered}
1\ge a_1\ge a_2\ge13\tau,\qquad
(a_3,a_4,a_5,a_6,a_7)=\tau(13,10,9,8,6),\\
a_8\ge a_9\ge\cdots>0,\qquad a_8\le5\tau,\qquad a_n\longrightarrow0.
\end{gathered}
\tag{300.1}
$$

On the original source and full carrier with the unchanged consumer and
the selected marked targets, the following are equivalent:

$$
\begin{aligned}
&\exists N\in\mathcal N_2:\ e_a(N)\le5\tau;\\
&\exists O\in\mathcal O_2:\ e_a(O)\le5\tau;\\
&a_1+7\tau\le1\quad\hbox{and}\quad a_2+11\tau\le1.
\end{aligned}
\tag{300.2}
$$

Feasibility necessarily implies $\tau\le1/24$. On precisely this
feasible head domain, both original optima are attained and equal $5\tau$.
For every positive closed cap $\varepsilon$, either class is feasible iff
$\varepsilon\ge5\tau$. This last cap classification is asserted under
the two head conditions; heads failing them are only excluded at cap
$5\tau$ by (300.2).

**Proof.** The necessity follows from Theorem 299.1 on $J=(3,4,5,6,7)$.
Here $S_J=46\tau$, and the weighted late sum in $Y_2$ is
$(52+50+45+40+24)\tau=211\tau$. At $e=5\tau$, the two relations
are exactly $a_1+7\tau\le1$ and $a_2+11\tau\le1$. Since
$a_2\ge13\tau$, they imply $24\tau\le1$.

For sufficiency use the following one law. In the table,
$O(i,j;u,s,t)$ emits $u$ after its first queried zero, $s$ after $10$,
and $t$ after $11$. Its mass is the final entry times $\tau$.

| $i$ | $j$ | $u$ | $s$ | $t$ | Mass / $\tau$ |
| --- | --- | --- | --- | --- | ---: |
| 1 | 2 | 1 | 2 | 0 | 4 |
| 1 | 2 | 1 | 2 | 3 | 2 |
| 1 | 2 | 1 | 2 | 4 | 1 |
| 1 | 2 | 1 | 2 | 5 | 1 |
| 1 | 3 | 1 | 3 | 0 | 3 |
| 1 | 4 | 1 | 4 | 0 | 1 |
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

These integer masses sum to 24. Set

$$
\rho=1-24\tau,\qquad x_1=(a_1-17\tau)_+,\qquad x_2=a_2-13\tau.
\tag{300.3}
$$

The head conditions give $0\le x_1\le\rho$ and $0\le x_2\le\rho$
individually. There is just **one shared remaining branch** of mass
$\rho$, with schedule $(1,2)$ and exhaustion output zero. On that branch
let $V$ be its local uniform coordinate. After first-zero 1 it emits 1
iff $V<x_1/\rho$, otherwise zero; after first-zero 2 it emits 2 iff
$V<x_2/\rho$, otherwise zero. Both counterfactual choices use the
same $V$. If $\rho=0$, omit the branch; then $x_1=x_2=0$.
There is no condition $x_1+x_2\le\rho$: different stopped cells use
the same schedule mass. For example, at $\tau=1/30$ the simultaneous
upper heads $a_1=23/30$, $a_2=19/30$ give
$x_1=x_2=\rho=1/5$.

Here is an all-word verification of that one law for every real permitted
parameter. Put $(s,t,u,v,z)=(w_3,w_4,w_5,w_6,w_7)$ and define

$$
\begin{aligned}
B&=2s(1-t)+st+(s+t)(2-u-v)+u(1-v)+v(1-z),\\
G&=3(1-s)+(1-t).
\end{aligned}
\tag{300.4}
$$

For fixed $q=s+t$ and $(u,v)=00,01,10,11$, maximization over $z$
of $q(2-u-v)+u(1-v)+v(1-z)$ gives $2q,q+1,q+1,1$.
Consequently its maxima for $(s,t)=00,01,10,11$ are $1,2,2,4$.
Adding $2s(1-t)+st+G$ in those four cases gives respectively at most
$5,5,5,5$. Hence $B+G\le5$ and $B\le5$.

Direct addition of the sixteen tables gives the following correct mass
$c_n$ after including the shared branch, and the mass $\delta_n$
outside $\{0,n\}$ in units of $\tau$:

| First zero $n$ | $c_n$ | $\delta_n/\tau$ |
| --- | --- | --- |
| $1$ | $12\tau+x_1$ | $B+w_2G$ |
| $2$ | $8\tau+x_2$ | $B+G$ |
| $3$ | $8\tau$ | $2+2(1-t)+t(2-u-v)+u(1-v)+v(1-z)$ |
| $4$ | $5\tau$ | $5-uv-vz$ |
| $5$ | $4\tau$ | $5-v-vz$ |
| $6$ | $3\tau$ | $5$ |
| $7$ | $\tau$ | $5$ |

The correct masses are constant over each entire first-zero fibre, with
no restriction on subsequent zeros. In row 3, $t=0$ gives
$4+u(1-v)+v(1-z)\le5$, since the last two terms cannot both be one.
For $t=1$ the expression is $4-uv-vz\le4$. Every other wrong-mass
entry is at most five by (300.4) or its displayed nonnegative products.
The residual branch adds only correct or base mass in classes 1 and 2,
and only base mass in later classes, so it adds no wrong mass.

For class 1, $13\tau\le a_1$ gives $c_1\le a_1$; when
$a_1\le17\tau$, $c_1=12\tau\ge a_1-5\tau$, and otherwise
$c_1=a_1-5\tau$. For class 2, $c_2=a_2-5\tau$. In all late
classes $c_n=a_n-5\tau$. Thus, for every zero word,

$$
a_n-c_n\le5\tau,\qquad
c_n+\delta_n-a_n\le\delta_n\le5\tau,\qquad
\delta_n\le5\tau.
\tag{300.5}
$$

These are separately the correct, base and independent union deficits
in (297.3). They prove all three rows for every word, including every
multiple-zero suffix and any negative singleton demand.

At the finite positive word the law is exactly

$$
p_+=(1-5\tau)\delta_0+2\tau\delta_3+\tau\delta_4+2\tau\delta_5.
\tag{300.6}
$$

For every actual $n>7$ it follows from (297.2) that its error is
$\max\{5\tau,a_n\}=5\tau$. This includes the closed tie
$a_8=5\tau$ and every specified positive vanishing tail. A positive
finite prefix represents actual later-zero sources, not an infinite
all-positive source. The late correct deficits also equal $5\tau$.

To execute the construction, partition one uniform seed $U\in[0,1)$
into the sixteen table intervals and the shared interval of length $\rho$.
Within the latter, use its affine coordinate as $V$; this is a coordinate
of the same seed, not an extra random input. The whole schedule and all
counterfactual outputs are thereby determined before replies. Execute only
that increasing schedule, stop at its first queried zero or exhaustion,
and emit the indicated actual $\theta_j$ on the full carrier. Every
source and seed has finite handoff, zero advice and at most two actual
requests. The same-seed $N$ completion obtains the entire schedule and
counts the ignored second request. The law is identical in both classes.

For the lower bound use the old five-late zero-cost score
[281.2](KBONACCI_SELF_CALIBRATING_ACQUISITION_RESOURCES_CONTINUATION_XVI.md),
whose necessary relation is $\sum_{j=3}^7a_j\le(46/5)\varepsilon$.
If any original arbitrary-address, full-carrier $N$ rule had error below
$5\tau$, choose a positive closed cap $\varepsilon<5\tau$ above
that error. Here $a_7=6\tau>\varepsilon$, so 110.2 supplies its
complete finite representative through address seven. Pairing the old
score gives $46\tau\le(46/5)\varepsilon$, a contradiction.
The same lower bound holds for every original $O$ by counted completion.
The constructed law attains it, and the same law is feasible at all
larger closed caps, irrespective of their changed active horizons.
$\square$

**Proposition 300.2 (Relation to the auxiliary hull and the earlier slice).**
When $a_2=13\tau$, the finite profile of Theorem 300.1 belongs to
$H_N$ with this same mass-one law. At $a_2>13\tau$ no membership in
the unreduced hull requiring $b_2=b_3$ is asserted. In particular
$(17,13,13,10,9,8,6)/24$, $e=5/24$, is attained in both classes.

**Proof.** Recall explicitly

$$
H_L=\{(b,e):1\ge b_1\ge\cdots\ge b_L\ge e\ge0,\ b_2=b_3,
\ 0\le E_b:=\sum_{j=3}^Lb_j-(L+1)e\le1-b_1\},
$$

and $H_N=\{(b,e)\in H_L:\exists\lambda\ge0,\ G_N\lambda\ge h\}$.
For $L=7$, $a_2=13\tau$ and $e=5\tau$, one has $E_b=6\tau$ and
$a_1+E_b\le1-\tau<1$ by the first head bound. The same law proves
full feasibility with mass one. If $a_2>13\tau=b_3$, the required
equality fails. The stated endpoint has $a_1=17\tau$, $a_2=13\tau$
and satisfies both head bounds. The earlier
[295.1](KBONACCI_SELF_CALIBRATING_ACQUISITION_RESOURCES_CONTINUATION_XVI.md)
already supplies its $a_1\le16\tau$, $a_2=13\tau$ slice; that old
attainment and the old $46/5$ lower bound are reused. The new assertion
is the coupled projection (300.2), including its necessary maximum scale.
It is not a classification of larger-cap optima outside that projection,
gapped primal laws or all feasible equality kernels. $\square$

## 301. Bounded exact comparisons and the consumed reductions

**Notation 301.1 (Only named finite comparison bases).**
In this section only, $L=7$, $J=(3,4,5,6,7)$,
$S=\sum_{j=3}^7b_j$, $R=(46/5)e-S$,
$v_a=b_{a+2}-r^\star_ae$, and $B=(72,30,18,18,36)$.
The reused relations are $R\ge0$ and $\pm v_a\le B_aR$ from
[293.2](KBONACCI_SELF_CALIBRATING_ACQUISITION_RESOURCES_CONTINUATION_XVI.md).
They also imply every necessary inequality supplied by the stated cone
in 294.1: if $\gamma=t\mathbf1+d$, $t\ge\sum_aB_a|d_a|$ and
$K\ge\gamma\cdot r^\star$, then

$$
\gamma\cdot b_J-Ke
\le-tR+\sum_a d_av_a
\le\left(-t+\sum_aB_a|d_a|\right)R\le0
$$

on these nonnegative-$e$ comparison points. This is a consequence of
the ten printed generators, not a claim about all possible uses of the
earlier full scores.

For recording a finite comparison, set

$$
D=b_2-1+2b_3+3b_4+3b_5+3b_6+4b_7-24e.
$$

Two weaker candidate relations are disposed of by exact reductions.
The first has left side $F_1$, so $F_1\le0$, $R\ge0$ imply
$F_1\le45R$. For the second,

$$
D=F_2+2R+2v_5.
\tag{301.1}
$$

The already specified coefficients $Z,H_7$ of
[292.1 and 292.8–292.9](KBONACCI_SELF_CALIBRATING_ACQUISITION_RESOURCES_CONTINUATION_XVI.md)
give the nonnegative zero-cost score $11Z-H_7$. Indeed the largest
positive coefficient ratio $H_7/Z$ is $5$, while its cell-gap estimate
is $|H_{7,ij,c}(\ell)-H_{7,ij,c}(0)|\le11D_{ij,c}$ with
$D_{ij,c}=Z_{ij,c}(0)-Z_{ij,c}(\ell)\ge0$. Hence both its coefficients
and its zero-label cell gaps are nonnegative. Its quotient is
$(0,0,33,33,33,33,34;1524/5)$, and its anchor is $694/5$.
Pairing this already available score with the same allocation gives
$v_5\le33R$. Together with $F_2\le0$, (301.1) yields
$D\le68R\le72R$. The auxiliary bound is consumed in this reduction;
neither residual relation is retained as a separate result. In particular,
non-implication within a finite basis omitting $v_5\le33R$ says nothing
about non-implication after this explicit prior consequence is included.

**Definition 301.2 (An exact 77-inequality comparison system).**
All the following inequalities have their usual left-minus-right
reading at most zero. The twelve hull inequalities mean
$b_1\le1$, $b_{i+1}\le b_i$ for $1\le i\le6$, $e\le b_7$,
$0\le e$, $b_2\le b_3$, $E=S-8e\ge0$ and $b_1+E\le1$;
the chain and $b_2\le b_3$ together give $b_2=b_3$.

| Family | Explicit inequalities | Count |
| --- | --- | ---: |
| Hull | the twelve inequalities just specified | 12 |
| Scalar | $R\ge0$ | 1 |
| Ratio generators | $\pm v_a\le B_aR$, $1\le a\le5$ | 10 |
| Consumed prior consequence | $v_5\le33R$ | 1 |
| Selected heads | $F_1\le0$, $F_2\le0$ | 2 |
| Four-late | $\sum_{j\in I}b_j\le8e$, $I\subset J$, $|I|=4$ | 5 |
| Weighted subsets | $\sum_{j\in I}b_j\le(|I|+21/5)e$, $\varnothing\ne I\subset J$ | 31 |
| 113 prefixes | $b_1+\sum_{j=3}^mb_j\le1+(m+1)e$, $3\le m\le7$ | 5 |
| 117 prefixes | $(m-3)b_2+(m-2)\sum_{j=3}^mb_j\le m-3+(m-2)(m+1)e$, $4\le m\le7$ | 4 |
| 235 prefixes | $c_mb_2+(d_m-1)b_3+d_m\sum_{j=4}^mb_j\le c_m+((m+1)d_m-1)e$, $4\le m\le7$ | 4 |
| 240 | $2b_2+4b_3+6b_4+5b_5+6b_6+6b_7\le2+45e$ | 1 |
| 241 | $10b_3+14b_4+13b_5+14b_6+14b_7\le117e$ | 1 |

Here $d_m=m(m-3)/2$ and $c_m=d_m-m+2$. The weighted subset family
is the indicator-generator form of
[282.1](KBONACCI_SELF_CALIBRATING_ACQUISITION_RESOURCES_CONTINUATION_XVI.md);
the other numbered families are
[113.2 and 117.2](KBONACCI_SELF_CALIBRATING_ACQUISITION_RESOURCES_CONTINUATION.md)
and [235.3, 240.1 and 241.1](KBONACCI_SELF_CALIBRATING_ACQUISITION_RESOURCES_CONTINUATION_XIV.md).
These are exactly the listed constraints, not all historical consequences.

**Proposition 301.3 (A strict off-equality-face comparison for $C$).**
The rational point

$$
b=(10392,10392,10392,6350,6350,6350,6207)/16838,
\qquad e=3880/16838
\tag{301.2}
$$

satisfies all 77 inequalities in 301.2, whereas
$F_C=1609/8419>0$. Thus $C$ adds a relation relative to that precise
finite comparison system. This point has no full feasible $N$ allocation
and is neither an attainer nor a separator.

**Proof.** Order and $b_2=b_3$ are immediate. One has
$E=4609/16838$ and $b_1+E=15001/16838<1$, while
$R=47/16838$, $F_1=-554/8419$, $F_2=0$, and
$v_5-33R=0$. Here are exact remaining readings. The ratio pairs are
listed as $(v_a-B_aR,-v_a-B_aR)$ in increasing $a$:

$$
\begin{gathered}
(-1540,-1844)/8419,\quad(-1410,0)/8419,\quad
(-740,-106)/8419,\\
(-352,-494)/8419,\quad(-141,-3243)/16838.
\end{gathered}
$$

The four-late readings, in lexicographic order of their subsets, are
$(-1598,-1741,-1741,-1741,-5783)/16838$.
For a weighted subset of size $k$, order makes its reading at most
$\sum_{j=3}^{k+2}b_j-(k+21/5)e$; for $k=1,\ldots,5$ these maxima are

$$
-4892/8419,\quad-3657/8419,\quad-2422/8419,\quad
-1187/8419,\quad-47/16838.
$$

The 113 prefix readings in increasing $m$ are
$(-5787,-4552,-3317,-2082)/8419$ followed by $-1837/16838$.
The 117 readings are
$(-5881,-6728,-5105)/8419$ followed by $-2739/16838$.
The 235 readings are $(-5914,-10172,-9102,0)/8419$.
The 240 and 241 readings are $-366/8419$ and $-1396/8419$.
All are nonpositive, exhausting the explicit families. Finally (299.2)
gives $F_C=1609/8419$. Theorem 299.1 therefore excludes full feasibility
at this point. The finite comparison proves no exhaustive historical
nonderivability and no assertion about unrestricted combinations of earlier
theorems. $\square$

**Definition 301.4 (The second finite comparison basis).**
Use the same twelve hull inequalities, $R\ge0$, all ten ratio
generators and all 31 weighted subset inequalities. For every nonempty
$I\subset J$ of size $k$, include the embedded 113 inequality

$$
b_1+\sum_Ib_j\le1+(k+3)e,
$$

and for every $2\le k\le5$ include the embedded 117 inequality

$$
(k-1)b_2+k\sum_Ib_j\le k-1+k(k+3)e.
$$

Include also the old one-pivot and protected-stock consequences

$$
\sum_Ib_j\le c_ke,\qquad
(k,c_k)=(1,4),(3,7),(4,8),(5,28/3),
\tag{301.3}
$$

for every subset of the indicated size. Their suppliers are
[198.7](KBONACCI_SELF_CALIBRATING_ACQUISITION_RESOURCES_CONTINUATION_VI.md)
and [207.12–207.13](KBONACCI_SELF_CALIBRATING_ACQUISITION_RESOURCES_CONTINUATION_IX.md).
For the latter, $k=h+1$ protected labels use stock
$4-2/\lceil(h+1)/2\rceil$, terminal weight one and correct total $k$,
giving $c_k=k+5-2/\lceil k/2\rceil$ at $k=3,4,5$.

Finally take the four comparison inequalities $F_1\le0,F_2\le0,
F_C\le0,D\le72R$, and omit one of them. The resulting system has
$12+1+10+31+31+26+21+3=135$ inequalities. It expressly omits the
consumed prior consequence $v_5\le33R$. Its inclusion of $D\le72R$
serves only to specify this bounded comparison, not to retain a separate
necessary theorem.

**Proposition 301.5 (Exact bounded non-implications).**
For each omitted relation in the following table, the specified rational
point satisfies all 135 other inequalities in 301.4 and violates that
omitted relation by the final column.

| Omitted relation | $b$ | $e$ | Positive reading |
| --- | --- | --- | --- |
| $F_1\le0$ | $(20299,12873,12873,12873,12873,12873,12873)/28584$ | $3505/14292$ | $425/9528$ |
| $F_2\le0$ | $(347,347,347,347,347,347,176)/555$ | $176/555$ | $49/555$ |
| $D\le72R$ | $(653,653,653,653,636,636,636)/1434$ | $175/717$ | $2/239$ |
| $F_C\le0$ | $(532,532,532,293,293,293,293)/807$ | $371/1614$ | $391/1614$ |

These are non-implications from the expressly named finite basis. They
are compatible with the reduction (301.1), whose consumed prior
consequence is absent from that basis. No point is claimed $N$-feasible.

**Proof.** The following tables give exact certificates for all the
families, in the same order of points as above. For any subset size $k$,
monotonicity makes $t_k=\sum_{j=3}^{k+2}b_j$ the largest subset sum.
Hence maxima over subsets are obtained from the explicit expressions

$$
\begin{array}{ll}
W_k=t_k-(k+21/5)e,&1\le k\le5,\\
A_k=b_1+t_k-1-(k+3)e,&1\le k\le5,\\
B_k=(k-1)b_2+kt_k-(k-1)-k(k+3)e,&2\le k\le5,\\
P_k=t_k-c_ke,&k=1,3,4,5.
\end{array}
\tag{301.4}
$$

Taking the maximum of these finite lists, and of the ten ratio readings,
gives:

| Point | $R$ | $E$ | $b_1+E$ | $\max_a(|v_a|-B_aR)$ |
| --- | --- | --- | --- | --- |
| First | $127/28584$ | $8285/28584$ | $1$ | $-37/9528$ |
| Second | $92/925$ | $52/185$ | $503/555$ | $-1547/925$ |
| Third | $1/239$ | $69/239$ | $1067/1434$ | $0$ |
| Fourth | $13/4035$ | $220/807$ | $752/807$ | $0$ |

| Point | $\max W_k$ | $\max A_k$ | $\max B_k$ | $\max P_k$ |
| --- | --- | --- | --- | --- |
| First | $-127/28584$ | $0$ | $-21419/28584$ | $-3185/85752$ |
| Second | $-92/925$ | $-52/555$ | $0$ | $-4/111$ |
| Third | $-1/239$ | $-367/1434$ | $-527/717$ | $-79/2151$ |
| Fourth | $-13/4035$ | $-55/807$ | $0$ | $-82/2421$ |

The remaining hull order and $0\le e\le b_7$ conditions follow
directly from the displayed coordinates. The four selected readings are:

| Point | $F_1$ | $F_2$ | $F_C$ | $D-72R$ |
| --- | --- | --- | --- | --- |
| First | $425/9528$ | $-4/3573$ | $0$ | $0$ |
| Second | $-24/185$ | $49/555$ | $0$ | $-19427/2775$ |
| Third | $-101/478$ | $0$ | $0$ | $2/239$ |
| Fourth | $-41/1614$ | $0$ | $391/1614$ | $-206/4035$ |

All these fractions follow by substitution into (299.1), (301.1) and
(301.4), which specify every coefficient. The positive omitted readings
and nonpositive remaining maxima prove the finite non-implications.
For the third point the excluded prior consequence has reading
$v_5-33R=3/239>0$, explicitly showing why it cannot refute the stronger
reduction. By Theorem 299.1 and the reduction, the points possess no full
feasible $N$ allocation. They give no separator, exhaustive independence
or novelty assertion. $\square$

## 302. A whole-sequence comparison with named older cuts

**Proposition 302.1 (An excluded tested cap, without an asserted attainer).**
Let

$$
(a_1,\ldots,a_7)=(117,117,117,90,81,72,54)/200,
\qquad e=9/40,
\tag{302.1}
$$

and append any positive nonincreasing vanishing tail with $a_8\le e$.
At this profile $E=27/100$, $a_1+E=171/200$, $R=0$ and
$b_J=r^\star e$. The $Y_2$ and $C$ readings are respectively
$2/25$ and $8/25$. Every original $N$, hence every original $O$, has
error at least $227/1000>225/1000=e$. No law attaining $227/1000$
is asserted.

**Proof.** The weighted sum in $Y_2$, including $a_2$, is $224\tau$
with $\tau=9/200$. Thus its uniform original necessary inequality is
$40e_a(A)\ge224\tau-1$, giving $e_a(A)\ge227/1000$.
At the tested cap $e=5\tau$, $F_2=24\tau-1=2/25$, and (299.2)
gives $F_C=8/25$.

For comparison, the older named prefix and full cuts have these exact
left-minus-right readings:

| Family | $m=4$ | $m=5$ | $m=6$ | $m=7$ |
| --- | --- | --- | --- | --- |
| 117.2 | $-119/200$ | $-14/25$ | $-69/200$ | $-31/100$ |
| 235.3 | $-27/50$ | $-37/50$ | $-41/100$ | $-63/200$ |

The 113.2 residual reading is $-29/200$; the readings of 240.1 and
241.1 are $-11/100$ and $-9/100$. For
[256.3](KBONACCI_SELF_CALIBRATING_ACQUISITION_RESOURCES_CONTINUATION_XV.md),
the reading is
$2a_2+4a_3+4a_4+5(a_5+a_6+a_7+a_8)-2-43e\le-13/200$.

The 113 reading follows from
$a_1+\sum_{j=3}^7(a_j-e)-3e-1=-29/200$; later inactive terms
vanish. For 117 prefixes $m\ge7$, replace every later amplitude by
$e$ to maximize its positive-coefficient reading. The result is
$(141-29m)/200<0$. For 235 prefixes, with $d_m=m(m-3)/2$, the
same padding gives

$$
[-29d_m+83(m-2)-72]/200.
$$

At $m=7$ this is $-63/200$; its successive difference is
$[83-29(m-1)]/200<0$. Actual later amplitudes only decrease both
readings. Monotonicity likewise bounds ordered gap placements of these
nonnegative old coefficients by their consecutive placements.

For all weighted five-late inequalities of 282.1, write their bound as
$\sum\gamma_ab_{j_a}\le(G+(21/5)\mu)e$, where
$G=\sum\gamma_a$, $0\le\gamma_a\le\mu$. On the consecutive
core, $r^\star_a>1$ and $\sum_a(r^\star_a-1)=21/5$, so
$\sum\gamma_a(r^\star_a-1)\le(21/5)\mu$. Ordered gap placements
cannot increase the left side; later coordinates at or below $e$ do
not add positive residual. The selected core ratio generators and their
294.1 cone consequences also pass, with equality at their least $K$.
These computations compare only the named older families; they do not
assert passage of every historical theorem or existence of a full
feasible allocation. $\square$

**Proposition 302.2 (A scalar-and-ratio comparison point).**
At $b=(13,13,13,10,9,8,6)/23$, $e=5/23$, one has $E=6/23$,
$b_1+E=19/23$, $R=0$ and $b_J=r^\star e$. Thus the old scalar and
ten ratio relations, and their stated nonuniform-cone consequences,
hold, whereas $F_2=1/23$ and $F_C=4/23$. This is only a comparison
with those relations.

**Proof.** Substitute $\tau=1/23$ into the displayed expressions.
The profile is in $H_7$, but Theorem 299.1 excludes any full feasible
$N$ allocation. Hence it is neither an attainer nor an $N/O$ separator.
The additional ceiling is already part of Theorem 300.1 and is not a
second scale result. $\square$

## 303. The remaining unrestricted alternative and literature boundary

**Definition 303.1 (The original unrestricted obligation).**
With the complete score, quotient, hull and signed support conventions
of 297.5 and 300.2, the positive universal assertion still requires:
for every full $y\ge0$ with $\Delta_O(y)\le1$, there are one
unrestricted full $V\ge0$ and one $\theta\in[0,1]$ such that

$$
\Delta_N(V)+\theta\le1,\qquad
\sigma_H(Qy-QV)\le\theta,\qquad
\sigma_H(q)=\max_{(b,e)\in H_L}F_q(b,e).
\tag{303.1}
$$

The residual is signed; nonzero zero-cost $V$ at $\theta=1$ remains
allowed. The alternative negative witness would require the same actual
$(b,e)\in H_N$, one full feasible $\lambda\ge0$ of mass $M\ge1$,
one full unit-$O$ score with $F_{Qy}(b,e)>M$, an actual original
$N$ attainer and a uniform strict lower transport against **every**
original arbitrary-address, full-carrier $O$ competitor. All the
source, common-seed, zero-advice, finite-handoff, hard-two-actual-request,
all-word, all-label, independent-union, positive-tail and closed-cap
conditions remain in both alternatives.

Neither alternative is established by the results here. Theorems 299.1
are necessary relations, and Theorem 300.1 constructs equal attained
optima on its specified contiguous ray and head domain. They give no
one-budget replacement for an arbitrary full unit-$O$ input. All the
strict comparison points in 301–302 lack a full feasible $N$ allocation,
so cannot satisfy the required negative alternative.

**Example 303.2 (Earlier unqueried labels remain legal).**
At the actual source $(r,g)=(19,436)$, $F_{19}=4181$,
$419\le436\le836$ and $N=1822917$. The first four prime replies
are $0100$. The legal rule $N(3,4;1,0,0,0)$ makes its two actual
requests at 3 and 4 and outputs the earlier **unqueried** label 1.
The endpoint stopped rule $O(3,4;0,0,0)$ outputs zero there. Changed
mass is one, and the $\ell^1$ counting defect is two (TV one).
This is an obstruction to that repair being free, not a separator
between the original acquisition classes. No result here deletes this
word, label or counted pair of requests.

**Literature scope 303.3.**
The integer supporting scores, their finite comparisons and the coupled
head theorem above are repository-derived ordinary mathematics. Their
proofs are the complete row data and arguments given here, together
with the specifically cited earlier source, score and transport results.
No exhaustive novelty or priority claim is made.

David Blackwell, *Comparison of Experiments*, Second Berkeley Symposium
(1951), pp. 93–102,
[sections 2–3 and Theorem 2](https://digitalassets.lib.berkeley.edu/math/ucb/text/math_s2_article-08.pdf),
defines an experiment as finitely many probability measures on a Borel
space, bounded vector-valued actions and attainable whole loss vectors
under decision procedures and their convex closure. Its comparison and
supporting-hyperplane argument concern that entire attainable vector.
This is the literature-attested comparison framework. It does not
provide a reverse hard-two increasing-stopping construction or the
specific row coefficients in 298.

Jędrzej Kaniewski, Troy Lee and Ronald de Wolf, *Query complexity in
expectation*, [arXiv:1411.7280v1](https://arxiv.org/pdf/1411.7280v1),
Definitions 6 and 8 and both directions of Theorem 9, characterize
nonnegative scalar expectation by nonnegative literal degree. Their
randomized cost is maximum supported root-to-leaf depth. In the converse,
coefficients of total mass $M$ are sampled with probabilities
$\alpha/M$ and the scalar output is multiplied by $M$. This gives
the stated scalar expectation; it does not give a normalized joint
probability-vector output law, equal counterfactual schedule-cell masses,
or an increasing first-queried-zero stopped rule. None of those missing
conditions is imported into (300.2) from that characterization.

## 追加锚（本行以下为增补区）
