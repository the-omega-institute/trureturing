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

## 304. Additional correct rows and one collective residual constraint

All source, carrier, target, resource, event-row and complete-allocation
conventions in 297 remain in force. In particular, the original nonatomic
targets and consumer are those of 297.1; error statements here concern the
separately selected marked laws (297.1). A finite profile need not be
ordered or belong to $H_L$ unless explicitly stated. Scores are
nonnegative event weights, whereas an allocation is the single vector
$\lambda$ satisfying every row of $G_C\lambda\ge h(b,e)$.

**Definition 304.1 (A sole-zero extension of the second-head score).**
Fix $L\ge7$, an ordered skeleton
$S=(1,2,j_1,\ldots,j_5)$ with $3\le j_1<\cdots<j_5\le L$,
and any finite set $I\subseteq\{1,\ldots,L\}\setminus S$.
Embed exactly the score $Y_2$ of 298.2 on $S$, with every nonskeleton
bit equal to one on its scored words. For $k\in I$ let $w^{(k)}$
have its sole zero at $k$, and, for arbitrary real $c_k\ge0$, set

$$
Y_c=Y_2+\sum_{k\in I}c_k C_{w^{(k)}}.
\tag{304.1}
$$

Here $C_{w^{(k)}}$ is the correct event row of weight one, not a
restriction on the output alphabet. Let $c_{[1]}\ge c_{[2]}\ge c_{[3]}$
be the three largest weights, padded by zeros. Empty sums and maxima
of nonnegative residuals are zero. The set $I$ may lie in gaps of $S$;
it need not follow $j_5$.

**Theorem 304.2 (Exact full support at every finite embedding).**
For every such $L,S,I,c$, the complete supports and anchor are

$$
\begin{aligned}
B_N(Y_c)=B_O(Y_c)
 &=\max\{17,\ 16+c_{[1]}+c_{[2]},\
                    c_{[1]}+c_{[2]}+c_{[3]}\},\\
W_{Y_c}&=17,\\
\Delta_N(Y_c)=\Delta_O(Y_c)
 &=\max\{0,\ c_{[1]}+c_{[2]}-1,\
                    c_{[1]}+c_{[2]}+c_{[3]}-17\}.
\end{aligned}
\tag{304.2}
$$

In particular zero excess is equivalent to $c_{[1]}+c_{[2]}\le1$.
The formula also describes all positive-excess regimes.

**Proof.** The reused 22 rows in 298.2 give constant-zero reward 16.
Their singleton cell maxima, in skeleton order, are

$$
(6,10),\ (6,10),\ (7,9),\ (7,9),\ (8,8),\ (9,7),\ (12,4).
\tag{304.3}
$$

These follow by the full-label addition rule (298.2). Every singleton
support is 16. Every $11$ entry of the $Y_2$ pair certificate in 298.4
is at least four. These are properties of that existing score, which
also has full support 17 and is attained by $R$.

Consider an arbitrary deterministic $N$ table with two distinct
queries. If both queries are in $S$, all new words lie in its $11$
cell. To earn any new correct reward its output there must be a label
in $I$. That label earns no old reward, losing at least four from the
old pair-cell maximum. Thus its total is at most $13+c_{[1]}$;
if it earns no new reward, the total is at most 17. Both bounds are
at most the maximum in (304.2).

If exactly one queried coordinate is in $S$, old scored words supply
only singleton information, with old reward at most 16. All new words
have value one at the skeleton query, so occupy at most two cells of
the pair. At most two distinct correct labels can be rewarded there,
with total at most $c_{[1]}+c_{[2]}$.

If neither query is in $S$, all old scored words lie in $11$.
When that cell's output is outside $I$, its old reward is at most 16
and at most two new correct rewards can occur in the other cells.
When its output is in $I$, old reward is zero and at most three new
correct rewards occur. Indeed, for sole-zero words the only possible
cells are $01,10,11$; a fixed cell output rewards at most one of
their distinct first-zero labels. This gives the last two branches
of the maximum. Unscored outside coordinates are included in these
cases. Constants and singleton or repeated schedules have coarser
information and obey the same bounds; reversal just permutes cells.
All labels, including earlier and unqueried ones, have been allowed.

For attainment, $R$ earns 17 and earns zero on every added correct
row. With at least two weights, query the addresses of two largest
weights increasingly, emit the queried first address at its first
zero, the second address at $10$, and zero at $11$. This stopped
table earns $16+c_{[1]}+c_{[2]}$. For one weight the singleton
$(k;k,0)$ earns $16+c_{[1]}$; for none this branch is 16 and
does not exceed 17. With at least three weights, query any two of
their three largest-weight addresses and emit the remaining label at
$11$. The stopped table earns their sum and no old reward. For fewer
than three weights that branch is dominated by the preceding branch.
These are actual legal stopped schedules regardless of the gaps in
$S$ or the order of addresses in $I$. Since $O\subseteq N$, the
upper bounds and these stopped attainers give both support equalities.
The anchor remains 17 because $R$ emits zero on every new word.
Subtracting it proves the excess formula. Finally
$c_{[1]}+c_{[2]}\le1$ implies
$c_{[1]}+c_{[2]}+c_{[3]}\le3/2<17$, proving the zero-excess
equivalence, including ties and zero coefficients. $\square$

**Theorem 304.3 (Collective residuals of the same full allocation).**
For any real finite profile $(b,e)$ and any one complete feasible
$N$ allocation of any finite mass $M$, put

$$
s=1+40e-b_2-4b_{j_1}-5b_{j_2}-5b_{j_3}-5b_{j_4}-4b_{j_5}.
\tag{304.4}
$$

Then, for every $c\ge0$ as in 304.1,

$$
\sum_{k\in I}c_k(b_k-e)\le s+
 M\max\{0,c_{[1]}+c_{[2]}-1,c_{[1]}+c_{[2]}+c_{[3]}-17\}.
\tag{304.5}
$$

Consequently

$$
s\ge\max\left\{\max_{k\in I}(b_k-e)_+,\
                    \frac12\sum_{k\in I}(b_k-e)_+\right\}.
\tag{304.6}
$$

The same conclusions hold for a complete $O$ allocation. For every
entire sequence (297.1), every original rule in either class meeting
any positive closed cap $e$, and every ordered skeleton, they hold
with $b=a$ for every finite disjoint $I$. In particular

$$
s\ge\max\left\{(a_{j_5+1}-e)_+,\
                 \frac12\sum_{k>j_5}(a_k-e)_+\right\}.
\tag{304.7}
$$

No summability of $a$ is required.

**Proof.** Equation (297.5) applied to this same given $\lambda$ and
the single score $Y_c$ gives $F_{QY_c}\le M\Delta_N(Y_c)$.
The old quotient contributes $-s$ and each added correct row
contributes $c_k(b_k-e)$, proving (304.5). Taking $c=0$ gives
$s\ge0$. A unit weight at one chosen coordinate gives each individual
positive-residual bound. Giving weight $1/2$ exactly to the coordinates
with $b_k>e$ gives the half-sum bound. Both choices have zero excess
by 304.2. This clips only the chosen score coefficients, never any
original demand. These are simultaneous necessary inequalities about
the same profile and allocation, not an assertion that different
extrema have a common attainer. Counted completion gives the $O$ case.

For an original rule at $0<e\le1$, apply the exact closed-cap
transport and prefix operations of 297.3 at
$K=\max(S\cup I)$. A longer active representative is restricted by
fixing higher replies to zero and projecting higher labels to zero;
a shorter representative is extended by ignored inputs. At an added
first zero its exact error is $\max\{1-p_+(0),a_n\}\le e$.
Thus all three rows, including negative singleton demands and the
independent union row, hold for one full representative. Apply
(304.6) to it. When $e\ge1$ the residuals vanish, and
$s\ge1+40-24=17$. Finally $a_k\to0$ makes the set
$\{k:a_k>e\}$ finite. Choose its members beyond $j_5$ as $I$;
monotonicity identifies the largest residual there with
$(a_{j_5+1}-e)_+$. This proves (304.7) for every actual positive
tail, including its closed ties. $\square$

## 305. A six-late integer score and the saturated-head tail boundary

**Definition 305.1 (An eight-coordinate score).**
On coordinates $1,\ldots,8$ give exactly the following independent
rows their integer weights. Every $A$ and every unlisted coefficient
is zero; all corresponding constraints remain present.

| Row | Word | Weight |
| --- | --- | ---: |
| P | 00110000 | 1 |
| P | 00110010 | 3 |
| P | 01001010 | 3 |
| P | 01010001 | 3 |
| P | 01010010 | 2 |
| P | 01010100 | 1 |
| P | 01011001 | 3 |
| P | 01100001 | 1 |
| P | 01100010 | 1 |
| P | 01100100 | 4 |
| P | 01101000 | 3 |
| P | 10001000 | 3 |
| P | 10001001 | 1 |
| P | 10001010 | 1 |
| P | 10010010 | 3 |
| P | 10010100 | 3 |
| P | 10011000 | 1 |
| P | 10100001 | 6 |
| P | 10101000 | 1 |
| C | 10110000 | 4 |
| C | 11000011 | 5 |
| P | 11000100 | 4 |
| C | 11001101 | 3 |
| C | 11010000 | 7 |
| C | 11011110 | 1 |
| C | 11100000 | 12 |
| C | 11100001 | 4 |
| C | 11101000 | 4 |
| C | 11110000 | 8 |
| C | 11110101 | 8 |
| C | 11110110 | 4 |
| C | 11111000 | 16 |
| C | 11111011 | 4 |
| C | 11111100 | 16 |
| C | 11111110 | 16 |
| T | 11111111 | 16 |

**Theorem 305.2 (Full support and the all-mass six-late cut).**
This score $Z_6$ has

$$
\beta=(0,4,16,20,20,20,16,16),\quad K=176,\quad
W=B_N=B_O=68,\quad\Delta_N=\Delta_O=0.
\tag{305.1}
$$

For every $L\ge8$, every $3\le j_1<\cdots<j_6\le L$,
every real finite profile and one complete feasible allocation in
either class of any finite mass,

$$
b_2+4b_{j_1}+5b_{j_2}+5b_{j_3}+5b_{j_4}+4b_{j_5}+4b_{j_6}
\le1+44e.
\tag{305.2}
$$

Every original arbitrary-address, full-carrier competitor in either
class satisfies the same bound with its actual amplitudes and every
positive closed cap it meets. In particular

$$
44e_a(A)\ge
a_2+4a_{j_1}+5a_{j_2}+5a_{j_3}+5a_{j_4}+4a_{j_5}+4a_{j_6}-1.
\tag{305.3}
$$

**Proof.** Direct class summation gives the displayed $\beta$ and
$K$. The union weights sum to 48, the early correct weight to four,
and the positive weight is 16. Hence $R$ earns $48+4+16=68$.
For completeness the following is the full pair-cell certificate.
For each cell maximize the sum of its row rewards over all nine
labels $0,\ldots,8$, exactly as in (298.2).

| Pair | Maxima in $00,01,10,11$ |
| --- | --- |
| 12 | $(4,21,23,20)$ |
| 13 | $(12,13,20,23)$ |
| 14 | $(12,13,20,23)$ |
| 15 | $(16,9,20,23)$ |
| 16 | $(20,5,20,23)$ |
| 17 | $(16,9,20,20)$ |
| 18 | $(18,7,16,23)$ |
| 23 | $(12,11,20,25)$ |
| 24 | $(12,11,20,25)$ |
| 25 | $(16,7,20,25)$ |
| 26 | $(20,3,20,25)$ |
| 27 | $(19,7,20,22)$ |
| 28 | $(16,7,18,23)$ |
| 34 | $(12,16,20,20)$ |
| 35 | $(16,12,20,20)$ |
| 36 | $(20,8,20,20)$ |
| 37 | $(19,9,20,20)$ |
| 38 | $(21,8,16,23)$ |
| 45 | $(16,12,20,20)$ |
| 46 | $(20,8,20,20)$ |
| 47 | $(23,5,16,24)$ |
| 48 | $(20,8,16,22)$ |
| 56 | $(20,12,20,16)$ |
| 57 | $(23,9,16,20)$ |
| 58 | $(22,10,16,20)$ |
| 67 | $(23,13,16,16)$ |
| 68 | $(22,14,16,16)$ |
| 78 | $(21,14,16,16)$ |

Every vector sums to at most 68. Each unrestricted pair table chooses
one output in each cell and is therefore bounded by that sum. Empty,
singleton and repeated schedules coarsen pair information, reversal
permutes cells, and a stopped table merges $00,01$. These operations
cannot increase the sum of cell maxima. Since $R$ attains 68 in both
classes, (305.1) follows for their entire catalogs.

Embed the eight coordinates as $(1,2,j_1,\ldots,j_6)$ with all other
scored bits one. A query outside the skeleton is constant on the scored
support, and an outside label earns zero. Thus arbitrary queries give
one of the displayed partitions or a coarsening. This proves the bound
at every finite embedding, without removing any unscored event row.
Pair this single nonnegative score with the same full allocation:
$F_{QZ_6}\le M\Delta_N(Z_6)=0$. Its quotient is four times the
left-minus-right expression in (305.2), proving that expression is
nonpositive. The argument uses every original demand and permits every
real profile and finite mass.

For an original rule use 297.3 at prefix $j_6$, with its restriction
or extension as needed, and apply (305.2) to its one normalized finite
representative. At caps at least one the bound follows from
$a_i\le1$, since the left side is at most 28. Applying the result
at every positive cap above $e_a(A)$ and decreasing those caps to
the error proves (305.3), also when that error is zero. $\square$

**Theorem 305.3 (The precise tail condition on a saturated second head).**
Let $\tau>0$ and take an entire positive nonincreasing vanishing
sequence with

$$
a_2=1-11\tau,\quad (a_3,\ldots,a_7)=(13,10,9,8,6)\tau,
\quad1\ge a_1\ge a_2.
\tag{305.4}
$$

The tail is subject only to the sequence order, not initially to
$a_8\le5\tau$. At the closed cap $5\tau$, feasibility in either
original class is equivalent to

$$
a_1+7\tau\le1\quad\hbox{and}\quad a_8\le5\tau.
\tag{305.5}
$$

In those feasible cases both optima are attained at $5\tau$. If
$a_8>5\tau$, every original competitor in either class has error
at least

$$
5\tau+\frac{a_8-5\tau}{11}>5\tau.
\tag{305.6}
$$

**Proof.** Order gives $1-11\tau\ge13\tau$, hence
$\tau\le1/24$. The first necessary relation of 299.1 gives
$a_1+7\tau\le1$ at cap $5\tau$, regardless of the tail.
The five weighted late terms in (305.2) sum to $211\tau$.
With $j_a=a+2$, (305.2) at that cap becomes
$a_2+11\tau+4(a_8-5\tau)\le1$, so (305.4) forces
$a_8\le5\tau$. Conversely, under (305.5) all hypotheses of
Theorem 300.1 hold. Its one common stopped law and counted completion
attain $5\tau$; its old five-late lower bound proves optimality.
At a general error $r$, (305.3) gives
$44r\ge a_2+211\tau+4a_8-1=200\tau+4a_8$,
which is exactly (305.6).

For example, take $\tau=1/24$, $a_1=a_2=a_3=13/24$,
$a_8=11/48$, the other late amplitudes as in (305.4), and
$a_n=(5/24)2^{-(n-9)}$ for $n\ge9$. The closed tie
$a_9=5/24$ is allowed. At the tested cap $5/24$ the six-late
left-minus-right reading is $1/12$, and (305.6) gives $37/176$.
This excludes that cap in both classes; it supplies no feasible $N$
allocation there and therefore no separator. Attainment of the general
larger-cap bound (305.6) is not asserted. $\square$

## 306. A positive cap strip with two jointly filled heads

**Theorem 306.1 (Exact closed-cap head projection on the strip).**
For every real $\tau>0$ and $0\le\delta\le\tau/40$, put
$e=5\tau+\delta$. Prescribe

$$
(a_3,\ldots,a_7)=(13,10,9,8,6)\tau,\qquad
1\ge a_1\ge a_2\ge13\tau,
\tag{306.1}
$$

and append any positive nonincreasing vanishing tail with $a_8\le e$.
Then original $\mathcal N_2$ feasibility at this closed cap, original
$\mathcal O_2$ feasibility there, and the conjunction

$$
a_1\le1-7\tau+17\delta,
\qquad a_2\le1-11\tau+40\delta
\tag{306.2}
$$

are equivalent. The following explicit single allocation realizes all
feasible heads simultaneously.

**Construction 306.2 (The raw core and one shared prefix).**
Write $e_r$ for the label unit vector. In this table a row consists
of one schedule, its mass $m$, and its three unnormalized terminal
vectors $f,v,z$ for stopped cells $0,10,11$. Each of these vectors
has the same mass $m$. A range in a row means a separate schedule
for every indicated value. All undisplayed vector coordinates are zero.

| Schedule | $m$ | $f$ | $v$ | $z$ |
| --- | --- | --- | --- | --- |
| $(1,2)$ | $8\tau-34\delta$ | $m e_1$ | $m e_2$ | $(4\tau-27\delta)e_0+(2\tau-23\delta)e_3+(\tau-3\delta)e_4+(\tau+5\delta)e_5+14\delta e_6$ |
| $(h,3)$, $h=1,2$ | $3\tau+11\delta$ | $m e_0$ | $m e_3$ | $m e_0$ |
| $(h,4)$, $h=1,2$ | $\tau-9\delta$ | $(\tau-38\delta)e_0+29\delta e_h$ | $m e_4$ | $m e_0$ |
| $(h,5)$, $h=1,2$ | $4\delta$ | $m e_h$ | $m e_5$ | $m e_0$ |
| $(h,6)$, $h=1,2$ | $4\delta$ | $m e_0$ | $m e_6$ | $m e_0$ |
| $(3,4)$ | $2\tau+20\delta$ | $m e_0$ | $m e_4$ | $(\tau+16\delta)e_0+(\tau+4\delta)e_5$ |
| $(3,5),(3,6),(4,5),(4,6)$ | $\tau-9\delta$ | $m e_0$ | $m e_j$ for schedule $(i,j)$ | $m e_0$ |
| $(5,6)$ | $\tau-5\delta$ | $m e_0$ | $m e_6$ | $(\tau-9\delta)e_0+4\delta e_7$ |
| $(6,7)$ | $\tau-5\delta$ | $m e_0$ | $m e_7$ | $m e_0$ |

The sixteen schedule masses sum to $24\tau-40\delta$.
Define

$$
\begin{gathered}
\rho=1-24\tau+40\delta,\qquad T_0=4\tau-23\delta,\\
u=\min\{a_1-13\tau,T_0\},\qquad
q_1=a_1-13\tau-u,\qquad q_2=a_2-13\tau.
\end{gathered}
\tag{306.3}
$$

In the first cells of $(1,3),(1,4),(1,6)$, move the fraction
$u/T_0$ of each label-zero mass to label 1. Their combined available
zero mass is precisely $T_0$. Add just one more schedule $(1,2)$ of
mass $\rho$, with terminal vectors

$$
(\rho-q_1)e_0+q_1e_1,\qquad
(\rho-q_2)e_0+q_2e_2,\qquad \rho e_0.
\tag{306.4}
$$

If $\rho=0$ omit this row. Within a positive row of mass $m$,
one explicit complete-table coupling assigns to
$O(i,j;r_0,r_{10},r_{11})$ mass

$$
\frac{f(r_0)v(r_{10})z(r_{11})}{m^2}.
\tag{306.5}
$$

Summing over the other two labels recovers the required cell vector,
and the sum over all three labels is $m$. Zero-mass rows are omitted.
Thus these are full table weights with one total probability budget.
Equivalently, on each row interval all three counterfactual labels
can be fixed by quantile partitions of the same local seed coordinate.
Neither description requires $q_1+q_2\le\rho$.

**Proof of Theorem 306.1.** The two existing all-competitor cuts
299.1 give, at the prescribed late amplitudes,

$$
a_1+92\tau\le1+17e,\qquad
a_2+211\tau\le1+40e.
\tag{306.6}
$$

These are exactly (306.2). Their original closed-cap necessity includes
arbitrary addresses, full-carrier outputs and inactive selected addresses
by 297.3. It does not require an active horizon exactly seven.

Assume (306.2). Since $a_2\ge13\tau$, the second condition gives
$\rho\ge a_2-13\tau\ge0$. Moreover $T_0>0$ and the first
condition gives

$$
0\le a_1-13\tau\le T_0+\rho.
$$

Consequently $0\le u\le T_0$ and $0\le q_1,q_2\le\rho$
individually. Every displayed raw entry is nonnegative throughout the
strip; the smallest potentially limiting first-cell entry is
$\tau-38\delta\ge\tau/20>0$. The other subtractions are
nonnegative from $\delta\le\tau/40$. Directly adding the entries
of each vector gives its schedule mass; adding those masses and $\rho$
gives one. Moving label-zero mass preserves each schedule mass and
nonnegativity. Formula (306.5) therefore gives a single full normalized
allocation, including all zero-weight and $\rho=0$ endpoints.

On every first-zero fibre the raw correct masses, in order $1,\ldots,7$,
are

$$
(8\tau-\delta,\ 8\tau-\delta,\ 8\tau-\delta,\
5\tau-\delta,\ 4\tau-\delta,\ 3\tau-\delta,\ \tau-\delta).
\tag{306.7}
$$

For example class 1 receives $(8\tau-34\delta)+29\delta+4\delta$;
class 2 receives the same amount. Class 3 receives twice
$3\tau+11\delta$ plus $2\tau-23\delta$. Class 4 receives
twice $\tau-9\delta$, then $2\tau+20\delta$, and
$\tau-3\delta$. Class 5 receives $8\delta$,
$\tau+5\delta$, $\tau+4\delta$ and twice
$\tau-9\delta$. Classes 6 and 7 follow by adding their displayed
second-cell and exhaustion entries. Earlier bits are one on each
such fibre, so no later zero changes these totals. The moves in the
three first cells act only in class 1, within $\{0,1\}$, and add
$u$ there. The prefix row adds $q_1,q_2$ to classes 1 and 2.
It follows that for the final law

$$
p_w(n)=a_n-e\qquad(w\in\Omega_n,\ 1\le n\le7).
\tag{306.8}
$$

Here is a complete all-word bound on the mass $D_n$ outside $\{0,n\}$.
It concerns the raw core; the head moves and prefix row add no such
mass. Denote that core by $C(\tau,\delta)$ as a family of terminal
vectors. At $(1,0)$ it is the core of 300.1 with first-cell correct
mass in $(1,3),(1,4)$ moved to zero. These moves stay inside
$\{0,1\}$ and occur only in class 1. Thus its wrong masses are
exactly those already proved in (300.4)–(300.5), all at most five.
This uses the existing all-suffix proof, not a claim about sole-zero
words only.

The other algebraic endpoint $C(40,1)$ need not itself be a normalized
probability law. It is an explicit nonnegative family of equal-mass
terminal vectors. Set $(h,s,t,u,v,z)=(w_2,w_3,w_4,w_5,w_6,w_7)$.
Adding its row vectors gives the following exact wrong-mass polynomials:

$$
\begin{aligned}
D_1={}&33+137h-131hs-31ht-4hu-4hv+162s-56st\\
 &-31su-31sv+62t-31tu-31tv+35u-31uv+35v-35vz,\\
D_2={}&170+31s-56st-31su-31sv+31t-31tu-31tv\\
 &+31u-31uv+31v-35vz,\\
D_3={}&174-31tu-31tv+27u-31uv+27v-35vz,\\
D_4={}&194-4u-31uv-4v-35vz,\\
D_5={}&178-35v-35vz,\qquad D_6=183,\qquad D_7=197.
\end{aligned}
\tag{306.9}
$$

For each row only coordinates after its first zero are free. The full
Boolean maxima can be verified without a search assumption. Set $z=0$
to maximize the first three expressions. For fixed $h,s,t$ in row 1,
the remaining $u,v$ part is $A(u+v)-31uv$ with
$A=35-4h-31(s+t)$; its maximum is
$\max\{0,A,2A-31\}$. Row 2 has $A=31-31(s+t)$;
row 3 has $A=27-31t$. Substitution gives every value in this table:

| Class | Fixed suffix bits in order | Maximum over the other suffix bits |
| --- | --- | --- |
| 1 | $hst=000,001,010,011,100,101,110,111$ | $72,99,199,201,201,201,201,176$ |
| 2 | $st=00,01,10,11$ | $201,201,201,176$ |
| 3 | $t=0,1$ | $201,174$ |
| 4 | $uv=00,01,10,11$ | $194,190,190,155$ |
| 5 | $v=0,1$ | $178,143$ |
| 6 | none | $183$ |
| 7 | none | $197$ |

Rows 4 and 5 follow directly by setting $z=0$; rows 6 and 7 are
constant. Therefore $D_n\le201$ at this endpoint on every word.
Every raw vector depends linearly on the parameters, with the exact
identity

$$
C(\tau,\delta)=(\tau-40\delta)C(1,0)+\delta C(40,1).
\tag{306.10}
$$

Both coefficients are nonnegative. Wrong mass is linear in these
unnormalized vectors at each fixed word, so the two endpoint bounds
give

$$
D_n\le5(\tau-40\delta)+201\delta=5\tau+\delta=e.
\tag{306.11}
$$

This proves the entire real strip, not just rational parameter samples.
Combining (306.8) with $D_n\le e$ verifies separately all three
deficits in (297.3):

$$
a_n-p_w(n)=e,\quad
1-a_n-p_w(0)=D_n-e\le0,\quad
1-p_w(0)-p_w(n)=D_n\le e.
\tag{306.12}
$$

Thus every zero-word TV is exactly $e$. Direct addition in the positive
word gives nonbase mass
$(2\tau-23\delta)+(\tau-3\delta)+(\tau+5\delta)
+14\delta+(\tau+4\delta)+4\delta=5\tau+\delta$.
The head moves are inactive there and the prefix emits zero, so
$p_+(0)=1-e$.

Implement the full table weights (306.5) by half-open intervals of one
source-independent uniform seed, fixing the whole schedule and every
counterfactual label before replies. Execute that increasing schedule
until its first queried zero or exhaustion and emit its actual original
mark. Every source and seed hands off finitely, measurably, with zero
advice and at most two actual requests. Its counted $N$ completion uses
the same seed and source and has the identical output law. For every
actual $n>7$, (297.2) gives exact error $\max\{e,a_n\}=e$,
including $a_8=e$ and every permitted later positive tail. Since
$a_7=6\tau>e$, actual active length at this cap is exactly seven.
Finite-pattern actuality is supplied by 297.3. This proves original
sufficiency and completes the equivalence. $\square$

**Corollary 306.3 (Attained optima throughout the declared strip).**
For the ordered heads and fixed late amplitudes (306.1), set

$$
d_* =\max\left\{0,\frac{a_1+7\tau-1}{17},\
                       \frac{a_2+11\tau-1}{40}\right\}.
\tag{306.13}
$$

If $d_*\le\tau/40$ and the entire positive nonincreasing vanishing
tail satisfies $a_8\le5\tau+d_*$, both original marked-target
optima are attained and equal $5\tau+d_*$. All positive closed
caps in either class are feasible exactly when they are at least this
value.

**Proof.** Apply 306.1 with $\delta=d_*$. For every original $N$
competitor, the reused five-late score 281.2 and the two head cuts give

$$
e_a(A)\ge\max\left\{5\tau,
 \frac{a_1+92\tau-1}{17},
 \frac{a_2+211\tau-1}{40}\right\}=5\tau+d_*.
\tag{306.14}
$$

To justify the bound even if a proposed competitor has a different
active horizon, apply 297.3 at every positive cap above its error,
then use the one finite prefix representative for all three scores.
Decrease those caps to its error; this also excludes zero error.
Counted completion gives the same lower bound for $O$. The displayed
law attains it, and that same law is feasible at every larger cap,
regardless of the new cap's active horizon. $\square$

**Proposition 306.4 (An attained normal-domain interval).**
If $a_2=a_3=13\tau$ and (306.2) holds, the same finite profile
belongs to $H_N$ at $L=7$ with this same mass-one allocation. In
particular, for every

$$
\frac1{24}<\tau\le\frac1{23},\quad
\delta=\frac{24\tau-1}{40},\quad
13\tau\le a_1\le1-7\tau+17\delta,
\tag{306.15}
$$

and every permitted tail $a_8\le5\tau+\delta$, the optima are
attained at $5\tau+\delta$.

**Proof.** The hull excess is
$\sum_{n=3}^7a_n-8e=6\tau-8\delta>0$ and
$a_1+6\tau-8\delta\le1-\tau+9\delta<1$.
Order, $a_7>e$ and $a_2=a_3$ supply the other hull conditions;
306.2 supplies one full feasible mass-one allocation. In (306.15),
$\delta>0$ and $\delta\le\tau/40$ are equivalent to the stated
interval, and the second expression in (306.13) involving $a_2$
equals $\delta$. The first head bound makes its other expression
at most $\delta$. Thus $d_*=\delta$, including $\tau=1/23$
where $\rho=0$. The upper head interval is nonempty, since
$1-20\tau+17\delta=(23-392\tau)/40>0$ there.
This proves the asserted continuum. The endpoint $1/23$ is not a
global upper bound on scales at other caps. $\square$

## 307. A changing late-amplitude cone with an attained boundary

**Theorem 307.1 (Exact joint heads at a prescribed cone cap).**
Let $\tau,\sigma\ge0$, $\tau+\sigma>0$, and prescribe

$$
\begin{gathered}
E=5\tau+17\sigma,\\
(a_3,a_4,a_5,a_6,a_7)=
(13\tau+46\sigma,10\tau+35\sigma,9\tau+29\sigma,
 8\tau+26\sigma,6\tau+20\sigma).
\end{gathered}
\tag{307.1}
$$

Take $1\ge a_1\ge a_2\ge a_3$ and any entire positive
nonincreasing vanishing tail with $a_8\le E$. At the closed cap
$E$, feasibility in either original class is equivalent to

$$
a_1+7\tau+23\sigma\le1,\qquad
a_2+11\tau+34\sigma\le1.
\tag{307.2}
$$

The allowed head domain is nonempty exactly when
$24\tau+80\sigma\le1$. On that domain the construction below
has uniform error exactly $E$. If at least one inequality in (307.2)
is an equality, both original optima are attained and equal $E$;
then every positive closed cap is feasible exactly when it is at least
$E$. Head tightness here is a sufficient condition for this optimality
conclusion. No converse is asserted.

**Construction 307.2 (One sixteen-table core and one prefix).**
Each row gives $O(i,j;u,v,z)$ and its mass $A\tau+B\sigma$.
The outputs $u,v,z$ are on $0,10,11$, respectively.

| $i$ | $j$ | $u$ | $v$ | $z$ | $A$ | $B$ |
| --- | --- | --- | --- | --- | ---: | ---: |
| 1 | 2 | 1 | 2 | 3 | 2 | 7 |
| 1 | 2 | 1 | 2 | 4 | 1 | 4 |
| 1 | 2 | 1 | 2 | 5 | 1 | 4 |
| 1 | 3 | 1 | 3 | 0 | 3 | 11 |
| 1 | 4 | 1 | 4 | 0 | 1 | 3 |
| 2 | 3 | 0 | 3 | 0 | 3 | 8 |
| 2 | 3 | 2 | 3 | 0 | 0 | 3 |
| 2 | 4 | 0 | 4 | 0 | 1 | 3 |
| 3 | 4 | 0 | 4 | 0 | 1 | 6 |
| 3 | 4 | 0 | 4 | 5 | 1 | 2 |
| 3 | 5 | 0 | 5 | 0 | 1 | 3 |
| 3 | 6 | 0 | 6 | 0 | 1 | 3 |
| 4 | 5 | 0 | 5 | 0 | 1 | 3 |
| 4 | 6 | 0 | 6 | 0 | 1 | 3 |
| 5 | 6 | 0 | 6 | 0 | 1 | 3 |
| 6 | 7 | 0 | 7 | 0 | 1 | 3 |

Their masses sum to $20\tau+69\sigma$. Put

$$
\rho=1-20\tau-69\sigma,\qquad
x_1=a_1-13\tau-46\sigma,\qquad
x_2=a_2-9\tau-35\sigma.
\tag{307.3}
$$

Use the remaining mass $\rho$ for a single prefix $(1,2)$ with
terminal vectors

$$
(\rho-x_1)e_0+x_1e_1,\qquad
(\rho-x_2)e_0+x_2e_2,\qquad \rho e_0.
\tag{307.4}
$$

One local uniform coordinate $V$ fixes both counterfactual choices
by $V<x_1/\rho$ and $V<x_2/\rho$ before replies. The two
thresholds each lie in $[0,1]$; their sum need not be at most one.
This is one schedule branch, whose mass is counted once.

**Proof of Theorem 307.1.** The late sum is $46\tau+156\sigma$;
its $Y_2$ weighted sum is $211\tau+714\sigma$. Substituting
these and $E$ in the two existing head cuts (299.1) gives (307.2)
exactly. Necessity is for every original competitor by their already
proved arbitrary-address/full-carrier closed-cap interpretation.
Since $a_2\ge13\tau+46\sigma$, the second head bound forces
$24\tau+80\sigma\le1$. Conversely, if that scale bound holds,
the choice $a_1=a_2=a_3$ satisfies the second head bound, and
the first follows from $20\tau+69\sigma\le24\tau+80\sigma$.
Thus the head domain is nonempty precisely as stated.

Assume (307.2). Then

$$
\rho\ge4\tau+11\sigma>0,\qquad
0\le x_1\le\rho,\qquad
4\tau+11\sigma\le x_2\le\rho.
\tag{307.5}
$$

The lower bounds use order; the upper bounds are exactly the two
head inequalities after subtracting the core correct stocks. Every
listed mass and every entry in (307.4) is nonnegative. The sixteen
core masses and the single prefix mass total one. The common threshold
construction, or formula (306.5) applied to (307.4), specifies full
table weights with this same total.

Direct addition on an entire first-zero fibre gives these core correct
mass coefficients:

$$
\begin{array}{c|rrrrrrr}
n&1&2&3&4&5&6&7\\\hline
\tau\text{ coefficient}&8&4&8&5&4&3&1\\
\sigma\text{ coefficient}&29&18&29&18&12&9&3
\end{array}
\tag{307.6}
$$

For instance the first three $(1,2)$ rows contribute $(4,15)$
in the first two classes; $(1,3),(1,4)$ add $(4,14)$ in
class 1, and $(2,3;2,3,0)$ adds $(0,3)$ in class 2.
For classes $3,\ldots,7$, add rows with second output that class
and rows with exhaustion output that class. Earlier bits are one,
so these totals hold independently of every later bit. The prefix
adds $x_1,x_2$ in the first two classes and zero correct mass in
the others. Thus the final correct mass is

$$
c_n=p_w(n)=a_n-E\qquad(w\in\Omega_n,\ n\le7).
\tag{307.7}
$$

We verify every independent union row by bounding wrong mass outside
$\{0,n\}$. Set $(s,t,u,v,z)=(w_3,w_4,w_5,w_6,w_7)$ and put

$$
\begin{aligned}
B&=2s(1-t)+st+(s+t)(2-u-v)+u(1-v)+v(1-z),\\
G&=3(1-s)+(1-t),\\
B'&=8s(1-t)+2st+3(s+t)(2-u-v)+3u(1-v)+3v(1-z),\\
G'&=11(1-s)+3(1-t).
\end{aligned}
\tag{307.8}
$$

For the core the two coefficients of that wrong mass are as follows;
the prefix has zero wrong mass in every class.

| First zero | Coefficient of $\tau$ | Coefficient of $\sigma$ |
| --- | --- | --- |
| 1 | $B+w_2G$ | $B'+w_2G'+3(1-w_2)$ |
| 2 | $B+G$ | $B'+G'$ |
| 3 | $2+2(1-t)+t(2-u-v)+u(1-v)+v(1-z)$ | $8+6(1-t)+3t(2-u-v)+3u(1-v)+3v(1-z)$ |
| 4 | $3+(1-u)+(1-v)+u(1-v)+v(1-z)$ | $11+3[(1-u)+(1-v)+u(1-v)+v(1-z)]$ |
| 5 | $3+2(1-v)+v(1-z)$ | $11+6(1-v)+3v(1-z)$ |
| 6 | $5$ | $17$ |
| 7 | $5$ | $17$ |

These expressions follow by evaluating each of the sixteen stopped
tables on the indicated first-zero fibre and adding the masses whose
output is neither zero nor its first-zero label. They retain every
Boolean suffix. Their bounds can all be established explicitly.
For $q=s+t$, the maximum of
$q(2-u-v)+u(1-v)+v(1-z)$ is
$\max\{2q,q+1,1\}$. For $st=00,01,10,11$ it is respectively
$1,2,2,4$. Hence

$$
\begin{array}{c|rrrr}
st&00&01&10&11\\\hline
\max B&1&2&4&5\\
G&4&3&1&0\\
\max B'&3&6&14&14\\
G'&14&11&3&0
\end{array}
\tag{307.9}
$$

This proves $B+G\le5$ and $B'+G'\le17$.
In class 1, $w_2=1$ uses these bounds; $w_2=0$ uses
$B\le5$ and $B'+3\le17$.
For class 3, $t=0,1$ give $\tau$ bounds five and four and
$\sigma$ bounds seventeen and fourteen, since
$u(1-v)+v(1-z)\le1$ and
$2-u-v+u(1-v)+v(1-z)=2-uv-vz\le2$.
For class 4 the bracket equals $2-uv-vz\le2$.
Class 5 is bounded by distinguishing $v=0,1$; classes 6 and 7
are already constant. Every $\tau$ coefficient is therefore at
most five and every $\sigma$ coefficient at most seventeen.
For all real nonnegative parameters it follows that

$$
D_n\le5\tau+17\sigma=E.
\tag{307.10}
$$

Combined with (307.7), the three distinct deficits are $E$,
$D_n-E\le0$, and $D_n\le E$. Thus every zero-word TV equals
$E$, without deriving the union constraint from the two singleton
constraints. Negative singleton demands and zero entries remain in
the full system. At the positive word the only nonzero-label outputs
are the first three exhaustion rows and $(3,4;0,4,5)$.
Their total is $(4\tau+15\sigma)+(\tau+2\sigma)=E$.
The prefix emits zero, so $p_+(0)=1-E$.

Partition one source-independent uniform seed into intervals of the
core table masses and the one prefix interval, using its local
coordinate for both thresholds in (307.4). This fixes the complete
schedule and all counterfactual labels before replies. Execute only
that increasing schedule on the actual source, stop at its first
queried zero or exhaustion, and deliver the indicated original mark.
The rule has zero advice, measurable finite handoff at every source
and seed, and at most two actual requests. Its $N$ completion acquires
the same whole schedule with the same seed and source, ignores replies
past the reconstructed stop, and counts those actual requests. For
every actual $n>7$, error is exactly $\max\{E,a_n\}=E$
by (297.2). Since $a_7-E=\tau+3\sigma>0$, the active length
is seven, including both axes and every tail tie $a_8=E$.
All finite words are actual by 297.3. This proves original sufficiency.

If the first head is tight, the all-competitor first-head cut gives
$17e_a(A)\ge a_1+2\sum_{3}^7a_n-1=17E$.
If the second is tight, its second-head counterpart gives
$40e_a(A)\ge40E$. These inequalities hold at every original
error by the prefix transport and limiting-cap argument used in
306.14. Thus at either tight head no competitor in either class
improves on $E$, which the one constructed law attains. The same
law works at every larger cap. This proves the sufficient sharpness
claim and does not prove that tightness is necessary. $\square$

**Proposition 307.3 (The normal domain and a nonradial continuum).**
Under (307.2), setting $a_2=a_3$ puts the finite profile in $H_N$
with the same mass-one law. In particular let

$$
\begin{gathered}
0<q\le1/80,\quad \sigma=q,\quad\tau=(1-80q)/24,\\
a_2=a_3=13/24+8q/3,\quad a_4=5/12+5q/3,\\
a_5=3/8-q,\quad a_6=1/3-2q/3,\quad a_7=1/4,\\
13/24+8q/3\le a_1\le17/24+q/3.
\end{gathered}
\tag{307.11}
$$

With every permitted positive vanishing tail $a_8\le E$, both
optima are attained at $E=5/24+q/3$, including $q=1/80$
where $\tau=0$. The hull excess is identically $1/4$.

**Proof.** In general the hull excess is

$$
\sum_{n=3}^7a_n-8E=6\tau+20\sigma>0,
\qquad a_1+6\tau+20\sigma\le1-\tau-3\sigma<1.
\tag{307.12}
$$

Together with order, $a_7>E$ and $a_2=a_3$, these are all hull
conditions. The same full probability law supplies $H_N$ feasibility.
Substituting $\tau=(1-80q)/24$ gives every amplitude and cap in
(307.11). The scale bound is equality, so its second head is tight.
Its first head bound is exactly the stated upper bound on $a_1$;
the difference between its upper and lower bounds is $1/6-7q/3>0$.
Also $6\tau+20q=1/4$ and $a_7=1/4$. Theorem 307.1 now proves
the asserted optima and cap classification throughout this real interval.

This cone changes shape: at $\sigma>0$,
$a_3/E-13/5=9\sigma/(5E)>0$, whereas common radial scaling of
the old ratio ray leaves that ratio unchanged. On the entire cone
$2a_3+a_5+a_6+2a_7=11E$, so identity (299.2) makes the old
$C$ reading exactly four times the $Y_2$ reading here. It gives
no additional cut on this cone. At $\sigma=0$ the optimal old
ray is already covered by 300.1; its optimality can hold with both
heads strict. At $\sigma>0$ with both heads strict, the present
theorem makes no optimality claim about $E$ and no classification at
other caps. $\square$

## 308. Applicability and the unrestricted remaining question

The support extension in 304 applies to every finite set disjoint from
its skeleton, including gap addresses, and its whole-tail consequence
uses only finitely many positive residuals at each positive cap. Adding
correct rows instead on later absorbing-chain words can give the same
zero-excess quotient consequences. That choice of score representation
does not add a second collective-residual relation. Where 305 applies,
its coefficient four on a sixth late amplitude gives a stronger
single-coordinate boundary bound than the coefficient one consequence
of 304; the arbitrary-set and half-sum assertions in 304 remain distinct.

The primal laws in 306 and 307 concern the contiguous seven-coordinate
head and every declared actual tail. All-embedding necessity of their
supporting scores does not imply a gapped primal construction, a
classification of other active lengths, or a larger-cap classification
outside the stated attained domains. The slices $\delta=0$ in 306
and $\sigma=0$ in 307 reuse 300.1. The strip endpoint in 306 is
a sufficient range for its displayed law, not a maximal feasible
radius theorem. Failure of a particular continued law on one
multiple-zero word would exclude that law only, not every stopped
law at the same cap.

All constructions use actual original marks, one source-independent
seed and zero advice. Their stopped execution and counted completion
share the same actual source and seed; no arbitrary starting $N$ law
is required to be preserved. All original competitor addresses and
Borel outputs remain in the necessary directions supplied by 110.2.
The legal actual $0100$ example and earlier unqueried label 1 in
303.2 remain within every complete catalog used here. None of these
finite atomic laws estimates an original nonatomic target: their TV
distance from each such target is one, as in 297.1.

The mature comparison and scalar-query precedents have precisely the
conditions and limitations in 303.3. A whole attainable vector must
come from one rule. Scalar coefficient normalization followed by
scalar output rescaling supplies no normalized vector law or stopped
schedule in place of the explicit equal-mass constructions above.
The existing source arithmetic, 109.1 stopped criterion, 110.2
closed-cap transport, five-late lower score, and the old supporting
scores are used at their stated scopes. No exhaustive novelty,
historical nonderivability or priority assertion is made.

The unrestricted original obligation is still (303.1), with its exact
quantifier order: for every $L\ge3$ and every full unit-$O$ score
there must be one unrestricted full $V\ge0$ and one
$\theta\in[0,1]$ paying both the complete $N$ excess and the
entire signed residual. Nonzero zero-cost $V$ at $\theta=1$
remains allowed. The alternative separator still requires the same
actual $b\in H_N$, one full feasible allocation of mass $M\ge1$,
a strict reading above $M$, an original $N$ attainer and a uniform
lower bound against every original $O$ competitor. The necessary
relations 304–305 and the scoped common laws 306–307 establish neither
alternative. Their excluded profiles lack a feasible $N$ allocation
at the tested cap; their attainers belong to both classes. Every
original all-sequence, common-seed, resource, full-row, target,
positive-tail and closed-cap obligation in 303.1 therefore remains.

## 追加锚（本行以下为增补区）
## 309. The common full interface for two further relations

**Definition 309.1 (Objects, rules and complete rows).**
Use the actual source $X$ of 297.1, not a distribution on words:
$F_0=0$, $F_1=1$, $F_{k+2}=F_{k+1}+F_k$,
$N(r,g)=1+F_rg$, $r$ prime,
$\lceil F_r/10\rceil\le g\le\lfloor F_r/5\rfloor$,
$q_i=[p_i\mid N]$ and $n=\min\{i:q_i=0\}$.
All finite reply patterns are actual by the Fibonacci-matrix and CRT
argument in 297.3, which reuses 280.1. Every actual source has finite
first absence. The full carrier remains
$\Theta=\bigsqcup_{j\ge1}B_j\sqcup\bigsqcup_{j\ge1}P_j$, with each
block a Borel copy of $(0,1)$. The unchanged consumer returns unknown
on $B_j$ and proposes $j$ on $P_j$. Its original nonatomic targets
$\mu_x^{\rm orig}$ remain exactly those in 297.1.

The accuracy target here is the separately selected law

$$
\lambda_x^a=(1-a_{n(x)})\delta_{\theta_0}
                 +a_{n(x)}\delta_{\theta_{n(x)}},\qquad
\theta_j=(B_1,1/(j+2)),\qquad
1\ge a_1\ge a_2\ge\cdots>0,\quad a_n\to0.
\tag{309.1}
$$

An original competitor may use arbitrary query addresses and arbitrary
Borel outputs in $\Theta$. It has zero advice, one source-independent
common seed and sourcewise almost-sure finite handoff. The schedule
in $\mathcal N_2$ is wholly fixed before replies and all its replies
are obtained. In $\mathcal O_2$ the schedule is fixed increasingly
before replies and execution stops at its first queried zero or
exhaustion. The second address cannot depend on the first reply.
The bound is two actual requests, including repetitions and ignored
replies. No source distribution, bounded-address assumption, runtime
bound or mean-request relaxation is introduced. Write
$e_a(A)=\sup_{x\in X}\operatorname{TV}(\mathcal L(A(x)),\lambda_x^a)$.

For every finite horizon $L\ge3$ retain all words $w\in\{0,1\}^L$ and
all labels $0,\ldots,L$. If $n(w)$ is its first zero, the three
independent event rows $A,C,P$ have events $\{0\},\{n(w)\}$,
$\{0,n(w)\}$ and demands $1-b_{n(w)}-e,b_{n(w)}-e,1-e$.
At $+=1^L$ retain the base event with demand $1-e$.
Every unscored row and every negative singleton demand is retained.
For a probability vector and $0\le b_n\le1$ the three TV deficits are

$$
1-b_n-p_w(0),\qquad b_n-p_w(n),\qquad
1-p_w(0)-p_w(n).
\tag{309.2}
$$

Their maximum is the TV distance. For arbitrary real $(b,e)$,
feasibility refers to these linear demands, without claiming a
probability target outside $0\le b_n\le1$.

The complete $N$ catalog contains every four-cell table
$N(i,j;u,v,s,t)$ on $00,01,10,11$, every constant and singleton,
and all labels in every cell. The $O$ catalog contains every
$O(i,j;u,s,t)$ on $0,10,11$, with $i<j$, and its shorter schedules.
Repeated queries coarsen information without refunding a request;
reversing static queries permutes cells. Earlier unqueried labels
remain legal outputs.

**Definition 309.2 (The single allocation and its supporting score).**
As in 297.5 set $R=O(1,2;1,2,0)$,
$\alpha=(1,1,0,\ldots,0)$, $r=z_R=d(\alpha,0)$,
$h=d(b,e)-r$ and $G_C=(z_D-r)_{D\in\mathcal D_C}$.
A complete feasible allocation means one vector $\lambda\ge0$
satisfying every row of $G_C\lambda\ge h$, with one finite total
mass $M=\sum_D\lambda_D$. The claims below allow any such finite
mass. Mass one is normalized feasibility; division by $M$ does not
preserve the same profile.

For a nonnegative score $Y=(A_w,C_w,P_w;T)$ define

$$
\begin{aligned}
g_Y(w,\ell)&=A_w[\ell=0]+C_w[\ell=n(w)]
                         +P_w[\ell\in\{0,n(w)\}],\\
g_Y(+,\ell)&=T[\ell=0],\\
\beta_n&=\sum_{w:n(w)=n}(C_w-A_w),\qquad
K=\sum_{w\ne+}(A_w+C_w+P_w)+T,\\
W&=Yr,\qquad B_C(Y)=\max_{D\in\mathcal D_C}Yz_D,
\qquad\Delta_C(Y)=B_C(Y)-W,\\
F_{QY}(b,e)&=Yh=\sum_n\beta_n(b_n-\alpha_n)-Ke.
\end{aligned}
\tag{309.3}
$$

Nonnegativity and the same full allocation give

$$
F_{QY}(b,e)\le YG_C\lambda
=\sum_D\lambda_D(Yz_D-W)\le M\Delta_C(Y).
\tag{309.4}
$$

In particular zero excess proves a necessary relation independent of
mass, order and hull membership. This is the existing pairing
(297.5), not an additional duality theorem.

**Lemma 309.3 (Complete finite support and original closed caps).**
Suppose a nonnegative score on $d\ge3$ coordinates has pair-cell maxima

$$
m_{ij,uv}=\max_{0\le\ell\le d}
 \sum_{w:(w_i,w_j)=(u,v)}g_Y(w,\ell),\qquad uv=00,01,10,11,
\tag{309.5}
$$

whose four-entry sums are at most $W=Yr$. Then
$B_N=B_O=W$ if $R$ attains $W$. The same bound holds after embedding
coordinates as $(1,2,j_1,\ldots,j_{d-2})$ at every ordered choice
$3\le j_1<\cdots<j_{d-2}\le L$, by setting nonskeleton bits to
one on the scored words and mapping labels by the embedding.
Every original rule meeting a positive closed cap satisfies the
resulting finite necessary relation. A linear inequality in the cap
therefore also holds at its actual error by decreasing positive caps
to that error.

**Proof.** A fixed $N$ pair chooses a label independently in each
cell, so its score is at most the sum in (309.5). For nonnegative
reward vectors, the maximum of a sum is at most the sum of maxima.
A constant, singleton or repeated schedule coarsens a distinct-pair
partition; reversal only permutes cells. A stopped table merges the
$00,01$ cells before choosing its first output, so is bounded as well.
The common anchor supplies equality for both catalogs.

On the embedded support every outside query has the constant answer
one. Two arbitrary queries thus induce a displayed pair partition or
a constant or singleton coarsening. An outside label earns zero and
cannot improve a maximum of nonnegative rewards. This proves the
bound for the entire catalog, rather than for a pruned set of queries
or outputs. All unscored word rows remain in the allocation problem.

The original implication reuses the exact class-feasibility transport
110.2 and the prefix consequence 280.3, stated in 297.3. At
$0<c\le1$, vanishing of $a$ makes the active horizon
$L_a=\max(\{n:a_n>c\}\cup\{0\})$ finite. Transport supplies one
normalized finite representative at the closed cap $c$ for any
original cap-feasible competitor. Its necessity includes arbitrary
original addresses and full-carrier outputs: countability gives a
common probability-one execution event, and actual finite witnesses,
truncation and compactness give finite class feasibility. It does not
preserve every initial law or coupling. For stopped sufficiency the
reused exact criterion 109.1 is $c_0\ge H$ coordinatewise for
$p_w=c_0+\sum_i\ell_iw_i+\sum_{i<j}Q_{ij}w_iw_j$,
$H=\sum_i(\sum_{j>i}(-Q_{ij})_+-\ell_i)_+$;
normalization makes its scalar schedule budget redundant.

At a desired prefix $K$, restrict a longer representative by fixing
higher replies to zero, projecting higher labels to zero and deleting
those constant observations. On an old positive prefix this projection
also contracts TV to the new base target. Extend a shorter representative
by ignored inputs. At each added first-zero address $n$ its old positive
law, supported below that address, has exact error

$$
\operatorname{TV}(p_+,(1-a_n)e_0+a_ne_n)
              =\max\{1-p_+(0),a_n\}\le c.
\tag{309.6}
$$

Thus all three independent rows hold for this one representative,
including closed ties. These are representation operations in the
proof, not free observations by an original rule. Apply (309.4).
For actual error zero use every positive cap and pass to zero.
For error less than one decrease caps in $(e_a(A),1]$; when the error
is one, the particular inequalities below follow directly from
$a_n\le1$. Caps above one are likewise immediate. $\square$

## 310. A joint two-tail constraint on the same complete allocation

**Definition 310.1 (The nine-coordinate score $Z_7$).**
The following 46 independent rows specify all its nonzero coefficients.
Every $A$ and every unlisted coefficient is zero. This sets score
weights only, not the retained constraints.

| Row | Word | Weight |
| --- | --- | ---: |
| P | 001100001 | 1 |
| P | 001100010 | 3 |
| P | 010010100 | 2 |
| P | 010100100 | 3 |
| P | 010101000 | 3 |
| P | 010110000 | 3 |
| P | 010110001 | 1 |
| P | 011000110 | 3 |
| P | 011001000 | 3 |
| P | 011010000 | 3 |
| P | 011010100 | 1 |
| P | 100010000 | 2 |
| P | 100010001 | 1 |
| P | 100010010 | 2 |
| P | 100010100 | 1 |
| P | 100100010 | 4 |
| P | 100100100 | 1 |
| P | 100101000 | 1 |
| P | 101000001 | 1 |
| P | 101000100 | 4 |
| P | 101001000 | 1 |
| C | 101100001 | 1 |
| C | 101100010 | 3 |
| C | 110000000 | 6 |
| P | 110001000 | 4 |
| C | 110010010 | 2 |
| C | 110100000 | 1 |
| C | 110100100 | 5 |
| C | 110110111 | 2 |
| C | 111000000 | 14 |
| C | 111000100 | 2 |
| C | 111010011 | 2 |
| C | 111010110 | 2 |
| C | 111100000 | 5 |
| C | 111100001 | 2 |
| C | 111100100 | 3 |
| C | 111100110 | 1 |
| C | 111101010 | 9 |
| C | 111110000 | 5 |
| C | 111110100 | 11 |
| C | 111110111 | 4 |
| C | 111111000 | 12 |
| C | 111111001 | 4 |
| C | 111111100 | 16 |
| C | 111111110 | 16 |
| T | 111111111 | 16 |

**Theorem 310.2 (Full support and seven-late necessity).**
The complete score invariants are

$$
\beta=(0,4,16,20,20,20,16,16,16),\quad K=192,\quad
W=B_N=B_O=68,\quad\Delta_N=\Delta_O=0.
\tag{310.1}
$$

For every $L\ge9$, every ordered $3\le j_1<\cdots<j_7\le L$,
every real finite profile and one complete feasible allocation in
either class of any finite mass,

$$
b_2+4b_{j_1}+5b_{j_2}+5b_{j_3}+5b_{j_4}
       +4b_{j_5}+4b_{j_6}+4b_{j_7}\le1+48e.
\tag{310.2}
$$

Every original competitor in either class therefore satisfies

$$
48e_a(A)\ge a_2+4a_{j_1}+5a_{j_2}+5a_{j_3}+5a_{j_4}
                    +4a_{j_5}+4a_{j_6}+4a_{j_7}-1.
\tag{310.3}
$$

**Proof.** Sum the correct rows by their first-zero class to get
$\beta$. The union rows total 48, the correct rows total 128 and
the positive row is 16, giving $K=192$. The anchor earns every
union unit, all 16 positive units and the four correct units at
first zero 2, hence $W=68$.

Here are all 36 pair-cell maxima of (309.5), each maximizing over
all ten labels $0,\ldots,9$. Their values can be reproduced by
integer additions of the row weights followed by a finite maximum;
there is no optimization oracle in this certificate.

| Pair | Maxima in $00,01,10,11$ |
| --- | --- |
| 12 | $(4,22,22,20)$ |
| 13 | $(12,14,20,22)$ |
| 14 | $(12,14,20,22)$ |
| 15 | $(16,10,20,22)$ |
| 16 | $(20,6,20,22)$ |
| 17 | $(17,9,16,22)$ |
| 18 | $(20,6,16,22)$ |
| 19 | $(24,2,20,18)$ |
| 23 | $(12,10,20,26)$ |
| 24 | $(12,10,20,26)$ |
| 25 | $(16,6,20,26)$ |
| 26 | $(20,2,20,26)$ |
| 27 | $(16,6,17,25)$ |
| 28 | $(13,9,23,19)$ |
| 29 | $(19,3,25,17)$ |
| 34 | $(12,16,20,20)$ |
| 35 | $(16,12,20,20)$ |
| 36 | $(20,8,20,20)$ |
| 37 | $(21,7,16,24)$ |
| 38 | $(22,6,16,22)$ |
| 39 | $(26,2,18,18)$ |
| 45 | $(16,12,20,20)$ |
| 46 | $(20,8,20,20)$ |
| 47 | $(17,11,16,20)$ |
| 48 | $(23,5,16,23)$ |
| 49 | $(26,2,18,18)$ |
| 56 | $(20,12,20,16)$ |
| 57 | $(21,11,16,20)$ |
| 58 | $(22,10,16,18)$ |
| 59 | $(30,2,16,18)$ |
| 67 | $(21,15,16,16)$ |
| 68 | $(24,12,16,16)$ |
| 69 | $(32,4,16,16)$ |
| 78 | $(24,9,16,19)$ |
| 79 | $(29,4,16,16)$ |
| 89 | $(32,4,16,16)$ |

Every quadruple sums to at most 68. Lemma 309.3 proves the complete
support equality in both classes and at every embedding, including
queries in gaps or beyond the skeleton and every earlier unqueried
output. It also covers shorter, repeated and reversed schedules.
Pair with the same full allocation using (309.4). Its quotient is

$$
F_{QZ_7}=4\bigl[b_2-1+4b_{j_1}+5b_{j_2}+5b_{j_3}+5b_{j_4}
          +4b_{j_5}+4b_{j_6}+4b_{j_7}-48e\bigr]\le0.
$$

This proves (310.2) for all real profiles and any finite mass.
Lemma 309.3 gives original closed-cap necessity and its limit
(310.3), without assuming any selected address active. At caps at
least one, the left side of (310.2) is at most 32 and its right
side at least 49. $\square$

**Corollary 310.3 (One allowance for two positive residuals).**
For the same seven ordered late addresses put

$$
s_J=1+40e-b_2-4b_{j_1}-5b_{j_2}-5b_{j_3}-5b_{j_4}-4b_{j_5}.
$$

Under the same complete-allocation hypotheses,

$$
s_J\ge4\bigl[(b_{j_6}-e)_++(b_{j_7}-e)_+\bigr].
\tag{310.4}
$$

It holds at every positive original closed cap, with $b=a$.

**Proof.** The reused $Y_2$ relation 299.1 gives $s_J\ge0$.
Apply the reused six-late relation 305.2 once with sixth address
$j_6$ and once with sixth address $j_7$; these give
$s_J\ge4(b_{j_6}-e)$ and $s_J\ge4(b_{j_7}-e)$.
Equation (310.2) gives
$s_J\ge4[(b_{j_6}-e)+(b_{j_7}-e)]$.
All four are necessary inequalities of the very same profile and
full allocation. For real $u,v$,
$\max\{0,u,v,u+v\}=u_++v_+$, proving (310.4).
Only score selection clips a residual; no demand was clipped.
No independently attainable laws or budgets have been added.
Original necessity follows from the same one-representative argument.
The arbitrary-set half-sum bound (304.6) is separately reused and
is not replaced by a claim about more than these two coefficient-four
residuals. $\square$

**Corollary 310.4 (Actual two-tail lower bound at a saturated head).**
Take an entire sequence (309.1) with $\tau>0$,
$a_2=1-11\tau$, $(a_3,\ldots,a_7)=(13,10,9,8,6)\tau$
and $1\ge a_1\ge a_2$, with only sequence order imposed on its
later tail. Every original competitor in either class has

$$
e_a(A)\ge5\tau+\frac{a_8+a_9-10\tau}{12}.
\tag{310.5}
$$

**Proof.** At $j_a=a+2$, the first five weighted late terms sum
to $211\tau$. Thus (310.3) says
$48e_a(A)\ge200\tau+4(a_8+a_9)$, which rearranges to (310.5).
This bound does not assume $a_8,a_9$ inactive. The six-late bound
(305.6) can be used simultaneously; neither lower bound supplies
attainment or a classification at a larger cap. $\square$

## 311. A strict bounded comparison and a reused feasible example

**Proposition 311.1 (A diagnostic excluded from complete feasibility).**
Set

$$
e_0=\frac{501}{2400},\qquad
(a_1,\ldots,a_9)=\frac{(1300,1300,1300,1000,900,800,600,507,507)}{2400},
\qquad a_n=e_0\,2^{-(n-10)}\quad(n\ge10).
\tag{311.1}
$$

This entire sequence is positive, nonincreasing and vanishes; its
active horizon at $e_0$ is nine and $a_{10}=e_0$ is a closed tie.
Its finite profile belongs to the hull $H_9$ of 300.2, passes precisely
the older named necessary families $Y_1,Y_2,C$, 304.6 and 305.2 at
all embeddings and finite disjoint sets allowed there, and violates
(310.2) by $1/300$. It has no complete feasible $N$ or $O$
allocation of any finite mass at $e_0$. Every original competitor
for this sequence has error at least $3007/14400$.

**Proof.** Recall the full hull definition

$$
H_L=\left\{(b,e):1\ge b_1\ge\cdots\ge b_L\ge e\ge0,
\ b_2=b_3,\quad
0\le\sum_{n=3}^Lb_n-(L+1)e\le1-b_1\right\}.
\tag{311.2}
$$

Here the hull excess is $151/600$ and its sum with $a_1$ is
$119/150<1$. All the remaining hull conditions follow directly
from (311.1). The exact maximal left-minus-right readings of the
specified old families are

| Named family | Maximum reading |
| --- | ---: |
| $Y_1$ in 299.1 | $-139/800$ |
| $Y_2$ in 299.1 | $-1/60$ |
| $C$ in 299.1 | $-57/800$ |
| 304.6 | $-17/1200$ |
| 305.2 | $-1/150$ |

These are finite rational sums over the 21 ordered five-subsets
and seven ordered six-subsets of $\{3,\ldots,9\}$. For the fourth
row, for each five-subset maximize over finite disjoint $I$ by taking
all omitted positive residuals, and use
$\max\{\max_{k\in I}(a_k-e_0)_+,\frac12\sum_{k\in I}(a_k-e_0)_+\}-s_J$.
This describes the arithmetic calculation completely.

It also proves the comparisons for unbounded address choices, as
follows. All tail residuals from 10 on are zero. Every old cut with
nonnegative late coefficients weakens when a selected address moves
later. In 304.6, removing one selected amplitude and replacing it
by a smaller one with difference $\delta\ge0$ increases the total
omitted positive residual by at most $\delta$ and increases its
maximum individual residual by at most $\delta$. Hence the maximum
of the individual residual and half-sum increases by at most
$\delta$, whereas $s_J$ increases by at least $4\delta$.
Successively moving the ordered selected addresses later cannot
increase that family's reading. This proves the claimed whole
comparison, including every finite $I$, rather than extrapolating
from a bounded scan.

For $J=(3,\ldots,9)$, the new reading is $1/300$.
Equivalently $s_J=1/60$, while
$4[(a_8-e_0)+(a_9-e_0)]=1/50$. Theorem 310.2 excludes a
complete feasible allocation at every finite mass. Its original
inequality gives

$$
e_a(A)\ge e_0+\frac{1/300}{48}
          =e_0+\frac1{14400}=\frac{3007}{14400}.
\tag{311.3}
$$

This is a strict refinement relative to the displayed older basis
and $H_9$, not relative to every historical consequence. There is
no feasible $N$ witness here, no original $N/O$ separation and no
claim that (311.3) is attained. $\square$

**Example 311.2 (Positive two-tail residuals in a common feasible law).**
For a reused, nonempty feasible example take $a_1=\cdots=a_9=1/4$,
$e=7/40$ and $a_n=e\,2^{-(n-10)}$ for $n\ge10$.
Use the synthesis already provided by 113.3: mass $3/4$ emits zero
and mass $1/4$ uses $P_{9,2}$. Explicitly, that subset rule chooses
uniformly a three-subset of the ordered labels $1<\cdots<9<*$,
where $*$ denotes zero. It queries the first two numerical labels
in increasing order until a queried zero; if both are positive it
emits the third label without querying it. Thus it uses at most
two actual calls even when the output is an earlier unqueried label.
Every three-subset can be chosen by intervals of the same seed.

For a word with first zero $n\le9$, a subset emits $n$ exactly
when it contains $n$, so the whole mixture has correct mass
$(1/4)(3/10)=3/40=a_n-e$. It has base mass at least $3/4$;
its mass outside $\{0,n\}$ is at most $1/4-3/40=7/40$.
All three deficits in (309.2) are therefore bounded by $e$, and the
correct deficit equals $e$. At the positive word its base mass is
$3/4+(1/4)(3/10)=33/40$, so its nonbase mass is $e$.
Every actual later first zero has exact error $\max\{e,a_n\}=e$.
The counted $N$ completion uses the same seed and source.
The hull excess at nine is zero, and both $a_8-e$ and $a_9-e$
are $3/40>0$. This is a direct application of an existing construction,
with no new construction or optimality credit.

## 312. One complete head-independent lower certificate

**Definition 312.1 (The seven-coordinate score $Z_{43}$).**
Use exactly these 18 independent nonzero rows. All $A$ coefficients
and all other score coefficients vanish. The $P$ and $C$ rows at
1111000 are distinct events and are not merged.

| Row | Word | Weight |
| --- | --- | ---: |
| P | 0100100 | 1 |
| P | 0101000 | 2 |
| P | 0101010 | 1 |
| P | 0101100 | 1 |
| P | 0110000 | 2 |
| P | 0110010 | 1 |
| P | 0110100 | 1 |
| P | 1000010 | 2 |
| P | 1000100 | 2 |
| P | 1001001 | 1 |
| P | 1010001 | 1 |
| P | 1111000 | 1 |
| C | 1100000 | 5 |
| C | 1110000 | 5 |
| C | 1111000 | 4 |
| C | 1111100 | 5 |
| C | 1111110 | 4 |
| T | 1111111 | 4 |

**Theorem 312.2 (The complete 43-charge inequality).**
Its invariants are

$$
\beta=(0,0,5,5,4,5,4),\quad K=43,\quad
W=B_N=B_O=20,\quad\Delta_N=\Delta_O=0.
\tag{312.1}
$$

For every $L\ge7$, ordered $3\le j_1<\cdots<j_5\le L$,
real finite profile and one complete feasible allocation in either
class of any finite mass,

$$
5b_{j_1}+5b_{j_2}+4b_{j_3}+5b_{j_4}+4b_{j_5}\le43e.
\tag{312.2}
$$

Consequently every original competitor in either class satisfies

$$
43e_a(A)\ge5a_{j_1}+5a_{j_2}+4a_{j_3}+5a_{j_4}+4a_{j_5}.
\tag{312.3}
$$

**Proof.** The union weights total 16, the correct weights total
23, and $T=4$. Class summation gives the displayed $\beta$ and
$K$. Both $R$ and constant-zero output earn all 16 union units
and the four positive units, giving 20. Here is the full addition
and maximum certificate, with all eight labels in every cell:

| Pair | Maxima in $00,01,10,11$ |
| --- | --- |
| 12 | $(0,9,6,5)$ |
| 13 | $(5,4,5,6)$ |
| 14 | $(5,4,5,6)$ |
| 15 | $(6,3,5,6)$ |
| 16 | $(7,2,5,6)$ |
| 17 | $(9,0,5,6)$ |
| 23 | $(5,1,5,9)$ |
| 24 | $(5,1,5,9)$ |
| 25 | $(4,2,7,7)$ |
| 26 | $(4,2,8,6)$ |
| 27 | $(4,2,10,4)$ |
| 34 | $(5,5,5,5)$ |
| 35 | $(6,4,5,5)$ |
| 36 | $(7,3,5,5)$ |
| 37 | $(9,1,5,5)$ |
| 45 | $(6,4,5,5)$ |
| 46 | $(7,3,5,5)$ |
| 47 | $(9,1,5,5)$ |
| 56 | $(7,4,5,4)$ |
| 57 | $(9,2,5,4)$ |
| 67 | $(10,2,4,4)$ |

Every quadruple sums to 20. Formula (309.5) specifies every one
of the $21\cdot4\cdot8=672$ integer reward sums behind the table.
Lemma 309.3 supplies the complete-catalog support at every horizon
and embedding, including outside, earlier and unqueried labels.
Pairing with the same allocation yields

$$
F_{QZ_{43}}=5b_{j_1}+5b_{j_2}+4b_{j_3}+5b_{j_4}+4b_{j_5}-43e
\le M\Delta_N(Z_{43})=0.
$$

The stopped conclusion follows either from its catalog or its
counted completion. The original implication and limit follow from
309.3, even if a smaller proposed cap activates more tail addresses.
At error one the weighted amplitude sum is at most $23<43$.
This proves all assertions. $\square$

**Corollary 312.3 (The same cut in directional coordinates).**
Put $R_J=(46/5)e-\sum_{k=1}^5b_{j_k}$ and
$v_k=b_{j_k}-(13,10,9,8,6)_k e/5$. Then (312.2) is exactly

$$
v_3+v_5\ge-5R_J.
\tag{312.4}
$$

**Proof.** Expanding $5R_J+v_3+v_5$ gives
$43e-5b_{j_1}-5b_{j_2}-4b_{j_3}-5b_{j_4}-4b_{j_5}$.
This is one inequality in two coordinate systems, not a second
mathematical result. On the cone below, $R_J=2\sigma/5$ and
$v_3+v_5=-2\sigma$, so it is tight. $\square$

## 313. Attained optimum throughout the feasible late-amplitude cone

**Theorem 313.1 (Both heads may be strict).**
Let $\tau,\sigma\ge0$, $\tau+\sigma>0$, and prescribe

$$
\begin{gathered}
E=5\tau+17\sigma,\\
(a_3,a_4,a_5,a_6,a_7)=
(13\tau+46\sigma,10\tau+35\sigma,9\tau+29\sigma,
 8\tau+26\sigma,6\tau+20\sigma).
\end{gathered}
\tag{313.1}
$$

Take any ordered heads $1\ge a_1\ge a_2\ge a_3$ satisfying

$$
a_1+7\tau+23\sigma\le1,\qquad
 a_2+11\tau+34\sigma\le1,
\tag{313.2}
$$

and any entire positive nonincreasing vanishing continuation with
$a_8\le E$. Then

$$
\min_{A\in\mathcal N_2} e_a(A)
 =\min_{A\in\mathcal O_2} e_a(A)=E.
\tag{313.3}
$$

Both minima are attained by the law below and its same-seed counted
completion. For this fixed entire sequence, feasibility in either
class at any positive closed cap $c$ is equivalent to $c\ge E$.
This includes $a_8=E$, both parameter axes, and both strict head
inequalities. It imposes no summability requirement on the tail.

**Proof: lower bound on every original competitor.**
Use (312.3) at $(j_1,\ldots,j_5)=(3,4,5,6,7)$. The exact generator
products are

$$
\begin{aligned}
(5,5,4,5,4)\mathbin{\cdot}(13,10,9,8,6)&=215=43\cdot5,\\
(5,5,4,5,4)\mathbin{\cdot}(46,35,29,26,20)&=731=43\cdot17.
\end{aligned}
\tag{313.4}
$$

Therefore every original competitor has $43e_a(A)\ge43E$.
This is independent of both heads. In particular a hypothetical
smaller cap cannot escape the bound by changing active horizon or
by activating additional actual tail coordinates.

**Reused construction for the upper bound.**
Use exactly Construction 307.2, with no new primal credit. To give
the complete attaining rule here, the following table lists
$O(i,j;u,v,z)$ on stopped cells $0,10,11$ and its mass
$A\tau+B\sigma$:

| $i$ | $j$ | $u$ | $v$ | $z$ | $A$ | $B$ |
| --- | --- | --- | --- | --- | ---: | ---: |
| 1 | 2 | 1 | 2 | 3 | 2 | 7 |
| 1 | 2 | 1 | 2 | 4 | 1 | 4 |
| 1 | 2 | 1 | 2 | 5 | 1 | 4 |
| 1 | 3 | 1 | 3 | 0 | 3 | 11 |
| 1 | 4 | 1 | 4 | 0 | 1 | 3 |
| 2 | 3 | 0 | 3 | 0 | 3 | 8 |
| 2 | 3 | 2 | 3 | 0 | 0 | 3 |
| 2 | 4 | 0 | 4 | 0 | 1 | 3 |
| 3 | 4 | 0 | 4 | 0 | 1 | 6 |
| 3 | 4 | 0 | 4 | 5 | 1 | 2 |
| 3 | 5 | 0 | 5 | 0 | 1 | 3 |
| 3 | 6 | 0 | 6 | 0 | 1 | 3 |
| 4 | 5 | 0 | 5 | 0 | 1 | 3 |
| 4 | 6 | 0 | 6 | 0 | 1 | 3 |
| 5 | 6 | 0 | 6 | 0 | 1 | 3 |
| 6 | 7 | 0 | 7 | 0 | 1 | 3 |

The core mass is $20\tau+69\sigma$. Set

$$
\rho=1-20\tau-69\sigma,\qquad
x_1=a_1-13\tau-46\sigma,\qquad
x_2=a_2-9\tau-35\sigma.
\tag{313.5}
$$

The remaining mass is one prefix $(1,2)$ branch with cell vectors

$$
(\rho-x_1)e_0+x_1e_1,\qquad
(\rho-x_2)e_0+x_2e_2,\qquad \rho e_0.
\tag{313.6}
$$

Order and (313.2) give

$$
\rho\ge4\tau+11\sigma>0,\qquad
0\le x_1\le\rho,\qquad
4\tau+11\sigma\le x_2\le\rho.
\tag{313.7}
$$

Indeed $a_2\ge a_3$ and its head bound imply
$24\tau+80\sigma\le1$, giving the lower bound on $\rho$.
The two upper bounds $x_i\le\rho$ are exactly the two head
inequalities; the lower bounds follow from head order.
Thus every core mass and every vector entry is nonnegative, and
the core plus the one prefix mass totals one. To specify complete
table weights for that prefix, set

$$
\begin{aligned}
q_{11}&=\min(x_1,x_2),&q_{10}&=(x_1-x_2)_+,\\
q_{01}&=(x_2-x_1)_+,&q_{00}&=\rho-\max(x_1,x_2).
\end{aligned}
\tag{313.8}
$$

Assign mass $q_{ab}$ to $O(1,2;a,2b,0)$ for $a,b\in\{0,1\}$.
All four masses are nonnegative and total $\rho$, with first-cell
correct mass $x_1$ and middle-cell correct mass $x_2$. Equivalently,
on one local uniform coordinate $V$, fix both counterfactual choices
by $V<x_1/\rho$ and $V<x_2/\rho$ before replies. There is no
condition $x_1+x_2\le\rho$: for example $x_1=x_2=\rho$ selects
just $O(1,2;1,2,0)$ of mass $\rho$. This explicit coupling only
unpacks the existing common-prefix construction.

**Verification on every word for the same law.**
Direct addition of the sixteen core rows gives the following correct
mass coefficients, independent of every bit after the first zero:

$$
\begin{array}{c|rrrrrrr}
n&1&2&3&4&5&6&7\\\hline
\tau&8&4&8&5&4&3&1\\
\sigma&29&18&29&18&12&9&3
\end{array}
\tag{313.9}
$$

For example the first three rows give $(4,15)$ in each of the
first two classes; rows $(1,3),(1,4)$ add $(4,14)$ in class 1,
and $(2,3;2,3,0)$ adds $(0,3)$ in class 2. In the later classes,
earlier queried bits are one, so the displayed second or exhaustion
outputs give the same totals for every suffix. Adding $x_1,x_2$
from the prefix proves

$$
p_w(n)=a_n-E\qquad(n=n(w)\le7).
\tag{313.10}
$$

It remains to bound the independent union deficit, not just the
correct event. Let $D_n$ be the mass outside $\{0,n\}$.
The prefix contributes zero to this mass. For the core set
$(s,t,u,v,z)=(w_3,w_4,w_5,w_6,w_7)$ and define

$$
\begin{aligned}
B&=2s(1-t)+st+(s+t)(2-u-v)+u(1-v)+v(1-z),\\
G&=3(1-s)+(1-t),\\
B'&=8s(1-t)+2st+3(s+t)(2-u-v)+3u(1-v)+3v(1-z),\\
G'&=11(1-s)+3(1-t).
\end{aligned}
\tag{313.11}
$$

Evaluation of the listed stopped rows gives these exact coefficients
of $D_n$, retaining every Boolean suffix:

| First zero | Coefficient of $\tau$ | Coefficient of $\sigma$ |
| --- | --- | --- |
| 1 | $B+w_2G$ | $B'+w_2G'+3(1-w_2)$ |
| 2 | $B+G$ | $B'+G'$ |
| 3 | $2+2(1-t)+t(2-u-v)+u(1-v)+v(1-z)$ | $8+6(1-t)+3t(2-u-v)+3u(1-v)+3v(1-z)$ |
| 4 | $3+(1-u)+(1-v)+u(1-v)+v(1-z)$ | $11+3[(1-u)+(1-v)+u(1-v)+v(1-z)]$ |
| 5 | $3+2(1-v)+v(1-z)$ | $11+6(1-v)+3v(1-z)$ |
| 6 | $5$ | $17$ |
| 7 | $5$ | $17$ |

Here is an analytic all-suffix bound, so no extrapolation from
rational parameter tests is needed. For $q=s+t$, distinguish
$uv=00,01,10,11$ in
$q(2-u-v)+u(1-v)+v(1-z)$. After maximizing over $z$ its maximum
is $\max\{2q,q+1,1\}$, giving $1,2,2,4$ for
$st=00,01,10,11$. Substitution yields

$$
\begin{array}{c|rrrr}
st&00&01&10&11\\\hline
\max B&1&2&4&5\\
G&4&3&1&0\\
\max B'&3&6&14&14\\
G'&14&11&3&0
\end{array}
\tag{313.12}
$$

Thus $B+G\le5$ and $B'+G'\le17$.
Class 1 with $w_2=1$ uses those bounds, and with $w_2=0$ uses
$B\le5$ and $B'+3\le17$.
In class 3, $t=0$ gives bounds five and seventeen because
$u(1-v)+v(1-z)\le1$; $t=1$ gives four and fourteen because
$2-u-v+u(1-v)+v(1-z)=2-uv-vz\le2$.
For class 4 its bracket is likewise $2-uv-vz\le2$.
Class 5 follows from $v=0,1$, and classes 6 and 7 are constant.
Consequently every coefficient is bounded by five or seventeen,
respectively. Nonnegative real $\tau,\sigma$ give $D_n\le E$
on every word for this same law.

Using (313.10), the three distinct deficits (309.2) are

$$
1-a_n-p_w(0)=D_n-E\le0,\qquad
a_n-p_w(n)=E,\qquad
1-p_w(0)-p_w(n)=D_n\le E.
\tag{313.13}
$$

Thus TV is exactly $E$ on every first-zero fibre up to seven.
The positive word has nonbase mass from just the first three core
exhaustion outputs and $(3,4;0,4,5)$:
$(4\tau+15\sigma)+(\tau+2\sigma)=E$.
The prefix emits zero there, so $p_+(0)=1-E$.

**Original execution, tails and closed caps.**
Partition one source-independent uniform seed into half-open intervals
of the sixteen core masses and the prefix mass $\rho$. The prefix
local coordinate fixes both thresholds, or the four weights (313.8),
before seeing replies. Interval endpoints can be assigned to either
adjacent table; every resulting table obeys the same resource bound.
Execute the selected increasing schedule on the same actual source,
stop at the first queried zero or exhaustion, and emit the indicated
actual original mark. This is a measurable zero-advice rule with
finite handoff at every seed and source and at most two actual calls.
Its $N$ completion uses exactly the same seed and actual source,
obtains the entire preselected schedule, reconstructs the stopped
output and counts any ignored second reply. It has the identical law.

No mark above seven is emitted. Every actual $n>7$ therefore has
exact error

$$
\max\{1-p_+(0),a_n\}=\max\{E,a_n\}=E.
\tag{313.14}
$$

This includes the tie $a_8=E$ and every permitted positive
nonincreasing vanishing continuation. The positive finite word
represents actual later-zero sources, not an infinite all-positive
source. Since $a_7-E=\tau+3\sigma>0$, the active horizon at $E$
is exactly seven. Hence both original rules attain $E$, matching
(313.4). The same law meets every larger cap, while (313.4) excludes
every smaller cap. This completes the proof of (313.3) and its
closed-cap equivalence. $\square$

**Corollary 313.2 (The reused projection and its newly sharp interior).**
The head domain (313.2) is nonempty exactly when
$24\tau+80\sigma\le1$. If $a_2=a_3$, its finite profile is in
$H_N$ with the same mass-one allocation. The only new optimality
scope relative to 307.1 and 300.1 is $\sigma>0$ with both head
inequalities strict; the old sufficient head-tightness conclusion
remains valid.

**Proof.** Necessity of the scale bound was shown in (313.7).
Conversely take $a_1=a_2=a_3$: the second head inequality is exactly
that bound, and the first follows since
$20\tau+69\sigma\le24\tau+80\sigma$.
For $a_2=a_3$, the hull excess is
$\sum_{3}^7a_n-8E=6\tau+20\sigma>0$ and
$a_1+6\tau+20\sigma\le1-\tau-3\sigma<1$.
Order, $a_7>E$ and equality of the second and third amplitudes give
all other hull conditions. The one law just proved supplies full
mass-one feasibility. These projection, hull and primal facts are
those of 307; the lower certificate 312 supplies the previously
unclaimed interior optimality. When $\sigma=0$ the old ray theorem
300.1 already proves optimality, including strict heads. When a
head is tight 307.1 already proves it. That theorem said "if", not
"only if", so no old result is reversed. $\square$

**Example 313.3 (A genuinely strict-head parameter point).**
Set $\tau=0$, $\sigma=1/100$,
$(a_1,\ldots,a_7)=(46,46,46,35,29,26,20)/100$ and
$a_n=(17/100)2^{-(n-8)}$ for $n\ge8$.
Then $E=17/100$, $\rho=31/100$, $x_1=0$ and $x_2=11/100$.
The first and second head slacks are $31/100$ and $1/5$.
The hull excess is $1/5$, its sum with $a_1$ is $33/50$,
and $p_+(0)=83/100$. The theorem gives both attained original
optima $17/100$; the same conclusion holds with any other permitted
tail bounded at eight by $17/100$.

For a bounded necessary-basis comparison, keep the same first seven
amplitudes but take $c_0=1699/10000$ and
$a_n=c_0\,2^{-(n-8)}$ for $n\ge8$.
The active horizon is seven and its hull excess is $251/1250$.
The exact readings of $Y_1,Y_2,C$ and the reused uniform five-late
cut $\sum_{3}^7a_n\le(46/5)c_0$ are, respectively,

$$
-\frac{3083}{10000},\qquad-\frac{49}{250},\qquad
-\frac{7829}{10000},\qquad-\frac{77}{25000}.
$$

Their nonnegative late coefficients make consecutive placements the
largest readings among all ordered placements. The new reading is
$43/10000>0$. These are exact substitutions into the specified
inequalities, and show refinement only of that named basis.
The new cut excludes this profile from complete $N$ feasibility;
it is not a separator or a second optimum result. Its fixed sequence
still has optimum $17/100$ by 313.1, since its new tail also lies
below that cap.

## 314. Source conditions, credit and the remaining unrestricted question

The legal regression of 303.2 remains explicit. At $(r,g)=(19,436)$,
$F_{19}=4181$, the allowed window is $419\le436\le836$ and
$N=1822917$. Replies on primes $2,3,5,7$ are $0100$.
The complete-catalog rule $N(3,4;1,0,0,0)$ makes two actual requests
at addresses 3 and 4, obtains $00$ and emits earlier unqueried label
1. The endpoint rule $O(3,4;0,0,0)$ emits zero on the same source.
Changing that unit mass has $\ell^1$ defect two and TV one.
It is a regression against a free endpoint repair, not an original
class separator. All the words, labels and actual calls in this
example remain allowed by every catalog above.

The mature framework in 303.3 retains its precise scope. In David
Blackwell, *Comparison of Experiments* (1951), pp. 93–102,
[sections 2–3, Theorem 2 and its proof](https://digitalassets.lib.berkeley.edu/math/ucb/text/math_s2_article-08.pdf),
an experiment is finitely many probability measures on a Borel space,
actions form a bounded subset of finite-dimensional loss space, and
comparison concerns whole attainable loss vectors and their convex
closure. The supporting-hyperplane argument tests those joint vectors.
It supplies a comparison framework, not our integer coefficients or
a hard-two increasing-stopping bridge.
In Jędrzej Kaniewski, Troy Lee and Ronald de Wolf,
*Query complexity in expectation*,
[arXiv:1411.7280v1, Definitions 6 and 8, Theorem 9 and both proof directions](https://arxiv.org/pdf/1411.7280v1),
the target is a nonnegative scalar expectation and the cost is the
maximum supported root-to-leaf depth. The converse samples literal
coefficients of total mass $M$ with probabilities $\alpha/M$ and
multiplies the scalar output by $M$. This does not supply normalized
vector probabilities, equal counterfactual schedule-cell masses or
an increasing first-queried-zero rule. Those conditions are verified
here by the complete rows and the one explicit common law.

The full 46-row score and its pairing supply one joint two-tail
necessity result. The old $Y_2$, six-late bound, collective half-sum
bound, diagnostic comparisons, source arithmetic and exact closed-cap
transport receive no repeat content credit. The 18-row score is one
sufficient proof route to one optimality completion on the entire
feasible cone 307.1. Alternative normals or row realizations do not
supply additional discoveries. Its upper law, head projection, scale
condition, parameter axes and previously sharp contacts are reused;
the new optimum scope is $\sigma>0$ with both heads strict.
These are ordinary mathematical arguments, without a claim of formal
kernel verification, exhaustive novelty or priority.

Neither result supplies a gapped primal law, a classification for
arbitrary other amplitude cones, or an attained value for the larger
cap lower bound (311.3). Every finite atomic law displayed here has
TV one from every unchanged original nonatomic target, since the
latter gives its finite support zero mass. Accuracy is only to the
separately selected marked laws. The original full carrier, consumer,
sourcewise execution and all actual positive tails remain unchanged.

The unrestricted obligation is still the full quantified statement
303.1. For every $L\ge3$ and every full $y\ge0$ with
$\Delta_O(y)\le1$, it requires one unrestricted full $V\ge0$ and
one $\theta\in[0,1]$ satisfying

$$
\Delta_N(V)+\theta\le1,\qquad
\sigma_H(Qy-QV)\le\theta,\qquad
\sigma_H(q)=\max_{(b,e)\in H_L}F_q(b,e).
\tag{314.1}
$$

The residual is signed. No fixed-anchor, unary-only, exact-quotient
or positive-residual restriction is imposed on $V$; a nonzero
zero-cost $V$ at $\theta=1$ is allowed. The negative alternative
requires the same actual $(b,e)\in H_N$, one complete feasible
$\lambda$ of mass $M\ge1$, a full unit-$O$ score with
$F_{Qy}(b,e)>M$, an original same-seed $N$ attainer and a uniform
strict lower bound against every original arbitrary-address,
full-carrier $O$ competitor. Equivalently the original question is
whether every positive nonincreasing vanishing sequence and every
positive closed cap satisfy
$\mathcal F_N(a,c)\ne\varnothing\Rightarrow
 \mathcal F_N(a,c)\cap\mathscr C_{L_a}\ne\varnothing$,
or admit that complete original separator.

The excluded profiles in 311.1 and 313.3 have no full feasible $N$
allocation at their tested caps. The attaining laws in 311.2 and
313.1 belong to both classes. They provide neither unrestricted
alternative. All original quantifiers, common-seed, zero-advice,
finite-handoff, two-actual-request, all-word, all-label, independent
union-row, target, positive-tail and closed-cap obligations persist.
The stopping point of the present results is the proved joint
two-tail necessity and the attained optimum on the declared cone.

## 追加锚（本行以下为增补区）
