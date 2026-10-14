# k-bonacci 自校准获取资源续卷 IX：共同 Boolean 矩、保留信用与低尾精确比较

This volume continues
[Continuation VIII, §206](KBONACCI_SELF_CALIBRATING_ACQUISITION_RESOURCES_CONTINUATION_VIII.md).
It uses ordinary mathematical definitions and proofs. Throughout,
$x_+=\max\{x,0\}$, empty sums are zero, and a maximum of an empty
family of nonnegative quantities is zero. All displayed weak inequalities
include their equality endpoints.

## 207. Joint realizability, retained early credit and equal-cylinder comparison

The four groups below concern a biased product construction, a reduced
correlated stock threshold, a global Boolean realizability obstruction
with a sharp protected-stock bound, and an exact low-tail fixed-data
comparison. The sufficient regions may overlap. A score is a collection
of nonnegative proof weights, not a probability allocation or a law on
the original sources.

**Definition 207.1 (Original source and resources).** Retain the source
and transport of [110.1–110.2](KBONACCI_SELF_CALIBRATING_ACQUISITION_RESOURCES_CONTINUATION.md#110-exact-closed-cap-transport-on-the-original-countable-source):

$$
\begin{aligned}
X&=\{(r,g):r\text{ prime},\ g\in\mathbb Z,
 \lceil F_r/10\rceil\le g\le\lfloor F_r/5\rfloor\},\\
N(r,g)&=1+F_rg,\qquad F_0=0,\ F_1=1,\ F_{r+2}=F_{r+1}+F_r,\\
q_i(x)&=\mathbf1_{p_i\mid N(x)},\qquad
n(x)=\min\{i:q_i(x)=0\},
\end{aligned}
\tag{207.1}
$$

where $p_1<p_2<\cdots$ are the primes. Replies are static. Every finite
Boolean word, including every multiple-zero word, has an actual source
witness by Boundaries, Theorem 35.2. The full tape carrier is the Borel
disjoint union $\bigsqcup_{j\ge1}B_j\sqcup\bigsqcup_{j\ge1}P_j$,
each block a copy of $(0,1)$, with distinct measurable marks
$\theta_j=(B_1,1/(j+2))$, $j\ge0$. The consumer and its original
nonatomic targets remain those of Acquisition Resources, Definition 73.1.
For every sequence

$$
1\ge a_1\ge a_2\ge\cdots>0,\qquad a_j\longrightarrow0,
\qquad
\lambda_x^a=(1-a_{n(x)})\delta_{\theta_0}
                  +a_{n(x)}\delta_{\theta_{n(x)}},
\tag{207.2}
$$

the marked laws are separately selected; they do not replace the original
consumer targets. No condition on a score profile below restricts this
class of amplitude sequences.

$\mathcal N_2,\mathcal O_2$ have exactly the resource meaning of
Acquisition Resources, Definition 90.1: zero advice, one common
source-independent seed, actual sourcewise almost-sure finite handoff,
arbitrary addresses, and outputs anywhere in the full carrier. The hard
bound is at most two actual requests, including repetitions and ignored
replies. $N$ preselects its whole schedule and obtains its replies; $O$
preselects an increasing schedule and stops at its first queried zero or
at exhaustion. The second address is not chosen adaptively. Error is
the supremum of TV over all actual sources and all Borel events. There
is no source distribution, extra observation, address bound, runtime
bound, mean-request relaxation or additional seed.

For $0<\varepsilon\le1$, let
$L_a=\max(\{j:a_j>\varepsilon\}\cup\{0\})$. Every low word with
first zero $n$ has the independent finite demands

$$
p_w(0)\ge1-a_n-\varepsilon,\qquad
p_w(n)\ge a_n-\varepsilon,\qquad
p_w(0)+p_w(n)\ge1-\varepsilon,
\qquad p_{1^{L_a}}(0)\ge1-\varepsilon.
\tag{207.3}
$$

The pair row is not deduced from the singleton rows. Negative singleton
demands and rows with zero score remain. Theorem 109.1 characterizes
the normalized stopped kernels by its coefficient condition $c\ge H$;
Theorem 110.2 transports feasibility at the exact closed cap. Neither
failure to reproduce one $N$ law nor a score example proves that no
other stopped law meets that cap.
Here $\mathscr N_{L_a}$ is the convex hull of complete finite $N$
tables, $\mathscr C_{L_a}$ is the stopped-kernel class of 109.1, and
$\mathcal F_N(a,\varepsilon)$ is the subset of $\mathscr N_{L_a}$
satisfying every row of (207.3).

**Definition 207.2 (Complete scores and fixed totals).** Fix $L\ge3$.
For every $w\in\{0,1\}^L\setminus\{1^L\}$, put
$n(w)=\min\{j:w_j=0\}$ and $\Omega_j=\{w:n(w)=j\}$. A full score
has independent coefficients $A_w,C_w,P_w\ge0$ and $T\ge0$ at $1^L$.
At a zero word label $\ell\in\{0,\ldots,L\}$ earns

$$
g_V(w,\ell)=A_w\mathbf1_{\ell=0}
 +C_w\mathbf1_{\ell=n(w)}+P_w\mathbf1_{\ell\in\{0,n(w)\}};
\qquad g_V(1^L,\ell)=T\mathbf1_{\ell=0}.
\tag{207.4}
$$

For each schedule, sum rewards inside each cell, maximize over **all**
labels in that cell, then sum the maxima. $B_N(V)$ maximizes over empty,
singleton and distinct-pair schedules, the latter with cells
$00,01,10,11$. $B_O(V)$ uses increasing pairs and cells $0,10,11$.
Unqueried and earlier labels remain available. With anchor
$R=(1,2;1,2,0)$ in stopped-cell order, write

$$
\begin{aligned}
W_V&=\sum_{n(w)\ge3}A_w+\sum_{n(w)\le2}C_w+\sum_wP_w+T,\\
\Delta_C(V)&=B_C(V)-W_V\ge0\quad(C=N,O),\\
Q(V)&=(\beta,K),\quad
\beta_j=\sum_{w\in\Omega_j}(C_w-A_w),\quad
K=\sum_w(A_w+C_w+P_w)+T.
\end{aligned}
\tag{207.5}
$$

The input family has $A=0$, arbitrary correct rows, pair support in
$\Omega_1\cup\Omega_2$ (including early prefix $00$), and $T=t$.
Set

$$
\gamma_j=\sum_{\Omega_j}C_w,\quad E=\gamma_1+\gamma_2,\quad
G=\sum_{j=3}^L\gamma_j,\quad\mu=\max_{j\ge3}\gamma_j,\quad
S=\sum_wP_w,\quad W=E+S+t.
\tag{207.6}
$$

Then $Q=(\gamma,G+W)$. Unless stated otherwise, fixed totals mean each
individual $\gamma_j$, as well as $S,t$. Write $w(Z)$ for the word
whose zero set is exactly $Z$. In every construction, unspecified
coefficients are zero and coincident coefficients are added.

An empty or singleton output function embeds in a distinct-pair $N$
table by ignoring answers. Reversal permutes cells; repetition gives
singleton information. Thus bounds for all distinct $N$ pairs cover the
whole catalog. These information identities do not exempt any actual
request from the hard count. Every $O$ table is an $N$ function, so
$B_O\le B_N$. Adding any early $C$ row, early $P$ row or $T$ row
increases each fixed-table reward by at most its weight and the anchor
by exactly its weight. Such additions cannot increase either excess.

**Definition 207.3 (Reused signed residual and one-budget certificate).**
Use the hull and certificate of 198.5, 199.3–199.4 and 206.3. With
$\alpha=(1,1,0,\ldots,0)$,

$$
\begin{aligned}
H_L=\{(b,e):\;&1\ge b_1\ge\cdots\ge b_L\ge e\ge0,
\ b_2=b_3,\\
 &(L+1)e\le\sum_{j=3}^Lb_j,\quad
 b_1+\sum_{j=3}^Lb_j-(L+1)e\le1\},\\
F_{(\beta,K)}(b,e)&=\sum_j\beta_j(b_j-\alpha_j)-Ke,
\qquad\sigma_H(q)=\max_{H_L}F_q.
\end{aligned}
\tag{207.7}
$$

Its vertices are $o=0$, $p=(1,0,\ldots;0)$, and for $3\le k\le L$,
$u_k$ with its first $k$ entries $1/(k-1)$ and all other entries zero,
and $v_k$ with its first $k$ entries one and all remaining entries,
including $e$, equal to $(k-2)/(k+1)$. For a comparison score with early
correct totals $c_1,c_2$, late totals $\eta$, early pair support, no
base rows and anchor $W'$, put
$x=\gamma_1-c_1$, $y=\gamma_2-c_2$,
$R_k=\sum_{j=3}^k(\gamma_j-\eta_j)$. The exact residual readings are

$$
-x-y,\qquad-y,\qquad
\frac{R_k-(k-2)(x+y)}{k-1},\qquad
\frac{3R_k+(k-2)(W'-W)}{k+1}.
\tag{207.8}
$$

These follow by substitution, using $K_y-K_V=R_L+W-W'$; both prefix
columns are retained and the residual need not have positive coordinates.
Its nonnegative charge is the maximum of these readings and zero.

Let $d(b,e)$ contain all three demands $1-b_n-e,b_n-e,1-e$ at every
zero word and $1-e$ at the positive word. Put $r=z_R=d(\alpha,0)$,
$h=d-r$, and $G_C=(z_D-r)_D$ for the full event columns. A certificate
is one $V\ge0$ and one $\theta\in[0,1]$ with

$$
\Delta_N(V)+\theta\le1,\qquad
\sigma_H(q-Q(V))\le\theta.
\tag{207.9}
$$

Write $E_N$ for the set of $q$ admitting (207.9). For $(b,e)\in H_L$
and the same complete $\lambda\ge0$ satisfying
$G_N\lambda\ge h(b,e)$, of mass $M$, nonnegativity gives

$$
F_q(b,e)\le V\cdot h(b,e)+\theta
 \le V\cdot G_N\lambda+\theta
 \le M\Delta_N(V)+\theta\le\max\{1,M\}.
\tag{207.10}
$$

For $M\le1$ use $M\Delta_N\le\Delta_N$; for $M\ge1$ use
$\theta\le M\theta$. Every same-$Q$ construction below has residual
identically zero, so uses $\theta=0$. This is the existing certificate
rule, not separate allowances for cells or components.

**Definition 207.4 (The subset measure supplied by 201.2).** On a set
$J$ of $m\ge2$ actual addresses and for $a\ge0$, write $\mathcal L_m(a)$
for this measure on zero subsets. If $m=2q-1$, put mass
$2ma/[q\binom mq]$ on each $q$-subset. If $m=2q$, put mass
$2a/\binom mq$ on each $q$-subset and
$2qa/[(q+1)\binom m{q+1}]$ on each $(q+1)$-subset. Its total is
$c_ma$, where $c_m=4-2/\lceil(m+1)/2\rceil$; its unary zero masses
are $2a$ and both directed disagreement masses are $a$. Thus every
answer pair has cells $(a,a,a,(c_m-3)a)$. These are the same atoms as
201.2. The inclusion and directed-disagreement probabilities for a
uniform $r$-subset are $r/m$ and $r(m-r)/(m(m-1))$; substitution proves
the stated moments simultaneously for this one measure.

### 207.1 A biased product retaining early correct credit

**Theorem 207.5 (Same-total biased construction).** Suppose $s>0$,
$0\le d\le s$, and $\gamma_j\le s+d$ for every late $j$. Choose
$0\le c_a\le\gamma_a$, $a=1,2$, and put $c=c_1+c_2$. If

$$
c\le s,\qquad(s-c)^2\ge sd,\qquad
S\ge\frac{(2s-c)^2}{s},\qquad t\ge s,
\tag{207.11}
$$

there is a full score with the prescribed totals, hence the same $Q,W$,
and $\Delta_N\le d$. If $\mu=s+d$ and $t=s$, both excesses equal
$d$, and $d$ is their attained minimum over the entire fixed-total
$A=0$/early-pair class, with unrestricted correct suffixes and early
pair allocation.

**Proof.** Put

$$
v=s-c,\quad M=2s-c=s+v,\quad S_0=M^2/s,\quad
q=s/M,\quad z=v^2/s,\quad\rho_a=(s-c_a)/M.
\tag{207.12}
$$

On the entire late cube define one measure
$\nu(x)=S_0\prod_{j=3}^Lf(x_j)$, where $f(0)=q$, $f(1)=1-q$.
At $01x$ and $10x$, respectively, put $P=\rho_1\nu(x)$ and
$P=\rho_2\nu(x)$. Put $C=c_a$ at
$e_a=w(\{a\}\cup\{3,\ldots,L\})$. For each late $j$, put

$$
C_{w(\{j\})}=\min(\gamma_j,v),\qquad
C_{w(\{j,\ldots,L\})}=(\gamma_j-v)_+,\qquad T=s.
\tag{207.13}
$$

This core has anchor $W_0=c+S_0+s$. All coefficients are nonnegative
and $\rho_1+\rho_2=1$. Product summation gives

$$
\nu(x_j=0)=M,\quad\nu(x_j=1)=Mv/s,\quad
(\nu_{00},\nu_{01},\nu_{10},\nu_{11})=(s,v,v,z),
\quad S_0=s+2v+z.
\tag{207.14}
$$

Writing $\nu_a=\rho_a\nu$, we also have

$$
\nu_a(x_j=0)+c_a=s,\quad
\nu_a(x_j=1)=(s-c_a)v/s\ge z\ge d,\quad
\rho_as+c_a\le s.
\tag{207.15}
$$

Since $v^2\ge sd$ and $s\ge d$, $v\ge d$. Every absorbing
correct mass is at most $s+d-v=c+d\le s$.

The head pair $(1,2)$ has maxima
$(0,\rho_1S_0+c_1,\rho_2S_0+c_2,\max(s,\mu))$, of sum at most
$W_0+d$. For an early/late pair $(a,j)$, with $b$ the other early
index, the four maxima are bounded by

$$
\bigl(s,\ \nu_a(x_j=1),\ s+d,\ \nu_b(x_j=1)+s\bigr).
\tag{207.16}
$$

The early-zero cells contain only early class $a$; its zero-suffix
correct mass gives the first entry. Cell $10$ contains the other early
label with reward $s$ and late labels of total at most $s+d$. In $11$
there is no early correct mass, and the zero reward is at least $s+d$
by (207.15), so it dominates all labels. The sum in (207.16) is
$W_0+d$, using $\nu_b(x_j=0)=s-c_b$.

For late $i<j$, an earlier class has its absorbing part only in $00$
and its singleton part only in $11$. Class $i$ has singleton mass in
$01$, an intermediate class has absorbing mass in $10$ and singleton
mass in $11$, class $j$ lies wholly in $10$, and later classes lie
in $11$. Thus their four bounds are $s,v,s+d,s+d$. Each early label
earns at most $\rho_as+c_a\le s$ in $00$ and at most the pair
baseline elsewhere. Label zero earns $s,v,v,z+s$. Consequently the
complete maxima are bounded by

$$
(s,v,s+d,z+s),
\tag{207.17}
$$

whose sum is $W_0+d$ because $c=s-v$ and $z\ge d$. This includes
all earlier unqueried labels. Catalog completion from 207.2 proves the
core upper bound. Complete the prescribed totals by adding
$C=\gamma_a-c_a$ at $e_a$, $P=S-S_0$ at $e_1$, and $T=t-s$.
These anchor-collected additions cannot increase the excess.

For any competitor with those totals, the stopped table
$(1,2;1,2,j_*)$, where $\gamma_{j_*}=\mu$, collects $E+S+\mu$,
including every early $00$ pair row. It forces
$\Delta_O\ge\mu-t$. At $\mu=s+d,t=s$ this equals the constructed
upper bound $d$; $\Delta_O\le\Delta_N$ proves both attained minima.
$\square$

**Corollary 207.6 (Optimizing the displayed stock requirement).** For
$d\ge0$, $\mu>0$, $\mu\ge2d$, take

$$
s=\mu-d,\qquad c_* =\min\{E,s-\sqrt{sd}\}.
\tag{207.18}
$$

Then $t\ge s$ and $S\ge(2s-c_*)^2/s$ suffice. Indeed $c_*$ is the
largest permitted retained early mass, and $(2s-c)^2/s$ decreases for
$0\le c\le s$. It can be split below the two early totals, for
example $c_a=c_*\gamma_a/E$ when $E>0$. This is an optimization only
within (207.11). For a unit-$O$ input with $\mu\ge2$, the head table
already forces $t\ge\mu-1$; the stock condition is an additional
sufficient hypothesis. Zero $d$, zero class totals, arbitrary early
imbalance and all equalities are included. When $c=s,d=0$, $q=1$ and
the product is the all-zero late atom. If $\mu=0$, the anchor collects
every scored row and both costs are zero directly.

**Example 207.7 (A full family with cost one).** For every $L\ge6$,
let $\gamma_1+\gamma_2=2$, $\gamma_a\ge0$, and $\gamma_j=5$ for
all late $j$. Put $S=9,t=4$. In 207.5 choose $s=4,d=1,c_a=\gamma_a$
and $c=2$, so
$v=2,q=2/3$ and $\rho_a=(4-\gamma_a)/6$. Explicitly,
$\nu(x)=9\prod f(x_j)$ with $f(0)=2/3,f(1)=1/3$, pair rows
$\rho_a\nu$ on the two early lifts, early $C=\gamma_a$ at $e_a$,
late $C=2$ at each singleton and $C=3$ at each absorbing suffix,
and $T=4$. Here $W=15$, $K=5(L-2)+15$.

The empty support is $13$; a single early $a$ has support
$13+\gamma_a$, and each single late address has support $13$.
The complete pair maxima are

| Schedule | $N$ maxima in order $00,01,10,11$ |
| --- | --- |
| $(1,2)$ | $(0,6-\gamma_1/2,6-\gamma_2/2,5)$ |
| early/late $(a,j)$ | $(4,2-\gamma_a/2,5,5+\gamma_a/2)$ |
| late/late | $(4,2,5,5)$ |

These follow from (207.14)–(207.17); in each first branch a common
label attains both constituent maxima, so merging to $O$ loses nothing.
Every pair support is $16$ and both excesses are one.

For precise comparison, 203.2 at this projection has unary masses $6$,
directed masses $2$, hence $\kappa=3$, $\pi=1$. In the entire
full-profile product family of 203.4, $5\le u\le15/2$ and two
cost terms are $2u-10$ and $15-2u$; their sum is five, so its cost
is at least $5/2$. The fair unit threshold of 203.6 is $20>15$.
The displayed stock-exchange test of 206.17 requires
$S\ge\max(10,16-4)=12>9$. Zero score fails at $u_3$, with reading
$(5-2)/2=3/2$. These compare the named tests and specified product
family, not all of their residual or mixture consequences.

### 207.2 A reduced correlated threshold with one early-credit charge

**Theorem 207.8 (Retained credit on actual active coordinates).** Let
$J=\{j\ge3:\gamma_j>0\}$, $m=|J|\ge2$, and
$c_m=4-2/\lceil(m+1)/2\rceil$. Suppose

$$
d,h\ge0,\quad h\le\min(\gamma_1,\gamma_2),\quad
\mu\ge2d+h,\quad a=\mu-d-h,
\qquad
t\ge\mu-d,
\qquad S\ge\max\{c_ma,2\mu,3\mu-2d-4h\}.
\tag{207.19}
$$

There is a score with the same $\gamma,S,t,Q,W$ and $\Delta_N\le d$.
At $t=\mu-d$, both excesses equal $d$, also the attained fixed-total
minima. Actual gaps in $J$ and arbitrary ordering of the positive
profile are allowed.

**Proof.** On subsets of the actual set $J$ use
$\nu=\mathcal L_m(a)+(S-c_ma)\delta_\varnothing$; inactive bits
are one. Put $P=\nu(Z)/2$ and $C=h\nu(Z)/S$ at each
$w(\{b\}\cup Z)$, $b=1,2$. Here $\mu>0$ since $J$ is active, and
$S\ge2\mu>0$. For each $j\in J$ put $C=\min(\gamma_j,a)$ at
$w(\{j\})$ and $C=(\gamma_j-a)_+$ at
$w(\{n\in J:n\ge j\})$. Set $T=t$. The core has early mass $2h$
and anchor $S+t+2h$. The same measure has unary masses $2a$ and pair
cells $(a,a,a,S-3a)$.

Put $u=(\mu-2a)_+$. The hypotheses imply

$$
a\ge d,\quad u\le h,\quad h\le t,\quad h\le S/2,
\quad S\ge3a+u+d-h,
\quad(d-S+3a)_+\le h-u.
\tag{207.20}
$$

For the fifth inequality its right side is
$\max(3\mu-2d-4h,2\mu-2h)$, bounded by the stock assumptions.
Also $S\ge c_ma\ge3a$.

The head pair has excess $(\mu-t)_+\le d$. On an early/active pair,
the early-zero cells together have maximum $S/2+h$. The $10$ cell
compares the other early label's reward $a+2ah/S$ with late rewards
at most $\mu$. The $11$ zero reward $S/2-a+t$ dominates all late
labels because $S/2\ge\mu$ and $t\ge a$, and dominates the other
early label because its extra correct reward is at most $h\le t$.
Subtracting the whole anchor gives at most

$$
\max(a+2ah/S,\mu)-a-h
 =\max\{-h(1-2a/S),d\}=d.
\tag{207.21}
$$

For active $i<j$, early labels earn the fraction $1/2+h/S\le1$ of
the pair mass in each cell. Threshold correct words bound late rewards
in $00,01,10,11$ by $\mu-a,a,\mu,\mu$. An earlier class has its
absorbing part in $00$ and its singleton part in $11$; an intermediate
class has only $10/11$ contributions. These statements include all
earlier unqueried labels. The total excess is therefore at most

$$
\begin{aligned}
(\mu-2a)_++(\mu-a)+(\mu-t-S+3a)_+-2h
 &\le u+d-h+(d-S+3a)_+\\
 &\le d.
\end{aligned}
\tag{207.22}
$$

This subtracts the early $2h$ once from one complete table. Inactive
coordinates are constant one on the core; queries there reduce to
singleton information. Catalog completion covers all schedules.
Add the original early correct measures scaled to totals
$\gamma_b-h$ (omit a zero-total measure). Their arbitrary suffixes
cause no increase in excess. The resulting totals are exactly the
prescribed ones. At $t=\mu-d$ the stopped head table collecting a
largest late class forces $\mu-t=d$ for every fixed-total competitor.
It matches the constructed upper bound. All zero and equality cases
allowed by (207.19) are included; this theorem assumes $m\ge2$.
$\square$

**Example 207.9 (A growing family below named stock tests).** For every
$m\ge3$, put $L=m+2$, $k=\lceil(m+1)/2\rceil$ and

$$
h=\frac1{2k},\quad \mu=2+\frac2k,\quad a=1+\frac3{2k},\quad
S=4+\frac4k,\quad t=1+\frac2k,\quad
\gamma_1=\gamma_2=h,\quad\gamma_j=\mu\ (j\ge3).
\tag{207.23}
$$

Use the measure and early rows of 207.8. Its empty-subset surplus is
$S-c_ma=3/k^2$. Define input $y$ by putting late $C=\mu$ solely at
$w(\{j\})$; define $V$ by replacing this with $a$ at the singleton
and $\mu-a$ at the absorbing suffix. Both have $E=1/k$ and
$W=5+7/k$. Every pair cylinder is $(a,a,a,1-h)$ and
$2a-\mu=1/k$.

The empty and late-single supports are $W-2h$, and each early-single
support is $W-h$. Head and early/late pairs have support $W+1$.
For $y$, late-pair $N$ maxima are $(a,\mu,\mu,\mu)$ and stopped
maxima are $(2a,\mu,\mu)$; hence its costs are $(2+h,1)$.
For $V$, late-pair maxima are $(a,a,\mu,\mu)$ when $j<L$ and
$(a,a,\mu,2+3h)$ when $j=L$, with excesses $1$ and $1-h$.
Their first two maxima merge without loss, so $V$ has costs $(1,1)$.
All these formulas follow by the label classification in 207.8; no
restriction on a queried label replaces maximization over all labels.

For $m\ge4$, the aggregate threshold of 205.10 at $d=1$ is
$5+8/k$, exceeding $W$ by $1/k$; decreasing $d$ raises that threshold.
At $m=3$ this supplier is outside its stated domain, so evaluating its
formula there is not an application of the theorem. The actual 203.2
test has $\kappa=1+h,\pi=1$. The 205.9 positive-cell test has
$\zeta=1-h$ and $D\ge1+h$. The fair unit threshold is
$5+10/k>W$.

The following comparisons include the whole indicated parameter
families from §206. In its balanced-fair family, let $u$ be the largest
retained late total, $c_1,c_2$ the early totals, $D$ the score cost and
$\theta$ its nonnegative residual charge. The complete fair support
and the $u_3$ residual give

$$
D\ge\frac{u-\min c_a}{2},\quad
\theta\ge\frac{\mu-\eta_3-E+c_1+c_2}{2},\quad
D+\theta\ge\frac{\mu-E+u-\eta_3+\max c_a}{2}
\ge1+\frac1{2k}>1.
\tag{207.24}
$$

For its clipped-fair test with scale in $[0,1]$, the $u_3$ condition
would force $\mu-E\le2$, whereas here $\mu-E=2+1/k$. In the
coupled-stock test, if $d'\le1$ and
$c=\max(0,2(u-d')-S/2)\le E$, then
$u\le1+d'+3/(2k)$. The function $3(\mu-u)-E+c$ decreases in $u$
and at this largest permitted value is $3(1-d'+h)$. The last-prefix
residual thus obeys, for $A_m=3m/(m+3)>1$,

$$
\theta\ge A_m(1-d'+h),\qquad
d'+\theta\ge1+A_mh>1.
\tag{207.25}
$$

These are failures of those named ansatzes, not failures of $E_N$.
At $h=0$, 207.8 reuses the corresponding correlated mechanism wherever
its earlier stated domain applies; no disjointness is asserted.

### 207.3 Global Boolean realization and sharp protected stock

**Proposition 207.10 (Integer moment cuts).** Let $\nu$ be an actual
finite nonnegative measure on Boolean variables $Z_i\in\{0,1\}$, with
$S=\int1$, $m_i=\int Z_i$, $q_{ij}=\int Z_iZ_j$. For all integers
$a_i,r$,

$$
\sum_i a_i^2m_i+2\sum_{i<j}a_ia_jq_{ij}
 -(2r+1)\sum_i a_im_i+r(r+1)S\ge0.
\tag{207.26}
$$

**Proof.** $U=\sum_i a_iZ_i$ is integer at each atom. Hence
$(U-r)(U-r-1)\ge0$ pointwise. Integrate and expand using $Z_i^2=Z_i$.
The same argument applies separately to each nonnegative event or
first-zero measure and to every projection. These are necessary cuts,
not a sufficient characterization of the Boolean moment cone. $\square$

**Theorem 207.11 (Consistent proper marginals and PSD do not suffice).**
For even $h=2q\ge4$ and $s>0$, prescribe

$$
S_0=\frac{4hs}{h+1},\qquad m_i=2s,\qquad q_{ij}=s.
\tag{207.27}
$$

All pair tables are nonnegative, the augmented degree-two moment matrix
is positive semidefinite, and there are mutually consistent genuine
laws on every proper subset. Nevertheless no measure on all $h$ bits
has these moments.

**Proof.** In indicator order $00,01,10,11$, each pair table is
$(S_0-3s,s,s,s)$, nonnegative for $h\ge4$. The augmented matrix has
upper-left entry $S_0$, cross vector $2s\mathbf1$ and lower block
$s(I+J)$, where $J=\mathbf1\mathbf1^\mathsf T$. Its Schur complement is

$$
s(I+J)-\frac{4s^2}{S_0}J=s(I-J/h)\succeq0.
\tag{207.28}
$$

On $h-1$ bits choose a subset uniformly conditional on its cardinality
$K$, where

$$
\begin{array}{c|ccc}
K&q-1&q&q+1\\\hline
\mathsf P(K)&1/8+1/(4h)&3/4&1/8-1/(4h).
\end{array}
\tag{207.29}
$$

These nonnegative probabilities sum to one. Direct summation yields

$$
\mathsf EK=q-\frac1{2h},\qquad
\mathsf E[K(K-1)]=\frac{(h-1)(h-2)(h+1)}{4h}.
\tag{207.30}
$$

Dividing by $h-1$ and $(h-1)(h-2)$ gives one- and two-bit means
$(h+1)/(2h)$ and $(h+1)/(4h)$. Scaling by $S_0$ yields $2s,s$.
Give each proper subset the corresponding marginal of this exchangeable
$(h-1)$-bit law. Exchangeability makes the assignment independent of
its embedding, and further projections agree on every intersection.
Thus entire proper-subset laws, not just their pair moments, agree.

A full measure would instead have, for $K=\sum_{i=1}^hZ_i$ under
$\nu/S_0$,

$$
\mathsf EK=\frac{h+1}{2}=q+\frac12,\qquad
\mathsf EK^2=\frac{(h+1)^2}{4}.
\tag{207.31}
$$

Variance zero would make the integer $K$ equal to a half-integer almost
surely, a contradiction. Equivalently (207.26) with every $a_i=1,r=q$
has value $-S_0/4<0$. Adjoining a forced-zero terminal and splitting
early lifts cannot supply a missing full pair measure. This example
refutes the local/PSD gluing implication; it is not an actual input
score, a certificate nonmember or an acquisition counterexample.
At $s=0$ the zero measure is realizable and the obstruction vanishes.
$\square$

**Definition 207.12 (Protected shared-terminal class).** Fix $h\ge2$
actual late internal addresses $I$ and an actual address $z>\max I$,
with $L\ge z$, and $s>0$. Put correct mass $s$ at $w(\{j,z\})$ for
each $j\in I\cup\{z\}$, interpreting $\{z,z\}=\{z\}$. Put no other
late correct or base mass. For one measure $\nu$ on subsets of $I$,
put pair mass $\nu(Z)/2$ at each

$$
w(\{1,z\}\cup Z),\qquad w(\{2,z\}\cup Z).
\tag{207.32}
$$

Put $T=\tau\ge0$, and allow arbitrary early correct rows with prescribed
totals and total $E$. Inactive coordinates are one on the specified
core. Protection means that, after removing early correct rows, in
every non-$11$ cell of every distinct $N$ pair, every late-label reward
is at most the label-zero pair reward.

**Theorem 207.13 (Sharp protected stock and its complete cost).** Write
$m_i=\nu(i\in Z)$, $d_{ij}=\nu(i\notin Z,j\in Z)$ for ordered
distinct $i,j\in I$. Protection is equivalent to

$$
m_i\ge2s\quad(i\in I),\qquad d_{ij}\ge s\quad(i\ne j).
\tag{207.33}
$$

The least possible stock is

$$
S_* =s\left(4-\frac2{\lceil(h+1)/2\rceil}\right).
\tag{207.34}
$$

Every protected score has $\Delta_N=\Delta_O=(s-\tau)_+$, regardless
of its early correct placements. At fixed exact $B=S+\tau$, the class
is empty for $B<S_*$; otherwise its attained minimum cost is
$(s-B+S_*)_+$. It has a score of cost at most $d\ge0$ exactly when

$$
B\ge S_*+(s-d)_+.
\tag{207.35}
$$

**Proof.** On an early/internal pair, cell $10$ has class $i$ reward
$s$ and pair capacity $m_i/2$, forcing the unary inequality. An
internal pair has class $i$ in $01$ and class $j$ in $10$, each of
weight $s$, forcing both directed inequalities. Conversely those
directed inequalities cover the only nonzero non-$11$ late rewards
of internal pairs. On $(i,z)$, cell $00$ has capacity $m_i\ge2s$,
and cell $10$ has capacity $S-m_i\ge d_{ij}\ge s$ for any other
internal $j$; every correct label has weight at most $s$. On early/$i$
use $m_i/2\ge s$, and on early/$z$ use $S/2\ge s$. The head pair
has late rewards only in $11$. Inactive coordinates yield singleton
or constant information: an internal zero cell has capacity $m_i$,
an early zero cell contains no late correct mass, and a terminal zero
cell has capacity $S$. Thus they too satisfy protection. Early labels
collect only subsets of pair mass. This proves the equivalence for all
cells and labels.

Set $K=|Z|$. Summing the unary and ordered directed inequalities gives

$$
\int K\ge2hs,\qquad\int K(h-K)\ge h(h-1)s.
\tag{207.36}
$$

For $h=2q-1$, $K(h-K)\le q(q-1)$, giving $S\ge2hs/q$. For
$h=2q$, integer $K$ satisfies $(K-q)(K-q-1)\ge0$, or
$K(h-K)\le q(q+1)-K$. Integration yields

$$
q(q+1)S\ge h(h-1)s+2hs,
\qquad S\ge\frac{2(2q+1)s}{q+1}.
\tag{207.37}
$$

These are exactly (207.34) in the two parities. The already supplied
measure $\mathcal L_h(s)$ attains all unary $2s$ and directed $s$
capacities and total $S_*$. Extra stock at the empty subset preserves
protection. This attainment reuses 201.2; the necessary stock bound
does not assert optimality outside the declared protected class.

In a complete core table every non-$11$ maximum equals its pair
baseline; in $11$ a late label earns at most $s$, whereas zero earns
its pair mass plus $\tau$. The core excess is at most $(s-\tau)_+$.
Restoring early correct rows increases any fixed table by at most $E$
and the anchor by exactly $E$. The stopped head table with exhaustion
label zero or $z$ attains $E+S+\max(\tau,s)$, so both costs equal
$(s-\tau)_+$. At fixed $B$, $\tau=B-S$ and $S\ge S_*$; minimizing
$(s-B+S)_+$ gives the attained value at $S=S_*$. Combining this with
$B\ge S_*$ gives (207.35). All equalities, $d=0$ and $\tau=0$ are
included. Early $E$ is retained and cannot replace any of this $B$.
$\square$

**Corollary 207.14 (The exact protected-class relaxation loss).** For
even $h\ge4$, let

$$
g_h=S_*-S_0=\frac{4s}{(h+1)(h+2)}>0.
\tag{207.38}
$$

If $s\ge d\ge0$ and $s-d\ge g_h$, fix $B=S_0+s-d$. The impossible
local/PSD data (207.27) with $T=s-d$ report protected-cell cost $d$.
Every actual protected score at this same $B$ has cost at least
$d+g_h$, attained by $\mathcal L_h(s)$ and $T=s-d-g_h$.

**Proof.** The difference in (207.38) follows by subtraction. Actual
stock at least $S_*$ forces $T\le B-S_*=s-d-g_h$, and the head
table forces cost at least $s-T\ge d+g_h$. Theorem 207.13 attains it.
The stock increase is paid once by lowering $T$. Adding it to pair mass
while keeping $T$ would change $K,Q$ and require residual accounting.
This is a restricted-class relaxation gap, not a lower bound against
all full-score representatives. $\square$

**Example 207.15 (Exact rational stock loss).** Take $I=\{3,4,5,6\}$,
$z=L=7$, $h=4,s=2,d=1$. Put $\nu(Z)=2/3$ on each of the six
two-subsets and four three-subsets of $I$. Thus each corresponding
early pair word in (207.32) has weight $1/3$. Put $C=2$ at
$w(\{j,7\})$ for $j=3,\ldots,7$, no early correct rows, and
$T=11/15$. Then

$$
S_*=20/3,\qquad S_0=32/5,\qquad B=W=37/5,
\qquad g_4=4/15,\qquad\Delta_N=\Delta_O=19/15.
\tag{207.39}
$$

Every empty or singleton support is $W$. The head maxima are
$(0,10/3,10/3,2)$ with support $26/3$; internal/internal maxima are
$(2,2,2,2)$ with support $8$ and excess $3/5$. The stopped versions
merge the first two entries without loss. Early/internal, early/terminal
and internal/terminal supports equal $W$: their $11$ baselines also
cover all correct labels. These exhaust the pair types.

For the false relaxed data, a proper three-bit measure assigns weight
$2/5$ to each singleton, $8/5$ to each two-subset and $2/5$ to the
triple. It has total $32/5$, unary masses $4$ and pair intersections
$2$, and its further projections agree. Yet the full four-bit integer
cut is $-S_0/4=-8/5$. The relaxed $T=1$ would report cost one at
the same $B$, while no full pair measure realizes it. Arbitrary early
correct additions preserve the actual exact cost $19/15$ by 207.13.

### 207.4 Exact low-tail comparison with one actual equal-cylinder measure

**Definition 207.16 (Full fixed data).** Fix $L\ge4$,
$J=\{3,\ldots,L\}$, $m=L-2$, $s>0$ and $3\le c\le4$. Stipulate
one actual measure $\nu$ on subsets of $J$, of total $cs$, unary
zero masses $2s$, and directed masses
$\nu(i\notin Z,j\in Z)=s$ for $i<j$. Equal unary masses give the
opposite directed masses too; each answer pair therefore has cells
$(s,s,s,z)$, where $z=(c-3)s$. Existence of this measure is a premise;
arbitrary $c\in[3,4]$ is not presumed realizable at every length.

Choose $r_j\in[0,s]$ in arbitrary order, set $\gamma_j=s+r_j$,
$T=s$ and $E=0$. The fixed-data competitors are all $A=0$/early-pair
scores with these late totals, this entire late pair projection $\nu$
and this $T$. Their correct suffixes and early pair allocations,
including prefix $00$, are unrestricted. In particular the projection
is $P_{00x}+P_{01x}+P_{10x}$, not just the last two summands. Define

$$
\begin{aligned}
b_*&=(c-2)s/2,\qquad R_j=\max(\{r_n:n>j\}\cup\{0\}),
\qquad r_{\max}=\max_jr_j,\\
D&=\max\left\{r_{\max},\
 \max_{j\ge3}[r_j+(R_j-b_*)_+],\
 \max_{j\ge4}[r_j+(R_j-z)_+]\right\}.
\end{aligned}
\tag{207.40}
$$

**Theorem 207.17 (Attained full fixed-data minima).** Both complete
excesses have attained minimum $D$ over the class of 207.16. An
attaining score $V$ is the threshold placement supplied by 203.2:
put $P=\nu(Z)/2$ at each $w(\{a\}\cup Z)$, $a=1,2$, put $C=s$
at $w(\{j\})$ and $C=r_j$ at $w(\{j,\ldots,L\})$ for every late
$j$, and put $T=s$. It preserves $Q$, the anchor $W=(c+1)s$ and
the entire $\nu$, and $\Delta_N(V)=\Delta_O(V)=D$.

Every unit-$O$ input in this $E=0$ fixed-data class therefore has the
same-$Q$ certificate $(V,0)$. After arbitrary early correct rows are
added to both input and representative, $Q$ is still preserved and
$\Delta_N(V)\le D$; this gives a certificate when $D\le1$. A
fixed-data minimum and an automatic implication from unit-$O$ input to
$D\le1$ are asserted only at $E=0$. If $D=r_{\max}$, the head table
still attains $D$ after arbitrary early additions.

**Proof.** The threshold cutoffs of 203.2 are all
$\nu(n\in Z,k\notin Z)=s$, so its full words are exactly the two
correct words just specified. They have the declared first zero and
the correct totals, including coincident terminal words.

The complete cell maxima of $V$ are

| Schedule | $N$ maxima in order $00,01,10,11$ |
| --- | --- |
| $(1,2)$ | $(0,cs/2,cs/2,s+r_{\max})$ |
| early/late $(a,j)$ | $(s,b_*,s+r_j,s+\max(b_*,R_j))$ |
| late/late $i<j$ | $(s,s,s+r_j,s+\max(z,R_j))$ |

For an early/late pair, its early-zero cells contain only pair rewards.
In $10$, class $j$ supplies $s+r_j$; earlier absorbing residuals are
at most $s$ and future classes do not occur. In $11$, earlier
singleton contributions are at most $s$, future classes have maximum
$s+R_j$, and zero gives $s+b_*$. For late $i<j$, every correct
contribution in $00$ is an absorbing residual at most $s$. In $01$
only class $i$ can contribute its singleton mass $s$. In $10$, class
$j$ supplies $s+r_j$ and intermediate residuals are at most $s$.
In $11$, earlier singletons are at most $s$, future classes supply
$s+R_j$, and zero gives $s+z$. Early labels collect subsets of pair
mass. This proves the table over all labels, including earlier and
unqueried ones. Its three excess formulas are exactly the three
families in (207.40); each $j\ge4$ occurs as the second late query.
Catalog completion gives $\Delta_N(V)=D$.

For any fixed-data competitor, the stopped head table forces
$r_{\max}$. Start a late pair $i<j$ with label zero on all stopped
cells, whose reward is the anchor $W=cs+s$. Independently switch $10$
to label $j$ and $11$ to a largest future class whenever beneficial.
These classes lie wholly in their respective cells for any correct
suffixes. The two gains in one table sum to
$r_j+(R_j-z)_+$ (omit the future switch if there is no future class).
Thus every such $O$ cost is at least the third family in (207.40).

For early/late $(a,j)$ set
$p_{a0}=P\{w_a=1,w_j=0\}$, $p_{a1}=P\{w_a=1,w_j=1\}$.
The two loss sets for $a=1,2$ are disjoint on early pair support,
even for atoms with prefix $00$. Hence

$$
p_{10}+p_{20}\le2s,\qquad
p_{11}+p_{21}\le(c-2)s=2b_*.
\tag{207.41}
$$

The stopped table independently switching $10$ to $j$ and $11$ to
a largest future class has gain at least

$$
f(p_{a0},p_{a1})=(s+r_j-p_{a0})_++(R_j-p_{a1})_+.
\tag{207.42}
$$

When no future class exists the second summand is zero. The function
$f$ is convex and decreasing in each capacity. The maximum of the two
legal schedule gains is at least their average, which by convexity
and (207.41) is at least
$f(s,b_*)=r_j+(R_j-b_*)_+$. This bounds a maximum of two whole
tables; it does not average their requests into a new acquisition.
All entries of $D$ therefore lower-bound every fixed-data $O$ cost.
Apply this to $V$ and use $B_O\le B_N$ to obtain both equalities and
both attained minima. Equality of $Q$ gives zero residual.

Adding early correct rows raises a fixed table by at most their total
$E$ and the anchor by $E$, proving the sufficient extension. The head
table retains all of them, giving the claimed exactness when
$D=r_{\max}$. Ties, $r_j=0,s$, $D=1$, and $c=3,4$ whenever the
stipulated measure exists are included. At the separate $s=0$ limit,
the late, pair and $T$ score is zero and $D=0$. These auxiliary zero
endpoints do not replace positive original amplitude tails. $\square$

**Corollary 207.18 (A dense family at every growing length).** For
every $m=L-2\ge4$, set $c=4-2/\lceil(m+1)/2\rceil$, use
$\nu=\mathcal L_m(s)$, and choose

$$
\frac2{c-2}\le s<\frac1{c-3},\qquad
r_3=r_4=1,\qquad 0\le r_j\le z=(c-3)s\quad(j\ge5).
\tag{207.43}
$$

Then $D=1$. The threshold representative has both costs one, also
after arbitrary early correct additions. With $E=0$, the input that
has the same pair rows and $T$ but places all $C_j=s+r_j$ at the
singleton $w(\{j\})$ has costs $(\Delta_N,\Delta_O)=(2,1)$.

**Proof.** $3<c<4$, so the interval is nonempty. It gives $s\ge1$,
$b_*\ge1$ and $z<1$. Now $R_3=1\le b_*$ and every $R_j$ for
$j\ge4$ is at most $z$. Thus all terms of (207.40) are at most one
and $r_{\max}=1$ attains it. The head-table equality also preserves
the representative's cost after early additions.

For the singleton input, empty and all single supports equal
$W=(c+1)s$: zero marginals $2s$ dominate every $\gamma_j\le2s$,
and the positive baseline $(c-1)s$ dominates each late total. Head
excess is one. An early/late excess is
$r_j+(\max_{n\ne j}r_n-b_*)_+\le1$. A late pair has $N$ maxima

$$
\bigl(s,s+r_i,s+r_j,s+\max(z,\max_{n\notin\{i,j\}}r_n)\bigr),
\tag{207.44}
$$

so its $N$ excess is $r_i+r_j+(\max_{n\notin\{i,j\}}r_n-z)_+$.
Its stopped first cell has maximum $2s$ because $r_i\le s$, giving
$O$ excess $r_j+(\max_{n\notin\{i,j\}}r_n-z)_+$. If both heavy
classes $3,4$ are queried these are two and one. If exactly one is
queried and another heavy class remains, $j$ is nonheavy, so
$r_j\le z$ bounds the $O$ excess by one and the $N$ excess by two.
If neither is queried, $N\le1+z<2$ and $O\le1$. This proves the
complete costs, including shorter schedules. The exact input $N$ cost
two is an $E=0$ claim; early additions may reduce it.

At the upper endpoint $s=1/(c-3)$, allow all other $r_j\in[0,1]$.
Then $z=1$, $b_*\ge1$, all extra positive parts vanish, and the same
representative still has costs $(1,1)$ while the $E=0$ singleton input
has costs $(2,1)$. This endpoint is already within 205.8's positive-cell
protection, with $\zeta=\pi=1$, and within the aggregate supply of
205.10. The strict upper inequality in (207.43) excludes it only from
that strict comparison, not from the exact theorem. $\square$

**Example 207.19 (A rational dense profile and precise overlap).** Take

$$
L=8,\quad m=6,\quad c=7/2,\quad s=9/5,\quad
r_3=r_4=1,\quad r_5=\cdots=r_8=9/10.
\tag{207.45}
$$

Put $\nu(Z)=9/50$ on each three- or four-subset of $\{3,\ldots,8\}$,
so all 70 early pair rows have weight $9/100$. The singleton input
has $C=14/5$ at $w(\{3\}),w(\{4\})$, $C=27/10$ at each
$w(\{j\})$, $5\le j\le8$, and $T=9/5$. The representative puts
$9/5$ at each singleton and the corresponding residual $1$ or $9/10$
at the absorbing suffix. Thus

$$
S=63/10,\quad W=81/10,\quad G=82/5,\quad K=49/2,
\quad z=9/10,\quad b_*=27/20.
\tag{207.46}
$$

At $(3,4)$ the input maxima are $(9/5,14/5,14/5,27/10)$ with sum
$101/10$, and the representative maxima are
$(9/5,9/5,14/5,27/10)$ with sum $91/10$. Both stopped maxima are
$(18/5,14/5,27/10)$ with sum $91/10$. Formulas (207.40) and (207.44)
give all other schedules and prove the exact costs $(2,1)$ and $(1,1)$.

Here are comparisons with specific earlier families, using their stated
domains and the signed residual (207.8).

1. The actual 203.2 test has $\kappa=\pi=1$, so its sum is two;
   its protected-tail exact-minimum clause does not apply since
   $t<\mu=14/5$. The 205.9 positive-cell completion has
   $\zeta=9/10$, added tail $1/10$, $D=1$ and residual charge
   $(2/3)(1/10)$, totaling $16/15$. In 205.10, the least threshold
   for $d\le1$ occurs at $d=1$, and equals
   $\max((c+1)s,3s+\mu)=41/5>81/10$.

2. The fixed-projection zero core retains at most $s$ per class and
   has $v_4$ residual at least $6/5$. More generally, on the declared
   scaled zero-core ray with common capacity $x$ and
   $W'\ge(c+1)x$, retained late totals are at most $x$. If $x\ge s$,
   (207.8) gives a $v_4$ reading at least $3x/5+3/25\ge6/5$.
   If $x<s$, put $a=s-x$. Even at maximal retained totals $x$,
   $u_8\le1$ requires $a\le7/30$, while $v_4\le1$ requires
   $a\ge1/3$. Indeed these two lower readings are
   $4/5+6a/7$ and $6/5-3a/5$. Smaller retained totals or extra
   stock only increase these bounds. This excludes that scaled ray.

3. Consider the entire single-zero core family of 202.4, including
   arbitrary retained $\eta,p$, pair reserve $h$, terminal reserve
   $\tau$ and signed residual. Put $B'=\sum p+h+\tau$, let its cost be at most
   $d=1-\theta$, and set $u_j=(\eta_j-p_j)_+$. Its exact formula
   in 202.10 gives $u_i+u_j\le d$ for every pair, hence
   $\sum\eta_j\le\sum p_j+3d\le B'+3d$. The $u_8$ residual
   forces $\sum\eta_j\ge82/5-7\theta$, giving
   $B'\ge67/5-4\theta\ge47/5$. The $v_8$ residual, together
   with the same upper bound on retained totals, forces

   $$
   3(82/5)-3B'-9d\le6(81/10-B')+9\theta.
   \tag{207.47}
   $$

   Since $d+\theta=1$, this gives $B'\le14/5$, a contradiction.
   Thus no parameter choice in that named family has budget one.

4. In 201.3, $\Lambda=(10/3)(27/10)+3(1/10)=93/10$, and the
   unit threshold is $\Lambda+\mu-1=111/10$. The displayed threshold
   of 202.3 is $G+(\mu-1)+(\mu-2)=19$. For 202.6 the two largest
   totals sum to $M_2=28/5$, giving
   $\mu+(1-1/M_2)\Lambda=2923/280$. Each exceeds
   $81/10$. The 202.8 internal remainder $109/10$ exceeds
   $2\mu=28/5$; 202.11's five-label premise does not include these
   six positive late classes. The 203.6 fair threshold is
   $5(\mu-1)=9>81/10$. In the 203.4 product family the heavy
   labels are both internal and $u\le81/20$. Their two non-$11$
   deficits are at least
   $2\mu(2\mu/u-1)\ge868/405>1$.

5. Terminal-maximum and nondecreasing-profile premises fail since the
   last total is $27/10<14/5$. The conditional shared-terminal
   supplier also requires a forced-zero last bit, whereas
   $\nu(x_8=1)=27/10$. One- or two-active-class results do not
   apply. Zero score fails at $u_3$ with value $7/5$. Neither the
   singleton input nor the threshold representative has the common
   Markov suffix relation of 198.2: conditional on bit 3 zero, the
   input's correct class 3 has bit 4 always one while the pair
   class has bit 4 zero with probability $1/2$; in the
   representative, correct class 3 conditional on bit 4 zero has
   bit 5 zero with probability one, while the pair measure conditional
   on bit 4 zero has bit 5 zero with probability $1/2$.

6. The §206 chain parameter is $q=\max(\mu,2\mu-t)=19/5$, so
   its exact cost contains $q-E>1$. A clipped-fair test would require
   $\gamma_3\le2$ at $u_3$, which fails. In its coupled-stock
   family $E=0$ forces $u\le d+63/40$; the $v_4$ residual gives
   $\theta\ge6(\mu-u)/5$. Consequently

   $$
   d+\theta\ge147/100-d/5\ge127/100>1\quad(0\le d\le1).
   \tag{207.48}
   $$

   For the entire balanced-fair family, (207.24)'s argument with
   $E=0$ gives $D+\theta\ge\gamma_3/2=7/5>1$, independently
   of retained totals, early masses and $W'$.

The thresholds in item 4 are substitutions into the owning suppliers,
not new minima. In particular the comparison is not separation from
all consequences, mixtures or closures of earlier constructions.

**Proposition 207.20 (Original necessary bound by existing transport).**
For either original class attaining a closed cap $\varepsilon>0$, the
representative of 207.17 yields the necessary condition

$$
\sum_{j=3}^L\gamma_j a_j
 \le D+\bigl(G+(c+1)s\bigr)\varepsilon.
\tag{207.49}
$$

At (207.45) this reads

$$
28(a_3+a_4)+27(a_5+a_6+a_7+a_8)\le10+245\varepsilon.
\tag{207.50}
$$

**Proof.** The ordinary full support bound is $B_N=W+D$, while the
target event score is $W+\sum\gamma_ja_j-K\varepsilon$, with
$W=(c+1)s$, $K=G+W$. Multiplying all independent event demands by
their nonnegative score weights and comparing gives (207.49). This
finite inequality requires no membership in $H_L$.

For arbitrary original active length, reuse the finite-prefix argument
of 137.1 together with 110.2. If the transported active length exceeds
$L$, restrict its later replies to zero and project output labels
greater than $L$ to zero. The full low-word event bounds remain and
constant high replies can be composed into each finite table. This is
an algebraic restriction of the representation, not an uncounted source
observation. If active length is smaller than $L$, ignore new input
coordinates; their positive amplitudes are at most $\varepsilon$,
and the exact tail identity below supplies their TV bounds. Thus all
low words, including multiple zeros, and the positive word satisfy the
finite comparison. For $\varepsilon\ge1$ the inequality is immediate
from $a_j\le1$ and $K\ge G$. Containment of stopped laws in
preselected laws uses 90.2 with the same seed and hard count. The
rational substitution multiplies (207.49) by ten, giving (207.50).
These are necessary conditions only. $\square$

**Scope, transport and remaining comparison.** The constructions above
use actual joint Boolean measures for their scores. Proper marginals,
PSD matrices, separate optimizers and a score-maximizing deterministic
table do not supply a feasible acquisition probability law. The subset
atoms remain those of [201.2](KBONACCI_SELF_CALIBRATING_ACQUISITION_RESOURCES_CONTINUATION_VI.md),
the threshold placement remains that of
[203.2](KBONACCI_SELF_CALIBRATING_ACQUISITION_RESOURCES_CONTINUATION_VII.md),
and the hull/certificate remains that of 198.5 and 199.3–199.4.
The additional assertions here are their stated retained-credit bounds,
the global nonextendibility and protected-stock necessity, and the
simultaneous low-tail fixed-data minima. Integer moment cuts and the
distinction between a Boolean moment cone and its PSD relaxation are
ordinary classical methods. No external priority or exhaustive overlap
claim is needed for these proofs.

For actual normalized feasible finite probability configurations,
Theorem 110.2 supplies the original acquisition transport. Its necessity
projects arbitrary full-carrier tapes measurably to the finite marks;
countability gives a common full-measure seed event of finite handoff
and at most two requests. A common seed event controls the maximum
address of the whole preselected schedule. Actual finite-word witnesses
are fixed before the seed, sourcewise finite handoff supplies a cutoff
for each finite witness family, and compactness of the finite catalog
simplex preserves the closed cap. These steps retain arbitrary-address
competitors; a fixed finite calculation alone would not do so.

For sufficiency, one $U\sim\operatorname{Unif}[0,1)$ chooses the entire
schedule and terminal table by a fixed interval partition before any
reply. The actual prime queries and original output marks give finite
handoff. Two finite class configurations can use this same $U$ by a
common refinement of their partitions; seedwise equality of their outputs
is not required. This realizes probability configurations, not the score
weights used here. All-word and independent pair demands remain (207.3).
For every actual source with $n>L_a$, the exact transported error is

$$
\operatorname{TV}\left(\sum_{j=0}^{L_a}p_{1^{L_a}}(j)\delta_{\theta_j},
 (1-a_n)\delta_{\theta_0}+a_n\delta_{\theta_n}\right)
 =\max\{1-p_{1^{L_a}}(0),a_n\}\le\varepsilon.
\tag{207.51}
$$

This includes $a_n=\varepsilon$ and all actual positive tails. The
finite positive word is not an infinite all-positive source. Small
active lengths and the cap-one endpoint retain their existing transport;
auxiliary hull endpoints with $e=0$ do not alter (207.2).

The entire all-$L$, $A=0$/early-pair, arbitrary-correct, low-$T$
unit-excess inclusion is still unresolved. The fixed-total and fixed-data
minima above have exactly their declared scopes; the protected-class
necessity does not become a universal lower certificate, and the
nonextendible data are not an actual input. In the notation of 199,
the universal relation $\rho_O(b)\le\max\{1,\rho_N(b)\}$ and, for
every original sequence and every positive closed cap,

$$
\mathcal F_N(a,\varepsilon)\ne\varnothing
\quad\Longrightarrow\quad
\mathcal F_N(a,\varepsilon)\cap\mathscr C_{L_a}\ne\varnothing
\tag{207.52}
$$

remain open. A strict separator would require one compatible $b\in H_L$,
an actual full $y\ge0$ with $\Delta_O(y)\le1$, and an attained
$\lambda\ge0$ satisfying all complete rows $G_N\lambda\ge h(b)$,
mass $M=\sum_D\lambda_D\ge1$, and $F_{Q(y)}(b)>M$, followed by
the existing normalization
and original-source transport. No such attainer or uniform lower bound
against every original $O_2$ competitor is supplied here. The remaining
question is whether one common realizable full-row construction, with
early credit charged once, covers the omitted unit inputs, or whether
an actual full-budget separator exists.

## 追加锚（本行以下为增补区）
