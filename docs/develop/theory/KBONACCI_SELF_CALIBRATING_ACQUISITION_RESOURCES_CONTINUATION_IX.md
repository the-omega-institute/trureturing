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

## 208. Actual ordered-event bounds and changed-carrier stock minima

**Definition 208.1 (Input measures and the unchanged comparison).**
Use the original source, resources, complete scores, catalogs, quotient
and one-budget certificate of Definitions 207.1–207.3. In particular,
$L\ge3$, $A=0$, $P$ is supported on $\Omega_1\cup\Omega_2$, and
the correct rows are arbitrary. Write

$$
c_a=\gamma_a,\quad p_a=\sum_{\Omega_a}P_w\quad(a=1,2),\qquad
E=c_1+c_2,\quad S=p_1+p_2,\quad T=t,\quad W=E+S+t,
\qquad \delta=\Delta_O(y).
\tag{208.1}
$$

The actual late-bit measure, of mass $S$, is

$$
\nu(x)=P_{00x}+P_{01x}+P_{10x},\qquad
Z_j=\{x:x_j=0\},\quad m_j=\nu(Z_j),\quad
d_{ij}=\nu(Z_j\setminus Z_i)\quad(3\le i<j\le L).
\tag{208.2}
$$

Thus prefix $00$ is included. The late totals $\gamma_j$ need not
be ordered, and $t$ may be zero. All finite words, all labels, the
independent pair row and negative singleton demands remain as in
(207.3)–(207.4), even when their score coefficients are zero.
The measures here are nonnegative proof weights. Their normalizations
are not laws on the original sources or acquisitions.

Fixed-total families below retain their specified correct totals and
stock variables, while allowing every joint placement consistent with
the input shape. A replacement may change $\nu$, the early pair split
and unary correct marginals unless a theorem explicitly fixes them.
The certificate still consists of one full score and one residual
charge in (207.9); it does not require preservation of these auxiliary
coordinates.

### 208.1 Marginal spread of the actual input

**Theorem 208.2 (All-threshold spread and joint stock bounds).** Set
$d=\delta+E$. For $s>0$ let
$J_s=\{j\ge3:\gamma_j\ge d+s\}$ and $m=|J_s|$. Define

$$
\chi_r=\frac{2\lfloor r^2/4\rfloor}{r(r-1)}\quad(r\ge2),\qquad
\Gamma_1=2,\qquad
\Gamma_m=\max\left\{3,\
 \max_{2\le r\le m}\frac{2(q+1)}{1+q\chi_r}\right\}\quad(m\ge2),
\quad q=\left\lfloor\frac{m-1}{r-1}\right\rfloor.
\tag{208.3}
$$

On the same actual measure (208.2),

$$
m_j\ge2s\quad(j\in J_s),\qquad
d_{ij}\ge s\quad(i<j,\ i,j\in J_s).
\tag{208.4}
$$

For any $r\ge2$ selected events, the range $R$ of their marginal
masses satisfies $R\ge2s-\chi_rS$. More generally, if $n\ge2$
selected marginal masses lie in an interval of length $R_0$, then

$$
R_0\ge q(2s-\chi_rS),\qquad
2\le r\le n,\quad q=\left\lfloor\frac{n-1}{r-1}\right\rfloor.
\tag{208.5}
$$

Consequently every input satisfies, simultaneously at every such
threshold,

$$
\begin{aligned}
t&\ge(\mu-\delta)_+,\qquad S\ge\Gamma_ms &&(m\ge1),\\
S+t&\ge4s+d &&(m\ge3),\\
(1+q\chi_r)S+t&\ge2(q+2)s+d
 &&\left(m\ge4,\ 2\le r\le m-2,\
 q=\left\lfloor\frac{m-3}{r-1}\right\rfloor\right).
\end{aligned}
\tag{208.6}
$$

These are necessary conditions on complete $O$ inputs, without
independence, exchangeability or a condition on a replacement measure.

**Proof.** Delete only the early correct rows, obtaining $y_c$.
Its support cannot increase and its anchor decreases by $E$, so
$\Delta_O(y_c)\le\delta+E=d$. Constant output zero on this score
earns $S+t$. For $a=1,2$, the legal stopped table $(a,j;0,j,0)$
changes only cell $10$ and gains

$$
\gamma_j-P\{w_a=1,w_j=0\}.
\tag{208.7}
$$

The two loss sets are disjoint on $\Omega_1\cup\Omega_2$ and their
union is contained in $Z_j$. Prefix $00$ belongs to neither loss
set. Hence $m_j\ge2(\gamma_j-d)_+$. The table
$(i,j;0,j,0)$ similarly gives $d_{ij}\ge(\gamma_j-d)_+$.
This proves (208.4), charging the deleted $E$ once.

For an original-order pair $i<j$ among $r$ selected events,

$$
\nu(Z_i\mathbin{\triangle}Z_j)
 =2\nu(Z_j\setminus Z_i)+m_i-m_j\ge2s-R.
\tag{208.8}
$$

At a point where exactly $k$ of the $r$ events occur, exactly
$k(r-k)\le\lfloor r^2/4\rfloor$ unordered pairs disagree.
Integrating on this one measure yields
$\binom r2(2s-R)\le S\lfloor r^2/4\rfloor$, proving the range
bound. This is the classical cut-count argument; see Robert Šámal,
[*Cubical coloring — fractional covering by cuts and semidefinite
programming*](https://arxiv.org/pdf/0911.2589v3), Lemma 2.1 and
Corollary 2.2, for the fractional-cut counting principle. Here its
inputs are the actual directed losses (208.7).

Sort only the $n$ numerical marginal masses. Take $q$ consecutive
blocks of $r$ numbers, consecutive blocks sharing one endpoint.
Their ranges telescope and each obeys (208.8), independently of the
original address order. Their total range is at most $R_0$, which
proves (208.5), also when its right side is negative. For all $m$
events the range is at most $S-2s$, so
$(1+q\chi_r)S\ge2(q+1)s$. If $m\ge2$, the disjoint sets
$Z_i$ and $Z_j\setminus Z_i$ also force $S\ge3s$; for $m=1$
use $S\ge2s$. This proves the $\Gamma_m$ bound. Sorting the
marginal numbers has not relabeled any query address.

In the original score, $(1,2;1,2,j_*)$ collects all $E+S$ and
$\mu=\gamma_{j_*}$, forcing $t\ge\mu-\delta$. For late $i<j<k$,
the one stopped table $(i,j;0,j,k)$ collects at least
$m_i+\gamma_j+\gamma_k$. Its exhaustion label $k$ is legal even
though unqueried. Thus

$$
m_i+\gamma_j+\gamma_k\le S+t+d.
\tag{208.9}
$$

Retain the first $m-2$ addresses of $J_s$ and use its last two
addresses as $j,k$. The retained marginal masses lie in
$[2s,S+t-2s-d]$. Nonemptiness gives the second line of (208.6).
For $m\ge4$, apply (208.5) to their range, at most $S+t-4s-d$,
and rearrange. No sum of separately attainable support gains occurs.
$\square$

**Theorem 208.3 (Dense restricted asymptotic minimum).** Fix $s>0$
and $0\le\delta_0\le s$. For $m\ge1$, let $S_m$ be the minimum
pair mass among all complete input-family scores on $L=m+2$ with

$$
E=0,\qquad \gamma_j=s+\delta_0\quad(3\le j\le L),\qquad
T=s,\qquad \Delta_O\le\delta_0.
\tag{208.10}
$$

All correct suffixes and actual joint early pair measures are free,
including early $00$. The minimum is attained and

$$
\Gamma_ms\le S_m\le4s,\qquad
\lim_{m\to\infty}S_m=4s,\qquad
\lim_{m\to\infty}(S_m+T)=5s.
\tag{208.11}
$$

**Proof.** The head table in 208.2 forces
$\Delta_O\ge\gamma_j-T=\delta_0$, so each feasible score has
exact excess $\delta_0$. Apply 208.2 with $d=\delta_0$.
For the upper witness, use the fair-suffix score of
[Theorem 203.6](KBONACCI_SELF_CALIBRATING_ACQUISITION_RESOURCES_CONTINUATION_VII.md)
with $\kappa_f=2s$ and terminal $s$. Its pair rows on $01x,10x$
each have weight $2s/2^m$; class $j$ is uniform on all of its
suffixes with total $s+\delta_0$. Its one actual product measure has
$S=4s$. Since every late total is at most $2s$, 203.6 gives both
complete excesses equal to $\delta_0$. That existing full-catalog
supplier provides the upper witness, rather than an assumption that
prescribed pair marginals can be glued.

Restrict the feasible set to $S\le4s$. At fixed $m$ it is a closed,
bounded set of finitely many nonnegative score coefficients: correct
totals and $T$ are fixed, and every table inequality is closed.
The set is nonempty by the witness, so $S$ attains its minimum.
Choose integers $r\to\infty$ with $r=o(m)$. Then
$q=\lfloor(m-1)/(r-1)\rfloor\to\infty$ and $\chi_r\to1/2$.
The corresponding ratio in (208.3) tends to four. Each ratio is
less than four since $\chi_r\ge1/2$, so $\Gamma_m\to4$ and
(208.11) follows. The endpoints $\delta_0=0,s$ are included.
This is an asymptotic minimum in (208.10), not an exact finite-$m$
formula or a minimum over arbitrary signed representatives.
The dense sufficient constructions of §206 and the fixed-projection
minima of 207.17 retain their different fixed-data scopes. $\square$

### 208.2 Ordered packing and strict affordability

**Theorem 208.4 (Actual-input ordered-event packing).** Suppose
$\Delta_O(y)\le d$. Select $m\ge2$ late addresses
$j_1<\cdots<j_m$ with $\gamma_j\ge g$, and put $s=g-E-d>0$.
For $3\le\tau<4$ define

$$
\begin{aligned}
a_\tau&=\frac{4-\tau}{\tau},&
n_\tau&=\max\left\{1,\left\lceil\frac{2(\tau-3)}{a_\tau}\right\rceil\right\},\\
w_\tau&=\frac{\tau-3}{n_\tau},&
\Pi(\tau)&=n_\tau\left\lfloor\frac1{a_\tau-w_\tau}\right\rfloor.
\end{aligned}
\tag{208.12}
$$

Then $S\ge3s$, $t\ge(\mu-d)_+$, and

$$
S\le\tau s\quad\Longrightarrow\quad m-1\le\Pi(\tau).
\tag{208.13}
$$

**Proof.** The actual losses in (208.7), using the bound $d$ for
the original excess, give $m_j\ge2s$ and $d_{ij}\ge s$ on the
selected addresses. The disjoint-union and terminal arguments of
208.2 give the first two assertions. Delete the largest selected
address and, for each remaining one, put $A_i=Z_i^c$ and
$r_i=\nu(A_i)/s$. Write $q=S/s\le\tau$. The outgoing directed
loss to the deleted address is at least $s$, whereas $m_i\ge2s$,
so

$$
1\le r_i\le q-2\le\tau-2,\qquad
\frac{\nu(A_i\cap A_j)}s
 =r_i-\frac{d_{ij}}s\le r_i-1\quad(i<j).
\tag{208.14}
$$

Partition $[1,\tau-2]$ into $n_\tau$ bins of width $w_\tau$,
assigning each endpoint to one bin. At $\tau=3$ this is one
singleton bin. In a bin with lower endpoint $r$ and $N$ events,
let $Z=\sum\mathbf1_{A_i}$ and integrate against $\nu/s$.
The marginal lower bound and the ordered intersection upper bound
give

$$
\int Z\ge Nr,\qquad
\int Z^2\le N(r+w_\tau)+N(N-1)(r+w_\tau-1)
 =N^2(r+w_\tau-1)+N.
\tag{208.15}
$$

Cauchy–Schwarz on a measure of mass $q\le\tau$ gives
$\int Z^2\ge N^2r^2/\tau$. Therefore

$$
N(1-r-w_\tau+r^2/\tau)\le1.
\tag{208.16}
$$

On $[1,\tau-2]$, $1-r+r^2/\tau$ is decreasing and is at least
$a_\tau$. The definition of $n_\tau$ gives
$0\le w_\tau\le a_\tau/2$, so the denominator is positive.
Each bin contains at most
$\lfloor1/(a_\tau-w_\tau)\rfloor$ events. Summing over bins
proves (208.13) for real, not just rational or integral, score
weights.

The threshold four in this dimension-free statement cannot be
increased. For any $s>0$, $0\le d\le s$, the existing fair witness
used in 208.3 has arbitrarily many late classes of weight $s+d$,
actual $m_j=2s$, $d_{ij}=s$, $S=4s$, $T=s$, and both excesses
$d$. This is a full score with one measure. It supplies no extension
of the finite packing bound to $\tau=4$. $\square$

**Theorem 208.5 (Strict packing implies fair-score affordability).**
Suppose $\Delta_O(y)\le d\le1$, $\mu\ge2$, and at least $m\ge2$
late classes have weight at least $g$. Put

$$
s=g-E-d>0,\qquad \tau=\frac{4\mu-5+d-E}{s}.
\tag{208.17}
$$

If either $\tau<3$, or $3\le\tau<4$ and $m-1>\Pi(\tau)$, then
$W>5(\mu-1)$. There is one full comparison score $V$ with

$$
\Delta_N(V)=\Delta_O(V)=1,\qquad
\sigma_H(Q(y)-Q(V))=0,
\tag{208.18}
$$

and therefore $Q(y)\in E_N$ with $\theta=0$.

**Proof.** If $W\le5(\mu-1)$, the actual terminal bound
$t\ge\mu-d$ gives $S\le4\mu-5+d-E=\tau s$. This contradicts
$S\ge3s$ when $\tau<3$, and otherwise contradicts 208.4.

Set $a=\mu-1\ge1$. Use the existing fair score of 203.6 with
$\kappa_f=2a$, all original late totals, zero early correct mass,
and $T_V=W-4a>a$. The second-largest late total is at most
$\mu=a+1\le2a$, as required there. Its exact excess is
$\max(0,\mu-a,\mu-T_V)=1$. Its correct total is $G$ and its
anchor is $W$, so it preserves $K=G+W$ and all late quotient
coordinates. The residual is

$$
F_{Q(y)-Q(V)}(b,e)=c_1(b_1-1)+c_2(b_2-1)\le0
\quad((b,e)\in H_L).
\tag{208.19}
$$

It equals zero at every $v_k$ of (207.7), hence its support charge
is zero. The single budget in (207.9) is exactly $1+0$.
The measure, all correct rows and terminal stock coexist in this
one score; no cell receives a separate budget.

For an explicit specialization of the input implication, take
$E=0,d=3/4,\mu=g=3$ and at least $68$ late classes of weight
three. Then

$$
s=9/4,\quad\tau=31/9,\quad a_\tau=5/31,\quad
n_\tau=6,\quad w_\tau=2/27,\quad
\Pi(\tau)=6\lfloor837/73\rfloor=66.
\tag{208.20}
$$

Thus $m-1\ge67$ forces $W>10$. This input class is nonempty at
every such length: the old fair witness has $S=9,T=9/4$ and
both excesses $3/4$, with $W=45/4$.
The certificate construction remains 203.6's supplier. The additional
implication is from the actual input to its affordability.

The strict condition $\tau<4$ is equivalently
$4(\mu-g)+3E+5d<5$. No conclusion at its critical equality, or
for arbitrary remaining profiles and early credit, follows from this
argument. In particular the critical $\tau=4$ affordability question
remains unresolved. $\square$

### 208.3 Relocating early support at fixed totals

**Definition 208.6 (Relocated carrier and ordered statistics).**
For nonnegative $c_1,c_2,p_1,p_2,\gamma_3,\ldots,\gamma_L,t$, let
$r_a=c_a+p_a$, $S=p_1+p_2$, $Z=E+S$, and $W=Z+t$.
For a multiset $D$, let $\operatorname{top}_k(D)$ be the sum of its
$k$ largest entries, padding with zeros. Put

$$
\begin{aligned}
D&=\{\gamma_3,\ldots,\gamma_L,t\},&
M_k&=\operatorname{top}_k(D),\\
U_2&=\operatorname{top}_2(\{\gamma_4,\ldots,\gamma_L,t\}),&
q_3&=\operatorname{top}_3(\{r_1,r_2\}\cup D),\\
h&=\max(Z/2,c_1,c_2),&
B_*&=\max(M_3,h+M_2,Z+M_1).
\end{aligned}
\tag{208.21}
$$

The fixed-total family $\mathcal A(c_1,c_2,\gamma,S,t)$ consists of
all input scores with these correct totals, total early pair mass $S$
and terminal $t$. Its pair split and every correct or pair suffix
are free, including early $00$. It fixes neither the actual measure
(208.2) nor unary correct marginals.

**Theorem 208.7 (Complete support of the relocated carrier).** Put
$e_1=010^{L-2}$, $e_2=100^{L-2}$ and
$z_n=1^{n-1}0^{L-n+1}$ for $n\ge3$. The full score

$$
C_{e_a}=c_a,\quad P_{e_a}=p_a\quad(a=1,2),\qquad
C_{z_n}=\gamma_n\quad(n\ge3),\qquad T=t
\tag{208.22}
$$

with all other coefficients zero preserves $Q,W$ and has

$$
B_N(V)=B_O(V)=\max(q_3,S+U_2).
\tag{208.23}
$$

**Proof.** Its actual late pair measure is $S\delta_{0^{L-2}}$;
all correct suffixes and both early lifts have been specified on the
same word space. Class totals, $K$ and $W$ are unchanged.
Maximizing over every label gives the following complete cell values.
Empty maxima in the table are zero.

| Schedule | $N$ maxima in order $00,01,10,11$ |
| --- | --- |
| $(1,2)$ | $(0,r_1,r_2,\max(t,\mu))$ |
| early/late $(a,j)$, other early label $b$ | $(r_a,0,\max(r_b,\max_{3\le n\le j}\gamma_n),\max(t,\max_{n>j}\gamma_n))$ |
| late/late $i<j$ | $(\max(S,r_1,r_2,\max_{3\le n\le i}\gamma_n),0,\max_{i<n\le j}\gamma_n,\max(t,\max_{n>j}\gamma_n))$ |

For early/late pairs the other early class's zero-label reward is
$p_b\le r_b$. For late pairs, zero earns the pooled mass $S$ in
$00$, each early label earns its $r_a$ there, and every other label
earns only its own correct mass. This explains all entries, including
earlier and unqueried labels.

If a late pair's first entry uses a class weight rather than $S$,
the three nonzero maxima are distinct entries of the multiset defining
$q_3$. If it uses $S$, the other two maxima are distinct entries
from $\{\gamma_4,\ldots,\gamma_L,t\}$ and sum to at most $U_2$.
The early-pair and early/late bounds are at most $q_3$ as well.
The full $N$ upper bound follows by the catalog completion in 207.2.

For the lower bound, reuse the three-label collection from 198.4
and 203.7, now assigning early label $a$ its weight $r_a$.
Order any three selected distinct labels from $\{1,\ldots,L,*\}$,
where $*$ means output zero and is last. Query the first two
increasingly and output their labels at their first zero; on positive
exhaustion output the third label. Every selected first-zero class
is collected, for every suffix. An early class contributes all its
$C+P$, and selection of $*$ collects $t$. Thus this one legal
stopped table supplies the selected three weights, and
$B_O\ge q_3$ on $V$ (indeed on any input with that early split).

For $L\ge4$, select the two entries defining $U_2$. If they are
$\gamma_j,\gamma_k$ with $4\le j<k$, table $(3,j;0,j,k)$
collects at least $S+\gamma_j+\gamma_k$ on $V$. If they are
$\gamma_j,t$, use $(3,j;0,j,0)$. Zero-weight ties may be selected
as distinct multiset entries. At $L=3$, $U_2=t$ and
$S+t\le W\le q_3$, so this second lower table is unnecessary.
This proves the matching $O$ lower bound and (208.23).

At $(1,2)$ the nonempty first-zero $N$ cell is $01$.
For both choices of the early address in an early/late pair it is
$00$, and a late pair likewise has empty $01$. Thus merging
$00,01$ before maximizing is consistent with the stated stopped
attainers. All zero totals, unordered late weights, ties and $t=0$
are included. This changes joint support; it imposes no preservation
of an input's auxiliary pair projection. $\square$

**Theorem 208.8 (Dominance region for attained fixed-total minima).**
In $\mathcal A(c_1,c_2,\gamma,S,t)$, define the data (208.21)
independently of the early pair split. Then

$$
B_*\le\min_{\mathcal A}B_O\le\min_{\mathcal A}B_N
 \le\max(B_*,S+U_2).
\tag{208.24}
$$

The split
$p_1^*=\min\{S,\max(0,Z/2-c_1)\}$, $p_2^*=S-p_1^*$ in
(208.22) attains the displayed upper bound. If

$$
B_*\ge S+U_2,
\tag{208.25}
$$

both minima in (208.24) equal $B_*$, and both minimum excesses
equal $B_*-W$. Condition (208.25) holds in particular if
$E\ge S$, $\max(c_1,c_2)\ge S$, or $\gamma_3\ge S$.
For any actual input $y$ with these totals, the constructed score
also satisfies

$$
\Delta_N(V)=\Delta_O(V)
 \le\max\{\delta,U_2-E-t\}.
\tag{208.26}
$$

Thus $U_2\le E+t+\delta$ suffices for a same-$Q$ comparison at
excess at most $\delta$; and $\delta\le1$ with
$U_2\le E+t+1$ suffices for $(V,0)$ in (207.9).

**Proof.** For any early split, separate the three selected weights
according to whether zero, one or two are early:

$$
q_3=\max\{M_3,\max(r_1,r_2)+M_2,Z+M_1\}.
\tag{208.27}
$$

The interval for $r_1$ is $[c_1,c_1+S]$, with $r_2=Z-r_1$.
Clamping $Z/2$ to that interval gives the stated split, minimizing
$\max(r_1,r_2)$ at $h$. The three-label lower table in 208.7
therefore supplies $B_*$ for every competitor, including its
arbitrary early $00$ rows and suffix correlations; the optimized
relocated score gives the upper bound. The finite coefficient
simplex for $\mathcal A$ is compact, and supports are continuous,
so both minima exist. This proves (208.24) and attainment under
(208.25).

This input lower bound is exactly the one already supplied by
[206.7](KBONACCI_SELF_CALIBRATING_ACQUISITION_RESOURCES_CONTINUATION_VIII.md).
To match its notation, let $H_k$ be the sum of the $k$ largest
late totals and put

$$
q=\max(\mu,H_2-t),\qquad
c_0=\min(Z/2,S+\min(c_1,c_2)).
\tag{208.28}
$$

Then $h=Z-c_0$,
$M_1=\max(\mu,t)$, $M_2=\max(H_2,\mu+t)$, and
$M_3=\max(H_3,H_2+t)$. Substitution gives

$$
B_*-W
 =\max\{0,\mu-t,H_2-Z,H_3-W,q-c_0\}=d_0
\tag{208.29}
$$

of (206.21). Padding at short lengths contributes only dominated
terms, not fictitious queried labels. The lower bound is reused;
the relocated score has cost $\max(d_0,U_2-E-t)$, whereas
206.7's particular balanced chain has $\max(d_0,q-E)$.
Since $U_2\le M_2$ and $M_2-t=q$, the former is no larger.
This compares two constructions, not all signed or convex
consequences of the earlier one.

If $E\ge S$ or $\max(c_1,c_2)\ge S$, then $h\ge S$ and
$B_*\ge h+M_2\ge S+U_2$. If $\gamma_3\ge S$, its entry and
the two entries defining $U_2$ give $M_3\ge S+U_2$.
At $L=3$ the padded zero causes no change to this inequality.
Finally $B_*\le B_O(y)=W+\delta$, so subtracting $W=E+S+t$
from the constructed maximum proves (208.26). There is one maximum
of two costs, not their sum.

In particular any unit-$O$ input with $Q(y)\notin E_N$ would have
to satisfy

$$
U_2>E+t+1,\qquad E<S,\qquad\gamma_3<S,\qquad
c_1+p_1<S,\quad c_2+p_2<S
\tag{208.30}
$$

for its actual early split. Indeed if some actual $r_a\ge S$,
then $q_3\ge r_a+U_2\ge S+U_2$, and (208.22) at that split
has support $q_3\le B_O(y)$, giving a certificate. The other
conditions follow from the preceding sufficient cases.
These exclusions are necessary, not sufficient for nonmembership.
Outside (208.25), (208.24) and (208.26) are the asserted bounds;
no global fixed-total minimum equal to their upper endpoint is
implied. $\square$

### 208.4 A free carrier with two leading classes and bounded later classes

**Theorem 208.9 (Three-block stock and restricted minima).** Suppose
$E=0$ and the first two positive late classes are at actual addresses
$a<b$, with totals $\gamma_a=\mu$, $\gamma_b=\eta>0$.
All remaining positive late classes lie in $J\subseteq\{b+1,\ldots,L\}$
and have totals $g_j$ in arbitrary order. Let $d\ge0$ satisfy

$$
\mu\ge\eta+d,\qquad \eta\ge2d,\qquad
u=\mu-d,\quad v=\eta-d,\quad A=2u-v,\qquad
r=\frac{Av}{A+v},\qquad 0\le g_j\le r.
\tag{208.31}
$$

Other late totals are zero; zero $g_j$ may also be retained in $J$.
Among all $A_w=0$/early-pair scores with these correct totals and
$E=0$, allowing both $S,T$ and all joint placements to vary, the
least stock $B=S+T$ permitting $\Delta_O\le d$ or permitting
$\Delta_N\le d$ is in both cases

$$
B^\star=3u+v=3\mu+\eta-4d.
\tag{208.32}
$$

At $B=B^\star$ the minimum of each excess is exactly $d$.
For every $B\ge B^\star$ there is one score with that stock and
these correct totals, hence the prescribed $Q$, with
$\Delta_N=\Delta_O=d$. Consequently each actual input of this
profile with $\Delta_O\le d$ has a same-$Q$ representative of
$N$ cost $d$. It is a unit certificate when $d\le1$.
No claim that $d$ is the minimum excess at $B>B^\star$ is made.

**Proof.** The disjoint-loss bound (202.35), from the original
stopped tables, applies to every competitor of excess $\epsilon$:

$$
S\ge2(\mu-\epsilon)_++(\eta-\epsilon)_+,\qquad
T\ge(\mu-\epsilon)_+.
\tag{208.33}
$$

For completeness, the first two losses are
$\{w_1=1,w_a=0\}$ and $\{w_2=1,w_a=0\}$, each forced by
$(h,a;0,a,0)$ to have mass at least $\mu-\epsilon$.
They are disjoint on early pair support, also with early $00$.
The third loss, forced by $(a,b;0,b,0)$, is
$\{w_a=1,w_b=0\}$ and is disjoint from the first two.
The table $(1,2;1,2,a)$ gives the terminal bound.
Thus (208.33) reuses the existing lower mechanism on one measure.
For $\epsilon\le d$, it gives
$B\ge3\mu+\eta-4\epsilon\ge B^\star$.

Here is a joint construction attaining the bound. Set every inactive
late bit to one. On the active late bits use three finite measures:

| Component | Mass | $(x_a,x_b)$ | Later bits $j\in J$ |
| --- | --- | --- | --- |
| I | $v$ | $00$ | all one |
| II | $A$ | $01$ | product with zero probabilities $g_j/A$ |
| III | $v$ | $10$ | product with zero probabilities $g_j/v$ |

Their sum is $\nu$, of total $2u+v$. The hypotheses imply
$u\ge v+d$, $v\ge d$, $v>0$, $A\ge\mu$ and
$r<\min(A,v)$, so every component is nonnegative.
For each atom $x$, put pair mass $\nu(x)/2$ at each of $01x,10x$.
Put correct mass $\mu$ at $w(\{a\})$ and $g_j$ at
$w(\{j\})$ for $j\in J$.

For class $b$, use length measure on $q\in[0,\eta)$.
Bits before $b$ are one, bit $b$ is zero, and a later active bit
$j$ is one exactly when $q<2v-g_j$; inactive bits are one.
Assign each resulting word the length of its parameter set.
The finitely many thresholds partition this interval, supplying
nonnegative correct coefficients of total $\eta$ on $\Omega_b$.
Coincident words have their coefficients added. Put $T=u$.
This defines one full score of stock $3u+v$.
The product measures and interval lengths specify proof weights;
they require no source law or acquisition randomness.

The $(a,b)$ pair masses are $(v,A,v,0)$. For $j\in J$,

$$
\nu(x_j=0)=2g_j,\qquad
\nu(x_a=0,x_j=0)=\nu(x_b=0,x_j=0)=g_j.
\tag{208.34}
$$

Write $c=1/A+1/v=1/r$. For $i<j$ in $J$ the actual pair
masses, in $00,01,10,11$ order, are

$$
\begin{aligned}
p_{00}&=cg_ig_j,&p_{01}&=2g_i-p_{00},\\
p_{10}&=2g_j-p_{00},&
p_{11}&=2u+v-2g_i-2g_j+p_{00}.
\end{aligned}
\tag{208.35}
$$

Since $cg_i,cg_j\le1$, $p_{01}\ge g_i$ and $p_{10}\ge g_j$.
Component I lies wholly in $11$, so $p_{11}\ge v$.
These are marginals of the same $\nu$.

Label zero collects each cell's entire pair mass and also $T$ in
the all-positive cell. Early labels collect subsets of that baseline,
because $E=0$. It remains to bound every late correct label.
The head pair $(1,2)$ has maxima
$(0,(2u+v)/2,(2u+v)/2,\mu)$ and excess $d$.
For an early/$a$ pair, the $10$ baseline is $u$ and the largest
correct reward there is $\mu=u+d$. Its $11$ baseline
$u+v/2$ covers $\eta$ and every $g_j$, since
$u\ge v+d$. For an early/$b$ pair, cell $10$ has baseline
$v$ and reward $\eta=v+d$; the $11$ baseline
$2u-v/2$ covers $\mu$. For an early/$j$ pair, the $10$
baseline $g_j$ covers both class $j$ and class $b$'s mass
$(d-v+g_j)_+\le g_j$. Its $11$ baseline
$2u+v/2-g_j\ge\mu$ covers all labels.
In each of these schedules the two early-zero cells contain no
late correct mass. Therefore the early-pair types cost at most $d$.

For $(a,b)$ the complete four maxima are

$$
(v,A,v+d,u),
\tag{208.36}
$$

because $A\ge\mu$ and all remaining totals are at most $v\le u$.
The stopped maxima are $(2u,v+d,u)$, attaining excess $d$.
For $(a,j)$ the pair baselines are
$(g_j,2u-g_j,g_j,v-g_j)$. Class $a$ earns $\mu$ in $01$,
covered by $2u-g_j\ge A\ge\mu$. Class $b$ earns
$(d-v+g_j)_+\le g_j$ in $10$ and at most $\eta$ in $11$,
whose baseline including $T$ is $u+v-g_j\ge\eta$.
Class $j$ is covered in $10$; all other sole-zero classes lie
in $11$ and have total at most $r<v$.

For $(b,j)$ the pair baselines are
$(g_j,2v-g_j,g_j,A-g_j)$. Class $b$ contributes
$(d-v+g_j)_+\le g_j$ in $00$ and
$\min(\eta,2v-g_j)$ in $01$, both covered. Class $j$ is
covered in $10$, while class $a$ and every other correct label
are covered in $11$ by $u+A-g_j\ge\mu$. Thus these two
pair types have no excess.

For $i<j$ in $J$, class $i$ is covered by $p_{01}\ge g_i$,
and class $j$ by $p_{10}\ge g_j$. Class $b$'s off-diagonal
rewards are at most $(g_i-g_j)_+$ and $(g_j-g_i)_+$,
respectively, so are covered too, without an ordering assumption
on $g_i,g_j$. In $11$, the baseline is
$u+p_{11}\ge u+v\ge\mu$, covering every label, including
$a$ and $b$ when neither is queried. The only possible uncovered
reward is class $b$'s $00$ mass

$$
h_{ij}=(d-v+\min(g_i,g_j))_+\le d.
\tag{208.37}
$$

The excess of this complete table is therefore at most
$(h_{ij}-p_{00})_+\le d$. Its other three cells have no positive
excess to add. This checks every earlier, intermediate and future
label on the same carrier.

Inactive coordinates are one on all positive-score rows, so a
schedule involving them supplies only singleton or constant
information. Empty schedules, repetitions and reversals are covered
by the information identities in 207.2; repetitions still count as
actual requests. Consequently $\Delta_N\le d$. The stopped
$(a,b;0,b,0)$ table attains $d$, proving both equalities.

For $B>B^\star$, add $B-B^\star$ at $T$. Each fixed table's
reward increases by at most this increment and its anchor by
exactly the increment, so no excess increases. The same stopped
table uses zero in $11$ and retains excess $d$.
At $B=B^\star$, a competitor with $\epsilon<d$ would violate
(208.33), proving the claimed minimum of each excess. This also
proves the minimum-stock statement for both catalogs and the
same-$Q$ comparison for any original input in the declared class.
All comparisons use (207.9) with the single charge $\theta=0$.

The construction includes $d=0$, $\eta=2d$, $\mu=\eta+d$,
$g_j=0,r$, empty $J$, ties, and arbitrary gaps between active
addresses. The case $\eta=0$ belongs to the earlier single-class
result and is not included in the denominators of (208.31).
For empty $J$, this is the attained two-class case of 204.3.
The new assertion here is its stated bounded-later-class extension
and restricted stock minimum; it does not optimize over arbitrary
full-score representatives or signed residual certificates.
$\square$

**Definition 208.10 (Earlier coverage and original-source boundary).**
The fair/common-suffix mechanisms remain those of 198.2 and 203.6;
the fixed two-late minima and zero-cost rays remain those of
204.3–204.4. The lower bound (208.29) is 206.7's $d_0$.
The retained early-credit restrictions of 205.5–205.6 and the
fixed-projection results of §207 keep their own hypotheses.
None of (208.6), (208.13), (208.24) or (208.32) asserts a
sufficient characterization of unrestricted $E_N$.

In particular the portion of 208.9 with every $g_j\le d$ is
already covered by the zero-cost rays of 204.4 with one signed
residual charge at most $d$. The same-$Q$ stock minimum does not
assert new quotient membership for that portion. For $r>d$, no
exclusion from the complete old convex, signed or zero-core closure
is asserted either.

The original countable labeled source, static prime replies,
unchanged consumer and nonatomic targets are exactly those in
207.1 and [110.1–110.2](KBONACCI_SELF_CALIBRATING_ACQUISITION_RESOURCES_CONTINUATION.md#110-exact-closed-cap-transport-on-the-original-countable-source).
The original sequences remain positive, monotone and vanishing;
zero finite score totals place no zero-amplitude restriction on them.
Only an actual normalized finite probability configuration satisfying
all of (207.3) is supplied to 110.2. That theorem retains full-carrier
outputs and arbitrary addresses in its necessary direction, and its
compact finite-catalog limit retains the exact closed cap. In its
sufficient direction one source-independent uniform seed selects
the whole schedule and terminal table before replies. Two class
configurations can use partitions of this same seed and their common
refinement. Outputs need not agree seedwise. Handoff is actually
finite, advice is zero, and the hard budget remains at most two
actual requests, including repetitions and ignored replies.
$N$ obtains its preselected replies; $O$ uses its increasing
preselected schedule and stops at the first queried zero.

Every multiple-zero word and independent pair demand remains in
that finite configuration. The exact actual-tail identity (207.51)
includes $a_n=\varepsilon$, small active lengths and the cap-one
endpoint; the finite positive word is not an infinite positive
source. The coefficient conditions $c\ge H$ and $\beta\le1$ retain
all the probability-vector and degree hypotheses of 109.1.
Neither a score measure nor a deterministic
table maximizing its support is thereby a feasible probability
configuration or acquired information.

The all-profile, low-terminal, full-carrier comparison (207.52)
remains unresolved, as does the critical $\tau=4$ affordability
case omitted by 208.5. These results supply actual-input necessary
relations and the stated restricted constructors and minima.
They supply neither a universal affordable selector nor an original
common-seed $N_2$ attainer together with a lower certificate against
every original arbitrary-address $O_2$ competitor. In particular
112.2's obstruction to preserving one law does not exclude a different
stopped law at the same cap.

## 追加锚（本行以下为增补区）

## 209. Common-carrier support, retained-credit minima and unary-preserving relocation

**Definition 209.1 (Inherited scores and actual carriers).** Use
Definitions 207.1–207.3 and 208.1 without changing the original source,
resource classes, event rows or certificate. Thus $L\ge3$,
$I=\{3,\ldots,L\}$, $A=0$, $P$ is supported on
$\Omega_1\cup\Omega_2$, and every correct suffix is permitted.
In particular the actual full late projection is
$\nu(x)=P_{00x}+P_{01x}+P_{10x}$, of mass $S$.
Write $e_j=w(\{j\})$ and $v_j=w(\{j,j+1,\ldots,L\})$.
The prefix-reset map $R_j$ sends a late word $x$ to the full word
with coordinates before $j$ equal to one, coordinate $j$ zero, and
coordinates after $j$ copied from $x$.
All measures below are finite nonnegative score weights on this full
Boolean carrier. Several class measures may use the same atom.
They are not source laws or normalized probability kernels.

For a fixed increasing pair $s$, write $B_N^s,B_O^s$ for its support
before maximizing over schedules. The complete catalogs, all labels,
and the refinement argument for short $N$ schedules are those of
207.2. In particular $B_O\le B_N$ includes every empty and singleton
$O$ rule. No embedding of a last-address singleton into a longer
increasing stopped pair is needed. The signed hull, its four vertex
families, and the single certificate inequality remain (207.7)–(207.10).

### 209.1 Equal pair marginals with unrestricted class masses

**Theorem 209.2 (Complete support on one equal-pair carrier).** Let
$L\ge4$, and stipulate one actual measure $\nu$ whose cells at every
late pair $i<j$ have masses $(a,d,d,h)$ in order $00,01,10,11$.
All four parameters are nonnegative; put $S=a+2d+h$ and $m=a+d$.
Choose arbitrary $g_j,c_1,c_2,\tau\ge0$, and set

$$
\begin{aligned}
c&=c_1+c_2,&c_*&=\min(c_1,c_2),&\mu&=\max_{j\in I}g_j,\\
f_j&=\max(\{g_k:k>j\}\cup\{0\}),&
u_j&=\min(g_j,d),&r_j&=(g_j-d)_+.
\end{aligned}
\tag{209.1}
$$

Construct $V$ by $P_{01x}=P_{10x}=\nu(x)/2$, by early correct
masses $c_a$ at $w(\{a\}\cup I)$, by late correct masses
$u_j\delta_{e_j}+r_j\delta_{v_j}$, and by $T=\tau$.
Coincident words are added. Its anchor is $W_V=S+c+\tau$.
Define

$$
\begin{aligned}
I_j&=(g_j-m/2-c_*)_++(f_j-(d+h)/2-\tau)_+,\\
J_{ij}&=(g_i-m)_++(g_j-d)_++(f_j-h-\tau)_+-c,\\
D_F&=\max\{0,\mu-\tau,\max_j I_j,\max_{i<j}J_{ij}\}.
\end{aligned}
\tag{209.2}
$$

Then $\Delta_N(V)=\Delta_O(V)=D_F$. This is equality of complete
catalog maxima. It does not assert $B_N^s(V)=B_O^s(V)$ for every
schedule. There is no upper bound on $g_j$, $c$ or $\tau$ in this
statement. Existence of the single full $\nu$ is a hypothesis;
compatible pair tables alone do not supply it.

**Proof.** The late placement is exactly the threshold placement of
[203.2](KBONACCI_SELF_CALIBRATING_ACQUISITION_RESOURCES_CONTINUATION_VII.md)
when every directed cutoff $a_{nj}=d$. Here its complete support is
computed without the protected-terminal or bounded-profile restrictions.

The head pair supplies $(\mu-\tau)_+$ and the anchor supplies zero.
On early/late $(a,j)$, with other early label $b$, the stopped-zero
cell supplies $S/2+c_a$; the other two cells offer respectively
$m/2+c_b$ or $g_j$, and $(d+h)/2+\tau$ or $f_j$.
Choose $a$ so that $c_b=c_*$. This gives $I_j$.
A late stopped $(i,j)$ can independently choose zero or $i$ in its
first cell, zero or $j$ in $10$, and zero or a future maximizing
label in $11$. Its baselines are $m,d,h+\tau$, giving $J_{ij}$.
Thus $\Delta_O(V)\ge D_F$. Ordering distinct late labels also gives

$$
D_F\ge g_n+g_q-S/2-\tau-c_*\quad(n\ne q),\qquad
D_F\ge g_n+g_q+g_k-W_V\quad(n,q,k\text{ distinct}).
\tag{209.3}
$$

For the first inequality use $I$ at the earlier label; for the second
use $J$ at the first two ordered labels. Positive parts dominate their
arguments. These are bounds from one stopped table at a time.

For an early/late $N$ pair the two early-zero maxima sum to
$S/2+c_a$. The remaining maxima are

$$
\max(m/2+c_b,g_j,\max_{n<j}r_n),\qquad
\max((d+h)/2+\tau,f_j,\max_{n<j}u_n).
\tag{209.4}
$$

If the second uses its baseline or a future label, choose a late
winner $n\le j$ of the first, taking $n=j$ when its gain is zero.
The first gain is at most $(g_n-m/2-c_*)_+$ and $f_n\ge f_j$,
so $I_n$ bounds the combined excess. If an earlier label $k$ wins
the second, its reward is $u_k\le d$. With positive first gain the
excess is at most
$g_n-m/2-c_b+d-(d+h)/2-\tau\le\mu-\tau$;
with no first gain use $u_k\le\mu$ instead. Thus (209.4) is bounded.

For late $i<j$, all-label maxima in $N$ are exactly

$$
\begin{aligned}
M_{00}&=\max(a,a/2+c_1,a/2+c_2,\max_{n\le i}r_n),\\
M_{01}&=d,\\
M_{10}&=\max(d,g_j,\max_{i<n<j}r_n),\\
M_{11}&=\max(h+\tau,f_j,\max_{n<j,\ n\ne i}u_n).
\end{aligned}
\tag{209.5}
$$

In $01$ only class $i$ can add correct reward, at most $u_i\le d$.
Earlier unqueried labels occur explicitly in $00$ and $11$.
Let $g_{00},g_{10},g_{11}$ be the gains over $a,d,h+\tau$;
the excess is $g_{00}+g_{10}+g_{11}-c$.

Suppose first that $00$ uses a late label or its baseline, and $11$
uses a future label or its baseline. Select winners $n\le i$ and
$i<q\le j$ for the first and third cells, using $n=i,q=j$ for
zero gains. Then

$$
g_{00}\le(g_n-m)_+,\qquad g_{10}\le(g_q-d)_+,\qquad
g_{11}\le(f_q-h-\tau)_+.
$$

One $J_{nq}$ bounds their sum minus $c$. If instead an earlier label
$k$ positively wins $11$, use $u_k\le d$. When at most one of
$g_{00},g_{10}$ is positive, the excess is at most $\mu-\tau$.
When both are positive, the distinct winners satisfy $n\le i<q\le j$,
and the excess is

$$
g_n+g_q+u_k-W_V-\epsilon,\qquad
\epsilon=\begin{cases}0&q=j,\\d&q<j.\end{cases}
$$

For $k\notin\{n,q\}$ use the three-label inequality (209.3).
For $k=n$ or $q$ use its two-label inequality and
$u_k\le d\le S/2+c-c_*$. No separate allowance is paid for $11$.

Finally suppose an early label positively wins $00$. Its gain is
$c^{\max}-a/2$, so the excess becomes
$g_{10}+g_{11}-c_*-a/2$.
If $11$ has a future winner and both gains are positive, choose $q$
for $10$ and bound this by
$g_q+f_q-d-h-\tau-c_*-a/2\le I_q$, since
$d+h+a/2\ge S/2$. With only the $10$ gain use
$d+a/2\ge m/2$ and the first part of $I_q$; with only the $11$
gain use $\mu-\tau$. If $11$ has an earlier winner, $u_k\le d$
gives the same $\mu-\tau$ bound, with or without a $10$ gain.
This includes arbitrarily large early credit.

Every $N$ pair is bounded by $W_V+D_F$. The catalog completion in
207.2 handles every shorter rule. Together with the stopped lower
bounds and $B_O\le B_N$ this proves both equalities, including
$a,d,h,\tau$ or any class mass zero. $\square$

**Theorem 209.3 (The zero-early-credit fixed-data minimum).** Fix
$\nu$ as in 209.2, arbitrary late totals $\gamma_j\ge0$ and $T=t$,
and impose $E=0$. Among all input-family scores with this entire
projection, these individual totals and this $t$, both complete
excesses have attained minimum $D_F$, with parameters
$g=\gamma,c_1=c_2=0,\tau=t$. The score in 209.2 attains both and
preserves $Q$. Competitors may use arbitrary early $00$ pair rows
and arbitrary correct suffixes. Every unit-$O$ competitor therefore
has its same-$Q$ certificate $(V,0)$.

**Proof.** For any competitor the head and late stopped lower tables
in 209.2 still collect whole correct classes, independently of suffixes.
For early address $a$ put
$p_{a0}=P\{w_a=1,w_j=0\}$ and
$p_{a1}=P\{w_a=1,w_j=1\}$.
The stopped table, with zero on its first cell and independent switches
to $j$ and a largest future class on the other cells, gives

$$
\Delta_O(y)\ge(\gamma_j-p_{a0})_++(f_j-p_{a1}-t)_+.
\tag{209.6}
$$

On early pair support the two early-one sets are disjoint, including
when some input atoms have early prefix $00$. Hence
$p_{10}+p_{20}\le m$ and $p_{11}+p_{21}\le d+h$.
The maximum of the two bounds (209.6) is at least their average.
Convexity and decreasing dependence on both capacities bound that
average below by $I_j$ with $c_*=0$. Thus every competitor costs
at least $D_F$ in $O$, and consequently in $N$. The score of 209.2
attains it. This extends 207.17 beyond $s\le\gamma_j\le2s$ and
beyond equal cells, using $a=d=s,h=(\chi-3)s,\tau=s$ for that
supplier's domain. Its $E=0$ equal-cell specialization is counted
here only once. $\square$

For later use, applying the existing residual identity (207.8) to
209.2 with $g=\eta$ gives the exact nonnegative charge

$$
\Theta_F=\max\left\{0,c-E,c_2-\gamma_2,
 \max_k\frac{R_k-(k-2)(E-c)}{k-1},
 \max_k\frac{3R_k+(k-2)(W_V-W)}{k+1}\right\},
\quad R_k=\sum_{j=3}^k(\gamma_j-\eta_j).
\tag{209.7}
$$

Here the chosen carrier has mass $S$, $W=E+S+t$ and
$W_V=S+c+\tau$; the input projection need not equal that carrier.
One certificate exists whenever $D_F+\Theta_F\le1$, by (207.10).
Both signed prefix columns are required. In particular
$\eta=\gamma,c_a\le\gamma_a,\tau=t+E-c$ leave $W_V=W$ and
residual $-\sum_{a=1}^2(\gamma_a-c_a)(1-b_a)\le0$.
This is a substitution into the old hull, not another fixed-data
minimum for $E>0$.

**Proposition 209.4 (Early zero-zero inputs and the schedule boundary).**
For every $L\ge5$, take the actual product measure of mass $15/2$
and late zero probability $4/5$, so that
$(a,d,d,h)=(24/5,6/5,6/5,3/10)$. Put
$g_j=31/5,c_1=c_2=12/5,\tau=27/5$ in 209.2.
Both excesses equal $9/10$. Replacing its pair lifts by
$P_{00x}=\nu(x)/100$ and
$P_{01x}=P_{10x}=99\nu(x)/200$ gives an input with the same $Q,W$
and $\Delta_O\le39/40$.
At $L=6$, instead put $g_3=32/5$ and $g_4=g_5=g_6=6$, leaving
the original balanced lifts and other parameters fixed. Both global
excesses equal one, while the particular pair $(4,5)$ has $N$ excess
$7/10$ and $O$ excess $3/10$.

**Proof.** In the first case (209.2) gives $I_j=17/20$ before the
last label, $I_L=4/5$, and $J_{ij}=9/10$ when $j<L$, $2/5$
when $j=L$. Moving mass $S/100=3/40$ between the indicated early
prefixes changes the reward of any fixed table by at most $3/40$;
maximization preserves that bound. Class totals and the anchor do not
change. This gives $9/10+3/40=39/40$.

For the second case $W_V=177/10$ and (209.2) gives $D_F=1$.
At $(4,5)$ the $N$ maxima are $(26/5,6/5,6,6)$, sum $92/5$;
the earlier unqueried label 3 wins $00$. The stopped maxima are
$(6,6,6)$, sum $18$. Subtracting $177/10$ gives the two stated
excesses. A different stopped table attains the global value one.
The first quotient family is already covered by 206.15:
$E\ge\mu-2$ and $W\ge3\mu-1$. These examples concern support
and row fidelity, not a new quotient region. $\square$

### 209.2 Equal cells with positive retained early credit

**Theorem 209.5 (Exact retained-credit fixed-data minimum).** Let
$L\ge4$, $s>0$, $3\le\chi\le4$, and stipulate one actual full
late measure $\nu$ of mass $S=\chi s$ with every late pair having
cells $(s,s,s,z)$, where $z=(\chi-3)s$. Fix arbitrary
$\gamma_1,\ldots,\gamma_L\ge0$, $T=s$ and $0<E=\gamma_1+\gamma_2\le S$.
Set

$$
\begin{aligned}
r_j&=(\gamma_j-s)_+,&r_*&=\max_jr_j,&
R_j&=\max(\{r_k:k>j\}\cup\{0\}),&b_*&=(\chi-2)s/2,\\
D_T&=\max\left\{r_*,\max_j(r_j+R_j-b_*-E/2),
 \max_{i<j}\big((r_i-s)_++r_j+(R_j-z)_+-E\big)\right\}.
\end{aligned}
\tag{209.8}
$$

Over all scores with this entire $\nu$, these individual correct
totals and this terminal mass, both complete excesses have attained
minimum $D_T$. Early $00$ pair allocations and all correct suffixes
remain arbitrary in the competitor class.
An attainer uses $H=(S+E)/2$, $p_a=H-\gamma_a$ and

$$
P_{01x}=p_1\nu(x)/S,\quad P_{10x}=p_2\nu(x)/S,\quad
C_{01x}=\gamma_1\nu(x)/S,\quad C_{10x}=\gamma_2\nu(x)/S,
\qquad C|_{\Omega_j}=\min(\gamma_j,s)\delta_{e_j}+r_j\delta_{v_j}.
\tag{209.9}
$$

It preserves $Q,W$ and has $\Delta_N=\Delta_O=D_T$.
At $E=0$ the same conclusion is the specialization of 209.3, so
no second zero-credit minimum is needed. A unit-$O$ input in the
stated range has the single certificate $(V,0)$.

**Proof.** Since $\gamma_a\le E\le H\le S$, all coefficients
in (209.9) are nonnegative, $p_1+p_2=S$, and each early label's
reward measure is $H\nu/S\le\nu$. Totals are preserved.

For any competitor the head table forces $r_*$. A late stopped
$(i,j)$ offers baselines $2s,s,z+s$ against correct totals
$\gamma_i,\gamma_j$ and a maximal future total. Its lower excess
is $(r_i-s)_++r_j+(R_j-z)_+-E$.
For the early lower bound it suffices to consider $r_j,R_j>0$;
otherwise the claimed expression is at most $r_*$.
Choose $k>j$ with $\gamma_k=s+R_j$, and write
$P_a=\sum_{\Omega_a}P$, so $P_1+P_2=S$ even with early $00$.
The original stopped tables $(a,j;a,j,k)$, $a=1,2$, earn at least
$\gamma_a+P_a+\gamma_j+\gamma_k$.
The catalog maximum exceeds their average, so subtracting $W$ gives
$r_j+R_j-b_*-E/2$. Averaging valid lower bounds executes no extra
schedule. Every competitor therefore has $\Delta_O\ge D_T$.

For (209.9), at a late $N$ pair $i<j$ put

$$
A_i=\max(\{(r_p-s)_+:p\le i\}\cup\{0\}),\quad
U_{ij}=\max(\{r_j\}\cup\{(r_q-s)_+:i<q<j\}),\quad
V_j=(R_j-z)_+.
$$

All-label maxima are $s+A_i,s,s+U_{ij},z+s+V_j$.
The dominated early labels add no larger entry; earlier chain masses,
intermediate chain masses and future totals are explicitly retained.
Choose $p\le i$ attaining $A_i$ and $q\in(i,j]$ attaining
$U_{ij}$, using $p=i$ when its gain is zero and $q=j$ when the
queried class wins. Then $A_i=(r_p-s)_+$, $U_{ij}\le r_q$,
$R_q\ge R_j$, and the whole excess is bounded by the single term
$(r_p-s)_++r_q+(R_q-z)_+-E$ in (209.8).
This readdressing compares static tables; it is not an adaptive query.

For early/late pairs put $c_* =\min(\gamma_1,\gamma_2)$,
$\ell=(\chi-2)/\chi$, and
$U_j=\max(\{r_j\}\cup\{(r_k-s)_+:k<j\})$.
The early-zero branch contributes $H$ even after splitting.
The other zero-cell maximum is $s+\max(E/\chi,U_j)$.
In the last cell the other early owner has reward $H\ell$, while
zero has reward $(H-\gamma_b)\ell+s$.
The larger of the two early-address supports uses $\gamma_b=c_*$.
Only for that maximizing choice do we need zero to dominate this
owner: $c_*\ell\le S\ell/2=b_*\le s$ proves it.
Earlier sole-zero correct rewards are at most $s$. Consequently the
maximum excess over the two early addresses is exactly

$$
(U_j-E/\chi)_+
 +(R_j-b_*-\ell(E/2-c_*))_+-\ell c_*.
\tag{209.10}
$$

Expanding the two positive parts gives the maximum of

$$
-\ell c_*,\quad U_j-E/\chi-\ell c_*,\quad
R_j-b_*-\ell E/2,\quad U_j+R_j-b_*-E/2.
$$

The first three are at most $r_*$. If $U_j=r_j$, the last is a
term of (209.8); otherwise $U_j=(r_k-s)_+$ for some $k<j$, and
$U_j+R_j\le r_k+R_k$, giving another such term.
The head excess is $r_*$, and catalog completion bounds all shorter
rules. Hence $\Delta_N(V)\le D_T$; the universal lower bound and
$B_O\le B_N$ give both minima and attainment. No condition
$\gamma_j\le2s$ was used.

When $E>S$, this fixed-projection minimum is not asserted.
The existing chain supplier 206.7–206.8 has
$E\ge\min(S,\mu)$ and supplies a unit certificate for a unit input,
possibly changing its projection. This separate application does not
extend (209.8)'s minimum domain. $\square$

**Proposition 209.6 (An all-length strict relocation and an over-stock endpoint).**
Let $m=L-2\ge4$, $\chi=4-2/\lceil(m+1)/2\rceil$, and use the
actual subset measure $\mathcal L_m(s)$ of 207.4. Choose
$1<s<1/(\chi-3)$ and $z=(\chi-3)s<u<1$.
Put $\gamma_1=E=u-z$, $\gamma_2=0$, $\gamma_j=s+u$ for
$3\le j<L$, $\gamma_L=s+1$, and $T=s$.
Keep the early rows (209.9), but put every late correct mass on its
sole-zero word to obtain $Y$. Then

$$
(\Delta_N(Y),\Delta_O(Y))=(1+u,1),\qquad
(\Delta_N(V),\Delta_O(V))=(1,1),\qquad Q(Y)=Q(V).
\tag{209.11}
$$

**Proof.** The moments of the one subset measure in 207.4 give the
required cells at all lengths. In (209.8), $r_j=u$ before the last
class and $r_L=1$; the early joint term is at most
$1+(u-s)/2<1$, and a late term with a future class is
$u+1-z-E=1$. Thus $D_T=1$.
For $Y$, a late stopped pair's first maximum is $2s$ since
$\gamma_i<2s$; the remaining two maxima sum to $2s+u+1$.
Its excess is one. Splitting the first cell in $N$ gives maximum
$s$ in $00$ and $\gamma_i$ in $01$; the full support is
$4s+2u+1$ for every late pair, whereas $W=4s+u$.
Early/late excesses are at most $\max(1,1+(u-s)/2)=1$, and the
head attains one. The catalog completion proves (209.11).
For example $L=6,s=2,\chi=10/3,u=4/5$ gives $W=44/5$,
input supports $(53/5,49/5)$ and output supports $(49/5,49/5)$.
Here $\nu$ assigns $2/3$ to each late word having two or three zeros;
its ten atoms form the required joint measure.

At the distinct closed endpoint $L=6,s=1/2,\chi=10/3$,
$\gamma_1=4/3,\gamma_2=0$ and every late $\gamma_j=3/2$,
(209.8) again gives one: $r_*=1$, the largest early term is
$2-1/3-2/3=1$, and the largest late term is
$1/2+1+5/6-4/3=1$. The actual zero marginal is only $2s=1$.
Thus this minimum allows correct mass above marginal stock.
Neither example excludes all prior convex or signed certificates.
$\square$

### 209.3 Comparable class measures on a common carrier

**Definition 209.7 (Simultaneous comparable submeasures).** Let $L\ge3$
and let $\nu$ be one actual measure on all late coordinates, of mass
$S>0$. Put $\nu_n=\nu|_{\{x_n=0\}}$,
$m_j=|\nu_j|$, $d_{ij}=\nu\{x_i=1,x_j=0\}$ and
$h_{ij}=\nu\{x_i=x_j=1\}$.
Choose $c_a\ge0$ with $E=c_1+c_2\le S$, and put
$H=(S+E)/2$, $p_a=H-c_a$, $p_*=\max(p_1,p_2)$.
For every late $n$ choose

$$
0\le\mu_n\le\nu,\qquad |\mu_n|=\eta_n,\qquad
\mu_n\le\nu_n\ \text{or}\ \nu_n\le\mu_n.
\tag{209.12}
$$

The last alternative is comparability of measures on the whole cube,
not just of their total masses. Its direction may depend on $n$.
There is no condition $\sum_n\mu_n\le\nu$.
For $n<j$ write $u_{nj}=\mu_n\{x_j=0\}$, and set

$$
\begin{aligned}
f_j&=\max(\{\eta_n:n>j\}\cup\{0\}),&\mu&=\max_n\eta_n,\\
U_j&=\max(\{\eta_j\}\cup\{u_{nj}:n<j\}),&
Z_j&=\max(\{f_j\}\cup\{\eta_n-u_{nj}:n<j\}),\\
U_{ij}&=\max(\{\eta_j\}\cup\{u_{nj}:i<n<j\}),&
Z_{ij}&=\max(\{f_j\}\cup\{\eta_n-u_{nj}:i<n<j\}).
\end{aligned}
\tag{209.13}
$$

All class indices in these expressions lie in $I$.

**Theorem 209.8 (Exact simultaneous cost with comparable measures).**
Use the proportional early rows
$P_{01x}=p_1\nu(x)/S$, $P_{10x}=p_2\nu(x)/S$,
$C_{01x}=c_1\nu(x)/S$, $C_{10x}=c_2\nu(x)/S$,
late correct measures $(R_n)_*\mu_n$, and $T=t\ge0$.
This single score $V$ has anchor $W_V=S+E+t$ and exact cost

$$
\begin{aligned}
D_j={}&\max(Hm_j/S,U_j)\\
 &+\max(H(S-m_j)/S,p_*(S-m_j)/S+t,Z_j)-H-t,\\
D_{ij}={}&(\eta_i-m_i)_++(U_{ij}-d_{ij})_+
                  +(Z_{ij}-h_{ij}-t)_+-E,\\
D_N={}&\max\{0,\mu-t,\max_jD_j,\max_{i<j}D_{ij}\},\\
\Delta_N(V)={}&\Delta_O(V)=D_N.
\end{aligned}
\tag{209.14}
$$

For this score the stronger equality $B_N^s(V)=B_O^s(V)$ holds
for every increasing pair. The construction preserves the entire
$\nu$, the declared class totals, and $t$.
Every choice $0\le\eta_n\le S$ admits measures (209.12), for example

$$
\mu_n=\begin{cases}
(\eta_n/m_n)\nu_n,&0<m_n,\ \eta_n\le m_n,\\
0,&\eta_n=m_n=0,\\
\nu_n+\dfrac{\eta_n-m_n}{S-m_n}(\nu-\nu_n),&m_n<\eta_n\le S.
\end{cases}
\tag{209.15}
$$

This existence assertion alone supplies no bound $D_N\le1$.

**Proof.** Each early label's reward measure is $H\nu/S\le\nu$.
On a late pair $i<j$, any earlier class $n<i$ has, in each queried
cell, at most the corresponding $\nu$ mass: $R_n$ leaves both
queried coordinates unchanged. No later label can occur in $00$ or
$01$. The only potentially larger reward there is class $i$, whose
two pieces are $\mu_i\{x_j=0\}$ and $\mu_i\{x_j=1\}$.
By (209.12), their differences from the two pieces of $\nu_i$ have
the same sign. Hence

$$
\begin{aligned}
&\max(\nu\{00\},\mu_i\{x_j=0\})
 +\max(\nu\{01\},\mu_i\{x_j=1\})\\
&\hspace{25mm}=\max(m_i,\eta_i).
\end{aligned}
\tag{209.16}
$$

This also is the merged stopped-zero maximum. Comparing only masses
$\eta_i,m_i$ would not justify (209.16).
In $10$, earlier classes are dominated, intermediate classes supply
$u_{nj}$, and the queried class supplies $\eta_j$; the maximum is
$\max(d_{ij},U_{ij})$.
In $11$, earlier classes remain dominated, intermediate classes supply
the complementary pieces $\eta_n-u_{nj}$ and future classes supply
their totals. Its maximum is $\max(h_{ij}+t,Z_{ij})$.
Since $m_i+d_{ij}+h_{ij}=S$, subtracting the anchor gives $D_{ij}$
for both catalogs on this pair.

On early/late $(a,j)$ the early owner $a$ maximizes both split-zero
cells and their rewards sum to $H$. In the other cells the maxima are

$$
\max(Hm_j/S,U_j),\qquad
\max(H(S-m_j)/S,p_b(S-m_j)/S+t,Z_j),\quad b=3-a.
$$

Maximizing over $a$ gives $D_j$. The head contributes $(\mu-t)_+$.
Thus every pair has equal $N/O$ support. Refine every shorter $N$
function into a distinct-pair $N$ function, apply the pair bounds,
and use $O\subset N$; a maximizing pair attains the full value in
$O$. This proves (209.14), including $L=3$ when there is no late pair.

In the last branch of (209.15), $S-m_n>0$ and the multiplier lies
in $[0,1]$. Thus each displayed measure is dominated by $\nu$ and
comparable to $\nu_n$, with exactly the required mass. They coexist
on one carrier: write $\mu_n=f_n\nu$, $0\le f_n\le1$, and on
$\nu(dx)\,du$, $0\le u<1$, mark class $n$ when $u<f_n(x)$.
Overlapping marks are allowed. Their marginal marked measures are
all the $\mu_n$ simultaneously. This auxiliary representation is of
score weights and is not an additional acquisition seed. $\square$

The conditional densities in 205.12 are a special case of (209.15),
but their ordered profile, common terminal and half-density hypotheses
are not assumed in (209.12). Conversely the exact minimum assertion
of 205.12 is not inherited by (209.14).

For extraction from an input $y$, use its actual $\nu$ and choose
$c_a\le\gamma_a$, $\eta_n\le\gamma_n$ subject to (209.12).
Write $E_{\rm lost}=E_y-E\ge0$ and
$R_k=\sum_{n=3}^k(\gamma_n-\eta_n)\ge0$.
The existing residual formula (207.8) reduces exactly to

$$
\Theta_N=\max\left\{0,\max_{3\le k\le L}
 \frac{3R_k-(k-2)E_{\rm lost}}{k+1}\right\}.
\tag{209.17}
$$

Indeed the $o,p$ readings are nonpositive, and the $v_k$ reading
minus the $u_k$ reading is
$2(k-2)(R_k+E_{\rm lost})/((k-1)(k+1))\ge0$.
Only these signs permit removing the $u$ column here.
The residual itself is

$$
-\sum_{a=1}^2(\gamma_a-c_a)(1-b_a)
 +\sum_{n\ge3}(\gamma_n-\eta_n)(b_n-e)-E_{\rm lost}e.
$$

Thus $D_N+\Theta_N\le1$ gives one certificate by (207.10).
Original $\gamma_n$ may exceed $m_n$ or $S$; retained
$\eta_n\le S$ and all losses in (209.17) must still be respected.
Retaining all totals makes the residual zero. Arbitrary original
early $00$ rows are included in $\nu$ before its redistribution.

**Proposition 209.9 (An attained all-length comparison above marginal stock).**
Let $m=L-2\ge4$, $1\le a\le2$, $0\le r\le a-1$.
Give each late word with exactly one one mass $a$, obtaining $\nu$.
Put

$$
S=ma,\quad z=(m-1)a,\quad \mu=z+r,\quad
E=2\mu-S,\quad c_1=c_2=E/2,\quad t=\mu-1,
\quad\gamma_n=\mu\ (n\in I).
\tag{209.18}
$$

Use the early rows of 209.8. Let $Y$ have late correct mass $\mu$
at every $e_n$, and let $V$ instead use
$\mu_n=\nu_n+(r/a)(\nu-\nu_n)$ followed by $R_n$.
Then $Q(Y)=Q(V)$ and

$$
(\Delta_N(Y),\Delta_O(Y))=((m-2)a+1,1),\qquad
(\Delta_N(V),\Delta_O(V))=(1,1).
\tag{209.19}
$$

The value one is the attained minimum at these fixed totals over all
allowed suffixes and early allocations. For $r>0$, every retained
late mass exceeds its marginal stock.

**Proof.** Here $m_j=z,d_{ij}=a,h_{ij}=0$, and $H=\mu\le S$.
Each $\mu_n$ contains $\nu_n$, is dominated by $\nu$, and has mass
$\mu$. For $n<j$, $u_{nj}=\mu-a$ and its complementary piece is
$a$. In an early/late pair with $j<L$, the two remaining maxima are
$\mu,\mu$, using $t+a/2\le\mu$; its excess is one. At the last
label it is $a/2\le1$. Late-pair excesses in (209.14) are one for
$j<L$ and zero for $j=L$, while the head attains $\mu-t=1$.

For $Y$, every late stopped pair has three maxima $\mu,\mu,\mu$,
and all early pairs have support at most $3\mu$. Every late $N$
pair has maxima $(S-2a,\mu,\mu,\mu)$. The anchor is $3\mu-1$,
so (209.19) follows by catalog completion. The head lower bound one
holds for every competitor at these totals, proving the minimum.
An atom is reused fully by $m-1$ class measures; no disjoint-allocation
bound could retain this construction.

This entire quotient family is already in 206.15's clipped-fair region:
$\mu\ge3$, $E-(\mu-2)=2-a+r\ge0$, and $W=3\mu-1$.
The strict raw-support decrease establishes no additional quotient
coverage. $\square$

### 209.4 Retained-credit comparison with the actual original input

**Theorem 209.10 (Full-mass dominated classes and original-table charging).**
For an arbitrary input $y$ of 209.1, let $S>0$, $E\le S$,
$\delta=\Delta_O(y)$ and $\mu=\max_{n\in I}\gamma_n$.
Choose actual separate measures

$$
0\le\rho_n\le\nu_n,\qquad |\rho_n|=\gamma_n.
\tag{209.20}
$$

In particular $\gamma_n\le m_n$ is required; unit $O$ cost does not
by itself imply this condition. Use 209.8 with
$c_a=\gamma_a$, $\mu_n=\rho_n$, $\eta_n=\gamma_n$ and $T=t$,
so $Q(V)=Q(y)$. Reuse its $U_j,Z_j,U_{ij},Z_{ij}$, put
$p_j=S-m_j$, $H=(S+E)/2$, and define

$$
\begin{aligned}
\kappa_{aj}&=\min\left\{t,\frac{\gamma_{3-a}p_j}{S},
                 \left(\frac{Hp_j}{S}+t-\mu\right)_+\right\},\\
D_{\rm early}&=\max_{a=1,2;\ j\in I}
       \left((U_j-Hm_j/S)_+-\kappa_{aj}\right)_+,\\
D_{\rm late}&=\max_{i<j}(U_{ij}-d_{ij}-E)_+,\qquad
D_P=\max(D_{\rm early},D_{\rm late}).
\end{aligned}
\tag{209.21}
$$

Then

$$
\Delta_N(V)=\Delta_O(V)\le\max\{\delta,D_P\}.
\tag{209.22}
$$

Thus $\delta\le1,D_P\le1$ give the same-$Q$ certificate $(V,0)$,
and $D_P\le\delta$ gives comparison at the original budget.
No order of the correct profile, common terminal-zero coordinate or
constant class density is required.

**Proof.** The construction and support identity are the lower-stock
specialization of 209.8, not a second catalog theorem.
Substituting (209.20) into that identity gives the head term
$(\mu-t)_+$, early terms

$$
J_{aj}=(U_j-Hm_j/S)_+
 +\max\{-t,-\gamma_{3-a}p_j/S,Z_j-Hp_j/S-t\},
\tag{209.23}
$$

and late terms
$J_{ij}=(U_{ij}-d_{ij})_++(Z_{ij}-h_{ij}-t)_+-E$.
The original head table forces $(\mu-t)_+\le\delta$.

For a late pair where both positive gains occur, choose winning labels
$k,l>i$. If they are distinct, the single original stopped schedule
$(i,\min(k,l))$, with outputs $0,\min(k,l),\max(k,l)$, earns at
least $m_i+\gamma_k+\gamma_l$.
Since $d_{ij}+h_{ij}=S-m_i$, this bounds
$J_{ij}=U_{ij}+Z_{ij}+m_i-W\le\delta$.
If $k=l$, its two disjoint $\rho_k$ pieces sum to $\gamma_k$;
the original singleton $(i;0,k)$ proves the same bound.
If only the $10$ gain is present use $D_{\rm late}$; if only the
$11$ gain is present use $\mu-t\le\delta$ whenever that gain
is positive. If neither occurs the term is $-E\le0$.

For an early pair set
$g=(U_j-Hm_j/S)_+$, $z=Z_j-Hp_j/S-t$ and
$s_0=\min(t,\gamma_{3-a}p_j/S)$, so $J_{aj}=g+\max(-s_0,z)$.
In the original input put $H_a=\sum_{\Omega_a}(P+C)$.
Their sum is $S+E=2H$, including arbitrary early $00$ rows, so
some $a_0$ has $H_{a_0}\ge H$.
If $g,z>0$ have distinct winning late labels $k,l$, the original
stopped $(a_0,\min(k,l))$ collects at least
$H_{a_0}+\gamma_k+\gamma_l$.
This bounds $J_{aj}=U_j+Z_j-H-t$ by $\delta$.
If the labels coincide use the original singleton $a_0$ and the two
complementary pieces of $\rho_k$. If $g=0,z>0$ use
$J_{aj}\le\mu-t\le\delta$.

Finally if $z\le0$, then $Z_j\le\mu$ gives
$-z\ge\max(0,Hp_j/S+t-\mu)$. Therefore
$\min(s_0,-z)\ge\kappa_{aj}$ and
$J_{aj}\le g-\kappa_{aj}\le D_{\rm early}$.
This uses negative slack in the same table, not an extra positive
budget. Taking the maximum proves (209.22). The preserved $Q$ gives
zero residual in (207.10). $\square$

**Proposition 209.11 (An unordered full-mass relocation family).**
Let $L=6$, $0\le r,d\le1$, and let $x^{(j)}$ be the late word
whose only one is at $j$. Put

$$
\nu=d\left(r\delta_{0000}+2\sum_{j=3}^6\delta_{x^{(j)}}\right),
\quad (\gamma_3,\gamma_4,\gamma_5,\gamma_6)=(5,4,4,5)d,
\quad \gamma_1=\gamma_2=d,\quad t=4d.
\tag{209.24}
$$

Take $P_{01x}=P_{10x}=\nu(x)/2$ and
$C_{01x}=C_{10x}=\nu(x)/(8+r)$. Put late correct masses at $v_j$
to obtain $Y$, and replace them by $(R_j)_*\rho_j$ to obtain $V$,
where $\rho_j=(g_j/(6+r))\nu_j$, $(g_3,g_4,g_5,g_6)=(5,4,4,5)$.
Then

$$
(\Delta_N(Y),\Delta_O(Y))=((2-r)d,d),\qquad
(\Delta_N(V),\Delta_O(V))=(d,d),\qquad Q(Y)=Q(V).
\tag{209.25}
$$

**Proof.** For $d>0$, $S=(8+r)d$, $m_j=(6+r)d$ and each late
pair has cells $((4+r)d,2d,2d,0)$. All full-mass dominations hold,
$E=2d\le S$, and $W=(14+r)d$.
For $Y$, the stopped late maxima are $((6+r)d,4d,5d)$ for $j<6$
and $((6+r)d,5d,4d)$ for $j=6$, each of excess $d$.
In $N$, the first two maxima are $(5d,2d)$, instead of their
merged value $(6+r)d$, adding $(1-r)d$.
An early/late pair has first-zero total $(10+r)d/2$ and remaining
maxima $5d,5d$, hence excess $(1-r/2)d\le d$.
The head excess is $d$, so these bounds and catalog completion give
the input costs.

For $V$, domination fixes $00,01$ at their pair baselines.
Intermediate zero rewards are at most
$5(4+r)d/(6+r)\le4d$, and intermediate one rewards are at most
$10d/(6+r)\le4d$.
Thus its late-pair excess is $d$; its early/late maxima are no larger
than those of $Y$, and its head still attains $d$.
This proves the output costs. Equivalently (209.21) has
$D_{\rm late}=d$, $\kappa_{aj}=2d/(8+r)$ and
$D_{\rm early}\le(1-r/2)d$.
At $d=0$ all scores vanish directly, without invoking $S>0$.
The endpoints $r=0,1$ are included; strictness holds for $d>0,r<1$.
Padding with constant-one inactive coordinates does not increase the
number of active labels. No exclusion from the whole earlier signed
or convex closure follows from this strict relocation. $\square$

### 209.5 Unary-preserving relocation inside mixed early reward carriers

**Definition 209.12 (The retained early score and matching condition).**
For any input $y$ of 209.1, let $Z$ retain all its pair rows, early
correct rows and $T=t$, deleting only the late correct rows.
For $i<j$ let $g_{ij,b}(\ell)$ be the reward of $Z$ at label
$\ell$ in the cell $w_i=0,w_j=b$. Impose the condition

$$
\operatorname*{argmax}_{\ell}g_{ij,0}(\ell)
 \cap\operatorname*{argmax}_{\ell}g_{ij,1}(\ell)\ne\varnothing
 \quad\text{for every }i<j.
\tag{209.26}
$$

This is a condition on the actual early score, including its $00$
prefix rows. Only labels $0,1,2$ can have nonzero rewards there.
Define three measures on the full late cube by

$$
\begin{aligned}
\zeta_0(x)&=\sum_{w|_I=x}P_w,\\
\zeta_a(x)&=\sum_{w\in\Omega_a,\ w|_I=x}(P_w+C_w)
                      \quad(a=1,2).
\end{aligned}
\tag{209.27}
$$

For $n\ge3$, let $\omega_{r,n}$ be the suffix projection onto
$n+1,\ldots,L$ of $\zeta_r|_{\{x_n=0\}}$, $r=0,1,2$.
Let $\mu_n(v)=C_{1^{n-1}0v}$ be the original correct suffix measure,
and put $c_{nj}=\mu_n\{v_j=0\}$ for $j>n$.
A permitted replacement consists of a suffix measure $\sigma_n$ and
coefficients $\tau_{n,r}\ge0$, $\sum_r\tau_{n,r}=1$, such that

$$
0\le\sigma_n\le\sum_{r=0}^2\tau_{n,r}\omega_{r,n},\qquad
|\sigma_n|=\gamma_n,\qquad
\sigma_n\{v_j=0\}=c_{nj}\quad(j>n).
\tag{209.28}
$$

All classes are replaced simultaneously, leaving the entire $Z$
unchanged; no sum of the $\sigma_n$ across labels is restricted.
For a finite suffix measure $\omega$ write

$$
\mathcal Z(\omega)=
 \left\{\int f(v)(1,X(v))\,d\omega(v):0\le f\le1\right\},
\quad X_j(v)=\mathbf1_{v_j=0},\qquad
\mathcal D_n=\operatorname{conv}\bigcup_{r=0}^2\mathcal Z(\omega_{r,n}).
\tag{209.29}
$$

At $n=L$ the suffix has one empty word and there are no unary
coordinates. Zero carrier masses are permitted.

**Theorem 209.13 (Same-schedule support decrease and exact carrier cuts).**
Suppose (209.26) holds and every vector
$(\gamma_n,(c_{nj})_{j>n})$ belongs to $\mathcal D_n$.
There exist simultaneous replacements (209.28); the resulting score
$V$ satisfies, for every increasing pair $s$,

$$
B_N^s(V)=B_O^s(V)\le B_O^s(y).
\tag{209.30}
$$

Empty and singleton supports are unchanged. Hence
$Q(V)=Q(y)$, $W_V=W_y$ and
$\Delta_N(V)=\Delta_O(V)\le\Delta_O(y)$.
A unit-$O$ input satisfying these hypotheses has certificate $(V,0)$.
For this declared matching route, membership in $\mathcal D_n$ is
exactly the system of all real signed inequalities

$$
a_0\gamma_n+\sum_{j>n}a_jc_{nj}
 \le\max_{r=0,1,2}\int
       \left(a_0+\sum_{j>n}a_jX_j(v)\right)_+\,d\omega_{r,n}(v).
\tag{209.31}
$$

Separately, (209.26) is exactly equality of the split and merged
zero-branch supports for $Z$. These conditions are not asserted
necessary for arbitrary $E_N$ membership.

**Proof.** First suppose (209.28) is given. Fix $i<j$ and a late
class $n\le i$. For $n<i$ both queried bits are preserved suffix
coordinates; for $n=i$ its first queried bit is fixed zero.
Domination by the projected mixture in (209.28) bounds this class's
reward in every applicable cell by the same convex combination of
$Z$'s three label rewards in that cell. The extra restriction
$x_n=0$ can only decrease those rewards. A convex combination of
three label rewards is at most their maximum.
Thus no relocated class $n\le i$ can exceed the $Z$ maximum.
Classes $n>i$ never occur in the first-zero branch.
The maxima of $V$ in $00$ and $01$ are therefore precisely those
of $Z$. Their sum equals the merged $Z$ maximum by (209.26).
The same domination also holds on the merged cell, giving equality
of the $N/O$ contributions there.

In $10$ and $11$ the classes $n\le i$ remain dominated by $Z$.
For $i<n<j$ their complementary rewards are $c_{nj}$ and
$\gamma_n-c_{nj}$; for $n=j$ they are $\gamma_j,0$;
for $n>j$ they are $0,\gamma_n$.
All these numbers agree with those in the corresponding cells of the
original $y$. The $Z$ rewards are also unchanged. Thus each new
maximum is at most the original stopped maximum in that same cell,
proving (209.30). If $i=1$ or $2$, there is no late $n\le i$,
and the rest of the argument is unchanged.
Empty and singleton label rewards depend only on the preserved class
totals and unary marginals, so their supports agree exactly.
Pair equality and catalog completion give the claimed full equality
and inequality. Totals preserve $Q,W$, and (207.10) gives the
certificate without any positive residual.

It remains to prove existence and the exact cuts. If
$\sigma\le\sum_r\tau_r\omega_r$, define the atomwise density
$f=\sigma/(\sum_r\tau_r\omega_r)$, taking zero at a zero
denominator. Then $0\le f\le1$ and
$\sigma=\sum_r\tau_r(f\omega_r)$, so its moment vector is in
$\operatorname{conv}\bigcup_r\mathcal Z(\omega_r)$.
Conversely a convex combination of measures
$\sigma_r\le\omega_r$ is dominated by the corresponding carrier
combination. Convexity within each $\mathcal Z(\omega_r)$ permits
grouping repeated terms with the same $r$. This proves the equivalence
with (209.28), including zero carriers. The choices for distinct $n$
are compatible because they share no disjoint-allocation constraint.

Each $\mathcal Z(\omega)$ is the linear image of a finite box, so
it is compact and convex. Its support in direction $(a_0,a_j)$ is
the integral in (209.31): choose $f=1$ where the affine expression
is positive and $f=0$ where it is negative. The support of the convex
hull is the maximum, not the sum, of the three supports.
For completeness, if a vector $x$ is outside this compact convex set,
let $z$ minimize its distance to the set. For every point $y$ in the
set, differentiating the squared distance along $z+t(y-z)$ at
$t=0+$ gives $\langle x-z,y-z\rangle\le0$.
The direction $x-z$ strictly separates $x$, since
$\langle x-z,x-z\rangle>0$. Thus all signed cuts are sufficient.
This is ordinary finite convex support and separation; the finite
polytope and linear-image framework is the one in Volker Kaibel,
[*Basic Polyhedral Theory*, Theorem 8 and §1.6](https://arxiv.org/html/1001.2161v1).
Here the box coordinates are the actual suffix-atom densities, and the
linear map consists of their mass and unary zero moments. This
classical step supplies neither common carrier existence nor the
acquisition comparison; those are the explicit hypotheses and
same-cell argument above.

Finally for any two finite reward vectors $u,v$,
$\max u+\max v=\max(u+v)$ exactly when their maximizing index
sets intersect. If equality holds, a maximizer of $u+v$ must attain
both individual maxima; the converse is immediate. Applied to the
actual $g_{ij,b}$ this proves the precise claim about (209.26).
$\square$

A direct sufficient construction inside (209.28) uses the same finite
moment map. Choose one mixed carrier $\omega$ of mass $M>0$;
under $\omega/M$ put $p=\mathbb E X$,
$\Sigma=\mathbb E[(X-p)(X-p)^\mathsf T]$ and
$d=c-\gamma p$. If

$$
M\Sigma v=d,\qquad
0\le f(x)=\gamma/M+v\mathbin{\cdot}(X(x)-p)\le1
 \quad\text{on every actual carrier atom},
\tag{209.32}
$$

then $\sigma=f\omega$ has mass $\gamma$ and moment vector $c$:
integrating gives $\int f\,d\omega=\gamma$ and
$\int Xf\,d\omega=\gamma p+M\Sigma v=c$.
For nonsingular $\Sigma$ the pointwise condition is exactly
$-\gamma\le d^\mathsf T\Sigma^{-1}(X-p)\le M-\gamma$.
If $0<\gamma<M$ and $\Sigma$ is positive definite, finiteness of
the support and strict slack at $d=0$ give a neighborhood of
$c=\gamma p$ satisfying it. A singular covariance still requires
the displayed linear equation and pointwise bounds, not an inverse.
At $M=0$ only the zero vector is permitted. These are sufficient
conditions on an actual carrier; covariance positivity alone is not
a substitute for (209.28).

**Corollary 209.14 (Early zero-zero rows and the remaining obstruction).**
Let one probability measure $\kappa$ on all late bits and six
nonnegative numbers $a,b,c,u,v,w$ specify the early rows by

$$
\begin{array}{lll}
P_{00x}=a\kappa(x),&P_{01x}=b\kappa(x),&P_{10x}=c\kappa(x),\\
C_{00x}=u\kappa(x),&C_{01x}=v\kappa(x),&C_{10x}=w\kappa(x).
\end{array}
\tag{209.33}
$$

Keep arbitrary $t$ and arbitrary late correct rows. Condition (209.26)
holds. With $H=\max(a+b+c,a+b+u+v,c+w)$ and
$\bar\kappa_n$ the suffix projection of
$\kappa|_{\{x_n=0\}}$, the matching region is exactly
$\mathcal D_n=\mathcal Z(H\bar\kappa_n)$.
In the full input family, any unit-$O$ score with $Q(y)\notin E_N$
must fail (209.26) or at least one signed cut (209.31).
At $E=0$, (209.26) is automatic and the cuts reduce to the single
actual pair carrier $\omega_{0,n}$.

**Proof.** For a late first query, the three early label rewards are
$a+b+c,a+b+u+v,c+w$ times the same $\kappa$ cell mass. A largest
coefficient maximizes both split cells.
For first query 1, label 1 wins both cells. For first query 2 followed
by a late query the coefficients are $a+c,a+u,c+w$, again with the
same factor. Pair $(1,2)$ has label 1 maximizing both first-zero
pieces. This proves (209.26) even with nonzero early $00$ rows.
The three carriers are scalar multiples of $\bar\kappa_n$ and the
largest contains the other two, giving the stated moment box.
This common-factor calculation reuses the mechanism of 198.2 only
on the early score; the original late rows need not have any common
Markov suffix law. The nonmembership implication is the contrapositive
of 209.13. At $E=0$ nonnegativity deletes early correct rows, zero
then dominates every early-only reward, and
$\zeta_1,\zeta_2\le\zeta_0$. This proves both simplifications.
Failure of a cut is failure of this matching route, not proof of
nonmembership. $\square$

**Proposition 209.15 (Strict matching and its boundary).** There are
unary-preserving replacements (209.28) that reduce complete $N$
support, and the matching conditions can fail for scores already of
zero cost in both catalogs.

**Proof.** For the strict example let $L=6$. Give each late word
$ab01$ and $ab10$, $a,b\in\{0,1\}$, pair-projection mass one,
and lift it equally to early prefixes $01,10$. Thus $S=8$.
Take $t=2$, no early correct rows, and the only late correct rows

$$
C_{110000}=C_{110011}=1,\quad
C_{110100}=C_{110111}=1/2,\quad
C_{111000}=C_{111011}=3/2.
\tag{209.34}
$$

Replace them by

$$
C'_{110001}=C'_{110010}=1,\quad
C'_{110101}=C'_{110110}=1/2,\quad
C'_{111001}=C'_{111010}=3/2.
\tag{209.35}
$$

Both have late totals $(3,3,0,0)$, $E=0$ and $W=10$.
The new class 3 takes full pair-carrier density when $x_4=0$ and
half when $x_4=1$; class 4 takes three quarters of its carrier.
They are simultaneously dominated, and every unary correct marginal
is unchanged. In particular $c_{34}=2$, whereas constant conditional
density would give $3/2$. The common maximizer is label zero.

All empty and singleton supports are $10$. Pairs
$12,13,14,23,24,34$ have support $11$ in both catalogs for both
scores; pairs $15,16,25,26,35,36,45,46$ have support $10$.
For example pair $34$ has $N$ maxima $(2,2,3,4)$, and early/3
or early/4 has first-zero contribution $4$ and other maxima $3,4$.
The remaining pair $56$ has original $N$ maxima
$(3/2,4,4,2)$ and new maxima $(0,4,4,2)$; the merged first-zero
maximum is $4$ in both scores, so both stopped supports are $10$.
The other listed pair values follow by their preserved unary rewards,
at most $3/2$ in those suffix cells. These exhaust all pairs.
Thus the input excesses are $(3/2,1)$ and the output excesses $(1,1)$.
This changes second-order correct correlations, unlike the
pair-moment compression of 206.5, which preserves both supports.
Its quotient is already in the old fair region, using 203.6 with
$\kappa_f=4,\tau=2$, so no new quotient coverage is implied.

For a retained-credit example above pair stock, take $L=4$ and

$$
P_{0100}=2/3,\quad C_{0100}=2/3,\quad
C_{1100}=1,\quad C_{1110}=1/3,\quad t=1/3.
\tag{209.36}
$$

Here $m_3=2/3<\gamma_3=1$, but $\zeta_1$ has mass $4/3$
at late $00$, dominating the required class-3 row and class-4 suffix.
The early common-maximizer condition holds. The head has support
$7/3$ and pair $34$ has support $2$; pairs $13,14$ have support
$8/3$, and pairs $23,24$ have support $5/3$, with the same values
in both catalogs.
The anchor is $5/3$, giving both costs one.
This distinguishes mixed early reward stock from pair stock alone.
At a fixed carrier, constant-density conditional measures are contained
in arbitrary dominated measures, which are contained in mixed-carrier
measures by selecting $r=0$. Equations (209.34)–(209.36) make these
representation inclusions strict. Original unary matching remains an
additional hypothesis, so these are not blanket inclusions of the
input domains of earlier conditional theorems.

Finally let $L=5$, $\nu_{001}=\nu_{010}=1$, balanced early lifts,
$C_{11011}=1$, and $t=1$, all other correct rows zero.
The threshold cutoffs $a_{34}=a_{35}=1$ in 203.2 put the whole
class-3 row at suffix $11$ and give both costs zero:
$m_3=2,m_4=m_5=1$, $\kappa=0$ and $t\ge\mu=1$.
But the actual class-3 pair carrier has suffix support $\{01,10\}$.
In (209.31) choose $(a_0,a_4,a_5)=(1,-1,-1)$.
The desired moment side is one and every carrier support side is zero.
So no permitted unary-preserving replacement exists for that class.
Conversely its half-density conditional row on $01,10$ is dominated
but is not this threshold row. A route obstruction can therefore occur
inside the old zero-cost region. $\square$

**Definition 209.16 (Suppliers, overlap and the original unresolved comparison).**
The threshold words in 209.2 and 209.5 belong to 203.2; the actual
subset carrier in 209.6 belongs to 201.2 and 207.4.
The $E=0$ equal-cell minimum is included once in 209.3, with 207.17
as its bounded-profile subcase. Formula (209.14) supplies the catalog
identity used by 209.10; that theorem's additional statement is the
comparison to the actual original input with retained early slack.
The finite support-box argument in 209.13 is classical convex analysis;
the additional relation is the simultaneous same-schedule decrease
under exact carrier and unary matching. These are derivations for the
specified score classes, without a claim of literary priority or
exhaustive exclusion of older consequences.

Existing signed and convex certificates still apply to the overlapping
families. For the mixed-product strip
$0<d\le1$, $t\ge d$, $d\le z\le\sqrt{td}$,
$E=t-z$, $S=t+2z+d$, $T=t$, $0\le\gamma_j\le t+d$,
the fair endpoint of 206.15 at scale $d$ and the product endpoint
207.5 with $s=t$, $c=t-\sqrt{td}$ interpolate at
$\lambda=(z-d)/(\sqrt{td}-d)$ when $t>d$; at $t=d$ the fair
endpoint suffices. More explicitly, write $\gamma_a=\alpha_a(t-z)$
with $\alpha_1+\alpha_2=1$; at $t=z$ choose any such split.
The product endpoint uses $c_a=\alpha_a(t-\sqrt{td})$ and the
fair endpoint has zero early totals. The input quotient is affine
in $z$, and the fair-endpoint residual is nonpositive by (207.8).
This is reuse of convex support and the signed hull.
For the three-leading-class family
$\gamma_3=\gamma_4=\gamma_5=\mu\ge1$,
$0\le\gamma_j\le1$ thereafter and $W\ge4\mu-1$, the old
three-class shared-terminal block of 201.2–201.3 at $s=\mu-1$
has zero cost, and (207.8) gives the residual allowance
$((L-2)/(L-1))(1-E)_+$. The block is zero when $\mu=1$.

For the terminal box $L\ge8$, $E=8$, $S=50$, $T=20$,
$\gamma_L=21$ and $0\le\gamma_j\le19$ before $L$, use 207.5
at $d=0,s=19,c_a=\gamma_a$, retaining late totals except
$\eta_L=19$. Its product measure has mass $900/19$, zero probability
$19/30$ and pair cells $(19,11,11,121/19)$.
The early pair coefficients are $(19-\gamma_a)/30$, not a forced
equal split; they apply to every $\gamma_1+\gamma_2=8$.
Its anchor is $1413/19$, cost zero, and (207.8) gives residual
$2b_L-(107/19)e$ with exact charge $2/(L-1)$.
These are parameter applications of existing suppliers, not separate
new theorems or evidence of a new quotient region. The old support
and minimum statements for those families remain valid.

The original countable prime source, static replies, unchanged consumer
and original nonatomic targets remain exactly 207.1. The marked laws
(207.2) are separately selected on the full measurable tape carrier.
Their amplitudes are arbitrary positive monotone sequences tending
to zero. All Boolean words, multiple-zero words, output labels, negative
singleton demands, and the independent pair-event row (207.3) remain.
An auxiliary zero score or an $e=0$ hull vertex does not replace the
actual positive tails.

Only an actual normalized finite probability-vector configuration
satisfying every event row may be supplied to
[109.1 and 110.2](KBONACCI_SELF_CALIBRATING_ACQUISITION_RESOURCES_CONTINUATION.md).
The former uses the degree-at-most-two probability-vector domain and
$c\ge H$; the scalar bound $\beta\le1$ in its displayed form is
redundant under that normalization, as in 108.4. Neither criterion
applies to unnormalized score weights.
The latter's necessary direction retains arbitrary-address,
full-carrier competitors through the countable common seed event,
finite source witnesses and compact finite-catalog limit. Its sufficient
direction selects the entire schedule and table before replies by a
fixed partition of one source-independent uniform seed. Two class
configurations may use different partitions of that same seed and a
common refinement, without identical seedwise outputs.
Advice remains zero, handoff actually finite, and the hard bound counts
at most two actual requests, including ignored and repeated requests.
$N$ obtains its preselected replies; $O$ preselects an increasing
schedule and stops at its first queried zero or exhaustion.
No address, depth, runtime, expected-count or source-law proxy is used.

At the actual active length $L_a$ of 207.1, every actual $n>L_a$
still has the exact TV error
$\max\{1-p_{1^{L_a}}(0),a_n\}$ in (207.51).
The all-source bound therefore retains equality at the closed cap,
all vanishing tails and the existing small-active-length cases.
This transport is a supplier for feasible probability configurations;
none of the support-maximizing tables or auxiliary carrier measures
above is thereby a feasible acquisition.

The universal implication (207.52) remains unresolved. The fixed-data
minima do not force a general input to have equal pair marginals;
(209.12) and (209.17) do not supply a universally affordable selection;
(209.20) still requires full mass below actual marginal stock;
and (209.26), (209.31) can fail even inside the feasible region.
No theorem here places every arbitrary-credit, nonconstant-capacity,
over-stock input inside the union of these constructions with one
budget. Strict support relocation alone gives neither new quotient
coverage nor exclusion from the full old convex, signed and nonzero
zero-cost closure. The alternative original common-seed $N_2$
attainer with a uniform lower certificate against every original
$O_2$ competitor is also absent. The exact-law obstruction of 112.2
continues to allow a different stopped law at the same cap.

## 追加锚（本行以下为增补区）
