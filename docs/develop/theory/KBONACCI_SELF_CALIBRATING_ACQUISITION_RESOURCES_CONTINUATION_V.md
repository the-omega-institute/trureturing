# Self-calibrating acquisition resources: residual extensions and coupled endpoint allocations

## 172. Finite auxiliary cores within the original acquisition contract

**Definition 172.1 (Actual targets and the hard-two classes).** Retain
[Definition 110.1 and Theorem 110.2](KBONACCI_SELF_CALIBRATING_ACQUISITION_RESOURCES_CONTINUATION.md#110-exact-closed-cap-transport-on-the-original-countable-source)
and [Acquisition Resources, Definition 90.1](KBONACCI_SELF_CALIBRATING_ACQUISITION_RESOURCES.md#90-adaptive-preselected-and-increasing-first-zero-stop-acquisitions).
Thus the actual labeled source is

$$
X=\{(s,g):s\text{ prime},\ g\in\mathbb Z,
       \lceil F_s/10\rceil\le g\le\lfloor F_s/5\rfloor\},\qquad
N(s,g)=1+F_sg,
$$

with static answers $b_i(x)=\mathbf1_{p_i\mid N(x)}$ and finite actual
first absence $n(x)=\min\{i:b_i(x)=0\}$. The original Fibonacci numbers
and ordered primes have the meanings in (110.1). Every finite answer
pattern has an actual witness, as supplied there by Boundaries,
Theorem 35.2. The original measurable carrier, consumer and nonatomic
targets remain those of Acquisition Resources, Definition 73.1.
The distinct original marks are $\theta_j=(B_1,1/(j+2))$, $j\ge0$.
For an entire sequence

$$
1\ge a_1\ge a_2\ge\cdots>0,\qquad a_i\longrightarrow0,
$$

the separately selected targets are
$\lambda_x^a=(1-a_{n(x)})\delta_{\theta_0}+a_{n(x)}\delta_{\theta_{n(x)}}$.
Error is the uniform supremum of TV over $X$.

There is zero advice and one source-independent common seed, with
actual sourcewise almost-sure finite handoff. An $N_2$ rule preselects
at most two actual requests and obtains their replies, including
repeated requests. An $O_2$ rule preselects an increasing schedule of
at most two actual requests and stops at its first queried zero or
exhaustion. Original competitors retain arbitrary addresses and may
output any tape in the full carrier. No probability law on sources or
additional source observation is included. The selected marked targets
are distinct from the unchanged original nonatomic targets.

**Definition 172.2 (A finite non-strict auxiliary core).** For an integer
$m\ge2$, write $B_m=\{0,1\}^m$ and $J_m=\{0,\ldots,m\}$.
Let $e_j$ denote the unit probability vector at label $j$.
A core consists of numbers and a stopped probability-vector kernel

$$
1\ge A_1\ge\cdots\ge A_m\ge e_0>0,\qquad q\in\mathscr O_m,
$$

where $e_0$ in this inequality is a scalar cap, distinguished from the
unit vector $e_0$ by context. For every word $b\in B_m$ whose first
zero is $n$, require all three inequalities

$$
\begin{aligned}
q_b(0)&\ge1-A_n-e_0,\\
q_b(n)&\ge A_n-e_0,\\
q_b(0)+q_b(n)&\ge1-e_0,
\end{aligned}
\qquad q_{1^m}(0)\ge1-e_0.
\tag{172.1}
$$

Here $\mathscr O_m$ is the complete finite stopped class of Definition
108.1, equivalently the coefficient region of Theorem 109.1. The rows
are the supplied two-point TV criterion (110.6). The core may have
$A_m=e_0$, need not attain its cap, and need not be the active prefix
of an infinite target sequence. In particular the scalar $e_0$ is not
an assertion of optimality for $q$.

**Definition 172.3 (Subset branches and residual scales).** Fix integers
$L>m\ge2$ and finite residuals

$$
g_{m+1}\ge\cdots\ge g_L\ge0,\qquad g_{L+1}=0.
$$

For $m<h\le L$, let $P_h$ be the hard-two subset branch supplied by
[Acquisition Resources, Theorem 87.1, at count two](KBONACCI_SELF_CALIBRATING_ACQUISITION_RESOURCES.md#87-unit-leading-plateaus-and-unbounded-address-to-count-ratios).
It chooses uniformly a three-subset of $1<\cdots<h<\ast$, where
$\ast$ means output label zero. It preselects the first two numerical
labels of the subset, stops at a queried zero and emits that label,
or on positive exhaustion emits the last selected label without
querying it. There are exactly two numerical queried labels even when
$\ast$ is selected, since $\ast$ is last. Its kernel is regarded as a
kernel on $B_L$ with output labels in $J_L$.

Set

$$
\begin{aligned}
w_h&=\frac{h+1}{3}(g_h-g_{h+1}),&
W&=\sum_{h=m+1}^Lw_h,\\
c_h&=\frac{h-2}{h+1},&
E&=\sum_{h=m+1}^Lw_hc_h,&r&=1-W.
\end{aligned}
\tag{172.2}
$$

The residual construction assumes $W\le1$. It uses a single mixture
of the whole core and whole subset tables, rather than a separate
mixture for each word or TV row.

## 173. Residual extension at every finite auxiliary length

**Theorem 173.1 (All-word extension with an exact uniform cap).** For
every core of Definition 172.2 and residuals of Definition 172.3 with
$W\le1$, put

$$
\begin{aligned}
\varepsilon&=re_0+E,\\
a_i&=rA_i+W &&(1\le i\le m),\\
a_i&=\varepsilon+g_i &&(m<i\le L),\\
p_b&=r q_{(b_1,\ldots,b_m)}+\sum_{h=m+1}^Lw_hP_{h,b}.
\end{aligned}
\tag{173.1}
$$

Append any positive nonincreasing vanishing actual tail with
$a_{L+1}\le\varepsilon$. Then $0<\varepsilon\le1$ and the entire
sequence has the order and positivity of Definition 172.1.
There is an original $O_2$ acquisition with this kernel at every actual
low word and exact uniform error $\varepsilon$, and its same-seed
$N_2$ completion has the identical law. The finite kernel belongs to
$\mathscr C_L$ of Definition 108.2. If $g_L>0$, its actual active
length at this cap is exactly $L$.

For each actual source with $m<n(x)\le L$, its error is exactly
$\varepsilon$, including every multiple-zero suffix. On an actual
tail source $n>L$, its error is precisely

$$
\max\{t_{\rm tail},a_n\},\qquad
t_{\rm tail}=r(1-q_{1^m}(0))+E\le\varepsilon.
\tag{173.2}
$$

All actual tails have error $\varepsilon$ if and only if

$$
r\bigl[q_{1^m}(0)-(1-e_0)\bigr]=0.
\tag{173.3}
$$

Thus core tail-row tightness suffices, and $r=0$ also suffices. Exact
uniform attainment does not assert that this extension cap is optimal.

**Proof.** Summation by parts in the finite residual list gives

$$
\begin{aligned}
W&=\frac{(m+2)g_{m+1}+\sum_{i=m+2}^Lg_i}{3},\\
E&=\frac{(m-1)g_{m+1}+\sum_{i=m+2}^Lg_i}{3},\\
W-E&=g_{m+1},\qquad r+W=1,\\
\sum_{h=n}^L\frac{3w_h}{h+1}&=g_n\quad(m<n\le L).
\end{aligned}
\tag{173.4}
$$

All weights are nonnegative. If $g_{m+1}>0$, then $E>0$ because
$m\ge2$. Otherwise all residuals vanish, $W=E=0$, and
$\varepsilon=e_0>0$. Moreover

$$
\varepsilon=1-g_{m+1}-r(1-e_0)\le1.
\tag{173.5}
$$

The head is ordered by the $A_i$, the late list by the $g_i$, and

$$
\begin{aligned}
a_m-a_{m+1}&=r(A_m-e_0)\ge0,\\
a_i-\varepsilon&=r(A_i-e_0)+g_{m+1}\ge0\quad(i\le m).
\end{aligned}
\tag{173.6}
$$

Head amplitudes are at most $r+W=1$. Every late amplitude is at most
$a_m$ and at least $\varepsilon>0$. The permitted actual tail preserves
the order, is positive and vanishes. If $g_L>0$, all first $L$
amplitudes exceed $\varepsilon$, and every later amplitude is at most
$\varepsilon$, proving the asserted active length.

The subset identities of Theorem 87.1 apply word by word. If the actual
first zero is $n\le h$, the branch emits $n$ if and only if its selected
subset contains $n$, hence

$$
P_{h,b}(n)=\frac{3}{h+1}.
\tag{173.7}
$$

All preceding selected labels are positive, whether $n$ is queried or
is the final unqueried label. Later zeros cannot change this equivalence.
If $k_h(b)$ is the number of positive bits among the first $h$, the base
probability is

$$
P_{h,b}(0)=\frac{\binom{k_h(b)}2}{\binom{h+1}3}.
\tag{173.8}
$$

Indeed base emission requires selecting $\ast$ and two positive
numerical labels. Consequently the outside-$\{0,n\}$ mass is at most
$c_h$. If $n>h$, all first $h$ bits are positive; (173.8) is
$3/(h+1)$, the correct mass is zero and the outside-pair mass is
exactly $c_h$. These are applications of the subset supplier, used here
inside the new residual mixture.

Fix a word with first zero $n\le m$. Its target vector satisfies
$\eta_n^a=r\eta_n^A+We_n$, since $a_n=rA_n+W$.
For the same mixture at that word, (172.1), (173.7) and (173.4) give

$$
\begin{aligned}
p_b(n)&\ge r(A_n-e_0)+W-E=a_n-\varepsilon,\\
p_b(0)+p_b(n)&\ge r(1-e_0)+W-E=1-\varepsilon,\\
p_b(0)&\ge r(1-A_n-e_0)=1-a_n-\varepsilon+E.
\end{aligned}
\tag{173.9}
$$

The second inequality uses the independent pair row of the core and
the subset correct mass. It is not deduced by adding the two singleton
lower bounds. All three required TV rows hold for every suffix.

Next fix $m<n\le L$. The core sees $1^m$ and cannot emit $n$.
Every subset branch with $h<n$ also cannot emit it. Thus

$$
p_b(n)=\sum_{h=n}^L\frac{3w_h}{h+1}=g_n=a_n-\varepsilon.
\tag{173.10}
$$

The core's outside-pair mass is at most $re_0$, and the total subset
outside-pair mass is at most $E$. Therefore

$$
1-p_b(0)-p_b(n)\le\varepsilon,\qquad
p_b(0)\ge1-\varepsilon-g_n=1-a_n.
\tag{173.11}
$$

These prove the pair row and the required base row independently.
The correct-row deficit $a_n-p_b(n)=\varepsilon$ gives a TV lower
bound $\varepsilon$, while all three rows give the upper bound. This
proves equality on every such word, even when $g_n=0$.

At $1^L$ the base probability is

$$
p_{1^L}(0)=r q_{1^m}(0)+g_{m+1},\qquad
1-p_{1^L}(0)=r(1-q_{1^m}(0))+E=t_{\rm tail}.
\tag{173.12}
$$

This satisfies the all-positive base row. At any actual $n>L$, all
queried low answers are positive and no tail mark is emitted. The
exact original-carrier identity (110.9) gives (173.2), including the
closed endpoint $a_{L+1}=\varepsilon$. The difference
$\varepsilon-t_{\rm tail}$ is the left side of (173.3). If it vanishes,
every actual tail error is $\varepsilon$. If it is positive, vanishing
of $a_n$ supplies later actual first absences with $a_n<\varepsilon$,
whose errors are strictly smaller. Actual witnesses exist for each
such finite first-absence pattern. Thus (173.3) is exactly the
condition for equality on all tails. A particular tail can still have
error $\varepsilon$ when its amplitude equals the cap.

Partition one source-independent $U\in[0,1)$ into intervals of masses
$r,w_{m+1},\ldots,w_L$, omitting zero masses. The finite complete-table
realization of $q$, supplied by Definition 108.1 and Proposition 140.3,
and the finite categorical realization of each subset branch subdivide
their intervals. Rescaling within an interval fixes its entire schedule
and terminal table before any answers. The rule queries the actual
low primes, stops as required and hands the chosen $\theta_j$ to the
unchanged consumer on the same source. Every branch is measurable and
finite at every actual source and seed, with zero advice and at most
two actual requests. Only the selected branch is executed.

Using the identical $U$, the $N_2$ rule obtains the whole preselected
schedule and reconstructs the same stopped cell and tape. Ignored
replies are counted. This is exactly Proposition 90.2's completion,
without a second source trajectory. Theorem 109.1 puts this explicitly
stopped probability kernel in $\mathscr C_L$. Theorem 110.2 supplies
the exact original closed-cap correspondence when $L$ is active,
including its arbitrary-address/full-carrier necessity for competitors.
When some $g_i$ vanish, $L$ is only an auxiliary length; the direct
all-source argument above still applies without asserting it is active.

An actual source with first absence $m+1$ exists, and (173.10) forces
its error to be $\varepsilon$. All sources have error at most that
number. This proves exact uniform error even for a slack core.
At $W=1$, the core interval is simply omitted and the head amplitudes
are all one; there is no division or limit sampler. At $W=0$, the
rule is the core, the late amplitudes equal $e_0$, and actual late
first absences still force uniform error $e_0$. Residual plateaus and
zero terminal weights require only omission of empty intervals.
$\square$

## 174. Recognition, excess conservation and a non-strict boundary

**Proposition 174.1 (Sufficient residual recognition).** Let an original
sequence have active length $L>m\ge2$ at a positive cap $\varepsilon$.
Set $g_i=a_i-\varepsilon$ for $m<i\le L$, and define $W,E$ by
(173.4). If $W<1$ and $\varepsilon>E$, put

$$
A_i=\frac{a_i-W}{1-W}\quad(i\le m),\qquad
e_0=\frac{\varepsilon-E}{1-W}.
\tag{174.1}
$$

These numbers satisfy $1\ge A_1\ge\cdots\ge A_m\ge e_0>0$.
If there is a finite stopped core satisfying all rows (172.1), the
original sequence has an $O_2$ attainer, and its same-seed $N_2$
completion, of exact uniform error $\varepsilon$. At the separate
$W=1$ endpoint, $\varepsilon=E$ and $a_i=1$ for $i\le m$ suffice
for the direct core-free construction. Neither criterion asserts that
$N$ feasibility is preserved by residual subtraction.

**Proof.** Order and $A_1\le1$ follow by subtracting the same $W$ and
dividing by $1-W>0$. Using $W-E=g_{m+1}$ gives

$$
A_m-e_0=\frac{a_m-\varepsilon-g_{m+1}}{1-W}
        =\frac{a_m-a_{m+1}}{1-W}\ge0.
$$

Thus positivity and every non-strict core inequality hold, without a
strict original join. Substitution into (173.1) reconstructs the
given head, cap and late amplitudes exactly; its actual tail is already
permitted. Apply Theorem 173.1. If $W=1$, the stated direct endpoint
reconstructs the same data with no core contribution and no division
by $1-W$. Failure of these sufficient conditions has no implication
of original $N$ or $O$ infeasibility. $\square$

**Proposition 174.2 (The exact excess identity).** For the construction
of Theorem 173.1, define

$$
D_{\rm core}=\sum_{i=3}^m(A_i-e_0),\qquad
D_3(a,\varepsilon)=\sum_{i\ge3}(a_i-\varepsilon)_+,
$$

with $D_{\rm core}=0$ when $m=2$. Then

$$
\begin{aligned}
D_3(a,\varepsilon)&=rD_{\rm core}+3E,\\
D_3(a,\varepsilon)-3\varepsilon
  &=r(D_{\rm core}-3e_0),\\
1-a_i&=r(1-A_i)\quad(i\le m).
\end{aligned}
\tag{174.2}
$$

**Proof.** The head residuals in (173.6) and the late residuals $g_i$
are nonnegative, and every actual tail residual is zero. Their sum is

$$
rD_{\rm core}+(m-2)g_{m+1}+\sum_{i=m+1}^Lg_i
=rD_{\rm core}+(m-1)g_{m+1}+\sum_{i=m+2}^Lg_i.
$$

Equation (173.4) identifies the last two terms with $3E$.
Subtract $3(re_0+E)$ to obtain the second equality; $r+W=1$
gives the third. Thus positive core excess survives precisely when
the core coefficient $r$ is positive. $\square$

**Proposition 174.3 (A finite boundary core with slack tail error).**
Take $m=2$, $A=(3/4,1/2)$, $e_0=1/2$, and $L=3$, $g_3=1/10$.
There is a finite core with these parameters whose extension has

$$
a=(47/60,17/30,17/30),\qquad \varepsilon=7/15,
\tag{174.3}
$$

followed by any permitted actual tail. Its exact uniform error is
$7/15$, while $t_{\rm tail}=1/30$. In particular the head-to-late
join need not be strict, and the core tail row need not be tight.

**Proof.** Preselect $(1,2)$; on its first queried zero $n$, emit $n$
with probability $A_n$ and zero otherwise, and emit zero on positive
exhaustion. Predetermined partitions of one seed fix both cell outputs.
The finite core equals its two-point target on every zero-containing
word and has $q_{11}(0)=1$. It therefore satisfies (172.1), including
$A_2=e_0$. The residual formulas give
$W=2/15$, $E=1/30$, $r=13/15$, and (173.1) gives (174.3).
Equation (173.12) gives $p_{111}(0)=29/30$ and
$t_{\rm tail}=1/30$. Actual first absence three nevertheless has
correct deficit $7/15$, as in (173.10). Every tail error is
$\max\{1/30,a_n\}$, rather than an assertion of equality to the
uniform cap on each tail. $\square$

## 175. Sharp-core extensions on arbitrary finite active lengths

**Proposition 175.1 (The sharp core inside the residual strip).** Use
the seven-cell core (118.5) at the parameters of Proposition 118.2:

$$
A=(17/20,17/20,16/25,31/50,27/50),\qquad e_0=17/60.
\tag{175.1}
$$

For every finite $L\ge6$ choose $g_6\ge\cdots\ge g_L>0$ with

$$
W=\frac{7g_6+\sum_{i=7}^Lg_i}{3}\le1,
\qquad E=\frac{4g_6+\sum_{i=7}^Lg_i}{3},\qquad r=1-W.
\tag{175.2}
$$

The amplitudes and cap of (173.1) have actual active length $L$ and
original same-seed $O_2$ and $N_2$ attainers with exact uniform error
$\varepsilon=17r/60+E$. Every actual tail error equals this cap.
For $r>0$, they satisfy

$$
D_3-3\varepsilon=\frac r{10}>0,\qquad
1-a_2=\frac{3r}{20},\qquad
\frac{D_3-3\varepsilon}{1-a_2}=\frac23,
\quad a_1=a_2<1.
\tag{175.3}
$$

The case $r=0$ is included in feasibility, but the displayed ratio
is asserted only for $r>0$.

**Proof.** The parameters
$\delta=3/20$, $\alpha=0$, $t=3/5$, $u=1/25$, $v=1/50$
satisfy (118.1). Theorem 118.1 and its formulas (118.5), (118.11)
give the core, with scalar weights $w=1/2$, $x=1/15$, $y=13/60$,
$z=1/20$, total mass one, and $q_{1^5}(0)=43/60=1-e_0$.
These are reused core facts from
[Section 118](KBONACCI_SELF_CALIBRATING_ACQUISITION_RESOURCES_CONTINUATION.md#118-a-sharp-five-active-family-with-unequal-late-amplitudes),
not an additional proof of the five-active optimum. The core residual
sum is

$$
D_{\rm core}=(16/25+31/50+27/50)-3(17/60)=19/20,
\qquad D_{\rm core}-3e_0=1/10.
$$

Apply Theorem 173.1 at $m=5$ and (174.2). Tightness of the reused
core tail row proves equality on every actual tail. The head identity
in (174.2) gives the slack and ratio. Freely unequal late residuals,
late plateaus and $W=1$ are all covered by the same finite proof.
The old core's optimality does not imply optimality of the extended
cap. $\square$

**Proposition 175.2 (A geometric family at every finite length).** For
each finite $L\ge6$, choose

$$
g_i=\frac{1}{100\,2^{i-6}}\quad(6\le i\le L),\qquad
z=2^{-(L-6)}.
$$

Then the construction in Proposition 175.1 has

$$
W=\frac{8-z}{300},\quad E=\frac{5-z}{300},\quad
r=\frac{292+z}{300},\quad \varepsilon=\frac{17r}{60}+E,
\qquad B:=\sum_{i=6}^Lg_i=\frac{2-z}{100}<\frac r{10}.
\tag{175.4}
$$

One permitted original tail is $a_{L+j}=\varepsilon/j$, $j\ge1$.
Each finite $L$ defines its own positive monotone vanishing sequence
with the conclusions of Proposition 175.1.

**Proof.** The finite geometric sum gives
$\sum_{i=7}^Lg_i=(1-z)/100$, including its empty value at $L=6$,
where $z=1$. Substitution proves the formulas. Since $0<z\le1$,
$W<1$ and $r\ge292/300$. Thus
$B\le1/50<292/3000\le r/10$. All residuals are positive.
The proposed tail starts at the closed cap, is positive, nonincreasing
and vanishes. Proposition 175.1 applies. The family is indexed by
finite active lengths; it supplies no single infinite positive-cap
plateau. $\square$

## 176. Augmented endpoints, duplicate conventions and exact core membership

**Definition 176.1 (Restricted and augmented complete-table catalogs).**
Fix $L\ge3$ and the complete stopped catalog $\mathcal D_O$ of
[Definition 164.2](KBONACCI_SELF_CALIBRATING_ACQUISITION_RESOURCES_CONTINUATION_IV.md#164-complete-deterministic-catalogs-and-event-demands).
Write $D=(i,j;s,r,\ell)$ for the increasing schedule $(i,j)$,
$i<j$, with outputs $s,r,\ell$ on its stopped cells $0,10,11$.
The complete table, including its schedule, is fixed before replies.

Let $T_L$ consist exactly of the empty schedule emitting zero,
the singletons $(i;i,0)$, the pairs $(i,j;i,j,0)$, the numerical
triples $(i,j;i,j,k)$ with $i<j<k\le L$, and the four prefix
tables $(1,2;s,r,0)$ with $s\in\{0,1\}$ and $r\in\{0,2\}$.
Let

$$
\begin{aligned}
Z_L&=\{(i,j;0,r,\ell):1\le i<j\le L,\ i<r\le j,
                   \ \ell=0\text{ or }j<\ell\le L\},\\
E_L&=T_L\cup Z_L.
\end{aligned}
\tag{176.1}
$$

The primary convention identifies equal schedule/table pairs, including
entries appearing in two descriptions, while retaining distinct
schedules with identical output kernels. The indexed list $Z_L$ has
one coordinate for each quadruple $(i,j,r,\ell)$ satisfying (176.1).
The union $E_L$ identifies its intersection with $T_L$. A further
kernel quotient identifies entries with identical outputs on every word.
Any of these conventions can describe mixtures, provided each chosen
coordinate contributes its weight exactly once to the same total mass.

**Proposition 176.2 (Exact union counts and closed sharp-core membership).**
In the primary schedule/table convention,

$$
\begin{aligned}
|T_L|&=4+L+\binom L2+\binom L3,\\
|Z_L|&=\binom{L+2}4,\\
T_L\cap Z_L&=\{(1,2;0,2,0)\},\\
|E_L|&=3+L+\binom L2+\binom L3+\binom{L+2}4.
\end{aligned}
\tag{176.2}
$$

There are $\binom{L+2}4-1$ new union entries beyond $T_L$.
The kernel quotient removes exactly two further duplicates. At $L=6$
the three primary counts are $45,70,114$, with $112$ distinct kernels.
For every parameter choice in (118.1), the entire kernel (118.5)
belongs to $\operatorname{conv}(E_5)$. More generally, a core in
$\operatorname{conv}(E_m)$ has every residual extension of Theorem
173.1 in $\operatorname{conv}(E_L)$; this includes the whole
closed-parameter sharp-core family.

**Proof.** The prefix table $(1,2;1,2,0)$ is already a canonical pair;
the other three prefix entries add to the empty, singleton, pair and
triple counts, giving $|T_L|$. For $Z_L$, a fixed $(i,j)$ has $j-i$
middle labels and $L-j+1$ exhaustion labels. Thus

$$
|Z_L|=\sum_{j=2}^L\binom j2(L+1-j)
      =\sum_{t=2}^L\sum_{j=2}^t\binom j2
      =\sum_{t=2}^L\binom{t+1}3=\binom{L+2}4.
\tag{176.3}
$$

Comparing first and middle labels shows that the only intersection
entry is $(1,2;0,2,0)$. This proves the union count.
The two kernel identifications are the prefix $(1,2;0,0,0)$ with
immediate base emission, and $(1,2;1,0,0)$ with the canonical singleton
at one. Every other pair table in this union has both queried bits
essential to its output function. The set of its essential coordinates
therefore determines its increasing schedule. Within that schedule,
all three stopped cells are reachable, so the kernel determines each
terminal label. A singleton's essential coordinate similarly determines
it. There are consequently no further identifications. Substituting
$L=6$ gives the numerical counts.

For membership, apply the existing complete-cell realization of
[Proposition 140.3](KBONACCI_SELF_CALIBRATING_ACQUISITION_RESOURCES_CONTINUATION_II.md#140-original-sources-and-complete-common-budget-allocations)
to each of the seven schedules in the reused table (118.5).
For a schedule $(i,j)$ of mass $\beta$, its first vector has support
in $\{0,i\}$, its middle vector is $\beta e_j$, and its exhaustion
vector has support in $\{0,j+1,\ldots,5\}$. Denote the first masses
by $a_s$ and exhaustion masses by $w_\ell$. Both sum to $\beta$.
If $\beta>0$, give the complete endpoint $(i,j;s,j,\ell)$ mass

$$
\frac{a_s w_\ell}{\beta}.
\tag{176.4}
$$

Summing over $\ell$ recovers $a_s$, summing over $s$ recovers
$w_\ell$, and their joint sum is $\beta$. The middle vector is
unchanged. If $\beta=0$, all these nonnegative masses vanish and
the schedule is omitted. An endpoint with $s=i$ is a canonical pair
or numerical triple; one with $s=0$ is in $Z_5$, since its middle
label is $j$. This reproduces every cell and hence every word law,
not just the correct marginal or cap. Non-strict parameter endpoints
are included without division on zero-mass schedules.

The natural embedding $E_m\subseteq E_L$ uses the same schedules and
labels. Each $P_h$ branch is a mixture of canonical numerical triples,
or of canonical base-exhausting pairs when its last label is $\ast$.
These belong to $T_L$. Therefore the one normalized residual mixture
stays in $\operatorname{conv}(E_L)$ with exactly the same kernel.
The same-seed actual realization and every actual tail are then those
of Theorem 173.1, with the entire original carrier retained.
Membership does not assert that all stopped kernels belong to this
subcatalog. $\square$

**Definition 176.3 (Coupled zero-first terminal coordinates).** A
zero-first schedule $(i,j)$ can be described by nonnegative masses
$\beta_{ij}$, $v_{ij}(r)$ for $i<r\le j$, and $w_{ij}(\ell)$ for
$\ell=0$ or $j<\ell\le L$, subject to

$$
\sum_r v_{ij}(r)=\sum_\ell w_{ij}(\ell)=\beta_{ij}.
\tag{176.5}
$$

Its three cell vectors are $\beta_{ij}e_0,v_{ij},w_{ij}$.
These are coupled coordinates for the existing complete-cell model,
not independent row budgets. Its endpoint weights can be chosen as
$\mu_{ijr\ell}=v_{ij}(r)w_{ij}(\ell)/\beta_{ij}$ when
$\beta_{ij}>0$, and zero when $\beta_{ij}=0$; nonnegativity forces
both marginal vectors to vanish in the latter case. Marginal summation
recovers (176.5) and total mass $\beta_{ij}$. Conversely any endpoint
weights give exactly these marginals by summation. At a word exactly
one stopped cell is reached, so the recovered kernel is identical on
all words, including base, correct and pair rows. One common seed
selects the whole coupled endpoint, as in Proposition 140.3; this is
an application of that finite realization, not an additional content
theorem about coupling.

There are $L-i+1$ raw terminal-marginal coordinates for each pair
$(i,j)$, and hence

$$
\sum_{i=1}^{L-1}(L-i)(L-i+1)=\frac{L^3-L}{3}
\tag{176.6}
$$

across pairs, with $\binom L2$ optional explicit schedule masses.
The equality follows by summing $d(d+1)$ for $d=1,\ldots,L-1$.
These are raw coordinate counts subject to (176.5), not independent
dimensions or bounds on computational complexity. The indexed
endpoint count remains (176.3); union duplicates are treated by
Definition 176.1.

## 177. Simultaneous nested allocation cuts and the 25-mode obstruction

**Definition 177.1 (Prefix event scores in one full catalog).** Fix
$L\ge3$. For $3\le k\le L$, put $w_t=1^t0^{L-t}$, $0\le t\le k$,
and define events

$$
\begin{aligned}
H_0&=\{0,1\},&H_1&=\{0,2\},\\
H_t&=\{t+1\} &&(2\le t<k),\\
H_k&=\begin{cases}\{0,k+1\},&k<L,\\\{0\},&k=L.\end{cases}
\end{aligned}
$$

The dependence of $H_t$ on $k,L$ is understood. Set

$$
\begin{aligned}
\Psi_k(p)&=\sum_{t=0}^kp_{w_t}(H_t),\\
f_k(a,\varepsilon)&=\sum_{i=3}^ka_i-(k+1)\varepsilon,\\
M_k&=\{(i,j;0,r,\ell):2\le i<j\le k,\ i<r\le j,
          \ \ell=0\text{ or }j<\ell\le\min(k+1,L)\}.
\end{aligned}
\tag{177.1}
$$

All $M_k$ are subsets of the same complete stopped catalog on $J_L$.
The full-prefix event $H_L$ contains only zero: label $L+1$ is not in
the catalog. Its row is the finite all-positive base requirement which
Theorem 110.2 derives from actual tails.

**Theorem 177.2 (Exact supports and simultaneous required masses).**
For every $3\le k\le L$, both the complete stopped and complete
preselected support maxima of $\Psi_k$ are four. Among stopped
tables, score four occurs exactly on $M_k$. The prefix anchor
$R=(1,2;1,2,0)$ has score three, and every $T_L$ mixture has score
at most three. In any single cap-feasible complete stopped
probability representation with weights $p_D$, the masses

$$
q_k=\sum_{D\in M_k}p_D\ge\max\{0,f_k(a,\varepsilon)\}
\qquad(3\le k\le L)
\tag{177.2}
$$

hold simultaneously. They satisfy $q_3\le\cdots\le q_L$, with

$$
|M_k|=\begin{cases}
\binom{k+1}4+\binom k3,&k<L,\\
\binom{L+1}4,&k=L.
\end{cases}
\tag{177.3}
$$

These are constraints on one finite representation. For an original
arbitrary-address/full-carrier $O_2$ cap attainer, every finite feasible
representation obtained through Theorem 110.2 obeys them; its weights
are not identified with the competitor's original seed-mode weights.

**Proof.** A pair $(i,j)$ partitions the selected chain words into
three transcript intervals: $t<i$, $i\le t<j$, and $j\le t\le k$,
intersected with $0\le t\le k$. Suppose $2\le i<j\le k$.
In the first interval a fixed label hits at most two events, and hits
two exactly when it is zero, at rows zero and one. Every other label
hits at most one. In the middle interval a fixed label hits at most
one event, with equality exactly for labels $i+1,\ldots,j$.
In the final interval it also hits at most one, with equality exactly
for zero or labels $j+1,\ldots,\min(k+1,L)$. These choices produce
four precisely on the tables in $M_k$.

If $i=1$, the first interval has maximum one, and each of the next
two intervals has maximum one: the second contains row one but no
other event carrying zero before the final row. Thus its total is at
most three. If $i\le k<j$, the final interval is empty. For $i\ge2$
the first maximum is two and the second is one; for $i=1$ the second
can hit both rows one and $k$ with zero but the first maximum is one.
Both totals are at most three. If $i>k$, only the first interval is
nonempty; zero hits exactly rows zero, one and $k$, and no label hits
more. Empty and singleton schedules also score at most three: a
singleton splits the rows at $i$, and the same event multiplicities
give maximum three. This proves the entire stopped upper support and
all its equality cases. The table $(2,3;0,3,0)$ attains four for every
$k\ge3$.

On these chain words a sorted preselected pair observes only $00,10,11$;
its $01$ cell never occurs. Hence its three used outputs have precisely
the interval optimization just proved. Static repetitions give no extra
cell information, and sorting a reversed preselected schedule only
permutes its table. The full preselected maximum is therefore also
four. This uses separate word laws in a linear score, without a joint
observation of several trajectories.

For a canonical numerical triple in $T_L$, each of its three distinct
numerical labels can hit at most one selected event. A canonical pair
has the same first two numerical contributions, and base on positive
exhaustion can hit only the final row. A singleton has at most one
numerical hit and at most two base hits after its queried coordinate;
immediate base hits rows zero, one and $k$. Each of the four prefix
tables hits exactly these three rows. In particular $\Psi_k(R)=3$,
and $T_L$ has support at most three.

For a cap-feasible kernel, the rows at $t=0,1$ are pair rows, each
at least $1-\varepsilon$. At $2\le t<k$, the correct row is at
least $a_{t+1}-\varepsilon$. The last row is another pair row when
$k<L$, and the all-positive base row when $k=L$; it is at least
$1-\varepsilon$ in either case. Their sum is

$$
\Psi_k(p)\ge3+\sum_{i=3}^ka_i-(k+1)\varepsilon=3+f_k.
\tag{177.4}
$$

All deterministic scores are integers. Tables in $M_k$ have score four,
and all other stopped tables have score at most three. Therefore the
same mixture satisfies $\Psi_k(p)\le3+q_k$. Combining the inequalities
and $q_k\ge0$ proves (177.2).

For the counts, sum the $j-i$ middle choices over $2\le i<j$ to
obtain $\binom{j-1}2$. At the full prefix the exhaustion count is
$L+1-j$, so

$$
\sum_{j=3}^L\binom{j-1}2(L+1-j)=\binom{L+1}4.
$$

For a proper prefix replace $L$ by $k$ and add one exhaustion choice
per middle choice, giving $\binom{k+1}4+\binom k3$.
These identities follow by the same two cumulative binomial sums as
(176.3).

Within the fixed full-$L$ catalog, a table with $i\ge2$, first label
zero, $i<r\le j$, and legal exhaustion label enters the sets at

$$
\vartheta(D)=\begin{cases}
j,&\ell=0,\\
\max\{j,\ell-1\},&\ell>j,
\end{cases}
\tag{177.5}
$$

and every other table has $\vartheta(D)=+\infty$. Thus
$D\in M_k$ exactly when $\vartheta(D)\le k$. This proves nesting
even at $k=L$, including the new tables with $j=L,\ell=0$.
It also writes $q_k=\mathsf P\{\vartheta\le k\}$ under the one
common finite weight measure. The lower cuts cannot be treated as
independently chosen row budgets.

Finally apply the necessary direction of the reused Theorem 110.2
to any original competitor at its active length. The theorem preserves
feasibility at the exact closed cap; it does not preserve an arbitrary
competitor's law or seed decomposition. The cuts apply to every
representation of the resulting finite feasible stopped kernel.
The $k=L$ row is therefore an actual-tail requirement, not a new
infinite all-positive source. $\square$

**Corollary 177.3 (Exactly 25 modes at the five-prefix score).** For
$L\ge6$, put $\Phi=\Psi_5$. Its complete stopped score-four tables
are exactly

$$
(i,j;0,r,\ell),\qquad 2\le i<j\le5,\quad i<r\le j,\quad
\ell=0\text{ or }j<\ell\le6.
\tag{177.6}
$$

There are 25, and their mass in any finite stopped cap attainer is
at least $\max\{0,a_3+a_4+a_5-6\varepsilon\}$.
Every $T_L$ cap attainer must have $a_3+a_4+a_5\le6\varepsilon$.
For the sharp-core extension of Proposition 175.1 this demanded mass is

$$
f_5=\frac r{10}-B,\qquad B=\sum_{i=6}^Lg_i.
\tag{177.7}
$$

When $B<r/10$, the full $O_2$ construction exists at the cap while
the restricted $T_L$ method does not. The geometric family of
Proposition 175.2 has this strict method obstruction at every finite
$L\ge6$.

**Proof.** Apply Theorem 177.2 at the proper prefix $k=5$.
The count is also explicitly
$\sum_{j=3}^5\sum_{i=2}^{j-1}(j-i)(7-j)=4+9+12=25$.
If a $T_L$ mixture were cap-feasible, (177.4) and its support three
would give $f_5\le0$. The full excess identity gives
$f_L=D_3-3\varepsilon=r/10$, while
$f_L-f_5=\sum_{i=6}^L(a_i-\varepsilon)=B$.
This proves (177.7); the geometric inequality is (175.4).
The complete $N$ and $O$ supports for this score are both four, so
this obstruction is a failure of a restricted method, with no full
$N/O$ support gap or extended-cap optimality conclusion. $\square$

**Proposition 177.4 (Conic mass cuts from the same full-row scores).**
Use the complete event vector $z_D$, demand vector $d(x)$ and prefix
$R$ of Sections 164--166. Write $\mathbf r=z_R$,
$h(x)=d(x)-\mathbf r$, and let $A_C$ have columns $z_D-\mathbf r$.
For a nonnegative conic allocation satisfying $A_O\lambda\ge h(x)$,

$$
\sum_{D\in M_k}\lambda_D\ge\max\{0,f_k(x)\}.
\tag{177.8}
$$

For both full classes, the common conic costs of Definition 166.1 satisfy
$\rho_N(x),\rho_O(x)\ge\max\{0,f_k(x)\}$ for every $k$.
These masses need not be probabilities.

**Proof.** Let $y_k\ge0$ select exactly the event rows in $\Psi_k$.
Theorem 177.2 gives
$y_k\cdot\mathbf r=3$, $y_k\cdot h(x)=f_k(x)$, and
$\Delta_N(y_k)=\Delta_O(y_k)=4-3=1$. Thus

$$
f_k\le\sum_D\lambda_D(\Psi_k(D)-3)
     \le\sum_{D\in M_k}\lambda_D
$$

in the stopped case. For either class, replacing the last sum by the
total mass gives the same lower bound on any feasible conic allocation,
and then on the infimum of its mass. The nonnegative lower bound
also follows from nonnegativity of the coefficients. This is the
existing conic model of Definition 166.1 applied to these new scores;
no coefficient is a seed probability before the total mass is made
into a probability budget. $\square$

## 178. All-word suffix normal form with two coupled Boolean minima

**Definition 178.1 (Suffix coordinates and their common quadratic form).**
For a first-zero class $n\le L$, fix $b_i=1$ for $i<n$, $b_n=0$,
and write $v_j=b_j$ for $j>n$. For coefficients $Q_{jk}\ge0$, set

$$
\mathcal M_n(c)=\min_{v\in\{0,1\}^{L-n}}
 \left[\sum_{j>n}c_jv_j+\sum_{n<j<k\le L}Q_{jk}v_jv_k\right].
\tag{178.1}
$$

At $n=L$ the suffix is empty and $\mathcal M_L=0$.
Different instances of $\mathcal M_n$ below use the same quadratic
coefficients from the same endpoint mixture.

**Theorem 178.2 (Exact augmented-catalog suffix criterion).** For every
probability mixture on $E_L$, there are real $C_n,\beta_{nj}$ and
nonnegative $\kappa_{nj},Q_{jk}$ such that on its entire first-zero
class $n$,

$$
\begin{aligned}
p_b(0)&=C_n+\sum_{j>n}\beta_{nj}v_j
                    +\sum_{n<j<k\le L}Q_{jk}v_jv_k,\\
p_b(n)&=\gamma_n+\sum_{j>n}\kappa_{nj}(1-v_j),\qquad
\gamma_n=p_{1^{n-1}0\,1^{L-n}}(n).
\end{aligned}
\tag{178.2}
$$

All finite cap rows (110.6) are equivalent to the joint conditions

$$
\begin{aligned}
\gamma_n&\ge a_n-\varepsilon,\\
C_n+\mathcal M_n(\beta_n)&\ge1-a_n-\varepsilon,\\
C_n+\gamma_n+\sum_{j>n}\kappa_{nj}
  +\mathcal M_n(\beta_n-\kappa_n)&\ge1-\varepsilon
                         &&(1\le n\le L),\\
p_{1^L}(0)&\ge1-\varepsilon.
\end{aligned}
\tag{178.3}
$$

In particular the base and pair constraints retain two Boolean
quadratic minima. Their endpoint coefficients and total probability
budget are shared; neither minimum replaces the other.

**Proof.** For each endpoint the global base indicator has the following
multilinear polynomial:

$$
\begin{array}{c|c}
\text{endpoint}&D_b(0)\\\hline
\text{immediate base}&1\\
(i;i,0)&b_i\\
(i,j;i,j,0)&b_ib_j\\
(i,j;i,j,k),\ i<j<k&0\\
(1,2;s,r,0)&A+(B-A)b_1+(1-B)b_1b_2\\
(i,j;0,r,\ell)\in Z_L&1-b_i+\mathbf1_{\ell=0}b_ib_j
\end{array}
\tag{178.4}
$$

Here $A=\mathbf1_{s=0}$ and $B=\mathbf1_{r=0}$ in the prefix row.
All quadratic coefficients are nonnegative. Summing with the one
mixture's weights gives

$$
p_b(0)=C+\sum_i l_i b_i+\sum_{i<j}q_{ij}b_ib_j,
\qquad q_{ij}\ge0.
$$

After fixing the prefix and its zero, this has the first form (178.2),
with explicit coefficients

$$
\begin{aligned}
C_n&=C+\sum_{i<n}l_i+\sum_{i<j<n}q_{ij},\\
\beta_{nj}&=l_j+\sum_{i<n}q_{ij}\quad(j>n),\qquad
Q_{jk}=q_{jk}\quad(n<j<k).
\end{aligned}
\tag{178.5}
$$

Every canonical singleton, pair, triple and prefix contribution to
the correct label $n$ is constant within its first-zero class. For
example a canonical first label $n$ sees $b_n=0$, a canonical middle
label $n$ has its earlier queried bit positive, and a numerical last
label $n$ has both earlier queried bits positive. A zero-first endpoint
can emit $n$ in its exhaustion cell only when $\ell=n>j$, in which
case both queried bits are fixed positive and its contribution is
constant. It can emit $n$ in its middle cell only when $r=n$ and
$i<n\le j$. If $j=n$ it is constant; if $j>n$ its indicator is
$1-v_j$. It cannot emit a positive $n$ in its first cell.
Consequently $\kappa_{nj}$ is the sum of nonnegative masses of the
endpoints with $r=n$, $i<n$, $j>n$. All remaining correct contributions
form the constant $\gamma_n$, obtained by taking the all-one suffix.
This proves the second form (178.2) and its coefficient signs.

The minimum correct probability is $\gamma_n$. The minimum base
probability is $C_n+\mathcal M_n(\beta_n)$. Adding the two expressions
in (178.2) makes the pair probability

$$
C_n+\gamma_n+\sum_{j>n}\kappa_{nj}
 +\sum_{j>n}(\beta_{nj}-\kappa_{nj})v_j
 +\sum_{n<j<k}Q_{jk}v_jv_k.
$$

Its minimum is precisely the third left side of (178.3). The three
TV rows must each hold at every suffix, so taking their individual
minima is necessary and sufficient, with the separate positive-word
base row retained. This enumerates every multiple-zero word, as well
as the empty suffix, and proves the exact equivalence. $\square$

**Proposition 178.3 (Extreme suffixes do not determine base or pair rows).**
The endpoint $(2,3;0,3,0)\in E_3$, in its first-zero-one class, has
base probability one at words $000$ and $011$, but zero at $010$.
Its correct probability at label one is always zero. Thus checking
only the all-zero and all-one suffixes cannot enforce either the base
or pair lower row at every suffix.

**Proof.** Its base polynomial is $1-b_2+b_2b_3$, and it has no
output label one. Direct substitution proves all three values.
For example take $a_1=1/2$, $\varepsilon=1/4$ when testing this
class's base and pair rows: the two extreme suffixes satisfy their
lower bounds, but $010$ violates both. This is a counterexample to
that suffix test, not a cap-feasible global kernel or a full-class
separator. For larger $L$, append arbitrary suffix coordinates beyond
three; the same indicator values remain. $\square$

**Definition 178.4 (The graph-cut sign boundary of these suffix energies).**
The intermediate graph-representation criterion is
[Kolmogorov and Zabih, *What Energy Functions Can Be Minimized via
Graph Cuts?*, IEEE TPAMI 26(2), Theorem 4.1 and equation (7), p. 150](https://www.cs.cornell.edu/~rdz/Papers/KZ-PAMI04.pdf).
For binary pair terms it requires
$E_{jk}(0,0)+E_{jk}(1,1)\le E_{jk}(0,1)+E_{jk}(1,0)$
for direct graph representation. This intermediate sign criterion is
literature-attested. Applied to the pair terms in (178.1),
the difference of its two sides is

$$
E_{jk}(0,0)+E_{jk}(1,1)-E_{jk}(0,1)-E_{jk}(1,0)=Q_{jk}.
\tag{178.6}
$$

Unary terms cancel in this difference. The nonnegative quadratic
forms here are supermodular, and a strictly positive $Q_{jk}$ fails
that direct graph-cut condition in the stated suffix coordinates.
The literature theorem is used only for this sign boundary inside
the suffix criterion; it supplies no augmented-catalog sufficiency,
polynomial-time minimization bound for these forms, or impossibility
under every change of variables. The exact coupled minima (178.3)
remain the acquisition criterion. The residual and endpoint statements
in this volume are repo-derived compositions with their named
ordinary suppliers, without a first-discovery or exhaustive
literary-priority assertion.

## 179. Full-row endpoint support and probability padding of conic masses

**Definition 179.1 (Augmented full-row support and common conic cost).**
Use all $3(2^L-1)+1$ event rows of Definition 164.1. For a
nonnegative row score $y$, define its reward for output $s$ at word
$u$ by

$$
F_s(u)=\sum_{j:w_j=u}y_j\mathbf1_{s\in H_j},
$$

where $(w_j,H_j)$ runs through those full event rows. Thus
$y\cdot z_D=\sum_uF_{D(u)}(u)$. Put
$B_E(y)=\max_{D\in E_L}y\cdot z_D$,
$\Delta_E(y)=B_E(y)-y\cdot\mathbf r$, and let $A_E$ have columns
$z_D-\mathbf r$, with $\mathbf r=z_R$ and $R$ the same prefix anchor.
Define $\rho_E(x)$ by the infimum of $\sum_D\mu_D$ over
$\mu\ge0$, $A_E\mu\ge h(x)$, with value $+\infty$ if infeasible.
This uses the same demand vector, common mass and radial domain as
[Definitions 165.1 and 166.1](KBONACCI_SELF_CALIBRATING_ACQUISITION_RESOURCES_CONTINUATION_IV.md#165-a-unique-radial-direction-away-from-the-first-two-prefix).
Because $E_L\subseteq\mathcal D_O$, $\rho_O\le\rho_E$.

For a fixed zero-first schedule $(i,j)$, its exact endpoint support is

$$
\begin{aligned}
&\sum_{u_i=0}F_0(u)
 +\max_{i<r\le j}\sum_{u_i=1,\,u_j=0}F_r(u)\\
&\hspace{35mm}
 +\max_{\ell\in\{0,j+1,\ldots,L\}}
                     \sum_{u_i=u_j=1}F_\ell(u).
\end{aligned}
\tag{179.1}
$$

Indeed the three sums partition the full word set into its stopped
cells; choosing labels attaining the two maxima makes one legal
complete endpoint. Taking the maximum of (179.1) over pairs and the
$T_L$ support gives $B_E(y)$ exactly. This is the complete-cell
support calculation of Definition 164.3 applied to the restricted
label sets, rather than independent maximization at each word.
Every multiple-zero word, the actual-tail base row and the same total
mass budget remain part of this support.

**Proposition 179.2 (Affine suffix identities versus probability laws).**
For nonnegative endpoint masses $\mu_D$, $D\in E_L$, of total
$\tau=\sum_D\mu_D$, set

$$
f_b=\sum_D\mu_D D_b+(1-\tau)R_b.
\tag{179.2}
$$

The first-zero-class identities (178.2) still hold for $f$, with
nonnegative suffix $Q_{jk}$ and $\kappa_{nj}$. Both Boolean minima
in (178.3) exactly test its affine row inequalities. If $\tau>1$,
these identities do not guarantee that $f_b$ is nonnegative, and
$f$ need not be a probability kernel.

Suppose instead $A_E\mu\ge h(b)$ and $\tau\le M$ for some $M\ge1$.
For $b$ in the radial domain $H_L$, the weights

$$
\frac{\mu_D}{M},\qquad\text{with additional }R\text{ mass }
1-\frac{\tau}{M},
\tag{179.3}
$$

are an actual common probability allocation for
$x=\alpha+(b-\alpha)/M$ and satisfy all its closed-cap rows.
For a positive interior profile, retain every actual tail by the same
radial scaling. The construction uses one seed and has original
hard-two $O$ and same-seed $N$ realizations.

**Proof.** The nonnegative sum $\sum_D\mu_DD_b$ has the suffix
identities proved from endpoint polynomials in Theorem 178.2.
The prefix $R$ has base indicator $b_1b_2$, and its correct
probability is constant in each first-zero class. Once a first zero is
fixed, $b_1b_2$ is either zero or constant; in particular it is never
a suffix-suffix monomial. Thus the possibly negative $1-\tau$
changes only constant or unary coefficients and not any suffix
$Q_{jk}$ or $\kappa_{nj}$. The same algebra and two minima still
test the affine rows. For a concrete failure of positivity, give
immediate base mass two and every other endpoint mass zero. Then
$f_b=2e_0-R_b$, which has correct-label-one mass $-1$ throughout
the first-zero-one class. Total coordinate sum one is insufficient
for a probability law.

In (179.3) all weights are nonnegative and their sum is one, including
the endpoint $\tau=M$. If $R$ already has a coordinate in $\mu$,
add the padding mass to that coordinate exactly once. The event vector
of this probability mixture is

$$
\mathbf r+\frac{A_E\mu}{M}\ge
\mathbf r+\frac{h(b)}M=d\left(\alpha+\frac{b-\alpha}{M}\right).
\tag{179.4}
$$

This last identity is the supplied affine radial identity (165.5),
with $d(\alpha)=\mathbf r$. It establishes all rows using the same
weights, with no independent choice of singleton or pair budgets.
Zero weights are omitted. A finite partition of one source-independent
seed chooses the entire endpoint before actual prime requests; stopping,
completion and the full-carrier actual-tail bound are the already
supplied Theorems 109.1, 110.2 and Proposition 90.2.

For the whole original sequence, at scale $1/M$ the first two
amplitudes become $1-(1-b_i)/M$, and every $i\ge3$, including each
actual $i>L$, has amplitude $b_i/M$. The cap is $e_b/M$.
[Theorem 170.1](KBONACCI_SELF_CALIBRATING_ACQUISITION_RESOURCES_CONTINUATION_IV.md#170-every-original-tail-under-the-same-radial-law-identity)
owns this full-sequence target identity. Positivity, order, vanishing
and each actual tail-cap comparison are retained; original tail marks
are not discarded in the target identity. The finite all-positive row
is only the separate transport device. $\square$

**Definition 179.3 (The unproved augmented-budget obligation).** A
sufficient augmented route to the universal comparison would establish

$$
\rho_E(b)\le\max\{1,\rho_N(b)\}
\quad\text{for every }b\in H_L\text{ with }\rho_N(b)<\infty.
\tag{179.5}
$$

For an attained optimal $N$ mass $s=\rho_N(b)$, an $E_L$ allocation
of mass at most $M=\max\{1,s\}$ would allow Proposition 179.2's
probability padding. When $s\ge1$ this requires preserving the optimal
budget; when $s<1$ it permits mass up to one. It suffices to lift the
attained optimum, rather than every nonoptimal representation.
Attainment and the radial equivalence are owned by Theorems 166.2 and
167.2; the augmented inequality (179.5) is unproved. Its failure would
be a method obstruction, since $E_L$ is a subcatalog of the full
stopped class. A whole-class negative certificate must maximize its
score over every table of $\mathcal D_O$, not only $E_L$ or $T_L$.

## 180. A rational seven-active extension and its distinct event scores

**Proposition 180.1 (An all-word rational attainer).** Take the core
(175.1), $L=7$, $g_6=1/100$, $g_7=1/200$. Then

$$
\begin{aligned}
W&=1/40,&E&=3/200,&r&=39/40,&\varepsilon&=233/800,\\
(a_1,\ldots,a_7)
 &=\left(\frac{683}{800},\frac{683}{800},\frac{649}{1000},
          \frac{1259}{2000},\frac{1103}{2000},
          \frac{241}{800},\frac{237}{800}\right).
\end{aligned}
\tag{180.1}
$$

For every positive nonincreasing vanishing actual tail with
$a_8\le233/800$, including $a_{7+j}=233/(800j)$, there are original
same-seed stopped and preselected hard-two acquisitions of exact
uniform error $233/800$. Each actual first absence six or seven,
and every actual tail source, has that exact error.

The mixture uses core mass $39/40$, $P_6$ mass $7/600$ and $P_7$
mass $1/75$. A particular $P_6$ three-subset has mass $1/3000$,
and a particular $P_7$ three-subset has mass $1/4200$. On all 128
words its base probability is

$$
p_b(0)=\frac{39}{40}q_{(b_1,\ldots,b_5)}(0)
       +\frac{\binom{k_6(b)}2}{3000}
       +\frac{\binom{k_7(b)}2}{4200},
\tag{180.2}
$$

where $k_h(b)=\sum_{i=1}^hb_i$. Its correct probabilities are constant
on each first-zero class, respectively

$$
\left(\frac{489}{800},\frac9{16},\frac{1431}{4000},
       \frac{1353}{4000},\frac{1041}{4000},\frac1{100},\frac1{200}\right).
\tag{180.3}
$$

The minima of the three independent TV-row slacks, in the order
base, correct, pair, are

$$
\begin{array}{c|c|c|c}
n&\min[p_b(0)-(1-a_n-\varepsilon)]
 &\min[p_b(n)-(a_n-\varepsilon)]
 &\min[p_b(0)+p_b(n)-(1-\varepsilon)]\\\hline
1&97/400&39/800&0\\
2&233/800&0&0\\
3&389/875&0&4293/28000\\
4&13299/28000&0&643/3500\\
5&13893/28000&0&2869/14000\\
6&1663/5600&0&1/175\\
7&1651/5600&0&1/280
\end{array}
\tag{180.4}
$$

The all-positive base probability is $567/800=1-\varepsilon$.
Thus the $381$ zero-containing-word rows and the final base row all
hold, retaining every multiple-zero word.

**Proof.** Substitute the residuals into (173.4) to obtain $W,E,r$
in (180.1). The branch weights in (172.2) are $7/600$ and $1/75$.
There are $\binom73=35$ and $\binom83=56$ subsets, respectively,
giving the individual masses. The amplitude formulas (173.1) give
exactly (180.1); their order is
$a_1=a_2>a_3>a_4>a_5>a_6>a_7>\varepsilon>0$.
Equation (173.8) proves (180.2) at every word.

The reused correct core probabilities from (118.8) are
$37/60,17/30,107/300,101/300,77/300$.
Each of the first five classes gains correct mass
$3(7/600)/7+3(1/75)/8=1/100$ from the subset branches.
The sixth class has that same mass, and the seventh has only
$3(1/75)/8=1/200$. This proves (180.3), including its independence
of later zeros.

For completeness, the following words attain the base minima in
their respective classes:

$$
0100000,\quad1000000,\quad1100000,\quad1110000,
\quad1111000,\quad1111100,\quad1111110.
\tag{180.5}
$$

For classes one through five, the reused core formula (118.8) gives
base lower bounds $1/10,3/20,31/60,17/30,2/3$.
They are attained at the first five listed words. In class one the
core minimum $1/10$ follows from the transition bracket in (118.8);
the attaining word has only one positive bit, so both subset base
terms vanish. In class two every word has at least the positive bit
one, and the attaining word again makes both subset terms zero.
In each class $n=3,4,5$, every word has at least $n-1$ positive
bits in each subset range. The displayed word has exactly this many
and also attains the core minimum. Since $\binom{k}{2}$ is
nondecreasing for nonnegative integer $k$, it simultaneously
minimizes the subset contributions.

In class six the core sees $1^5$ with base $43/60$ and the minimal
positive-bit counts are $k_6=k_7=5$, attained at $1111100$.
In class seven the counts are both six, attained at $1111110$,
and the core has the same positive law. These observations give
the exact base minima

$$
\frac{39}{400},\quad\frac{117}{800},\quad
\frac{403}{800}+\frac1{1750},\quad
\frac{221}{400}+\frac3{1750},\quad
\frac{13}{20}+\frac6{1750},\quad
\frac{559}{800}+\frac1{175},\quad
\frac{559}{800}+\frac3{350}.
\tag{180.6}
$$

Subtracting each base demand, and using the class-constant correct
probabilities (180.3), gives every entry of (180.4). In particular
the pair slack is computed from the sum of base and correct
probabilities, rather than inferred from their separate lower bounds.
All entries are nonnegative. At $1^7$, (180.2) gives
$\frac{39}{40}\frac{43}{60}+15/3000+21/4200=567/800$.
Thus all $3(128-1)+1=382$ rows hold by these identities and lower
bounds, without a restriction to chain words.

Theorem 173.1 realizes the entire mixture on the actual original
source using one seed, with the same-seed $N$ completion counting
ignored requests. It gives exact uniform error, and its tail formula
uses the tight positive-word base mass just computed, so every actual
tail has error $233/800$, including $a_8=233/800$.
Theorem 110.2 supplies the same exact closed-cap finite/original
correspondence, with full-carrier and arbitrary-address competitors
in its necessary direction. No optimality at this cap is implied.
$\square$

**Proposition 180.2 (Demanded score, attained score and nested masses).**
For the same kernel,

$$
\begin{aligned}
D_3-3\varepsilon&=39/400,\\
(f_5,f_6,f_7)&=(33/400,37/400,39/400),\\
(|M_5|,|M_6|,|M_7|)&=(25,55,70).
\end{aligned}
\tag{180.7}
$$

The cap-demanded lower score and the kernel's actual score are
distinct:

$$
3+f_5=1233/400,\qquad \Phi(p)=17567/5600.
\tag{180.8}
$$

The complete-table refinement (176.4) of this attainer has
$q_5=q_6=q_7=117/800$. Every finite stopped cap attainer must instead
obey the necessary lower bounds $q_k\ge f_k$ from (180.7).
The $q_7$ lower bound does not strengthen the lower bound on its
25-mode subset $q_5$ to $39/400$.

Every $T_7$ competitor on the same entire original sequence has
uniform error at least $61/200$. The constructed full $O_2$ rule
has error $233/800$, so their restricted-method difference is
$11/800$. These facts assert neither a full $N/O$ support gap nor
optimality for the full stopped class.

**Proof.** Proposition 174.2 gives the excess $r/10=39/400$.
Here $B=g_6+g_7=3/200$; (177.7) gives $f_5=33/400$.
The successive differences are $f_6-f_5=g_6=1/100$ and
$f_7-f_6=g_7=1/200$. Formula (177.3) gives the three mode counts,
using its full-prefix branch at seven.

For the actual score, the six selected event probabilities at
$w_0,\ldots,w_5$ are, using (180.2)--(180.3),

$$
\frac{303}{400},\quad\frac{567}{800},\quad
\frac{1431}{4000},\quad\frac{1353}{4000},\quad
\frac{1041}{4000},\quad\frac{4001}{5600}.
\tag{180.9}
$$

Their sum is $17567/5600$. The demanded sum in (177.4) is only
$3+33/400=1233/400$, establishing the distinction in (180.8).

In the refinement (176.4) of the seven-cell core, the schedules
$(2,3),(3,4),(4,5)$ each have first-zero-label-zero mass $z=1/20$.
Their middle labels are respectively $3,4,5$, and all their
exhaustion labels are zero or a legal later label at most five.
Every endpoint in these three zero-first portions lies in $M_5$.
No other core schedule contributes to $M_5$, $M_6$ or $M_7$:
the schedules starting at one are excluded by $i\ge2$, and
$(2,4)$ has numerical first label two. The subset endpoints also
have numerical first labels, so none contributes. Consequently each
of the three nested masses is $r(3z)=(39/40)(3/20)=117/800$.
This is a particular legal common representation, not a claim that
it saturates any lower cut or that all representations have these
masses. Nesting permits additional mass in $M_7\setminus M_5$,
so a lower bound on the larger set cannot be assigned to the smaller.

Let $\eta$ be the uniform error of a $T_7$ competitor. If it is
infinite the asserted bound holds immediately. Otherwise actual
witnesses for the six finite chain patterns give the three pair
rows and three correct rows with error at most $\eta$.
Thus $\Phi\ge3+a_3+a_4+a_5-6\eta$ while its restricted support
is at most three. It follows that

$$
\eta\ge\frac{a_3+a_4+a_5}{6}
       =\frac{61}{200},\qquad
\frac{61}{200}-\frac{233}{800}=\frac{11}{800}.
$$

This is exclusion of the declared $T_7$ method at the constructed
cap. The full catalogs both have score support four by Theorem 177.2,
and the full stopped attainer is explicit, so it supplies no
whole-class separation. $\square$

## 181. The unchanged original intersection and coupled-budget boundary

**Definition 181.1 (The remaining universal comparison).** For every
original sequence of Definition 172.1 and every positive closed cap,
let $L=\max(\{i:a_i>\varepsilon\}\cup\{0\})$. The universal
obligation remains

$$
\mathcal F_N(a,\varepsilon)\ne\varnothing
\quad\Longrightarrow\quad
\mathcal F_N(a,\varepsilon)\cap\mathscr C_L\ne\varnothing.
\tag{181.1}
$$

Equivalently, on the remaining radial directions it asks for the
full-catalog exchange
$\rho_O(b)\le\max\{1,\rho_N(b)\}$ of Theorem 167.2.
The entire five- and six-active comparisons are owned respectively by
[Theorem 148.1](KBONACCI_SELF_CALIBRATING_ACQUISITION_RESOURCES_CONTINUATION_II.md#148-the-entire-original-five-active-closed-cap-comparison)
and [Theorem 161.1](KBONACCI_SELF_CALIBRATING_ACQUISITION_RESOURCES_CONTINUATION_III.md#161-every-original-six-active-profile-and-every-actual-tail).
Theorems 109.1 and 110.2 own coefficient membership and exact
closed-cap transport. The exact-law obstruction of Theorem 112.2
does not exclude a different stopped law in the same cap slice.

For arbitrary lengths, (181.1), sufficiency of $E_L$, and (179.5)
remain unproved. The residual extension proves explicit families in
the intersection and a sufficient recognition criterion; it does not
prove that an arbitrary cap-feasible $N$ kernel yields a feasible
auxiliary core after subtraction. The nested allocation cuts are
necessary conditions on one common finite stopped representation,
and their masses are not intrinsic unprojected original seed modes.
The suffix criterion retains both coupled minima and the same
probability budget, rather than replacing all suffixes by a chain or
assigning row budgets independently. A negative answer to the
universal obligation would require an original common-seed $N_2$
attainer and a uniform lower certificate against every full-carrier,
arbitrary-address original $O_2$ competitor, with all actual tails
retained, as specified by Section 169. The restricted-method
obstructions here provide no such certificate.

## 追加锚（本行以下为增补区）
