# FIB native unequal two-tail attained frontier

## 1. Fixed original objects and reusable premises

**Definition 1.1 (Source, carrier and targets).**
Let $F_0=0$, $F_1=1$, $F_{k+2}=F_{k+1}+F_k$, and let $p_i$ be the
increasing primes. Retain the actual countable source

$$
X=\{(r,g):r\text{ prime},\ g\in\mathbb Z,\
 \lceil F_r/10\rceil\le g\le\lfloor F_r/5\rfloor\},\qquad
N(r,g)=1+F_rg,\quad q_i(x)=[p_i\mid N(x)],\quad
n(x)=\min\{i:q_i(x)=0\}.
\tag{1.1}
$$

Replies are static. The full carrier is the Borel disjoint union
$\Theta=\bigsqcup_{j\ge1}B_j\sqcup\bigsqcup_{j\ge1}P_j$, with each block
a copy of $(0,1)$. The unchanged consumer makes no prime requests,
returns unknown on $B_j$, and proposes $j$ on $P_j$.

For $0<h_0<1$, put $t_x=\sum_i3^{-i}q_i(x)$ and
$Z_t=\int_0^1e^{tz}\,dz$. The original nonatomic targets remain
$\mu_x^{\rm orig}=(1-h_0)\nu_x+h_0\pi_{\Omega(x)}$, where $\nu_x$ has
density $e^{t_xz}/Z_{t_x}$ on $B_{n(x)}$, $\pi_j$ is uniform on $P_j$,
and $\Omega(x)$ counts distinct prime divisors of $N(x)$.
The separately selected accuracy targets in this volume are

$$
\theta_j=(B_1,1/(j+2))\quad(j\ge0),\qquad
\lambda_x^a=(1-a_{n(x)})\delta_{\theta_0}
                   +a_{n(x)}\delta_{\theta_{n(x)}},\qquad
e_a(A)=\sup_{x\in X}\operatorname{TV}(\mathcal L(A(x)),\lambda_x^a).
\tag{1.2}
$$

There is no carrier block indexed zero: all these marks belong to $B_1$.
Every finite marked output law has TV distance one from every unchanged
nonatomic target, which assigns its finite support mass zero.

**Definition 1.2 (Hard two actual requests).**
An original acquisition has one source-independent common seed, zero
advice and sourcewise almost-sure finite handoff to the unchanged consumer.
In $\mathcal N_2$ the whole schedule is preselected before replies and all
its replies are obtained. In $\mathcal O_2$ an increasing schedule is
preselected before replies and execution stops at its first queried zero
or exhaustion. The second address cannot depend on the first reply.
At most two actual requests are allowed, including repetitions and ignored
replies. Competitors retain arbitrary addresses and arbitrary Borel outputs
in $\Theta$. There is no source distribution, free observation of
$r,g,N,n$, address bound, runtime bound or mean-request relaxation.

A stopped rule has a same-source, same-seed $N$ completion: obtain the
whole preselected schedule and reconstruct its stopped output. Its ignored
second reply still counts as an actual request. This gives the class
inclusion used below, without converting an arbitrary $N$ rule to $O$.

**Reference frame 1.3 (Fixed source references).**
All reference paths are under docs/develop/theory/. The fixed DEV revision
of [XVII](KBONACCI_SELF_CALIBRATING_ACQUISITION_RESOURCES_CONTINUATION_XVII.md)
is 07dfbdac. The fixed DEV revision of
[XVIII](KBONACCI_SELF_CALIBRATING_ACQUISITION_RESOURCES_CONTINUATION_XVIII.md)
is 24e09b5c3ffd3b9e709ae2319cf79239572be790.

| Reference at its fixed revision | Reused content |
| --- | --- |
| XVII §§297, 309; XVIII §315 | Original objects, actual finite patterns, exact closed-cap class-feasibility and prefix transport |
| XVII Theorems 305.2–305.3 | The reused six-late lower bound |
| XVII Theorem 312.2 | Complete head-independent 43-charge core lower bound |
| XVIII Theorem 318.2 | Complete $N$ and $O$ support of $Y_{128}$ |
| XVIII Construction 319.1 and verification 319.2 | The actual $P^0$ and its all-word endpoint proof |
| XVIII Construction 320.1 and Theorem 320.2 | The complete $P^\star$ and its all-word endpoint proof |
| XVIII Theorem 321.1 | Equal-tail mixture, attained minima and original realization |

Reuse the finite-pattern theorem in XVII 297.3 and XVIII 315.3: every
finite reply word is actual, including all multiple-zero words and positive
prefixes, and every actual first absence is finite. A finite positive word
represents actual later first absences. No infinite all-positive word is
made an actual source.

The correspondence expressly stated in those sections imports Theorems
109.1/110.2 and prefix consequence 280.3 at their supplied scope. At a met
cap $0<c\le1$, any original competitor supplies some normalized complete
finite representative in its own class on
$H=\max(\{i:a_i>c\}\cup\{0\})$ bits. Vanishing makes $H$ finite.
Necessity covers arbitrary addresses and full-carrier outputs through
countability, sourcewise finite handoff, actual finite witnesses,
whole-schedule truncation and finite-simplex compactness. It preserves
class feasibility, not an arbitrary starting law or coupling.

For a shorter prefix, fix higher finite replies to zero, project higher
labels to zero and contract constant observations. For a longer prefix,
ignore added inputs. For a probability law $p$ supported on labels
$0,\ldots,K$ and any actual $n>K$, the exact identity is

$$
\operatorname{TV}(p,(1-a_n)e_0+a_ne_n)=\max\{1-p(0),a_n\}.
\tag{1.3}
$$

This handles newly represented first zeros and closed ties. On a positive
shorter prefix a higher first-zero target projects to the base point.
These are necessity representations, not free actual observations.
The normalized stopped criterion reused from 109.1 is $c_0\ge H_0$
coordinatewise, where
$p_w=c_0+\sum_i\ell_iw_i+\sum_{i<j}Q_{ij}w_iw_j$ and
$H_0=\sum_i(\sum_{j>i}(-Q_{ij})_+-\ell_i)_+$.
Normalization supplies its scalar schedule budget; degree two alone is
not that criterion.

**Definition 1.4 (The fixed unequal family).**
The original amplitudes are exactly

$$
\begin{gathered}
0<\tau\le1/24,\qquad0\le v\le u\le\tau,\qquad
a_1=a_2=1-11\tau,\\
(a_3,a_4,a_5,a_6,a_7)=(13,10,9,8,6)\tau,\qquad
a_8=5\tau+u,\quad a_9=5\tau+v,\\
a_{10}\ge a_{11}\ge\cdots>0,\qquad a_{10}\le5\tau,\qquad
a_n\longrightarrow0.
\tag{1.4}
\end{gathered}
$$

These give $1\ge a_1\ge a_2\ge\cdots>0$, since $24\tau\le1$ and
$a_8\le6\tau=a_7$. No summability is required. Write

$$
E_{\rm sum}=5\tau+\frac{11(u+v)}{128},\qquad
L_8=5\tau+\frac{11u}{117},\qquad
U=5\tau+\max\left\{\frac{22u}{181},\frac{11(u+v)}{128}\right\}.
\tag{1.5}
$$

## 2. Every word, independent rows and one allocation

**Definition 2.1 (The complete finite problem).**
For $L\ge3$ retain every word on $L$ bits, all labels $0,\ldots,L$, the positive word
$+=1^L$, and every first-zero fibre
$\Omega_n=\{w:w_1=\cdots=w_{n-1}=1,w_n=0\}$.
A table $N(i,j;r_{00},r_{01},r_{10},r_{11})$ allows independent outputs
on $00,01,10,11$. A table $O(i,j;r_0,r_{10},r_{11})$, $i<j$, uses
stopped cells $0,10,11$. Include constants and singletons. Reversal
permutes static cells; repetition gives singleton information without
refunding an actual call. Earlier unqueried output labels remain legal.

One normalized allocation is one $\lambda_D\ge0$ with
$\sum_D\lambda_D=1$, supplying
$p_w(\ell)=\sum_D\lambda_D[D(w)=\ell]$ at every word. Retain separately

$$
\begin{array}{c|c|c}
\text{row}&\text{event probability on }w\in\Omega_n&\text{demand}\\\hline
A&p_w(0)&1-b_n-e\\
C&p_w(n)&b_n-e\\
P&p_w(0)+p_w(n)&1-e
\end{array}
\qquad p_+(0)\ge1-e.
\tag{2.1}
$$

Negative singleton demands remain literal. For $b_n\in[0,1]$, putting
$c_n=p_w(n)$ and $D_n=1-p_w(0)-p_w(n)$ gives the exact TV

$$
\max\{c_n+D_n-b_n,\ b_n-c_n,\ D_n\}.
\tag{2.2}
$$

The union row is independent. All unscored rows remain constraints.

**Reused score 2.2 (The full nine-coordinate certificate).**
XVIII 318.1–318.2 supplies the complete nonnegative score $Y_{128}$ with

$$
\beta=(0,16,88,104,104,96,88,88,88),\quad K=1024,\quad
W=B_N=B_O=368,\quad\Delta_N=\Delta_O=0.
\tag{2.3}
$$

Use its full support theorem directly, including every independent $N$
cell output, every label, shorter and repeated schedules, and all ordered
embeddings. Its 46-row certificate is not reproved here. For the same
full feasible allocation it implies

$$
2b_2+11b_3+13b_4+13b_5+12b_6+11b_7+11b_8+11b_9
\le2+128e.
\tag{2.4}
$$

The supplied affine theorem also permits finite conic mass: with
$R=O(1,2;1,2,0)$, $r=z_R=d((1,1,0,\ldots,0),0)$,
$G_C=(z_D-r)_D$ and $h=d(b,e)-r$, its reused pairing is
$Yh\le YG_C\lambda\le M\Delta_C(Y)=0$.
Division by $M$ does not preserve an unchanged profile.
All constructed probability laws below have mass one.

## 3. Complete endpoint laws and the relabeling

**Construction 3.1 (The precise reused law $P^0$).**
Each row is $O(i,j;r_0,r_{10},r_{11})$ of mass $k/24$.
These are exactly the sixteen tables of XVIII 319.1.

| $i$ | $j$ | $r_0$ | $r_{10}$ | $r_{11}$ | $k$ |
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

The counts sum to 24. The $(1,4)$ first output is zero. The class-1
correct count is eleven, whereas the distinct head-filled law in XVII
300.1 has twelve. $P^0$ ignores bits eight and nine.

**Construction 3.2 (The precise reused law $P^\star$).**
The deterministic part of XVIII 320.1 consists of these sixteen rows,
with masses $k/3072$.

| $i$ | $j$ | $r_0$ | $r_{10}$ | $r_{11}$ | $k$ |
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

The five remaining schedule rows have these unnormalized label vectors;
all counts are divided by 3072, and $e_j$ is the label unit vector.
Each vector in a row has the same schedule count $m$.

| Schedule | $m$ | First vector | Middle vector | Exhaustion vector |
| --- | ---: | --- | --- | --- |
| $(1,2)$ | 944 | $944e_1$ | $944e_2$ | $463e_0+220e_3+162e_4+99e_5$ |
| $(2,3)$ | 391 | $333e_0+58e_2$ | $391e_3$ | $391e_0$ |
| $(3,4)$ | 236 | $236e_0$ | $236e_4$ | $148e_0+88e_5$ |
| $(6,7)$ | 74 | $74e_0$ | $74e_7$ | $17e_0+4e_8+53e_9$ |
| $(6,8)$ | 53 | $53e_0$ | $53e_8$ | $17e_0+36e_9$ |

The deterministic counts total 1374 and these schedule counts total
1698, giving the single total 3072. Counterfactual cell masses are not
added to that schedule budget.

For full-table weights, in each cell partition $[0,1)$ in label order,
with interval lengths equal to vector entries divided by $m$. Assign to
$O(i,j;r_0,r_{10},r_{11})$ mass

$$
\frac{m}{3072}
 |I_0(r_0)\cap I_{10}(r_{10})\cap I_{11}(r_{11})|.
\tag{3.1}
$$

The intersections partition one interval and recover every marginal.
Each displayed row has only one nonconstant cell, so equivalently split
its count by that cell's entries while retaining the other two labels.
This is exactly the supplied coupling: one local seed coordinate fixes
all counterfactual labels before replies.

**Reused endpoint facts 3.3 (Entire first-zero fibres).**
XVIII 319.2 proves all rows of $P^0$ at target
$(13,13,13,10,9,8,6,5,5)/24$ and cap $5/24$.
XVIII 320.2 proves all rows of $P^\star$ at target
$(13,13,13,10,9,8,6,6,6)/24$ and cap $662/3072$.
These cover every Boolean suffix. The exact correct counts needed here
are

$$
\begin{array}{c|rrrrrrrrr}
n&1&2&3&4&5&6&7&8&9\\\hline
24P^0_w(n)&11&8&8&5&4&3&1&0&0\\
3072P^\star_w(n)&1081&1002&1002&618&490&362&106&106&106
\end{array}
\tag{3.2}
$$

All independent outside-$\{0,n\}$ masses obey their respective caps.
The positive nonbase masses are $5/24$ and $662/3072$.
On the entire first-zero-8 and first-zero-9 fibres the $P^\star$
nonbase counts are respectively 728 and 679, by the restricted
polynomial identities of XVIII 320.5–320.7.
The complete endpoint proofs are reused, including their independent
union rows; these facts are not extrapolations from sole-zero words.

**Construction 3.4 (The law $Q$ and its exact event transfer).**
Replace exactly the $53/3072$ mass of $O(6,7;0,7,9)$ in $P^\star$
by the same mass of $O(6,7;0,7,8)$. All other tables remain unchanged.
The $(6,7)$ row now has vectors $74e_0$, $74e_7$, $17e_0+57e_8$,
still of count 74 each.

The change is active only when $w_6=w_7=1$. For every first-zero
class $n\le7$, both exchanged labels lie outside $\{0,n\}$.
Every $A,C,P$ event probability is therefore unchanged on the whole
fibre, regardless of later zeros. The positive base probability is
unchanged too. On a first-zero-8 word, bits 6 and 7 are one, so the
correct count increases by 53; on a first-zero-9 word it decreases
by 53. Base probability is unchanged in both cases. In units $1/3072$,

$$
\begin{array}{c|rr|rr}
\text{law}&c_8&c_9&Z_8&Z_9\\\hline
P^\star&106&106&728&679\\
Q&159&53&728&679
\end{array}
\qquad Z_n=3072[1-p_w(0)].
\tag{3.3}
$$

The new outside-pair counts are 569 and 626. These whole-fibre identities
use the precise supplied law and assert no new supporting score.

## 4. The one-budget law and its exact all-word error

**Theorem 4.1 (One complete allocation).**
For $x,y\ge0$, $W=x+y\le24\tau$, use the single law

$$
\lambda(x,y)=(1-24\tau)R+(24\tau-W)P^0+yP^\star+xQ,\qquad
R=O(1,2;1,2,0).
\tag{4.1}
$$

Its exact original error, for both its stopped realization and its counted
$N$ completion, is

$$
\max\left\{
5\tau+\frac{22W}{3072},\
5\tau+u-\frac{159x+106y}{3072},\
5\tau+v-\frac{53x+106y}{3072}\right\}.
\tag{4.2}
$$

Proof. The branch weights are nonnegative and sum to one. Each component
is a complete normalized law; identical tables can have their weights
added. No counterfactual cell receives an independent budget.
Put $t=W/24\in[0,\tau]$ and $h=5\tau+22W/3072$. On every first-zero
fibre through seven, and for the positive base event, (3.3) gives exactly
the event probabilities of the supplied equal-tail law

$$
(1-24\tau)R+24(\tau-t)P^0+24tP^\star.
\tag{4.3}
$$

XVIII 321.1's all-word affine endpoint argument proves every core
$A,C,P$ row at $h$ for the fixed core amplitudes. Equivalently,
probabilities and demands for each independent event are affine in
law, amplitudes and cap; apply the complete endpoint inequalities in
3.3 and the exact anchor rows to this one mixture. Multiple-zero suffixes,
negative singleton demands and independent union rows are all included.

On every class-2 word the correct mass is exactly

$$
(1-24\tau)+(24\tau-W)\frac8{24}+W\frac{1002}{3072}
=1-16\tau-\frac{22W}{3072}.
\tag{4.4}
$$

Its deficit is $h$, so this core bound is attained. The positive nonbase
mass is also exactly $h$.

Mixing the same full tables on the entire later first-zero fibres gives

$$
\begin{aligned}
c_8&=\frac{159x+106y}{3072},&
c_9&=\frac{53x+106y}{3072},\\
Z_8:=1-p_8(0)&=5\tau+\frac{88W}{3072},&
Z_9:=1-p_9(0)&=5\tau+\frac{39W}{3072},\\
D_8=Z_8-c_8&=5\tau-\frac{71x+18y}{3072},&
D_9=Z_9-c_9&=5\tau-\frac{14x+67y}{3072}.
\end{aligned}
\tag{4.5}
$$

The independent union deficits $D_8,D_9$ are at most $5\tau$.
Also $c_8,c_9\le159W/3072\le159\tau/128<5\tau\le a_8,a_9$.
Each base deficit $Z_n-a_n=c_n+D_n-a_n$ is consequently at most $D_n$.
The remaining correct deficits are precisely the last two entries in
(4.2). Thus $A,C,P$ are checked separately without clipping a demand.

For every actual $n>9$, the output is the finite positive law and no
label $n$ is emitted. By (1.3) its exact error is
$\max\{h,a_n\}=h$, because $a_n\le5\tau\le h$.
All finite first-zero fibres have actual witnesses. The attained core
deficit and the two exact later correct deficits give the lower direction
in (4.2), and all other rows give its upper direction. The original
resource realization is 6.1. $\square$

**Corollary 4.2 (The design criterion and its scope).**
For the law (4.1) at cap $e=5\tau+d$, its exact cap criterion is

$$
22W\le3072d,\qquad159x+106y\ge3072(u-d),\qquad
53x+106y\ge3072(v-d),
\tag{4.6}
$$

together with $x,y\ge0$, $W=x+y\le24\tau$. This characterizes the
displayed construction only. It is not full-catalog necessity.

## 5. Exact attained wedge and entire-family upper bound

**Theorem 5.1 (The attained wedge).**
If (1.4) holds and $181v\ge75u$, both original minima are attained and

$$
\min_{A\in\mathcal N_2}e_a(A)
=\min_{A\in\mathcal O_2}e_a(A)=E_{\rm sum}.
\tag{5.1}
$$

Every positive closed cap $c$ is feasible in either class exactly when
$c\ge E_{\rm sum}$.

Proof. Set in (4.1)

$$
x=\frac{1536}{53}(u-v),\qquad
y=12(u+v)-x=\frac{12}{53}(181v-75u),\qquad W=12(u+v).
\tag{5.2}
$$

The weights are nonnegative and $W\le24\tau$. The identities

$$
181x+128y=3072u,\qquad75x+128y=3072v,\qquad
22W/3072=11(u+v)/128
\tag{5.3}
$$

make all three entries of (4.2) equal to $E_{\rm sum}$.

For every original competitor the full $N$ score (2.4), with its original
closed-cap transport, gives

$$
128e_a(A)\ge
2a_2-2+11a_3+13a_4+13a_5+12a_6+11a_7+11(a_8+a_9)
=640\tau+11(u+v).
\tag{5.4}
$$

Here the three contributions are $-22\tau$, $552\tau$ and
$110\tau+11(u+v)$. Apply the score at positive caps decreasing to the
actual error; representatives may change with the cap. A smaller cap
activating more tail coordinates remains covered by 1.3. At error one
the bound is immediate from $E_{\rm sum}\le331/1536<1$.
Counted completion gives the same lower bound for stopped competitors.
It matches the explicit common law, and that law works at every larger
cap. This proves attainment and the closed-cap classification. $\square$

**Theorem 5.2 (The common upper law on the entire family).**
On $181v\le75u$, choose

$$
x=3072u/181,\qquad y=0,\qquad W=x
\tag{5.5}
$$

in (4.1). Its exact error is $5\tau+22u/181$. Together with (5.2),
this yields the upper bound $U$ on the entire fixed family.

Proof. Since $3072/181<24$ and $u\le\tau$, all weights are nonnegative.
The entries of (4.2) become

$$
5\tau+22u/181,\qquad5\tau+22u/181,\qquad5\tau+v-53u/181.
\tag{5.6}
$$

The last is at most the first precisely when $181v\le75u$.
Also $22u/181\ge11(u+v)/128$ is equivalent to that condition.
This evaluates this law and supplies $U$; it does not evaluate the
full-catalog complementary minimum. $\square$

## 6. Actual execution and all parameter boundaries

**Realization 6.1 (Common seed and counted requests).**
Partition one source-independent uniform seed in $[0,1)$ into the
complete-table intervals of (4.1), omitting zero weights. Equivalently,
choose its branch and schedule interval and use the same rescaled
coordinate for every quantile partition in (3.1). Half-open intervals
specify endpoints. The seed fixes the entire schedule and all
counterfactual labels before any reply.

Execute the selected increasing schedule in $O$ until its first queried
zero or exhaustion, then hand off its actual $\theta_j$ to the unchanged
consumer. Every source and seed terminates finitely and measurably,
with zero advice and at most two actual calls. Its $N$ completion obtains
the whole same schedule on the same actual source and seed and reconstructs
the stopped output; ignored replies count. This construction gives equal
laws without stopping an arbitrary competing $N$ rule.

**Boundary statement 6.2 (Closed parameters and active horizons).**
At $181v=75u$ the prescriptions (5.2) and (5.5) coincide and $y=0$.
At $v=u$, $x=0$ and $y=24u$, exactly the reused equal-tail law of XVIII
321.1. At $u=v=0$ both later branches vanish and the reused seven-active
law attains $5\tau$. At $\tau=1/24$ the $R$ branch vanishes.
At $u=v=\tau$ the $P^0$ branch vanishes. The cases $u=\tau$, $v=0$,
$a_8=a_7$, $a_{10}=5\tau$ and all other allowed tail ties are included.
There is no division by $u$, $v$ or a vanishing branch mass.
The algebraic $\tau=0$ degeneration is outside the original positive
sequence assertion.

On the exact wedge with $u>0$,
$a_9-E_{\rm sum}=(117v-11u)/128>0$, since $v\ge75u/181$.
The active horizon is nine; at $u=v=0$ it is seven.
At the complementary displayed upper cap with $u>0$, $a_8$ is active;
the horizon is eight for $v\le22u/181$ and nine for $v>22u/181$.
Equality is inactive under the convention $a_i>c$.
All later amplitudes are inactive at these upper caps.
These statements do not describe the unknown complementary minimizing
horizons.

As a concrete single-budget boundary, take $\tau=u=1/24$ and
$v=75u/181$. The branch weights on $R,P^0,P^\star,Q$ are
$0,53/181,0,128/181$. The combined $(6,7)$ schedule has mass
$127/4344$ and vectors

$$
\frac{127}{4344}e_0,\qquad\frac{127}{4344}e_7,\qquad
\frac{70e_0+57e_8}{4344}.
\tag{6.1}
$$

Each counterfactual cell has the same schedule mass, counted once.
Every finite positive prefix and later first-zero fibre used above is
actual. Arbitrarily slow positive vanishing tails are allowed, without
an infinite all-positive actual source or an extra request.

## 7. The stronger eight-prefix lower consequence

**Lemma 7.1 (The same-law inactive-coordinate bridge).**
Suppose a complete normalized eight-bit $N$ allocation satisfies all
rows (2.1) at $b_i\in[0,1]$ and $e\in[0,1]$. No order, active-length,
hull or $b_2=b_3$ hypothesis is needed. Then

$$
2b_2+11b_3+13b_4+13b_5+12b_6+11b_7+11b_8\le2+117e.
\tag{7.1}
$$

Proof. Extend each table to nine inputs by ignoring input nine, with
identical weights, schedules and outputs in $0,\ldots,8$.
Use $b'_i=b_i$ for $i\le8$ and the auxiliary amplitude $b'_9=e$.
Each old first-zero word, for either ninth bit, copies all three old
event probabilities and demands. At the new first-zero word $1^8 0$,
put $q=p_+(0)\ge1-e$. Its $A,C,P$ probabilities are $(q,0,q)$ and
demands $(1-2e,0,1-e)$. All hold separately. At $1^9$ the positive
row remains $q\ge1-e$. Thus one complete mass-one law satisfies every
nine-bit row. At $e=0$ one has $q=1$; at $e=1$ the new demands are
$(-1,0,0)$. No condition $b_8\ge e$ is used.

Apply the existing full inequality (2.4) to this law and subtract its
last term $11b'_9=11e$. This proves (7.1).
The ninth coordinate costs no query because every table ignores it.
This is a same-law application of XVIII 318.2, not a new score or an
unchanged-profile extension for arbitrary conic mass. $\square$

**Theorem 7.2 (Explicit lower bound for every allowed actual continuation).**
Every original competitor in either class under (1.4) satisfies

$$
e_a(A)\ge L_8=5\tau+11u/117.
\tag{7.2}
$$

Proof. Let an original $N$ rule meet $0<c\le1$ and take its credited
normalized representative on its actual finite active horizon $H$.
For $H>8$, fix higher replies to zero, project labels above eight to
zero and contract constant observations. Every low first-zero target
is unchanged. On the positive eight-prefix, the higher first-zero
target projects to the base point, giving $p_+(0)\ge1-c$ regardless
of actual $a_9$. For $H=8$ use the representative directly.
For $H<8$, ignore the added inputs. Each newly represented first zero
has $a_n\le c$ and the old positive law has no mass at its label;
(1.3) verifies every row. This includes $H=0$, all multiple-zero words,
closed ties and negative demands. Hence there is one complete normalized
eight-bit law at $(a_1,\ldots,a_8;c)$.

Apply Lemma 7.1 to this law. Its sum is

$$
2a_2+11a_3+13a_4+13a_5+12a_6+11a_7+11a_8
=(2-22\tau)+552\tau+55\tau+11u
=2+585\tau+11u.
\tag{7.3}
$$

Thus $c\ge5\tau+11u/117$. Decrease positive met caps to any actual
error below one, including hypothetical zero error. At error one the
bound follows from $L_8\le596/(117\cdot24)<1$.
Counted $N$ completion proves the stopped-competitor conclusion.

In the positive-width parameterization $a_8=5\tau+11\delta$,
$r_0=5\tau+\delta$, the correspondence is exactly $\delta=u/11$.
For $u>0$ it satisfies $0<\delta\le\tau/11$.
The required head interval $a_2\le a_1\le1-7\tau$ holds because
$a_1=a_2=1-11\tau$. Also $a_9\le a_8$, and the full stipulated
continuation is positive, ordered and vanishing.
Actual $a_9$ can exceed the cap: it is not replaced in the original
sequence. Only the necessity representation receives $b'_9=c$ in
Lemma 7.1. At $u=0$ the boxed bridge and direct substitution still
hold without asserting positive width.

The same deduction can be written with $S=\sum_{3}^8b_n$,

$$
s=1+44e-b_2-4b_3-5b_4-5b_5-5b_6-4b_7-4b_8,\qquad
g=3S-b_6-29e.
\tag{7.4}
$$

Expansion of (7.1) is exactly $g\le2s$. With $\delta=u/11$ and
$t=e-r_0$, one has $s=44t$ and $g=4\delta-29t$, so
$4\delta\le117t$. This is the same stronger consequence
$e\ge r_0+4\delta/117$, not an independent score result. $\square$

**Corollary 7.3 (Valid exclusions and the boundary).**
For $u>0$, the bound $L_8$ exceeds the six-late value
$r_0=5\tau+u/11$ by exactly $4u/1287>0$, uniformly in $v$ and the
allowed continuation. Also

$$
L_8-E_{\rm sum}=\frac{11(11u-117v)}{14976}.
\tag{7.5}
$$

Consequently the cap $E_{\rm sum}$ is infeasible in both classes
whenever $u>0$ and $117v<11u$.
At $117v=11u$ these two lower bounds coincide; this argument does not
exclude their common cap. No matching law for $L_8$ is asserted.

## 8. Compact minima and independence from the later tail

**Theorem 8.1 (Separate compact problems equal original attained minima).**
For $C=N,O$, let $\Delta_C^9$ be the probability simplex of its own
complete deterministic nine-bit catalog, with all labels $0,\ldots,9$,
constants and singletons. For $N$, all four cell outputs remain
independent. Set

$$
\begin{aligned}
f_C(\lambda)=\max\bigl(&
\{1-a_n-p_w(0),\ a_n-p_w(n),\ 1-p_w(0)-p_w(n):
                           w\in\Omega_n,\ n\le9\}\\
&\cup\{1-p_+(0)\}\bigr),\qquad
m_C=\min_{\lambda\in\Delta_C^9} f_C(\lambda).
\end{aligned}
\tag{8.1}
$$

Both minima exist, equal their respective original attained minima,
and depend only on $a_1,\ldots,a_9$ among all continuations in (1.4).
For each class its positive closed caps are feasible exactly when $c\ge m_C$.
Throughout the family,

$$
\max\{E_{\rm sum},L_8\}\le m_N\le m_O\le U.
\tag{8.2}
$$

Proof. Each catalog is finite. The objective is a finite maximum of
continuous affine functions on a compact simplex, so it has a minimizer
separately in each class. This proves existence, not an evaluation.

The full core inequality of XVII 312.2 embedded in either catalog gives

$$
43f_C\ge5a_3+5a_4+4a_5+5a_6+4a_7=215\tau.
\tag{8.3}
$$

Thus $m_C\ge5\tau>0$. The explicit common law gives
$m_C\le U\le331\tau/64\le331/1536<1$.

For any original competitor of error $r<1$, take positive caps
decreasing to $r$ and apply the own-class correspondence and prefix
operations of 1.3 to obtain complete nine-bit representatives with
$f_C\le c$. Hence $m_C\le r$. Active horizons and representatives can
change; no common limiting law is required. At $r=1$ the same comparison
follows from $m_C<1$.

Conversely select a finite minimizer by one uniform-seed partition of its
complete tables. Execute it in its own original class: $N$ obtains the
whole preselected schedule, and $O$ executes its increasing schedule to
first queried zero or exhaustion. Emit actual marks. Every seed and
source hands off finitely and measurably, with zero advice and at most
two actual requests. Every actual first absence through nine has error
at most $m_C$ by (8.1). For every actual $n>9$, (1.3) gives

$$
\operatorname{TV}(p_+,(1-a_n)e_0+a_ne_n)
=\max\{1-p_+(0),a_n\}\le m_C,
\tag{8.4}
$$

because the positive row holds and $a_n\le5\tau\le m_C$.
This finite minimizer attains original error at most $m_C$.
The preceding comparison with every original competitor proves equality
and original attainment, separately for $N$ and $O$.

The definition (8.1) uses only the first nine amplitudes. Equation (8.4)
works for every allowed continuation, including $a_{10}=5\tau$, so both
original minima are separately tail independent on exactly this domain.
Counted completion gives $m_N\le m_O$; (5.4) and Theorem 7.2 give the
two lower bounds, and the common law gives $U$.
No equality of the two complementary minima follows from existence.
The attained minimizer meets every cap at least $m_C$, and the lower
comparison excludes every smaller positive cap.
$\square$

## 9. Full-score face, unresolved complement and result boundaries

**Proposition 9.1 (The finite face question at $E_{\rm sum}$).**
In either unchanged nine-bit catalog, feasibility at $E_{\rm sum}$ is
equivalent to one normalized allocation on complete $Y_{128}$-score-368
maximizers satisfying every full row. Every positively scored row must
then be tight. All unscored $A,C,P$ and positive rows remain constraints.

Proof. At this cap the demanded score equals 368 by (5.4). For a normalized
full feasible allocation,

$$
0=\sum_D\lambda_D(368-Y_{128}z_D)
 +\sum_{\text{rows }r}Y_{128}(r)
       [p_\lambda(\text{event }r)-\text{demand }r].
\tag{9.1}
$$

All summands are nonnegative by full support and feasibility. This
forces maximizing support and tight scored rows. Conversely, one
allocation of those tables satisfying all rows is feasible.
The tail is below this cap, so the original realization applies.
The criterion is separate in $N$ and $O$; their catalogs are not
identified. $\square$

The explicit law solves this intersection on $181v\ge75u$.
The eight-prefix bound excludes it when $u>0$ and $117v<11u$.
For $u>0$ and $11u/117\le v<75u/181$, these arguments do not settle
the intersection, including $117v=11u$.

A sufficient missing full-$N$ necessary relation for matching the
complementary upper law would be

$$
181(e-5\tau)\ge22u\qquad\text{when }181v\le75u.
\tag{9.2}
$$

This relation is unproved for the full catalog. Eliminating $x,y$ from
(4.6) cannot prove it. On $181v<75u$, $U$ remains an explicit upper
bound. Compact attainment and the available necessary bounds do not
evaluate either minimum or prove their equality there.
Falsity of (9.2) would give a full $N$ feasible law below $U$, with
original realization in this tail regime. It would not alone give an
improved stopped common law or equality $m_N=m_O$.

The result identity is the relabeling $Q$, its whole-fibre event transfer,
the unequal one-budget law, the exact attained wedge, the entire-family
upper bound and the compact tail correspondence. The stronger eight-prefix
inequality is an application of the existing full $Y_{128}$ score.
Source arithmetic, closed-cap transport, full score support, all-word
endpoint proofs and equal-tail attainment retain their cited roles,
without repeat discovery credit.

The whole-vector framework cited in XVII 303.3 and XVIII 323.2 is
Blackwell, *Comparison of Experiments*, sections 2–3 and Theorem 2,
concerning whole attainable loss vectors. The scalar-expectation
framework cited there is Kaniewski–Lee–de Wolf, *Query complexity in
expectation*, arXiv:1411.7280v1, Definitions 6 and 8 and Theorem 9.
Sampling coefficients of mass $M$ and rescaling a scalar output by $M$
does not furnish a normalized joint output law, equal counterfactual
schedule masses or increasing first-queried-zero execution.
These references carry their specified framework roles, without an
exhaustive literature or priority claim.

The unrestricted signed-budget question of XVII 314.1 and XVIII 323.1
remains outside these results: for every full unit-$O$ score $y$, find
one unrestricted full $V\ge0$ and $\theta\in[0,1]$ with
$\Delta_N(V)+\theta\le1$ and $\sigma_H(Qy-QV)\le\theta$, or supply the
complete same-profile original separator. Here $Qy$ is the score quotient
of those sources, distinct from the law $Q$ in 3.4.
The residual remains signed; nonzero zero-cost $V$ at $\theta=1$ is
allowed. General $N/O$ replacement or separation, common-map questions
and acquisition for the unchanged nonatomic targets remain outside this
fixed marked-target result.

The stopping point is (8.2), its exact wedge, the strict exclusions in
7.3 and the missing relation (9.2). These are ordinary proofs and
applications in the selected marked-target model. They assert no kernel
verification, global originality, physical efficiency, general
neural-network or empirical-learning consequence, or completion of the
unrestricted acquisition problem.

## 追加锚（本行以下为增补区）

