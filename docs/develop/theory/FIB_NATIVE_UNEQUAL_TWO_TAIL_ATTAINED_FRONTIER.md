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

## 10. The eight-prefix problem and the base-to-eight theorem

**Definition 10.1 (Domain, complete catalogs and credited premises).**
Retain exactly the original objects of 1.1–1.4. In particular,

$$
0<\tau\le1/24,\qquad 0\le v\le u\le\tau,\qquad
a_8=5\tau+u,\qquad a_9=5\tau+v,
\tag{10.1}
$$

and every actual continuation satisfies
$a_{10}\ge a_{11}\ge\cdots>0$, $a_{10}\le5\tau$, and $a_n\to0$.
At $v=0$ the actual ninth amplitude is $5\tau>0$.
For $C=N,O$, let $\nu_C(\tau,u)$ be the minimum of the complete
eight-bit objective (8.1), with nine replaced by eight and labels
$0,\ldots,8$, in that class's own normalized complete catalog.
All three independent events and the positive row are included.
The $N$ catalog retains four independent cell outputs, arbitrary labels,
constants, singletons, reversals and repetitions. Constructing one
stopped law imposes no restriction on these competitors.

The construction $K$ below, its conditional union slack and its
217 denominator are credited to the supplied complete
whole-counterexample-proposal.json; the supplied
whole-independent-ordinary-check.json supplies an independent ordinary
verification. Their assertions are fallible mathematical inputs.
The complete allocation and the proofs of the new conclusions are
given here. The sixteen-table $P^0$, $P^\star$, their endpoint
polynomials and full-word bounds, and the transfer $Q$ retain the
credits of 3.1–3.4 and XVIII 319–320, 324–327.
The full-score lower bounds, arithmetic realization and original
closed-cap correspondence retain the credits of 1.3, 2.2 and 7.
The supplied complete XVIII includes 324–330.

**Theorem 10.2 (A common 217 upper law and its exact original error).**
For every parameter and every entire actual continuation in (1.4),
there is one normalized law $K$, using addresses at most eight,
whose stopped $O$ execution and counted $N$ execution have identical
output laws and exact original marked-target error

$$
e_a(K)=5\tau+\max\left\{\frac{22u}{217},v\right\}.
\tag{10.2}
$$

Its complete eight-bit maximum error is exactly

$$
h=5\tau+\frac{22u}{217},
\qquad
\nu_N(\tau,u)\le\nu_O(\tau,u)\le h.
\tag{10.3}
$$

For $u>0$, (10.3) is strictly below
$T=5\tau+22u/181$. In the original family this same law is strictly
below $T$ exactly when $v<22u/181$.
Thus the proposed universal complementary original lower relation
(9.2) is false: for every $0<\tau\le1/24$ and $0<u\le\tau$,
the permitted choice $v=0$, with every allowed actual continuation,
supplies an original counterexample in both classes.
This statement evaluates the displayed law, not either full minimum.
The construction and proof occupy 11–14; a rational actual witness
is given in 15.

## 11. A complete projected law and one conserved schedule budget

**Definition 11.1 (The exact law $Q_8$).**
Start with the genuine $P^\star$ of 3.2, make exactly the 53-count
label-nine-to-eight transfer of 3.4, fix its ninth input to zero,
and project every output label nine to zero. This defines a new
eight-bit law $Q_8$; fixing a finite input in its definition gives
the acquisition no observation of the actual ninth reply.
The 26 pair tables below, and the constant-zero table of count 17,
are its complete deterministic allocation. Each count is divided
by 3072. The columns $f,m,z$ are the outputs on stopped cells
$0,10,11$; its counted completion has outputs $f,f,m,z$ on
$00,01,10,11$.

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
| 1 | 2 | 1 | 2 | 0 | 463 |
| 1 | 2 | 1 | 2 | 3 | 220 |
| 1 | 2 | 1 | 2 | 4 | 162 |
| 1 | 2 | 1 | 2 | 5 | 99 |
| 2 | 3 | 0 | 3 | 0 | 333 |
| 2 | 3 | 2 | 3 | 0 | 58 |
| 3 | 4 | 0 | 4 | 0 | 148 |
| 3 | 4 | 0 | 4 | 5 | 88 |
| 6 | 7 | 0 | 7 | 0 | 17 |
| 6 | 7 | 0 | 7 | 8 | 57 |
| 6 | 8 | 0 | 8 | 0 | 53 |

The constant-zero table makes no requests. In the restriction of
$P^\star$, its former $O(8,9;0,9,0)$ branch of count 17 is
constant zero. The $(6,8)$ exhaustion vector becomes $53e_0$,
and the $(6,7)$ exhaustion vector is $17e_0+57e_8$.
The other mixed rows split exactly as in 3.2.
The original deterministic and mixed schedule counts were 1374 and
1698, with single total 3072. Restriction, label projection and
splitting preserve that total. These are weights on complete tables;
counterfactual cell masses are counted once per schedule.

For completeness, when a schedule of mass $\mu>0$ is specified by
three equal-mass cell vectors, partition $[0,1)$ in each cell into
increasing-label half-open intervals $I_0(f),I_{10}(m),I_{11}(z)$,
whose lengths are the respective entries divided by $\mu$.
Its complete-table weight is

$$
\mu\,|I_0(f)\cap I_{10}(m)\cap I_{11}(z)|.
\tag{11.1}
$$

The intersections partition one interval and recover all cell
marginals with total mass $\mu$. Every mixed row used here has only
one nonconstant cell, so the displayed splitting is also immediate.
One local coordinate of the same seed fixes all counterfactual
labels before any reply. Zero-mass intervals are omitted.

**Definition 11.2 (The complete law $K$).**
Let $R=O(1,2;1,2,0)$ and let $P^0$ be precisely the complete
sixteen-table law in 3.1, including $O(1,4;0,4,0)$.
Set

$$
s=\frac{u}{217},\qquad W=3072s,\qquad \varepsilon=36s,\qquad
L=(1-24\tau)R+(24\tau-W)P^0+WQ_8.
\tag{11.2}
$$

In the $P^0$ component replace mass $\varepsilon$ of
$D_0=O(6,7;0,7,0)$ by the same mass of
$D_8=O(6,7;0,7,8)$, keeping the whole schedule and its other
two cell labels. The resulting law is

$$
K=L+\varepsilon(D_8-D_0).
\tag{11.3}
$$

Equation (11.3) denotes a transfer of existing stock.
Explicitly, each count-$k$ row of 3.1 receives mass
$k(\tau-128s)$, each count-$k$ row of 11.1 receives mass $ks$,
and $R$ receives $1-24\tau$. Subtract $36s$ from the indicated
$P^0$ donor and add it to $D_8$. Coincident complete-table
weights add. These instructions specify every final weight.

**Lemma 11.3 (Nonnegative donor stock and the full-vector identity).**
The allocation $K$ is nonnegative, normalized, and legal in both
complete finite catalogs. For every eight-bit word,

$$
K_w-L_w=36s\,w_6w_7(e_8-e_0).
\tag{11.4}
$$

Proof. The starting branch weights are nonnegative and sum to one:
$1-24\tau\ge0$, $W\ge0$, and
$24\tau-W=24(\tau-128s)>0$, since $u\le\tau$ and $128<217$.
The donor's precise remaining $P^0$ stock is

$$
\tau-128s-36s=\tau-164s\ge\frac{53\tau}{217}>0.
\tag{11.5}
$$

All other weights are nonnegative. After coincident rows are added,
the total $D_0$ weight is $\tau-147s$ and the total $D_8$
weight is $93s$; their common $(6,7)$ schedule mass is
$\tau-54s$. The transfer preserves the total probability and every
cell's total mass. Thus one normalized complete-table allocation
supplies all words and events.

Only the exhaustion cell of $(6,7)$ changes. Its indicator on
every word is $w_6w_7$, independently of every other zero, and
its vector change is $36s(e_8-e_0)$. This proves (11.4) on
the entire cube. No address depends on a reply. The counted
$N$ table $N(i,j;f,f,m,z)$ and the corresponding stopped
table are both legal. $\square$

## 12. The entire activation set and the positive-word allowance

**Lemma 12.1 (The conditional $P^0$ union slack).**
For every core first-zero word $n\le7$ with $w_6=w_7=1$,
the outside-$\{0,n\}$ probability of $P^0$ is at most $4/24$.
This includes every multiple-zero suffix where (11.4) acts.

Proof. Record the precise reused full-word polynomials of XVIII
319.2, now with $(b,c,d,z,t)=(w_3,w_4,w_5,w_6,w_7)$:

$$
\begin{aligned}
B&=2b(1-c)+bc+(b+c)(2-d-z)+d(1-z)+z(1-t),\\
G&=3(1-b)+(1-c).
\end{aligned}
\tag{12.1}
$$

Direct evaluation of the complete tables of 3.1 gives the following
outside counts, all in units $1/24$:

$$
\begin{array}{c|l}
n&24D_n(P^0)\\ \hline
1&B+w_2G\\
2&B+G\\
3&2+2(1-c)+c(2-d-z)+d(1-z)+z(1-t)\\
4&3+(1-d)+(1-z)+d(1-z)+z(1-t)\\
5&3+2(1-z)+z(1-t)\\
6&5\\
7&5
\end{array}
\tag{12.2}
$$

These identities retain all suffix bits. For example, the two
$(3,4)$ tables give $2b(1-c)+bc$, the four edges from
$3,4$ to $5,6$ give $(b+c)(2-d-z)$, and the final edges
give $d(1-z)+z(1-t)$. The head-to-$3,4$ contributions
give $w_2G$ and $G$ in the first two classes.
The correct counts are the reused
$(11,8,8,5,4,3,1)$.

The global bound five in 3.3 is visible from these identities.
For $q=b+c$, maximizing
$q(2-d-z)+d(1-z)+z(1-t)$ over $t$ at
$dz=00,01,10,11$ gives $2q,q+1,q+1,1$.
The maxima for $bc=00,01,10,11$ are $1,2,2,4$;
adding $2b(1-c)+bc+G$ gives five in each case.
Thus $B+G\le5$, and $B+w_2G\le5$ because $G\ge0$.
In class three, $c=0$ gives
$4+d(1-z)+z(1-t)\le5$, since the last two terms cannot
both be one; $c=1$ gives $4-dz-zt\le4$.
The next two expressions simplify to $5-dz-zt$ and
$5-z-zt$, and the final two are constant.

For the asserted stronger conditional bound set $z=t=1$.
Now

$$
B=2b(1-c)+bc+(b+c)(1-d),\qquad G=3(1-b)+(1-c).
\tag{12.3}
$$

For $bc=00,01,10,11$ the exact values of $B+G$ are,
respectively,

$$
4,\qquad4-d,\qquad4-d,\qquad3-2d.
\tag{12.4}
$$

All are at most four. This proves both first two classes, since
$B+w_2G\le B+G$. Class three becomes
$2+2(1-c)+c(1-d)=4-c-cd\le4$.
Class four becomes $4-d\le4$, and class five becomes three.
Classes six and seven cannot have $w_6=w_7=1$.
The eighth bit is ignored by $P^0$, so every free suffix is
included. $\square$

**Lemma 12.2 (The same-law $Q_8$ core bounds and later vectors).**
On every core first-zero fibre $n\le7$, $Q_8$ has correct
counts

$$
(1081,1002,1002,618,490,362,106)/3072
\tag{12.5}
$$

and outside-$\{0,n\}$ mass at most $662/3072$.
Its later and positive vectors are exactly

$$
\begin{aligned}
(Q_8)_8&=\frac{2344e_0+220e_3+162e_4+187e_5+159e_8}{3072},\\
(Q_8)_+&=\frac{2446e_0+220e_3+162e_4+187e_5+57e_8}{3072}.
\end{aligned}
\tag{12.6}
$$

Thus its positive nonbase count is 626, leaving 36 counts below
the core endpoint allowance 662.

Proof. The reused all-word theorem XVIII 320.2 supplies (12.5)
and the outside bound for the genuine $P^\star$. Its complete
polynomial certificate, with $x_i=w_i$, is

$$
\begin{aligned}
3072[1-P^\star_x(0)]
 &=J+A x_6+B(x_7+x_8)
       -17(x_6x_7+x_6x_8+x_7x_8+x_8x_9),\\
A&=127-125x_3-110x_4-127x_5,\qquad
B=17-15x_3-17x_5,\\
J&=1139+391x_1+470x_2+523x_3+227x_4+161x_5\\
 &\quad-463x_1x_2-391x_1x_3-110x_1x_4-27x_1x_5\\
 &\quad-391x_2x_3-110x_2x_4-27x_2x_5
       -148x_3x_4-132x_3x_5-117x_4x_5.
\end{aligned}
\tag{12.7}
$$

Each schedule contributes its nonbase first count times $(1-x_i)$,
middle count times $x_i(1-x_j)$ and exhaustion count times $x_ix_j$.
For fixed $x_1,\ldots,x_5$, $B\le17$ and the suffix maximum
is $J+\max\{0,A,B\}$: take $x_9=0$; at $x_6=0$ the
remaining maximum is $\max\{0,B,2B-17\}=\max\{0,B\}$,
and at $x_6=1$ the remaining coefficients are nonpositive,
giving maximum $A$.
The credited grouped outside-count maxima, in lexicographic order
of all free bits through five, are

$$
\begin{array}{c|l}
n&\text{complete grouped maxima}\\ \hline
1&185,219,302,329,583,610,662,572,655,662,662,662,662,662,631,514\\
2&655,662,662,662,662,662,631,514\\
3&662,642,559,532\\
4&662,635\\
5&649
\end{array}
\tag{12.8}
$$

For classes six and seven the restricted nonbase polynomials are
$995-15(x_7+x_8)-17(x_7x_8+x_8x_9)$ and
$760-32x_8-17x_8x_9$; subtracting their correct counts gives
outside maxima 633 and 654. These are the supplied full-word
endpoint bounds, with no sole-zero restriction.

The 53-count transfer from nine to eight preserves every core
$A,C,P$ event on every word. Fixing input nine to zero retains
all eight-bit core words, and projecting label nine to zero
preserves correct mass and can only increase base and union mass.
This proves the claimed core bounds for the actual law $Q_8$.

To derive (12.6) directly from its complete tables, the persistent
non-tail nonbase counts are $220,162,99+88=187$.
On first-zero eight its correct contributions are
$15+17+17+53+57=159$; nonbase total is 728 and base is 2344.
On the positive eight-word the four middle contributions of total
102 disappear into base, while the $(6,7)$ exhaustion contribution
57 remains. Thus its nonbase total is 626 and base is 2446.
All these counts come from the same allocation. $\square$

## 13. Every independent row of $K$ on every word

**Theorem 13.1 (Exact complete eight-bit error).**
At the first eight amplitudes of (1.4), the law 11.2 satisfies every
$A,C,P$ row and the positive row at cap $h=5\tau+22s$.
Its complete maximum error is exactly $h$.

Proof. Nonnegative normalized complete-table weights were proved
in 11.3, so all evaluated vectors are probability vectors.
Let $c_n=K_w(n)$ and $D_n=1-K_w(0)-K_w(n)$ on a word
with first zero $n$. By (2.2), its three independent deficits are
$c_n+D_n-a_n$, $a_n-c_n$, and $D_n$.

The transfer changes only labels zero and eight. The complete
$P^0$ and $Q_8$ correct counts therefore give, constantly on
each entire first-zero fibre,

$$
\begin{array}{c|l|l}
n&c_n&a_n-c_n\\ \hline
1&1-13\tau-327s&2\tau+327s\\
2&1-16\tau-22s&5\tau+22s\\
3&8\tau-22s&5\tau+22s\\
4&5\tau-22s&5\tau+22s\\
5&4\tau-22s&5\tau+22s\\
6&3\tau-22s&5\tau+22s\\
7&\tau-22s&5\tau+22s\\
8&195s&5\tau+22s
\end{array}
\tag{13.1}
$$

For the first two entries the sums are
$(1-24\tau)+11(\tau-128s)+1081s$ and
$(1-24\tau)+8(\tau-128s)+1002s$.
The remaining core entries follow in the same way from the printed
correct counts. In class eight, (12.6) supplies $159s$ and
(11.4) adds $36s$, while $u=217s$.
All deficits in the last column are nonnegative.
The first is at most $h$, because
$305s\le305\tau/217<3\tau$.
Thus every $C$ row holds, and $c_n\le a_n$ in every class.

The independent $P$ rows require a separate full-word bound.
The anchor $R$ has no outside-$\{0,n\}$ mass on any core
word. If $n\le7$ and $w_6w_7=0$, the transfer is inactive,
and the full-word bounds of 12.1–12.2 give

$$
D_n\le(24\tau-3072s)\frac5{24}
          +(3072s)\frac{662}{3072}
      =5\tau+22s=h.
\tag{13.2}
$$

If $n\le7$ and $w_6w_7=1$, then $n\le5$ and the
conditional $P^0$ bound is four rather than five.
Label eight is outside $\{0,n\}$, so the transfer adds $36s$
to this independent deficit. Consequently

$$
\begin{aligned}
D_n&\le(24\tau-3072s)\frac4{24}
           +(3072s)\frac{662}{3072}+36s
       =4\tau+186s,\\
h-D_n&\ge\tau-164s\ge53\tau/217>0.
\end{aligned}
\tag{13.3}
$$

This is the full activation-set check, including every multiple-zero
suffix; it uses neither a marginal-only table nor sole-zero samples.

In class eight, $R$ emits zero, $P^0$ has outside mass $5/24$,
and $Q_8$ has outside count $728-159=569$.
The transfer stays inside $\{0,8\}$, so

$$
D_8=(24\tau-3072s)\frac5{24}
             +(3072s)\frac{569}{3072}
       =5\tau-71s\le5\tau\le h.
\tag{13.4}
$$

All $P$ rows are now proved independently.
For each word the $A$ deficit is
$c_n+D_n-a_n=D_n-(a_n-c_n)\le D_n\le h$,
using the separately proved $c_n\le a_n$.
Every $A$ row therefore holds, including negative demands.

At the positive eight-word, (12.6) gives for $L$ nonbase mass
$5(\tau-128s)+626s=5\tau-14s$.
The transfer adds exactly $36s$, giving $h$.
The exact positive and first-zero-eight vectors are

$$
\begin{aligned}
K_+={}&(1-h)e_0+(2\tau-36s)e_3+(\tau+34s)e_4
                    +(2\tau-69s)e_5+93s e_8,\\
K_8={}&(1-5\tau-124s)e_0+(2\tau-36s)e_3+(\tau+34s)e_4
                    +(2\tau-69s)e_5+195s e_8.
\end{aligned}
\tag{13.5}
$$

Hence the positive row is equality. The three class-eight deficits
are $-93s,h,5\tau-71s$, respectively.
Every fibre $n=2,\ldots,8$ also has correct deficit exactly $h$.
This proves the exact full eight-bit error, as well as the upper bound.

No step divides by $u$, $W$, $\varepsilon$ or a branch weight.
At $u=0$, $K=(1-24\tau)R+24\tau P^0$ and $h=5\tau$.
At $\tau=1/24$ the $R$ branch is absent; at $u=\tau$
the donor bound (11.5) is still strictly positive.
All head ties, $a_8=a_7$, and zero transfer are included.
The algebraic $\tau=0$ point is outside the original positive domain.

The balance explaining 217 is exact: the core deficit contributes
$22s$, $Q_8$ supplies correct-eight mass $159s$, and its
positive-word allowance supplies a further $36s$.
The equation $u=(22+159+36)s$ balances the correct-eight
deficit with the core cap. The donor and activation proofs make
this balance a single feasible law; they assert no full-catalog
optimality. $\square$

## 14. Direct original execution and exact actual-source error

**Theorem 14.1 (One seed, counted requests and every actual continuation).**
The finite law $K$ has original realizations in both classes satisfying
(10.2), with actual error attainment.

Proof. Partition one source-independent uniform seed in $[0,1)$
into half-open intervals of the complete-table weights in 11.2.
Omit zero intervals. Equivalently use the common-cell partition
(11.1) before splitting any row. Before replies this single seed
fixes the whole schedule and every counterfactual label.

On a selected pair $O(i,j;f,m,z)$, the stopped rule executes
its preselected increasing schedule until the first queried zero
or exhaustion and emits the corresponding actual mark $\theta_\ell$,
where $\ell$ is the selected output label.
The constant-zero branch emits $\theta_0$ with no requests.
For clarity, an output label need not be a queried address.
The counted $N$ realization requests both actual addresses on
that same source and seed, even if the first reply is zero.
It emits $f$ on $00$ or $01$, $m$ on $10$, and $z$ on
$11$. Every acquired reply, including an ignored second reply,
counts as an actual request. Both rules make at most two actual
requests, have zero advice and finite measurable handoff for every
source and seed, and use the unchanged consumer.
They have identical laws. This is a construction of these two rules,
without converting an arbitrary competing $N$ law to $O$.

Every actual first absence $n\le8$ gives a Boolean word covered
by Theorem 13.1; all higher replies are ignored.
For actual $n>8$, the finite eight-prefix is positive and no
emitted mark is $\theta_n$. Put $r=1-K_+(0)=h$.
Splitting the signed measure into the mark zero, mark $n$, and
the other emitted marks gives the exact full-carrier identity

$$
\operatorname{TV}\left(
 \sum_{j=0}^8K_+(j)\delta_{\theta_j},
 (1-a_n)\delta_{\theta_0}+a_n\delta_{\theta_n}\right)
 =\frac{|a_n-r|+a_n+r}{2}
 =\max\{a_n,h\}.
\tag{14.1}
$$

Actual $a_9$ is $5\tau+v$ and all $a_n$ for $n\ge10$
are at most $5\tau\le h$. Therefore the uniform error is at most
$\max\{h,5\tau+v\}$ for every allowed positive, nonincreasing,
vanishing continuation, including $a_{10}=5\tau$, all later
ties, nonsummable tails and arbitrarily slow decay.

The bound is attained on actual sources. A fixed explicit source
with first absence two is $(r,g)=(19,419)$, verified in 15.1.
Its correct deficit in (13.1) is $h$ for every $\tau,u$.
If $v\le22u/217$ this already attains the claimed maximum.
If $v>22u/217$, an actual source with first absence nine
attains $5\tau+v$ by (14.1).

Recall the credited finite-pattern argument in full to justify this
last actuality. Modulo a prime $p$, the invertible Fibonacci matrix
$M=\left(\begin{smallmatrix}1&1\\1&0\end{smallmatrix}\right)$
has
$M^k=\left(\begin{smallmatrix}F_{k+1}&F_k\\F_k&F_{k-1}\end{smallmatrix}\right)$
and is scalar exactly when $p\mid F_k$.
Its projective class has finite order $z(p)\ge3$, since
$F_1=F_2=1$, so $p\mid F_k$ iff $z(p)\mid k$.
For a finite set of specified primes of product $D$, choose a
prime index $r$ larger than all these orders, with
$F_r\ge10(D+2)$. None of these orders divides $r$, so $F_r$
is invertible modulo $D$. Prescribe $g=-F_r^{-1}\pmod p$
at desired ones and $g=0\pmod p$ at desired zeros.
CRT gives a residue modulo $D$. The actual interval
$[\lceil F_r/10\rceil,\lfloor F_r/5\rfloor]$ has length at least
$F_r/10-2\ge D$ and contains a representative.
Every finite word, including $1^8 0$ and every multiple-zero
word, is actual. Each actual positive integer $N(r,g)$ has finite
prime support, hence finite first absence.

Thus (14.1) attains the larger tail value when required.
At $v=0$ the actual ninth amplitude remains $5\tau>0$;
every actual later first absence has error exactly $h$.
A positive eight-prefix is a finite reply pattern, not an infinite
all-positive source. The acquisition obtains only its selected
schedule, without observing the full prefix or $r,g,N,n$.
This proves the exact original error (10.2). $\square$

**Corollary 14.2 (The exact refutation quantifiers).**
For every $0<\tau\le1/24$ and $0<u\le\tau$,
the universal original complementary plane (9.2) fails at the
allowed member $v=0$ for every allowed actual continuation.
For this same law and arbitrary allowed $v$, strict improvement
over the old complementary plane holds exactly for $v<22u/181$.

Proof. The exact difference at $v=0$ is

$$
\left(5\tau+\frac{22u}{181}\right)-h
 =\frac{792u}{181\cdot217}>0.
\tag{14.2}
$$

Moreover $181v=0<75u$, so this is a member of the strict
complementary region. For general $v$ and $u>0$, (10.2)
is less than $5\tau+22u/181$ iff
$\max\{22u/217,v\}<22u/181$, which is exactly the condition
stated. Such a $v$ automatically satisfies $181v<75u$.
At $u=0$ necessarily $v=0$ and there is no strict improvement.
Theorem 5.2 still evaluates its own old law correctly;
(9.2), proposed as a full-class necessary relation, is the
assertion refuted here. $\square$

## 15. A complete rational original counterexample

**Proposition 15.1 (Twenty-nine tables and an actual attainer).**
At $\tau=u=1/24$, $v=0$, the following is the full combined
law $K$. There are 28 pair tables and one constant-zero table;
every count is divided by 5208.

| $i$ | $j$ | $f$ | $m$ | $z$ | Count |
| --- | --- | --- | --- | --- | ---: |
| 1 | 2 | 1 | 2 | 0 | 819 |
| 1 | 2 | 1 | 2 | 3 | 398 |
| 1 | 2 | 1 | 2 | 4 | 251 |
| 1 | 2 | 1 | 2 | 5 | 188 |
| 1 | 3 | 1 | 3 | 0 | 267 |
| 1 | 3 | 0 | 3 | 0 | 391 |
| 1 | 4 | 0 | 4 | 0 | 89 |
| 1 | 4 | 1 | 4 | 0 | 110 |
| 1 | 5 | 1 | 5 | 0 | 27 |
| 2 | 3 | 0 | 3 | 0 | 600 |
| 2 | 3 | 2 | 3 | 0 | 58 |
| 2 | 4 | 0 | 4 | 0 | 199 |
| 2 | 5 | 0 | 5 | 0 | 27 |
| 3 | 4 | 0 | 4 | 0 | 237 |
| 3 | 4 | 0 | 4 | 5 | 177 |
| 3 | 5 | 0 | 5 | 0 | 221 |
| 3 | 6 | 0 | 6 | 0 | 214 |
| 3 | 7 | 0 | 7 | 0 | 15 |
| 3 | 8 | 0 | 8 | 0 | 15 |
| 4 | 5 | 0 | 5 | 0 | 206 |
| 4 | 6 | 0 | 6 | 0 | 199 |
| 5 | 6 | 0 | 6 | 0 | 216 |
| 5 | 7 | 0 | 7 | 0 | 17 |
| 5 | 8 | 0 | 8 | 0 | 17 |
| 6 | 7 | 0 | 7 | 0 | 70 |
| 6 | 7 | 0 | 7 | 8 | 93 |
| 6 | 8 | 0 | 8 | 0 | 53 |
| 7 | 8 | 0 | 8 | 0 | 17 |

The remaining table is constant zero of count 17.
Use first eight amplitudes $(13,13,13,10,9,8,6,6)/24$ and,
for every $n\ge9$, take

$$
a_n=\frac5{24}\,2^{-(n-9)}.
\tag{15.1}
$$

This is an entire actual amplitude sequence in (1.4).
The law has exact original error $369/1736$, strictly below
the plane value $309/1448$, and the actual source $(19,419)$
attains that error.

Proof. Here $s=1/5208$, $W=128/217$, $\varepsilon=36/5208$,
the $R$ weight is zero, and the $P^0$ weight is $89/217$.
In denominator 5208, before transfer the counts are 89 times
the integer list of $P^0$ plus the integer list of $Q_8$.
Their total is $89\cdot24+3072=2136+3072=5208$.
For example the $(1,2)$ counts are
$4\cdot89+463=819$, $2\cdot89+220=398$,
$89+162=251$, and $89+99=188$.
The distinct first-label-one and first-label-zero $(1,3)$
counts are 267 and 391. Combining other coincident rows gives
exactly the printed table. The changed $(6,7)$ counts are
$89+17-36=70$ and $57+36=93$.
Its remaining $P^0$ donor stock is $89-36=53$.
The transfer preserves the total 5208 and all counts are nonnegative.

The correct counts on the entire eight first-zero fibres are

$$
(2060,1714,1714,1063,846,629,195,195)/5208.
\tag{15.2}
$$

The exact positive and class-eight vectors are

$$
\begin{aligned}
K_+&=(4101e_0+398e_3+251e_4+365e_5+93e_8)/5208,\\
K_8&=(3999e_0+398e_3+251e_4+365e_5+195e_8)/5208.
\end{aligned}
\tag{15.3}
$$

The class-eight $A,C,P$ deficits are respectively
$-93/5208$, $1107/5208$, and $1014/5208$.
Theorems 13.1 and 14.1 cover every other word and every actual
source, not only the displayed class-eight vector.
The exact cap and comparison are

$$
h=\frac{1107}{5208}=\frac{369}{1736},\qquad
T=\frac{927}{4344}=\frac{309}{1448},\qquad
T-h=\frac{33}{39277}>0.
\tag{15.4}
$$

The sequence (15.1) has $a_9=5/24$, $a_{10}=5/48$,
strictly positive ordered tail and vanishing limit.
It keeps the actual ninth amplitude, and the law also works for
every other permitted $v=0$ continuation by 14.1.

Finally $19$ is prime, $F_{19}=4181$, and the legal $g$ window
is $419\le g\le836$. With $g=419$,

$$
N(19,419)=1+4181\cdot419=1751840.
\tag{15.5}
$$

This integer is even and has digit sum 26, so it is not divisible
by three. Its first absence is exactly two.
At that source $a_2=13/24=2821/5208$ and the correct count
is $1714/5208$, giving deficit $1107/5208=h$.
The all-word and actual-tail upper proof gives TV at most $h$,
so this source attains the exact original uniform error.
The witness is a law on the whole original source and entire
positive sequence. $\square$

## 16. The precise reduced interval and retained original frontier

**Proposition 16.1 (Reduced minima, original correspondence and the gap).**
For both complete reduced problems,

$$
5\tau+\frac{11u}{117}
 \le\nu_N(\tau,u)\le\nu_O(\tau,u)
 \le5\tau+\frac{22u}{217}.
\tag{16.1}
$$

For each class and every continuation in (1.4),

$$
\nu_C(\tau,u)\le m_C(\tau,u,v),\qquad
\nu_C(\tau,u)=m_C(\tau,u,0).
\tag{16.2}
$$

At $u=0$ both reduced minima and the allowed original minima
equal $5\tau$. For $u>0$ the interval in (16.1) has positive width

$$
\frac{187u}{117\cdot217}.
\tag{16.3}
$$

Proof. Each eight-bit catalog is finite and the full-row maximum
is continuous on its probability simplex, so its minimum exists
separately. The credited head-independent 43-charge inequality
of XVII 312.2 gives $43e\ge215\tau$, hence a lower bound
$5\tau$ in both catalogs.

For the stronger lower endpoint reuse precisely the same-law bridge
of 7.1. At any feasible eight-bit cap $e\in[0,1]$, extend the
same complete allocation by ignoring nine and set the auxiliary
finite amplitude $b_9=e$. If $q=p_+(0)\ge1-e$, the new
first-zero-nine probabilities are $(q,0,q)$ and its demands
are $(1-2e,0,1-e)$. Each holds separately, as does the
positive row. This costs no query and requires no order condition.
Apply the full $Y_{128}$ relation (2.4) to this one allocation
and subtract $11b_9=11e$. Its eight-coordinate left side is

$$
2a_2+11a_3+13a_4+13a_5+12a_6+11a_7+11a_8
 =2+585\tau+11u.
\tag{16.4}
$$

Thus $117e\ge585\tau+11u$.
This is the credited full-$N$ lower consequence, not a new score.
It includes arbitrary independent $N$ outputs.
Counted completion yields $\nu_N\le\nu_O$, and Theorem 13.1
gives their common upper bound. Their relevant caps are below one.

For (16.2), use the original compact correspondence of 8.1 in
each class separately. Restrict any nine-bit feasible law by fixing
input nine to zero and projecting label nine to zero, contracting
constant observations within its schedule. Low correct events
are unchanged, and their base and union events improve.
The positive eight-word is the former first-zero-nine word.
Its new base mass is the old $p(0)+p(9)\ge1-e$ by the
independent $P_9$ row, for every actual $a_9$.
Hence $\nu_C\le m_C$ for any allowed $v$.
These are finite proof representations, not free observations.

Conversely take an eight-bit minimizer in its own class.
At $v=0$, every actual amplitude beyond eight is at most
$5\tau\le\nu_C$. The common-seed execution of its complete
tables has the original cap $\nu_C$: every low first absence
is covered by its rows, and every later one by the exact identity
$\max\{1-p_+(0),a_n\}\le\nu_C$.
Thus $m_C(\tau,u,0)\le\nu_C$.
The original necessity correspondence retains all arbitrary addresses
and Borel outputs and preserves class feasibility, not an arbitrary
starting law. This is the supplied R1 correspondence at its precise
scope. It never replaces the actual $a_9$ of a specified sequence.

When $u=0$, necessarily $v=0$ and (16.1)–(16.2) give the
exact value $5\tau$. Subtracting the lower endpoint of (16.1)
from its upper gives (16.3), positive for $u>0$.
Neither minimax optimality of $K$ nor equality $\nu_N=\nu_O$
for $u>0$ follows. $\square$

**Corollary 16.2 (Original bounds and the unchanged attained wedge).**
All valid lower bounds and attained results in 5–8 remain valid.
On the whole original family,

$$
\begin{aligned}
\max\{E_{\rm sum},L_8\}
 &\le m_N\le m_O\\
 &\le5\tau+
 \min\left\{
 \max\left\{\frac{22u}{181},\frac{11(u+v)}{128}\right\},
 \max\left\{\frac{22u}{217},v\right\}
 \right\}.
\end{aligned}
\tag{16.5}
$$

On $181v\ge75u$ the exact attained value in both classes
is still $E_{\rm sum}$. The full-class complement remains
unevaluated in general.

Proof. Choose the better of the two complete common laws in 5.2
and 10.2 for the fixed parameters. This selects one whole law;
it does not combine separately optimized event margins.
The lower bounds are (5.4) and 7.2.

The old wedge's parameter condition is exactly the conserved-transfer
parameter domain of XVIII 324–327 under
$t=(u+v)/2$, $\delta=(u-v)/2$:
$\delta\le53t/128$ is exactly $75u\le181v$,
and $\delta\le\tau-t$ is $u\le\tau$.
This domain is broader than the narrower overlapping slice
$v\ge u/2$ identified in XVIII 330.
The wedge law (5.2) is that same credited law, since
$x+y=24t$ and $53x/3072=\delta$.
At $u>0$ on the wedge, $v\ge75u/181>22u/217$,
so $K$ has error $5\tau+v\ge E_{\rm sum}$.
There is no conflict with the old matching lower bound or new
optimality credit for that wedge.
Compact original attainment in 8.1 still holds separately;
it does not supply a value or equality in the complement.
The full-score face question in 9.1 retains its stated unresolved
intersection range. $\square$

## 17. The surviving slack identity and exact remaining obligations

**Proposition 17.1 (The R2 identity survives and its extra strengthening fails).**
Let a complete normalized eight-bit $N$ law be feasible at
$e=5\tau+d\in[0,1]$ for the first eight amplitudes of (1.4).
Extend that same law by ignoring nine at auxiliary $b_9=e$
as in 7.1. With $Y=Y_{128}$ and $\mathfrak d_r$ the demand
of a full nine-bit row, define

$$
S=\sum_D\lambda_D(368-Yz_D)
   +\sum_rY_r\,[p(\operatorname{event}r)-\mathfrak d_r].
\tag{17.1}
$$

Then the supplied R2 slack identity is exactly

$$
S=8(117d-11u)\ge0.
\tag{17.2}
$$

The additional proposed full-class strengthening $S\ge212d$
is false for every $u>0$, as witnessed by $K$ at $e=h$.

Proof. Full support gives $Yz_D\le368$ for every complete
$N$ table. Every full row of the extended law is feasible, and
$Y\ge0$, so each summand in (17.1) is nonnegative.
Normalization and $p=\sum_D\lambda_Dz_D$ cancel the incidence
terms, leaving $S=368-Y\mathfrak d$.
The quotient (2.3)–(2.4), with $b_9=e$, gives exactly
$S=8[117(e-5\tau)-11u]$.
This auxiliary finite amplitude asserts nothing about the actual
original $a_9$ and needs no order assumption.
The identity is the credited score pairing, not a new certificate.

For $K$, $d=22u/217$, and therefore

$$
S=\frac{1496u}{217},\qquad
212d=\frac{4664u}{217},\qquad
S-212d=-\frac{3168u}{217}<0\quad(u>0).
\tag{17.3}
$$

The nonnegative identity remains valid.
Its proposed strengthening would imply
$8(117d-11u)\ge212d$, equivalently $181d\ge22u$;
(17.3) shows why that additional full-class step cannot hold.
For $K$ at $u=0$, one has $d=0$ and both quantities vanish. $\square$

**Proposition 17.2 (The R3 restriction and R4 failed move retain their scopes).**
The fixed-base tail-relabeling obstruction called R3 does not
apply to $K$. The failed unaccompanied rescheduling called R4
is not a full-class obstruction to (10.3).

Proof. R3 fixes schedule masses and every originally zero- or
core-labeled cell, redistributing only originally eight- or
nine-labeled stock. Within that restricted family, the reused
class-two correct mass is
$1-16\tau-22W/3072$, and correct-eight mass is at most
$159W/3072$. At cap $5\tau+d$ its two correct rows require

$$
22W\le3072d,\qquad 3072(u-d)\le159W,
\tag{17.4}
$$

which imply $181d\ge22u$, also when the second demand is
negative. This remains a restricted-family statement.
For $u>0$, $K$ moves the positive amount $36s$ from an
originally base-labeled $P^0$ cell to label eight and obtains
$195s$ correct-eight mass. That operation violates R3's
fixed-base premise. Its legality is proved by 11.3 and 12.1–13.1,
rather than by broadening R3's scope.

R4 replaces the old 17-count $O(8,9;0,9,0)$ branch by
$O(7,8;0,8,0)$ without compensation.
On the actual finite word $101000100$, with first zero two,
this raises the old $Q$ outside count from 662 to 679:
the old branch emits zero and its replacement emits eight.
Here $w_6=0$. In $Q_8$ the old branch instead becomes
constant zero, and the additional $(6,7)$ transfer of $K$
is inactive. No such 17-count addition to $(7,8)$ is made.
Thus that failed move remains excluded, while the all-word
proof above supplies a different legal law. $\square$

**Definition 17.3 (Current limits and premise boundary).**
The established increment is the base-label-to-eight transfer,
the full activation-set slack proof, the consumed positive-word
allowance, the exact 217 upper law and the full original
counterexample. The proposal supplies that construction; the
independent ordinary check verifies it; this body supplies its
complete ordinary derivation. The mature $P^0$, $P^\star$,
$Q$, endpoint polynomials, full-score support, old attained
wedge, finite-pattern arithmetic, compactness and closed-cap
transport are reused with their stated credits.

The exact full reduced minima for $u>0$, a matching new lower
certificate, optimality of $K$, and equality or separation of
$N$ and $O$ remain unresolved. The positive-width interval
(16.1) is the present reduced frontier, while (16.5) and the
old attained wedge give the stated original frontier.
Relation (9.2) and the extra R2 strengthening are refuted;
R2's identity, R3's restricted obstruction and R4's failed-move
obstruction retain precisely the scopes proved above.

The unrestricted simultaneous signed-budget problem of 9 and
XVIII 323.3 still asks, for every full unit-$O$ score, for one
unrestricted full $V\ge0$ and one common $\theta\in[0,1]$
paying both $\Delta_N(V)+\theta\le1$ and
$\sigma_H(Qy-QV)\le\theta$, or for the complete same-profile
original separator. Its residual remains signed and nonzero
zero-cost $V$ at $\theta=1$ remains allowed. The present law
belongs to both classes and supplies neither unrestricted alternative.

The mathematical statements here are repo-derived relative to the
complete supplied DEV, owning source, proposal and check.
Blackwell's whole attainable loss-vector framework and
Kaniewski–Lee–de Wolf's scalar-expectation framework retain only
the roles specified in 9 and XVIII 323.2; scalar coefficient
normalization does not supply this law's vector or schedule budget.
No unseen nested supplier body or unprovided external reference
is used as additional evidence. The earlier correspondence
theorems are reused only at the scopes expressly supplied in 1.3.
These are ordinary mathematical proofs, without a claim of
formal-kernel verification, worldwide priority, physical efficiency,
general neural-network or empirical-learning consequences, or
completion of the wider acquisition problem.

All outputs are finite laws on the actual marks in $B_1$.
Every unchanged original nonatomic target assigns their finite
support zero mass, so their TV distance from it is one.
The accuracy and counterexample concern the selected marked targets
on the unchanged source, carrier, consumer and hard resource classes.

## 追加锚（本行以下为增补区）
