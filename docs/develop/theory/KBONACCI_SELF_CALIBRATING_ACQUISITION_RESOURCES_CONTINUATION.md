# Self-calibrating acquisition resources: two-request output laws

## 108. Common probability-vector kernels and stopped schedules

**Definition 108.1 (Finite preselected and stopped kernels).** Let $L$ be
an integer with $L\ge0$, let $J_L=\{0,\ldots,L\}$, and let
$B_L=\{0,1\}^L$. A kernel is a family $p=(p_b)_{b\in B_L}$ of
probability vectors on $J_L$. Write $e_r$ for the probability vector
concentrated at label $r$. Every input word is included, without any
restriction on the number of its zero coordinates.

A finite preselected two-request rule chooses, from one source-independent
seed, a schedule of length at most two in $\{1,\ldots,L\}$ and a
terminal output table. It acquires the entire scheduled reply sequence
and outputs a label using only this sequence and its seed. Requests to
the same coordinate count separately; deleting a repetition and using
its already acquired static answer preserves its output law. Let
$\mathscr N_L$ be the set of kernels obtainable by these rules.

A finite increasing first-zero-stop two-request rule instead chooses
one of the schedules $\varnothing$, $(i)$ or $(i,j)$ with $i<j$.
It queries until its first queried zero or exhaustion and then outputs
using only the stopped transcript and the same seed. For $(i,j)$ its
three terminal cells are $b_i=0$, $(b_i,b_j)=(1,0)$ and
$(b_i,b_j)=(1,1)$. The first cell contains both $00$ and $01$.
Outputs are arbitrary labels, not necessarily queried coordinates.
Let $\mathscr O_L$ be its set of kernels. Completing a stopped schedule
and ignoring replies after its first zero gives
$\mathscr O_L\subseteq\mathscr N_L$.

The seed fixes the entire deterministic terminal table before replies.
Equivalently, either class is a single common probability distribution
over its finite set of deterministic schedules and terminal tables.
Terminal probabilities may be described separately on different cells,
but their unnormalized output-mass vectors all have the schedule's
common weight. No error cap is imposed separately on a schedule or
on a cell.

**Definition 108.2 (Coefficients and coordinate mass).** Suppose the
unique multilinear expansion of a probability-vector kernel has degree
at most two, and write

$$
p_b=c+\sum_{i=1}^L\ell_i b_i+
             \sum_{1\le i<j\le L}Q_{ij}b_i b_j.
\tag{108.1}
$$

These are vectors in $\mathbb R^{J_L}$. In particular $c=p_{0^L}$ is
a probability vector. Summing (108.1) over labels and using uniqueness
of the multilinear expansion of the constant function one gives

$$
\sum_{r=0}^Lc(r)=1,\qquad
\sum_{r=0}^L\ell_i(r)=0,\qquad
\sum_{r=0}^LQ_{ij}(r)=0.
\tag{108.2}
$$

For a nonnegative vector $u$ define its coordinate mass by
$\mathfrak m(u)=\sum_{r=0}^Lu(r)=\|u\|_1$. This notation sums over
output labels, not over query coordinates. Positive parts and vector
inequalities are coordinatewise. Define

$$
\begin{aligned}
v_{ij}&=(-Q_{ij})_+, &
V_i&=\sum_{j>i}v_{ij}, &
h_i&=(V_i-\ell_i)_+,\\
H&=\sum_{i=1}^Lh_i, &
m_i&=\max\{\mathfrak m(V_i),\mathfrak m(h_i)\}, &
\beta&=\sum_{i=1}^Lm_i.
\end{aligned}
\tag{108.3}
$$

Empty sums are zero. The condition $c\ge H$ is a vector inequality;
$\beta\le1$ is one scalar probability-budget inequality. Let
$\mathscr C_L$ be the set of probability-vector kernels of degree at
most two satisfying both conditions. Normalization makes the displayed scalar
condition redundant once the vector condition holds: since
$\sum_r(V_i(r)-\ell_i(r))=\mathfrak m(V_i)$, taking positive parts
gives $\mathfrak m(h_i)\ge\mathfrak m(V_i)$. Consequently

$$
m_i=\mathfrak m(h_i),\qquad \beta=\mathfrak m(H),\qquad
c\ge H\ \Longrightarrow\ \beta\le1.
\tag{108.4}
$$

The notation $\beta$ also records the total mass assigned to nonempty
schedules in the construction below.

The coefficients can be read from zero, one-coordinate and
two-coordinate inputs:

$$
\begin{aligned}
c&=p_{0^L},\\
\ell_i&=p_{e_i^{\mathrm{in}}}-c,\\
Q_{ij}&=p_{e_i^{\mathrm{in}}+e_j^{\mathrm{in}}}
                  -p_{e_i^{\mathrm{in}}}-p_{e_j^{\mathrm{in}}}+c,
\end{aligned}
\tag{108.5}
$$

where $e_i^{\mathrm{in}}$ denotes a unit input word, distinct from an
output label vector. Degree at most two also requires (108.1) at every
remaining word. Every kernel in $\mathscr N_L$ has this degree bound:
a deterministic terminal table on at most two distinct acquired bits
has such an expansion, and common mixtures preserve it. The degree
bound alone asserts neither stopped realizability nor cap feasibility.

## 109. An exact coefficient criterion with one common probability budget

**Theorem 109.1 (Stopped output-law realizability).** For every integer
$L\ge0$ and every probability-vector kernel $p$ on all of $B_L$ whose
multilinear expansion has degree at most two,

$$
p\in\mathscr O_L
\quad\Longleftrightarrow\quad
c\ge H\ \hbox{coordinatewise and}\ \beta\le1.
\tag{109.1}
$$

The sufficient direction gives one source-independent common seed and
an increasing first-zero-stop rule with at most two actual requests,
whose law is exactly $p_b$ at every word. All inequalities are
non-strict, including zero schedule weights and every degenerate case.
Consequently $\mathscr O_L=\mathscr C_L$.

**Proof.** Describe a stopped mixture by nonnegative output-mass
vectors. Let $r$ be the empty-schedule vector. For singleton $(i)$ let
$u_i^0,u_i^1$ be its two terminal vectors, each of coordinate mass
$s_i$. For pair $(i,j)$ let $u_{ij}^0,u_{ij}^{10},u_{ij}^{11}$ be its
three terminal vectors, each of mass $t_{ij}$. Integrating the
seed-fixed output tables on each schedule event supplies these vectors
for any common-seed stopped rule. Conversely such vectors describe
terminal probabilities on each positive-mass schedule. Their total
schedule mass must satisfy

$$
\mathfrak m(r)+\sum_i s_i+\sum_{i<j}t_{ij}=1.
\tag{109.2}
$$

The law at any word is

$$
\begin{aligned}
p_b={}&r+\sum_i\bigl((1-b_i)u_i^0+b_i u_i^1\bigr)\\
 &+\sum_{i<j}\bigl((1-b_i)u_{ij}^0
       +b_i(1-b_j)u_{ij}^{10}+b_i b_j u_{ij}^{11}\bigr).
\end{aligned}
\tag{109.3}
$$

In particular (109.3) has degree at most two. Comparing its unique
coefficients with (108.1), put

$$
A_i=u_i^0+\sum_{j>i}u_{ij}^0,\qquad
B_i=u_i^1+\sum_{j>i}u_{ij}^{10}.
\tag{109.4}
$$

Then

$$
c=r+\sum_iA_i,\qquad \ell_i=B_i-A_i,\qquad
Q_{ij}=u_{ij}^{11}-u_{ij}^{10}.
\tag{109.5}
$$

Nonnegativity forces $u_{ij}^{10}\ge(-Q_{ij})_+=v_{ij}$.
Thus $B_i\ge V_i$, and $A_i\ge0$ together with
$A_i+\ell_i=B_i\ge V_i$ gives $A_i\ge h_i$. Summing proves
$c\ge H$. Equal terminal masses in (109.4) give

$$
\mathfrak m(A_i)=\mathfrak m(B_i)
                =s_i+\sum_{j>i}t_{ij}=:w_i.
\tag{109.6}
$$

Since $A_i\ge h_i$ and $B_i\ge V_i$, one has $w_i\ge m_i$.
Equation (109.2) therefore gives
$\beta\le\sum_iw_i=1-\mathfrak m(r)\le1$. This proves necessity,
including the common scalar budget rather than separate budgets for
individual output coordinates.

For sufficiency suppose $c\ge H$ and $\beta\le1$. By (108.4)
set

$$
d_i=h_i,\qquad r=c-H.
\tag{109.7}
$$

Then

$$
d_i\ge0,\qquad d_i\ge V_i-\ell_i,\qquad
\mathfrak m(d_i)=m_i,\qquad \sum_i d_i=H\le c.
\tag{109.8}
$$

In particular

$$
r\ge0,\qquad \mathfrak m(r)=1-\beta.
\tag{109.9}
$$

For every $i<j$ take

$$
u_{ij}^{10}=v_{ij},\qquad
u_{ij}^{11}=v_{ij}+Q_{ij}=(Q_{ij})_+,\qquad
t_{ij}=\mathfrak m(v_{ij}).
\tag{109.10}
$$

The two terminal vectors in (109.10) have the same mass because
$Q_{ij}$ has signed coordinate sum zero. If $m_i>0$, set

$$
\begin{aligned}
u_{ij}^0&=\frac{t_{ij}}{m_i}d_i\quad(j>i),\\
u_i^0&=\left(1-\frac{\mathfrak m(V_i)}{m_i}\right)d_i,\\
u_i^1&=d_i+\ell_i-V_i,\qquad
s_i=m_i-\mathfrak m(V_i).
\end{aligned}
\tag{109.11}
$$

Each vector is nonnegative: for $u_i^1$, use
$d_i\ge(V_i-\ell_i)_+\ge V_i-\ell_i$. Its mass is $s_i$ by
(108.2), as is that of $u_i^0$. The first-zero pair vector has mass
$t_{ij}$, and

$$
u_i^0+\sum_{j>i}u_{ij}^0=d_i,\qquad
u_i^1+\sum_{j>i}u_{ij}^{10}=d_i+\ell_i.
\tag{109.12}
$$

If $m_i=0$, then $V_i=h_i=d_i=0$. The relation
$h_i=(-\ell_i)_+=0$ makes $\ell_i$ nonnegative; its zero signed
coordinate sum makes it zero. Every outgoing $v_{ij}$ is zero, and
then $Q_{ij}\ge0$ with signed coordinate sum zero, so $Q_{ij}=0$.
Define all singleton and outgoing-pair vectors for this $i$ to be zero.
Thus no division by zero occurs, and (109.10)--(109.12) remain valid.

The weights $\mathfrak m(r)$, $s_i$ and $t_{ij}$ are nonnegative,
and their sum is

$$
1-\beta+\sum_i\bigl(m_i-\mathfrak m(V_i)\bigr)
                   +\sum_{i<j}\mathfrak m(v_{ij})=1.
\tag{109.13}
$$

Use these vectors in (109.3). Its constant coefficient is
$r+\sum_i d_i=c$, its coefficient at $b_i$ is $\ell_i$ by
(109.12), and its coefficient at $b_i b_j$ is $Q_{ij}$ by
(109.10). Hence it equals $p_b$ for every word, including every word
with several zeros; coefficient equality is equality of the entire
multilinear functions.

To execute this mixture, partition one uniform seed $U\in[0,1)$ into
half-open intervals of these schedule masses, omitting zero-mass
intervals. Within the chosen interval, rescale $U$ to a uniform local
coordinate. For each possible stopped cell, partition that same local
coordinate into label intervals of its normalized terminal vector.
The cell tables can use different partitions of the same local
coordinate: all tables are fixed before replies, and no extra random
variable is generated at a cell. The schedule is empty, a singleton,
or an increasing pair. Ask its actual questions until first zero or
exhaustion, and hand off its selected label. Thus every execution is
finite, makes at most two requests, and has the law (109.3). Every
record and label event is a finite union of measurable seed intervals.
When $L=0$, this construction is simply the empty-schedule law $c$;
all sums, $H$ and $\beta$ are zero. Equality in either inequality of
(109.1), vanishing vectors, and $\beta=1$ require no limiting
sampler. $\square$

The scalar nonnegative-literal precedent is Kaniewski, Lee and de Wolf,
[*Query complexity in expectation*, arXiv:1411.7280v1, Sections
2.3 and 3.1--3.2, Definition 8 and Theorem
9](https://arxiv.org/html/1411.7280v1). Their function is
$f:\{0,1\}^L\to\mathbb R_+$; a nonnegative scalar output has
expectation $f(b)$, and query cost is the largest root-to-leaf depth
among deterministic trees given positive mixture weight. That is a
worst-path query cost, not a mean number of requests. Their scalar
characterization does not impose equal schedule masses across output
labels or the three stopped cells in (109.3). The probability-vector
criterion (109.1), including its one common budget and increasing
first-zero-stop restriction, follows from the allocation proof above.

## 110. Exact closed-cap transport on the original countable source

**Definition 110.1 (Original source, selected laws and the finite cap
slice).** Retain the actual labeled source of [Acquisition Resources,
Definition 71.1](KBONACCI_SELF_CALIBRATING_ACQUISITION_RESOURCES.md#71-actual-sources-and-the-simultaneous-optimum-of-the-maximum-address):

$$
\begin{aligned}
X&=\{(r,g):r\text{ prime},\ g\in\mathbb Z,
       \ \lceil F_r/10\rceil\le g\le\lfloor F_r/5\rfloor\},\\
N(r,g)&=1+F_rg,\qquad
q_i(x)=\mathbf1_{p_i\mid N(x)},\qquad
n(x)=\min\{i\ge1:q_i(x)=0\}.
\end{aligned}
\tag{110.1}
$$

Here $F_0=0,F_1=1,F_{r+2}=F_{r+1}+F_r$ and $p_1<p_2<\cdots$ are
the primes. The source is countable, $N(x)$ is static and has finite
prime support, and $n(x)$ is always finite. Every finite answer pattern
has an actual witness, by [Boundaries, Theorem
35.2](KBONACCI_SELF_CALIBRATING_BOUNDARIES.md#35-exact-finite-divisibility-fibres-in-canonical-fibonacci-windows).

The full original measurable tape carrier, its marks $\theta_j$ and
its unchanged consumer and nonatomic targets $\mu_x$ are those of
[Acquisition Resources, Definition
73.1](KBONACCI_SELF_CALIBRATING_ACQUISITION_RESOURCES.md#73-monotone-marked-first-absence-laws-and-their-finite-certificates).
In particular the marks are distinct measurable points
$\theta_j=(B_1,1/(j+2))$, $j\ge0$, in the original carrier
$\bigsqcup_{j\ge1}B_j\sqcup\bigsqcup_{j\ge1}P_j$, whose blocks
are copies of $(0,1)$. For every sequence

$$
1\ge a_1\ge a_2\ge\cdots>0,\qquad a_i\longrightarrow0,
\tag{110.2}
$$

the separately selected marked target is

$$
\lambda_x^a=(1-a_{n(x)})\delta_{\theta_0}
                       +a_{n(x)}\delta_{\theta_{n(x)}}.
\tag{110.3}
$$

Original acquisitions and the classes $\mathcal N_2,\mathcal O_2$
mean exactly [Acquisition Resources, Definition
90.1](KBONACCI_SELF_CALIBRATING_ACQUISITION_RESOURCES.md#90-adaptive-preselected-and-increasing-first-zero-stop-acquisitions).
They have zero advice, one source-independent common seed, actual
sourcewise almost-sure finite handoff and the unchanged consumer run
on the same source and handed original tape. The hard budget is at
most two actual requests, counting repetitions. Competitors can choose
arbitrary addresses and output anywhere on the full measurable carrier.
No source label, value $N(x)$, first absence, source law or extra
observation is supplied. Write

$$
e_a(A)=\sup_{x\in X}\operatorname{TV}
       (\widehat\lambda_{A,x},\lambda_x^a),\qquad
\operatorname{TV}(\nu,\lambda)=\sup_{E\in\mathcal F}|\nu(E)-\lambda(E)|.
\tag{110.4}
$$

For $0<\varepsilon\le1$ set
$L=\max(\{i:a_i>\varepsilon\}\cup\{0\})$. For a low word $b$ with a zero, put
$n_L(b)=\min\{i\le L:b_i=0\}$ and $n=n_L(b)$, and let
$\eta_b=(1-a_n)e_0+a_ne_n$, and let $\eta_{1^L}=e_0$.
The finite cap slice is the set

$$
\mathcal F_N(a,\varepsilon)
 =\{p\in\mathscr N_L:
       \operatorname{TV}(p_b,\eta_b)\le\varepsilon
                         \text{ for every }b\in B_L\}.
\tag{110.5}
$$

Equivalently its rows, supplied by [Acquisition Resources, (84.2)](KBONACCI_SELF_CALIBRATING_ACQUISITION_RESOURCES.md#84-explicit-tv-rows-and-a-complete-finite-obstruction-recurrence), are

$$
\begin{gathered}
p_b(0)\ge1-a_n-\varepsilon,\quad
p_b(n)\ge a_n-\varepsilon,\quad
p_b(0)+p_b(n)\ge1-\varepsilon
\quad(b\ne1^L,\ n=n_L(b)),\\
p_{1^L}(0)\ge1-\varepsilon.
\end{gathered}
\tag{110.6}
$$

In particular the pair row is retained independently of the singleton
rows. The finite all-positive word is not an additional infinite
all-positive source.

**Theorem 110.2 (Class-preserving feasibility transport).** For every
sequence (110.2) and every $0<\varepsilon\le1$,

$$
\begin{aligned}
\exists N\in\mathcal N_2:\ e_a(N)\le\varepsilon
 &\quad\Longleftrightarrow\quad
             \mathcal F_N(a,\varepsilon)\ne\varnothing,\\
\exists O\in\mathcal O_2:\ e_a(O)\le\varepsilon
 &\quad\Longleftrightarrow\quad
             \mathcal F_N(a,\varepsilon)\cap\mathscr C_L\ne\varnothing.
\end{aligned}
\tag{110.7}
$$

In particular any globally cap-feasible finite $\mathcal N_2$ kernel
satisfying (109.1) supplies an original $\mathcal O_2$ rule at that
same closed cap. This rule reproduces that finite kernel's laws at
every actual low word, and on every actual tail source its error is

$$
\max\{1-p_{1^L}(0),a_{n(x)}\}\le\varepsilon.
\tag{110.8}
$$

The original-to-finite direction transports feasibility, without
asserting preservation of an arbitrary original competitor's laws.

**Proof.** Use the measurable original-tape projection $\pi_L$ of
[Acquisition Resources, (83.7)--(83.9)](KBONACCI_SELF_CALIBRATING_ACQUISITION_RESOURCES.md#83-a-complete-finite-query-tree-criterion-for-positive-error-hard-counts):
it fixes $\theta_1,\ldots,\theta_L$ and sends every other tape to
$\theta_0$. Event pullbacks contract TV. It fixes (110.3) when
$n(x)\le L$ and projects it to $\delta_{\theta_0}$ otherwise.
For a law supported on these $L+1$ marks and $n>L$, the same supplier
gives the exact identity

$$
\operatorname{TV}\left(\sum_{j=0}^Lp(j)\delta_{\theta_j},
                  (1-a_n)\delta_{\theta_0}+a_n\delta_{\theta_n}\right)
          =\max\{1-p(0),a_n\}.
\tag{110.9}
$$

Here projection is a device for proving finite feasibility; the
constructed acquisitions will output actual original marks.

For necessity fix an original competitor $A$ in either restricted
class. Countability of $X$ gives one common probability-one seed
event $G$ on which every actual execution hands off finitely with
$K\le2$. For $\mathcal N_2$ its preselected schedule has length at
most two, and for $\mathcal O_2$ the same bound follows from its
contract and the schedule normalization in Proposition 90.2. On a
null complement it may be replaced by an empty schedule. Its maximum
preselected address $M_S$ is measurable and finite almost surely;
therefore

$$
J_m=\{M_S>m\},\qquad \gamma_m=\mathsf P_A(J_m)\longrightarrow0.
\tag{110.10}
$$

This is a common seed event controlling the entire preselected
schedule. It is not a separate sourcewise address bound.

For each $m\ge L+1$ and each $b\in B_L$, fix an actual source
$x_{b,m}$ with low word $b$ and zero replies at every index
$L<i\le m$. Boundaries, Theorem 35.2 supplies this finite family
before seeds. Its projected selected targets are precisely $\eta_b$:
a low word with a zero has its prescribed first absence, and the
all-positive low word has actual first absence $L+1$. Choose a
deterministic transition cutoff $t_m$ for this finite family such that

$$
\max_{b\in B_L}\mathsf P_A
       \{\text{handoff at }x_{b,m}\text{ occurs after }t_m\}\le1/m.
\tag{110.11}
$$

Sourcewise almost-sure finite handoff supplies this cutoff. It is
not a uniform transition bound over $X$.

Apply the finite simulation and whole-execution transport of the
proof of Theorem 83.3: supply low replies $b$, supply zero at
$L<i\le m$, and output label zero before any address above $m$,
third request or transition beyond $t_m$. At an original handoff
project its tape by $\pi_L$. Repetitions are counted during this
simulation. For each seed it gives a deterministic output function
$f_{s,m}:B_L\to J_L$; its label events are measurable by the
finite-record witness argument in that proof. Finite actual witnesses
for consistent reply words are fixed before seeds, and the
finite-execution supplier is [Source-Correlated Laws, Lemma
45.3](KBONACCI_SELF_CALIBRATING_SOURCE_CORRELATED_LAWS.md#45-lawful-acquisition-through-one-inherited-seed).

The restricted class survives this construction. In the preselected
case, all variable replies belong to the at most two distinct low
indices of the seed's schedule. Acquire these low replies first and
then evaluate the truncated table using them and the fixed high
replies. This is a finite preselected table, even when its output is
a cutoff label or an original early output. Repeated low requests
need no second observation in this representation. In the stopped
case, all high indices follow all selected low indices. A selected
low zero stops before any high question; if the low schedule is
exhausted positively, its high continuation has fixed replies.
Consequently two low words in the same stopped low cell have the
same truncated output. A transition cutoff also gives the same
output on such a cell, because processing is deterministic on the
same acquired transcript and seed. The resulting function is thus
represented by an increasing stopped low schedule of length at most
two. No high-coordinate simulation is used as an uncounted source
observation in the eventual acquisition.

In either class the deterministic low catalog is finite. Choose once
one representative schedule and table for each representable output
function. The measurable map $s\mapsto(f_{s,m}(b))_{b\in B_L}$
then supplies a common probability vector $w^{(m)}$ on that class's
finite catalog. On the whole event

$$
G\setminus J_m\ \cap\
\{\text{handoff at }x_{b,m}\text{ occurs by }t_m\},
\tag{110.12}
$$

the simulation and original finite execution agree after projection.
The complement has probability at most $\gamma_m+1/m$.
The supplied event coupling and projection contraction therefore give
for the finite laws $p_b^{(m)}$

$$
\operatorname{TV}(p_b^{(m)},\eta_b)
                \le\varepsilon+\gamma_m+1/m
                   \qquad\text{for every }b\in B_L.
\tag{110.13}
$$

The finite catalog simplex is compact. A subsequence of its common
weight vectors converges to one weight vector in the same class.
All finitely many law coordinates and TV constraints are continuous
in these weights. Its limit $p$ therefore satisfies the exact closed
cap at every word, with $p\in\mathscr N_L$ in the preselected case
and $p\in\mathscr O_L$ in the stopped case. This proves the two
necessary finite feasibility statements, with full-carrier outputs,
arbitrary addresses and repetitions retained in the original
competitor.

Conversely, execute any finite rule by actually querying its scheduled
low primes and handing its leaf mark to the unchanged consumer.
The finite common seed and table give finite handoff for every seed
and actual source, using at most two actual requests. At a source
with $n(x)\le L$, its low word has exactly the selected target in
(110.5), regardless of all later zero patterns. At every actual
$n(x)>L$, the acquired low word is $1^L$, and no tail mark is
emitted. Since $a_{n(x)}\le\varepsilon$, (110.9) proves (110.8),
including equality of a tail amplitude with the cap. This gives the
first sufficient direction. For the second use
$\mathscr O_L=\mathscr C_L\subseteq\mathscr N_L$ from Theorem
109.1. Its explicit seed construction supplies the stopped rule.
All required caps concern the mixed law, not individual schedules.
When $\varepsilon=1$, $L=0$ and immediate base output is such a
rule. $\square$

**Definition 110.3 (The remaining hard-two intersection question).**
For the original source and every sequence (110.2), the general
hard-two exact-cap comparison asks whether

$$
\mathcal F_N(a,\varepsilon)\ne\varnothing
\quad\Longrightarrow\quad
\mathcal F_N(a,\varepsilon)\cap\mathscr C_L\ne\varnothing
\qquad(0<\varepsilon\le1)
\tag{110.14}
$$

always holds. This implication remains unresolved for general active
length in this theory. Its quantifier allows replacement of the
entire feasible mixed kernel. Failure of (109.1) for one feasible
kernel only excludes its exact-law realization, and does not exclude
a different kernel in the same cap slice.

The budget-zero/one and near-full-depth cases are supplied by
[Acquisition Resources, Proposition
93.1](KBONACCI_SELF_CALIBRATING_ACQUISITION_RESOURCES.md#93-minimal-active-dimension-and-request-depth-for-a-feasibility-gap);
the active-four hard-two comparison is [Theorem
96.2](KBONACCI_SELF_CALIBRATING_ACQUISITION_RESOURCES.md#96-the-analytic-hard-two-boundary-for-four-active-amplitudes).
The plateau rules used below are Theorem 87.1. These results retain
their own scopes and are not a general implication (110.14).

## 111. A cap-feasible preselected family on unbounded active lengths

**Definition 111.1 (Plateau mixture and a two-bit terminal table).**
Let $L\ge5$ be an integer, let $0<\gamma<1/3$, and retain any
positive nonincreasing vanishing sequence with

$$
a_1=\cdots=a_L=1,\qquad
a_{L+1}\le\varepsilon_{L,\gamma}
       :=\frac{L-2+3\gamma}{L+1}.
\tag{111.1}
$$

Write $e_{L,2}=(L-2)/(L+1)$. Let $P_{L,2}$ be the original
increasing stopped subset rule supplied by [Acquisition Resources,
Theorem 87.1](KBONACCI_SELF_CALIBRATING_ACQUISITION_RESOURCES.md#87-unit-leading-plateaus-and-unbounded-address-to-count-ratios):
choose a uniform three-subset $C$ of $\{1,\ldots,L,*\}$, where
$*$ is ordered last and means output $\theta_0$; query its first two
labels increasingly until a zero, outputting that zero's mark, or
on positive exhaustion output the maximum label of $C$ without
querying it. The first two labels are always numerical. Denote its
finite output kernel by $p^P$.

Let $R$ be the preselected rule that queries both coordinates $4,5$,
including after a zero at $4$, and uses the terminal table

$$
\begin{array}{c|cccc}
(b_4,b_5)&00&01&10&11\\\hline
R_b&\theta_1&\theta_2&\theta_2&\theta_1.
\end{array}
\tag{111.2}
$$

Let $p^R_b$ be the corresponding point probability vector, and define

$$
p^{N}_{b}=(1-\gamma)p^P_b+\gamma p^R_b.
\tag{111.3}
$$

In executing the $P$ branch as a preselected rule, acquire both of
its scheduled replies and then reconstruct its original stopped
output, ignoring the unused reply. Thus (111.3) is a common
$\mathcal N_2$ mixture on actual original marks.

**Theorem 111.2 (Exact selected-target error on all words and tails).**
For every parameter and every original tail in (111.1), there is one
original $N\in\mathcal N_2$ with laws (111.3), finite handoff at
every actual source and seed, exactly two actual requests per seed,
and maximum requested index at most $L$. It satisfies

$$
e_a(N)=\varepsilon_{L,\gamma}.
\tag{111.4}
$$

More precisely, at a low word with first zero $n\le L$,

$$
\operatorname{TV}(\nu^N_b,\lambda_n)
       =\varepsilon_{L,\gamma}-\gamma p^R_b(n),\qquad
\nu^N_b=\sum_{j=0}^Lp^N_b(j)\delta_{\theta_j},
\tag{111.5}
$$

and at every actual source with $n(x)>L$ its error is exactly
$\varepsilon_{L,\gamma}$. An original $\mathcal O_2$ rule is also
feasible at this same cap: the supplied $P_{L,2}$ has
$e_a(P_{L,2})\le\varepsilon_{L,\gamma}$.

**Proof.** Partition a uniform seed into one interval of length
$\gamma$ for $R$ and $\binom{L+1}{3}$ intervals of length
$(1-\gamma)/\binom{L+1}{3}$ for the individual $P$ subsets.
Each interval fixes its entire schedule and output table before
any observation. The $R$ branch acquires $4,5$ and uses (111.2).
On a subset branch acquire its first two numerical labels in order;
after both replies, output the first scheduled zero's mark if any,
and otherwise the final unqueried label. This is precisely the
law-preserving completion of Proposition 90.2. It may make a second
request after its output choice is already determined, and that
request is counted. Every branch makes two actual requests and then
hands an original tape to the original consumer. The indices are
at most $L$, the same source is used throughout, and the finite
seed partition makes all records and outputs measurable.

The supplied all-word calculation of Theorem 87.1 gives
$p^P_b(n)=3/(L+1)$ whenever $n\le L$ is the first zero of $b$.
This remains true for every multiple-zero suffix. Since the selected
target is $\lambda_n=\delta_{\theta_n}$ on this plateau,

$$
p^N_b(n)=(1-\gamma)\frac3{L+1}+\gamma p^R_b(n),\qquad
1-p^N_b(n)=\varepsilon_{L,\gamma}-\gamma p^R_b(n).
\tag{111.6}
$$

Distance to a point target is one minus its output mass, proving
(111.5) at all $2^L-1$ words with a zero. Here $p^R_b(n)$ is either
zero or one, determined by (111.2). In particular it is zero whenever
$n\ge3$, so these occupied first-zero classes attain the cap.

At $1^L$ the supplied subset rule has base mass $3/(L+1)$, while
$R$ emits $\theta_1$. Hence

$$
p^N_{1^L}(0)=(1-\gamma)\frac3{L+1},\qquad
1-p^N_{1^L}(0)=\varepsilon_{L,\gamma}.
\tag{111.7}
$$

Every actual source with $n(x)>L$ produces this same low-word law,
with no mass at its tail mark. The exact tail identity (110.9) gives
error $\max\{\varepsilon_{L,\gamma},a_{n(x)}\}
=\varepsilon_{L,\gamma}$. There are actual sources in every such
first-absence class by Boundaries, Theorem 35.2. Thus the uniform
error equals the closed cap, not merely an upper bound or a limiting
infimum. Equality $a_{L+1}=\varepsilon_{L,\gamma}$ is included.

For the ordered comparison rule, Theorem 87.1 gives error $e_{L,2}$
on all low first-zero classes, and
$\max\{e_{L,2},a_{n(x)}\}$ on every actual tail source. Since
$e_{L,2}<\varepsilon_{L,\gamma}$ and
$a_{n(x)}\le a_{L+1}\le\varepsilon_{L,\gamma}$, this is an
original ordered rule at the same cap. The active length at this cap
is exactly $L$, since $a_L=1>\varepsilon_{L,\gamma}>0$ and
the retained tail is at most the cap. $\square$

## 112. A three-word obstruction to preserving the mixed output law

**Proposition 112.1 (Stopped three-word event inequality).** Fix
$L\ge5$, and for $u,v\in\{0,1\}$ let $b^{uv}\in B_L$ have
$b_4=u,b_5=v$ and every other coordinate equal to one. For every
finite stopped kernel $q\in\mathscr O_L$ and every label event
$E\subseteq J_L$,

$$
q_{b^{01}}(E)\le q_{b^{00}}(E)+q_{b^{11}}(E).
\tag{112.1}
$$

**Proof.** Fix the common seed and its increasing schedule. If it
includes coordinate $4$, the executions at $b^{00}$ and $b^{01}$
agree until querying $4$, and both stop there; coordinate $5$ cannot
precede it. They therefore have the same acquired transcript and
output. If the schedule does not include $4$, then $b^{01}$ and
$b^{11}$ agree on every scheduled coordinate, so their executions
and outputs agree. Thus the indicator of output in $E$ at the middle
word is bounded by the sum of the indicators at the other two words.
Integrating under the one common seed proves (112.1). No condition
on the output label or on a schedule's individual error was used.
$\square$

**Theorem 112.2 (Original-source exact-law obstruction).** For every
$L\ge5$, $0<\gamma<1/3$ and tail in (111.1), let $N$ be the
original preselected rule of Theorem 111.2. Every original
$O\in\mathcal O_2$, with arbitrary seed-selected addresses and
full-carrier output laws, satisfies

$$
\sup_{x\in X}\operatorname{TV}
       (\widehat\lambda_{O,x},\widehat\lambda_{N,x})
                      \ge\frac\gamma3.
\tag{112.2}
$$

In particular $p^N\in\mathcal F_N(a,\varepsilon_{L,\gamma})$
but $p^N\notin\mathscr C_L$, while
$p^P\in\mathcal F_N(a,\varepsilon_{L,\gamma})\cap\mathscr C_L$.
This family is an obstruction to exact-law replacement and leaves
the cap intersection nonempty.

**Proof.** First evaluate the measurable event $\{\theta_2\}$ for
$N$ at the three low words in Proposition 112.1. The subset rule
cannot emit $\theta_2$ at these words: coordinate $2$ answers one,
so it is not an emitted queried zero, and label $2$ cannot be the
maximum of a three-subset of $\{1,\ldots,L,*\}$. Thus the $P$
contribution to this event is zero. Table (111.2) gives exactly

$$
p^N_{b^{00}}(2)=0,\qquad
p^N_{b^{01}}(2)=\gamma,\qquad
p^N_{b^{11}}(2)=0.
\tag{112.3}
$$

These violate (112.1). By Theorem 109.1 the finite kernel is outside
$\mathscr C_L$; this conclusion does not depend on a chosen
representation of $p^N$ or on preserving its schedule distribution.

For the unrestricted original lower bound, fix an arbitrary $O$ and
put

$$
d=\sup_{x\in X}\operatorname{TV}
       (\widehat\lambda_{O,x},\widehat\lambda_{N,x}).
\tag{112.4}
$$

Use the common probability-one event $G$ of finite hard-two execution
at all actual sources, the finite increasing preselected schedule
from Definition 90.1 and Proposition 90.2, and its common address
event $J_m$ from (110.10). Then
$\gamma_m=\mathsf P_O(J_m)\to0$. For each $m\ge L+1$, fix
three actual sources $x_{00,m},x_{01,m},x_{11,m}$ with low words
$b^{00},b^{01},b^{11}$ respectively and zero replies at every index
$L<i\le m$. The finite-pattern supplier gives these sources before
seeds. Their actual first absences are $4,4,L+1$ respectively.
No assertion about replies beyond $m$ is made.

On the whole event $G\setminus J_m$, every scheduled address is
at most $m$. The pointwise event argument of Proposition 112.1
continues to hold on these three actual sources. If the schedule
contains $4$, the executions at $x_{00,m},x_{01,m}$ have identical
answers before $4$ and stop at its zero, so they hand off the same
tape. If it does not contain $4$, the entire acquired execution at
$x_{01,m}$ agrees with that at $x_{11,m}$; all other replies through
$m$ coincide. This also covers a schedule stopped at a fixed high
zero. Whole finite-execution transport is the supplier in
Source-Correlated Laws, Lemma 45.3. Since the output event is the
measurable original singleton $\{\theta_2\}$, the argument needs
neither a support restriction nor a measurable tape equality diagonal.

Let $z_{uv,m}=\widehat\lambda_{O,x_{uv,m}}(\{\theta_2\})$.
Integrating the pointwise inequality on $G\setminus J_m$ and
bounding the middle indicator by one on its complement gives

$$
z_{01,m}\le z_{00,m}+z_{11,m}+\gamma_m.
\tag{112.5}
$$

The $N$ laws depend only on the low word, so (112.3) holds at these
actual sources for every $m$. By the event definition of TV,

$$
\gamma-d\le z_{01,m},\qquad
z_{00,m}\le d,\qquad z_{11,m}\le d.
\tag{112.6}
$$

Therefore $\gamma-d\le2d+\gamma_m$. Letting $m\to\infty$
gives $d\ge\gamma/3$. This limit exhausts a common seed event
of a fixed arbitrary-address competitor; it introduces no infinite
all-positive source, no maximum-address restriction and no distribution
on $X$. Repeated-request competitors in $\mathcal N_2$ remain in
that class; the competitor here is the strictly increasing stopped
class specified by Definition 90.1, not a different notion of $O$.

Theorem 111.2 places $p^N$ in the finite cap slice. The same theorem
and the ordered supplier place $p^P$ in that slice, and its stopped
realization places it in $\mathscr C_L$. Thus (112.2) cannot be
read as cap infeasibility. It is a non-strict universal lower bound
on distance from this supplied law; no equality for that distance or
attained distance minimum is asserted. The parameter range is the
stated open interval $0<\gamma<1/3$; the cap and tail inequalities
within it are closed.

All constructed laws use a finite set of original marks in $B_1$.
As in [Acquisition Resources, Theorem
82.1](KBONACCI_SELF_CALIBRATING_ACQUISITION_RESOURCES.md#82-original-carrier-and-resource-applicability-of-the-positive-error-laws),
the unchanged original consumer returns unknown on these tapes,
and their distance from every unchanged nonatomic original target
$\mu_x$ is one. The selected-law conclusions concern (110.3).
The common measurable seed partitions specify exact law existence;
no finite-precision, computational-speed or physical-availability
conclusion follows. $\square$

## 追加锚（本行以下为增补区）
