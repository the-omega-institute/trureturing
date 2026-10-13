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

## 113. Residual demand and a common stopped mixture

**Definition 113.1 (Residual demand at a positive cap).** Retain the
original source, carrier, consumer and selected laws of Definition
110.1, with the entire positive nonincreasing vanishing sequence
(110.2). The classes remain exactly those of Acquisition Resources,
Definition 90.1: the resource is at most two actual requests,
including repetitions, with zero advice and one source-independent
seed. Original competitors retain arbitrary addresses, full-carrier
outputs and sourcewise almost-sure finite handoff. No probability
law on the source set is introduced.

For $0<\varepsilon\le1$ define

$$
L=\max\bigl(\{i:a_i>\varepsilon\}\cup\{0\}\bigr),\qquad
d_i=(a_i-\varepsilon)_+,\qquad
D_3(a,\varepsilon)=\sum_{i=3}^{\infty}d_i.
\tag{113.1}
$$

The active length $L$ is finite, so this residual sum is finite
without a summability assumption on the amplitudes. In particular
$d_i=0$ for $i>L$. The finite cap slice and the coefficient region
are $\mathcal F_N(a,\varepsilon)$ and $\mathscr C_L$ from Sections
108--110. All conclusions concern the separately selected atomic
laws (110.3); the original nonatomic targets remain fixed.

**Theorem 113.2 (An arbitrary-length necessary residual bound).** For
every sequence (110.2) and every $0<\varepsilon\le1$,

$$
\mathcal F_N(a,\varepsilon)\ne\varnothing
\quad\Longrightarrow\quad
D_3(a,\varepsilon)\le3\varepsilon+1-a_1.
\tag{113.2}
$$

By Theorem 110.2 this is necessary for every original
$\mathcal N_2$ acquisition at the cap, and hence for every original
$\mathcal O_2$ acquisition there.

**Proof.** If $L\le2$, the residual sum is zero and the inequality
is automatic. Let $L\ge3$ and $p\in\mathcal F_N(a,\varepsilon)$.
Extend the chain-score argument of Acquisition Resources, Theorem
91.1, to the $L+1$ words and label events

$$
\begin{aligned}
w_t&=1^t0^{L-t}\quad(0\le t\le L),\\
H_0&=\{1\},\qquad H_1=\{0,2\},\\
H_t&=\{t+1\}\quad(2\le t<L),\qquad H_L=\{0\}.
\end{aligned}
\tag{113.3}
$$

Fix the common seed of a finite preselected rule. Two distinct
queried coordinates $i<j$ divide this chain into the three transcript
intervals $t<i$, $i\le t<j$, and $j\le t$. A terminal label is
constant on each interval. The only repeated label between distinct
events in (113.3) is zero, shared by $H_1$ and $H_L$. No interval
can contain both $t=1$ and $t=L$: equality of both queried bits on
these two words would require both distinct coordinates to be at
most one. Thus each interval scores at most one and the total is
at most three. A single distinct coordinate gives at most two
intervals, only one of which can score twice through that shared
zero label, again giving at most three. With no coordinate the
score is at most two. Repeated requests do not refine transcripts
because the answers are static. These bounds permit every terminal
label, including unqueried marks and the base label.

Integrating under the one common mixture proves

$$
p_{w_0}(1)+p_{w_1}(0)+p_{w_1}(2)
       +\sum_{t=2}^{L-1}p_{w_t}(t+1)+p_{w_L}(0)\le3.
\tag{113.4}
$$

The cap rows (110.6) bound the first singleton, the pair event,
the later singletons and the final base event from below by
$a_1-\varepsilon$, $1-\varepsilon$, $d_{t+1}$, and
$1-\varepsilon$, respectively. Hence

$$
a_1+2+D_3(a,\varepsilon)-3\varepsilon\le3,
\tag{113.5}
$$

which is (113.2). The row at $w_1$ uses the pair event
$\{0,2\}$, not just a singleton demand. The original-to-finite
direction of Theorem 110.2 supplies the cap-feasible $p$ for any
original competitor; no bounded-address or mark-support assumption
on that competitor has entered this proof. $\square$

**Theorem 113.3 (Synthesis from the residual increments).** For every
sequence (110.2) and every $0<\varepsilon\le1$,

$$
D_3(a,\varepsilon)\le3\varepsilon
\quad\Longrightarrow\quad
\mathcal F_N(a,\varepsilon)\cap\mathscr C_L\ne\varnothing.
\tag{113.6}
$$

There is an explicit original $\mathcal O_2$ acquisition at this
closed cap, using one common seed and handing an original mark off
after finitely many operations at every source and every seed. If
$L\ge3$, its TV error is exactly $\varepsilon$ at every source
with first absence at most $L$. At every actual tail source its
error is $\max\{D_3(a,\varepsilon)/3,a_{n(x)}\}$. The finite
kernel of this rule satisfies $c\ge H$ by Theorem 109.1.

**Proof.** When $L\le2$, preselect the active prefix and query it
in increasing order until its first zero or exhaustion. At a zero
$n\le L$, emit $\theta_n$ with probability $a_n$ and otherwise
$\theta_0$; emit $\theta_0$ on positive exhaustion. These terminal
choices are fixed from the same seed before replies. Every active
target is realized exactly, and every actual tail has error
$a_{n(x)}\le\varepsilon$. For $L=0$ the rule immediately emits
$\theta_0$. Theorems 109.1 and 110.2 give (113.6) in these cases.

Let $L\ge3$, abbreviate $D=D_3(a,\varepsilon)$, and set
$s=D/3$. Use the subset rule $P_{m,2}$ of Acquisition Resources,
Theorem 87.1, for $3\le m\le L$. Its execution does not depend
on the target amplitudes: choose uniformly a three-subset of the
ordered labels $1<\cdots<m<\ast$, with $\ast$ meaning
$\theta_0$; query its first two numerical labels increasingly until
a zero, emit that zero's mark, and otherwise emit the third label
without querying it. Denote its kernel, extended to $B_L$, by
$p^{(m)}$.

The supplied inclusion identity (87.5) gives, for every word whose
first zero is $n\le m$,

$$
p^{(m)}_b(n)=\frac3{m+1}.
\tag{113.7}
$$

It holds with every multiple-zero suffix: if the subset contains
$n$, all selected coordinates before $n$ are positive, whether
$n$ is queried or is its unqueried last label; if it does not
contain $n$, no output can equal $n$. The same subset rule also has
the following base formula. Put $k_m(b)=\sum_{i=1}^m b_i$. Base
emission requires a subset containing $\ast$ whose two numerical
coordinates both answer one. Consequently

$$
p^{(m)}_b(0)=
\frac{\binom{k_m(b)}2}{\binom{m+1}3},\qquad
\binom{k}2=0\quad(0\le k<2).
\tag{113.8}
$$

In particular this is $3/(m+1)$ whenever the first $m$ bits are
positive, including when the actual first absence is greater than
$m$. No all-positive infinite source is required.

Define the common schedule-family weights

$$
w_m=\frac{m+1}{3}(d_m-d_{m+1})\quad(3\le m\le L),\qquad
W=\sum_{m=3}^Lw_m,\qquad R=1-W,\qquad d_{L+1}=0.
\tag{113.9}
$$

They are nonnegative by monotonicity. Telescoping gives both a
probability budget and a wrong-output budget:

$$
\begin{aligned}
W&=\frac{4d_3+\sum_{i=4}^Ld_i}{3}=d_3+s,\\
\sum_{m=3}^Lw_m\frac{m-2}{m+1}
 &=\frac13\sum_{m=3}^L(m-2)(d_m-d_{m+1})=s.
\end{aligned}
\tag{113.10}
$$

Since $s\le\varepsilon$ and $d_3=a_3-\varepsilon$,

$$
W=a_3-\varepsilon+s\le a_3\le1,\qquad
R\ge1-a_3\ge a_n-a_3\ge0\quad(n=1,2).
\tag{113.11}
$$

With mass $w_m$ use $P_{m,2}$. With the remaining mass $R$, use
the preselected increasing schedule $(1,2)$, stopping at its first
zero. If $R>0$, on its zero cell $n=1$ or $2$ emit $\theta_n$
with probability

$$
\alpha_n=\frac{a_n-a_3}{R},\qquad 0\le\alpha_n\le1,
\tag{113.12}
$$

and otherwise emit $\theta_0$. On positive exhaustion emit
$\theta_0$. If $R=0$, omit this branch. In that case (113.11)
forces $a_3=1$ and $s=\varepsilon$, so $a_1=a_2=a_3=1$
and both numerators in (113.12) vanish; no division is needed.
There is no separate error cap on a branch.

Let $p$ be the resulting mixed law. Fix any $b\ne1^L$ and put
$n=n_L(b)$. When $n\ge3$, every branch $m<n$ outputs a label
at most $m$ or zero, and the prefix branch emits zero. Thus

$$
p_b(n)=\sum_{m=n}^L\frac{3w_m}{m+1}=d_n=a_n-\varepsilon.
\tag{113.13}
$$

When $n=1$ or $2$, all subset branches contribute in (113.7),
and the prefix branch contributes $R\alpha_n=a_n-a_3$.
If it is omitted this contribution and its numerator are both zero.
Hence in these cases as well

$$
p_b(n)=d_3+a_n-a_3=a_n-\varepsilon.
\tag{113.14}
$$

For all $n\le L$, let
$\delta_b=1-p_b(0)-p_b(n)$ be the mass outside the target pair.
The prefix branch adds none. If $n\le m$, (113.7) bounds the
outside-pair mass of $P_{m,2}$ by $(m-2)/(m+1)$. If $n>m$,
its positive prefix and (113.8) give exactly that outside-pair mass,
since it cannot emit $n$. Applying the common weights in (113.10)
therefore yields

$$
0\le\delta_b\le s\le\varepsilon.
\tag{113.15}
$$

Equations (113.13)--(113.15) verify all three TV rows simultaneously
for this one kernel:

$$
\begin{aligned}
p_b(n)&=a_n-\varepsilon,\\
p_b(0)&=1-a_n+\varepsilon-\delta_b\ge1-a_n,\\
p_b(0)+p_b(n)&=1-\delta_b\ge1-\varepsilon.
\end{aligned}
\tag{113.16}
$$

These hold on every word, with every additional zero pattern.
Relative to $(1-a_n)e_0+a_ne_n$, the mass at $n$ has deficit
$\varepsilon$, while the base excess is
$\varepsilon-\delta_b$ and the outside-pair mass is $\delta_b$.
Thus the TV distance is exactly $\varepsilon$.

At $1^L$, every subset branch has base probability $3/(m+1)$
and the prefix branch emits base. Therefore

$$
p_{1^L}(0)=R+\sum_{m=3}^L\frac{3w_m}{m+1}
          =R+d_3=1-s.
\tag{113.17}
$$

All outputs are in $\{\theta_0,\ldots,\theta_L\}$, so at every
actual source with $n(x)>L$, the exact tail identity (110.9) gives
$\max\{s,a_{n(x)}\}\le\varepsilon$. This retains all original
tail amplitudes, including $a_{L+1}=\varepsilon$, and all later
zero patterns.

For the common-seed realization, partition $U\in[0,1)$ into
half-open intervals of masses $R,w_3,\ldots,w_L$, omitting zero
masses. Refine the $w_m$ interval into equal intervals for its
three-subsets. On a positive $R$ interval, its rescaled local seed
$V$ fixes both prefix-cell choices before acquisition: cell $n$
emits its mark exactly when $V<\alpha_n$. The two thresholds use
the same $V$ and require no independence; each has its stipulated
conditional marginal. Thus the entire increasing schedule and all
its terminal outputs are fixed from one source-independent seed,
not from knowledge of the actual first absence. Seed endpoints
are assigned by the half-open convention. Every record and output
event is measurable.

Execute the chosen schedule by making its actual prime requests
on the same original source, stopping at its first queried zero
or exhaustion. Every branch makes at most two actual requests and
hands its selected original tape off finitely for every seed and
source. The finite kernel is in $\mathscr O_L$, so Theorem 109.1
places it in $\mathscr C_L\subseteq\mathscr N_L$. Theorem 110.2
provides the original closed-cap conclusion without changing the
carrier, consumer, source or amplitudes. Proposition 90.2 supplies
an $\mathcal N_2$ realization by completing the chosen schedule
and ignoring the reply after its reconstructed stop; any such
extra acquired reply is counted. Non-strict inequalities in
(113.11) and (113.15) include $D=3\varepsilon$, $R=0$, zero
residual increments, plateaus and every zero schedule weight.
$\square$

## 114. A saturated first amplitude and an attained common optimum

**Theorem 114.1 (Exact feasibility when the first amplitude is one).**
For every sequence (110.2) with $a_1=1$, and every
$0<\varepsilon\le1$, the following conditions are equivalent:

$$
\begin{aligned}
&\exists N\in\mathcal N_2:\ e_a(N)\le\varepsilon;\\
&\exists O\in\mathcal O_2:\ e_a(O)\le\varepsilon;\\
&\mathcal F_N(a,\varepsilon)\cap\mathscr C_L\ne\varnothing;\\
&D_3(a,\varepsilon)\le3\varepsilon.
\end{aligned}
\tag{114.1}
$$

No condition of a unit plateau, summability or bounded active length
is imposed. The comparison concerns replacement by some stopped
kernel in the cap slice, not preservation of every preselected
kernel's output law.

**Proof.** Theorem 113.2 with $a_1=1$ gives the last condition
from original preselected feasibility, using Theorem 110.2.
Theorem 113.3 gives an original stopped rule from that condition.
Stopped feasibility implies preselected feasibility by Proposition
90.2, and Theorem 110.2 equates stopped feasibility to the displayed
intersection. The constructions also cover $L=0,1,2$ and
$\varepsilon=1$. $\square$

**Theorem 114.2 (Attained optimum for every saturated vanishing
profile).** For every sequence (110.2) with $a_1=1$, put

$$
S_m=\sum_{i=3}^m a_i\quad(m\ge3),\qquad
r(a)=\max_{m\ge3}\frac{S_m}{m+1}.
\tag{114.2}
$$

The maximum exists at a finite index and $0<r(a)<1$. With the
original infima of Acquisition Resources, Definition 90.1,

$$
E_{\mathcal N}(2;a)=E_{\mathcal O}(2;a)=r(a).
\tag{114.3}
$$

Both infima are attained by original acquisitions with the same
source-independent seed law, and the stopped attainer is the rule
of Theorem 113.3 at $\varepsilon=r(a)$. In particular the optimum
does not depend on $a_2$ within its allowed monotone range.

**Proof.** By monotonicity the positive terms $a_i-\varepsilon$
form a prefix, with a finite last index for each positive cap.
Consequently

$$
D_3(a,\varepsilon)=
\max\left\{0,\sup_{m\ge3}
             \bigl(S_m-(m-2)\varepsilon\bigr)\right\}.
\tag{114.4}
$$

If $L\ge3$, the expression is maximized at $m=L$, possibly also
at subsequent indices whose amplitudes equal the cap. If $L\le2$,
all its summands are nonpositive and the outer maximum is zero.
It follows that

$$
D_3(a,\varepsilon)\le3\varepsilon
\quad\Longleftrightarrow\quad
S_m\le(m+1)\varepsilon\quad\hbox{for every }m\ge3.
\tag{114.5}
$$

The ratios in (114.2) tend to zero. Indeed, for any $t>0$, choose
$M\ge3$ with $a_i\le t$ for $i>M$; then for $m>M$,
$S_m/(m+1)\le S_M/(m+1)+t(m-M)/(m+1)$, whose limit superior
is at most $t$. Since $a_3/4>0$, a tail of these ratios is below
half that positive value. Their positive supremum is therefore
the maximum of a finite initial set. At its maximizing index,
$S_m/(m+1)\le(m-2)/(m+1)<1$, so $0<r(a)<1$.

At $\varepsilon=r(a)$ all inequalities in (114.5) hold. At a
maximizing index $m$, one has
$S_m-(m-2)r(a)=3r(a)$, so (114.4) also proves

$$
D_3(a,r(a))=3r(a).
\tag{114.6}
$$

The active length at this positive cap is finite and at least three.
Theorem 113.3 constructs the stopped rule, with error exactly
$r(a)$ in every active first-absence class and at most $r(a)$
at every actual tail. Each such class has an actual source by the
finite-pattern supplier in Definition 110.1. Thus its uniform
error is $r(a)$. Complete its schedule as in Proposition 90.2
using the same seed to obtain a preselected attainer of the same
error, still counting every acquired reply.

If an original preselected rule had uniform error less than $r(a)$,
choose a positive cap strictly between that error and $r(a)$.
Theorem 114.1 and (114.5) would then contradict a maximizing
prefix in (114.2). Stopped rules are included among preselected
law families, so neither infimum can be smaller. This proves
(114.3), including attainment. The argument uses vanishing, not
summability, and every original amplitude remains part of the
selected target family. $\square$

## 115. Unequal amplitudes and a lost joint constraint

**Proposition 115.1 (An unequal-amplitude closed-endpoint attainer).**
Consider the sequence

$$
a_1=1,\quad a_2=\frac45,\quad a_3=\frac35,\quad
a_4=\frac12,\quad a_5=\frac25,\qquad
a_{5+j}=\frac1{4j}\quad(j\ge1).
\tag{115.1}
$$

Its original hard-two optima in both restricted classes are
$1/4$, attained at that closed cap. The stopped attainer of
Theorem 113.3 uses the subset families $P_{3,2},P_{4,2},P_{5,2}$
and the prefix family $(1,2)$ with respective weights
$2/15,1/6,3/10,2/5$. In the prefix family, the zero at coordinate
one is emitted surely; the zero at coordinate two is emitted with
probability $1/2$, otherwise emitting the base mark.

**Proof.** The sequence is positive, nonincreasing and vanishes,
with unequal active amplitudes. At $\varepsilon=1/4$ its active
length is five, since the actual next amplitude is exactly
$a_6=1/4$. The residuals and budget are

$$
d_3=\frac7{20},\quad d_4=\frac14,\quad d_5=\frac3{20},\qquad
D_3=\frac34,\quad s=\frac14,\quad R=\frac25.
\tag{115.2}
$$

Substitution in (113.9) gives the stated weights, whose sum is
one. Formula (113.12) gives $\alpha_1=1$ and $\alpha_2=1/2$.
For every word with first zero $n\le5$, the correct-mark masses
are, in order,

$$
\frac34,\quad\frac{11}{20},\quad\frac7{20},\quad
\frac14,\quad\frac3{20}.
\tag{115.3}
$$

Equations (113.15)--(113.16) verify the base and pair rows on all
these words as well, giving TV exactly $1/4$. At the all-positive
low word the base mass is $3/4$, so every actual tail has error
$\max\{1/4,a_{n(x)}\}=1/4$, including $n(x)=6$.

The first prefix ratios are $S_3/4=3/20$, $S_4/5=11/50$,
$S_5/6=1/4$, and $S_6/7=1/4$. Since all subsequent amplitudes
are at most $1/4$, induction preserves $S_m\le(m+1)/4$ for
$m>6$. Thus $r(a)=1/4$, and Theorem 114.2 proves optimality
against all original preselected and stopped competitors. The
weights and inequalities are attained without removing the tail
at the cap endpoint. $\square$

**Definition 115.2 (A residual summary and its feasibility fibre).**
For the fixed original source and a positive cap, consider the
summary

$$
\Sigma_\varepsilon(a)=
  \bigl(\varepsilon,a_1,D_3(a,\varepsilon),a_3,a_4\bigr).
\tag{115.4}
$$

A summary determines cap feasibility on a class of amplitude
sequences if any two sequences in that class with the same summary
give the same truth value for
$\mathcal F_N(a,\varepsilon)\ne\varnothing$. Theorem 114.1
shows that $(\varepsilon,D_3)$ suffices for this predicate on
$a_1=1$. It does not assert that the summary reconstructs a
kernel; the sampler in (113.9) uses the individual residuals.

**Proposition 115.3 (Identical residual summaries with different
feasibility).** At $\varepsilon=1/10$, let two sequences $a^A,a^B$
share

$$
a_1=\frac{17}{20},\quad a_3=\frac7{20},\quad a_4=\frac14,\qquad
a_i=\frac1{10\cdot2^{i-4}}\quad(i\ge5),
\tag{115.5}
$$

and set $a^A_2=4/5$, $a^B_2=17/20$. Both satisfy (110.2),
have $L=4$, and have the same summary (115.4), with
$D_3=2/5\le3\varepsilon+1-a_1=9/20$. Nevertheless

$$
\begin{aligned}
\mathcal F_N(a^A,\varepsilon)\cap\mathscr C_4
   &\ne\varnothing,\\
\mathcal F_N(a^B,\varepsilon)&=\varnothing.
\end{aligned}
\tag{115.6}
$$

This is failure of the summary to determine general feasibility,
not a separation of preselected and stopped cap feasibility.

**Proof.** The shared residuals are $d_3=1/4,d_4=3/20$;
the shared tail begins at $a_5=1/20$. All assertions about the
sequence hypotheses and its summary follow directly.

For an explicit stopped witness for $a^A$, write
$[i;T_0,T_1]$ for querying coordinate $i$, followed by the zero
or one branch, and write a label for its original output mark.
Use the six seed-fixed tables with these common weights:

$$
\begin{array}{c|l}
\text{weight}&\text{table}\\\hline
3/5 &[1;1,[2;2,0]]\\
1/20 &[1;1,[2;2,3]]\\
1/20 &[1;1,[2;2,4]]\\
1/10 &[1;1,[3;3,0]]\\
1/10 &[2;0,[3;3,0]]\\
1/10 &[3;0,[4;4,0]]
\end{array}
\tag{115.7}
$$

Every table preselects an increasing pair and stops at its first
queried zero or at exhaustion. The unqueried outputs in its last
cell are permitted by Definition 90.1. The weights sum to one.
For every word in $B_4$ the mixed law has the following masses;
free suffix bits in the first two rows are unrestricted:

$$
\begin{array}{c|c|c|c}
\text{first zero}&p_b(n)&p_b(0)&p_b(0)+p_b(n)\\\hline
1&4/5&
  1/5-\tfrac1{10}b_2(1-b_3)-\tfrac1{10}b_3(1-b_4)&\ge9/10\\
2&7/10&1/5+\tfrac1{10}b_3b_4&\ge9/10\\
3&1/4&7/10&19/20\\
4&3/20&4/5&19/20\\
\text{none}&\text{--}&9/10&\text{--}
\end{array}
\tag{115.8}
$$

To obtain the first row, the first four tables contribute $4/5$
to label one. The remaining two can output a nonbase label only
on $b_2=1,b_3=0$ and on $b_3=1,b_4=0$, respectively. These
events are disjoint, proving the lower base mass $1/10$ and the
pair bound. In the second row the first three tables contribute
$7/10$ to label two. The fifth always emits base, the fourth
emits base when $b_3=1$, and the sixth emits base when $b_3=0$
or $b_4=1$, giving its displayed base formula. The last three
rows follow by substituting $110b_4$, $1110$ and $1111$ into
the same tables.

Thus for each first-zero class the correct singleton has mass at
least $a^A_n-1/10$, the base singleton has mass at least
$1-a^A_n-1/10$, and the pair has mass at least $9/10$. The
all-positive row has base mass $9/10$. These are all the TV rows
(110.6), including every multiple-zero word. The error equals
$1/10$, for example in first-zero class two, whose correct-label
deficit is $1/10$. Partitioning one uniform seed into the six
weight intervals realizes the tables on the same actual source
with at most two requests and finite handoff for every seed.
Theorems 109.1 and 110.2 place its kernel in the first
intersection in (115.6). Every actual tail has error
$\max\{1/10,a_{n(x)}\}=1/10$ by (110.9).

For $a^B$, use the weighted seven-event necessary certificate of
Acquisition Resources, Lemma 97.2, specifically (97.5)--(97.7).
It already includes arbitrary-address and full-carrier original
competitors and yields

$$
a_2+2a_3+2a_4-1\le10\varepsilon.
\tag{115.9}
$$

Its left side for $a^B$ is $21/20>1=10\varepsilon$, so no
original preselected rule meets the cap. Equivalently the required
weighted score is $121/20$, exceeding the supplied upper score
six. Theorem 110.2 gives the second line of (115.6); containment
also excludes a stopped attainer there. The lost joint relation
can be written with $h=(a_3+a_4-5\varepsilon)_+=1/10$ as
$a_2\le1-2h=4/5$, the restriction in Acquisition Resources,
Corollary 96.3. Sequence $a^A$ meets it at equality and $a^B$
violates it. Therefore even adjoining $a_3,a_4$ to the residual
summary cannot recover this relation. The two restricted classes
agree on each sequence's feasibility; (115.6) does not distinguish
them. $\square$

## 116. The remaining intersection strip

**Corollary 116.1 (Necessary location of a cap separator).** If a
sequence (110.2) and a cap $0<\varepsilon\le1$ satisfy

$$
\mathcal F_N(a,\varepsilon)\ne\varnothing,\qquad
\mathcal F_N(a,\varepsilon)\cap\mathscr C_L=\varnothing,
\tag{116.1}
$$

then necessarily

$$
a_1<1,\qquad L\ge5,\qquad
3\varepsilon<D_3(a,\varepsilon)
                 \le3\varepsilon+1-a_1.
\tag{116.2}
$$

**Proof.** The upper bound is Theorem 113.2. Theorem 113.3
excludes $D_3\le3\varepsilon$, and the strict lower bound together
with the upper bound forces $a_1<1$. Acquisition Resources,
Proposition 93.1 gives identical restricted feasibility for
$L\le3$, and Theorem 96.2 gives it for $L=4$. For active length
four its cap hypothesis holds automatically:
$a_5\le\varepsilon<a_4$. Hence (116.1) requires $L\ge5$.
These are necessary location conditions, not a stopped
infeasibility certificate in the strip. $\square$

**Definition 116.2 (The unresolved replacement obligation).** The
remaining implication (110.14) still asks for a stopped kernel
at the same cap whenever any preselected kernel is cap feasible.
For $a_1<1$ in the strip (116.2), the residual sandwich does not
settle this implication: the construction (113.9)--(113.16) uses
the bound $D_3\le3\varepsilon$ and does not absorb the additional
head allowance $1-a_1$. Proposition 115.3 exhibits a joint
constraint lost by a residual summary, but neither its feasible
sequence nor its infeasible sequence satisfies (116.1).
The exact-law obstruction of Theorem 112.2 likewise retains
a different stopped law at the same cap. No general cap separator
or universal replacement theorem follows from those obstructions.

All attainers here output original atomic marks in $B_1$, so the
unchanged consumer returns unknown on them. Their distance from
each unchanged nonatomic original target $\mu_x$ is one, as in
Acquisition Resources, Theorem 82.1. These selected-target
conclusions therefore change neither that consumer nor those
targets. The common seed specifies exact measurable law existence;
it imposes no runtime, address or mean-request resource in place
of the hard actual-request count. A constructed finite address
bound is an existence property of the attainer, not a restriction
on competitors. Caps above one admit immediate base output;
zero cap is outside the positive-cap statements.

## 追加锚（本行以下为增补区）

## 117. A uniform second-head necessary certificate

**Definition 117.1 (Weighted prefix events).** Retain Definition
110.1 and Acquisition Resources, Definition 90.1, including the
entire original positive nonincreasing vanishing sequence (110.2).
The source is the actual countable labeled prime-answer source;
its answers are static. The resource is a hard count of at most
two actual requests, including repetitions, with zero advice, one
source-independent common seed and sourcewise almost-sure finite
handoff. Original competitors retain arbitrary addresses and the
full original measurable output carrier. All targets here are the
separately selected marked laws (110.3).

For an integer $m\ge4$, use the finite targets on $B_m$ with first
zero $n$ given by $\eta_b=(1-a_n)e_0+a_ne_n$, and put
$\eta_{1^m}=e_0$. This last word is finite bookkeeping, not an
infinite all-positive actual source. Define the following words:
$h_k$ has its sole one at $k$; $g=10^{m-1}$; $g_k$ has ones
precisely at $1,k$; and

$$
w_n=1^{n-1}0^{m-n+1},\qquad
v_n=1^{n-1}0\,1^{m-n-1}0.
\tag{117.1}
$$

The weighted events $(b,E_b,k_b)$ are

$$
\begin{array}{c|c|c|c}
\text{word}&\text{index range}&E_b&k_b\\\hline
h_k&2\le k\le m-1&\{0,1\}&1\\
g&\text{one row}&\{0,2\}&1\\
g_k&3\le k\le m-1&\{2\}&1\\
w_n&3\le n\le m-2&\{n\}&m-3\\
v_n&3\le n\le m-2&\{n\}&1\\
w_n&n=m-1,m&\{n\}&m-2\\
1^m&\text{one row}&\{0\}&m-2
\end{array}
\tag{117.2}
$$

Empty index ranges contribute no rows. For a kernel $p$ define
$S_m(p)=\sum_b k_b p_b(E_b)$, with the sum taken over these
rows. Their total weight and target score are

$$
\begin{aligned}
M_m&=(m-2)(m+1),\\
T_m&=\sum_bk_b\eta_b(E_b)
 =2m-3+(m-3)a_2+(m-2)\sum_{n=3}^m a_n.
\end{aligned}
\tag{117.3}
$$

**Theorem 117.2 (Uniform original-source second-head bound).**
For every sequence (110.2), every integer $m\ge4$ and every
original acquisition $A\in\mathcal N_2$,

$$
(m-2)(m+1)e_a(A)
 \ge (m-3)a_2+(m-2)\sum_{n=3}^m a_n-(m-3).
\tag{117.4}
$$

The same bound holds for every $A\in\mathcal O_2$. No assumption
on $a_{m+1}$, no restriction on competitor addresses or output
support, and no probability law on the source set is imposed.

**Proof.** First consider a finite preselected rule on $B_m$.
Fix its common seed, which fixes both its schedule and its entire
deterministic terminal table. For a distinct queried pair $i<j$
and acquired cell $uv$, the score of output label $r$ is

$$
g_{ij}^{uv}(r)=
 \sum_{b:(b_i,b_j)=(u,v)}k_b\mathbf1_{r\in E_b}.
\tag{117.5}
$$

Every nonzero label in $J_m$ has total event weight $m-2$;
labels outside the displayed events have score zero. The four
maximum cell scores are

$$
\begin{array}{c|cccc}
\text{pair}&00&01&10&11\\\hline
i<j<m&m-3&1&m-2&m-2\\
i<j=m&m-2&0&m-2&m-2
\end{array}
\tag{117.6}
$$

Here is a uniform verification of all entries. Suppose $j<m$.
In cell $00$, label zero receives $m-3$ rows of weight one:
if $i=1$ these are the $h_k$ with $k\ne j$, while if $i>1$
there are $m-4$ such $h_k$ plus $g$. Label one receives only
those $h_k$; label two receives at most $m-3$ rows, from $g$
and the admissible $g_k$. For a later label $n$, a contributing
$w_n$ in $00$ requires $n\le i\le m-2$ and has weight
$m-3$. Its $v_n$ cannot also contribute there: its only zeros
are $n,m$. Thus the $00$ maximum is $m-3$.

In cell $01$, labels zero and one receive only $h_j$, of
weight one. Label two receives at most $g_j$. A chain word
$w_n$ never has bits $01$ at increasing coordinates; the only
possible later-label contribution is $v_i$, of weight one.
Thus this maximum is one. In cell $10$, label zero has score
at most one, and every nonzero label has total weight $m-2$.
Label $j$ attains that weight. For $j=2$, necessarily $i=1$;
$g$ and the $m-3$ rows $g_k$, $3\le k\le m-1$, contribute
one each, totaling $m-2$. For $3\le j\le m-2$, $w_j,v_j$
contribute $m-3,1$, and for $j=m-1$, $w_{m-1}$ contributes
$m-2$. In cell $11$, label zero attains $m-2$ from $1^m$;
no other zero-label row is in that cell. This proves the first
line of (117.6).

If $j=m$, every row word except $1^m$ has last bit zero, so
the $01$ cell carries no weight. In $00$, label zero receives
$m-2$ unit rows: all $h_k$ when $i=1$, or the $m-3$ rows
$h_k$ with $k\ne i$ together with $g$ when $i>1$. Other
labels cannot exceed their total weight $m-2$. Label $m$
attains $m-2$ in $10$ from $w_m$, and label zero attains
$m-2$ in $11$ from $1^m$. The second line follows.

Every distinct pair therefore scores at most $3(m-2)$.
An empty, singleton or repeated-coordinate schedule gives a
coarsening of a distinct pair's cells, and cannot improve that
upper bound. Reverse query order changes no acquired static
information. Integrating the seed-fixed score gives
$S_m(p)\le3(m-2)$ for every finite preselected kernel. If all
word laws are within cap $r$ of their targets, each event has
$p_b(E_b)\ge\eta_b(E_b)-r$, so

$$
T_m-M_mr\le S_m(p)\le3(m-2).
\tag{117.7}
$$

The union events in (117.2) use the independent pair-TV row,
not merely the two singleton rows. Rearranging gives (117.4)
with $r$ in place of $e_a(A)$ for the finite rule.

Now let an original competitor have error at most a positive
$r\le1$. Theorem 110.2 supplies a class-preserving cap-feasible
finite representative at active length $L(r)$. This does not
assert preservation of the original competitor's law. If $L(r)>m$,
fix every higher finite input bit to zero and project every output
label above $m$ to zero. A low first-zero target is fixed; the
low all-positive target becomes $e_0$ under this projection.
TV contracts. Delete the fixed high observations from each
preselected schedule and compose its table with their known zero
replies; this retains at most two low observations. For a stopped
schedule, a reached first high zero determines a terminal choice
without further observation, so the resulting rule is stopped as
well.

If $L(r)<m$, add ignored input bits. At any new first zero
$n>L(r)$, the output has no label $n$, $a_n\le r$, and the
old all-positive row has nonbase mass at most $r$. Consequently

$$
\operatorname{TV}(p,(1-a_n)e_0+a_ne_n)
       =\max\{1-p(0),a_n\}\le r.
\tag{117.8}
$$

The all-positive row is preserved too. This includes $L(r)=0$.
Both operations retain a common seed and a preselected hard-two
schedule. Thus (117.7) applies at every $m$, regardless of the
original tail or competitor addresses. For positive error take
$r=e_a(A)\le1$; for error zero apply the result at every $r>0$
and let $r$ decrease to zero. Error one is included by $r=1$.
Proposition 90.2 supplies $\mathcal O_2\subseteq\mathcal N_2$
with the same seed and law, proving the stopped bound. $\square$

The case $m=4$ is exactly Acquisition Resources, Lemma 97.2,
with $a_2,a_3,a_4$ in place of $v,w,z$. The uniform weighted-event
argument is repo-derived. The scalar expectation characterization
in Kaniewski, Lee and de Wolf, [*Query complexity in expectation*,
Definition 8 and Theorem 9](https://arxiv.org/html/1411.7280v1),
does not supply a common probability-vector stopped cap theorem.
The independent random-input and expected-testing-cost model of
Hellerstein, Kletenik, Liu and Witter, [*Adaptivity Gaps for the
Stochastic Boolean Function Evaluation Problem*, Section
1](https://arxiv.org/html/2208.03810v1), does not supply the uniform
all-source hard-request comparison here. These source relationships
assert no exhaustive mathematical-priority claim.

**Corollary 117.3 (A second restriction on the intersection strip).**
At active length $L\ge4$, cap feasibility in either original
restricted class implies

$$
D_3(a,\varepsilon)
 \le3\varepsilon+\frac{L-3}{L-2}(1-a_2).
\tag{117.9}
$$

In particular any separator as in (116.1) must satisfy

$$
\begin{gathered}
a_1<1,\qquad L\ge5,\\
3\varepsilon<D_3(a,\varepsilon)
 \le3\varepsilon+
 \min\left\{1-a_1,\frac{L-3}{L-2}(1-a_2)\right\}.
\end{gathered}
\tag{117.10}
$$

All prefix inequalities (117.4), including those with $m\ne L$,
remain necessary. None of these necessary inequalities alone is
asserted to be sufficient.

**Proof.** At $m=L$, divide (117.4) by $L-2$ and use
$D_3=\sum_{n=3}^L a_n-(L-2)\varepsilon$. This gives (117.9).
Combine it with Theorem 113.2 and Corollary 116.1 to obtain
(117.10). $\square$

## 118. A sharp five-active family with unequal late amplitudes

**Theorem 118.1 (An explicit stopped attainer on the second-head
boundary).** Choose parameters satisfying

$$
\begin{gathered}
0<\delta\le\frac9{31},\qquad
0\le\alpha\le\frac\delta3,\qquad
\frac{22\delta}9\le t\le1-\delta,\\
u\ge v\ge0,\qquad u+v\le\frac{4\delta}9,\qquad
t+u\le1-\delta.
\end{gathered}
\tag{118.1}
$$

Put

$$
\begin{aligned}
e&=\frac t2-\frac\delta9,\\
a_1&=1-\delta+\alpha,&a_2&=1-\delta,\\
a_3&=t+u,&a_4&=t+v,&a_5&=t-u-v.
\end{aligned}
\tag{118.2}
$$

Retain any original positive nonincreasing vanishing tail with
$a_6\le e$. For the resulting full sequence,

$$
E_{\mathcal N}(2;a)=E_{\mathcal O}(2;a)=e,
\qquad
\mathcal F_N(a,e)\cap\mathscr C_5\ne\varnothing.
\tag{118.3}
$$

Both infima are attained on the original source by acquisitions
using the same common seed. The active length at this closed cap
is five. Feasibility holds at every cap at least $e$ and fails
below $e$. These are feasible amplitude families, not separators.

**Proof.** Define

$$
z=\frac\delta3,\qquad x=\frac{4\delta}9,\qquad
y=\frac t2-\frac{5\delta}9,\qquad
w=1-\frac t2-\frac{4\delta}3.
\tag{118.4}
$$

Use the following seven increasing schedules. Each vector in the
last three columns is an unnormalized terminal mass; its coordinate
mass is the schedule's weight. Cell $0$ contains both acquired
cells $00,01$, while $10,11$ are the two cells reached after a
positive first reply.

$$
\begin{array}{c|c|l|l|l}
\text{schedule}&\text{weight}&0&10&11\\\hline
(1,2)&w&we_1&we_2&
 (w-5\delta/9)e_0+(\delta/9+u)e_3+ve_4+(4\delta/9-u-v)e_5\\
(1,3)&x&xe_1&xe_3&ze_0+(x-z)e_5\\
(1,4)&z&ze_1&ze_4&ze_0\\
(2,3)&x&ze_0+(x-z)e_2&xe_3&ze_0+(x-z)e_5\\
(2,4)&z&ze_2&ze_4&ze_0\\
(3,4)&y&ze_0+(y-z)e_3&ye_4&ze_0+(y-z)e_5\\
(4,5)&z&ze_0&ze_5&ze_0
\end{array}
\tag{118.5}
$$

Normalization follows from $w+2x+y+3z=1$. Every column has its
stated common mass. Nonnegativity uses

$$
x-z=\frac\delta9,\qquad
y-z=\frac t2-\frac{8\delta}9\ge\frac\delta3,\qquad
w-\frac{5\delta}9
 \ge\frac12-\frac{25\delta}{18}\ge\frac3{31},
\tag{118.6}
$$

and $4\delta/9-u-v\ge0$. The amplitude order follows from
$t+u\le1-\delta$ and $u\ge v\ge0$. Moreover

$$
e\ge\frac{10\delta}9>0,\qquad
a_5-e\ge\frac t2-\frac\delta3\ge\frac{8\delta}9>0.
\tag{118.7}
$$

Thus every original amplitude is positive, the sequence has the
required order, and $a_6\le e<a_5$, giving active length five.

We verify all word laws directly. For a word with first zero $n$,
let $p_b$ be the mixture (118.5). The correct-mark probability
is constant throughout each first-zero class, and the base
probability is as follows; all unspecified suffix bits are free:

$$
\begin{array}{c|l|l}
n&p_b(n)&p_b(0)\\\hline
1&w+x+z&
 z\bigl[3-b_2(1-b_3)-b_3(1-b_4)-b_4(1-b_5)+b_2b_4\bigr]\\
2&w+x&z\bigl[3+b_3b_4+b_4b_5\bigr]\\
3&t/2+\delta/9+u&
 1-t/2-11\delta/9+zb_4(1+b_5)\\
4&t/2+\delta/9+v&1-t/2-8\delta/9\\
5&t/2+\delta/9-u-v&1-t/2-2\delta/9
\end{array}
\tag{118.8}
$$

For example, at first zero one the four schedules not starting
at one contribute base masses
$z[1-b_2(1-b_3)]$, $zb_2b_4$,
$z[1-b_3(1-b_4)]$, $z[1-b_4(1-b_5)]$.
The remaining three schedules always emit label one there.
This proves the first row. Substituting $b_1=1,b_2=0$ in the
same seven columns gives the second row, and the remaining rows
follow by substituting $110b_4b_5$, $1110b_5$, $11110$.
The $u,v$ transfer occurs only in the $(1,2)$ exhaustion cell.
It leaves every first-zero-one or first-zero-two law unchanged,
and adds $ue_3+ve_4-(u+v)e_5$ to every first-zero-three,
four or five law and to $11111$.

The first base bracket is at least two. Indeed the number of
positive-to-zero transitions in the four-bit suffix is at most
two; if it is two, then $b_2=b_4=1$ and the extra $b_2b_4$
adds one. The second bracket is at least three. Hence the base
minima in (118.8) are attained respectively at $01000,10000,
11000,11100,11110$. Since each correct probability is fixed
within its class, these words attain the pair minima as well.
It follows that the actual class minima of the three independent
TV-row slacks

$$
p_b(0)-(1-a_n-e),\qquad
p_b(n)-(a_n-e),\qquad
p_b(0)+p_b(n)-(1-e)
\tag{118.9}
$$

are

$$
\begin{array}{c|c|c|c}
n&\text{base slack}&\text{correct slack}&\text{pair slack}\\\hline
1&e-\delta/3+\alpha&\delta/3-\alpha&0\\
2&e&0&0\\
3&t-4\delta/3+u&0&e-10\delta/9+u\\
4&t-\delta+v&0&e-7\delta/9+v\\
5&t-\delta/3-u-v&0&e-\delta/9-u-v
\end{array}
\tag{118.10}
$$

All entries are nonnegative under (118.1). In the last row,
$t-\delta/3-u-v\ge t-7\delta/9\ge15\delta/9$ and
$e-\delta/9-u-v\ge e-5\delta/9\ge5\delta/9$.
The other late base entries use $t\ge22\delta/9$, and the
late pair entries use $e\ge10\delta/9$. The head entries use
$0\le\alpha\le\delta/3$. Thus (110.6) holds on every one of
the 31 words containing a zero, with each pair row checked
independently. No chain-word restriction has been used.

The all-positive law is

$$
p_{11111}=(1-e)e_0+(\delta/9+u)e_3+ve_4
                  +(t/2-2\delta/9-u-v)e_5.
\tag{118.11}
$$

It has nonbase mass exactly $e$ and satisfies the all-positive
base row at equality. Theorem 110.2 and (110.9) give, at every
actual source with first absence $n>5$,

$$
\operatorname{TV}(p_{11111},\lambda_x^a)
          =\max\{e,a_n\}=e.
\tag{118.12}
$$

This retains every actual positive tail amplitude, including
$a_6=e$, and every later multiple-zero answer pattern.

For explicit same-seed realization, partition a source-independent
uniform $U\in[0,1)$ into the seven schedule intervals of the
listed weights. Within each positive-weight interval, rescale
$U$ to $[0,1)$ and predeclare a partition for each of the three
terminal cells according to that cell's normalized vector. All
three choices are fixed simultaneously by $U$; independence
between their partitions is unnecessary. Use half-open intervals
and omit zero-weight intervals. The stopped acquisition queries
the selected increasing pair until its first queried zero or
exhaustion, then hands off the selected original mark $\theta_j$.
With the identical $U$ and schedule, the preselected acquisition
obtains both static replies, reconstructs the same stopped cell
and hands off the same mark. Its second request is counted even
when its reply is ignored. These are measurable acquisitions
with zero advice, at most two actual requests and finite handoff
at every actual source and seed. The original source, full
carrier, consumer and nonatomic targets are unchanged.

The $10$ and $11$ vectors have disjoint supports for each
schedule. In (109.4)--(109.5) there is no empty or singleton
branch, so $v_{ij}=u_{ij}^{10}$, $V_i=B_i$ and
$h_i=(B_i-(B_i-A_i))_+=A_i$. Consequently

$$
\begin{aligned}
c=H={}&\delta e_0+(1-t/2-5\delta/9)e_1
            +(4\delta/9)e_2+(t/2-8\delta/9)e_3,\\
\beta&=1.
\end{aligned}
\tag{118.13}
$$

Theorem 109.1 therefore places this same finite kernel in
$\mathscr C_5$; its coefficient criterion is reused.

Finally the amplitudes satisfy

$$
2a_2+3(a_3+a_4+a_5)-2=18e,\qquad
D_3(a,e)=3e+\frac{2\delta}3>3e.
\tag{118.14}
$$

The $m=5$ case of Theorem 117.2 lower-bounds the error of every
original $\mathcal N_2$ competitor by $e$, including arbitrary
addresses and full-carrier outputs. Containment gives the same
lower bound for $\mathcal O_2$. The common-seed table attains
that bound, proving (118.3). Monotonicity in the allowed cap
proves feasibility above $e$ and impossibility below it.
All displayed non-strict parameter endpoints are included:
$\alpha=0,\delta/3$, compatible endpoints of $\delta,t$,
$u=v$, $v=0$, $u+v=4\delta/9$, $t+u=1-\delta$,
zero terminal masses and $a_6=e$. None requires a limit sampler.
$\square$

**Proposition 118.2 (A strictly unequal late profile at the closed
optimum).** The full original sequence

$$
a_1=a_2=\frac{17}{20},\quad a_3=\frac{16}{25},\quad
 a_4=\frac{31}{50},\quad a_5=\frac{27}{50},\qquad
 a_{5+j}=\frac{17}{60j}\quad(j\ge1)
\tag{118.15}
$$

has both restricted hard-two optima attained at $e=17/60$.
Its active length is five and its all-positive low law is

$$
\frac{43}{60}e_0+\frac{17}{300}e_3+\frac1{50}e_4
                  +\frac{31}{150}e_5.
\tag{118.16}
$$

**Proof.** Substitute $\delta=3/20$, $\alpha=0$, $t=3/5$,
$u=1/25$, $v=1/50$ in (118.1)--(118.2). All inequalities hold,
$a_6=e<a_5$, and the positive tail vanishes. Formula (118.11)
gives (118.16), and Theorem 118.1 gives both original-source
attainers and their uniform optimality. $\square$

## 119. Score loss and the exact five-active feasibility face

**Definition 119.1 (Five-coordinate score and its slack).** The
$m=5$ specialization of (117.2) consists of the following eleven
rows:

$$
\begin{array}{c|c|c|c}
b&E_b&k_b&\eta_b(E_b)\\\hline
01000&\{0,1\}&1&1\\
00100&\{0,1\}&1&1\\
00010&\{0,1\}&1&1\\
10000&\{0,2\}&1&1\\
10100&\{2\}&1&a_2\\
10010&\{2\}&1&a_2\\
11000&\{3\}&2&a_3\\
11010&\{3\}&1&a_3\\
11100&\{4\}&3&a_4\\
11110&\{5\}&3&a_5\\
11111&\{0\}&3&1
\end{array}
\tag{119.1}
$$

For a deterministic preselected terminal table $D$, let
$s(D)=\sum_bk_b\mathbf1_{D(b)\in E_b}$; thus a common
representation of a finite kernel satisfies $S_5(p)=\mathsf E s(D)$.
For cap $\varepsilon$ define

$$
\sigma=18\varepsilon-2a_2-3(a_3+a_4+a_5)+2.
\tag{119.2}
$$

The score uses only these rows; finite cap feasibility still means
all 32 word laws and all separate TV rows (110.6).

**Theorem 119.2 (Quantitative score-loss restriction).** For every
finite preselected five-coordinate kernel cap feasible for these
targets, and every common deterministic-table representation,

$$
\begin{aligned}
\mathsf E[9-s(D)]&\le\sigma,\qquad \sigma\ge0,\\
\mathsf P\{D\text{ queries at most one distinct coordinate}\}
       &\le\sigma/2,\\
\mathsf P\{s(D)<9\}&\le\sigma.
\end{aligned}
\tag{119.3}
$$

At $\sigma=0$, almost every represented table uses a distinct
pair and maximizes each of its acquired-cell scores. Each of the
eleven event inequalities is then an equality:
$p_b(E_b)=\eta_b(E_b)-\varepsilon$.

**Proof.** Every $s(D)$ is an integer at most nine by (117.6).
Directly summing (119.1), an empty schedule scores at most seven;
for a singleton coordinate $1,2,3,4$ the two cell maxima are
$3,4$, and for coordinate five they are $4,3$. Repeated-coordinate
schedules acquire the same static information as a singleton and
also score at most seven. Thus a short schedule loses at least
two score units, and any nonmaximizing table loses at least one.
The cap event inequalities give

$$
S_5(p)\ge7+2a_2+3(a_3+a_4+a_5)-18\varepsilon
          =9-\sigma.
\tag{119.4}
$$

Together with $S_5(p)\le9$, this proves the expectation and
probability bounds. At $\sigma=0$ all nonnegative score loss
vanishes almost surely. The sum of the four cell maxima of every
distinct pair is nine, so each cell's output must maximize its
score. Also each gap
$p_b(E_b)-\eta_b(E_b)+\varepsilon$ is nonnegative, and their
weighted sum is

$$
S_5(p)-[7+2a_2+3(a_3+a_4+a_5)]+18\varepsilon=0.
\tag{119.5}
$$

Every row weight is positive, forcing all eleven gaps to vanish.
$\square$

**Theorem 119.3 (An exact system on the five-active equality face).**
Assume the full original sequence satisfies (110.2), with

$$
1\ge a_1\ge a_2\ge a_3\ge a_4\ge a_5>\varepsilon>0,
\qquad a_6\le\varepsilon,\qquad \sigma=0.
\tag{119.6}
$$

For each $i<j\le5$, let $w_{ij}\ge0$ and let
$T_{ij}^{uv}\in\mathbb R_+^{J_5}$ be four terminal-mass vectors.
Consider the common-mass conditions and the word laws

$$
\mathfrak m(T_{ij}^{uv})=w_{ij}\quad(uv=00,01,10,11),\qquad
\sum_{i<j}w_{ij}=1,\qquad
p_b=\sum_{i<j}T_{ij}^{b_i b_j}.
\tag{119.7}
$$

Require that these laws satisfy all 94 separate rows (110.6),
namely the three TV rows on each of the 31 zero-containing words
and the all-positive base row. Require also that each
$T_{ij}^{uv}$ be supported on the corresponding maximizing-label
set in this table:

$$
\begin{array}{c|c|c|c|c}
(i,j)&W^{00}_{ij}&W^{01}_{ij}&W^{10}_{ij}&W^{11}_{ij}\\\hline
(1,2)&\{0,1\}&\{0,1\}&\{2\}&\{0,3,4,5\}\\
(1,3)&\{0,1\}&\{0,1\}&\{3\}&\{0,4,5\}\\
(1,4)&\{0,1\}&\{0,1\}&\{4\}&\{0,5\}\\
(1,5)&\{0,1\}&J_5&\{2,3,4,5\}&\{0\}\\
(2,3)&\{0,2\}&\{0,1,2\}&\{3\}&\{0,4,5\}\\
(2,4)&\{0,2\}&\{0,1,2\}&\{4\}&\{0,5\}\\
(2,5)&\{0,2\}&J_5&\{3,4,5\}&\{0\}\\
(3,4)&\{0,3\}&\{0,1,2,3\}&\{4\}&\{0,5\}\\
(3,5)&\{0,3\}&J_5&\{4,5\}&\{0\}\\
(4,5)&\{0,4\}&J_5&\{5\}&\{0\}
\end{array}
\tag{119.8}
$$

Then $\mathcal F_N(a,\varepsilon)\ne\varnothing$ if and only
if this system has a solution. Further,
$\mathcal F_N(a,\varepsilon)\cap\mathscr C_5\ne\varnothing$
if and only if this same system has a solution additionally
satisfying

$$
T_{ij}^{00}=T_{ij}^{01}\quad\text{for every }i<j.
\tag{119.9}
$$

These are existential conditions for a whole replacement kernel,
rather than a requirement to preserve a given preselected law.
They leave 96 preselected terminal-mass coordinates, or 56 stopped
terminal-mass coordinates after identifying (119.9), together with
ten shared schedule weights in either system.

**Proof.** Any feasible finite preselected kernel has a common
representation as in Definition 108.1. Theorem 119.2 at
$\sigma=0$ removes all empty, singleton and repeated-coordinate
schedules up to seed-null sets. Reorder each remaining pair
increasingly, which preserves its acquired static information.
Every positive-mass cell must use a maximizing label. Integrating
the deterministic tables on each pair event gives (119.7), with
all four columns having its common schedule mass. The maximizing
sets are obtained by evaluating (117.5) with the eleven explicit
rows (119.1): for $j<5$ their maxima are $2,1,3,3$, and for
$j=5$ they are $3,0,3,3$. Label zero together with $i$ attains
the $00$ maximum; in $01$ the winning labels are
$\{0,\ldots,i\}$ if $j<5$, and all of $J_5$ if $j=5$.
In $10$ the winners are just $j$ if $j<5$, or
$\{i+1,\ldots,5\}$ if $j=5$; in $11$ they are
$\{0,j+1,\ldots,5\}$. This gives every row of (119.8).
The counts follow by summing their set sizes.

Conversely (119.7) makes every $p_b$ a probability vector.
A single uniform seed selects a pair interval of length $w_{ij}$;
its rescaled value specifies each of the four cell labels by
predeclared partitions with masses $T_{ij}^{uv}/w_{ij}$.
Zero intervals are omitted. The resulting common deterministic
tables acquire both scheduled replies and realize all $p_b$.
Every retained TV row then gives cap feasibility. The winner
supports imply score nine, but do not replace any of those rows.

For stopped feasibility, Theorem 109.1 identifies $\mathscr C_5$
with $\mathscr O_5$. Apply the same equality argument to a stopped
representation: its first-zero vector is used in both $00,01$,
which gives (119.9). Its support must lie in
$W_{ij}^{00}\cap W_{ij}^{01}=\{0,i\}$. Conversely (119.9)
merges these two vectors into precisely that stopped cell, so
the same seed realization stops at its first queried zero or
exhaustion. The other two supports remain those in (119.8).
The $01$ cells of pairs ending at five carry no certificate
weight, and all labels remain permitted there for a preselected
kernel; their full-word TV constraints still apply.

Theorem 110.2 relates both existence statements to the original
classes at this exact closed cap. For original competitors the
support and schedule conclusions concern a finite representative,
not the original competitor's law, addresses or tapes. Conversely
the finite witnesses give original measurable marks and a finite
handoff at every source and seed. Completing a stopped schedule
gives the same-seed preselected law with both actual requests
counted. Theorem 119.2 at $\sigma=0$, applied to the all-positive
event row, forces $p_{11111}(0)=1-\varepsilon$. At every actual
first absence $n>5$, monotonicity gives $a_n\le\varepsilon$,
so (110.9) gives

$$
\max\{1-p_{11111}(0),a_n\}=\varepsilon.
\tag{119.10}
$$

All original positive tail amplitudes, $a_6=\varepsilon$, zero
schedule masses and closed equalities are included. Every original
rule realized from a finite face witness has tail error exactly
$\varepsilon$ at every actual first absence $n>5$.
$\square$

**Corollary 119.4 (Coefficient saturation for stopped equality-face
witnesses).** Under (119.6), every feasible stopped finite kernel
has $c=H$ and $\beta=1$.

**Proof.** Choose its representation supplied by Theorem 119.3.
There is no empty or singleton mass, and
$W_{ij}^{10}\cap W_{ij}^{11}=\varnothing$ for every pair.
Therefore $v_{ij}=u_{ij}^{10}$, $V_i=B_i$, $h_i=A_i$ and
$c=\sum_iA_i=H$ by (109.4)--(109.5). Its coordinate mass is
$\mathfrak m(H)=\sum_{i<j}w_{ij}=1$, so (108.4) gives
$\beta=1$. This is a property of the specified equality face,
not a condition imposed on all stopped kernels. $\square$

## 120. The remaining projected inclusion

**Definition 120.1 (Five-active replacement projections).** Let
$\Delta_5$ be the set of amplitude-cap tuples
$(a_1,\ldots,a_5,\varepsilon)$ satisfying the head order,
strict active inequalities and equality $\sigma=0$ in (119.6).
Let $\mathcal P_N$ be its subset for which the full system
(119.7)--(119.8), including all 32 word laws and their separate
TV rows, has a solution. Let $\mathcal P_O$ be the subset for
which it has a solution also satisfying (119.9). Any tuple can
be extended by an original positive nonincreasing vanishing tail
with $a_6\le\varepsilon$; Theorem 110.2 retains every such tail
without altering these feasibility predicates.

The unresolved face question is

$$
\mathcal P_N\subseteq\mathcal P_O.
\tag{120.1}
$$

The converse containment is supplied by Proposition 90.2. The
family of Theorem 118.1 lies in $\mathcal P_O$ by (118.14),
including strictly unequal late amplitudes. Neither its parameter
patch nor the support reduction establishes (120.1). The latter
exposes the remaining simultaneous compatibility: a replacement
must obey common pair weights, every word's three TV rows and
the identification of the two first-zero cells, including the
unscored $01$ cells ending at five. Saturated coefficients of
stopped witnesses do not produce such a witness from the
necessary scalar bound alone.

The universal implication (110.14) remains unresolved. Even a
proof of (120.1) would settle only this equality face; its other
five-active profiles with $\sigma>0$, other head ranges, and
six or larger active lengths are outside that conclusion. No
uniform all-original-stopped lower certificate excluding a
cap-feasible preselected attainer is furnished by these results.
The full-face question concerns existence of a different stopped
law, not exact-law preservation in Theorem 112.2.

All original-source conclusions use the actual countable source,
static answers, zero advice, one common seed and the hard count
of at most two actual requests from Definition 90.1. The explicit
attainers hand off original atomic marks; their distance from
each unchanged nonatomic original target is one by Acquisition
Resources, Theorem 82.1, and the unchanged consumer returns
unknown on those marks. The selected marked-law comparison
therefore retains the original carrier, consumer and targets.
Finite support and low addresses belong to constructed witnesses;
original competitors keep the arbitrary addresses and full carrier
allowed by Theorem 110.2. No runtime, mean-request count or
source distribution replaces that contract. Caps above one admit
immediate base output; zero cap is outside the positive-cap
replacement question. These are ordinary theoretical results
under the cited ordinary suppliers, without kernel certification
or a claim of exhaustive novelty.

## 追加锚（本行以下为增补区）

## 121. Complete replacement on the sharp five-active face

**Definition 121.1 (The face and its original acquisition contract).**
Retain Definition 110.1, the original source (110.1), the full
measurable tape carrier, the distinct original marks $\theta_r$,
and the separately selected laws (110.3). The consumer and the
original nonatomic targets are unchanged. Let the entire prescribed
amplitude sequence satisfy

$$
1\ge a_1\ge a_2\ge\cdots>0,\qquad a_n\longrightarrow0,
\qquad a_5>\varepsilon>0,\qquad a_6\le\varepsilon.
\tag{121.1}
$$

Assume the second-head equality face

$$
18\varepsilon=2a_2+3(a_3+a_4+a_5)-2,
\qquad \delta=1-a_2.
\tag{121.2}
$$

The active length is exactly five. Acquisitions are precisely
$\mathcal N_2,\mathcal O_2$ of Acquisition Resources, Definition
90.1: zero advice, one source-independent common seed, static
prime answers, sourcewise almost-sure finite handoff, and a hard
count of at most two actual requests, including repetitions.
Original competitors retain arbitrary addresses and arbitrary
outputs on the full original carrier. There is no probability
law on the source set and no additional observation of its label,
its integer $N(x)$ or its first absence. In particular, neither
mean count, address size nor transition time replaces actual count.

Use $J_5=\{0,\ldots,5\}$, $B_5=\{0,1\}^5$, the cap slice
$\mathcal F_N(a,\varepsilon)$ and coefficient region $\mathscr C_5$
of Sections 108--110. For a zero-containing word $b$, write
$n(b)=\min\{i:b_i=0\}$ and
$\eta_b=(1-a_{n(b)})e_0+a_{n(b)}e_{n(b)}$; set
$\eta_{11111}=e_0$. Every zero pattern is included.

**Theorem 121.2 (Full sharp-five-face classification).** Under
(121.1)--(121.2), the following four assertions are equivalent:

$$
\begin{aligned}
&\exists N\in\mathcal N_2:\ e_a(N)\le\varepsilon;\\
&\exists O\in\mathcal O_2:\ e_a(O)\le\varepsilon;\\
&\mathcal F_N(a,\varepsilon)\cap\mathscr C_5\ne\varnothing;\\
&a_1-a_2\le\frac\delta3,\quad
 a_3\ge\varepsilon+\frac{4\delta}3,\quad
 a_4\ge\varepsilon+\delta,\quad
 a_5\ge\varepsilon+\frac\delta3.
\end{aligned}
\tag{121.3}
$$

Whenever these conditions hold, there are original $O,N$ using
the same source-independent seed and having the same selected
output law at every source, with uniform error exactly
$\varepsilon$. The constructed $O$ actually makes one or two
requests, and the constructed $N$ actually makes two. Both hand
off finitely for every source and seed. Every prescribed positive
nonincreasing vanishing tail with $a_6\le\varepsilon$, including
$a_6=\varepsilon$, is retained. No equality among $a_3,a_4,a_5$
is assumed. Replacement concerns existence of a whole different
law at the same cap, rather than preservation of a given $N$ law.

**Proof.** Theorem 110.2 reduces an arbitrary original cap-feasible
$N$ to one common finite kernel in $\mathcal F_N$ on all 32
words, without imposing bounded addresses or mark support on
that competitor. Theorem 113.2 supplies the first cut in (121.3);
the three unrestricted finite-$N$ certificates of Section 122
supply the other cuts. Sections 123--126 construct a stopped
kernel for every real profile satisfying the cuts. Its all-word
cap and its membership in $\mathscr C_5$ follow there from
explicit cone coverage, jointly normalized endpoint laws and
the reused coefficient criterion 109.1. Theorem 110.2 realizes
that kernel on the original source; Section 127 gives the same
seed, actual counts, finite handoff and exact retained-tail error.
Conversely an original $O$ gives an original $N$ by Acquisition
Resources, Proposition 90.2, completing its entire schedule and
counting even ignored replies. Membership in the intersection
also gives an original $O$ by 110.2. This proves every direction.
$\square$

Theorem 117.2 supplies the second-head supporting inequality;
Theorems 118.1 and 119.3 supply, respectively, an earlier attained
parameter family and an exact finite system on this face.
Theorem 121.2 resolves the whole projected inclusion (120.1),
rather than just that parameter family. Its additional necessity
and its complete constructive projection are given below.

## 122. Three unrestricted preselected weighted-event certificates

**Definition 122.1 (Literal event data).** A row $(b,E,m)$ assigns
weight $m$ to $p_b(E)$, with $E\subseteq J_5$ a label event.
For $k=3,4,5$, let $S_k(p)$ be the sum over the following
respective tables. Distinct events at the same word remain
distinct rows; in particular $\{0,n\}$ is one union event.

| Certificate | Word $b$ | Event $E$ | Weight $m$ |
| --- | --- | --- | --- |
| C3 | 00100 | {0,1} | 1 |
| C3 | 00110 | {0,1} | 1 |
| C3 | 01000 | {0,1} | 1 |
| C3 | 01010 | {0,1} | 1 |
| C3 | 01100 | {0,1} | 1 |
| C3 | 10000 | {0,2} | 1 |
| C3 | 10010 | {0,2} | 1 |
| C3 | 10100 | {2} | 1 |
| C3 | 10100 | {0,2} | 1 |
| C3 | 10110 | {2} | 1 |
| C3 | 11000 | {3} | 2 |
| C3 | 11000 | {0,3} | 1 |
| C3 | 11010 | {3} | 2 |
| C3 | 11100 | {4} | 5 |
| C3 | 11110 | {5} | 5 |
| C3 | 11111 | {0} | 4 |
| C4 | 00100 | {0,1} | 3 |
| C4 | 00110 | {0,1} | 1 |
| C4 | 01000 | {0,1} | 2 |
| C4 | 01001 | {0,1} | 1 |
| C4 | 01010 | {0,1} | 2 |
| C4 | 10000 | {0,2} | 2 |
| C4 | 10001 | {0,2} | 1 |
| C4 | 10010 | {0,2} | 2 |
| C4 | 10100 | {2} | 3 |
| C4 | 10110 | {2} | 1 |
| C4 | 11000 | {3} | 5 |
| C4 | 11010 | {3} | 2 |
| C4 | 11011 | {3} | 2 |
| C4 | 11100 | {4} | 7 |
| C4 | 11100 | {0,4} | 1 |
| C4 | 11110 | {5} | 9 |
| C4 | 11111 | {0} | 8 |
| C5 | 00100 | {0,1} | 2 |
| C5 | 01000 | {0,1} | 1 |
| C5 | 01001 | {0,1} | 1 |
| C5 | 10000 | {0,2} | 1 |
| C5 | 10001 | {0,2} | 1 |
| C5 | 10100 | {2} | 1 |
| C5 | 10101 | {2} | 1 |
| C5 | 11000 | {3} | 2 |
| C5 | 11001 | {3} | 2 |
| C5 | 11100 | {4} | 2 |
| C5 | 11101 | {4} | 2 |
| C5 | 11110 | {5} | 2 |
| C5 | 11111 | {0} | 4 |

**Theorem 122.2 (All-schedule bounds and the four necessary cuts).**
For every finite preselected two-request kernel on $B_5$,

$$
S_3(p)\le15,\qquad S_4(p)\le27,\qquad S_5(p)\le12.
\tag{122.1}
$$

If it is cap feasible on every word, then

$$
\begin{aligned}
29\varepsilon&\ge2a_2+4a_3+5a_4+5a_5-2,\\
52\varepsilon&\ge4a_2+9a_3+7a_4+9a_5-4,\\
22\varepsilon&\ge2a_2+4a_3+4a_4+2a_5-2.
\end{aligned}
\tag{122.2}
$$

Together with the accepted residual bound 113.2, these imply all
four cuts of (121.3) on the face (121.2), for every original
$\mathcal N_2$ competitor and hence every original
$\mathcal O_2$ competitor.

**Proof.** Fix one seed of a finite preselected rule. It determines
one schedule and a label constant on each of its acquired cells.
For a distinct pair $i<j$, the exact maximum contribution of
cell $uv$ to certificate $C_k$ is

$$
M_{k,ij}^{uv}=\max_{r\in J_5}
 \sum_{(b,E,m)\in C_k:\ (b_i,b_j)=(u,v)}
                        m\mathbf1_{r\in E}.
\tag{122.3}
$$

This is a finite maximum of six explicit integer sums. Reading
Definition 122.1 gives the following complete table, with each
quadruple ordered as $00,01,10,11$:

| Pair $(i,j)$ | C3 cell maxima | C4 cell maxima | C5 cell maxima |
| --- | --- | --- | --- |
| (1,2) | (2,3,5,5) | (4,5,9,9) | (2,2,4,4) |
| (1,3) | (2,3,5,5) | (5,4,9,9) | (2,2,4,4) |
| (1,4) | (3,2,5,5) | (6,3,8,10) | (4,0,4,4) |
| (1,5) | (5,0,5,4) | (8,1,9,9) | (3,1,2,5) |
| (2,3) | (2,3,5,5) | (5,4,9,9) | (2,2,4,4) |
| (2,4) | (3,2,5,5) | (6,3,8,10) | (4,0,4,4) |
| (2,5) | (5,0,5,4) | (8,1,9,9) | (3,2,2,5) |
| (3,4) | (3,2,5,5) | (6,4,8,9) | (4,0,4,4) |
| (3,5) | (5,0,5,4) | (8,2,9,8) | (2,2,2,4) |
| (4,5) | (6,0,5,4) | (8,2,9,8) | (4,2,2,4) |

For example, in $C_3$ at pair $(4,5)$, cell $00$ has
label-zero weight six from the union rows at $00100,01000,01100$,
$10000,10100,11000$; its maximum is six. Cell $01$ has no rows,
cell $10$ has label-five weight five from $11110$, and cell
$11$ has label-zero weight four. The resulting
sum is fifteen. Formula (122.3) verifies every other entry by
the same six-label finite sums, without any terminal-support
restriction. The sums of the quadruples are at most $15,27,12$.

For the empty schedule the exact maxima are $13,23,10$.
For each singleton coordinate $i=1,\ldots,5$, summing its two
cell maxima again gives $13,23,10$, respectively. A repeated
pair $(i,i)$ has just those singleton cells because replies are
static. Reversing a distinct pair only interchanges $01,10$.
Thus this table and the short-schedule values cover all
$1+5+25=31$ ordered schedules of length at most two. An output
label outside the event sets scores zero. Integrating under the
one seed distribution proves (122.1); the proof never chooses
a separate output label or seed distribution for each source.

For a cap-feasible kernel, TV gives
$p_b(E)\ge\eta_b(E)-\varepsilon$ for each literal row. The
three total event weights and exact target scores are

$$
\begin{array}{c|c|l}
 &\sum m&\sum m\eta_b(E)\\\hline
C_3&29&13+2a_2+4a_3+5a_4+5a_5\\
C_4&52&23+4a_2+9a_3+7a_4+9a_5\\
C_5&22&10+2a_2+4a_3+4a_4+2a_5
\end{array}
\tag{122.4}
$$

Subtracting the event-weight times $\varepsilon$ and applying
(122.1) yields (122.2). Union rows retain their own TV constraint;
coincident words have not been collapsed.

Put $S=a_3+a_4+a_5$. Equation (121.2) is
$S=6\varepsilon+2\delta/3$. Theorem 113.2 gives
$S-3\varepsilon\le3\varepsilon+1-a_1$, and therefore
$a_1-a_2\le\delta/3$. The score slacks on this face are exactly

$$
\begin{aligned}
29\varepsilon-[2a_2+4a_3+5a_4+5a_5-2]
 &=a_3-\varepsilon-4\delta/3,\\
52\varepsilon-[4a_2+9a_3+7a_4+9a_5-4]
 &=2(a_4-\varepsilon-\delta),\\
22\varepsilon-[2a_2+4a_3+4a_4+2a_5-2]
 &=2(a_5-\varepsilon-\delta/3).
\end{aligned}
\tag{122.5}
$$

Equivalently the three inequalities become
$15a_3-3a_4-3a_5\ge22\delta$,
$15a_4-3a_3-3a_5\ge16\delta$, and
$15a_5-3a_3-3a_4\ge4\delta$.
These are precisely the remaining cuts. For an original competitor
use Theorem 110.2 at active length five first: projection,
common-seed truncation and compactness supply one representative
at the exact closed cap. We reuse that transport, including its
full-carrier and arbitrary-address scope; the finite certificate
does not restrict the original schedule to these ten pairs.
$\square$

## 123. Complete continuous cone coverage

**Definition 123.1 (Amplitude coordinates).** On the face put

$$
h=a_1-a_2,\quad x=a_3-a_4,\quad y=a_4-a_5,
\quad z=3a_5-x-2y-4\delta/3,
\quad g=z+4x+5y+13\delta/3.
\tag{123.1}
$$

The affine inverse is

$$
\begin{aligned}
a_2&=1-\delta,&a_1&=1-\delta+h,\\
a_5&=(z+x+2y+4\delta/3)/3,&a_4&=a_5+y,
 &a_3&=a_5+y+x,\\
\varepsilon&=z/6+x/3+2y/3+\delta/9.
\end{aligned}
\tag{123.2}
$$

**Theorem 123.2 (Coordinates and constructive cone decomposition).**
In the closed ambient domain
$1\ge a_1\ge a_2\ge a_3\ge a_4\ge a_5\ge\varepsilon\ge0$
with (121.2), the four cuts (121.3) are equivalent to

$$
\begin{gathered}
\delta,x,y,z\ge0,\qquad 0\le h\le\delta/3,\\
z+6y\ge4\delta,\qquad z+6x+6y\ge6\delta,
\qquad g\le3.
\end{gathered}
\tag{123.3}
$$

The homogeneous cone in $(\delta,x,y,z)$ before the final
normalization $g\le3$ is generated by

$$
A=(1,0,0,6),\quad B=(1,0,1,0),\quad
C=(1,1/3,0,4),\quad D=(1,1/3,2/3,0)
\tag{123.4}
$$

and the three coordinate axes at $\delta=0$. Every point has
a nonnegative decomposition

$$
(\delta,x,y,z)=q_AA+q_BB+q_CC+q_DD+(0,x_0,y_0,z_0)
\tag{123.5}
$$

given by the two branches below. This covers all real cone points.

**Proof.** Direct substitution gives

$$
\begin{aligned}
a_3-\varepsilon-4\delta/3&=(z+6x+6y-6\delta)/6,\\
a_4-\varepsilon-\delta&=(z+6y-4\delta)/6,\\
a_5-\varepsilon-\delta/3&=z/6,\\
a_5-\varepsilon&=z/6+\delta/3,\\
g&=3(a_3+\delta).
\end{aligned}
\tag{123.6}
$$

The ambient order gives $x,y,\delta\ge0$ and $h\ge0$;
its $a_3\le a_2$ is precisely $g\le3$. The cuts give the
other inequalities. Conversely (123.3) and (123.2) imply all
cuts, $a_5\ge\varepsilon\ge0$, the late order, and
$a_3\le a_2$. Also $a_1\le1$ follows from
$h\le\delta/3\le\delta$. Thus both normalization and order
are recovered; the four cuts alone without the ambient domain
are not the asserted region.

If $z+6y\ge6\delta$, set

$$
\begin{gathered}
q_A=\min\{\delta,z/6\},\quad q_B=\delta-q_A,
\quad q_C=q_D=0,\\
x_0=x,\qquad y_0=y-q_B,\qquad z_0=z-6q_A.
\end{gathered}
\tag{123.7}
$$

When $z\ge6\delta$, $q_B=0$ and $z_0\ge0$.
When $z<6\delta$, $q_B=\delta-z/6$, $z_0=0$, and
this branch inequality gives $y\ge q_B$. Every coefficient is
nonnegative in both cases, including $\delta=0$.

If $z+6y<6\delta$, put

$$
\begin{gathered}
f=3\delta-3y-z/2>0,\qquad
q_D=\max\{0,3(f+y-\delta)/2\},\\
q_C=f-q_D,\qquad q_B=y-2q_D/3,\qquad
q_A=\delta-q_B-f,\\
x_0=x-f/3,\qquad y_0=z_0=0.
\end{gathered}
\tag{123.8}
$$

The two cone inequalities give $f\le\delta$ and $f/3\le x$.
Hence $q_D\le3y/2$. Moreover
$f+3y=3\delta-z/2\le3\delta$ implies $q_D\le f$.
Therefore $q_B,q_C,x_0\ge0$. If $q_D=0$, its defining
inequality gives $\delta-y-f\ge0$, so $q_A\ge0$.
If $q_D>0$, substituting its value gives $q_A=0$.
All coefficients are again nonnegative.

In either branch the exact identities are

$$
\begin{aligned}
q_A+q_B+q_C+q_D&=\delta,\\
x&=(q_C+q_D)/3+x_0,\\
y&=q_B+2q_D/3+y_0,\\
z&=6q_A+4q_C+z_0.
\end{aligned}
\tag{123.9}
$$

For the second branch the last identity follows from
$6q_A+4q_C=6\delta-6y-2f=z$. Thus (123.5) holds
throughout the cone, including its boundaries. Equality
$z+6y=6\delta$ belongs to (123.7), so the second branch
never needs $f=0$.

For completeness these are its extreme rays. At $\delta=0$
nonnegativity makes the three axes extreme. At positive $\delta$,
ray $A$ has $x=y=0$ and $z+6x+6y=6\delta$; ray $B$
has $x=z=0$ and the same equality; ray $C$ has $y=0$
and both cone equalities; ray $D$ has $z=0$ and both
cone equalities. In each case these are three independent active
homogeneous constraints, leaving a single ray. The constructive
representation excludes any further extreme ray. No sampled hull
or numerical optimization is used in this coverage argument.
$\square$

## 124. Twelve jointly normalized stopped endpoint laws

**Definition 124.1 (Auxiliary finite profiles).** The coordinate
origin gives $V_0$; normalizing the three axes by $g=3$ gives
$V_x,V_y,V_z$ with axis coordinates $3/4,3/5,3$, respectively.
Normalizing $A,B,C,D$ by $g=3$ gives respective
$\delta_R=9/31,9/28,9/29,1/3$. For each ray use the two
head endpoints $h=0$ and $h=\delta_R/3$, denoted $V_{R0},V_{R1}$.
Their full profiles are as follows; $d_V$ is the denominator
of the integer terminal vectors in Definition 124.2.

| Profile | $a_1$ | $a_2$ | $a_3$ | $a_4$ | $a_5$ | $\varepsilon$ | $d_V$ |
| --- | --- | --- | --- | --- | --- | --- | --- |
| V0 | 1 | 1 | 0 | 0 | 0 | 0 | 1 |
| Vx | 1 | 1 | 1 | 1/4 | 1/4 | 1/4 | 4 |
| Vy | 1 | 1 | 1 | 1 | 2/5 | 2/5 | 5 |
| Vz | 1 | 1 | 1 | 1 | 1 | 1/2 | 4 |
| VA0 | 22/31 | 22/31 | 22/31 | 22/31 | 22/31 | 10/31 | 31 |
| VA1 | 25/31 | 22/31 | 22/31 | 22/31 | 22/31 | 10/31 | 31 |
| VB0 | 19/28 | 19/28 | 19/28 | 19/28 | 5/14 | 1/4 | 28 |
| VB1 | 11/14 | 19/28 | 19/28 | 19/28 | 5/14 | 1/4 | 28 |
| VC0 | 20/29 | 20/29 | 20/29 | 17/29 | 17/29 | 8/29 | 29 |
| VC1 | 23/29 | 20/29 | 20/29 | 17/29 | 17/29 | 8/29 | 29 |
| VD0 | 2/3 | 2/3 | 2/3 | 5/9 | 1/3 | 2/9 | 9 |
| VD1 | 7/9 | 2/3 | 2/3 | 5/9 | 1/3 | 2/9 | 9 |

These are auxiliary targets on the fixed finite 32-word carrier.
$V_0$ has zero cap and zero late amplitudes; $V_x,V_y$ have
$a_5=\varepsilon$. They are not original positive infinite
sources. The original-source theorem is applied only to a final
profile satisfying (121.1), with its prescribed entire tail.

**Definition 124.2 (Complete integer terminal tables).** For each
profile and increasing pair $(i,j)$ the following three integer
vectors $U^0,U^{10},U^{11}$ define
$T_{ij}^{\tau}=U_{ij}^{\tau}/d_V$. The first vector is used for
both acquired cells $00,01$. Each column has the same coordinate
mass, so it defines one pair weight
$w_{ij}=\mathfrak m(U_{ij}^0)/d_V$, counted once. Every omitted
pair has zero weight. Entries use the output unit vectors $e_r$,
not input bits.

| Profile | Pair $(i,j)$ | $U^0$ | $U^{10}$ | $U^{11}$ |
| --- | --- | --- | --- | --- |
| V0 | (1,2) | $e_1$ | $e_2$ | $e_0$ |
| Vx | (1,2) | $2e_1$ | $2e_2$ | $e_0+e_3$ |
| Vx | (1,3) | $e_1$ | $e_3$ | $e_0$ |
| Vx | (2,3) | $e_2$ | $e_3$ | $e_0$ |
| Vy | (1,2) | $e_1$ | $e_2$ | $e_4$ |
| Vy | (1,3) | $2e_1$ | $2e_3$ | $e_0+e_4$ |
| Vy | (2,3) | $e_2$ | $e_3$ | $e_0$ |
| Vy | (2,4) | $e_2$ | $e_4$ | $e_0$ |
| Vz | (1,2) | $e_1$ | $e_2$ | $e_5$ |
| Vz | (1,3) | $e_1$ | $e_3$ | $e_4$ |
| Vz | (2,3) | $e_2$ | $e_3$ | $e_0$ |
| Vz | (4,5) | $e_4$ | $e_5$ | $e_0$ |
| VA0 | (1,2) | $5e_1$ | $5e_2$ | $3e_0+e_3+e_5$ |
| VA0 | (1,3) | $4e_1$ | $4e_3$ | $3e_0+e_5$ |
| VA0 | (1,4) | $3e_0+3e_1$ | $6e_4$ | $3e_0+3e_5$ |
| VA0 | (2,3) | $3e_0+4e_2$ | $7e_3$ | $3e_0+4e_5$ |
| VA0 | (2,4) | $3e_2$ | $3e_4$ | $3e_0$ |
| VA0 | (3,4) | $3e_0$ | $3e_4$ | $3e_0$ |
| VA0 | (4,5) | $3e_0$ | $3e_5$ | $3e_0$ |
| VA1 | (1,2) | $5e_1$ | $5e_2$ | $3e_0+e_3+e_5$ |
| VA1 | (1,3) | $4e_1$ | $4e_3$ | $3e_0+e_5$ |
| VA1 | (1,4) | $6e_1$ | $6e_4$ | $3e_0+3e_5$ |
| VA1 | (2,3) | $7e_2$ | $7e_3$ | $3e_0+4e_5$ |
| VA1 | (2,4) | $3e_0$ | $3e_4$ | $3e_0$ |
| VA1 | (3,4) | $3e_0$ | $3e_4$ | $3e_0$ |
| VA1 | (4,5) | $3e_0$ | $3e_5$ | $3e_0$ |
| VB0 | (1,2) | $3e_0+5e_1$ | $8e_2$ | $3e_0+4e_3+e_4$ |
| VB0 | (1,3) | $4e_1$ | $4e_3$ | $3e_0+e_4$ |
| VB0 | (1,4) | $3e_1$ | $3e_4$ | $3e_0$ |
| VB0 | (2,3) | $4e_2$ | $4e_3$ | $3e_0+e_4$ |
| VB0 | (2,4) | $3e_0$ | $3e_4$ | $3e_0$ |
| VB0 | (3,4) | $3e_0$ | $3e_4$ | $3e_0$ |
| VB0 | (4,5) | $3e_0$ | $3e_5$ | $3e_0$ |
| VB1 | (1,2) | $8e_1$ | $8e_2$ | $3e_0+4e_3+e_4$ |
| VB1 | (1,3) | $4e_1$ | $4e_3$ | $3e_0+e_4$ |
| VB1 | (1,4) | $3e_1$ | $3e_4$ | $3e_0$ |
| VB1 | (2,3) | $3e_0+e_2$ | $4e_3$ | $3e_0+e_4$ |
| VB1 | (2,4) | $3e_2$ | $3e_4$ | $3e_0$ |
| VB1 | (3,4) | $3e_0$ | $3e_4$ | $3e_0$ |
| VB1 | (4,5) | $3e_0$ | $3e_5$ | $3e_0$ |
| VC0 | (1,2) | $3e_0+4e_1$ | $7e_2$ | $3e_0+2e_3+2e_5$ |
| VC0 | (1,3) | $5e_1$ | $5e_3$ | $3e_0+2e_5$ |
| VC0 | (1,4) | $3e_1$ | $3e_4$ | $3e_0$ |
| VC0 | (2,3) | $5e_2$ | $5e_3$ | $3e_0+2e_5$ |
| VC0 | (2,4) | $3e_0$ | $3e_4$ | $3e_0$ |
| VC0 | (3,4) | $3e_0$ | $3e_4$ | $3e_0$ |
| VC0 | (4,5) | $3e_0$ | $3e_5$ | $3e_0$ |
| VC1 | (1,2) | $7e_1$ | $7e_2$ | $3e_0+2e_3+2e_5$ |
| VC1 | (1,3) | $5e_1$ | $5e_3$ | $3e_0+2e_5$ |
| VC1 | (1,4) | $3e_1$ | $3e_4$ | $3e_0$ |
| VC1 | (2,3) | $3e_0+2e_2$ | $5e_3$ | $3e_0+2e_5$ |
| VC1 | (2,4) | $3e_2$ | $3e_4$ | $3e_0$ |
| VC1 | (3,4) | $3e_0$ | $3e_4$ | $3e_0$ |
| VC1 | (4,5) | $3e_0$ | $3e_5$ | $3e_0$ |
| VD0 | (1,2) | $e_0+2e_1$ | $3e_2$ | $e_0+2e_3$ |
| VD0 | (1,3) | $e_1$ | $e_3$ | $e_0$ |
| VD0 | (1,4) | $e_1$ | $e_4$ | $e_0$ |
| VD0 | (2,3) | $e_2$ | $e_3$ | $e_0$ |
| VD0 | (2,4) | $e_0$ | $e_4$ | $e_0$ |
| VD0 | (3,4) | $e_0$ | $e_4$ | $e_0$ |
| VD0 | (4,5) | $e_0$ | $e_5$ | $e_0$ |
| VD1 | (1,2) | $3e_1$ | $3e_2$ | $e_0+2e_3$ |
| VD1 | (1,3) | $e_1$ | $e_3$ | $e_0$ |
| VD1 | (1,4) | $e_1$ | $e_4$ | $e_0$ |
| VD1 | (2,3) | $e_0$ | $e_3$ | $e_0$ |
| VD1 | (2,4) | $e_2$ | $e_4$ | $e_0$ |
| VD1 | (3,4) | $e_0$ | $e_4$ | $e_0$ |
| VD1 | (4,5) | $e_0$ | $e_5$ | $e_0$ |

The endpoint word law is, literally,

$$
p_b^V=\frac1{d_V}\sum_{i<j}
 \big[(1-b_i)U_{ij}^0+b_i(1-b_j)U_{ij}^{10}
                         +b_i b_jU_{ij}^{11}\big].
\tag{124.1}
$$

Each term chooses exactly one column. The common column masses
sum to $d_V$ at each profile; hence every word law is a
probability vector. This is a single shared schedule budget,
not separately normalized choices for individual inputs or labels.

## 125. Every endpoint word and every independent TV row

**Theorem 125.1 (Complete finite endpoint certificate).** Each law
of Definition 124.2 satisfies the cap at every one of the 32
words, with the amplitudes and cap of its own auxiliary profile.
Its all-positive base mass is exactly $1-\varepsilon_V$.

**Proof.** For first-zero class $n$ define the three separate minima

$$
\begin{aligned}
B_{V,n}&=\min_{b=1^{n-1}0s}p_b^V(0),\\
C_{V,n}&=\min_{b=1^{n-1}0s}p_b^V(n),\\
P_{V,n}&=\min_{b=1^{n-1}0s}[p_b^V(0)+p_b^V(n)],
\qquad s\in\{0,1\}^{5-n}.
\end{aligned}
\tag{125.1}
$$

The suffixes have sizes $16,8,4,2,1$ for $n=1,2,3,4,5$.
Evaluating the integer sum (124.1) over each entire class gives
the following triples $(B_{V,n},C_{V,n},P_{V,n})$:

| Profile | $n=1$ | $n=2$ | $n=3$ | $n=4$ | $n=5$ |
| --- | --- | --- | --- | --- | --- |
| V0 | (0,1,1) | (0,1,1) | (1,0,1) | (1,0,1) | (1,0,1) |
| Vx | (0,3/4,3/4) | (0,3/4,3/4) | (1/4,3/4,1) | (3/4,0,3/4) | (3/4,0,3/4) |
| Vy | (0,3/5,3/5) | (0,3/5,3/5) | (0,3/5,3/5) | (2/5,3/5,1) | (3/5,0,3/5) |
| Vz | (0,1/2,1/2) | (0,1/2,1/2) | (0,1/2,1/2) | (1/4,1/2,3/4) | (1/4,1/2,3/4) |
| VA0 | (9/31,12/31,21/31) | (9/31,12/31,21/31) | (9/31,12/31,21/31) | (12/31,12/31,24/31) | (18/31,12/31,30/31) |
| VA1 | (6/31,15/31,21/31) | (9/31,12/31,21/31) | (9/31,12/31,21/31) | (12/31,12/31,24/31) | (18/31,12/31,30/31) |
| VB0 | (9/28,3/7,3/4) | (9/28,3/7,3/4) | (9/28,3/7,3/4) | (3/7,3/7,6/7) | (9/14,3/28,3/4) |
| VB1 | (3/14,15/28,3/4) | (9/28,3/7,3/4) | (9/28,3/7,3/4) | (3/7,3/7,6/7) | (9/14,3/28,3/4) |
| VC0 | (9/29,12/29,21/29) | (9/29,12/29,21/29) | (9/29,12/29,21/29) | (12/29,9/29,21/29) | (18/29,9/29,27/29) |
| VC1 | (6/29,15/29,21/29) | (9/29,12/29,21/29) | (9/29,12/29,21/29) | (12/29,9/29,21/29) | (18/29,9/29,27/29) |
| VD0 | (1/3,4/9,7/9) | (1/3,4/9,7/9) | (1/3,4/9,7/9) | (4/9,1/3,7/9) | (2/3,1/9,7/9) |
| VD1 | (2/9,5/9,7/9) | (1/3,4/9,7/9) | (1/3,4/9,7/9) | (4/9,1/3,7/9) | (2/3,1/9,7/9) |

For example, at $V_{D0}$ and a word whose first zero is four,
the leading bits are $111$. The first-zero column of pair
$(4,5)$ contributes $e_0/9$. Pairs $(1,4),(2,4),(3,4)$
contribute $3e_4/9$ through their $10$ columns; pairs
$(1,2),(1,3),(2,3)$ contribute $(3e_0+2e_3)/9$ through
$11$. Thus both suffix choices have base mass $4/9$,
correct-label mass $1/3$ and pair mass $7/9$, as displayed.
The other entries are obtained from exactly the same explicit
sum for every suffix, including all multiple-zero words.

Every triple meets the three respective thresholds

$$
B_{V,n}\ge1-a_n^V-\varepsilon_V,\qquad
C_{V,n}\ge a_n^V-\varepsilon_V,\qquad
P_{V,n}\ge1-\varepsilon_V.
\tag{125.2}
$$

These are all $3\cdot31=93$ zero-word TV rows (110.6).
The third minimum is evaluated for the union event itself,
independently of the two singleton minima. It is never discarded
on the assumption that the first two bounds suffice. At $11111$
only the $11$ columns contribute. Their base sum, divided by
$d_V$, is respectively

$$
1,\quad 3/4,\quad 3/5,\quad 1/2,\quad
21/31,\quad21/31,\quad3/4,\quad3/4,\quad
21/29,\quad21/29,\quad7/9,\quad7/9
\tag{125.3}
$$

in the profile order of Definition 124.1. These are exactly
$1-\varepsilon_V$, giving the 94th row. The finite identity
behind (110.6) is also explicit: for a probability vector $p$
and target $(1-a)e_0+ae_n$, the possible positive deficits lie
only at labels $0,n$, so

$$
\operatorname{TV}(p,(1-a)e_0+ae_n)
 =\max\{0,1-a-p(0),a-p(n),1-p(0)-p(n)\}.
\tag{125.4}
$$

Hence all 94 rows are precisely sufficient as well as necessary.
Definitions 124.1--124.2 and (124.1), (125.1) give rational finite
proof data for every endpoint law: 384 word laws and 1,128
separate cap rows across the twelve profiles. Their finite
validity is used only at these endpoints; continuous coverage
comes from Section 123 and the affine argument below.
$\square$

## 126. Nonnegative normalization, head interpolation and saturation

**Theorem 126.1 (A stopped kernel at every real face profile).**
For every tuple in the closed ambient region of Theorem 123.2,
there are twelve nonnegative weights summing to one that recover
its entire amplitude-cap tuple from Definition 124.1. Mixing the
endpoint laws with those same weights gives a cap-feasible stopped
kernel on every word, with $p_{11111}(0)=1-\varepsilon$ and
$c=H$, $\beta=1$ in Definition 108.2.

**Proof.** Take the nonnegative conic coefficients in (123.7)
or (123.8). Define

$$
\begin{aligned}
\lambda_x&=4x_0/3,&\lambda_y&=5y_0/3,&\lambda_z&=z_0/3,\\
\lambda_A&=31q_A/9,&\lambda_B&=28q_B/9,
 &\lambda_C&=29q_C/9,&\lambda_D&=3q_D,\\
\lambda_0&=1-g/3.
\end{aligned}
\tag{126.1}
$$

The normalization factors are the reciprocals of the axis and
ray scales in Definition 124.1. In particular

$$
\lambda_x+\lambda_y+\lambda_z+
\lambda_A+\lambda_B+\lambda_C+\lambda_D=g/3\le1.
\tag{126.2}
$$

This follows by applying the linear functional $g$ to (123.5),
since each normalized nonorigin profile has $g=3$.
Thus all weights, including $\lambda_0$, are nonnegative.
For $\delta>0$ set $s=3h/\delta\in[0,1]$ and assign

$$
\lambda_{R0}=(1-s)\lambda_R,\qquad
\lambda_{R1}=s\lambda_R\qquad(R=A,B,C,D).
\tag{126.3}
$$

For $\delta=0$, (123.9) makes every $q_R$ zero and
$h=0$; set $s=0$. This defines all twelve weights without
division by zero. The ray contribution to $\delta$ is
$\lambda_R\delta_R=q_R$, so the head contribution is

$$
\sum_R\lambda_{R1}\delta_R/3
      =s\sum_Rq_R/3=h.
\tag{126.4}
$$

The other four coordinates are recovered by (123.9).
The affine inverse (123.2), and total weight one, therefore
recover all six entries $(a_1,a_2,a_3,a_4,a_5,\varepsilon)$.
Every closed equality is included directly: $g=3$ gives
$\lambda_0=0$, $h=0$ or $h=\delta/3$ selects a head
endpoint, and zero cone or schedule weights are omitted.

For each pair mix its three terminal vectors with these weights;
write the results $T_{ij}^0,T_{ij}^{10},T_{ij}^{11}$ and the
mixed common pair weight $w_{ij}$. They are nonnegative,
have the same mass within each pair and satisfy
$\sum_{i<j}w_{ij}=1$. The mixed kernel is

$$
p_b=\sum_{i<j}\big[(1-b_i)T_{ij}^0+
 b_i(1-b_j)T_{ij}^{10}+b_ib_jT_{ij}^{11}\big]
       =\sum_V\lambda_Vp_b^V.
\tag{126.5}
$$

Fix any zero word $b$ and its first zero $n$. The corresponding
endpoint targets all use that same label $n$, even if an auxiliary
endpoint amplitude is zero or equal to its cap. The affine
amplitude identity gives

$$
(1-a_n)e_0+a_ne_n
 =\sum_V\lambda_V[(1-a_n^V)e_0+a_n^Ve_n].
\tag{126.6}
$$

Each of the three rows (110.6) is affine in the law, amplitude
and cap. Taking the same weighted sum of its endpoint inequalities
proves it at this $b$. This is done separately for all 31 zero
words and all three rows, including the pair row. The all-positive
target remains $e_0$, and (125.3) yields
$p_{11111}(0)=\sum_V\lambda_V(1-\varepsilon_V)=1-\varepsilon$.
Hence all 94 inequalities hold simultaneously. These identities
prove the claim for every real parameter through the explicit
cone decomposition; finite endpoint checks alone would not do so.

For coefficient saturation, observe a support property common to
all twelve tables: at any fixed pair $(i,j)$ every $10$ vector
is supported only at label $j$, and every $11$ vector has zero
at label $j$. Omitted vectors are zero. This property persists
under the common convex mixture, so the two mixed supports are
still disjoint. Put

$$
A_i=\sum_{j>i}T_{ij}^0,\qquad
B_i=\sum_{j>i}T_{ij}^{10}.
\tag{126.7}
$$

Expanding (126.5) and using that disjointness gives

$$
\begin{aligned}
c&=\sum_iA_i,&\ell_i&=B_i-A_i,
 &Q_{ij}&=T_{ij}^{11}-T_{ij}^{10},\\
(-Q_{ij})_+&=T_{ij}^{10},&V_i&=B_i,
 &h_i&=(V_i-\ell_i)_+=A_i,\\
H&=\sum_iA_i=c.
\end{aligned}
\tag{126.8}
$$

Here $h_i$ is the coefficient vector of Definition 108.2,
distinct from the head scalar $h$ in (123.1).
Common column masses imply
$\mathfrak m(A_i)=\mathfrak m(B_i)=\sum_{j>i}w_{ij}$;
therefore $\beta=\sum_i\mathfrak m(A_i)=1$.
The kernel has degree at most two. Applying Theorem 109.1 gives
$p\in\mathscr C_5=\mathscr O_5\subseteq\mathscr N_5$,
at the exact closed boundary $c=H$, $\beta=1$.
This also agrees with the general face-saturation supplier 119.4.
The support argument is made after mixing; disjointness for each
endpoint by itself would not ensure disjointness of mixed columns.
$\square$

## 127. One seed, counted requests and the prescribed actual tail

**Theorem 127.1 (Original realization and exact error).** For every
original sequence and cap satisfying (121.1)--(121.3), the law
constructed in Theorem 126.1 has original $\mathcal O_2$ and
$\mathcal N_2$ realizations with the same common seed and the
same original-tape law at every source. They use zero advice,
hand off finitely at every source and seed, and have uniform
selected-law error exactly $\varepsilon$. Every actual tail
source has error exactly $\varepsilon$.

**Proof.** Let one $U$ be uniform on $[0,1)$, independent of
the source. Its law is the same for all $x\in X$. Partition
this interval into the twelve endpoint weights from (126.1)--(126.3),
omitting zero intervals. Within the chosen positive endpoint
interval rescale the local value to $[0,1)$, and partition it
according to that endpoint's pair weights. Rescale within the
chosen positive pair interval once more to a value $v\in[0,1)$.
For each of its three stopped cells, predeclare a partition of
this same $v$ interval with label probabilities
$T_{ij}^{\tau}/w_{ij}$ from that endpoint table. These three
partitions define all three deterministic cell labels from $U$
before any answers. No independent terminal seeds are needed,
and no label choice is made separately for each source.

Use half-open intervals in a fixed order so that every boundary
has a specified branch and label. If the seed carrier is instead
$[0,1]$, assign the last null endpoint any valid pair and terminal
table explicitly. All branches then have finite case selection.
The probabilities and partitions are mathematically defined for
arbitrary real parameters; no effective arithmetic or algorithm
for computing arbitrary real interval boundaries is asserted.

The $O$ realization actually queries the chosen original prime
indices $i<j\le5$, stopping after a zero at $i$, a zero at $j$,
or positive exhaustion. It outputs the original measurable mark
$\theta_r$ prescribed by that stopped cell. Only acquired static
answers and the one seed are used. The $N$ realization with the
same $U$ actually acquires both replies, reconstructs the same
stopped cell and emits the identical mark. After a zero at $i$
its second reply is ignored, but this second request is still
made and counted. This is the completion of Proposition 90.2,
not a reduction of the count by ignoring a reply. Thus $O$ makes
one or two actual requests and $N$ makes exactly two, on distinct
original addresses. Both hand off after finite operations for
every seed and actual source. In particular they meet the weaker
sourcewise almost-sure handoff contract. The finite endpoint
selection is internal seed randomness, not advice about the source.

The original-to-finite necessity and finite-to-original realization
are the two directions of Theorem 110.2. In the realization used
here the finite index $i$ means exactly the actual static answer
$q_i(x)=\mathbf1_{p_i\mid N(x)}$ on the original labeled source;
label $r$ means the original tape $\theta_r$. A source with
$n(x)\le5$ has one of the 31 low words with that first zero,
including arbitrary additional zeros. Its selected target is
exactly the target checked at that word. Hence its error is at
most $\varepsilon$, and no later-zero restriction is imposed.

For $n(x)>5$ its low word is $11111$. The emitted law is
supported on $\theta_0,\ldots,\theta_5$, while its actual
selected target retains the distinct original mark
$\theta_{n(x)}$ with its prescribed positive amplitude. The
exact tail identity (110.9), with
$p_{11111}(0)=1-\varepsilon$, gives

$$
\operatorname{TV}(\widehat\lambda_{O,x},\lambda_x^a)
 =\operatorname{TV}(\widehat\lambda_{N,x},\lambda_x^a)
 =\max\{\varepsilon,a_{n(x)}\}=\varepsilon.
\tag{127.1}
$$

Monotonicity and $a_6\le\varepsilon$ give the last equality,
including $a_6=\varepsilon$. No tail amplitude is replaced,
truncated or set to zero. Boundaries, Theorem 35.2 supplies actual
sources with first absence six by the finite pattern $111110$.
Therefore (127.1) attains the supremum over actual sources;
an infinite all-positive source is neither needed nor available.
Together with the low-word bounds this proves uniform error exactly
$\varepsilon$.

The output-law statements concern only the separately selected
marked targets (110.3). The original consumer and original
nonatomic targets remain fixed on the full carrier. An emitted
atomic law has TV distance one from each unchanged nonatomic
original target, and the consumer returns unknown on these $B_1$
marks, as supplied by Acquisition Resources, Theorem 82.1.
Consequently the chosen marked-law acquisition claim is a literal
source/carrier/resource correspondence, with no new performance
claim for that consumer or those original targets. Bounded addresses
and finite mark support describe the constructed witnesses;
necessity still quantifies over the arbitrary-address, full-carrier
competitors transported by 110.2. No source distribution or
transition-time bound has been introduced. $\square$

## 128. Exact ambient closure and strict original-source density

**Definition 128.1 (Closed ambient projection).** Let $P$ be the
following subset of $\mathbb R^6$, in the coordinate order
$(a_1,a_2,a_3,a_4,a_5,\varepsilon)$:

$$
\begin{gathered}
1\ge a_1\ge a_2\ge a_3\ge a_4\ge a_5\ge\varepsilon\ge0,
\qquad \delta=1-a_2,\\
18\varepsilon=2a_2+3(a_3+a_4+a_5)-2,\\
a_1-a_2\le\delta/3,\quad
 a_3\ge\varepsilon+4\delta/3,\quad
 a_4\ge\varepsilon+\delta,\quad
 a_5\ge\varepsilon+\delta/3.
\end{gathered}
\tag{128.1}
$$

Order, upper normalization, the face equation and nonnegative cap
are part of $P$. If expressed in five amplitude coordinates,
eliminate $\varepsilon$ using the displayed face equation and
retain every resulting ambient inequality. The bare four cuts
without this domain are not the asserted polytope.

Let $R_N$ and $R_O$ be the finite amplitude-cap projections of
original cap-feasible rules on (121.1)--(121.2), allowing every
legal prescribed positive nonincreasing vanishing tail. Equivalently
these are the face projections $\mathcal P_N,\mathcal P_O$
of Definition 120.1, by 110.2 and 119.3. Feasibility is independent
of which such tail is attached; its actual error need not omit it.

**Theorem 128.2 (Exact closure).** In the usual topology of
$\mathbb R^6$,

$$
R_N=R_O=P\cap\{a_5>\varepsilon>0\},
\qquad \overline{R_N}=\overline{R_O}=P.
\tag{128.2}
$$

Every approximating strict profile is realized on an original
positive infinite sequence. Auxiliary zero-cap or
$a_5=\varepsilon$ endpoint tables are not substituted for
original sources in this assertion.

**Proof.** The equality of the strict-domain sets follows from
Theorem 121.2 and its arbitrary-tail realization. The set $P$ is
a closed bounded intersection of affine half-spaces and the face
hyperplane, so the two closures are contained in $P$.
For the reverse inclusion use the strictly interior finite profile

$$
q=(11/12,\ 9/10,\ 91/180,\ 17/36,\ 19/45,\ 2/9).
\tag{128.3}
$$

Its amplitudes are strictly decreasing, $a_1<1$ and
$a_5>\varepsilon>0$. It lies on the face and has coordinates

$$
(\delta,x,y,z,h)=(1/10,1/30,1/20,1,1/60).
\tag{128.4}
$$

The four cut slacks, in their order in (121.3), are
$1/60,3/20,3/20,1/6$, all strictly positive. For any $p\in P$
and $0<t\le1$, the convex combination $p_t=(1-t)p+tq$
therefore remains in $P$ and satisfies all original finite-domain
strict inequalities $a_5^{(t)}>\varepsilon_t>0$; it also has
strict ambient order and strict cuts. Attach, for example, the tail

$$
a_{5+k}^{(t)}=\varepsilon_t/2^{k-1}\qquad(k\ge1).
\tag{128.5}
$$

It is positive, nonincreasing, vanishes, and has
$a_6^{(t)}=\varepsilon_t<a_5^{(t)}$. Theorem 121.2 supplies
original cap-feasible $N,O$ on this actual infinite sequence,
so $p_t\in R_N=R_O$. As $t$ decreases to zero, $p_t$ converges
to $p$. This proves the reverse closure containment.

The finite profiles $V_0,V_x,V_y$ legitimately participate in
the affine proof of Theorem 126.1. None is individually subjected
to original-source transport with an illegal zero or nonvanishing
tail. It is the strict-density argument (128.3)--(128.5) that
relates all closed points, including those auxiliary profiles,
to the original strict domain. At a strict target the constructed
law attains the exact cap directly; a limit sampler is not needed.
$\square$

## 129. Supplier relationships and the remaining comparison

**Definition 129.1 (Scope of the derived classification).** The
classification (121.3) is a repo-derived ordinary consequence of
the new three full-schedule certificates, the complete cone
construction and the twelve common-budget stopped laws, relative
to the named ordinary suppliers. Theorem 109.1 owns stopped
coefficient realizability; Theorem 110.2 owns exact closed-cap
original transport; Theorem 113.2 owns the head residual cut;
Acquisition Resources, Proposition 90.2 owns same-seed schedule
completion. Their results are applied in their existing scopes,
not re-proved or identified as new face inequalities. Theorems
117.2, 118.1 and 119.3--119.4 supply the second-head bound,
the earlier sharp family, and the tight-face finite reduction
and saturation. The additional late cuts and the whole-face
constructive sufficiency extend that family to arbitrary unequal
late amplitudes in the stated normalized domain. The exact-law
obstruction 112.2 does not prevent existence of another stopped
law at the same cap.

Kaniewski, Lee and de Wolf, [*Query complexity in expectation*,
Definition 8 and Theorem 9](https://arxiv.org/html/1411.7280v1),
characterize scalar nonnegative expected output through nonnegative
literal degree. Their monomial-sampling proof uses a scaled
indicator output. It does not supply jointly normalized
probability-vector terminal budgets or an increasing first-zero-stop
replacement at a common TV cap. Hellerstein, Kletenik, Liu and
Witter, [*Adaptivity Gaps for the Stochastic Boolean Function
Evaluation Problem*, Section 1](https://arxiv.org/html/2208.03810v1),
use independent input-bit probabilities, Boolean evaluation and
expected testing costs. Those assumptions and resources differ
from uniform generation over every actual source with a hard
actual-request count. Neither source is used as the face
replacement theorem. The weighted-event method has antecedents
in Acquisition Resources, Sections 91, 97 and 104 and in Section
117 here; finite plateau and sparse laws are also existing suppliers.
These attributions distinguish the present derived composition
from borrowed methods and assert no exhaustive literature coverage
or mathematical-priority claim.

**Theorem 129.2 (Resolution of the specified face projection).**
For the strict face domain $\Delta_5$ of Definition 120.1,

$$
\mathcal P_N=\mathcal P_O
 =\Delta_5\cap\{\text{the four cuts in (121.3)}\}.
\tag{129.1}
$$

Thus the question (120.1) is affirmative on this entire face,
with the closure (128.1). This conclusion does not assert the
universal comparison (110.14), nor its negation.

**Proof.** Theorem 119.3 relates the two finite systems defining
these projections to original feasibility at the exact cap.
Theorem 121.2 gives both directions and their exact amplitude
conditions, with every legal actual tail. Theorem 128.2 gives
the closure. $\square$

The full all-amplitude/all-cap implication (110.14) remains
unresolved, as do the $L=5$ profiles off this equality face
and the $L\ge6$ comparison. No supplementary off-face theorem
is included here. In particular common endpoint budgets and
all-word affine interpolation prove this face; they furnish
neither a universal stopped replacement nor an all-stopped
separator at another profile. The claim is ordinary mathematical
existence relative to the accepted ordinary suppliers, without
kernel certification. Its exact real-parameter partitions do not
assert effective computation on arbitrary reals. The acquisition
statement applies to the separately selected original marked laws,
with actual original tapes and counted queries; it does not change
the original consumer or its nonatomic target laws.

## 追加锚（本行以下为增补区）

## 130. The complete adjacent C3-saturated five-active domain

**Definition 130.1 (Original contract and adjacent domain).** Retain
Definitions 108.1--108.2 and 110.1, and Acquisition Resources,
Definitions 71.1, 73.1 and 90.1. In particular the actual source is
$X=\{(r,g):r\text{ prime},\ \lceil F_r/10\rceil\le g\le\lfloor F_r/5\rfloor\}$,
with integer $g$, static $N(r,g)=1+F_rg$,
$q_i(x)=\mathbf1_{p_i\mid N(x)}$ and first absence $n(x)$.
Every finite answer pattern is occupied by Boundaries, Theorem 35.2.
There is no source distribution and no infinite all-positive actual source.
The full original measurable tape carrier is
$\Theta=\bigsqcup_{j\ge1}B_j\sqcup\bigsqcup_{j\ge1}P_j$,
with each block a copy of $(0,1)$ and its disjoint-union Borel sigma algebra.
The marks remain $\theta_j=(B_1,1/(j+2))$.
The separately selected law is
$\lambda_x^a=(1-a_{n(x)})\delta_{\theta_0}+a_{n(x)}\delta_{\theta_{n(x)}}$;
the original consumer and nonatomic targets $\mu_x$ remain those of
Source-Correlated Laws, Theorem 67.5.

Both original classes use zero advice, one source-independent seed,
measurable records and output, and actual sourcewise almost-sure finite
handoff. Once the seed is fixed there is one deterministic rule for all
sources. $\mathcal N_2$ preselects and acquires at most two requests;
$\mathcal O_2$ preselects an increasing schedule of length at most two
and stops at its first queried zero or exhaustion. All actual requests,
including repetitions and ignored completion replies, count. Competitors
may choose arbitrary addresses and any tape in $\Theta$. This hard count
is not a maximum address, depth, processing time or mean count.

For every full prescribed sequence $1\ge a_1\ge a_2\ge\cdots>0$
tending to zero and cap $\varepsilon>0$, put

$$
\begin{aligned}
\delta&=1-a_2,&h&=a_1-a_2,&S&=a_3+a_4+a_5,&M&=5a_3-a_4-a_5,\\
\kappa_3&=29\varepsilon-2a_2-4a_3-5a_4-5a_5+2,\\
\sigma&=18\varepsilon-2a_2-3S+2.
\end{aligned}
\tag{130.1}
$$

The strict adjacent domain $\mathcal D_{\rm adj}$ consists of precisely

$$
\begin{gathered}
1\ge a_1\ge a_2\ge a_3\ge a_4\ge a_5>\varepsilon>0,
\qquad a_6\le\varepsilon,\qquad \kappa_3=0,\quad\sigma>0,\\
3\varepsilon<D_3(a,\varepsilon)\le3\varepsilon+1-a_1,
\qquad D_3=\sum_{n\ge3}(a_n-\varepsilon)_+=S-3\varepsilon.
\end{gathered}
\tag{130.2}
$$

All actual positive vanishing tails are retained. Their residuals vanish;
the amplitudes themselves do not. Define the five affine cuts

$$
\begin{aligned}
F_1&=35a_3-7a_4-7a_5-32\delta,\\
F_2&=a_3-6a_4+23a_5-15\delta,\\
F_3&=6a_4+6a_5-a_3-14\delta,\\
F_4&=18a_3+8a_4-21a_5-9\delta,\\
F_5&=27a_4-19a_3-2a_5-5\delta.
\end{aligned}
\tag{130.3}
$$

On $B_5=\{0,1\}^5$ use all six labels $J_5=\{0,\ldots,5\}$.
For a word with first zero $n$, its finite target is
$\eta_b=(1-a_n)e_0+a_ne_n$, and $\eta_{11111}=e_0$.
The cap slice $\mathcal F_N$ and coefficient region $\mathscr C_5$
are exactly Definitions 110.1 and 108.2. The cap has 94 separate rows:
three for each of the 31 zero words, and one for $11111$.
Indeed the supplied identity (84.2) is

$$
\operatorname{TV}(p,\eta_b)
=\max\{0,1-a_n-p(0),a_n-p(n),1-p(0)-p(n)\}.
\tag{130.4}
$$

Thus the union row $p(0)+p(n)\ge1-\varepsilon$ is a separate
constraint; adding the two singleton demands does not replace it.

**Theorem 130.2 (Complete adjacent existential cap equivalence).**
For every original sequence and cap in $\mathcal D_{\rm adj}$,

$$
\begin{aligned}
\exists N\in\mathcal N_2:\ e_a(N)\le\varepsilon
&\ \Longleftrightarrow\ \exists O\in\mathcal O_2:\ e_a(O)\le\varepsilon\\
&\ \Longleftrightarrow\ \mathcal F_N(a,\varepsilon)\cap\mathscr C_5\ne\varnothing\\
&\ \Longleftrightarrow\ F_i\ge0\quad(1\le i\le5).
\end{aligned}
\tag{130.5}
$$

When feasible, one continuous finite-law construction attains the cap
exactly on every actual tail and supplies $O$ and its completed $N$
with one common seed and identical laws. This replaces the whole law;
it need not preserve an input $N$ law. Sections 131--136 prove the claim.

**Lemma 130.3 (Head and residual identities).** At $\kappa_3=0$,

$$
\begin{aligned}
29(S-6\varepsilon)&=12\delta+M,&29\sigma&=22\delta-3M,\\
S-6\varepsilon&=(2\delta-\sigma)/3,&
H_{\rm head}&=(17\delta-M)/29=(\delta+\sigma)/3.
\end{aligned}
\tag{130.6}
$$

The sign of $M$ in the first identity is positive. On the feasible strict
domain, $\delta>0$ and

$$
\begin{gathered}
0<\sigma\le2\delta/7,\qquad
0\le h\le H_{\rm head},\qquad
\delta/3<H_{\rm head}\le3\delta/7,\\
4\delta/7\le S-6\varepsilon<2\delta/3,\qquad
6\varepsilon<S\le7\varepsilon.
\end{gathered}
\tag{130.7}
$$

**Proof.** Substitute
$29\varepsilon=-2\delta+4a_3+5a_4+5a_5$ to obtain (130.6).
The retained upper residual condition, or the necessary supplier 113.2,
is $S-6\varepsilon\le\delta-h$, equivalent to $h\le H_{\rm head}$.
The cut $F_1\ge0$ says $M\ge32\delta/7$; $\sigma>0$ says
$M<22\delta/3$. These give the residual interval and sigma bound.
The cut $F_3\ge0$ is equivalent on this hyperplane to $S\le7\varepsilon$.
If $\delta=0$, order gives $M=3a_5+4(a_4-a_5)+5(a_3-a_4)>0$,
contradicting $29\sigma=-3M>0$. Hence $\delta>0$.
The head bounds follow from its identity. $\square$

## 131. Full schedule saturation and five shared-budget cuts

**Definition 131.1 (Literal events and scores).** Number the following
16 rows by $r=1,\ldots,16$. Coincident words with different events are
different rows. $C_3,J_1,\ldots,J_5,K_5$ denote the scores obtained by
weighting the event probabilities, with $K_5=C_3+J_5$.

| Row | Word | Event | C3 | J1 | J2 | J3 | J4 | J5 | K5 |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| 1 | 00100 | {0,1} | 1 | 0 | 1 | 0 | 0 | 1 | 2 |
| 2 | 00110 | {0,1} | 1 | 2 | 0 | 0 | 1 | 0 | 1 |
| 3 | 01000 | {0,1} | 1 | 1 | 1 | 0 | 0 | 1 | 2 |
| 4 | 01010 | {0,1} | 1 | 2 | 1 | 1 | 1 | 1 | 2 |
| 5 | 01100 | {0,1} | 1 | 3 | 1 | 1 | 1 | 0 | 1 |
| 6 | 10000 | {0,2} | 1 | 1 | 1 | 1 | 0 | 1 | 2 |
| 7 | 10010 | {0,2} | 1 | 2 | 1 | 0 | 1 | 1 | 2 |
| 8 | 10100 | {2} | 1 | 0 | 1 | 0 | 0 | 1 | 2 |
| 9 | 10100 | {0,2} | 1 | 3 | 1 | 0 | 1 | 0 | 1 |
| 10 | 10110 | {2} | 1 | 2 | 0 | 0 | 1 | 0 | 1 |
| 11 | 11000 | {3} | 2 | 2 | 1 | 0 | 0 | 1 | 3 |
| 12 | 11000 | {0,3} | 1 | 2 | 1 | 0 | 1 | 0 | 1 |
| 13 | 11010 | {3} | 2 | 3 | 2 | 1 | 2 | 2 | 4 |
| 14 | 11100 | {4} | 5 | 8 | 4 | 1 | 3 | 2 | 7 |
| 15 | 11110 | {5} | 5 | 8 | 3 | 1 | 4 | 3 | 8 |
| 16 | 11111 | {0} | 4 | 6 | 3 | 1 | 3 | 3 | 7 |

For any score with weights $k_r$, any canonical schedule $Q$, its cell
$z$, and any label $j\in J_5$, define

$$
g^k_{Qz}(j)=\sum_{r:b^r|_Q=z}k_r\mathbf1_{j\in E_r},\qquad
M^k_{Qz}=\max_{j\in J_5}g^k_{Qz}(j),\qquad
B^k_Q=\sum_zM^k_{Qz}.
\tag{131.1}
$$

This literal formula reconstructs every label score, including zeros.
Canonical schedules are empty, the five singletons and all ten distinct
increasing pairs. For a singleton cells are $0,1$; for a pair they
remain separately $00,01,10,11$. Reverse pairs reorder these cells.
A repeated request has only cells $00,11$ and singleton information;
its original actual request cost is still two. The full C3 maxima and
maximizer-label sets are as follows, before any support reduction.

| Schedule | Cell maxima | Maximizer sets in cell order | Sum |
| --- | --- | --- | --- |
| empty | (13) | {0} | 13 |
| 1 | (5,8) | {0,1}; {0} | 13 |
| 2 | (5,8) | {0,2}; {0} | 13 |
| 3 | (5,8) | {0,3}; {0} | 13 |
| 4 | (6,7) | {0}; {0} | 13 |
| 5 | (9,4) | {0}; {0} | 13 |
| 12 | (2,3,5,5) | {0,1}; {0,1}; {2}; {0,3,4,5} | 15 |
| 13 | (2,3,5,5) | {0,1}; {0,1}; {3}; {0,4,5} | 15 |
| 14 | (3,2,5,5) | {0,1}; {0,1}; {4}; {0,5} | 15 |
| 15 | (5,0,5,4) | {0,1}; {0,1,2,3,4,5}; {2,3,4,5}; {0} | 14 |
| 23 | (2,3,5,5) | {0,2}; {0,2}; {3}; {0,4,5} | 15 |
| 24 | (3,2,5,5) | {0,2}; {0,2}; {4}; {0,5} | 15 |
| 25 | (5,0,5,4) | {0,2}; {0,1,2,3,4,5}; {3,4,5}; {0} | 14 |
| 34 | (3,2,5,5) | {0,3}; {0,3}; {4}; {0,5} | 15 |
| 35 | (5,0,5,4) | {0,3}; {0,1,2,3,4,5}; {4,5}; {0} | 14 |
| 45 | (6,0,5,4) | {0}; {0,1,2,3,4,5}; {5}; {0} | 15 |

**Lemma 131.2 (Saturation from the entire N5 class).** Every finite
$\mathscr N_5$ kernel has $C_3(p)\le15$. At a feasible
$\kappa_3=0$ cap, all 16 C3 events are tight and a representation has
support only on pairs $12,13,14,23,24,34,45$, using precisely the
maximizer-label restrictions in the preceding table.

**Proof.** A common terminal-mass representation gives schedule weight
$w_Q$ and nonnegative cell masses $T_{Qz}(j)$, with
$\sum_jT_{Qz}(j)=w_Q$ for every cell and $\sum_Qw_Q=1$.
The schedule and all deterministic cell outputs are fixed by one seed.
Its score is at most $B^{C_3}_Q\le15$; integrating proves the bound.
For the target, the table gives

$$
C_3(\eta)=13+2a_2+4a_3+5a_4+5a_5,\qquad
\sum_r k^{C_3}_r=29.
\tag{131.2}
$$

Each event obeys $p_{b^r}(E_r)\ge\eta_{b^r}(E_r)-\varepsilon$,
so $C_3(p)\ge15-\kappa_3$. At $\kappa_3=0$ equality follows.
The exact nonnegative loss decomposition is

$$
15-C_3(p)=\sum_Q(15-B^{C_3}_Q)w_Q+
 \sum_{Q,z,j}(M^{C_3}_{Qz}-g^{C_3}_{Qz}(j))T_{Qz}(j).
\tag{131.3}
$$

Every summand must vanish. Empty and singleton schedules, thus also
repeated-coordinate schedules, and pairs $15,25,35$ have zero weight.
All remaining positive masses use C3 maximizers. Separately, the weighted
sum of nonnegative event gaps
$p_{b^r}(E_r)-\eta_{b^r}(E_r)+\varepsilon$ is zero; all C3 weights
are positive, so every event is tight. The $00,01$ masses remain distinct
N vectors even when their allowed sets agree. Pair $45/01$ has score
zero for all six labels and keeps all six labels and its full-word rows.
For original necessity first apply 110.2 to the unrestricted
arbitrary-address/full-carrier competitor. This deduction concerns its
finite feasible representative, without restricting the original rule's
addresses, tapes or exact laws. $\square$

**Lemma 131.3 (Five-cut elimination on the saturated representation).**
Every feasible saturated representation satisfies (130.3).

**Proof.** Maximize each J score over the allowed sets of Lemma 131.2,
separately on all four N cells. The resulting complete tables are:

| Pair | J1 maxima | J2 maxima | J3 maxima | J4 maxima | J5 maxima |
| --- | --- | --- | --- | --- | --- |
| 12 | (2,6,8,8) | (1,3,4,4) | (0,2,1,1) | (1,2,3,4) | (1,2,3,3) |
| 13 | (3,5,7,9) | (2,2,4,4) | (1,1,1,1) | (1,2,3,4) | (2,1,3,3) |
| 14 | (4,4,8,8) | (3,1,4,4) | (1,1,1,1) | (1,2,3,4) | (2,1,2,4) |
| 23 | (3,5,7,9) | (2,2,4,4) | (1,0,1,2) | (1,2,3,4) | (2,1,3,3) |
| 24 | (4,4,8,8) | (3,1,4,4) | (1,0,1,2) | (1,2,3,4) | (2,1,2,4) |
| 34 | (4,4,8,8) | (3,2,4,3) | (1,1,1,1) | (1,2,3,4) | (2,2,2,3) |
| 45 | (10,0,8,6) | (6,0,3,3) | (2,0,1,1) | (3,0,4,3) | (3,0,3,3) |

The sums on each permitted pair are respectively $24,12,4,10,9$.
This is one budget: summing the cell bounds gives these same bounds
multiplied by $\sum_Qw_Q=1$. No cell is assigned a separate unit budget.
In particular $45/01$ contributes zero for every allowed label.
The exact target score and row-weight sums are:

| Score | Target score | Weight sum | Saturated upper |
| --- | --- | --- | --- |
| J1 | $22+2a_2+5a_3+8a_4+8a_5$ | 45 | 24 |
| J2 | $11+a_2+3a_3+4a_4+3a_5$ | 22 | 12 |
| J3 | $4+S$ | 7 | 4 |
| J4 | $9+a_2+2a_3+3a_4+4a_5$ | 19 | 10 |
| J5 | $8+a_2+3a_3+2a_4+3a_5$ | 17 | 9 |

The lower bound is target score minus the displayed weight sum times
$\varepsilon$, including every union event with one cap subtraction.
Substituting the C3 hyperplane, 29 times upper minus this lower bound
is exactly $F_1,\ldots,F_5$ respectively. Thus all five cuts are
necessary. The event and maximum tables are integer certificates for
all labels and cells via (131.1), not scalar tests on selected inputs
or separate optimizations of incompatible terminal laws. $\square$

## 132. Compact ratio geometry and conforming continuous weights

**Definition 132.1 (The eight-facet ratio polytope).** Let $P\subset\mathbb R^3$
be the intersection $N_f\cdot(t,u,v)\le b_f$ of these eight half-spaces;
facet indices and vertex indices start at zero.

| Facet f | Normal N_f | Upper b_f |
| --- | --- | --- |
| 0 | (-1,1,0) | 0 |
| 1 | (0,-1,1) | 0 |
| 2 | (-35,7,7) | -32 |
| 3 | (-1,6,-23) | -15 |
| 4 | (1,-6,-6) | -14 |
| 5 | (-18,-8,21) | -9 |
| 6 | (19,-27,2) | -5 |
| 7 | (15,-3,-3) | 22 |

Its nine vertices and their active facets are:

| Vertex | (t,u,v) | Active facets |
| --- | --- | --- |
| R0 | (10/7,9/7,9/7) | (1,2,4,5,6) |
| R1 | (10/7,10/7,8/7) | (0,2,4) |
| R2 | (3/2,3/2,10/7) | (0,2,5) |
| R3 | (8/5,8/5,1) | (0,3,4) |
| R4 | (9/5,9/5,9/5) | (0,1,5) |
| R5 | (2,5/3,1) | (3,4,6,7) |
| R6 | (19/9,19/9,10/9) | (0,3,7) |
| R7 | (20/9,17/9,17/9) | (1,6,7) |
| R8 | (22/9,22/9,22/9) | (0,1,7) |

**Lemma 132.2 (Exact compact coverage).** $P$ is precisely the convex
hull of these nine vertices. The following is the complete classification
of the 56 three-facet systems. An infeasible row gives its exact solution,
a violated facet and its positive violation. A singular row has zero
determinant; a feasible row names its vertex.

| Facets | Type | Solution or vertex | Violated facet | Positive gap |
| --- | --- | --- | --- | --- |
| (0,1,2) | infeasible | (32/21,32/21,32/21) | 5 | 29/21 |
| (0,1,3) | infeasible | (5/6,5/6,5/6) | 2 | 29/2 |
| (0,1,4) | infeasible | (14/11,14/11,14/11) | 2 | 58/11 |
| (0,1,5) | feasible | R4 | — | — |
| (0,1,6) | infeasible | (5/6,5/6,5/6) | 2 | 29/2 |
| (0,1,7) | feasible | R8 | — | — |
| (0,2,3) | infeasible | (29/21,29/21,20/21) | 4 | 29/21 |
| (0,2,4) | feasible | R1 | — | — |
| (0,2,5) | feasible | R2 | — | — |
| (0,2,6) | singular | — | — | — |
| (0,2,7) | singular | — | — | — |
| (0,3,4) | feasible | R3 | — | — |
| (0,3,5) | infeasible | (18/17,18/17,15/17) | 2 | 145/17 |
| (0,3,6) | infeasible | (5/6,5/6,5/6) | 2 | 29/2 |
| (0,3,7) | feasible | R6 | — | — |
| (0,4,5) | infeasible | (4/3,4/3,11/9) | 2 | 29/9 |
| (0,4,6) | infeasible | (1,1,3/2) | 1 | 1/2 |
| (0,4,7) | infeasible | (2,2,2/3) | 3 | 29/3 |
| (0,5,6) | infeasible | (3/4,3/4,1/2) | 2 | 29/2 |
| (0,5,7) | infeasible | (5/2,5/2,8/3) | 1 | 1/6 |
| (0,6,7) | singular | — | — | — |
| (1,2,3) | infeasible | (26/21,17/21,17/21) | 4 | 116/21 |
| (1,2,4) | feasible | R0 | — | — |
| (1,2,5) | feasible | R0 | — | — |
| (1,2,6) | feasible | R0 | — | — |
| (1,2,7) | singular | — | — | — |
| (1,3,4) | infeasible | (-2,1,1) | 0 | 3 |
| (1,3,5) | infeasible | (12/11,9/11,9/11) | 2 | 58/11 |
| (1,3,6) | infeasible | (5/6,5/6,5/6) | 2 | 29/2 |
| (1,3,7) | infeasible | (16/9,7/9,7/9) | 4 | 58/9 |
| (1,4,5) | feasible | R0 | — | — |
| (1,4,6) | feasible | R0 | — | — |
| (1,4,7) | infeasible | (2,4/3,4/3) | 6 | 29/3 |
| (1,5,6) | feasible | R0 | — | — |
| (1,5,7) | infeasible | (8/3,3,3) | 0 | 1/3 |
| (1,6,7) | feasible | R7 | — | — |
| (2,3,4) | infeasible | (10/7,11/7,1) | 0 | 1/7 |
| (2,3,5) | infeasible | (8/7,3/7,5/7) | 1 | 2/7 |
| (2,3,6) | infeasible | (4/3,25/21,19/21) | 4 | 58/21 |
| (2,3,7) | singular | — | — | — |
| (2,4,5) | feasible | R0 | — | — |
| (2,4,6) | feasible | R0 | — | — |
| (2,4,7) | singular | — | — | — |
| (2,5,6) | feasible | R0 | — | — |
| (2,5,7) | singular | — | — | — |
| (2,6,7) | singular | — | — | — |
| (3,4,5) | infeasible | (1,3/2,1) | 0 | 1/2 |
| (3,4,6) | feasible | R5 | — | — |
| (3,4,7) | feasible | R5 | — | — |
| (3,5,6) | infeasible | (16/15,1,13/15) | 2 | 116/15 |
| (3,5,7) | infeasible | (4/3,-1,1/3) | 1 | 4/3 |
| (3,6,7) | feasible | R5 | — | — |
| (4,5,6) | feasible | R0 | — | — |
| (4,5,7) | infeasible | (2,1,5/3) | 1 | 2/3 |
| (4,6,7) | feasible | R5 | — | — |
| (5,6,7) | infeasible | (7/3,2,7/3) | 1 | 1/3 |

**Proof.** Put $x=t-u\ge0$, $y=u-v\ge0$ and
$m=5t-u-v=3v+4y+5x$. Facets 2 and 7 give
$32/7\le m\le22/3$. Facet 3 is $18v-5y+x\ge15$;
substitution gives $29(x+y)\le6m-15\le29$. Thus $x,y$ are
bounded between zero and one and $v=(m-4y-5x)/3$ is bounded.
Hence $P$ is closed and bounded. The arithmetic centroid

$$
C=(10417/5670,9907/5670,4127/2835)=\frac19\sum_{j=0}^8R_j
\tag{132.1}
$$

satisfies every inequality strictly, proving nonempty interior.
The literal systems above give eight singular, 27 infeasible and 21
feasible bases with exactly the nine displayed solutions.
If active normals fail to span $\mathbb R^3$, a nonzero annihilating
displacement preserves their equalities and, for a sufficiently small
movement in both directions, every inactive inequality. The point is
not extreme. Thus every vertex has an independent active triple and
appears in the table; conversely every listed vertex has such a triple.
For any other point in its minimal face, a nonzero tangent displacement
extends by compactness to a chord with endpoints on proper subfaces.
The point is a convex mixture of those endpoints. Induction on face
dimension terminates at vertices and proves the whole convex-hull
identity, rather than inferring continuum coverage from an endpoint scan.
$\square$

**Lemma 132.3 (A conforming fourteen-tetrahedron interpolation).** The
following facet cycles and their fans triangulate the entire boundary.

| Facet | Cyclic vertex indices | Fan triangles |
| --- | --- | --- |
| 0 | (1,2,4,8,6,3) | (1,2,4); (1,4,8); (1,8,6); (1,6,3) |
| 1 | (0,4,8,7) | (0,4,8); (0,8,7) |
| 2 | (0,1,2) | (0,1,2) |
| 3 | (3,5,6) | (3,5,6) |
| 4 | (0,1,3,5) | (0,1,3); (0,3,5) |
| 5 | (0,2,4) | (0,2,4) |
| 6 | (0,5,7) | (0,5,7) |
| 7 | (5,6,8,7) | (5,6,8); (5,8,7) |

For each of the fourteen listed triangles $(i,j,k)$ use the tetrahedron
$(C,R_i,R_j,R_k)$. These tetrahedra cover $P$ with disjoint interiors.
There are continuous nonnegative functions $\mu_0,\ldots,\mu_8$ on
$P$ satisfying

$$
\sum_j\mu_j(q)=1,\qquad q=\sum_j\mu_j(q)R_j.
\tag{132.2}
$$

**Proof.** The cycles contain exactly the vertices on each facet;
consecutive edges support their convex polygons. The fans cover those
polygons with disjoint interiors. Along two facets' common original
edge the triangulations agree. The fourteen boundary triangles have
21 edges, each in two triangles. A ray from the strictly interior $C$
meets the compact convex boundary in exactly one point. Coning each
triangle to $C$ therefore covers $P$; intersections of tetrahedra are
cones over common boundary faces, or just $C$. Each determinant is
nonzero since $C$ is outside its facet plane.
Assign nodal data $\mu(R_j)=e_j^{\rm vert}$ and
$\mu(C)=(1/9,\ldots,1/9)$ in $\mathbb R^9$.
On each tetrahedron solve the nonsingular barycentric system with
columns $(C,1),(R_i,1),(R_j,1),(R_k,1)$. For barycentric coordinates
$\alpha_C,\alpha_i,\alpha_j,\alpha_k$, set

$$
\mu_l=\alpha_C/9+\alpha_i\mathbf1_{l=i}
                   +\alpha_j\mathbf1_{l=j}+\alpha_k\mathbf1_{l=k}.
\tag{132.3}
$$

Inside the tetrahedron these are nonnegative, sum to one and recover
$q$ by (132.1). On a common face each opposite coordinate vanishes
and the remaining nodal data agree. Thus formulas agree on every
overlap and are globally continuous. $\square$

## 133. Nineteen exact stopped endpoint laws and all-word certificates

**Definition 133.1 (Normalized ray/head endpoints).** For $R_j=(t_j,u_j,v_j)$
of Section 132 put $\delta_j=1/(1+t_j)$ and

$$
\begin{aligned}
a_2^j=a_3^j&=\delta_jt_j,&a_4^j&=\delta_ju_j,&a_5^j&=\delta_jv_j,\\
\varepsilon_j&=\delta_j(-2+4t_j+5u_j+5v_j)/29,\\
H_j&=\delta_j(17-5t_j+u_j+v_j)/29.
\end{aligned}
\tag{133.1}
$$

The endpoints $V_j^-$ and $V_j^+$ have these same five coordinates,
and respectively $a_1^j=a_2^j$ and $a_1^j=a_2^j+H_j$.
The auxiliary base is $V_{\rm base}=(1,1,0,0,0,0)$.
In the following table divide every profile numerator by its denominator
$d$. The coordinate order is $(a_1,a_2,a_3,a_4,a_5,\varepsilon)$.

| Endpoint | d | Profile numerator |
| --- | --- | --- |
| Vbase | 1 | (1,1,0,0,0,0) |
| V0- | 17 | (10,10,10,9,9,4) |
| V0+ | 17 | (13,10,10,9,9,4) |
| V1- | 17 | (10,10,10,10,8,4) |
| V1+ | 17 | (13,10,10,10,8,4) |
| V2- | 35 | (21,21,21,21,20,9) |
| V2+ | 35 | (27,21,21,21,20,9) |
| V3- | 13 | (8,8,8,8,5,3) |
| V3+ | 13 | (10,8,8,8,5,3) |
| V4- | 14 | (9,9,9,9,9,4) |
| V4+ | 14 | (11,9,9,9,9,4) |
| V5- | 9 | (6,6,6,5,3,2) |
| V5+ | 9 | (7,6,6,5,3,2) |
| V6- | 28 | (19,19,19,19,10,7) |
| V6+ | 28 | (22,19,19,19,10,7) |
| V7- | 29 | (20,20,20,17,17,8) |
| V7+ | 29 | (23,20,20,17,17,8) |
| V8- | 31 | (22,22,22,22,22,10) |
| V8+ | 31 | (25,22,22,22,22,10) |

The complete joint terminal data follow. For each row divide all three
vectors and $w$ by the same endpoint denominator. Omitted pairs have
weight and all vectors zero. Within a listed pair the three vectors each
have mass $w$; pair weights sum to $d$. The cell $0$ means first queried
zero, equally for $00$ and $01$; cells $10,11$ are distinct.
Labels in a vector indicate its actual support, not a choice of a new
budget or seed. The expanded nineteen tables contain 127 pair rows and
381 terminal vectors.

| Endpoint | Pair | w numerator | T0 numerator | T10 numerator | T11 numerator |
| --- | --- | --- | --- | --- | --- |
| Vbase | 12 | 1 | $e_1$ | $e_2$ | $e_0$ |
| V0- | 12 | 5 | $5e_1$ | $5e_2$ | $3e_0+2e_5$ |
| V0- | 13 | 3 | $2e_0+e_1$ | $3e_3$ | $3e_0$ |
| V0- | 14 | 1 | $e_0$ | $e_4$ | $e_0$ |
| V0- | 23 | 3 | $2e_0+e_2$ | $3e_3$ | $3e_0$ |
| V0- | 24 | 1 | $e_0$ | $e_4$ | $e_0$ |
| V0- | 34 | 3 | $3e_0$ | $3e_4$ | $e_0+2e_5$ |
| V0- | 45 | 1 | $e_0$ | $e_5$ | $e_0$ |
| V0+ | 12 | 5 | $5e_1$ | $5e_2$ | $3e_0+2e_5$ |
| V0+ | 13 | 3 | $3e_1$ | $3e_3$ | $3e_0$ |
| V0+ | 14 | 1 | $e_1$ | $e_4$ | $e_0$ |
| V0+ | 23 | 3 | $2e_0+e_2$ | $3e_3$ | $3e_0$ |
| V0+ | 24 | 1 | $e_0$ | $e_4$ | $e_0$ |
| V0+ | 34 | 3 | $3e_0$ | $3e_4$ | $e_0+2e_5$ |
| V0+ | 45 | 1 | $e_0$ | $e_5$ | $e_0$ |
| V1- | 12 | 5 | $5e_1$ | $5e_2$ | $3e_0+e_4+e_5$ |
| V1- | 13 | 3 | $3e_1$ | $3e_3$ | $3e_0$ |
| V1- | 14 | 1 | $e_0$ | $e_4$ | $e_0$ |
| V1- | 23 | 3 | $2e_0+e_2$ | $3e_3$ | $3e_0$ |
| V1- | 24 | 1 | $e_0$ | $e_4$ | $e_0$ |
| V1- | 34 | 3 | $3e_0$ | $3e_4$ | $e_0+2e_5$ |
| V1- | 45 | 1 | $e_0$ | $e_5$ | $e_0$ |
| V1+ | 12 | 5 | $5e_1$ | $5e_2$ | $3e_0+e_4+e_5$ |
| V1+ | 13 | 3 | $3e_1$ | $3e_3$ | $3e_0$ |
| V1+ | 14 | 1 | $e_1$ | $e_4$ | $e_0$ |
| V1+ | 23 | 3 | $2e_0+e_2$ | $3e_3$ | $3e_0$ |
| V1+ | 24 | 1 | $e_0$ | $e_4$ | $e_0$ |
| V1+ | 34 | 3 | $3e_0$ | $3e_4$ | $e_0+2e_5$ |
| V1+ | 45 | 1 | $e_0$ | $e_5$ | $e_0$ |
| V2- | 12 | 9 | $9e_1$ | $9e_2$ | $6e_0+3e_5$ |
| V2- | 13 | 6 | $6e_1$ | $6e_3$ | $6e_0$ |
| V2- | 14 | 3 | $3e_0$ | $3e_4$ | $2e_0+e_5$ |
| V2- | 23 | 6 | $3e_0+3e_2$ | $6e_3$ | $6e_0$ |
| V2- | 24 | 3 | $3e_0$ | $3e_4$ | $2e_0+e_5$ |
| V2- | 34 | 6 | $6e_0$ | $6e_4$ | $2e_0+4e_5$ |
| V2- | 45 | 2 | $2e_0$ | $2e_5$ | $2e_0$ |
| V2+ | 12 | 9 | $9e_1$ | $9e_2$ | $6e_0+3e_5$ |
| V2+ | 13 | 6 | $6e_1$ | $6e_3$ | $6e_0$ |
| V2+ | 14 | 3 | $3e_1$ | $3e_4$ | $2e_0+e_5$ |
| V2+ | 23 | 6 | $3e_0+3e_2$ | $6e_3$ | $6e_0$ |
| V2+ | 24 | 3 | $3e_0$ | $3e_4$ | $2e_0+e_5$ |
| V2+ | 34 | 6 | $6e_0$ | $6e_4$ | $2e_0+4e_5$ |
| V2+ | 45 | 2 | $2e_0$ | $2e_5$ | $2e_0$ |
| V3- | 12 | 4 | $4e_1$ | $4e_2$ | $2e_0+e_3+e_4$ |
| V3- | 13 | 2 | $2e_1$ | $2e_3$ | $2e_0$ |
| V3- | 14 | 1 | $e_0$ | $e_4$ | $e_0$ |
| V3- | 23 | 2 | $e_0+e_2$ | $2e_3$ | $2e_0$ |
| V3- | 24 | 1 | $e_0$ | $e_4$ | $e_0$ |
| V3- | 34 | 2 | $2e_0$ | $2e_4$ | $e_0+e_5$ |
| V3- | 45 | 1 | $e_0$ | $e_5$ | $e_0$ |
| V3+ | 12 | 4 | $4e_1$ | $4e_2$ | $2e_0+e_3+e_4$ |
| V3+ | 13 | 2 | $2e_1$ | $2e_3$ | $2e_0$ |
| V3+ | 14 | 1 | $e_1$ | $e_4$ | $e_0$ |
| V3+ | 23 | 2 | $e_0+e_2$ | $2e_3$ | $2e_0$ |
| V3+ | 24 | 1 | $e_0$ | $e_4$ | $e_0$ |
| V3+ | 34 | 2 | $2e_0$ | $2e_4$ | $e_0+e_5$ |
| V3+ | 45 | 1 | $e_0$ | $e_5$ | $e_0$ |
| V4- | 12 | 4 | $4e_1$ | $4e_2$ | $2e_0+2e_5$ |
| V4- | 13 | 2 | $2e_1$ | $2e_3$ | $2e_0$ |
| V4- | 14 | 1 | $e_0$ | $e_4$ | $e_0$ |
| V4- | 23 | 2 | $e_0+e_2$ | $2e_3$ | $2e_0$ |
| V4- | 24 | 1 | $e_0$ | $e_4$ | $e_0$ |
| V4- | 34 | 3 | $2e_0+e_3$ | $3e_4$ | $e_0+2e_5$ |
| V4- | 45 | 1 | $e_0$ | $e_5$ | $e_0$ |
| V4+ | 12 | 4 | $4e_1$ | $4e_2$ | $2e_0+2e_5$ |
| V4+ | 13 | 2 | $2e_1$ | $2e_3$ | $2e_0$ |
| V4+ | 14 | 1 | $e_1$ | $e_4$ | $e_0$ |
| V4+ | 23 | 2 | $e_0+e_2$ | $2e_3$ | $2e_0$ |
| V4+ | 24 | 1 | $e_0$ | $e_4$ | $e_0$ |
| V4+ | 34 | 3 | $2e_0+e_3$ | $3e_4$ | $e_0+2e_5$ |
| V4+ | 45 | 1 | $e_0$ | $e_5$ | $e_0$ |
| V5- | 12 | 3 | $3e_1$ | $3e_2$ | $e_0+2e_3$ |
| V5- | 13 | 1 | $e_1$ | $e_3$ | $e_0$ |
| V5- | 14 | 1 | $e_0$ | $e_4$ | $e_0$ |
| V5- | 23 | 1 | $e_2$ | $e_3$ | $e_0$ |
| V5- | 24 | 1 | $e_0$ | $e_4$ | $e_0$ |
| V5- | 34 | 1 | $e_0$ | $e_4$ | $e_0$ |
| V5- | 45 | 1 | $e_0$ | $e_5$ | $e_0$ |
| V5+ | 12 | 3 | $3e_1$ | $3e_2$ | $e_0+2e_3$ |
| V5+ | 13 | 1 | $e_1$ | $e_3$ | $e_0$ |
| V5+ | 14 | 1 | $e_1$ | $e_4$ | $e_0$ |
| V5+ | 23 | 1 | $e_2$ | $e_3$ | $e_0$ |
| V5+ | 24 | 1 | $e_0$ | $e_4$ | $e_0$ |
| V5+ | 34 | 1 | $e_0$ | $e_4$ | $e_0$ |
| V5+ | 45 | 1 | $e_0$ | $e_5$ | $e_0$ |
| V6- | 12 | 8 | $8e_1$ | $8e_2$ | $3e_0+4e_3+e_4$ |
| V6- | 13 | 4 | $4e_1$ | $4e_3$ | $3e_0+e_4$ |
| V6- | 14 | 3 | $3e_0$ | $3e_4$ | $3e_0$ |
| V6- | 23 | 4 | $4e_2$ | $4e_3$ | $3e_0+e_4$ |
| V6- | 24 | 3 | $3e_0$ | $3e_4$ | $3e_0$ |
| V6- | 34 | 3 | $3e_0$ | $3e_4$ | $3e_0$ |
| V6- | 45 | 3 | $3e_0$ | $3e_5$ | $3e_0$ |
| V6+ | 12 | 8 | $8e_1$ | $8e_2$ | $3e_0+4e_3+e_4$ |
| V6+ | 13 | 4 | $4e_1$ | $4e_3$ | $3e_0+e_4$ |
| V6+ | 14 | 3 | $3e_1$ | $3e_4$ | $3e_0$ |
| V6+ | 23 | 4 | $4e_2$ | $4e_3$ | $3e_0+e_4$ |
| V6+ | 24 | 3 | $3e_0$ | $3e_4$ | $3e_0$ |
| V6+ | 34 | 3 | $3e_0$ | $3e_4$ | $3e_0$ |
| V6+ | 45 | 3 | $3e_0$ | $3e_5$ | $3e_0$ |
| V7- | 12 | 7 | $7e_1$ | $7e_2$ | $3e_0+2e_3+2e_5$ |
| V7- | 13 | 5 | $5e_1$ | $5e_3$ | $3e_0+2e_5$ |
| V7- | 14 | 3 | $3e_0$ | $3e_4$ | $3e_0$ |
| V7- | 23 | 5 | $5e_2$ | $5e_3$ | $3e_0+2e_5$ |
| V7- | 24 | 3 | $3e_0$ | $3e_4$ | $3e_0$ |
| V7- | 34 | 3 | $3e_0$ | $3e_4$ | $3e_0$ |
| V7- | 45 | 3 | $3e_0$ | $3e_5$ | $3e_0$ |
| V7+ | 12 | 7 | $7e_1$ | $7e_2$ | $3e_0+2e_3+2e_5$ |
| V7+ | 13 | 5 | $5e_1$ | $5e_3$ | $3e_0+2e_5$ |
| V7+ | 14 | 3 | $3e_1$ | $3e_4$ | $3e_0$ |
| V7+ | 23 | 5 | $5e_2$ | $5e_3$ | $3e_0+2e_5$ |
| V7+ | 24 | 3 | $3e_0$ | $3e_4$ | $3e_0$ |
| V7+ | 34 | 3 | $3e_0$ | $3e_4$ | $3e_0$ |
| V7+ | 45 | 3 | $3e_0$ | $3e_5$ | $3e_0$ |
| V8- | 12 | 8 | $8e_1$ | $8e_2$ | $3e_0+e_3+4e_5$ |
| V8- | 13 | 4 | $4e_1$ | $4e_3$ | $3e_0+e_5$ |
| V8- | 14 | 3 | $3e_0$ | $3e_4$ | $3e_0$ |
| V8- | 23 | 4 | $4e_2$ | $4e_3$ | $3e_0+e_5$ |
| V8- | 24 | 3 | $3e_0$ | $3e_4$ | $3e_0$ |
| V8- | 34 | 6 | $3e_0+3e_3$ | $6e_4$ | $3e_0+3e_5$ |
| V8- | 45 | 3 | $3e_0$ | $3e_5$ | $3e_0$ |
| V8+ | 12 | 8 | $8e_1$ | $8e_2$ | $3e_0+e_3+4e_5$ |
| V8+ | 13 | 4 | $4e_1$ | $4e_3$ | $3e_0+e_5$ |
| V8+ | 14 | 3 | $3e_1$ | $3e_4$ | $3e_0$ |
| V8+ | 23 | 4 | $4e_2$ | $4e_3$ | $3e_0+e_5$ |
| V8+ | 24 | 3 | $3e_0$ | $3e_4$ | $3e_0$ |
| V8+ | 34 | 6 | $3e_0+3e_3$ | $6e_4$ | $3e_0+3e_5$ |
| V8+ | 45 | 3 | $3e_0$ | $3e_5$ | $3e_0$ |

**Lemma 133.2 (All 32 words and all 94 independent rows at each endpoint).**
Each table defines a stopped probability-vector kernel at its exact
closed finite cap. It has $p_{11111}(0)=1-\varepsilon$.

**Proof.** For each of the 32 words use the literal sum

$$
p_b^V=\sum_{i<j}\big[(1-b_i)T_{ij}^{0,V}
       +b_i(1-b_j)T_{ij}^{10,V}+b_ib_jT_{ij}^{11,V}\big].
\tag{133.2}
$$

Every vector is nonnegative with its common pair mass, and pair masses
sum to one, so this is a probability vector on every word.
For each first-zero class $n$, define three separate minima

$$
B_{V,n}=\min_{b:n(b)=n}p_b^V(0),\quad
C_{V,n}=\min_{b:n(b)=n}p_b^V(n),\quad
P_{V,n}=\min_{b:n(b)=n}[p_b^V(0)+p_b^V(n)].
\tag{133.3}
$$

The next table gives their exact numerator triples, divided by the same
$d$ as the profile and terminal rows. Each minimum ranges over every
free suffix, including all multiple-zero words. The union minimum is
computed from the union itself, never by splitting it into two minima.
The last column gives the all-positive base numerator.

| Endpoint | n1 (B,C,P) | n2 (B,C,P) | n3 (B,C,P) | n4 (B,C,P) | n5 (B,C,P) | Positive base |
| --- | --- | --- | --- | --- | --- | --- |
| Vbase | (0,1,1) | (0,1,1) | (1,0,1) | (1,0,1) | (1,0,1) | 1 |
| V0- | (7,6,13) | (7,6,13) | (7,6,13) | (10,5,15) | (12,5,17) | 13 |
| V0+ | (4,9,13) | (7,6,13) | (7,6,13) | (10,5,15) | (12,5,17) | 13 |
| V1- | (5,8,13) | (7,6,13) | (7,6,13) | (10,6,16) | (12,4,16) | 13 |
| V1+ | (4,9,13) | (7,6,13) | (7,6,13) | (10,6,16) | (12,4,16) | 13 |
| V2- | (11,15,26) | (14,12,26) | (14,12,26) | (20,12,32) | (24,11,35) | 26 |
| V2+ | (8,18,26) | (14,12,26) | (14,12,26) | (20,12,32) | (24,11,35) | 26 |
| V3- | (4,6,10) | (5,5,10) | (5,5,10) | (7,5,12) | (9,2,11) | 10 |
| V3+ | (3,7,10) | (5,5,10) | (5,5,10) | (7,5,12) | (9,2,11) | 10 |
| V4- | (4,6,10) | (5,5,10) | (5,5,10) | (7,5,12) | (9,5,14) | 10 |
| V4+ | (3,7,10) | (5,5,10) | (5,5,10) | (7,5,12) | (9,5,14) | 10 |
| V5- | (3,4,7) | (3,4,7) | (3,4,7) | (4,3,7) | (6,1,7) | 7 |
| V5+ | (2,5,7) | (3,4,7) | (3,4,7) | (4,3,7) | (6,1,7) | 7 |
| V6- | (9,12,21) | (9,12,21) | (9,12,21) | (12,12,24) | (18,3,21) | 21 |
| V6+ | (6,15,21) | (9,12,21) | (9,12,21) | (12,12,24) | (18,3,21) | 21 |
| V7- | (9,12,21) | (9,12,21) | (9,12,21) | (12,9,21) | (18,9,27) | 21 |
| V7+ | (6,15,21) | (9,12,21) | (9,12,21) | (12,9,21) | (18,9,27) | 21 |
| V8- | (9,12,21) | (9,12,21) | (9,12,21) | (12,12,24) | (18,12,30) | 21 |
| V8+ | (6,15,21) | (9,12,21) | (9,12,21) | (12,12,24) | (18,12,30) | 21 |

Substitution in (133.2) yields every entry of (133.3). For example at
$V_0^-$, the word $00100$ has numerator $(7,6,1,0,3,0)$,
whereas $00110$ has $(7,6,1,0,0,3)$; both have first zero one
and union numerator 13. The minima are over all 16 such suffixes,
not just these two. To reconstruct the complete finite certificate,
enumerate $b=00000,00001,\ldots,11111$ lexicographically, take the
sum (133.2), and, for each zero word with first zero $n$, subtract
$(1-a_n-\varepsilon,a_n-\varepsilon,1-\varepsilon)$ from
$(p_b(0),p_b(n),p_b(0)+p_b(n))$. For $11111$ subtract
$1-\varepsilon$ from $p_b(0)$. All inputs to these sums are literal
rational entries above. Equivalently, the minima table has

$$
B_{V,n}\ge1-a_n^V-\varepsilon_V,\qquad
C_{V,n}\ge a_n^V-\varepsilon_V,\qquad
P_{V,n}\ge1-\varepsilon_V.
\tag{133.4}
$$

The all-positive entries equal $d(1-\varepsilon_V)$.
Thus all 608 word laws and 1,786 separate TV rows across the nineteen
profiles are determined and certified by these joint tables and the
three separate minima. This finite arithmetic establishes endpoints;
the continuum follows from the analytical construction in Section 134.
$\square$

## 134. One continuous mixture for every amplitude and every law

**Theorem 134.1 (All-domain stopped construction).** In the closed ambient
region

$$
\begin{gathered}
1\ge a_1\ge a_2\ge a_3\ge a_4\ge a_5\ge\varepsilon\ge0,
\quad\kappa_3=0,\quad\sigma\ge0,\\
0\le h\le H_{\rm head},\qquad F_i\ge0\quad(1\le i\le5),
\end{gathered}
\tag{134.1}
$$

one continuous nineteen-weight mixture recovers the entire amplitude-cap
profile and gives one common-budget kernel obeying all 94 cap rows,
with $p_{11111}(0)=1-\varepsilon$, $c=H$ and $\beta=1$.

**Proof.** Write $x=a_3-a_4\ge0$, $y=a_4-a_5\ge0$.
Since $M=3a_5+4y+5x\ge0$, $\delta=0$ and
$29\sigma=-3M\ge0$ force $a_3=a_4=a_5=0$.
The hyperplane then gives $\varepsilon=0$, and the head bound gives
$h=0$. This unique point is $V_{\rm base}$, only auxiliary finite data.
Otherwise $\delta>0$. The ratio
$q=(a_3,a_4,a_5)/\delta$ belongs to $P$: its eight inequalities
are order of the late amplitudes, the five cuts, and $\sigma\ge0$.
The scale and head conditions are
$\delta(1+t)\le1$ and $0\le h\le\delta(17-5t+u+v)/29$.
Use the continuous nodal functions $\mu_j(q)$ of (132.3) and define

$$
\lambda_j=\delta\mu_j(q)/\delta_j
         =\delta\mu_j(q)(1+t_j),\qquad
\lambda_{\rm base}=a_2-a_3.
\tag{134.2}
$$

They are nonnegative, and

$$
\sum_j\lambda_j=\delta+a_3,\quad
\lambda_{\rm base}+\sum_j\lambda_j=1,\quad
\sum_j\lambda_j\delta_j=\delta,\quad
\sum_j\lambda_j(a_3^j,a_4^j,a_5^j)=(a_3,a_4,a_5).
\tag{134.3}
$$

The same linear function of these four coordinates recovers
$\varepsilon$. Together with the base profile and total weight one,
this also recovers $a_2$. Since $m\le22/3$,
$H_{\rm head}\ge\delta/3>0$. Set $s=h/H_{\rm head}\in[0,1]$,
and split the ray weights into

$$
\lambda_{j,-}=(1-s)\lambda_j,\qquad
\lambda_{j,+}=s\lambda_j.
\tag{134.4}
$$

The identity $\sum_j\lambda_jH_j=H_{\rm head}$ implies the head
contribution is exactly $sH_{\rm head}=h$; hence these nineteen
weights recover all six coordinates simultaneously. Every equality
case is included: zero weights, $a_2=a_3$, and either head endpoint.
At the base point give it weight one and all other weights zero.
Because $P$ is compact and $0\le\lambda_j\le\delta(1+t_j)$,
all ray and split weights tend uniformly to zero as $\delta\to0$.
Thus this is a continuous origin extension despite the undefined ratio.

Mix all three terminal vectors and pair weights with these same weights,
so $T_{ij}^{\tau}=\sum_V\lambda_VT_{ij}^{\tau,V}$ and
$w_{ij}=\sum_V\lambda_Vw_{ij}^V$. The common cell-mass identities
and $\sum_{i<j}w_{ij}=1$ persist. Equation (133.2) gives
$p_b=\sum_V\lambda_Vp_b^V$. For any fixed first-zero word,

$$
(1-a_n)e_0+a_ne_n
 =\sum_V\lambda_V[(1-a_n^V)e_0+a_n^Ve_n].
\tag{134.5}
$$

This uses the same first-zero label even when an endpoint amplitude
is zero or equals its cap. Each separate row slack in (130.4) is
therefore the same convex mixture of its endpoint slacks. All 94 rows
hold at once, with every suffix and the union row preserved.
At $11111$, $p(0)=\sum_V\lambda_V(1-\varepsilon_V)=1-\varepsilon$.
No separate mixture is chosen for an amplitude, word, event or row.

For coefficients, the support property in every literal table is stable
across endpoints: $T_{ij}^{10}$ is supported only at label $j$, whereas
$T_{ij}^{11}(j)=0$. It persists after mixing. Put
$A_i=\sum_{j>i}T_{ij}^0$, $B_i=\sum_{j>i}T_{ij}^{10}$.
The expansion of (133.2) gives

$$
\begin{aligned}
c&=\sum_iA_i,&\ell_i&=B_i-A_i,&Q_{ij}&=T_{ij}^{11}-T_{ij}^{10},\\
(-Q_{ij})_+&=T_{ij}^{10},&V_i&=B_i,&(V_i-\ell_i)_+&=A_i,\\
H&=\sum_iA_i=c,&
\mathfrak m(A_i)&=\mathfrak m(B_i)=\sum_{j>i}w_{ij},&\beta&=1.
\end{aligned}
\tag{134.6}
$$

Here $H$ is the vector of Definition 108.2, distinct from $H_{\rm head}$.
The fixed supports, rather than mere endpointwise disjointness, justify
the mixed positive-part identity. The kernel has degree at most two
and lies at the closed boundary $c=H$, $\beta=1$ of $\mathscr C_5$.
Theorem 109.1 gives its stopped interpretation in its established scope.
$\square$

## 135. Actual sources, one seed and every prescribed tail

**Theorem 135.1 (Original realization with exact tail error).** For every
full original sequence in (130.2) satisfying the five cuts, the kernel
of Theorem 134.1 has original $O\in\mathcal O_2$ and
$N\in\mathcal N_2$ realizations using the same seed, with identical
handed-tape laws at every source and $e_a(O)=e_a(N)=\varepsilon$.

**Proof.** Use one $U$ uniform on $[0,1)$, independent of the source.
In a fixed order partition it into nineteen intervals of weights
$\lambda_V$, omitting zero intervals. Within a positive interval
rescale its local coordinate to $[0,1)$ and partition it by that
endpoint's rational pair weights. Within a positive pair interval
rescale the same coordinate again to $v\in[0,1)$.
For each of the three cells predeclare a partition of this same $v$
by the rational probabilities $T_{ij}^{\tau,V}/w_{ij}^V$.
Thus $U$ fixes the pair and every possible terminal label before replies;
there is no independent seed at handoff or separate sourcewise choice.
Use half-open intervals in fixed label order with a specified boundary
convention. If the carrier is $[0,1]$, specify any valid pair/table
at the null endpoint one. All executions then have finite case selection.

The stopped rule actually queries the chosen original prime $i$.
If its static answer is zero it emits the cell-$0$ original mark.
Otherwise it actually queries prime $j>i$ and emits the cell-$10$ or
cell-$11$ mark. Its actual count is $K_O=1+q_i(x)\in\{1,2\}$.
The completed rule preselects exactly this same pair from this same $U$,
actually obtains both replies, reconstructs the same stopped cell and
emits the identical mark. If $q_i=0$ its second reply is ignored but
that actual request still counts, so $K_N=2$. This is precisely the
completion of Acquisition Resources, Proposition 90.2. Both hand off
finitely at every seed/source and have zero advice. Original competitors'
arbitrary addresses and repetitions remain covered by 110.2; the
bounded pairs describe these attainers only.

A source with $n(x)\le5$ has one of the 31 checked low words, regardless
of all higher replies and additional zeros. Its selected target is the
one used in (134.5). For every actual $n(x)>5$ its low word is $11111$.
The common output is supported on $\theta_0,\ldots,\theta_5$ with
base mass $1-\varepsilon$ and no mass at the distinct $\theta_{n(x)}$.
The exact supplied identity (110.9) gives

$$
\operatorname{TV}(\widehat\lambda_{O,x},\lambda_x^a)
=\operatorname{TV}(\widehat\lambda_{N,x},\lambda_x^a)
=\max\{\varepsilon,a_{n(x)}\}=\varepsilon.
\tag{135.1}
$$

Monotonicity and $a_6\le\varepsilon$ give the last equality, including
$a_6=\varepsilon$. Every retained tail amplitude remains positive and
unaltered. Each tail cylinder is occupied by Boundaries 35.2; the actual
pattern $111110$ already attains the supremum. No infinite all-positive
source is added. Thus the uniform selected-law error is exactly the cap.
Theorem 110.2 supplies the original correspondence; it is not a new
transport theorem or a restriction of the necessity class.

All constructed tapes lie in $B_1$. The unchanged consumer returns
unknown there. Their laws are finite atomic laws, whose TV distance
from each unchanged original nonatomic $\mu_x$ is one, as in
Acquisition Resources 82.1. The selected-law acquisition result therefore
makes no improvement claim for that consumer or those original targets.
$\square$

**Proposition 135.2 (Continuous laws and measurable realization).** The
constructed finite-law family is continuous in the finite profile,
including its auxiliary base extension. On the fixed original source
its handed-law family is continuous for the metric
$\sup_{x\in X}\operatorname{TV}(\nu_x,\nu'_x)$.
The interval realization is jointly measurable in profile and seed.

**Proof.** Each finite terminal mass is a continuous mixture of fixed
rational vectors. There are only 32 low-word laws, so their maximal TV
variation tends to zero. Every actual source uses one of those laws,
including the same low all-positive law for every tail. The supremum
metric statement follows and is independent of how legal tails vary.
In the fixed hierarchical order a global cut is a branch start plus
$\lambda_V$ times a fixed rational pair/cell cut; each cut is continuous
even when a branch weight becomes zero. Comparisons of $U$ with finitely
many such cuts are Borel measurable. Null boundary conventions and
omitted zero intervals preserve this property. Discrete output labels
need not be pointwise continuous across a cut. These are exact
measurable-existence claims for arbitrary real parameters, with no
effective arbitrary-real arithmetic or exact-real sampling guarantee,
and no processing-time bound. $\square$

**Proof of Theorem 130.2.** Starting from any original $N$ at the cap,
110.2 gives a feasible $\mathscr N_5$ representative; Lemmas 131.2--131.3
give all five cuts. Conversely the retained domain and those cuts imply
(134.1) by (130.6) and the upper residual condition. Theorem 134.1 gives
a point of $\mathcal F_N\cap\mathscr C_5$, 109.1 and 110.2 give
stopped original feasibility, and Theorem 135.1 gives explicit same-seed
attainers. Proposition 90.2 supplies the reverse stopped-to-preselected
implication. This proves every equivalence in (130.5). $\square$

## 136. The auxiliary R6 projection and strict original-source density

**Definition 136.1 (Closed finite ambient projection).** Let
$\overline P\subset\mathbb R^6$, in the amplitude-cap coordinate
order of Definition 133.1, be exactly (134.1), including order, cap
nonnegativity, normalization, C3 equality, sigma nonnegativity, head
bound and all five cuts. Let $R_N,R_O$ be the six-coordinate projections
of feasible original profiles in $\mathcal D_{\rm adj}$, allowing every
prescribed positive monotone vanishing tail satisfying $a_6\le\varepsilon$.

**Theorem 136.2 (Exact closed projection, nineteen vertices and density).**
Within the finite ambient order domain with $\kappa_3=0$, $\sigma\ge0$,
$\overline P$ is exactly the common $\mathscr N_5/\mathscr O_5$
cap-feasible projection. Its extreme points are exactly the nineteen
profiles of Definition 133.1. Moreover

$$
R_N=R_O=\overline P\cap\{a_5>\varepsilon>0,\ \sigma>0\},\qquad
\overline{R_N}=\overline{R_O}=\overline P
\quad\text{in }\mathbb R^6.
\tag{136.1}
$$

**Proof.** Finite score necessity gives the five cuts. The finite
chain-score bound (113.4), applied on $B_5$ with the cap rows, gives
$a_1+2+S-6\varepsilon\le3$, including nonpositive singleton lower
bounds. Thus $h\le H_{\rm head}$. This uses finite rows at cap zero;
it does not invoke positive-cap original transport at the base point.
Theorem 134.1 supplies finite stopped sufficiency throughout
$\overline P$. Its same mixture expresses every profile as a convex
combination of the nineteen endpoints, each of which lies in this
ambient set. Hence their convex hull is exactly $\overline P$.
For a nonbase endpoint, three independent ratio facets determine its
ray, $a_2=a_3$ fixes its scale, and $h=0$ or $h=H_{\rm head}$
fixes its head. These are five independent affine active equalities
within the five-dimensional C3 hyperplane, so the endpoint is extreme.
The base is the unique point with the nonnegative affine coordinate
$\delta=0$, so it too is extreme. The convex-hull identity leaves no
other extreme point.

For strict density take

$$
q_*=(17369/18900,\ 9/10,\ 10417/56700,\ 9907/56700,
                         \ 4127/28350,\ 4177/56700).
\tag{136.2}
$$

It has $\delta=1/10$, ratio $C$, $\kappa_3=0$,
$\sigma=22/1575$, $h=359/18900=H_{\rm head}/2$.
Its margins $1-a_1,a_1-a_2,a_2-a_3,a_3-a_4,a_4-a_5,
a_5-\varepsilon,\varepsilon$ are respectively

$$
(1531/18900,359/18900,40613/56700,17/1890,551/18900,
151/2100,4177/56700),
\tag{136.3}
$$

and its five cut slacks are

$$
(667/675,18589/18900,19169/56700,21199/28350,2059/4725).
\tag{136.4}
$$

All are positive, as are sigma and both head margins.
For any $p\in\overline P$ and $0<t\le1$, $p_t=(1-t)p+tq_*$
stays in $\overline P$ by affine convexity, with all these strict
margins positive. The positive-sign identity and $F_1\ge0$ give
$S_t-6\varepsilon_t\ge4\delta_t/7>0$; the head bound gives
$S_t-6\varepsilon_t\le1-a_{1,t}$. Thus it satisfies the precise
adjacent residual window. Attach the actual tail

$$
a_{5+k,t}=\varepsilon_t/2^{k-1}\qquad(k\ge1).
\tag{136.5}
$$

It is positive, monotone, vanishes, and has $a_{6,t}=\varepsilon_t<a_{5,t}$.
Theorem 130.2 supplies original attainers at each $p_t$, and
$p_t\to p$ as $t\downarrow0$. This proves the closure claim; the
reverse containment follows from necessity and closedness.
The strict projection equality follows from (130.6), since its lower
residual condition is automatic from $F_1$ and its upper condition
from the head bound. Feasibility holds for every allowed attached tail,
not just the illustrative geometric tail.
Zero-cap or nonpositive-amplitude endpoints are finite synthesis and
closure points only. In particular $V_{\rm base}$ is not an original
positive sequence, and original positive-cap transport is never applied
to it. Strict profiles are attained directly, without a limit sampler.
$\square$

## 137. Five necessary bounds without saturation or active-length assumptions

**Theorem 137.1 (Unrestricted original necessary cap bounds).** For every
full sequence $1\ge a_1\ge a_2\ge\cdots>0$ tending to zero, every
$\varepsilon>0$, and every original $A\in\mathcal N_2$ with
$e_a(A)\le\varepsilon$, the following five bounds hold:

$$
\begin{aligned}
45\varepsilon&\ge2a_2+5a_3+8a_4+8a_5-2,\\
22\varepsilon&\ge a_2+3a_3+4a_4+3a_5-1,\\
7\varepsilon&\ge a_3+a_4+a_5,\\
19\varepsilon&\ge a_2+2a_3+3a_4+4a_5-1,\\
46\varepsilon&\ge3a_2+7a_3+7a_4+8a_5-3.
\end{aligned}
\tag{137.1}
$$

They also hold for original $\mathcal O_2$ cap attainers. Addresses,
repetitions, output tapes, actual tails, zero advice, common seed and
finite handoff have the full original scope of Definition 130.1.
There is no saturation, support-mask, five-active or tail-cut premise.
These are necessary conditions, without a sufficiency claim.

**Proof.** First work on full $\mathscr N_5$ with all 32 input words
and arbitrary six-label terminal tables. Use the literal event rows of
Definition 131.1, with scores $J_1,J_2,J_3,J_4,K_5=C_3+J_5$.
Maximize (131.1) over all six labels, with no C3 maximizer restriction.
The complete 16-schedule maximum-cell table is:

| Schedule | J1 | J2 | J3 | J4 | K5 |
| --- | --- | --- | --- | --- | --- |
| empty | (22) | (11) | (4) | (9) | (21) |
| 1 | (8,14) | (4,7) | (2,2) | (3,6) | (8,13) |
| 2 | (8,14) | (4,7) | (1,3) | (3,6) | (8,13) |
| 3 | (8,14) | (5,6) | (2,2) | (3,6) | (9,12) |
| 4 | (10,12) | (6,5) | (2,2) | (3,6) | (9,12) |
| 5 | (16,6) | (8,3) | (3,1) | (6,3) | (14,7) |
| 12 | (2,6,8,8) | (1,3,4,4) | (0,2,1,1) | (1,2,3,4) | (3,5,8,8) |
| 13 | (3,5,7,9) | (2,2,4,4) | (1,1,1,1) | (1,2,3,4) | (4,4,8,8) |
| 14 | (4,4,8,8) | (3,1,4,4) | (1,1,1,1) | (1,2,3,4) | (5,3,7,9) |
| 15 | (8,0,8,6) | (4,0,4,3) | (2,0,1,1) | (3,0,4,3) | (8,0,8,7) |
| 23 | (3,5,7,9) | (2,2,4,4) | (1,0,1,2) | (1,2,3,4) | (4,4,8,8) |
| 24 | (4,4,8,8) | (3,1,4,4) | (1,0,1,2) | (1,2,3,4) | (5,3,7,9) |
| 25 | (8,0,8,6) | (4,0,4,3) | (1,0,2,1) | (3,0,4,3) | (8,0,8,7) |
| 34 | (4,4,8,8) | (3,2,4,3) | (1,1,1,1) | (1,2,3,4) | (5,4,7,8) |
| 35 | (8,0,8,6) | (5,0,4,3) | (2,0,1,1) | (3,0,4,3) | (9,0,8,7) |
| 45 | (10,0,8,6) | (6,0,3,3) | (2,0,1,1) | (3,0,4,3) | (9,0,8,7) |

Every entry is the maximum of all six integer label scores obtained
from the literal 16-row formula (131.1); the 51 cells and 306 scores
for each column are reconstructible without any omitted inputs.
Cell orders are empty, $0,1$, or $00,01,10,11$ as appropriate.
The sums are bounded respectively by $24,12,4,10,24$ for every
schedule. Reverse order swaps $01,10$; a repeated coordinate has the
singleton's reachable $00,11$ information; thus all 31 ordered schedules
of length at most two are covered too. Outputs outside the event labels
would score zero. One seed fixes both schedule and every cell label,
so these pointwise score bounds integrate under one common distribution.
No separate cell budgets or saturation assumptions are used.

The first four target scores and weights are in Lemma 131.3. The fifth is

$$
K_5(\eta)=21+3a_2+7a_3+7a_4+8a_5,\qquad
\sum_r k^{K_5}_r=46.
\tag{137.2}
$$

TV at cap $\varepsilon$ gives each event lower bound
$p_b(E)\ge\eta_b(E)-\varepsilon$. Summing with nonnegative weights
and comparing with the unrestricted score uppers gives exactly (137.1).
Union rows use one event bound and one cap subtraction, not two singleton
subtractions. This argument holds at every real finite profile with the
appropriate targets; it is not an extrapolation from amplitude scans.

For original $0<\varepsilon\le1$, set the actual active length
$L=\max(\{i:a_i>\varepsilon\}\cup\{0\})$. Theorem 110.2 supplies a
cap-feasible common-seed $\mathscr N_L$ kernel at this exact closed cap,
from any original arbitrary-address/full-carrier competitor.
If $L\ge5$, restrict its inputs to $b'=(b,0,\ldots,0)$ with
$b\in B_5$, and send labels $6,\ldots,L$ to zero, fixing labels
$0,\ldots,5$. A low-zero target is fixed; at $b=11111$ and $L>5$
the first zero of $b'$ is six, whose target projects to $e_0$.
For $L=5$ use the existing all-positive row. TV contracts under this
projection. For each fixed seed, high answers in the restricted finite
table are constants zero; deleting those observations and composing the
output with these constants leaves a preselected at-most-two low-coordinate
table under the same seed. It is an algebraic restriction of the
transported representation, not free high observations at an actual
source. In particular when $a_6>\varepsilon$ this comparison kernel is
not claimed to be a low-five original attainer on its actual tails.

If $L<5$, extend the kernel to $B_5$ by ignoring new coordinates and
including labels $J_L$ into $J_5$. For first zero $n\le L$ the old
cap holds. For $n>L$, the law is $p_{1^L}$ with no mass at $n$, and
$a_n\le\varepsilon$. The exact supplied identity (110.9) gives

$$
\operatorname{TV}(p_{1^L},(1-a_n)e_0+a_ne_n)
 =\max\{1-p_{1^L}(0),a_n\}\le\varepsilon.
\tag{137.3}
$$

The all-positive row is preserved. This includes $L=0$, closed
$a_n=\varepsilon$ and all multiple-zero suffixes. The schedule and seed
are unchanged. Thus the full finite argument applies for every actual
active length. Every original amplitude and tail remains in the original
premise, with no summability or extra source-law assumption.
For $\varepsilon\ge1$ the five right sides are at most
$21,10,3,9,22$ while their left sides are at least $45,22,7,19,46$,
so the bounds are trivial; the endpoint one is included.
Finally complete any original stopped rule using Proposition 90.2 with
the same seed and law and at most two actual requests. The original
$N$ necessity therefore applies to it. $\square$

**Corollary 137.2 (A full-class error lower bound).** Every original
$A\in\mathcal N_2\cup\mathcal O_2$ obeys

$$
\begin{aligned}
e_a(A)\ge\max\bigg\{0,&\frac{2a_2+5a_3+8a_4+8a_5-2}{45},
 \frac{a_2+3a_3+4a_4+3a_5-1}{22},\frac{S}{7},\\
&\frac{a_2+2a_3+3a_4+4a_5-1}{19},
 \frac{3a_2+7a_3+7a_4+8a_5-3}{46}\bigg\}.
\end{aligned}
\tag{137.4}
$$

**Proof.** For positive error use $\varepsilon=e_a(A)\le1$ in
137.1; for error zero apply it at every positive cap and let the cap
decrease to zero. This does not assert an attained optimal acquisition.
$\square$

**Proposition 137.3 (Sharp compensation for the fifth score).** On full
$\mathscr N_5$, $C_3+J_5\le24$, hence
$J_5\le9+(15-C_3)$. The coefficient one in this compensation is sharp
for this fixed score. The raw assertion $J_5\le9$ is false off saturation.

**Proof.** The unrestricted maximum table proves the combined bound.
The deterministic pair $35$, with terminal labels $(0,0,5,0)$ on
$(00,01,10,11)$, has C3 cell scores $(5,0,5,4)$ and J5 cell scores
$(4,0,3,3)$, so $C_3=14$, $J_5=10$ and their sum is 24.
It is realized by an original rule preselecting actual primes three and
five, obtaining both replies and emitting $\theta_5$ precisely for
$10$, otherwise $\theta_0$. A source-independent uniform seed may be
ignored; all executions have two actual requests and finite handoff.
It is only a score witness. If the compensation coefficient were
$\alpha$, this table would require $10\le9+\alpha$, so $\alpha\ge1$.
The combined bound proves one sufficient. This is not a claim of an
optimal universal cap projection, cap attainment or an N/O separator.
Since feasible laws satisfy $C_3\ge15-\kappa_3$, they obey
$\kappa_3\ge0$ and $J_5\le9+\kappa_3$. $\square$

**Proposition 137.4 (Lifted facets and the unsaturated identities).**
Let $E_i$ be the left side minus right side of the corresponding bound
(137.1), and $W=(45,22,7,19,46)$. For arbitrary amplitude-cap profiles,

$$
\begin{aligned}
29E_i&=F_i+W_i\kappa_3\quad(1\le i\le5),\\
2\delta+9\kappa_3-7\sigma&=3E_1,\\
29\sigma&=22\delta-3M+18\kappa_3,\\
29(S-6\varepsilon)&=12\delta+M-6\kappa_3.
\end{aligned}
\tag{137.5}
$$

Thus original feasibility requires $F_i+W_i\kappa_3\ge0$ and
$7\sigma\le2\delta+9\kappa_3$. At $\kappa_3=0$ these recover
the five adjacent cuts and $\sigma\le2\delta/7$.
At positive $\kappa_3$ they neither force the seven-pair saturation
mask nor establish stopped sufficiency.

**Proof.** Expand (130.1), (130.3) and the five affine slacks. Every
identity holds on the constant coordinate and each amplitude/cap
coordinate separately. The necessity follows from 137.1. The residual
identity still has positive $M$, with the unsaturated correction shown.
$\square$

## 138. A positive-kappa profile excluded by the new first bound

**Definition 138.1 (Original interior infeasibility profile).** Fix the
entire sequence and cap

$$
\begin{gathered}
a_1=a_2=61/103,\quad a_3=60/103,\quad a_4=59/103,
\quad a_5=54/103,\quad\varepsilon=1443/5974,\\
a_{6+j}=\varepsilon/2^j\qquad(j\ge0).
\end{gathered}
\tag{138.1}
$$

Every amplitude is positive, nonincreasing, bounded by one and tends
to zero. Here $a_6=\varepsilon$ and
$a_5-\varepsilon=1689/5974>0$, so the active length is exactly five.
The actual source, carrier, marked targets and all original competitors
remain as in Definition 130.1.

**Theorem 138.2 (Full original exclusion and bounded nonredundancy).**
At (138.1), both original classes have

$$
e_a(A)\ge224/927=\varepsilon+5/53766>\varepsilon
\qquad(A\in\mathcal N_2\cup\mathcal O_2).
\tag{138.2}
$$

This exclusion is not implied by the independently checked residual
113.2, C3/C4/C5 scalar bounds of Section 122, or any of the prefix
scalar bounds 117.2: all of those have strictly positive slack here.
This is nonredundancy relative only to those specified inequalities.
It is neither an N/O separator nor an assertion that every other
published obstruction misses this profile.

**Proof.** Direct rational substitution gives

$$
\begin{gathered}
\delta=42/103,\quad S=173/103,\quad M=187/103,\quad
\kappa_3=1/206>0,\quad\sigma=372/2987>0,\\
(F_1,F_2,F_3,F_4,F_5)=(-35,318,30,40,135)/103,\\
(E_1,E_2,E_3,E_4,E_5)
=(-25/5974,329/2987,67/5974,99/5974,158/2987).
\end{gathered}
\tag{138.3}
$$

The first bound in (137.4) is $224/927$, giving (138.2).
Its lifted slack is $F_1+45\kappa_3=-25/206$ and its equivalent
sigma slack $2\delta+9\kappa_3-7\sigma=-75/5974$.
The residual values and earlier scalar slacks are

$$
\begin{aligned}
D_3&=5705/5974,&3\varepsilon&=4329/5974,&S-6\varepsilon&=688/2987,\\
1-a_1-(S-6\varepsilon)&=530/2987,&\kappa_3&=1/206,\\
52\varepsilon-4a_2-9a_3-7a_4-9a_5+4&=659/2987,\\
22\varepsilon-2a_2-4a_3-4a_4-2a_5+2&=1373/2987.
\end{aligned}
\tag{138.4}
$$

Thus the profile lies strictly in the residual strip, while the older
three scalar certificates do not exclude it. The sigma value is the
$m=5$ prefix slack; no sigma-zero support theorem is applied.
For every integer $m\ge4$, the cap slack of Theorem 117.2 is

$$
R_m=(m-2)(m+1)\varepsilon-(m-3)a_2
          -(m-2)\sum_{n=3}^m a_n+(m-3).
\tag{138.5}
$$

At $m=4,5,6$ it equals respectively $1531/2987,372/2987,902/2987$.
For $m\ge6$, the actual geometric tail sums to
$\sum_{n=6}^m a_n=2\varepsilon(1-2^{-(m-5)})$, giving

$$
\begin{aligned}
R_m&=\frac{P(m)+2886(m-2)/2^{m-5}}{5974},\\
P(m)&=1443(m-2)(m-1)+2436(m-3)-10034(m-2)\\
 &=1443m^2-11927m+15646.
\end{aligned}
\tag{138.6}
$$

For $m\ge7$, $P(7)=2864>0$ and
$P(m+1)-P(m)=2886(m-1)-7598\ge9718>0$; the tail correction is
positive. Hence every remaining prefix scalar test has positive slack,
by an all-$m$ argument retaining the actual tail, not a finite scan.
There is no $N$ attainer at this cap, so this example excludes both
classes and cannot refute their existential comparison. $\square$

**Lemma 138.3 (Alternative integer validation of the older C4/C5 scalars).**
The following event arrays certify precisely the older inequalities

$$
52\varepsilon\ge4a_2+9a_3+7a_4+9a_5-4,\qquad
22\varepsilon\ge2a_2+4a_3+4a_4+2a_5-2.
\tag{138.7}
$$

They are alternative proof data for those existing scalar bounds,
not additional cap conditions or the new advance in 137.1.

| Word | Event | C4 weight | C5 weight |
| --- | --- | --- | --- |
| 00100 | {0,1} | 3 | 2 |
| 00110 | {0,1} | 1 | 0 |
| 01000 | {0,1} | 2 | 2 |
| 01001 | {0,1} | 1 | 0 |
| 01010 | {0,1} | 2 | 0 |
| 10000 | {0,2} | 3 | 2 |
| 10010 | {0,2} | 2 | 0 |
| 10100 | {2} | 3 | 2 |
| 10110 | {2} | 1 | 0 |
| 11000 | {3} | 6 | 4 |
| 11010 | {3} | 3 | 0 |
| 11100 | {0,4} | 1 | 0 |
| 11100 | {4} | 7 | 4 |
| 11110 | {5} | 9 | 2 |
| 11111 | {0} | 8 | 4 |

**Proof.** Use (131.1) on these literal arrays, over all six labels
without saturation. The full schedule maxima are:

| Schedule | C4 cell maxima | C5 cell maxima |
| --- | --- | --- |
| empty | (23) | (10) |
| 1 | (9,14) | (4,6) |
| 2 | (9,14) | (4,6) |
| 3 | (10,13) | (4,6) |
| 4 | (10,13) | (6,4) |
| 5 | (14,9) | (6,4) |
| 12 | (4,5,9,9) | (2,2,4,4) |
| 13 | (5,4,9,9) | (2,2,4,4) |
| 14 | (6,3,8,10) | (4,0,4,4) |
| 15 | (8,1,9,8) | (4,0,4,4) |
| 23 | (5,4,9,9) | (2,2,4,4) |
| 24 | (6,3,8,10) | (4,0,4,4) |
| 25 | (9,0,9,9) | (4,0,4,4) |
| 34 | (6,4,8,9) | (4,0,4,4) |
| 35 | (9,1,9,8) | (4,0,4,4) |
| 45 | (9,1,9,8) | (6,0,2,4) |

Their unrestricted uppers are 27 and 12, their weight sums 52 and 22,
and target scores respectively
$23+4a_2+9a_3+7a_4+9a_5$ and $10+2a_2+4a_3+4a_4+2a_5$.
The same common-budget event proof gives (138.7). The all-length
restriction/extension proof of 137.1 applies unchanged to each array.
For caps at least one, their right sides are at most 25 and 10 while
the left sides are at least 52 and 22. Thus this validation has full
original scope. It supplies an independent integer justification for
the named older scalar comparisons in (138.4), without strengthening
or replacing their conditions. $\square$

## 139. Supplier attribution and the unchanged universal obligation

**Definition 139.1 (Mathematical responsibility and sources).** The strict
adjacent classification is repo-derived ordinary theory: its added
content is the five saturated cuts, compact ratio geometry, full
nineteen-endpoint common-law construction and exact projection. The
unrestricted theorem is a distinct logical strength derived from the
same event data: five necessary all-length bounds, sharp fixed-score
compensation and the explicit positive-kappa exclusion. Its positive-kappa
necessity does not inherit the saturated support restrictions or
constructive sufficiency.

Theorem 109.1 supplies the probability-vector stopped coefficient
criterion; Theorem 110.2 supplies exact closed-cap feasibility transport
with arbitrary original addresses and full-carrier outputs. Proposition
90.2 in Acquisition Resources supplies the same-seed completion and
counted containment. They are reused within their original scopes.
Theorem 113.2 supplies the residual head bound, Theorem 117.2 the all-$m$
second-head scalars, and Sections 118--129 the sharp sigma-zero family,
score-loss reduction and complete predecessor face. The exact-law
obstruction 112.2 does not preclude a different stopped law at the
same cap. The new existential result concerns such replacements.
The alternative C4/C5 arrays in 138.3 validate existing scalar suppliers;
those inequalities are not counted as additional progress.

Kaniewski, Lee and de Wolf, [*Query complexity in expectation*,
Definition 8 and Theorem 9](https://arxiv.org/html/1411.7280v1), characterize
nonnegative scalar expected outputs by nonnegative literal degree.
Their reverse construction samples a literal monomial and emits a
scaled indicator. It does not give jointly normalized output-vector
terminal budgets or an increasing first-zero-stop replacement at a TV cap.
Hellerstein, Kletenik, Liu and Witter, [*Adaptivity Gaps for the Stochastic
Boolean Function Evaluation Problem*, Section 1](https://arxiv.org/html/2208.03810v1),
study Boolean evaluation with independent random input bits and expected
testing costs. Those objectives and resources differ from uniform law
generation on every actual source with a hard actual-request bound.
The common-seed weighted-event method also has the internal antecedents
in Acquisition Resources, Sections 91, 97, 104, and Section 117 here.
These are bounded source attributions, with no exhaustive overlap,
literary priority or external open-problem-resolution claim.

**Definition 139.2 (Remaining original comparison).** The universal
obligation remains exactly (110.14): for every full original monotone
positive vanishing sequence and every positive closed cap, either prove
$\mathcal F_N\ne\varnothing\Rightarrow\mathcal F_N\cap\mathscr C_L\ne\varnothing$
at its actual active length, or exhibit an original common-seed $N_2$
cap attainer together with a uniform lower certificate against every
original full-carrier arbitrary-address $O_2$ competitor. Caps at least
one have trivial feasibility. The remaining nontrivial work includes
five-active positive-$\kappa_3$ profiles satisfying the known necessary
bounds and the $L\ge6$ comparison. Theorem 130.2 settles its entire
specified adjacent saturated region; Theorem 137.1 shrinks the remaining
feasible intersection gap but supplies no general replacement theorem.
The infeasible profile 138.1 excludes both classes and does not supply
a separator. These are ordinary mathematical statements relative to
ordinary suppliers, without Lean/kernel certification. Real-parameter
existence, continuity and measurability do not assert effective exact
computation or sampling for arbitrary real inputs. The selected marked
laws remain distinct from the unchanged original consumer targets.

## 追加锚（本行以下为增补区）
