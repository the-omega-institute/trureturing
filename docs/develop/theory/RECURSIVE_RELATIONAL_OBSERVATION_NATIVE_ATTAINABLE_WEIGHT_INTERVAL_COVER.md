# Attainable-weight interval covers for native threshold preparation

## 1. Original whole-fiber task and literal complete entries

**Definition 1.1 (source, current row and whole target).** Retain the
original source and observation conventions of [WTF, Definition 1.1][WTF]
and [PCA, Definitions 1.1 and 4.1][PCA]. The source algebra and update are

$$
\mathcal T::=\alpha\mid\beta\mid\langle\mathcal T,\mathcal T\rangle,
\qquad
\rho\alpha=\beta,\quad \rho\beta=\langle\beta,\alpha\rangle,
\quad \rho\langle v,w\rangle=\langle\rho v,\rho w\rangle.
\tag{IC.1}
$$

Every finite absolute original-root address in $\{L,R\}^*$, including
the empty address, is legal. A query returns alpha, beta, branch or
absent; descent beyond a leaf is absent. Equal subtrees at different
addresses retain different occurrences. For a prefix-free cut, a complete
row contains the ordered exterior, every reached occurrence hole, the
entire equality partition of its hidden subtrees, all different-class
disequalities, and every concrete strict-prefix blocking guard. Canonical
class names follow first occurrences after restriction.

At $P=\{L,R\}^3$, fix the perfect depth-three exterior with classes

$$
\{LLL,LRL\}=a,\quad \{LLR\}=b_1,\quad \{LRR\}=b_2,
\quad \{RLL,RRL\}=c,\quad \{RLR\}=b_3,\quad \{RRR\}=b_4.
\tag{IC.2}
$$

Write this complete row as $R_*$. Its six class values are pairwise
different, with the two occurrences of each repeated class retained.
The domain and required whole predecessor target are

$$
\mathcal U_* =\{u\in\mathcal T:R_P(\rho u)=R_*\},
\qquad F(u)=R_P(u).
\tag{IC.3}
$$

This is the entire fiber of finite nonempty ordered trees. There is no
size, depth or interior-shape bound, and every compatible actual inverse
source belongs to the domain.

For six distinct values $x$, its current filling is

$$
\mathscr S(x)=
\left\langle
 \left\langle\langle x_a,x_{b_1}\rangle,
                  \langle x_a,x_{b_2}\rangle\right\rangle,
 \left\langle\langle x_c,x_{b_3}\rangle,
                  \langle x_c,x_{b_4}\rangle\right\rangle
\right\rangle.
\tag{IC.4}
$$

The supplied image grammar is
$\mathcal I=\rho[\mathcal T]=\{\beta,\langle\beta,\alpha\rangle\}
\cup\{\langle y,z\rangle:y,z\in\mathcal I\}$.
Its disjoint parsing cases have inverse
$\delta(\beta)=\alpha$,
$\delta\langle\beta,\alpha\rangle=\beta$, and
$\delta\langle y,z\rangle=\langle\delta y,\delta z\rangle$ for
image children. It satisfies $\delta\rho=\mathrm{id}$ and
$\rho\delta=\mathrm{id}$ on their respective domains. A filling
(IC.4) is an image exactly when all six values are images, or exactly
one right-class value $x_{b_j}$ is alpha, its repeated left partner is
beta, and the remaining values are images. Its actual origin is
$\delta(\mathscr S(x))$. These are the actual-source suppliers recorded
in WTF Definition 1.1; neither inverse nor image membership is a native
operation.

Use the supplied eleven full profiles. On $\Pi_j$, class $b_j$ is
alpha, its partner is beta, and all other class roots are branches.
On $Z_d$, only class $d$ is beta and the other roots are branches;
on $Z_*$ all six roots are branches. Branch class values range over
all allowed branch images. Distinct-class disequalities remain imposed.
The profiles exhaust (IC.3). Their five whole targets are $R_0=R_*$
on every $Z_d,Z_*$ and $R_j$ on $\Pi_j$. With

$$
(q_1,q_2,q_3,q_4)=(LL,LR,RL,RR),
$$

$R_j$ replaces the two sibling holes at $q_jL,q_jR$ by concrete beta
at $q_j$, retains the rest of the exterior and old holes, and restricts
the entire partition canonically. The other occurrence of that repeated
partner remains an old hole. All surviving disequalities and blocking
guards belong to the output.

**Definition 1.2 (unchanged pointwise code and reader).** Fix
$n\ge6$, $3\le k\le n-2$, positive integer positions
$s_1<\cdots<s_n$, and $r\ge0$. Put

$$
w_i=L^{s_i}R,\qquad a_i=LLLw_i,\qquad c_i=s_i+4,
\qquad C_B=\sum_{i\in B}c_i,\qquad W=C_{[n]}.
\tag{IC.5}
$$

For a branch image $B$ set
$\theta_i(B)=\mathbf1_{\{r_B(w_i)=\mathsf{branch}\}}$.
Alpha, beta and absent each contribute zero. The prescribed function on
the whole original fiber is exactly

$$
\sigma_{A,k}(u)=
\begin{cases}
0,&u\in\Pi_1\cup\Pi_2,\\
1,&u\in\Pi_3\cup\Pi_4,\\
\mathbf1_{\{\sum_i\theta_i(x_a)\ge k\}},&u\in Z_{b_3},\\
0,&u\text{ belongs to any other zero profile},
\end{cases}
\qquad A=\{s_1,\ldots,s_n\}.
\tag{IC.6}
$$

The original entries $e_0,e_1$ and all their contents are fixed as in
[PCA, Supplier application 4.3 and Convention 23.2][PCA], equivalently
[WTF, Convention 1.3][WTF]. Write $i_1,i_2$ for the original fixed
order of $\{1,2\}$ in the zero-entry chain; this order is not a design
variable here. The entire running table is

| Original reader state | Absolute literal | alpha | beta | branch | absent |
| --- | --- | --- | --- | --- | --- |
| $e_0$ | $q_{i_1}R$ | $H_{i_1}$ | $H_0$ | $Q_2$ | $H_0$ |
| $Q_2$ | $q_{i_2}R$ | $H_{i_2}$ | $H_0$ | $H_0$ | $H_0$ |
| $e_1$ | $RLR$ | $H_3$ | $H_0$ | $H_4$ | $H_0$ |

The five distinct halts $H_0,\ldots,H_4$ carry literally the complete
rows $R_0,\ldots,R_4$ just defined. Thus the independent reader has
three running states and five whole-row halts, with separate installed
count $K=8$, fresh invocation bound $2$ and fresh letter bound $6$.
Preparation must end at the original latch
$\widehat e_{\sigma_{A,k}(u)}$. Code-only handoff enters that same
literal complete entry on the same source. A different usable encoding
or a root-type answer does not meet this requirement.

**Assumption 1.3 (stationary native apparatus and separate services).**
A native preparer has one source-independent running start, one fixed
absolute word and four fixed successors at each running state, the two
original-entry latches, and all $r$ additional mandated distinct latches.
Its counted current state is its entire changing configuration. Every
installed running, output, unused and latch state counts. Every running
visit costs one invocation and its literal word length, including
constant, root, absent, repeated and postcertificate visits. Actual runs
must terminate correctly on every source in (IC.3); arbitrary fixed
successors, sharing and syntactic union cycles remain permitted.

The original binding of origin, authenticated update and current
register, genuine acquisition of same-version row and code arguments,
version authentication, lawful pre-cut native permission, actual
same-source export, complete access isolation, code-only handoff, lawful
complete entry and stationary truthful service continuity are separate
supplied services, with their original prices. The current register stays
that same $\rho u$ throughout preparation, handoff and reading.
An acquired finite-data description specifies (IC.6); its archive is
inaccessible to the paid common-start preparer. No later epoch, old
source, archive, code reread or fresh binding is supplied by a table.

There is no additional source copy, history, selector, counter, phase,
cursor, clock, reset, rerooting, computed address, equality, inverse,
provenance or source-identity port, or extra work/control register.
Representation of the installed table and connections, address bytes,
initialization, original entry contents, whole-output storage, local
acquired-term work, handoff and service/isolation storage retain separate
costs. Installed control, exported alphabet, finite code length,
microsteps, physical time, memory and energy are distinct quantities.
These are the unchanged premises of [PCA, Assumptions 1.2 and 33.2][PCA]
and [WTF, Assumption 1.5][WTF].

## 2. One complete Boolean graph and its actual live hosts

**Definition 2.1 (complete paid Boolean table).** A graph $P$ has a
finite installed running set $Q$, two distinct terminals $0,1$, one
fixed running start, a coordinate $i(q)\in[n]$ at every $q\in Q$,
and two fixed successors $\delta(q,0),\delta(q,1)$. On input
$\theta\in\{0,1\}^n$ it reads $\theta_{i(q)}$, pays one query
and $c_{i(q)}$ letters, and follows that successor. The sole changing
configuration is its current state. Put $m=|Q|$, including unused states;
the Boolean total installed count is $m+2$.

Require correct termination with output $\mathbf1_{\{|\theta|\ge k\}}$
and both bounds on each input of this same graph:

$$
t_P(\theta)\le n,\qquad J_P(\theta)\le W
\quad(\theta\in\{0,1\}^n).
\tag{IC.7}
$$

Every actual visit is paid, including repeated coordinates at different
states and all visits after certification. No order, leveling,
per-state residual predicate, read-once condition after certification or
union-acyclicity is assumed. A syntactic path with contradictory replies
to one coordinate need not be an actual input path.

An actual history ends just before a query. Its exposed coordinate
support is $S$ and its assignment is $\eta_S$. Let $h$ and $z$ be
the numbers of exposed ones and zeros. It is live when both outputs
still have completions, equivalently when

$$
(h,z)\in V_{\rm count}:=
\{0,\ldots,k-1\}\times\{0,\ldots,n-k\},
\qquad G=|V_{\rm count}|=k(n-k+1).
\tag{IC.8}
$$

For a cell $v=(h,z)$, let $F_v$ be the installed states reached by
actual live histories of that cell, and put

$$
\begin{aligned}
Q_{\rm live}&=\bigcup_v F_v,& b_v&=|F_v|,&
u&=|Q\setminus Q_{\rm live}|,\\
E&=\sum_v(b_v-1),&
d(q)&=|\{v:q\in F_v\}|,&
D&=\sum_{q\in Q_{\rm live}}(d(q)-1).
\end{aligned}
\tag{IC.9}
$$

A state live on one history remains in $Q_{\rm live}$ when another
history reaches it after certification. In particular a paid discriminator
is not automatically an extra member of $u$. These are incidences on
one installed graph, not independently allocated physical batches.

**Convention 2.2 (credited local and native suppliers).** The following
facts are used at their supplied scopes, rather than asserted as new
results of this interval-cover argument.

[SI, Theorem 2.2][SI] gives nonempty $F_v$, freshness of every live
query, query depth $h+z$ at a live history, and the actual fixed-label,
fixed-successor support law. Earlier prefixes of a live history are live.
Every completion of an exposed assignment follows the same prefix.
[PCA, Theorem 35.1][PCA] excludes equal live supports with unequal
hit counts at one host. [PE, Lemma 4.1][PE] excludes properly nested
live supports at a common host.

For incomparable supports $S,T$ of two actual live histories at one
host, with respective hit counts $h<h'$, [PE, Theorem 3.1][PE] supplies
two different necessary implications:

$$
\begin{aligned}
\eta_S|_{S\setminus T}=0
&\ \Longrightarrow\ C_{S\setminus T}\le C_{T\setminus S},
&&\text{PE Theorem 3.1(1)},\\
\eta_T|_{T\setminus S}=1
&\ \Longrightarrow\ C_{T\setminus S}\le C_{S\setminus T},
&&\text{PE Theorem 3.1(2)}.
\end{aligned}
\tag{IC.10}
$$

The old assignments on $S\cap T$ need not agree. To apply these
native suppliers to a Boolean graph in Definition 2.1, use the
full-fiber lift of [WTF, Theorem 4.1][WTF] on that same complete
graph. It installs every coordinate-$i$ state at $a_i$, has the
original code and reader, and satisfies both native caps $n+1,W+3$.
Every actual Boolean history becomes its actual cube history after the
paid profile front. Thus both implications (IC.10), including their
complete-run and postcertificate charges, apply here. There is no
new assumption that a state has a unique residual.

The same WTF theorem gives, for simultaneous uniform budgets,

$$
\mathsf N_{A,k,r}(H,q,\ell)
\quad\Longleftrightarrow\quad
\mathsf B_{c,k}(H-4-r,q-1,\ell-3).
\tag{IC.11}
$$

Here $\mathsf N$ is full-original-fiber native feasibility under
Assumption 1.3, and $\mathsf B$ is the unrestricted Boolean model of
Definition 2.1 with the indicated bounds. The specific projection keeps
reached selected states on the supplied actual cube, bypasses only
cube-constant chains, and fills impossible edges without making them
actual. It has $m\le H-4-r$. No time unrolling, source operation or
read-once normalization is part of this correspondence.

Finally [SI, Theorem 5.2][SI] supplies the exact identity

$$
|Q_{\rm live}|=G+E-D,\qquad m-G=E-D+u.
\tag{IC.12}
$$

## 3. Cheap attainable weights cover the common scan

**Definition 3.1 (attainable-weight interval-cover class).** Retain
all of Definitions 1.2 and 2.1. Partition $[n]$ into fixed disjoint
ordered lists $\mathsf I,\mathsf X,\mathsf Y,\mathsf U,\mathsf V$,
where

$$
|\mathsf I|=p\ge1,\qquad
\mathsf X=(x_1,\ldots,x_b),\quad
\mathsf Y=(y_1,\ldots,y_b),\quad b\ge1,
\qquad |\mathsf U|\ge1,\qquad C_{\mathsf Y}<C_{\mathsf X}.
\tag{IC.13}
$$

The tail $\mathsf V$ may be empty. Lists in set expressions mean their
underlying sets; the tail is distinct from $V_{\rm count}$. For an
ordered list $\mathsf Z$, write $\mathsf Z^{\le t}$ for its first
$t$ coordinates and $\mathsf Z^{<\ell}$ for its first $\ell-1$
coordinates. Define

$$
\pi_X=(\mathsf I,\mathsf X,\mathsf U,\mathsf Y,\mathsf V),
\qquad
\pi_Y=(\mathsf I,\mathsf Y,\mathsf U,\mathsf X,\mathsf V).
\tag{IC.14}
$$

There is a fixed descriptive function
$f:\{0,1\}^{\mathsf I}\to\{X,Y\}$ with this property on every
actual live history. Before depth $p$, the next coordinate is the next
member of $\mathsf I$. At depth $d\ge p$, with completed exposed
$\mathsf I$ assignment $\eta$, the next coordinate is
$\pi_{f(\eta)}(d+1)$. No order condition is imposed after the
history becomes certified.

Let the attainable cheap weights be

$$
\mathcal A=\{a\in\{0,\ldots,p\}:
  \text{some }\eta\text{ has }\operatorname{wt}(\eta)=a
                              \text{ and }f(\eta)=Y\}.
\tag{IC.15}
$$

Require $\mathcal A\ne\varnothing$, and for consecutive elements in
its increasing order require

$$
a<a'\text{ consecutive in }\mathcal A
\quad\Longrightarrow\quad a'-a\le b+1.
\tag{IC.16}
$$

The condition is vacuous for a singleton. No monotonicity of $f$, no
dependence only on weight, and no nondecreasing weight transversal of
the two modes is required. The cost comparison concerns whole blocks,
not their individual positions. List lengths and common-support gap
spans have no uniform bound. All postcertificate freedom of the original
model, including paid repeats, mixed certified/live receivers and
syntactic cycles, is retained subject to (IC.7) and actual termination.
The lists, $f$ and $\mathcal A$ describe the given graph; none is an
accessible selector, history, counter or phase coordinate.

**Theorem 3.2 (whole-graph injection by interval covering).** Every
graph satisfying Definition 3.1 has an injection

$$
\Phi:V_{\rm count}\longrightarrow Q_{\rm live},
\qquad \Phi(h,z)\in F_{(h,z)}.
\tag{IC.17}
$$

Consequently, on that same complete installed graph,

$$
|Q_{\rm live}|\ge G=k(n-k+1),\qquad D\le E,
\qquad m\ge G+u.
\tag{IC.18}
$$

There is no assertion of an attained minimum for each fixed partition
or each fixed nonconstant $f$.

Proof. A live history of depth $d$ follows the first $d$ coordinates
of its prescribed permutation, by Convention 2.2 and the actual-live
rule. We first select and separate representatives at each fixed depth.

During queries in $\mathsf I$ or $\mathsf V$, the exposed support is
the same for both modes. Different cells at that depth have different
hit counts. Equal-support exclusion separates any choices of hosts
from their nonempty $F_{(h,d-h)}$.

During either exchanged block, the depth determines the within-block
position $\ell$. In the early block the two next labels are
$x_\ell,y_\ell$, and in the late block they are $y_\ell,x_\ell$.
They differ because the blocks are disjoint. One installed state has
only one coordinate label, so histories in different modes cannot share
it there. Within a mode the supports agree, and unequal-hit exclusion
again separates different cells. Choose any actual host for each such
cell. This covers every depth except queries in $\mathsf U$.

For a common-scan query write

$$
d=p+b+t,\qquad 0\le t<|\mathsf U|,
\qquad a_- =\min\mathcal A,\quad a_+=\max\mathcal A.
$$

Using integer intervals, (IC.16) implies

$$
\bigcup_{a\in\mathcal A}[a,a+b+t]_{\mathbb Z}
       =[a_-,a_++b+t]_{\mathbb Z}.
\tag{IC.19}
$$

Indeed, consecutive intervals either overlap or have consecutive integer
endpoints, since their starting points differ by at most $b+1\le b+t+1$.
The first and last endpoints give exactly the displayed union. This also
covers a singleton $\mathcal A$.

For each live cell $(h,d-h)$ select an exposed assignment as follows.

| Range of $h$ | Assignment on $\mathsf I$ | Mode and remaining exposed values |
| --- | --- | --- |
| $h<a_-$ | Any assignment of weight $h$ | Mode $X$; all $\mathsf X$ and $\mathsf U^{\le t}$ values zero |
| $a_-\le h\le a_++b+t$ | A weight-$a$ assignment selecting $Y$, where $h\in[a,a+b+t]$ | Mode $Y$; place $h-a$ ones on $\mathsf Y\cup\mathsf U^{\le t}$ |
| $h>a_++b+t$ | Any assignment of weight $h-b-t$ | Mode $X$; all $\mathsf X$ and $\mathsf U^{\le t}$ values one |

Every entry in this table is feasible. In the low range,
$0\le h<a_-\le p$, and no assignment of that weight selects $Y$.
In the high range,

$$
a_+<h-b-t\le p,
$$

where the upper bound follows from $h\le d=p+b+t$.
Again that weight is outside $\mathcal A$, so its mode must be $X$.
In the middle range (IC.19) supplies $a$ and
$0\le h-a\le b+t$, exactly the available capacity. Endpoints are
included, and either extreme range may be empty.

These selected assignments are actual live prefixes. Complete any one
to all coordinates. Along the specified permutation, every earlier
prefix has at most $h$ ones and at most $d-h$ zeros. Since the final
cell is live, every such prefix is live. Induct from the sole fixed
start: a correct graph cannot halt while both outputs have completions;
the actual-live rule fixes its next coordinate; and its fixed successor
follows the assigned reply. Upon completing $\mathsf I$, the prescribed
assignment selects exactly the mode used in the table. This realizes
the whole chosen prefix on that one actual completing input. No claim
about arbitrary syntactic paths is needed.

Let $S_X=\mathsf I\cup\mathsf X\cup\mathsf U^{\le t}$ and
$S_Y=\mathsf I\cup\mathsf Y\cup\mathsf U^{\le t}$.
Representatives within one mode have the same support and different hit
counts, and hence different hosts. This also separates low and high
$X$ representatives from each other. For a low $X$ representative
and a middle $Y$ representative, the first has fewer hits,

$$
S_X\setminus S_Y=\mathsf X,
\qquad S_Y\setminus S_X=\mathsf Y,
\qquad \eta_{S_X}|_{\mathsf X}=0.
$$

If they shared a host, PE Theorem 3.1(1), the first line of (IC.10),
would give $C_{\mathsf X}\le C_{\mathsf Y}$, contradicting (IC.13).
For a middle $Y$ representative and a high $X$ representative,
the latter has more hits and its entire private block $\mathsf X$ is
one. PE Theorem 3.1(2), the second line of (IC.10), would give the
same contradictory inequality. The two applications use different
polarities. They require neither equal old values on $\mathsf I$ nor
equal values on the common exposed part of $\mathsf U$. Thus the
selected hosts at every common-scan depth are pairwise distinct.

It remains to exclude a common host at two different depths. Such
occurrences must have the same next coordinate. A coordinate of
$\mathsf I$, $\mathsf U$ or $\mathsf V$ has only one possible
position in the two permutations, so cannot occur at different depths.
For $x_\ell$, its two possible predecessor supports are exactly

$$
\mathsf I\cup\mathsf X^{<\ell}
\quad\subsetneq\quad
\mathsf I\cup\mathsf Y\cup\mathsf U\cup\mathsf X^{<\ell}.
\tag{IC.20}
$$

They are strictly nested. PE Lemma 4.1 excludes their sharing a live
host. For $y_\ell$ the same argument interchanges $\mathsf X$ and
$\mathsf Y$. These are all coordinates and all possible repeated
positions. Consequently no selected host at one depth is selected at
another. Choose one of the constructed actual hosts at every cell to
obtain (IC.17). Finally (IC.12) gives $D\le E$ and $m\ge G+u$.
The argument compares actual histories of one complete graph, including
its unchanged paid certified traffic. $\square$

**Corollary 3.3 (a necessary coverage hole for shortage in this geometry).**
Retain (IC.13), (IC.14), the actual-live order rule, both original caps,
and $\mathcal A\ne\varnothing$. If $m<G$, then $\mathcal A$ has
two consecutive elements with difference at least $b+2$.

Proof. Otherwise (IC.16) holds and Theorem 3.2 contradicts $m<G$.
This is a necessary condition within the stated geometry. An interval
hole is not a construction of a correct strict-subgrid graph. $\square$

## 4. A complete fixed table with nonmonotone attainable modes

**Definition 4.1 (parameters and redirected prefixes).** For every
integer $g\ge8$, put

$$
\begin{gathered}
p=2g,\qquad n=2p+4=4g+4,\qquad k=p+1=2g+1,
\qquad s_i=i,\quad c_i=i+4,\\
\mathsf I=(1,6,7,\ldots,p+4),\quad
\mathsf X=(4,5),\quad \mathsf Y=(2,3),\quad
\mathsf U=(p+5,p+6,\ldots,2p+4),\quad \mathsf V=\varnothing.
\end{gathered}
\tag{IC.21}
$$

Thus $|\mathsf I|=|\mathsf U|=p$, $b=2$,
$C_{\mathsf X}=17$, $C_{\mathsf Y}=13$ and $c_1=5$.
The symbol $x_1$ denotes coordinate $4$, and $y_2$ coordinate $3$.
Define the weight set and descriptive mode function by

$$
\mathcal E_g=\{0,g-2,g-1,p\}
\cup\{a:2\le a\le g-4,\ a\text{ even}\},
\qquad
f(\eta)=
\begin{cases}
X,&\operatorname{wt}(\eta)\in\mathcal E_g,\\
Y,&\operatorname{wt}(\eta)\notin\mathcal E_g.
\end{cases}
\tag{IC.22}
$$

Use exactly the permutations (IC.14). At depth $d_0=p+2$ specify
two collections of reply prefixes. Here $\eta(1)$ is the value at
the first coordinate of $\mathsf I$, and two-bit words follow the
displayed internal block orders:

| Collection | First-coordinate value | $\mathsf I$ weight | Early block replies | Mode |
| --- | --- | --- | --- | --- |
| $L$ | $\eta(1)=0$ | $g-1$ | $\mathsf X=10$ | $X$ |
| $L$ | $\eta(1)=0$ | $g-2$ | $\mathsf X=11$ | $X$ |
| $H$ | $\eta(1)=1$ | $p-1$ | $\mathsf Y=01$ | $Y$ |
| $H$ | $\eta(1)=1$ | $p-2$ | $\mathsf Y=11$ | $Y$ |

Write $\mathcal C_g$ for all their literal length-$d_0$ reply words,
with no identifications. Every $L$ prefix has counts $(g,g+2)$ and
old $x_1=1$; every $H$ prefix has counts $(p,2)$ and old $y_2=1$.
The old value at coordinate $1$ is respectively zero and one.

**Definition 4.2 (all states, labels and successors of $P_g$).** For
binary words, $|w|$ is length and $\operatorname{wt}(w)$ is weight.
Install precisely the following distinct running states, together with
the two distinct terminals $0,1$.

The retained parent states are

$$
\{q_w:w\in\{0,1\}^{<n},\
       \text{no }c\in\mathcal C_g\text{ is a prefix of }w\}.
\tag{IC.23}
$$

The unique start is $q_\varepsilon$. If $|w|<p$, its coordinate
is $\mathsf I_{|w|+1}$. If $|w|\ge p$, its first $p$ replies
are the assignment $\eta$ on $\mathsf I$, and its coordinate is
$\pi_{f(\eta)}(|w|+1)$. For each reply $e\in\{0,1\}$ set

$$
\delta(q_w,e)=
\begin{cases}
R_\varepsilon,&|w|+1=d_0\text{ and }we\in\mathcal C_g,\\
q_{we},&|w|+1<n\text{ and the first case does not hold},\\
\mathbf1_{\{\operatorname{wt}(w)+e\ge k\}},&|w|+1=n.
\end{cases}
\tag{IC.24}
$$

Install all scan states

$$
\{R_v:v\in\{0,1\}^{<p}\}.
\tag{IC.25}
$$

State $R_v$ queries coordinate $\mathsf U_{|v|+1}$. If
$|v|+1<p$, its reply-$e$ successor is $R_{ve}$. If $|v|+1=p$,
let $j=\operatorname{wt}(ve)$ and use the following fixed successor:

| Weight $j$ of the completed $\mathsf U$ word | Successor |
| --- | --- |
| $0$ | $A_1$ |
| $1\le j\le g-2$ | $J$ |
| $g-1$ | $B_1$ |
| $g$ | $C_1$ |
| $g+1\le j\le p$ | $1$ |

Finally install exactly six exit states:

| State | Coordinate | Zero successor | One successor |
| --- | --- | --- | --- |
| $A_1$ | $4$ | $A_2$ | $J$ |
| $A_2$ | $5$ | $0$ | $1$ |
| $B_1$ | $2$ | $J$ | $B_2$ |
| $B_2$ | $3$ | $0$ | $1$ |
| $C_1$ | $2$ | $B_2$ | $1$ |
| $J$ | $1$ | $0$ | $1$ |

The parent states, scan states, six exits and two terminals are pairwise
different. There are no other installed Boolean states. Word indices,
their weights and $f$ specify the fixed labels and fixed edges of each
separate installed state. They are not online calculations or additional
accessible configuration coordinates. In particular all word-indexed
states are charged individually.

## 5. All actual arrivals, correctness, counts and both caps

**Theorem 5.1 (complete original Boolean consumer).** For every $g\ge8$,
Definition 4.2 is a complete correct terminating graph satisfying every
condition of Definition 3.1. Put

$$
N_L=\binom{2g}{g-1},\qquad N_H=\binom{2g}{2},\qquad T_g=N_L+N_H.
$$

Its exact running-state count and total Boolean installed count are

$$
M_g=2^n-1-T_g(2^{p+2}-1)+2^p+5,
\qquad M_g+2.
\tag{IC.26}
$$

Every input satisfies both $t\le n$ and $J\le W$. The two maxima
are attained together on one input. Moreover

$$
M_g>G=(p+1)(p+4)=(2g+1)(2g+4).
\tag{IC.27}
$$

There is no state-saving or fixed-selector minimum claim.

Proof, closed parent table and actual input partition. The weights
$g-2,g-1$ belong to $\mathcal E_g$, whereas $p-2,p-1$ do not.
Thus all four rows of redirected prefixes have their stipulated actual
modes. Their first-coordinate values separate $L$ from $H$; within
each collection the full reply words are distinct. Their counts lie in
the live rectangle, so all earlier prefixes are live as well.

Before any redirection, the parent queries each coordinate exactly once
in its chosen permutation. A parent reply word therefore has one
exposed assignment and all its complete extensions follow that word.
Every retained $q_w$ is reachable: follow its word from the start and
complete its still-free coordinates arbitrarily. It has no earlier
redirected prefix. At that state the history is live exactly when
$\operatorname{wt}(w)\le p$ and
$|w|-\operatorname{wt}(w)\le p+3$; otherwise it is certified.
Its installed behavior is defined in both cases.

No edge in (IC.24) enters a deleted state. A retained word shorter than
$d_0-1$ has retained children. At length $d_0-1$, precisely the
$\mathcal C_g$ children are redirected. A retained longer word cannot
acquire a new length-$d_0$ prefix by adding one letter. Hence every
other internal child in (IC.24) exists. There is no scan or exit edge
back to a parent state.

It follows that the inputs reaching $R_\varepsilon$ are exactly all
completions of the displayed $L$ and $H$ prefixes. Their unexposed
coordinates are respectively $\mathsf U\cup\mathsf Y$ and
$\mathsf U\cup\mathsf X$, without restrictions. All other inputs
stay in the retained parent tree, make exactly $n$ queries, pay exactly
$W$, and receive the threshold of their actual full assignment from the
last line of (IC.24). Parent visits after certification are included.

Proof, all scan arrivals. Every $R_v$, $|v|=t<p$, is reached by
each $L$ or $H$ prefix completed with the first $t$ values of
$\mathsf U$ equal to $v$. These are all its arrivals, since its only
entrance from the parent is $R_\varepsilon$ and scan edges increase
word length. Write $j=\operatorname{wt}(v)$. The exposed counts are

$$
L:\ (g+j,g+2+t-j),\qquad
H:\ (p+j,2+t-j).
\tag{IC.28}
$$

Consequently an $L$ arrival is live exactly when
$j\le g$ and $t-j\le g+1$, and an $H$ arrival is live exactly
when $j=0$. Every other scan arrival is certified; it nevertheless
executes the full remaining scan and pays for every visit. This also
shows reachability of every scan state, including states with only
certified arrivals. No source-type mark is present in the current state.

At scan entry the true residual thresholds are

$$
L:\ \mathbf1_{\{|\theta_{\mathsf U}|+
                         |\theta_{\mathsf Y}|\ge g+1\}},
\qquad
H:\ \mathbf1_{\{|\theta_{\mathsf U}|+
                         |\theta_{\mathsf X}|\ge1\}}.
\tag{IC.29}
$$

After the entire scan, write $j=|\theta_{\mathsf U}|$. A live
$L$ arrival can only have $j=g-1$ or $g$; a live $H$ arrival
can only have $j=0$. The following cases cover every completion.

If $j=0$, an $L$ input is already certified zero because
$|\theta_{\mathsf Y}|\le2<g+1$. At $A_1$ it reads its old
$x_1=1$, then at $J$ its old coordinate $1=0$, and outputs zero.
An $H$ input needs OR on fresh $\mathsf X$. At $A_1$, a zero
reply goes to $A_2$ and returns $x_2$; a one reply goes to $J$
and returns its old coordinate $1=1$. Thus the same fixed table
computes its OR.

If $1\le j\le g-2$, every $L$ input is certified zero, since
$j+2\le g$, and every $H$ input is certified one. State $J$
reads their old coordinate $1$, respectively zero and one, and gives
exactly these answers.

If $j=g-1$, an $L$ input requires AND on fresh $\mathsf Y$.
At $B_1$, a zero $y_1$ reply goes to $J$ and returns zero; a one
reply goes to $B_2$ and returns $y_2$. Every $H$ input is already
certified one. Its old $\mathsf Y$ is either $01$ or $11$:
the former goes through $J$ and returns one, and the latter through
$B_2$, whose old $y_2=1$ also returns one.

If $j=g$, an $L$ input requires OR on fresh $\mathsf Y$.
State $C_1$ returns one when $y_1=1$, and otherwise $B_2$ returns
$y_2$. An $H$ input is already certified one; its old $y_2=1$
ensures the same table returns one, whether its old $y_1$ is zero
or one. If $j\ge g+1$, both residuals are already one and the
last scan edge directly outputs one.

For completeness, the following table lists all exit arrivals. The
conditions on $j$ refer to the completed scan. Liveness means just
before the indicated exit query.

| Exit | All $L$ arrivals | All $H$ arrivals |
| --- | --- | --- |
| $A_1$ | $j=0$, certified zero, old $x_1=1$ | $j=0$, live, $\mathsf X$ fresh |
| $A_2$ | None | $j=0,x_1=0$, live, $x_2$ fresh |
| $B_1$ | $j=g-1$, live, $\mathsf Y$ fresh | $j=g-1$, certified one, old $\mathsf Y\in\{01,11\}$ |
| $C_1$ | $j=g$, live, $\mathsf Y$ fresh | $j=g$, certified one, old $\mathsf Y\in\{01,11\}$ |
| $B_2$ | $j=g-1,y_1=1$ or $j=g,y_1=0$, live, $y_2$ fresh | $j=g-1,y_1=1$ or $j=g,y_1=0$, certified one, old $y_2=1$ |
| $J$ | $j=0$ after $A_1$, or $1\le j\le g-2$, or $j=g-1,y_1=0$; all certified zero | $j=0,x_1=1$, or $1\le j\le g-2$, or $j=g-1,y_1=0$; all certified one |

Every listed exit is reachable, and there are no other incoming edges.
The table shows why $J$ is never live, while several other exits have
both live and certified arrivals. They are still single installed states.
It also proves the actual-live order condition: $L$ histories continue
along $\mathsf U$ and, if still live, $\mathsf Y$; $H$ histories
continue along $\mathsf U$ and, if still live, $\mathsf X$. Every
query deviating from the prescribed permutation is a paid old-coordinate
query on a certified history. Retained parent live histories already
follow their fixed permutation. All runs terminate, since parent and
scan word lengths increase and exits reach a terminal within two queries.

Proof, exact installed count. The two $L$ rows contain

$$
\binom{p-1}{g-1}+\binom{p-1}{g-2}=\binom p{g-1}=N_L
$$

prefixes. The two $H$ rows contain

$$
\binom{p-1}{p-2}+\binom{p-1}{p-3}
=\binom p{p-2}=\binom p2=N_H.
$$

These elementary Pascal identities count literal prefixes once, rather
than their completing inputs. Start with the complete binary parent
tree of $2^n-1$ running states. Each of the $T_g$ distinct
depth-$d_0$ prefixes removes its entire disjoint running subtree of

$$
2^{n-d_0}-1=2^{p+2}-1
$$

states. Exactly $2^p-1$ scan states and six exits are added. This
proves (IC.26), with both terminals counted separately and no discount
for certified-only or unused states.

All $2^p-1$ parent states of depth less than $p$ are retained. To
check (IC.27) uniformly, the binomial expansion gives
$2^{2g}-1\ge\binom{2g}{3}$, and

$$
\begin{aligned}
\binom{2g}{3}-(2g+1)(2g+4)
 &=\frac{4g^3-18g^2-28g-12}{3}\\
 &\ge\frac{14g^2-28g-12}{3}>0
 \qquad(g\ge8).
\end{aligned}
$$

Thus even this untouched prefix part already exceeds $G$.

Proof, both complete-run budgets. A redirected run pays $d_0=p+2$
parent queries, then all $p$ scan queries, then at most two exit
queries. Thus its total is at most $2p+4=n$. Its letter charge
before the exits is exactly $W-C_{\mathsf Y}=W-13$ on $L$,
and exactly $W-C_{\mathsf X}=W-17$ on $H$. These quantities
include every scan query after certification. The complete bounds are

| Completed scan weight | Exit query bound | Full $L$ letter charge | Full $H$ letter charge |
| --- | --- | --- | --- |
| $j=0$ | $2$ | $W-13+c_4+c_1=W$ | $\le W-17+\max(c_4+c_5,c_4+c_1)=W$ |
| $1\le j\le g-2$ | $1$ | $W-13+5=W-8$ | $W-17+5=W-12$ |
| $j=g-1$ | $2$ | $\le W-13+\max(c_2+c_1,c_2+c_3)=W$ | $\le W-17+\max(c_2+c_1,c_2+c_3)=W-4$ |
| $j=g$ | $2$ | $\le W-13+c_2+c_3=W$ | $\le W-17+c_2+c_3=W-4$ |
| $j\ge g+1$ | $0$ | $W-13$ | $W-17$ |

Here $c_4+c_1=8+5=13=C_{\mathsf Y}$,
$c_2+c_1=6+5=11$, $c_2+c_3=13$, and $c_4+c_5=17$.
The old-bit rechecks at $J$, $A_1$, $B_1$, $B_2$ and $C_1$
have all been charged in their actual paths. Together with the unchanged
parent runs, these rows exhaust every input of this one graph.

Take any $H$ prefix and complete it with
$\mathsf U=0^p$, $\mathsf X=00$. The actual path is
$\mathsf I,\mathsf Y,\mathsf U,\mathsf X$, ending through
$A_1,A_2$. It queries all $n$ different coordinates once, pays $W$,
and stays live until its last query. Its final exposed count before that
query is $(p,p+3)=(k-1,n-k)$. Thus the same input attains both
maxima; they have not been taken from separate optimizers.

Finally $\mathcal A=\{0,\ldots,p\}\setminus\mathcal E_g$ has
minimum $1$ and maximum $p-1$. Among its omitted interior weights,
the only possible consecutive pair is $g-2,g-1$; the even omitted
weights below it are separated by odd retained weights, and $g-3$
is retained. There is no run of three omitted interior weights.
Consecutive cheap weights therefore differ by at most $3=b+1$.
All conditions of Definition 3.1 hold. Along the initial alternating
even and odd weights, the number of changes of mode grows without bound
with $g$. The actual graph still uses only the two permutations (IC.14).
$\square$

## 6. Actual overload and an unbounded late common-support gap

**Definition 6.1 (all-history mass and common cuts).** Use the actual
prefix indices of [SI, Definition 11.2][SI]. A prefix records its finite
sequence of states, queried coordinates and replies, ending just before
a query; different completing inputs following the identical prefix
count once. For a live prefix $H$ of counts $(h,z)$ assign

$$
\omega(H)=\binom{h+z}{h}^{-1},\qquad
\lambda(q)=\sum_{H\text{ actual live prefix ending at }q}\omega(H).
\tag{IC.30}
$$

These are proof weights, not an input distribution or a runtime service.
By SI Lemma 11.3, every cell has total weight one. A state is
both-conflict when every two distinct live prefixes ending there have
both directed intersections between one sets and zero sets nonempty.
SI Theorem 11.4, using the classical nonuniform Bollobás inequality,
then gives $\lambda(q)\le1$.

A depth $d<n$ is common-support if every actual live history of that
depth has the same support. Adjoin the formal endpoint $n$, even if
some runs have already certified. Consecutive common depths $a<b$
define the gap $(a,b)$ and its pool $Q_B$ of live states at internal
depths. SI Theorem 9.3 localizes all live occurrences of each such state
to its one pool. With $e_*=\max(k,n-k+1)$, the remaining late-long
gaps are $b-a\ge5$, $b>e_*$, denoted $\mathcal L_*$.
SI11's class $\mathfrak C$ requires both conflicts at every state in
these pools. [TS, Definition 6.3][TS] permits a terminal span-five
exception $I_5=(n-5,n)$, when this is an actual gap:
$\mathfrak C_5$ requires both conflicts in the
other remaining pools, and $\mathfrak A_5$ requires
$\mathcal L_*\subseteq\{I_5\}$.

**Theorem 6.2 (strict actual overload in a genuinely late long pool).**
For $P_g$, all actual live prefixes at $R_\varepsilon$ are exactly
the $N_L$ prefixes of counts $(g,g+2)$ and the $N_H$ prefixes of
counts $(p,2)$ in Definition 4.1. Consequently

$$
\lambda(R_\varepsilon)
=\frac{\binom{2g}{g-1}}{\binom{2g+2}{g}}
 +\frac{\binom{2g}{2}}{\binom{2g+2}{2}}
=\frac{5g^2}{(2g+2)(2g+1)}>1,
\qquad \lim_{g\to\infty}\lambda(R_\varepsilon)=\frac54.
\tag{IC.31}
$$

Its common-support depths are precisely $0,1,\ldots,p$ and the
formal endpoint $n$. The terminal gap $(p,n)$ has span $2g+4$,
ends after $e_*=p+4$, and contains $R_\varepsilon$ in its pool.
In particular $P_g$ belongs to none of
$\mathfrak C,\mathfrak C_5,\mathfrak A_5$.

Proof. The parent partition and absence of return edges in Theorem 5.1
give exactly the stated entrances to $R_\varepsilon$. They are all
live, and their distinct literal words give distinct actual prefixes.
There are no other entrances at any depth. Apply (IC.30) to them.
Writing the two binomial ratios with common denominator gives
$g(g+2)$ and $2g(2g-1)$ as their numerators, summing to $5g^2$.
Strictness is equivalent to

$$
g^2-6g-2=(g-3)^2-11>0\qquad(g\ge8).
$$

The limit follows by dividing numerator and denominator by $g^2$.
In particular this is actual all-history overload, rather than an
arbitrarily chosen overloaded family of abstract set pairs.

All histories through depth $p$ expose the same successive
$\mathsf I$ prefixes, and no redirection occurs before then.
For later depths compare two actual complete runs. Choose an $L$
prefix, complete $\mathsf U$ with $g-1$ ones, and set
$\mathsf Y=11$. Its run is $\mathsf I,\mathsf X,\mathsf U,
\mathsf Y$, ending through $B_1,B_2$, with total weight $k$.
Before its final query it has $(p,p+3)$, so every query is preceded
by a live history. Compare the $H$ run
$\mathsf U=0^p,\mathsf X=00$ used in Theorem 5.1; it too is
live before every query. Their support sets differ at each depth
$p<d<n$: during the early two coordinates they contain different
partial blocks, during $\mathsf U$ they contain different full early
blocks, and during the late block they still omit different coordinates
until the final exposure. Thus none of these depths is common-support.
This proves the exact list of common depths.

The sole nonsingle-step gap has span $n-p=p+4=2g+4>5$ and
right endpoint $n>p+4=e_*$. State $R_\varepsilon$ occurs at
internal depth $p+2$, so is in that remaining late pool. If the pool
satisfied SI11's both-conflict condition, its state would have mass at
most one, contrary to (IC.31). The gap is not the terminal span-five
exception, so the same contradiction excludes $\mathfrak C_5$;
its late span also directly excludes $\mathfrak A_5$.
An overloaded state does not by itself imply $D>E+u$, and no such
inference has been made. $\square$

## 7. Exclusion of every star or cyclic reblocking

**Theorem 7.1 (no SI12, SI13 or SI14 representation).** The complete
actual-live behavior of $P_g$ admits no representation satisfying
[SI, Definition 13.1][SI] and no representation satisfying
[SI, Definition 14.1][SI], even with different common prefix, block
length, number of blocks, block names, common lists and descriptive
selector, or with additional unused modes. Consequently it admits no
SI12 representation either.

Proof, actual orders fix every weight. For every assignment $\eta$
on $\mathsf I$, put $a=\operatorname{wt}(\eta)$ and set its early
block to $00$. Among the $p$ coordinates of $\mathsf U$ and the
first coordinate of its late block, place exactly $p-a$ ones, and set
the last coordinate to zero. This is possible since $0\le p-a\le p$.
It avoids every redirected prefix: each listed early word in
Definition 4.1 is different from $00$. Thus it stays in the parent
tree, reads its entire prescribed permutation, and has total weight
$p=k-1$. Immediately before the last query its counts are $(p,p+3)$.
Every earlier prefix has counts bounded by these, so every query is
preceded by a live history. We have thereby pinned the complete actual
live permutation for every $\eta$, not merely for one assignment at
each weight. There are exactly two possible complete live permutations,
$\pi_X,\pi_Y$, and both occur. Any full-length entirely live run
must obey (IC.14) by Theorem 5.1.

Consider a hypothetical star or cyclic representation, and let $p'$
be its common-prefix length. It cannot exceed $p$: the two pinned
permutations already have different next coordinates at depth $p$.
It cannot be less than $p$ either. At its first block coordinate, all
these pinned runs would still have the same next coordinate from the
original $\mathsf I$. Distinct star modes or distinct cyclic modes
have different first coordinates, since their early blocks are disjoint.
They would therefore all have to use a single mode. One fixed mode
would force a single complete permutation on these entirely live runs,
contradicting $\pi_X\ne\pi_Y$. Hence $p'=p$, and the new ordered
prefix is exactly $\mathsf I$.

Proof, all star reblockings. The permutations $\pi_X$ and $\pi_Y$
change the positions of exactly the four coordinates in
$\mathsf X\cup\mathsf Y$; every other coordinate keeps its position.
In an SI13 representation with block length $b'$, a center mode and
a noncenter mode differ at exactly $2b'$ coordinates. Two different
noncenter modes differ at exactly $3b'$ coordinates: the central
block and the two exchanged noncentral blocks form three moved slots.
All these coordinates change position, since the ordered blocks are
disjoint. The latter number cannot equal four. Thus one of the two
actually used modes is the center, the other is a noncenter mode, and
$2b'=4$, so $b'=2$.

Their two early ordered blocks must be the actual first two labels
after $\mathsf I$, namely $\mathsf X$ and $\mathsf Y$. The
center block is therefore one of those two, and its exchanged block is
the other. SI13's componentwise increasing costs make the center block
cheaper. It cannot be $\mathsf X=(4,5)$ rather than
$\mathsf Y=(2,3)$, since each coordinate of $\mathsf X$ is more
expensive. Hence $\mathsf Y$ must be center mode zero, and
$\mathsf X$ a mode $j>0$.

But at weight zero the unique $\mathsf I$ assignment selects
$\mathsf X$, whereas every weight-one assignment selects
$\mathsf Y$, by (IC.22). The pinned entirely live runs force those
values also in the proposed representation. Any nondecreasing
transversal $\gamma$ required by SI13 would have to satisfy
$\gamma(0)=j>0=\gamma(1)$, a contradiction. Extra unused blocks
or unused modes cannot alter the first two actual labels or these
forced mode values. This excludes all SI13 reblockings. SI13 Definition
13.1 explicitly contains SI12's two-mode proper-switch class, so the
same conclusion excludes every SI12 reblocking.

Proof, all cyclic reblockings. In an SI14 representation with $v'\ge3$
blocks of length $b'$, two different cyclic modes move every coordinate
of those $v'b'$ blocks. In fact a nonzero cyclic shift changes the
slot of each block, regardless of whether the shift is relatively prime
to $v'$. Coordinates in the common lists keep their positions. The two
actual permutations therefore force $v'b'=4$, whence
$v'=4$, $b'=1$.

If its common list $\mathsf U'$ is nonempty, both modes must have
the same coordinate at query position $p+2$, immediately after their
one-coordinate early block. The actual positions there are $x_2=5$
and $y_2=3$, which differ. If $\mathsf U'$ is empty, all four
rotating coordinates occupy the four consecutive positions after
$\mathsf I$, and different cyclic modes differ at each one. In
particular they must differ at position $p+3$. The actual permutations
both query the original first coordinate of the nonempty $\mathsf U$
there. Both possibilities are contradictory. No cost-transversal choice
can repair these position contradictions. This proves the cyclic
exclusion with all possible reblockings allowed. $\square$

## 8. Full original native lower consumer and explicit lifted table

**Theorem 8.1 (conditional lower and complete full-fiber lift).**
Let a native preparer under Assumption 1.3 be correct on every
$u\in\mathcal U_*$ and satisfy, on every such source, both caps
$n+1,W+3$. If its particular Boolean projection of WTF Theorem 4.1
satisfies Definition 3.1, then

$$
H_P\ge k(n-k+1)+4+r.
\tag{IC.32}
$$

For each $g\ge8$, the exact entire $P_g$ of Definition 4.2 has a
native lift on the whole original fiber with precisely

$$
M_g+4+r
\tag{IC.33}
$$

installed preparation states. Its invocation and letter maxima are
$n+1,W+3$, jointly attained on one actual original source. It produces
literally the original latch for (IC.6) and uses the independent original
reader of Definition 1.2, with its separate $K=8$ and fresh bounds
$2,6$.

Proof, conditional lower. The specified WTF projection is a complete
correct Boolean graph satisfying both caps (IC.7), with
$m\le H_P-4-r$. Its explicit class hypothesis permits Theorem 3.2,
which gives $m\ge G$. Combining proves (IC.32). No class membership
has been inferred from arbitrary native correctness, and another
projection or a chosen representative system is not substituted for
this particular projected graph.

Proof, complete installed lift. For every retained parent state, every
scan state and every exit state of $P_g$ with coordinate $i$, install
the fixed absolute native literal $a_i=LLL L^{s_i}R$. Its four
fixed successors are

$$
(\mathsf{alpha},\mathsf{beta},\mathsf{branch},\mathsf{absent})
\longmapsto(\delta(q,0),\delta(q,0),\delta(q,1),\delta(q,0)).
\tag{IC.34}
$$

The zero successor is installed separately for each of its three
replies. Replace the two Boolean terminals by the original latches
$\widehat e_0,\widehat e_1$; do not count the terminals again.
Add these two distinct running states, and take $D_0$ as the sole
native start:

| Native state | Literal | alpha | beta | branch | absent |
| --- | --- | --- | --- | --- | --- |
| $D_0$ | $RLR$ | $\widehat e_1$ | $q_\varepsilon$ | $T_0$ | $\widehat e_0$ |
| $T_0$ | $RRR$ | $\widehat e_1$ | $\widehat e_0$ | $\widehat e_0$ | $\widehat e_0$ |

Install every one of the $r$ further prescribed distinct latches,
including unused ones. These rows and (IC.23)–(IC.25), the six-exit
table and (IC.34) specify every installed state, literal and all four
successors. The total is $M_g$ selected running states, two profile
states, two original-entry latches and $r$ further latches, proving
(IC.33). No source-dependent mode or weight is evaluated outside these
counted fixed states.

For any actual $u\in Z_{b_3}$, its arbitrary branch image $x_a$
defines the static vector $\theta(x_a)$ of Definition 1.2. The
all-address occurrence identity supplied in WTF Section 2 is

$$
r_{\rho u}(pv)=r_{x_{[p]}}(v)
\quad(p\in\{L,R\}^3,\ v\in\{L,R\}^*).
\tag{IC.35}
$$

It makes each selected native visit exactly the appropriate bit query
under (IC.34), including noncomb shapes, alpha or absent replies,
repeats and certified traffic. Beta at $D_0$ means precisely
$Z_{b_3}$. The resulting selected run is the complete actual Boolean
run on that one vector, so it terminates correctly with its prescribed
entry, and its complete paid costs on that same source are

$$
q_P(u)=1+t_{P_g}(\theta(x_a)),\qquad
\ell_P(u)=3+J_{P_g}(\theta(x_a)).
\tag{IC.36}
$$

If $D_0$ returns alpha, the source belongs to $\Pi_3$ and requires
one. If it returns branch, the only remaining profile requiring one is
$\Pi_4$, recognized by alpha at $T_0$. Every other such profile
requires zero. All four edges are installed also for replies impossible
at those profile roots. This exhausts the other ten profiles; each uses
at most two calls and six letters. Thus the upper covers the full
unbounded fiber, rather than only a selected witness family. Since
$n\ge6$ and $c_i\ge5$, these other routes also fit $n+1,W+3$.

For joint attainment, the simultaneous actual cube supplier of
[PCA, Lemma 24.1][PCA], recorded in WTF Supplier 2.1, realizes the
$H,\mathsf U=0^p,\mathsf X=00$ vector of Theorem 5.1 as one
actual finite source in $Z_{b_3}$. More explicitly, with
$G_0=\langle\beta,\beta\rangle$ and
$C_0=G_0$, $C_{m+1}=\langle C_m,\beta\rangle$, choose
$m\ge s_n$ and replace the beta at each selected prefix-free word
$w_i$ by $G_0$ exactly when the chosen bit is one. Call the resulting
branch image $B_\theta$. Choose distinct branch images for
$x_c,x_{b_1},x_{b_2},x_{b_4}$ avoiding $B_\theta$, set
$x_a=B_\theta$, $x_{b_3}=\beta$, and use the actual origin
$\delta(\mathscr S(x))$. All repeated occurrences and six-class
disequalities are satisfied. The indicator vector is the selected
$\theta$, so (IC.36) attains $n+1$ and $W+3$ on that same source.
The inverse and word descriptions in this existence proof are not
operations of the apparatus.

At every source the resulting latch is precisely
$\widehat e_{\sigma_{A,k}(u)}$. Handoff enters the unchanged
complete $e_0$ or $e_1$ from Definition 1.2. The independently priced
reader then returns the entire predecessor row: ordered exterior,
occurrences, full equality partition, repeated partners, different-class
disequalities and strict-prefix blocking guards. Its fixed three
running states, five whole-row halts, literals and four successor
columns remain exactly the displayed original table. Its fresh calls
and letters are additional charges; they have not been absorbed into
the preparation count or caps.

Every finite original address and all four replies retain their original
meaning and permission. Binding, source epoch and same-version acquired
data, authentication, export, isolation, code-only handoff, complete
entry and stationary continuity retain Assumption 1.3's separate service
boundaries and prices. This construction grants no archive or code
reread, source copy, selector, counter, phase, time coordinate, computed
address, reset or additional work/control state. $\square$

## 9. Mathematical dependence and the unrestricted alternatives

**Convention 9.1 (attribution and extent of the composition).** The
interval-cover theorem and its complete consumers are repo-derived
ordinary-paper deductions. Their new composition is (IC.19)'s attainable
cheap interval selection with two differently oriented private-cost
exclusions, yielding (IC.17) on the whole graph without a monotone
weight transversal. Theorems 5.1–8.1 give an original-model consumer
with actual overload and unbounded late span outside every SI12–SI14
reblocking as well as SI11's qualified capacity classes. They do not
assert containment of the whole SI13 or SI14 class.

SI Theorems 2.2 and 5.2 own actual incidence and its accounting identity.
PE Theorem 3.1(1),(2), PE Lemma 4.1 and PCA Theorem 35.1 own all
local private-cost and support exclusions. SI12–SI14 supply the
actual-representative realization method, fixed-label depth separation,
full parent-tree and deleted-subtree count templates. Their binomial
normalization and PE's paid old-marker AND/OR motifs are reused.
WTF Theorem 4.1 owns the native resource correspondence, and PCA/WTF
own the original profiles, actual cube supplier and complete reader.
Neither the exponential table template nor the $+4+r$, $+1$, $+3$
overheads are additional mathematical discoveries here. TC Sections
1–9, the strict-short-block results and TS compensation remain applicable
at their stated scopes; they are not graph classes excluded by this
construction and are not reproved by the interval argument.

For the set-system comparison, [Király–Nagy–Pálvölgyi–Visontai,
Definition 1.1][KNPV] requires fixed set sizes, disjoint diagonal pairs,
and at least one of the two directed cross intersections for each pair.
It does not require both. [Scott–Wilmer, Theorem 4.2][SW] requires
every ordered off-diagonal intersection for the reciprocal-binomial
capacity used in SI11. Their Corollary 4.6 permits a specified skew
direction only together with nondecreasing first-set sizes and
nonincreasing second-set sizes. These are literature-attested suppliers
and applicability boundaries. An abstract weak or skew set family
supplies neither actual fixed successors nor an original all-input cost
or installed-state bridge. The proof of Theorem 3.2 instead uses the
explicit two PE implications on actual histories. Bounded comparison
with these sources implies no worldwide priority or absence result.

**Open problem 9.2 (the original collective target).** The class
hypotheses of Definition 3.1 are not proved for arbitrary original
competitors. In the general range $\min(k,n-k+1)\ge4$, retain both
unrestricted alternatives: prove the original collective grid lower
bound at both caps on every complete correct graph, or construct one
complete correct strict-subgrid graph at both caps.

In the notation of SI Sections 9–11, let $E_B,D_B$ be the actual
cell-incidence excess and duplication in the common-support pool $B$,
let $E_{\rm cut}$ be cut excess, and let
$\mathcal A_*=\mathcal B\setminus\mathcal L_*$. The exact
remaining general inequality is SI.59,

$$
\sum_{B\in\mathcal L_*}(D_B-E_B)
\le E_{\rm cut}+u+
           \sum_{B\in\mathcal A_*}(E_B-D_B).
\tag{IC.37}
$$

Equivalently, with

$$
O_*=\sum_{B\in\mathcal L_*}\sum_{q\in Q_B}(\lambda(q)-1)_+,
\qquad
S_*=\sum_{B\in\mathcal L_*}\sum_{q\in Q_B}(1-\lambda(q))_+,
$$

the unresolved SI.83 target is

$$
O_*\le S_*+E_{\rm cut}+u+
              \sum_{B\in\mathcal A_*}(E_B-D_B).
\tag{IC.38}
$$

These are collective inequalities on one graph. Separate compensation
in each remaining late gap would be stronger than required. Neither
strict overload (IC.31) nor an interval-cover hole proves a deficit
violating them. No marginal-flow lift, independently selected optimum,
free residual entry or state-count-cell allocation is substituted for
the actual joint table.

The equivalent [TC, Theorem 9.1][TC] target still needs a proof that
every correct $n$-query table with fewer than $G$ installed running
states has a nonzero actual-full-length-run cost obstruction. TC's
sparse alternative for each fixed table already exists; its universal
shortage implication is not supplied here. No state-nonincreasing
transformation into Definition 3.1 is established.

In particular $P_g$ has $M_g>G$ and no state-saving claim. The
unrestricted $n=8,k=4$ interval remains
$17\le m_{\rm exec}\le20$. The unrestricted-budget native
$H_{\min}$, without the two sharp execution caps, is a separate
unresolved optimum. Attainment for every fixed nonconstant mode function
in Definition 3.1 is also not asserted. The original whole fiber,
pointwise code, literal entries and service prices remain fixed in all
these questions. No operation, numerical state bound, source access,
acquisition service, time precision or storage permission is transferred
from a quantum, calibration, stochastic, analytic or expanded-storage
contract. The mathematical tables give no physical acquisition, memory,
energy or total-runtime conclusion.

[SI]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_SUPPORT_INCIDENCE_AND_COUNT_RELAXATION.md
[PE]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_PAID_PRIVATE_EXCHANGE.md
[PCA]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_PRESCRIBED_CODE_ACQUISITION.md
[WTF]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_WEIGHTED_THRESHOLD_FRONTIER.md
[TC]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_THRESHOLD_COST_CERTIFICATES.md
[TS]: FIB_NATIVE_TERMINAL_SPAN_FIVE_STRICT_COMPENSATION.md
[KNPV]: https://domotorp.web.elte.hu/cikkek/setpairs.pdf
[SW]: https://people.maths.ox.ac.uk/scott/Papers/twofamilies.pdf

## 追加锚（本行以下为增补区）
