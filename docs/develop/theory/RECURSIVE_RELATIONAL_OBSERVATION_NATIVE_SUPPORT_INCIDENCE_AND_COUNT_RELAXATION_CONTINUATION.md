# Actual penultimate support and threshold-four incidence compensation

## 21. Original graph and actual penultimate cut

**Assumption 21.1 (one original paid threshold graph).** Retain the
Boolean execution model of [SI, Definition 1.2][SI]. Thus positive
integer positions $s_1<\cdots<s_n$ give the original distinct costs
$c_i=s_i+4$ and $W=\sum_{i=1}^n c_i$. A finite installed running set
$Q$ has a fixed start, a fixed queried coordinate $i(q)\in[n]$ and
two fixed successors $\delta(q,0),\delta(q,1)$ at each state. The two
output terminals lie outside $Q$. The current state is the entire
changing configuration. Every input $\theta\in\{0,1\}^n$ terminates
with output $\mathbf1_{\{|\theta|\ge K\}}$ and, on that same input,
satisfies both

$$
t_P(\theta)\le n,\qquad
J_P(\theta)=\sum_{\text{all running visits }q}c_{i(q)}\le W.
\tag{SI.155}
$$

Put $L=n-K+1$, so $n=K+L-1$, and assume $K,L\ge3$.
All $m=|Q|$ installed states count, including unused states. Adaptive
coordinate order, shared states, repeated queries, paid queries after
certification, and cycles in the union graph remain allowed. Only
actual runs must terminate; an inconsistent syntactic path need not be
an actual run. There is no additional counter, history, clock, phase or
address register.

**Definition 21.2 (inherited incidence and a genuine right cut).** Use
the actual live histories, their exposed assignments, and
$V=\{0,\ldots,K-1\}\times\{0,\ldots,L-1\}$ from
[SI, Definition 2.1][SI]. In particular $F_p$ is the set of hosts of
cell $p=(h,z)$, $b_p=|F_p|$, and $a_p$ counts its actual supports.
Use the complete common-support cut list and consecutive gaps
$\mathcal B$ of [SI, Definition 9.1][SI], including its adjoined
formal endpoint $n$. For a gap $B=(a,b)$, retain

$$
\begin{aligned}
V_B&=\{(h,z)\in V:a<h+z<b\},\qquad
Q_B=\bigcup_{p\in V_B}F_p,\\
E_B&=\sum_{p\in V_B}(b_p-1),\qquad
D_B=\sum_{q\in Q_B}\bigl(|\{p\in V_B:q\in F_p\}|-1\bigr).
\end{aligned}
\tag{SI.156}
$$

The hypothesis $B=(a,n-1)\in\mathcal B$ requires an actual common
support $R=T_{n-1}$, of size $n-1$. Write $[n]\setminus R=\{j\}$.
It is stronger than merely using the formal endpoint $T_n=[n]$.
Supports, depths and count cells are mathematical indices of actual
histories, not accessible configuration of $P$.

The supplied laws used below are [SI, Theorem 2.2][SI] (live freshness,
actual fixed successors, $b_p\ge a_p\ge1$, and unique axis hosts),
[SI, Lemma 9.2][SI] (actual live extension and support envelopes), and
the local exclusions summarized in [SI, (SI.7)][SI]. The latter exclude
nested supports at a common host, equal supports with unequal hits,
and different cells with equal hits; for a shared pair oriented by
$h<g$, they require $g-h\ge2$ and $z-w\ge2$. Their original
suppliers are PCA Theorems 34.3 and 35.1, PE Lemma 4.1 and WTF
Convention 6.1 and Theorem 9.1, at the interfaces cited in SI Section 2.
Both caps and the original costs in Assumption 21.1 remain hypotheses
of these supplied laws. No all-history both-conflict condition is added.

## 22. Localization and strict compensation

**Theorem 22.1 (threshold-four sharing at an actual penultimate cut).**
Under Assumption 21.1 let $K=4$, $L\ge3$, $n=L+3$, and suppose
$B=(a,n-1)\in\mathcal B$ has span $n-1-a\ge5$. Every state in
$Q_B$ hosting distinct cells of $V_B$ is incident to
$p_*=(1,L-1)$. With $N=b_{p_*}$, on this same graph,

$$
D_B\le N,\qquad E_B\ge N-1+L-a,
\qquad E_B-D_B\ge L-a-1\ge2.
\tag{SI.157}
$$

Necessarily $1\le a\le L-3$. In particular the antecedent is empty
for $L=3$; no existence or sharpness of these gaps is asserted.

Proof. First record what the actual right cut forces. Every earlier
live support is contained in $R$ by live extension to depth $n-1$.
At any live depth less than $n-1$, its next coordinate also belongs
to $R$, by the same extension. At depth $n-1$ the counts are
$(3,L-1)$ and freshness forces query $j$. Both assignments of $j$
extend that history. The query cap and correctness force the two
successors to be the respective output terminals: a running successor
would make that actual input use more than $n$ queries.

Consequently, from any live history with three ones, assigning all
unread coordinates of $R$ zero and assigning $j=1$ gives an actual
positive continuation. It stays live until $j$: before that query it
has three ones and at most $L-1$ zeros. It therefore exposes every
coordinate outside its old support once, with $j$ last, and halts
immediately after $j=1$.

Consider two actual live histories at the same state with counts
$(h,z)$ and $(3,w)$, where $h<3$, and respective supports $S,T$.
Write $X=S\setminus T$ and $Y=T\setminus S$. Suppose the lower
history has no old one in $X$. Take the positive continuation just
described for the upper history. Its queried coordinates are exactly
$[n]\setminus T$, all with reply zero except $j=1$. Construct a
lower completion keeping its assignment on $S$, giving zero to $Y$,
and using those same replies on $[n]\setminus(S\cup T)$.
Every queried coordinate in $X$ agrees with its old lower value zero;
$j$ is outside both supports. Thus this is a consistent input which,
from the shared state, follows the entire upper continuation and
returns one. Its total weight is $h+1\le3$, a contradiction. Hence
the lower history must have an old one in $S\setminus T$.

This excludes row-$0$/row-$3$ sharing. Row-$0$/row-$2$ sharing is
also impossible: give their common next query reply one. Both children
are live at the actual common successor, now in rows $1$ and $3$.
The lower child's unique one is the newly queried coordinate, which
belongs to both child supports. Its private old coordinates are all
zero, contradicting the preceding conclusion. By (SI.7), the only
remaining row pair is therefore $1,3$. For any such pair the lower
history's unique old one is private.

Fix such a pair, with cells $(1,z),(3,w)$, supports $S,T$, and
$z-w\ge2$. Append $t=L-1-z$ common zero replies. Every prefix is
live on both histories: the lower zero count never exceeds $L-1$,
and the upper zero count never exceeds $w+t\le L-3$. Fixed
successors and freshness make this a consistent actual continuation
of each history. If $C$ is its exposed coordinate set, then
$C\cap(S\cup T)=\varnothing$. At their resulting common state the
supports are $S'=S\cup C$, $T'=T\cup C$, and the lower cell is
$(1,L-1)$, with $|S'|=L$.

Let $i$ be this state's query. It is fresh for both histories and
lies in $R$. On reply $i=1$ the lower history is live at
$(2,L-1)$, so its next query is the unique coordinate

$$
\{y\}=R\setminus(S'\cup\{i\}).
\tag{SI.158}
$$

Giving $y=1$ takes it to the corner $(3,L-1)$; giving the subsequent
$j=0$ returns zero. In contrast, the upper history already has four
ones after $i=1$. If $y$ were unread there, or already one, this
same suffix $y=1,j=0$ would be consistent with an upper completion
of weight at least four and would return zero. Stationarity forbids
that. Therefore $y\in T'$ and its old upper value is zero.
Freshness at the common query $i$ gives $T'\subseteq R\setminus\{i\}$,
while (SI.158) gives $R\setminus\{i\}=S'\cup\{y\}$. Thus

$$
T'\setminus S'=\{y\},\qquad
T\setminus S=\{y\},\qquad \eta_T(y)=0.
\tag{SI.159}
$$

The second equality follows because the appended coordinates $C$ are
common to both supports. This argument retains the upper history's
paid queries after certification; it uses their fixed successors.

Suppose now that the original $z\le L-2$. Put
$U=[n]\setminus(S\cup T)$. By (SI.159),

$$
|U|=n-(|S|+1)=L+1-z\ge3,\qquad
j\in U,\qquad [n]\setminus S=\{y\}\cup U.
\tag{SI.160}
$$

Construct one lower completion as follows. Preserve its old assignment,
give $y=0$, give one on the first two fresh exposures from $U$, and
give zero on every later exposure from $U$. This adaptive description
defines a single input, not an additional operation of $P$: each new
answer fixes a previously unread coordinate, and every finite prefix
has a total completion. Before the second new one, at most $z+1\le L-1$
zeros have been exposed. Afterwards there are exactly three ones, and
the total number of zeros on the completed input is

$$
z+1+(|U|-2)=L.
\tag{SI.161}
$$

Hence the run remains live until all coordinates have been exposed:
before the second new one the zero threshold is unmet; afterwards
every remaining unread coordinate is zero and is needed to reach
$L$ zeros. Live freshness supplies the next new exposure at each
step, and correctness forbids premature halting. The last coordinate
is $j$. Since $|U|\ge3$, at least two $U$ coordinates precede it,
so $j=0$. The lower run has exactly three ones, uses all $n$
distinct queries, and returns zero immediately at its last query.

Replay its entire suffix from the original upper history at the
shared state. The suffix queries only $\{y\}\cup U$, each once.
Its only coordinate already exposed by the upper history is $y$,
whose reply agrees with the old zero in (SI.159). Give the upper
completion the same $U$ assignment and any values on $S\setminus T$.
It is a consistent total input, so fixed labels and successors reproduce
that entire suffix and its zero output. But it has the upper history's
three old ones and the two new ones in $U$, giving weight at least
five. This contradicts correctness. Therefore $z=L-1$.

It follows that every shared host in $V_B$ is incident to $p_*$.
There are at most two cell incidences at one host: three distinct hit
rows in $\{0,1,2,3\}$ cannot be pairwise separated by at least two,
and different cells in one row cannot share. Each shared state thus
contributes exactly one to $D_B$. Sending it to its incidence in
$F_{p_*}$ is injective, proving $D_B\le N$.

Depth one is common, since its live histories expose the fixed start
coordinate. As $n-1>1$ and the gap is consecutive, $a\ge1$.
The span hypothesis gives $a\le L-3$. The cell $p_*$ lies at the
internal depth $L$ and contributes $N-1$ to $E_B$. The other
$L-a$ internal depths are all noncommon. On each, the diagonal
criterion of [SI, Definition 9.1 and Theorem 4.1][SI] gives a cell
with $a_p\ge2$, and $b_p\ge a_p$ gives at least one excess.
These are different cells on different diagonals of this same graph.
Thus $E_B\ge N-1+L-a$, proving (SI.157). For $L=3$ the required
inequalities $1\le a\le0$ are incompatible. $\square$

## 23. Transposition and the remaining endpoints

**Corollary 23.1 (zero-threshold four).** Under Assumption 21.1 let
$L=4$, $K\ge3$ and $B=(a,n-1)\in\mathcal B$ have span at
least five. Every shared host in $V_B$ is incident to $(K-1,1)$.
Writing $N_0=b_{(K-1,1)}$, one has

$$
D_B\le N_0,\qquad E_B\ge N_0-1+K-a,
\qquad E_B-D_B\ge K-a-1\ge2.
\tag{SI.162}
$$

Necessarily $1\le a\le K-3$, so the $K=3$ case is vacuous.

Proof. Complement inputs, interchange the two reply labels at every
state, and interchange the output terminals. This gives a threshold
graph with parameters $(K',L')=(4,K)$, the same start, installed
states, fixed queried coordinates and original costs. Under the input
bijection its actual state sequences, query counts and letter charges
agree with those of the original graph. Count cells transpose, while
supports, cuts and both quantities in (SI.156) are preserved. Apply
Theorem 22.1 to that graph and transpose its distinguished cell back.
$\square$

**Corollary 23.2 (formal-terminal necessity when the smaller threshold
is four).** Under Assumption 21.1 suppose $\min(K,L)=4$. Every
consecutive gap with $D_B>E_B$ ends at the formal endpoint $n$ and
has span at least six. In particular, an actual common-support depth
$n-1$ suffices for $m\ge KL$. If $m<KL$, the unique terminal gap
$B_{\mathrm{ter}}=(a,n)$ necessarily has

$$
1\le a\le n-6,\qquad D_{B_{\mathrm{ter}}}>E_{B_{\mathrm{ter}}}.
\tag{SI.163}
$$

Proof. Write $M=\max(K,L)$, so $n=M+3$. The supplied
[SI, Theorems 9.4 and 10.4][SI] compensate every span at most four.
[SI, Lemma 10.2][SI] excludes sharing at endpoints $b\le M$.
[SI, Theorem 20.1 and Corollary 20.2][SI] give a positive margin
for every long gap ending at $M+1=n-2$. Theorem 22.1 and Corollary
23.1 give a positive margin at $n-1$. These exhaust the nonterminal
endpoints. Finally [TS, Theorem 4.1][TS], whose hypothesis $K,L\ge4$
holds here, gives $E_B-D_B\ge1$ for a consecutive terminal gap of
span five. Any positive deficit must therefore have the asserted
terminal location and span.

Use the exact same-graph identity [SI, Theorem 9.3, (SI.32)][SI],
with $u=|Q\setminus Q_{\mathrm{live}}|$ and the supplied cut excess:

$$
m-KL=E_{\mathrm{cut}}+u+\sum_{B\in\mathcal B}(E_B-D_B).
\tag{SI.164}
$$

Every nonterminal contribution is now nonnegative. If depth $n-1$
is common, the terminal gap has span one and no internal cells, so
its contribution is zero and $m\ge KL$. If $m<KL$, the terminal
gap must have a positive deficit. Its span gives $a\le n-6$;
the common depth one gives $a\ge1$. $\square$

**Corollary 23.3 (nine-input margins and residual locations).** Under
Assumption 21.1 let $K=4$, $L=6$, $n=9$. Whenever the indicated
penultimate interval is a consecutive common-support gap, its margin is

$$
E_{(1,8)}-D_{(1,8)}\ge4,\qquad
E_{(2,8)}-D_{(2,8)}\ge3,\qquad
E_{(3,8)}-D_{(3,8)}\ge2.
\tag{SI.165}
$$

The only remaining possible positive-deficit gap locations are
$(1,9),(2,9),(3,9)$. At most one is present in a given complete cut
list. This does not assert that any is realizable or has a positive
deficit.

Proof. Substitute $L=6$ and $a=1,2,3$ in (SI.157). Corollary
23.2 excludes every nonterminal endpoint and every terminal span at
most five; equivalently, SI20 excludes endpoint seven and TS Theorem
4.1 excludes $(4,9)$. Its remaining lower endpoints satisfy
$1\le a\le9-6=3$. A complete consecutive cut list has exactly one
gap ending at nine. $\square$

## 24. The conditional collective boundary and mathematical sources

**Definition 24.1 (remaining formal-terminal compensation).** For
$\min(K,L)=4$, let $B_{\mathrm{ter}}$ denote the unique gap ending
at $n$. The still-required whole-table inequality is

$$
D_{B_{\mathrm{ter}}}-E_{B_{\mathrm{ter}}}
\le E_{\mathrm{cut}}+u+
\sum_{B\ne B_{\mathrm{ter}}}(E_B-D_B).
\tag{SI.166}
$$

By (SI.164) this is exactly $m\ge KL$ for the original graph;
every term on its right is nonnegative by Corollary 23.2. It is the
corresponding specialization of [SI, (SI.59) and (SI.83)][SI] and
the lower-bound obligation in [CP, (CP.28)][CP]. Establishing
$D_{B_{\mathrm{ter}}}\le E_{B_{\mathrm{ter}}}$ would suffice but is
stronger: (SI.166) also permits compensation by the other pools,
cut excess and never-live installed states. The formal endpoint supplies
no fixed missing coordinate $j$, so the two replays of Theorem 22.1
do not apply there without an additional hypothesis. In particular
the unrestricted nine-input equality $m_{\mathrm{exec}}=24$ and
the all-position implication of [TC, Theorem 9.1][TC] are not
consequences established here.

Theorem 22.1 and its consumers are repo-derived deductions from the
explicit SI interfaces. SI20 supplies the first late endpoint;
TS Theorem 4.1 supplies terminal span five. The eight-input support
forks of [CE, Lemmas 10.2--10.3][CE] and its critical live count in
Section 12 retain their eight-input scope and, where stated, their
singleton-support hypotheses, distinct from the uniform restriction
(SI.157).
The necessary private-bit conditions inside Theorem 22.1 do not assert
an all-history both-conflict property or a general exclusion of
one-way-sharing pairs.

The comparison with classical branching programs concerns their
different hypotheses. [Bryant, Section 2, Definition 1][Bryant]
requires strictly increasing variable indices on nonterminal edges,
which implies acyclicity. [Cook, Edmonds, Medabalimi and Pitassi,
Section 2.1][CEMP] defines an acyclic graph and requires each
consistent accepting path of a semantic read-once program to query
each variable at most once. Neither restriction is imposed by
Assumption 21.1, and neither citation supplies a size-preserving
normalization for its allowed paid certified traffic. The comparison
with Wegener's BP1 theorem is that of [SI, Section 8][SI]; it is not
an additional unrestricted lower-bound premise. These comparisons
make no literature priority claim. Installed-state count here gives no
physical-memory conclusion.

[SI]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_SUPPORT_INCIDENCE_AND_COUNT_RELAXATION.md
[TS]: FIB_NATIVE_TERMINAL_SPAN_FIVE_STRICT_COMPENSATION.md
[CP]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_COMMON_PREFIX_MEMORY_FRONTIER.md
[TC]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_THRESHOLD_COST_CERTIFICATES.md
[CE]: RECURSIVE_RELATIONAL_OBSERVATION_CRITICAL_EIGHT_INPUT_LOWER_BOUND.md
[Bryant]: https://www.cs.cmu.edu/~bryant/pubdir/ieeetc86.pdf
[CEMP]: https://doi.org/10.4230/LIPIcs.ICALP.2016.36

## 追加锚（本行以下为增补区）

## 25. Two-private-coordinate equality and terminal literal gates

**Definition 25.1 (qualifying actual history pair).** Under Assumption
21.1, let two actual live histories end at the same installed state
$q$. Write their exposed assignments as $\sigma:S\to\{0,1\}$ and
$\rho:T\to\{0,1\}$, with respective hit counts $h,g$. Require

$$
\begin{gathered}
X=S\setminus T,\quad Y=T\setminus S,\quad
I=S\cap T,\quad U=[n]\setminus(S\cup T),\\
|X|=|Y|=2,\qquad g=h+2,\qquad
d=|S|=|T|,\quad z=d-h,\quad w=d-g,\\
u=|U|=n-d-2,\qquad v=K-g,\\
\alpha=|\{i\in X:\sigma_i=1\}|,\qquad
\beta=|\{i\in Y:\rho_i=1\}|,\qquad
\eta=2+\alpha-\beta>0.
\end{gathered}
\tag{SI.167}
$$

Thus $z-w=2$, $v\ge1$, and $0\le\alpha,\beta\le2$.
The pair consists of actual histories on this one graph; support and
count data supply no extra configuration. No existence of such pairs
for every $K,L\ge3$ is assumed.

**Definition 25.2 (signed terminal literal gate).** An installed state
$r$ with label $i(r)=j$ is a positive terminal literal gate when
$\delta(r,0)=\mathsf0$ and $\delta(r,1)=\mathsf1$. It is a negative
terminal literal gate when $\delta(r,0)=\mathsf1$ and
$\delta(r,1)=\mathsf0$. Its signed label is respectively $(j,+)$
or $(j,-)$. Several states may have the same signed label. Starting
at such a state returns respectively $\theta_j$ or $1-\theta_j$
after one paid query.

**Theorem 25.3 (terminal equality and the possible live corner).** For
every pair of Definition 25.1 the integer interval

$$
\mathcal J=
[\max(0,v-\alpha),\ \min(u,v+1-\beta)]\cap\mathbb Z
\tag{SI.168}
$$

is nonempty. For every assignment $\tau:U\to\{0,1\}$ with weight
in $\mathcal J$, the paired completions (SI.171), constructed as in
[PE, Theorem 7.2][PE], have opposite outputs. Their first different reply after $q$
is query $n$ on both actual runs. Its state $r$ is a terminal
literal gate at some $j\in I$ with $\sigma_j\ne\rho_j$.
Its sign is positive for $(\sigma_j,\rho_j)=(0,1)$ and negative
for $(\sigma_j,\rho_j)=(1,0)$.

Every terminal literal gate that is live anywhere on this graph is
positive and hosts only the corner cell
$p_\diamond=(K-1,L-1)$. Its support at every live occurrence is
$[n]\setminus\{j\}$. In particular, with
$Q_{\mathrm{live}}=\bigcup_{p\in V}F_p$, the forced state belongs to
$F_{p_\diamond}\cup(Q\setminus Q_{\mathrm{live}})$; every negative
terminal literal gate belongs to the second set.

More precisely, the shared continuation strictly before its first
different reply queries exactly $u+1$ distinct coordinates. These
form disjoint sets

$$
\begin{gathered}
A\subseteq\{i\in X:\sigma_i=1\},\quad
B\subseteq\{i\in Y:\rho_i=0\},\\
U_0\subseteq\{i\in U:\tau_i=0\},\quad
U_1\subseteq\{i\in U:\tau_i=1\},\\
|B|+|U_0|=L-z,\qquad |A|+|U_1|=v,\\
|A|+|B|+|U_0|+|U_1|=u+1,\\
C_A+C_B+C_{U_0}+C_{U_1}+c_j
\le C_U+\min(C_X,C_Y),\qquad
C_Z=\sum_{i\in Z}c_i.
\end{gathered}
\tag{SI.169}
$$

The last inequality is the original same-input letter-cap consequence;
its sets come from this shared continuation.

Proof. Live freshness and the exact prefix lengths are supplied by
[SI, Theorem 2.2][SI]. Since $z\le L-1$,

$$
u-v=L-1-z\ge0.
\tag{SI.170}
$$

Also $v+1-\beta\ge0$, and
$(v+1-\beta)-(v-\alpha)=\eta-1\ge0$. These inequalities show
that the clipped interval (SI.168) is nonempty. Choose $\tau$ of
weight $t\in\mathcal J$. The paired-completion construction is

$$
\begin{array}{c|cccc}
 & I & X & Y & U\\ \hline
\theta^- & \sigma|_I & \sigma|_X & \rho|_Y & \tau\\
\theta^+ & \rho|_I & \sigma|_X & \rho|_Y & \tau.
\end{array}
\tag{SI.171}
$$

It extends the respective actual prefixes. Its weights are
$|\theta^-|=h+\beta+t\le K-1$ and
$|\theta^+|=g+\alpha+t\ge K$. Determinism preserves each
incoming history. Starting at their common state, fixed labels and
successors give the same continuation until the first different reply.
Correct termination with opposite outputs forces that reply to exist.
The two vectors agree outside $I$, so it is at a coordinate
$j\in I$ with $\sigma_j\ne\rho_j$.

Use the joint-certificate argument of PE Theorem 7.2. Immediately
before this old-coordinate query neither history is live, since a
live occurrence queries a fresh coordinate. The negative input must
therefore already have exposed $L$ distinct zeros, and the positive
input $K$ distinct ones. Let $A,B,U_0,U_1$ consist of all coordinates
of their respective indicated classes queried before the discriminator
in the shared continuation. The only additional zeros for the lower
history can come from $B\cup U_0$; the only additional ones for the
upper history can come from $A\cup U_1$. Consequently

$$
|B|+|U_0|\ge L-z,\qquad |A|+|U_1|\ge v,
\qquad (L-z)+v=u+1.
\tag{SI.172}
$$

These four coordinate classes are disjoint. If $k$ is the number of
shared continuation queries strictly before the discriminator, then
$k\ge u+1$. Each incoming live prefix has exactly $d$ queries.
On each of these same two actual inputs the discriminator thus occurs
at query number at least

$$
d+(u+1)+1=d+u+2=n.
\tag{SI.173}
$$

The cap $t_P\le n$ forces equality throughout. Thus $k=u+1$,
each of those visits queries a different coordinate in the four
certificate classes, and both inequalities in (SI.172) are equalities.
This asserts distinctness within the continuation, not freshness
relative to both incoming supports: coordinates of $A$ and $B$
were already queried on one of the prefixes. The final query $j$
is old on both.

Both runs must halt immediately after that query. Each of its two
different replies therefore has the corresponding output terminal as
its fixed successor. This proves the gate assertion and its sign.
It also shows that there are no other visits after the counted ones.
The incoming charges are exactly $C_S$ and $C_T$. Applying the
letter cap separately to the two complete runs gives, with
$C=C_A+C_B+C_{U_0}+C_{U_1}$,

$$
C_S+C+c_j\le W,\qquad C_T+C+c_j\le W.
\tag{SI.174}
$$

Since $W-C_S=C_Y+C_U$ and $W-C_T=C_X+C_U$, these are the
last inequality of (SI.169), reusing PE's original-cost bookkeeping.
No two independently minimized certificates have been combined.

It remains to classify every possible live occurrence of a terminal
literal gate labelled $j$. If the occurrence has unread set $M$ and
needs $a$ further ones, liveness says $1\le a\le|M|$. Each
coordinate of $M$ is relevant to this threshold residual: fix the
other $|M|-1$ coordinates to have $a-1$ ones, and flip that
coordinate. Both assignments are actual completions of the incoming
history. A one-query literal state depends on at most $j$. If
$j\notin M$ it is constant on these completions, contradicting
liveness; if $|M|>1$ it ignores another relevant coordinate. Hence
$M=\{j\}$, $a=1$, and the residual is the positive literal
$\theta_j$. Its exposed counts are exactly $(K-1,L-1)$.
A negative literal cannot equal this residual. This proves all the
live-incidence assertions. $\square$

## 26. Signed disagreement and one-graph gate capacity

**Definition 26.1 (signed disagreement family).** On one fixed graph
of Assumption 21.1, let $\mathcal E$ be any finite family of
qualifying actual pairs of Definition 25.1. For $e\in\mathcal E$
use its own $I_e,\sigma_e,\rho_e$ and put

$$
\begin{aligned}
\mathcal D_e={}&
\{(j,+):j\in I_e,\ \sigma_{e,j}=0,\ \rho_{e,j}=1\}\\
&\cup\{(j,-):j\in I_e,\ \sigma_{e,j}=1,\ \rho_{e,j}=0\},\\
\tau(\mathcal E)={}&
\min\{|H|:H\subseteq[n]\times\{+,-\},\;
                   H\cap\mathcal D_e\ne\varnothing\ (e\in\mathcal E)\},\\
\nu={}&|Q\setminus Q_{\mathrm{live}}|,\qquad
b_\diamond=b_{(K-1,L-1)}.
\end{aligned}
\tag{SI.175}
$$

Set $\tau(\varnothing)=0$. Each $\mathcal D_e$ is nonempty:
$\sum_{j\in I_e}(\rho_{e,j}-\sigma_{e,j})=\eta_e>0$.
Thus this minimum is defined. Repeated disagreement sets and repeated
signed gate labels are allowed. The number $\nu$ is global to the
original graph, including its unused never-live states.

**Theorem 26.2 (signed transversal capacity).** With Definition 26.1,

$$
b_\diamond+\nu\ge\tau(\mathcal E).
\tag{SI.176}
$$

If the family contains $r$ pairwise disjoint disagreement sets,
the graph has at least $r$ distinct installed terminal literal gates.

Proof. Collect the signed labels of all installed terminal literal
gates in a set $H_P$. For each $e$, Theorem 25.3 supplies a gate
whose signed label lies in $\mathcal D_e$. Thus $H_P$ meets every
$\mathcal D_e$, and $|H_P|\ge\tau(\mathcal E)$. The number of
installed gates is at least $|H_P|$, even when several have the same
label. Every gate live somewhere lies in $F_{(K-1,L-1)}$ by that
theorem. Every other gate lies in $Q\setminus Q_{\mathrm{live}}$.
These two disjoint pools contain at most $b_\diamond+\nu$ gates
in total, proving (SI.176). Pairwise disjoint disagreement sets
require different labels in any hitting set, proving the last claim.
The argument allows one gate to serve many pairs; it assigns no
injective charge from pairs to states. $\square$

## 27. The nine-input formal-terminal consumer

**Corollary 27.1 (exact remaining condition and a sufficient bound).**
Under Assumption 21.1 let $n=9$, $K=4$, $L=6$. Fix the original
positive increasing position tuple and its graph separately; the graph
may depend on that tuple. Suppose its actual consecutive terminal gap
is $B=(a,9)$ with $a\in\{1,2,3\}$. Write

$$
\begin{aligned}
E_B^\circ&=\sum_{p\in V_B,\ p\ne(3,5)}(b_p-1),\\
R&=E_{\mathrm{cut}}+
       \sum_{C\in\mathcal B,\ C\ne B}(E_C-D_C).
\end{aligned}
\tag{SI.177}
$$

Let $\mathcal E$ be any family from Definition 26.1 whose incoming
cells lie in $V_B$. All these quantities refer to this same graph.
Then $R\ge0$, $b_\diamond=b_{(3,5)}\ge2$, and

$$
\begin{aligned}
m&=23+R+E_B^\circ-D_B+b_\diamond+\nu\\
 &\ge23+R+E_B^\circ-D_B+
                    \max\{2,\tau(\mathcal E)\}.
\end{aligned}
\tag{SI.178}
$$

In particular the exact remaining condition for $m\ge24$ on this
graph is

$$
R+E_B^\circ+b_\diamond+\nu\ge D_B+1.
\tag{SI.179}
$$

A sufficient stronger condition is

$$
R+E_B^\circ+\max\{2,\tau(\mathcal E)\}\ge D_B+1.
\tag{SI.180}
$$

Proof. Every other consecutive gap has upper endpoint at most
$a\le3$, so its span is at most three and [SI, Theorem 9.4][SI]
gives $E_C-D_C\ge0$. Each cut excess is nonnegative. This proves
$R\ge0$ without adding margins from a different cut list.
Depth eight is internal to $B$, and hence is noncommon. Its unique
live cell is $(3,5)$. The diagonal criterion in [SI, Definition 9.1
and Theorem 4.1][SI] gives $a_{(3,5)}\ge2$, and SI Theorem 2.2
gives $b_\diamond\ge a_{(3,5)}\ge2$.

The exact identity [SI, Theorem 9.3, (SI.32)][SI] on this graph is
$m-24=R+E_B-D_B+\nu$. Substitute
$E_B=E_B^\circ+b_\diamond-1$ to obtain the equality in (SI.178).
Both $b_\diamond+\nu\ge2$ and Theorem 26.2 apply to this same
quantity, proving its lower bound by $\max\{2,\tau(\mathcal E)\}$.
Rearranging the equality proves (SI.179); replacing its capacity
term by a lower bound proves the sufficiency of (SI.180).
No localization of $\nu$ to a coordinate block is needed or asserted.
$\square$

## 28. Mathematical dependence and the unproved compensation

Theorem 25.3 is a repo-derived equality restriction relative to
Assumption 21.1 and [SI, Theorem 2.2][SI]. [PE, Theorem 7.2][PE]
already supplies paired completions, joint certificates, a paid
common-coordinate discriminator and the original-cost inequalities.
The additional conclusion forces that discriminator to be terminal
and restricts all its possible live incidences. Theorem 26.2 applies
the ordinary hypergraph transversal principle to those restricted
incidences. It does not eliminate the gate-reuse obstruction in
[PE, Proposition 9.1][PE]. The common-cone AND/OR arms of
[CL, Proposition 14.1][CL] retain their own tightness hypothesis;
no private last label is inferred from a merely formal terminal cut.
The exact identity in Corollary 27.1 is supplied SI incidence
bookkeeping, with its one-graph capacity term now bounded by (SI.176).

The classical ingredients are deterministic indistinguishability,
threshold certificates, equality in the query budget, cofactor relevance
and hypergraph transversals. The cofactor viewpoint is compatible with
[Bryant, Section 2, Definition 1][Bryant]; its increasing-index
restriction is not imposed here. The acyclicity and semantic read-once
accepting-path hypotheses of [Cook, Edmonds, Medabalimi and Pitassi,
Section 2.1][CEMP] are likewise absent from Assumption 21.1.
These comparisons provide no normalization or unrestricted lower bound
for this graph model, and imply no literature priority claim.

Neither (SI.179) nor (SI.180) is established for every terminal pool.
The second is a stronger sufficient condition, not an equivalent or
necessary reformulation of the first. Qualifying pairs exclude
$\eta=0$, private sizes other than two, and hit gaps other than two.
Even within this family, many pairs may use a single gate and need
not force a transversal number exceeding two. Thus no bound here
makes $\tau(\mathcal E)$ cover the full deficit $D_B$.
The whole-table inequality (SI.166), [CP, (CP.28)][CP], the
unrestricted nine-input equality $m_{\mathrm{exec}}=24$, and the
all-position target of [TC, Theorem 9.1][TC] remain open.
The results concern installed states in the stated mathematical
model and give no physical-memory consequence or Lean-kernel claim.

[PE]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_PAID_PRIVATE_EXCHANGE.md
[CL]: RECURSIVE_RELATIONAL_OBSERVATION_COMMON_LIVE_CONES_AND_PRIVATE_DEMAND_CAPACITY.md

## 追加锚（本行以下为增补区）
