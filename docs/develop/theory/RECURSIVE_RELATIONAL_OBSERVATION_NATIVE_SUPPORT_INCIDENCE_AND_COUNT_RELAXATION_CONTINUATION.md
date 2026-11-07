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

## 29. Axis hit-gap-three histories and their paid short exits

**Definition 29.1 (actual axis pair and positive short exits).** Fix
any positive increasing position tuple and any one original graph
satisfying Assumption 21.1 for that tuple. The graph may depend on the
tuple. Let two actual live histories end at the same state $q$, with
exposed assignments $\sigma:S\to\{0,1\}$ and
$\rho:T\to\{0,1\}$ and respective cells $(0,z),(3,w)$.
Thus $K\ge4$, $\sigma\equiv0$, and $\rho$ has three ones. Put

$$
\begin{gathered}
X=S\setminus T,\quad Y=T\setminus S,\quad
I=S\cap T,\quad U=[n]\setminus(S\cup T),\\
a=|X|,\quad b=|Y|,\quad u=|U|,\quad
\beta=|\{j\in Y:\rho_j=1\}|,\quad v=K-3,\\
D=\{j\in I:\sigma_j=0,\ \rho_j=1\},\\
d_-=z,\quad d_+=3+w,\qquad C_Z=\sum_{i\in Z}c_i.
\end{gathered}
\tag{SI.181}
$$

A state $r$ has **positive short exits** if there is a branch path
starting with reply zero at $r$ and ending at terminal $\mathsf0$
after at most two queries, and a branch path starting with reply one
at $r$ and ending at terminal $\mathsf1$ after at most two queries.
These are two existential paths in the installed graph. Each includes
the query at $r$ and, possibly, one query at its running successor.
They need not describe all continuations from $r$. A particular
witness path may be inconsistent with some other incoming history.

**Theorem 29.2 (axis discrimination with one query of slack).** For
every pair of Definition 29.1,

$$
\begin{gathered}
D\ne\varnothing,\quad |D|=3-\beta,\quad
1\le a\le b\le3,\quad C_X\le C_Y,\quad u\ge v,\\
\Delta_d:=d_+-d_-=b-a\in\{0,1\},\\
\mathcal J_3=[v,\min(u,K-1-\beta)]\cap\mathbb Z
                 \ne\varnothing.
\end{gathered}
\tag{SI.182}
$$

For every assignment $\tau:U\to\{0,1\}$ of weight in
$\mathcal J_3$, form the two completions

$$
\begin{array}{c|cccc}
 &I&X&Y&U\\ \hline
\theta^-&0&0&\rho|_Y&\tau\\
\theta^+&\rho|_I&0&\rho|_Y&\tau.
\end{array}
\tag{SI.183}
$$

Their outputs are respectively zero and one. Starting at $q$, their
first different reply occurs at a state $r$ querying some $j\in D$.
Let $k$ be the number of queries strictly before this discriminator
in their common continuation, and let $\ell_-,\ell_+$ be the actual
numbers of queries strictly after it on the respective complete runs.
Then, with

$$
M=b+u-2=n-z-2,\qquad e=k-M,
$$

one has

$$
e\ge0,\qquad e+\ell_-\le1,\qquad
\Delta_d+e+\ell_+\le1.
\tag{SI.184}
$$

In particular $r$ has positive short exits. If $d_+=d_-+1$,
then $e=\ell_+=0$ and $\delta(r,1)=\mathsf1$.
If $e=1$, both tails are empty and $r$ is a positive terminal
literal gate. Every tail in these conclusions is paid on its own
actual input.

More explicitly, write $C_{\rm pre}$ for the complete charge of the
$k$ common queries, counting every repeated query, and $C_-,C_+$
for the charges of the actual tails. The original letter caps give

$$
\begin{aligned}
C_{\rm pre}+c_j+C_-&\le C_Y+C_U,\\
C_{\rm pre}+c_j+C_+&\le C_X+C_U.
\end{aligned}
\tag{SI.185}
$$

Proof. The histories are distinct. Their supports are incomparable
by the supplied exclusions in SI Section 2, so $a,b\ge1$.
[SI, Lemma 11.3][SI] says that their exposed assignments are
incompatible. Because the lower assignment is entirely zero, this
requires an upper one in $I$. Thus $D\ne\varnothing$ and
$|D|=3-\beta$, in particular $\beta\le2$.

We first recover the interval separation and one-sided exchange used
in [PE, Theorems 3.1 and 7.2][PE], directly for these Boolean
histories. There is no integer in

$$
[0,u]\cap[K-b,K-1]\cap[v-a,v-1].
\tag{SI.186}
$$

Indeed, give $U$ a common assignment of such a weight. After exposing
all of $U$, both histories would still be live: their remaining
thresholds would lie respectively between one and $b$, and between
one and $a$. Before that, their counts are bounded by these final
live counts. While both are live, their common queried coordinate
must be fresh for both by SI Theorem 2.2, hence belong to $U$.
They therefore follow a common fresh continuation through $U$.
Halting while live is incorrect; after exhausting $U$, another
common fresh query is impossible. This proves (SI.186) using actual
completions and fixed successors.

The two intervals
$[\max(0,K-b),\min(u,K-1)]$ and
$[\max(0,v-a),\min(u,v-1)]$ are nonempty by incoming liveness
and $a,b\ge1$. The second upper endpoint is no greater than the
first. Their disjointness places the second interval strictly below
the first. The first lower endpoint must therefore be $K-b>0$,
and the second upper endpoint must be $v-1<u$. It follows that
$K\ge b+1$, $v\le u$ and $v-1<K-b$, hence $b\le3$.

For the one-sided exchange, start from the upper history and answer
every fresh $X$ query zero. On first exposures in $U$, answer one
on the first $v-1$ and zero on the rest. This adaptive description
constructs a single input: each answer fixes a previously unread
coordinate. Before the first $v-1$ exposures in $U$ are finished,
there are at most $a\le a+u-v$ additional zeros and fewer than
$v$ additional ones. Afterwards there are exactly $K-1$ ones
in total, and every remaining unread coordinate is zero and is
needed for the negative certificate. Thus the upper run remains
live until its last unread coordinate. Freshness makes its suffix
query exactly $X\cup U$ once. It has used all $n$ queries and
must halt immediately at terminal zero.

Replay that suffix from the lower history, keeping the same $U$
assignment and giving $Y$ arbitrary values. Every queried $X$
coordinate has its old lower value zero; the suffix never queries
$I$ or $Y$. This is an actual completion of the lower history and
follows the entire suffix by stationarity. Its weight is at most
$b+v-1\le K-1$, consistent with its zero output. Its full query
count and charge are

$$
z+a+u=n+a-b,\qquad
C_S+C_X+C_U=W+C_X-C_Y.
$$

Applying both caps to this same replayed input proves $a\le b$
and $C_X\le C_Y$. This argument pays for the repeats in $X$;
it uses no equality of distinct subset sums.

Since $u\ge v$ and $\beta\le2$, one has
$K-1-\beta\ge K-3=v$, proving the nonemptiness of
$\mathcal J_3$. Each vector in (SI.183) extends its respective
actual incoming history. Its weight is $\beta+|\tau|\le K-1$
or $3+|\tau|\ge K$. Opposite correct outputs force a first
different reply in their common continuation. The vectors differ
only in $D$, so the discriminator queries $j\in D$, with replies
zero and one in that order.

This is an old-coordinate query on both runs. Freshness therefore
implies that both histories are already certified immediately before
it. The negative input has exposed at least $L$ distinct zeros and
the positive input at least $K$ distinct ones. In the common
continuation before this query put

$$
\begin{aligned}
B_0&=\{i\in Y:\rho_i=0,\ i\text{ was queried there}\},\\
U_0&=\{i\in U:\tau_i=0,\ i\text{ was queried there}\},\\
U_1&=\{i\in U:\tau_i=1,\ i\text{ was queried there}\}.
\end{aligned}
$$

The lower run's new zeros can only be in $B_0\cup U_0$;
the upper run's new ones can only be in $U_1$, because every
$X$ value is zero. Consequently

$$
|B_0|+|U_0|\ge L-z,\qquad |U_1|\ge K-3,
\qquad k\ge|B_0|+|U_0|+|U_1|\ge n-z-2=M.
\tag{SI.187}
$$

These are joint certificates from one common continuation, as in
PE Theorem 7.2; repeats cannot enlarge the sets or lower $k$.
The exact incoming query counts are $d_-,d_+$ by SI Theorem 2.2.
The full counts on these two actual inputs are therefore

$$
d_-+k+1+\ell_-=n-1+e+\ell_-,\qquad
d_++k+1+\ell_+=n-1+(b-a)+e+\ell_+.
$$

The query caps give (SI.184). Since $b-a\ge0$, they also force
$b-a\in\{0,1\}$. The two actual discriminator branches now
halt at their respective terminals in at most one further query,
giving the positive short exits. If $b-a=1$, (SI.184) forces
$e=\ell_+=0$; if $e=1$, it forces both tails empty. Fixed
successors give the asserted terminal edges. Finally the complete
charges are $C_S+C_{\rm pre}+c_j+C_-$ and
$C_T+C_{\rm pre}+c_j+C_+$. Subtracting the respective incoming
charges from their own caps gives (SI.185). $\square$

## 30. Every live occurrence of a state with positive short exits

**Theorem 30.1 (global two-by-two localization).** On any graph of
Assumption 21.1 with $K\ge4$, a state with positive short exits
can be live only in the cells

$$
\Pi_4=\{K-2,K-1\}\times\{L-2,L-1\}.
\tag{SI.188}
$$

If its reply-one successor is terminal $\mathsf1$, its possible
live cells reduce to the rightmost two cells

$$
\Pi_R=\{K-1\}\times\{L-2,L-1\}.
\tag{SI.189}
$$

These assertions concern every actual live occurrence anywhere in
the graph, including occurrences unrelated to the pair that supplied
the short exits. All such occurrences have depth at least $n-3$.

Proof. Take any live occurrence of the state, with counts $(h,z)$.
Its queried coordinate is fresh. Suppose $z\le L-3$. On reply
zero the history remains live. The zero short exit cannot be an
immediate terminal, since a live history has completions of both
outputs. Its running successor, if any, must query another fresh
coordinate by SI Theorem 2.2. The indicated next answer on the
short path is therefore consistent with some actual completion of
this incoming history. That path returns zero with at most $z+2<L$
exposed zeros. But every partial assignment with fewer than $L$
zeros has a positive completion, contradicting correctness. Thus
$z\ge L-2$.

Similarly, if $h\le K-3$, reply one leaves the history live.
The positive short path then returns one after at most two fresh
exposures, with fewer than $K$ ones. The exposed assignment has
a negative completion, another contradiction. Hence $h\ge K-2$.
Liveness supplies the opposite inequalities $h\le K-1$ and
$z\le L-1$, proving (SI.188). If reply one goes directly to
terminal one, the same reasoning with one exposure requires
$h+1\ge K$, so $h=K-1$, proving (SI.189).
The minimum depth in (SI.188) is $K+L-4=n-3$. The argument
uses freshness only at occurrences that are live; it imposes none
on certified traffic. $\square$

**Proposition 30.2 (short exits do not give a two-query algorithm).**
The ordinary fixed-order threshold grid satisfies Assumption 21.1
and has a live state with positive short exits whose residual cannot
be computed by any deterministic algorithm using at most two queries
on every completion. That state is not a terminal literal gate. The grid
itself has no shared host of distinct count cells.

Proof. Install one state for each $(h,z)\in V$, querying coordinate
$h+z+1$ in the fixed order $1,\ldots,n$. Send each reply to its
updated cell while live and to the correct terminal on reaching a
threshold. Every run queries a prefix of this order once, so both
caps hold with the original costs. Each state has only its named
count cell.

At $(K-2,L-2)$ there are three unread coordinates $x,y,t$,
and the residual is majority of three. Replies $x=y=0$ lead to
terminal zero, and $x=y=1$ to terminal one. Both paths use two
queries. Both successors after the first query are running, so the
state is not a literal gate. Any two-query algorithm for this
residual can be answered with one zero and one one on distinct
coordinates; the remaining coordinate then changes the answer.
A repeated query supplies still less information. Thus a uniform
two-query algorithm is impossible. This example distinguishes the
short-exit property from stronger continuation properties; it does
not realize an axis collision of Definition 29.1. $\square$

## 31. Natural representatives and genuine excess capacity

**Definition 31.1 (coordinate disagreements on one graph).** Let
$A_0$ be the unique all-zero-axis support at cell $(0,L-1)$.
For any finite family $\mathcal E$ of actual axis pairs of
Definition 29.1, let $D_e$ be its sets (SI.181), and define the
coordinate transversal number by

$$
\tau_3(\mathcal E)=
\min\{|H|:H\subseteq[n],\ H\cap D_e\ne\varnothing
                                      \ (e\in\mathcal E)\},
\qquad \nu=|Q\setminus Q_{\rm live}|.
\tag{SI.190}
$$

Every $D_e$ is nonempty by Theorem 29.2 and is contained in
$A_0$, since the support of every $(0,z)$ history is an initial
support of the unique all-zero axis. Set $\tau_3(\varnothing)=0$.
This is a coordinate transversal, distinct from the signed
transversal $\tau$ of Definition 26.1.

**Theorem 31.2 (excess, rather than gross, capacity).** With
Definition 31.1,

$$
\nu+\sum_{p\in\Pi_4}(b_p-1)\ge\tau_3(\mathcal E).
\tag{SI.191}
$$

If every pair in a subfamily $\mathcal E_R$ has unequal incoming
depths, then

$$
\nu+\sum_{p\in\Pi_R}(b_p-1)\ge\tau_3(\mathcal E_R).
\tag{SI.192}
$$

For $K=4$ every actual shared-history pair with hit gap three is
an axis pair of Definition 29.1, so (SI.191) covers all such pairs.

Proof. First exclude actual natural representatives in each possible
live cell. For $p=(h,t)\in\Pi_4$ follow the reply word
$0^t1^h$ from the fixed start, and denote its host by $q_p$.
Every prefix remains live, so SI Theorem 2.2 realizes this as an
actual live history. Its support contains $A_0$. For $t=L-1$
this follows from its first $L-1$ zero replies. For $t=L-2$,
its next query, answered one, is exactly the query that the all-zero
axis answers zero to complete $A_0$. There is at least one such
one reply since $h\ge K-2\ge2$. Thus in both cases freshness
at $q_p$ implies

$$
i(q_p)\notin A_0.
\tag{SI.193}
$$

Let $\mathcal P$ be the set of installed states with positive
short exits and labels in $A_0$, and let $H_P$ be their set of
coordinate labels. For every $e\in\mathcal E$, Theorem 29.2
supplies one of these states with label in $D_e$. Therefore
$|H_P|\ge\tau_3(\mathcal E)$ and $|\mathcal P|\ge|H_P|$.
Theorem 30.1 classifies all live occurrences of every member of
$\mathcal P$. Equation (SI.193) excludes $q_p$ in every possible
cell, giving the actual set containment

$$
\mathcal P\subseteq
(Q\setminus Q_{\rm live})\ \cup\!
       \bigcup_{p\in\Pi_4}(F_p\setminus\{q_p\}).
\tag{SI.194}
$$

The union bound now gives
$\tau_3(\mathcal E)\le|\mathcal P|
 \le\nu+\sum_{p\in\Pi_4}(b_p-1)$, proving (SI.191).
The subtraction of one in each cell is justified by its actual
excluded host, rather than by a gross bound on live states.

For $\mathcal E_R$, Theorem 29.2 supplies states in $\mathcal P$
whose reply-one edge is terminal one. Restrict $\mathcal P$ to
these states. Their labels meet all $D_e$ for $e\in\mathcal E_R$,
and Theorem 30.1 restricts their possible live cells to $\Pi_R$.
The same natural representatives and union bound prove (SI.192).
Finally, the live hit rows when $K=4$ are $0,1,2,3$, so a hit
gap of three necessarily has lower row zero and upper row three.
No injection from pairs to states, or from pairs to labels, was used.
A single state may serve many pairs. $\square$

## 32. Pinning short-exit states behind an actual common cut

**Theorem 32.1 (common-cut strengthening).** On a graph of
Assumption 21.1 with $K\ge4$, let $T_a$ be an actual common
support at depth $a\le n-3$. Let $\mathcal E$ be a finite
positive-short disagreement family in the following precise sense:
each member has a nonempty coordinate set $D_e\subseteq T_a$,
and an installed state with positive short exits whose label is in
$D_e$. Then, writing $\tau_3(\mathcal E)$ for the coordinate
transversal number of these sets,

$$
\nu\ge\tau_3(\mathcal E).
\tag{SI.195}
$$

In particular this applies to every family of Definition 31.1 whose
$D_e$ lie in $T_a$. The short-exit hypothesis in the general
statement is supplied by Theorem 29.2 in that application.

Proof. Any installed positive-short state with label in $T_a$
is globally never-live. Otherwise Theorem 30.1 puts an actual
live occurrence at depth $d\ge n-3\ge a$. Its actual live
ancestor at depth $a$ has support $T_a$, so its own support
contains $T_a$. This is the ancestry part of [SI, Lemma 9.2][SI],
also when $d=a$. Freshness forbids its fixed label from lying in
$T_a$, a contradiction. Consequently the labels of globally
never-live positive-short states in $T_a$ form a hitting set for
the $D_e$. Its cardinality is at most $\nu$, proving (SI.195).
The argument excludes all live occurrences, rather than charging a
state merely because its discriminating occurrence was certified.
$\square$

**Corollary 32.2 (automatic pinning in the nine-input gap $(3,9)$).**
Let $n=9$, $K=4$, $L=6$, and let $B=(3,9)$ be an actual
consecutive common-support gap. Consider any finite family of
actual hit-gap-three pairs with equal incoming depths, two private
coordinates on each side, and both incoming cells in $V_B$.
Every pair has incoming cells $(0,5),(3,2)$ and

$$
S\cap T=T_3,\qquad \varnothing\ne D_e\subseteq T_3.
\tag{SI.196}
$$

Thus this family satisfies (SI.195).

Proof. The lower row is zero, so these are pairs of Definition 29.1.
Write $d=|S|=|T|$. The actual common depth three and incoming
depth $d>3$ imply $T_3\subseteq S\cap T$ by SI Lemma 9.2.
The two private coordinates on each side require $d-3\ge2$.
The lower axis is live, so $d=z\le L-1=5$. Hence $d=5$,
and $|S\cap T|=d-2=3$ forces $S\cap T=T_3$.
The incoming counts and (SI.196) follow, with nonemptiness from
SI Lemma 11.3 as in Theorem 29.2. Apply Theorem 32.1 at
$a=3\le9-3$. This is conditional on actual pairs; it does not
assert that the family is nonempty or that such a gap is realizable.
$\square$

## 33. The same-graph nine-input counting consumer

**Corollary 33.1 (exact capacity pool and a sufficient condition).**
Retain Assumption 21.1 with $n=9$, $K=4$, $L=6$, and an
actual consecutive terminal gap $B=(a,9)$, $a\in\{1,2,3\}$.
Fix the original position tuple and its graph separately, as in
Corollary 27.1. Choose either

$$
\Pi=\Pi_4=\{2,3\}\times\{4,5\},\qquad\text{or}\qquad
\Pi=\Pi_R=\{3\}\times\{4,5\},
$$

and on this same graph put

$$
\begin{aligned}
R&=E_{\rm cut}+\sum_{C\in\mathcal B,\ C\ne B}(E_C-D_C),\\
E_B^{\setminus\Pi}&=\sum_{p\in V_B\setminus\Pi}(b_p-1),\\
C_\Pi&=\nu+\sum_{p\in\Pi}(b_p-1).
\end{aligned}
\tag{SI.197}
$$

Let $\mathcal E_3$ be any axis family with incoming cells in
$V_B$; for the choice $\Pi_R$, require all its pairs to have
unequal incoming depths. Write $t_3=\tau_3(\mathcal E_3)$.
Optionally take a signed literal-gate family of Definition 26.1 on
this graph, with incoming cells in $V_B$, and write $t_{\rm lit}$
for its signed transversal number. Also optionally take a family
of Theorem 32.1 on this graph and write $t_{\rm cut}$ for its
coordinate transversal number. Empty families have transversal
number zero. Then $R\ge0$, $b_{(3,5)}\ge2$, and

$$
\begin{aligned}
m&=24+R+E_B^{\setminus\Pi}-D_B+C_\Pi,\\
C_\Pi&\ge\max\{1,t_3,t_{\rm lit}-1,t_{\rm cut}+1\}.
\end{aligned}
\tag{SI.198}
$$

The exact remaining condition for $m\ge24$ on this graph is

$$
R+E_B^{\setminus\Pi}+C_\Pi\ge D_B.
\tag{SI.199}
$$

A clearly sufficient, possibly stronger condition is

$$
R+E_B^{\setminus\Pi}+
       \max\{1,t_3,t_{\rm lit}-1,t_{\rm cut}+1\}\ge D_B.
\tag{SI.200}
$$

Proof. The nonnegativity of $R$ and $b_{(3,5)}\ge2$ are the
same-graph conclusions proved in Corollary 27.1: every other gap
has span at most three, and depth eight is internal and noncommon
with unique cell $(3,5)$. Both choices of $\Pi$ lie in $V_B$
and contain this cell. Split $E_B$ into its $\Pi$ and
$V_B\setminus\Pi$ sums in the exact incidence identity
[SI, Theorem 9.3, (SI.32)][SI],
$m-24=R+E_B-D_B+\nu$. This gives the equality in (SI.198).

The corner excess alone gives $C_\Pi\ge b_{(3,5)}-1\ge1$.
Theorem 31.2 gives $C_\Pi\ge t_3$, using (SI.192) for
$\Pi_R$. Theorem 26.2 gives
$b_{(3,5)}+\nu\ge t_{\rm lit}$, and hence
$C_\Pi\ge t_{\rm lit}-1$. Theorem 32.1 gives
$\nu\ge t_{\rm cut}$; its never-live states are disjoint
from the corner's live hosts, so
$C_\Pi\ge t_{\rm cut}+(b_{(3,5)}-1)\ge t_{\rm cut}+1$.
These are lower bounds on one capacity pool, so their maximum is
valid. Adding the transversal bounds to one another is not justified:
the same states and labels can serve the different families.

For comparison with (SI.178)--(SI.179), the exact relation is

$$
\begin{aligned}
C_\Pi&=b_{(3,5)}+\nu-1+
                   \sum_{p\in\Pi\setminus\{(3,5)\}}(b_p-1),\\
E_B^\circ&=E_B^{\setminus\Pi}+
                   \sum_{p\in\Pi\setminus\{(3,5)\}}(b_p-1).
\end{aligned}
\tag{SI.201}
$$

Thus (SI.199) is exactly (SI.179), with its natural hosts already
subtracted in the new pool. Rearranging the equality proves its
equivalence to $m\ge24$, and the lower bound in (SI.198) proves
the sufficiency of (SI.200). No gross four-cell host count is added
to the older terminal-gate count. In the situation of Corollary 32.2,
its $t_{\rm cut}$ is automatically available for the family there.
$\square$

## 34. Mathematical sources and the remaining quantified condition

**Proposition 34.1 (scope of the transfer).** The preceding conclusions
hold for every original increasing position tuple, separately for
every graph satisfying Assumption 21.1 for that tuple. They preserve
both pointwise caps, adaptive coordinate orders, union cycles and
paid post-certification queries. They supply conditional counting
criteria, without establishing (SI.200) for every terminal pool.
The whole-table condition (SI.166), [CP, (CP.28)][CP], and the
unrestricted nine-input conclusion $m_{\rm exec}=24$ therefore
remain unproved by these criteria. There is no physical-memory
consequence.

Proof and source correspondence. SI Theorem 2.2 supplies actual
freshness, exact live prefix depths and the unique zero axis; SI
Lemma 11.3 supplies actual-history incompatibility and hence the
nonempty positive disagreement $D$. SI Lemma 9.2 supplies actual
common cuts and support envelopes. The paired-completion, joint
certificate and original-cost arguments are those of PE Theorems
3.1 and 7.2, specialized and proved in Boolean form in Theorem
29.2. The new restrictions used for counting are the global live
localization in Theorem 30.1, exclusion of the natural representative
in every cell in Theorem 31.2, and common-cut pinning in Theorem
32.1. Transversal counting is the ordinary hitting-set principle;
the exact consumer is the existing SI incidence identity.

The short paths are witnessed by actual paired runs, but only two
existential exits are transferred to other histories. Proposition
30.2 disproves the stronger uniform two-query interpretation. A
certified discriminator occurrence alone is not a globally new or
never-live state; the exclusions in Sections 30--32 are what permit
the stated capacity charges. Neither the number of pairs nor their
separately attainable certificates can replace a coordinate
transversal or the joint certificates (SI.187).

The bounded primary-source comparisons retain their exact
hypotheses. [Bryant, Section 2, Definition 1][Bryant] requires a
strict increase of the variable index on every edge to a nonterminal
child, and explicitly derives acyclicity from that restriction.
[Cook, Edmonds, Medabalimi and Pitassi, Section 2.1][CEMP] starts
with an acyclic nondeterministic branching program; semantic
read-once requires every consistent path from its start to its
accepting state to query each variable at most once. These hypotheses
are absent here and provide no size-preserving normalization of the
allowed certified traffic. The deductions above are relative to the
stated repository suppliers, with no worldwide novelty assertion.

For the all-position lower-bound target, the remaining obligation is
to prove the exact condition (SI.199), or a sufficient condition such
as (SI.200), for every permitted graph for every original tuple.
No such uniform bound on its deficit or transversals has been
established here. The common-cut strengthening uses an actual
$T_a$ at $a\le n-3$; the formal endpoint $T_n=[n]$ supplies
no substitute for that premise. Counting the graph's installed
states also supplies none of the separately priced representation
or service resources needed for a physical-memory statement.
$\square$

## 追加锚（本行以下为增补区）


## 35. Common-input compatibility of saturated and axis completions

**Definition 35.1 (constructed inputs and absolute query indices).**
Fix one graph of Assumption 21.1 with $K\ge4$. For a qualifying
pair of Definition 25.1 and an assignment of its $U$ with weight
in (SI.168), denote the two particular vectors (SI.171) by
$x^-,x^+$, and their discriminator state from Theorem 25.3 by
$r_2$. Independently choose an actual axis pair of Definition 29.1
on this same graph and an assignment of its own $U$ with weight
in (SI.182). Denote its particular vectors (SI.183) by $y^-,y^+$
and its discriminator by $r_3$. Use $d_-,d_+,k,\ell_-,\ell_+$
for this axis pair as in Theorem 29.2, and write

$$
\Delta=d_+-d_-,\qquad
\varepsilon=k-(n-d_--2).
\tag{SI.202}
$$

Thus $\Delta\in\{0,1\}$ and $\varepsilon$ is the nonnegative
integer called $e$ in (SI.184). No equality between the incoming
states, supports or depths of the two separately chosen pairs is
assumed. A common input means equality of the whole Boolean
vectors on $[n]$, evaluated from the fixed start of this one graph.
It does not mean only equal weights or equal exposed counts.

For an actual input $x$ let $q_t(x)$ be its running state at its
$t$-th query, let $i_t(x)=i(q_t(x))$, and put
$S_{<t}(x)=\{i_s(x):1\le s<t\}$, for
$1\le t\le t_P(x)$. A query is old on this input precisely when
$i_t(x)\in S_{<t}(x)$. These are indices of the actual run, not
extra changing configuration.

**Theorem 35.2 (colour freshness and common-input exclusion).**
For every choice in Definition 35.1 both $x^-$ and $x^+$ use
exactly $n$ queries, with final state $r_2$. Their pre-final
queries satisfy the separate implications

$$
\begin{aligned}
1\le t<n,\quad x^-_{i_t(x^-)}=0
   &\ \Longrightarrow\ i_t(x^-)\notin S_{<t}(x^-),\\
1\le t<n,\quad x^+_{i_t(x^+)}=1
   &\ \Longrightarrow\ i_t(x^+)\notin S_{<t}(x^+).
\end{aligned}
\tag{SI.203}
$$

The compatibility restrictions on the two same-output comparisons
are as follows.

1. If $y^-=x^-$, then $r_3=r_2$ is a positive terminal literal
   gate and

$$
\Delta=0,\qquad\varepsilon=1,\qquad
\ell_-=\ell_+=0,\qquad t_P(y^-)=t_P(y^+)=n.
\tag{SI.204}
$$

2. If $y^+=x^+$, then $r_3=r_2$ is again a positive terminal
   literal gate and

$$
(\Delta,\varepsilon)\in\{(0,1),(1,0)\},\qquad
\ell_-=\ell_+=0,\qquad
 t_P(y^-)=n-\Delta,\quad t_P(y^+)=n.
\tag{SI.205}
$$

In particular, when this chosen $r_2$ has negative sign, neither
same-output equality can hold. Both signs in Definition 26.1 remain
permitted for qualifying pairs in general.

More precisely, let $\mathcal E_2$ be any signed family of
Definition 26.1 and let $\mathcal E_{3,R}$ be any family of
Definition 29.1 whose pairs have unequal incoming depths, all on
this same graph. Let $\mathcal X_2^-$ be exactly the set of negative
vectors (SI.171) from $\mathcal E_2$, over every permitted
assignment in (SI.168), and let $\mathcal X_{3,R}^-$ be exactly
the set of negative vectors (SI.183) from $\mathcal E_{3,R}$, over
every permitted assignment in (SI.182). Then

$$
\mathcal X_2^-\cap\mathcal X_{3,R}^-=\varnothing.
\tag{SI.206}
$$

For the choice $\Pi_R$ in Corollary 33.1, this excludes a joint-demand
route that uses one negative actual input as both a saturated
literal-family completion and an unequal-depth axis-family
completion. It supplies no additive installed-state capacity bound.

Proof. Reuse the precise equality conclusion of Theorem 25.3.
The incoming prefixes each use $d$ fresh queries, the common
continuation before the discriminator has exactly $u+1$ queries,
and its coordinates are exactly the disjoint sets $A,B,U_0,U_1$
of (SI.169), each queried once there. The discriminator is query
$n=d+u+2$ on both complete runs and is followed immediately by
termination. Every earlier query in either incoming prefix is fresh
by SI Theorem 2.2.

On $x^-$ the coordinates in $A$ have value one and those in $B$
have value zero. Thus the zero queries in this common continuation
are precisely $B\cup U_0$. Both sets lie outside its incoming
support $S$, and distinctness in (SI.169) makes each of these zero
queries fresh relative to all earlier queries of this actual run.
On $x^+$ the one queries in the common continuation are precisely
$A\cup U_1$. These sets lie outside its incoming support $T$ and
are likewise queried once there. This proves both implications in
(SI.203), including queries in the incoming prefixes. The argument
does not assert freshness of pre-final ones on $x^-$ or of
pre-final zeros on $x^+$: $A$ is old on the former and $B$ is old
on the latter whenever the respective set is nonempty. The final
coordinate is old on both inputs; its sign is exactly the sign
specified in Theorem 25.3, with no positivity assumption.

For the axis pair, Theorem 29.2 places the discriminator at an old
coordinate of both incoming supports, with replies zero on $y^-$
and one on $y^+$. Its absolute query numbers on those inputs are
respectively

$$
N_-=d_-+k+1=n-1+\varepsilon,\qquad
N_+=d_++k+1=n-1+\Delta+\varepsilon.
\tag{SI.207}
$$

Both queries actually occur, and both numbers are at most $n$.
These are occurrence numbers on the actual runs; the graph need
not assign one depth to an installed state.

Suppose first that $y^-=x^-$. The axis discriminator is an old
zero query on this input. Equation (SI.203) forbids its occurring
before query $n$, so $N_-=n$ and $\varepsilon=1$. Its state is
$q_n(x^-)=r_2$, by determinism on the same whole input. Since
$r_2$ is a signed terminal literal gate and this zero reply returns
the correct output zero, its sign is positive. Its two fixed
successors are therefore the two output terminals, giving
$\ell_-=\ell_+=0$. The inequality
$\Delta+\varepsilon+\ell_+\le1$ in (SI.184) now forces
$\Delta=0$. Equation (SI.207) gives (SI.204).

Suppose instead that $y^+=x^+$. This time the axis discriminator
is an old one query on the shared input. The second implication
of (SI.203) forces $N_+=n$. Hence
$\Delta+\varepsilon=1$ and its state is $q_n(x^+)=r_2$.
Its one reply returns the correct output one, so the signed gate
$r_2$ must be positive. Both tails are empty because its fixed
successors are terminals. The possibilities $\Delta\in\{0,1\}$
and (SI.207) give exactly (SI.205). In particular the case
$\Delta=1,\varepsilon=0$ is not eliminated by this argument;
this necessary-case possibility asserts no graph realizing it.
The gate-sign conclusion in both cases proves the negative-sign
exclusion. For every unequal-depth axis pair, (SI.182) gives
$\Delta=1$. Applying (SI.204) to each proposed common negative
input proves (SI.206), including empty families. No analogous
positive-family disjointness is inferred from (SI.205).

The source correspondence uses the actual histories throughout.
SI Theorem 2.2 supplies live freshness and exact incoming depths;
SI Lemma 11.3 supplies the incompatibility used in Theorem 29.2.
PE Theorem 7.2 supplies the paired vectors and joint certificates,
with its $(p,y,V,Q)$ corresponding to
$(\alpha,\beta,K-g,K-h)$ for the gap-two pair. Theorem 25.3
specializes these vectors to (SI.171) and saturates the common
continuation; (SI.169) yields the colour-specific consequence
(SI.203). For the axis pair the correspondence is
$(p,y,V,Q)=(0,\beta,K-3,K)$, and Theorem 29.2 supplies (SI.183),
the old positive discriminator and the slack inequalities
(SI.184). Arbitrary opposite-output extensions of the incoming
histories need not have the form (SI.171) or (SI.183) and are not
covered by this comparison. The original letter-cap inequalities
(SI.174) and (SI.185) continue to apply separately on their own
actual inputs; identifying one vector neither concatenates runs
nor combines independently minimized charges.

The precise counting consumer is Corollary 33.1 with $n=9$, $K=4$,
$L=6$, $B=(a,9)$, $a\in\{1,2,3\}$ and $\Pi=\Pi_R$.
Take $\mathcal E_2$ to be its optional signed family giving
$t_{\rm lit}$ and $\mathcal E_{3,R}$ its unequal-depth axis
family giving $t_3$, with both families' incoming cells in $V_B$.
Equation (SI.206) rules out identifying their negative witnessing
inputs in an attempted joint charge toward (SI.199). It does not
make their installed discriminator images disjoint: distinct inputs
can have the same discriminator state and label. In particular a positive
terminal literal gate already has positive short exits, as in
Definitions 25.2 and 29.1. Neither equality of the two input
vectors nor a shared incoming history is required for an installed
state to serve different pairs. PE Proposition 9.1 gives precisely
this state-reuse boundary. Thus the maximum in (SI.198), rather
than an unsupported sum of its separate transversal demands,
remains the supplied capacity bound. A separation of the installed
state images, or another joint lower bound that pays for their
intersection, is an additional obligation.

This is a repo-derived restriction comparing the two constructed
completion families. Deterministic indistinguishability, threshold
certificates and equality in a query budget are inherited
arguments; no new general hitting-set inequality is used.
The ordered graphs of [Bryant Section 2, Definition 1][Bryant] require
strictly increasing variable indices on nonterminal edges.
The acyclic programs and semantic read-once accepting paths of
[Cook, Edmonds, Medabalimi and Pitassi Section 2.1][CEMP] also have
hypotheses absent from Assumption 21.1. Those sources supply no
normalization of its certified traffic for this proof, and no
worldwide novelty assertion is made.

The argument holds separately for every original positive increasing
position tuple and every permitted graph for that tuple. It keeps
both pointwise caps, adaptive orders, paid certified queries and
union cycles. It proves neither existence of either collision family
nor a uniform deficit bound for (SI.199) or (SI.200). The whole-table
condition (SI.166), CP.28 and unrestricted $m_{\rm exec}=24$
remain unresolved; no physical-memory consequence or Lean-kernel
verification is asserted. $\square$

## 追加锚（本行以下为增补区）

## 36. Exact separated histories and the cut-pinned obstruction

**Definition 36.1 (separated demands in one actual terminal gap).**
Fix one graph of Assumption 21.1 with $n=9$, $K=4$, $L=6$,
and an actual consecutive common-support gap $B=(3,9)$.
Let $T_3$ be its actual depth-three common support, and let $A_0$
be its unique zero-axis support at $(0,5)$, as in Definition 31.1.
Thus $|T_3|=3$, $|A_0|=5$, and $T_3\subseteq A_0$.
Put

$$
\Omega_\perp=([9]\times\{-\})\ \cup\
                  (([9]\setminus A_0)\times\{+\}).
\tag{SI.208}
$$

Let $\mathcal E_\perp$ be a finite family of Definition 26.1
whose incoming cells lie in $V_B$ and for which
$\mathcal D_e\subseteq\Omega_\perp$ for every member. Write
$t_\perp=\tau(\mathcal E_\perp)$. Independently choose an actual
axis family $\mathcal E_3$ of Definition 31.1 with incoming cells
in $V_B$, and write $t_3=\tau_3(\mathcal E_3)$.
An axis family is called cut-pinned here when all its $D_e$ lie
in $T_3$; Theorem 32.1 then applies to this very family.
Corollary 32.2 supplies this property when its equal-depth and
two-private-coordinate hypotheses hold.

For comparison also choose a signed family $\mathcal E_{\rm lit}$
with incoming cells in $V_B$ containing $\mathcal E_\perp$,
and a family $\mathcal E_{\rm cut}$ of Theorem 32.1 on this graph.
Write their transversal numbers as $t_{\rm lit}$ and $t_{\rm cut}$.
Different members of the cut family may use different actual common
cuts of depth at most six. All these cuts have depth at most three
because $B$ is consecutive, so their supports lie in $T_3$.
The conclusion of Theorem 32.1 still holds for their union:
its proof places every supplying state globally in the never-live
pool. Empty families are allowed, with transversal number zero.

The comparison with every available literal or cut family can be made
by taking all qualifying actual literal pairs with incoming cells in
$V_B$, and the singleton sets $\{j\}$ for every label $j\in T_3$
of an installed state with positive short exits, respectively.
The first choice is finite by SI Lemma 11.3. The second is a family
of Theorem 32.1 at $T_3$; its transversal is the number of these
labels. It dominates any other cut-family transversal because those
same labels meet every such demand. In particular
$t_{\rm lit}\ge t_\perp$ and $0\le t_{\rm cut}\le3$.
These choices concern one installed graph, without identifying
histories, states or independently chosen inputs.

**Theorem 36.2 (complete local classification and the two paid patterns).**
For an actual qualifying pair with incoming cells in $V_B$,
the condition $\mathcal D_e\subseteq\Omega_\perp$ holds if and only
if its data have the following form. Its incoming depth and cells are

$$
d=6,\qquad (h,z)=(1,5),\qquad (g,w)=(3,3),
\tag{SI.209}
$$

and, with the notation of Definition 25.1,

$$
\begin{gathered}
I=T_3\sqcup\{j\},\qquad j\notin A_0,\qquad
\sigma|_{T_3}=\rho|_{T_3},\qquad
(\sigma_j,\rho_j)=(0,1),\\
\mathcal D_e=\{(j,+)\},\qquad
U=\{u_0\},\qquad \eta=1,\qquad
|\sigma^{-1}(1)\cap T_3|=1 .
\end{gathered}
\tag{SI.210}
$$

Both actual incoming histories query $j$ at their fourth query.
The private assignments are necessarily $X\equiv0$ on the lower
history and $Y=\{y_0,y_1\}$ with upper values $0,1$.

More generally, to distinguish the two private-one alternatives,
consider an actual qualifying pair satisfying (SI.209) with
$I=T_3\sqcup\{j\}$, equal assignments on $T_3$ and
$(\sigma_j,\rho_j)=(0,1)$, without imposing $j\notin A_0$.
There are two possible count patterns. In pattern A the common
assignment on $T_3$ is all zero, $X=\{x,x_0\}$ has lower values
$1,0$, and $Y$ has upper values $1,1$. In pattern B the common
assignment on $T_3$ has one one, $X$ has lower values $0,0$,
and $Y=\{y_0,y_1\}$ has upper values $0,1$.
Pattern A forces $j\in A_0$ and is therefore excluded from the
separated family. Pattern B is the only retained separated pattern;
its actual existence is not asserted.

For any actual pair of this broader form, in pattern A the only
assignment permitted by (SI.168) is $u_0=0$.
On the two particular inputs (SI.171), the common suffix queries
$u_0,x,j$, in this order, with replies $(0,1,0)$ and $(0,1,1)$.
In pattern B that assignment is $u_0=1$, and the common suffix
queries $u_0,y_0,j$, in this order, with replies $(1,0,0)$ and
$(1,0,1)$. In both patterns these inputs have weights three and
four, use exactly nine queries, and finish at a positive terminal
literal gate labelled $j$. Their original letter caps are equivalent
to the respective inequalities

$$
\begin{array}{ll}
\mathrm A:&c_x+c_j\le\min(C_X,C_Y),\\
\mathrm B:&c_{y_0}+c_j\le\min(C_X,C_Y).
\end{array}
\tag{SI.211}
$$

The original all-input caps also require the one-sided exchange
conditions

$$
\begin{array}{ll}
\mathrm A:&C_Y\le C_X,\qquad c_x+c_j\le C_Y,\\
\mathrm B:&C_X\le C_Y,\qquad c_{y_0}+c_j\le C_X .
\end{array}
\tag{SI.212}
$$

Consequently $c_j<c_{x_0}$ in pattern A and $c_j<c_{y_1}$ in
pattern B. None of these cost conditions is asserted sufficient
for an entire graph or for all completions of the incoming histories.

Proof. First exclude lower hit row zero. Such a lower history has
an all-zero support $S$ contained in $A_0$, by the unique zero axis
and liveness. Every disagreement in $I\subseteq S$ is then positive
and lies in $A_0$. The disagreement set is nonempty by
$\eta>0$, contradicting (SI.208). The only other possible hit rows
are $h=1$, $g=3$, since $g=h+2\le3$. Liveness gives
$d-1=z\le5$, so $d\le6$.

Both incoming depths are greater than three. Actual ancestry at the
common cut, SI Lemma 9.2, gives $T_3\subseteq I$. Since
$|I|=d-2$, depth four is impossible. At depth five one has
$I=T_3\subseteq A_0$, where separation forbids positive
disagreements. But

$$
\sum_{i\in I}(\rho_i-\sigma_i)
       =(3-\beta)-(1-\alpha)=2+\alpha-\beta=\eta>0
$$

requires a positive disagreement. This excludes depth five as well.
Thus $d=6$, giving (SI.209), $|I|=4$ and $|U|=1$.
Write $I=T_3\sqcup\{j\}$. The required positive disagreement
must be at $j$, and separation forces $j\notin A_0$.
Its contribution to the displayed sum is one. Every contribution
on $T_3$ is nonpositive; positivity of the integer sum therefore
forces all of them to vanish. This proves all assertions of
(SI.210) except the last one.

Let $r$ be the common number of ones on $T_3$. The lower total is
one and its $j$ value is zero, so $r\in\{0,1\}$. The private
one counts are

$$
\alpha=1-r,\qquad \beta=2-r .
$$

For $r=0$ these give pattern A; for $r=1$ they give pattern B,
including all choices of the common one and of the private
coordinates. These same equations classify the broader actual pairs
in the statement, whose intersection assignments have been specified.

The actual common prefix now decides which pattern can be separated.
The two incoming histories have identical exposed assignments on
$T_3$. Every actual live depth-three history has support $T_3$.
Complete the two incoming assignments to full inputs. From the fixed
start these inputs follow identical first three queries: each query
belongs to $T_3$, and they give it the same reply. Hence they reach
the same depth-three state. Its next coordinate lies in both incoming
supports, because both histories continue to depth six. Freshness
places it outside $T_3$, so it must be the sole element $j$ of
$I\setminus T_3$. Thus $j$ is query four on both histories.
If $r=0$, the first three replies are all zero. Query four is then
the fourth coordinate of the actual all-zero axis, and lies in $A_0$.
This contradicts separation. Therefore $r=1$, proving the last
assertion of (SI.210) and excluding pattern A in that scope.
For the broader pairs the same argument proves the asserted
implication from pattern A to $j\in A_0$. Conversely, the stated
separated data of pattern B have exactly the disagreement $(j,+)$
with $j\notin A_0$, proving the equivalence for actual qualifying
pairs. This does not construct their incoming paths.

Here $u=v=1$. Substitution into (SI.168) gives
$\mathcal J=\{r\}$. Substitution into (SI.171) gives weights
$1+\beta+r=3$ and $3+\alpha+r=4$. Apply Theorem 25.3
to precisely these inputs. Its equality (SI.169) requires one new
zero for the lower certificate and one new one for the upper
certificate before the discriminator, using exactly two queries.
In pattern A there is no old zero in $Y$ and $u_0=0$,
so those two coordinates must be $u_0$ and $x$. In pattern B
there is no old one in $X$ and $u_0=1$, so they must be
$y_0$ and $u_0$. The first query at the common live state must
be fresh for both incoming histories; their common unread set is
exactly $\{u_0\}$. This fixes the orders asserted above.
The unique differing coordinate is $j$, so Theorem 25.3 makes it
the final query, with positive sign.

Write $v_0=x$ in pattern A and $v_0=y_0$ in pattern B.
The complete charges on the two actual paired inputs are exactly

$$
C_S+c_{u_0}+c_{v_0}+c_j,\qquad
C_T+c_{u_0}+c_{v_0}+c_j .
$$

As $W-C_S=C_Y+c_{u_0}$ and
$W-C_T=C_X+c_{u_0}$, their separate caps are equivalent to
$c_{v_0}+c_j\le C_Y$ and $c_{v_0}+c_j\le C_X$.
This is (SI.211). The certificates are the joint certificates of
this fixed shared suffix, not independently minimized witnesses.

For completeness, the one-sided replay of PE Theorem 3.1 gives
the additional inequalities in (SI.212) directly on actual Boolean
inputs. In pattern A complete the lower history by setting all of
$Y\cup U$ to one. It starts at $(1,5)$ and stays live until
all three unread coordinates have been queried once. Freshness and
correctness force these queries; the nine-query cap forces immediate
termination afterwards. Replay this same suffix from the upper
history, setting $u_0=1$ and retaining its old all-one $Y$.
It queries only $Y\cup U$, so arbitrary values on $X$ extend
it to an actual upper input following those fixed successors.
Its full charge is

$$
C_T+C_Y+c_{u_0}=W+C_Y-C_X .
$$

The letter cap on that very input proves $C_Y\le C_X$.
In pattern B complete the upper history by setting all of $X\cup U$
to zero. Starting at $(3,3)$, it stays live until those three
fresh zeros have all been read, and then halts by the query cap.
Replay the suffix from the lower history with its old all-zero $X$
and $u_0=0$. Any assignment on $Y$ completes this actual run;
its charge is $C_S+C_X+c_{u_0}=W+C_X-C_Y$.
Its own letter cap gives $C_X\le C_Y$. Combining these replays
with (SI.211) yields (SI.212). They pay for the old $Y$ or $X$
queries on the replayed input, including certified traffic.
Finally $c_x+c_j\le C_X=c_x+c_{x_0}$ in pattern A, and
$c_{y_0}+c_j\le C_Y=c_{y_0}+c_{y_1}$ in pattern B.
The coordinates are distinct and individual costs are strictly
increasing, so the resulting weak inequalities are strict.

The source correspondence is SI Theorem 2.2 for actual depths,
zero-axis uniqueness and live freshness; SI Lemma 9.2 for containment
of $T_3$; and Definition 25.1 for the private sizes and $\eta$.
PE Theorem 7.2 has parameters
$(p,y,V,Q)=(\alpha,\beta,1,3)$ here; its paired vectors and
joint certificates are the ones specialized in Theorem 25.3.
Equations (SI.169) and (SI.174) supply the exact suffix and the
two original-cost charges, while the last replays are PE's one-sided
exchange argument. This is a repo-derived restriction of the original
model, not a claim that threshold certificates or replay arguments
are new. $\square$

**Corollary 36.3 (same-graph strictness test and cut-pinned exclusion).**
Retain Definition 36.1 and the choice $\Pi=\Pi_4$ in
Corollary 33.1. On this same graph put

$$
\begin{gathered}
\lambda=(b_{(2,4)}-1)+(b_{(2,5)}-1)+(b_{(3,4)}-1),\qquad
\gamma=b_{(3,5)}-1,\\
C=C_{\Pi_4}=\nu+\lambda+\gamma,\qquad
M_{\rm mix}=t_3+t_\perp-1,\\
M_0=\max\{2,t_3,t_{\rm lit},t_{\rm cut}+2\},\qquad
M_1=\max\{M_0,t_{\rm cut}+t_\perp\}.
\end{gathered}
\tag{SI.213}
$$

Then $\lambda\ge1$, $\gamma\ge1$, and

$$
\begin{gathered}
t_\perp=|\{j_e:e\in\mathcal E_\perp\}|\le3,\qquad
C\ge\max\{M_1,M_{\rm mix}\},\\
m=24+R+E_B^{\setminus\Pi_4}-D_B+C .
\end{gathered}
\tag{SI.214}
$$

The numerical comparison $M_{\rm mix}>M_0$ is equivalent to

$$
t_\perp\ge2,\qquad
t_3+t_\perp\ge t_{\rm cut}+4,\qquad
t_{\rm lit}\le t_3+t_\perp-2 .
\tag{SI.215}
$$

In particular it requires $t_3\ge2$. After also including the
joint cut bound in $M_1$, the exact comparison is

$$
M_{\rm mix}>M_1
\quad\Longleftrightarrow\quad
t_\perp\ge2,\qquad t_3\ge t_{\rm cut}+2,\qquad
t_{\rm lit}\le t_3+t_\perp-2 .
\tag{SI.216}
$$

These are necessary and sufficient conditions for comparison of the
specified expressions, conditional on their actual graph and families.
They are necessary conditions for a strict consumer of these bounds,
without sufficient conditions for realizing that graph. Any strict
profile has $t_\perp\in\{2,3\}$ and must supply that many distinct
fourth-query labels from actual depth-three histories with one one
on $T_3$, each with the surviving paid pattern of Theorem 36.2.

If $\mathcal E_3$ is cut-pinned, there is instead the stronger bound

$$
C\ge t_3+t_\perp .
\tag{SI.217}
$$

Thus its proposed mixed expression is never a strict improvement once
this applicable cut bound is included. If the cut comparison includes
this axis family, or uses the complete-cut choice of Definition 36.1,
then $t_3\le t_{\rm cut}\le3$, and already

$$
M_{\rm mix}=t_3+t_\perp-1\le t_{\rm cut}+2\le M_0 .
\tag{SI.218}
$$

In particular, in the additional scope of Corollary 32.2 the proposed
mixed expression cannot beat even $M_0$. Four coordinates outside
$A_0$ do not supply four possible separated singleton labels:
the actual depth-three prefixes restrict their number to three.

Proof. Depth seven is internal to the consecutive gap and is
noncommon. Its live cells are precisely $(2,5),(3,4)$. The diagonal
criterion of SI Definition 9.1 and Theorem 4.1 gives support
multiplicity at least two in one of these cells; SI Theorem 2.2
therefore gives

$$
(b_{(2,5)}-1)+(b_{(3,4)}-1)\ge1 .
$$

Depth eight is also noncommon, with unique live cell $(3,5)$,
so $\gamma\ge1$ by the same criterion. This proves $\lambda\ge1$.
Theorem 36.2 makes every separated disagreement set a positive
singleton outside the five-element $A_0$, so its transversal is
exactly its number of distinct labels. For each $a\in T_3$ there
is a unique actual depth-three history with assignment one at $a$
and zero on $T_3\setminus\{a\}$. To see existence, complete that
assignment arbitrarily and run the graph: all depth-three prefixes
are live and have support $T_3$. Uniqueness follows by deterministic
induction on its three fresh queries. Denote its host by $r_a$.
Theorem 36.2 shows that every separated pair with common one at $a$
has

$$
j_e=i(r_a)\notin A_0,\qquad
\{j_e:e\in\mathcal E_\perp\}
      \subseteq\{i(r_a):a\in T_3\}\setminus A_0 .
$$

There are only three such histories; their hosts or labels can
coincide, which can only decrease the number of distinct labels.
This proves $t_\perp\le3$. Distinct demanded labels require distinct
actual depth-three hosts as well as the distinct final gates.

Reuse Theorems 26.2, 31.2 and 32.1. They give, respectively,
$\nu+b_{(3,5)}\ge t_{\rm lit}$, $C\ge t_3$ and
$\nu\ge t_{\rm cut}$. Consequently

$$
C\ge2,\qquad
C\ge t_{\rm lit}+\lambda-1\ge t_{\rm lit},\qquad
C\ge t_{\rm cut}+\lambda+\gamma\ge t_{\rm cut}+2 .
\tag{SI.219}
$$

Together these give $C\ge M_0$. In particular comparing only with
$\max\{1,t_3,t_{\rm lit}-1,t_{\rm cut}+1\}$ from (SI.198)
does not test strictness against these source-derived diagonal bounds.

Here is the finite union argument for the separated demands.
Let $\mathcal P_3$ consist of all installed states with positive
short exits and labels in $A_0$. The proof of Theorem 31.2 gives
$|\mathcal P_3|\ge t_3$ and places it in the never-live pool
together with $F_p\setminus\{q_p\}$ for $p\in\Pi_4$,
where $q_p$ are its actual natural representatives.
Let $\mathcal G_\perp$ be all installed terminal literal gates with
signed labels in $\Omega_\perp$. Theorem 25.3 makes their labels
meet every $\mathcal D_e$, so $|\mathcal G_\perp|\ge t_\perp$.
In the present scope the positive gates with labels outside $A_0$
already suffice, by Theorem 36.2.

The state sets $\mathcal P_3$ and $\mathcal G_\perp$ are disjoint.
A negative terminal literal gate cannot have positive short exits:
its zero edge already ends at terminal one. A positive gate in
$\mathcal G_\perp$ has label outside $A_0$.
By Theorem 25.3 all live occurrences of any literal gate are at the
corner. Thus their union is contained in

$$
(Q\setminus Q_{\rm live})\ \cup\ F_{(3,5)}\
\cup\!\!\bigcup_{p\in\Pi_4\setminus\{(3,5)\}}
                       (F_p\setminus\{q_p\}).
$$

The sum of the displayed pool sizes is $C+1$, even if some pools
intersect. The union bound gives
$t_3+t_\perp\le C+1$, proving $C\ge M_{\rm mix}$.
This is ordinary separated-set counting, not an injection from
histories or completion vectors to installed states.

There is a further applicable count when a cut family is present.
Let $\mathcal P_{\rm cut}$ consist of the positive-short states with
labels in $T_3$. The common-cut argument of Theorem 32.1 puts
every such state globally in $Q\setminus Q_{\rm live}$.
Their labels meet the cut family, so
$|\mathcal P_{\rm cut}|\ge t_{\rm cut}$. Their labels lie in
$A_0$, hence $\mathcal P_{\rm cut}$ is disjoint from
$\mathcal G_\perp$. The union is now contained just in
$(Q\setminus Q_{\rm live})\cup F_{(3,5)}$, giving

$$
\nu+b_{(3,5)}\ge t_{\rm cut}+t_\perp,\qquad
C\ge t_{\rm cut}+t_\perp+\lambda-1
                       \ge t_{\rm cut}+t_\perp .
\tag{SI.220}
$$

This proves $C\ge M_1$. If the axis family itself is cut-pinned,
the same $\mathcal P_{\rm cut}$ meets all its $D_e$ by
Theorems 29.2 and 32.1, so its size is at least $t_3$.
Replacing $t_{\rm cut}$ by $t_3$ in that very union count proves
(SI.217), irrespective of the optional cut family's choice.
It follows directly that $M_{\rm mix}$ is smaller than this valid
bound by one. With a cut family containing the axis family,
monotonicity of transversals gives $t_{\rm cut}\ge t_3$;
the complete-cut choice also gives this inequality by its hitting
set of available labels in $T_3$.

All transversal numbers are integers. The comparison with the $t_3$
branch of $M_0$ gives $t_\perp\ge2$; comparison with
$t_{\rm cut}+2$ gives $t_3+t_\perp\ge t_{\rm cut}+4$;
comparison with $t_{\rm lit}$ gives the last inequality of
(SI.215). The middle inequality also beats the constant branch two.
These implications reverse, proving (SI.215).
As $t_{\rm lit}\ge t_\perp$, its last inequality forces $t_3\ge2$.
Adding comparison with $t_{\rm cut}+t_\perp$ requires exactly
$t_3\ge t_{\rm cut}+2$. Together with $t_\perp\ge2$
this already implies the middle inequality of (SI.215), proving
the equivalence (SI.216).

In the cut-pinned scope, $t_3\le t_{\rm cut}\le3$ and
$t_\perp\le3$ give (SI.218) directly. Equivalently
$t_3+t_\perp\le t_{\rm cut}+3$, contradicting the middle
condition of (SI.215). Equation (SI.217) supplies a further
valid bound larger than $M_{\rm mix}$ by one without needing
to select the optional cut family. Thus omitting applicable cut
demands cannot certify a gain, and one axis demand cannot suffice
even for the general numerical strictness test.

Finally the equality for $m$ in (SI.214) is exactly (SI.198),
using SI Theorem 9.3 on this graph; $R\ge0$ is supplied by
Corollary 33.1. Thus
$R+E_B^{\setminus\Pi_4}+\max\{M_1,M_{\rm mix}\}\ge D_B$
is a sufficient condition for $m\ge24$, whereas (SI.199) with
the actual $C$ remains the exact condition. For a proposed mixed
term to make this substitution strict, its actual families must
first satisfy (SI.216), and any further available graph-specific
bound, including the versions with $\lambda,\gamma$ retained in
(SI.219)--(SI.220), must also be beaten. Selecting smaller comparison
families cannot establish strictness against the complete choices.
The proof supplies no graph realizing (SI.216) and no uniform
inequality covering the full deficit $D_B$.

The new model restriction is Theorem 36.2 and its cut-pinned
strictness obstruction; the finite unions, diagonal excess and exact
incidence arithmetic above reuse Sections 25--33 and SI's diagonal
criterion as intermediate facts. This is a repo-derived consequence
of the stated suppliers. The bounded classical comparisons remain
those with Bryant Section 2, Definition 1 and Cook, Edmonds,
Medabalimi and Pitassi Section 2.1: their ordered or acyclic and
semantic read-once hypotheses supply no normalization of the present
graph. No literature priority assertion is needed.

The classification (SI.209)--(SI.212) uses the actual cut $T_3$;
it is not transferred to gaps $(1,9)$ or $(2,9)$.
The mixed consumer here uses $\Pi_4$, not the unequal-depth
$\Pi_R$ axis consumer. The general axis family in Definition 36.1
need not satisfy Corollary 32.2; (SI.217) is conditional on
cut-pinning and is not an exclusion of every general-axis realization.
All assertions hold separately for each original positive increasing
position tuple and each permitted graph for that tuple. They retain
fixed successors, actual histories and cuts, both pointwise caps,
adaptive orders, paid certified traffic and union cycles.
Neither actual graph existence nor nonexistence is concluded.
The whole-table condition (SI.166), CP.28 and the unrestricted
nine-input minimum remain outside the proved consequences. $\square$

## 追加锚（本行以下为增补区）

## 37. One-host concentration and the complete cut-capacity comparison

**Definition 37.1 (the actual axis class of a fixed graph).** Fix any
original positive increasing position tuple and any one graph satisfying
Assumption 21.1 for that tuple, with $K\ge4$, $L\ge3$ and
$n=K+L-1$. In particular, correctness and termination hold on every
$\theta\in\{0,1\}^n$, and both original pointwise bounds
$t_P(\theta)\le n$ and $J_P(\theta)\le W$ hold on that same input,
with $c_i=s_i+4$. The graph may depend on the tuple. All installed
states count; coordinate order is adaptive, labels and successors are
fixed, certified repeats remain paid, and inconsistent paths and cycles
in the union graph remain permitted.

Write $(S_z^0,q_z)$ for the support and host of the unique actual
zero-axis history at $(0,z)$, $0\le z\le L-1$, and retain
$A_0=S_{L-1}^0$ from Definition 31.1. Let
$\mathcal A$ be the complete class of actual pairs of Definition 29.1
on this graph. For $e\in\mathcal A$, write its counts as
$(0,z_e),(3,w_e)$, its supports and upper assignment as
$S_e,T_e,\rho_e$, and put

$$
\begin{gathered}
X_e=S_e\setminus T_e,\qquad Y_e=T_e\setminus S_e,\qquad
I_e=S_e\cap T_e,\\
\delta_e=3+w_e-z_e,\qquad
D_e=\{j\in I_e:\rho_e(j)=1\}.
\end{gathered}
\tag{SI.221}
$$

Membership in $\mathcal A$ requires the two actual histories at one
installed state, not just these numerical data. It is a finite class:
each live prefix has at most $n-1$ fresh queries, and there are finitely
many Boolean inputs and prefixes. Repeated copies of a demand do not
change its transversal number.

**Theorem 37.2 (actual zero-axis concentration).** Every pair
$e\in\mathcal A$ extends by exactly $L-1-z_e$ common zero replies
along the installed lower zero-axis path to $q_{L-1}$. Both histories
remain actual and live throughout. Their final counts are

$$
(0,L-1),\qquad (3,L-4+\delta_e),\qquad
\delta_e\in\{0,1\},
\tag{SI.222}
$$

and their disagreement set is exactly $D_e$.

If $\mathcal A\ne\varnothing$, there is one support $T^*$ for
all actual live three-hit histories at $q_{L-1}$, and one value
$\delta\in\{0,1\}$ common to all $\delta_e$. Define

$$
\begin{gathered}
X^*=A_0\setminus T^*,\qquad Y^*=T^*\setminus A_0,\qquad
J=A_0\cap T^*,\\
\alpha=|X^*|,\qquad b=|Y^*|,\qquad
\beta_e=|\{j\in Y_e:\rho_e(j)=1\}|.
\end{gathered}
\tag{SI.223}
$$

Here $\alpha$ denotes private cardinality; cut depths below are denoted
by $s$. For every original pair, with $C_e=A_0\setminus S_e$,

$$
\begin{gathered}
C_e\cap(S_e\cup T_e)=\varnothing,\qquad
A_0=S_e\sqcup C_e,\qquad T^*=T_e\sqcup C_e,\\
X_e=X^*,\qquad Y_e=Y^*,\qquad
J=I_e\sqcup C_e,\qquad
\varnothing\ne D_e\subseteq I_e\subseteq J.
\end{gathered}
\tag{SI.224}
$$

The extended upper assignment is zero on $C_e$. In particular,

$$
\begin{gathered}
1\le\alpha\le b\le3,\qquad b-\alpha=\delta,\qquad
C_{X^*}\le C_{Y^*},\qquad |T^*|=L-1+\delta,\\
|J|=L-1-\alpha\le L-2,\qquad
|D_e|=3-\beta_e,\qquad 0\le\beta_e\le\min\{b,2\},\\
|[n]\setminus(A_0\cup T^*)|=K-b\ge K-3.
\end{gathered}
\tag{SI.225}
$$

For every actual common-support cut $T_s$ at a depth $s\le L-1$,

$$
T_s\subseteq J,\qquad
|J\setminus T_s|=L-1-\alpha-s\le L-2-s.
\tag{SI.226}
$$

Thus a nonempty axis class forces such a cut depth to satisfy
$s\le L-2$. For an actual common-support depth $s>L-1$, both
$A_0$ and $T^*$ are contained in $T_s$, so
$J\setminus T_s=\varnothing$. These are conditional assertions about
actual cuts; no support at the adjoined formal endpoint is used as an
actual history.

Proof. Fix an actual pair $e$ and abbreviate $z=z_e$, $w=w_e$.
Theorem 29.2 gives $\delta_e\in\{0,1\}$. Put
$r=L-1-z\ge0$. At the $t$-th step of the proposed common zero
continuation, $0\le t\le r$, its intended counts are
$(0,z+t)$ and $(3,w+t)$. The lower zero count is at most $L-1$,
and

$$
w+t\le w+r=L-4+\delta_e\le L-3.
$$

The upper hit count is $3\le K-1$. All these counts are nonnegative:
in particular the last upper zero count equals $w+r$, with $w,r\ge0$.
Both histories and, for $t<r$, both zero children are live.

Actuality follows inductively, not from treating a syntactic path as an
input. Initially the histories end at $q_z$. Suppose their actual
extensions share $q_{z+t}$. SI Theorem 2.2 makes its fixed queried
coordinate fresh for each history, hence outside the union of their
currently exposed supports. Giving it value zero is consistent separately
with each exposed assignment. Each new assignment has a full Boolean
completion following the corresponding prefix. Since both new count
pairs are live, the installed zero successor is running, and that single
successor is the next zero-axis host $q_{z+t+1}$. This proves the
induction through $r$, including $r=0$ without any extra step.

Let $C_e$ be the queried coordinates in this continuation. Freshness
makes them distinct and disjoint from $S_e\cup T_e$. The lower
extension is the unique zero-axis history of length $L-1$, so
$C_e=A_0\setminus S_e$ and $A_0=S_e\sqcup C_e$. The final
upper support is $T_e\sqcup C_e$. Both histories give every added
coordinate value zero. Their old intersection assignments are unchanged;
therefore their final disagreement set is exactly $D_e$, with no
coordinate removed, added or relabelled. The two full input completions
need not coincide: the incoming assignments can be incompatible.

Suppose $\mathcal A$ is nonempty, and choose one of these final upper
histories to define $T^*$. Apply the existing equal-hit support exclusion
[PE, Lemma 4.1][PE] through its Boolean interface in SI Section 2.
Every other final upper history has three hits at the same installed
state $q_{L-1}$, so its support must be $T^*$. The same supplied
exclusion applies to any other actual live three-hit history at that
state, whether or not it arose from the selected continuation. There
is no additional rigidity lemma here. Exact live depths from SI
Theorem 2.2 now give
$|T^*|=3+w_e+r=L-1+\delta_e$, fixing the single value $\delta$.

Taking differences and intersections in
$A_0=S_e\sqcup C_e$ and $T^*=T_e\sqcup C_e$, with
$C_e$ disjoint from both old supports, proves (SI.224). Theorem 29.2
on the original pairs supplies the private-size and cost inequalities
in (SI.225). Its nonempty disagreement has size $3-\beta_e$;
the upper private assignment is unchanged. Counting $A_0$ gives
$|J|=L-1-\alpha$, and counting
$A_0\cup T^*=A_0\sqcup Y^*$ gives the last equality in (SI.225).

If $s\le L-1$ is an actual common-support depth, both final live
histories have actual ancestors at depth $s$, since their depths are
$L-1$ and $L-1+\delta$. SI Lemma 9.2 puts $T_s$ in each
final support. Hence $T_s\subseteq J$; its cardinality $s$ proves
(SI.226). For $s>L-1$, integrality and $\delta\le1$ give
$s\ge L\ge L-1+\delta$. Extend both final histories live to
that actual common depth by SI Lemma 9.2. Their old supports are
contained in its common support $T_s$, proving the remaining claim.

All feasible depths and private cardinalities are covered by this
argument. An existing pair necessarily has
$3-\delta\le z_e\le L-1$ and $w_e=z_e+\delta-3$.
The necessary private-size candidates are
$(\alpha,b)\in\{(1,1),(2,2),(3,3)\}$ for $\delta=0$ and
$(\alpha,b)\in\{(1,2),(2,3)\}$ for $\delta=1$, additionally
subject to $|J|\ge1$ and every actual-cut restriction above. This
list asserts no realization of any candidate. If $\mathcal A$ is
empty, no $T^*,X^*,Y^*,J,\alpha,b$ or $\delta$ is manufactured;
all selected axis families have transversal zero. If only a selected
family is empty, the graph-owned sets still exist when $\mathcal A$
is nonempty. The argument modifies no installed state and removes no
paid visit from any run. $\square$

**Corollary 37.3 (the complete cut slice of an actual family).** Suppose
$\mathcal A\ne\varnothing$, and let $T_s$ be an actual common
support with $s\le L-1$. For any selected actual axis family
$\mathcal E\subseteq\mathcal A$, define

$$
\begin{gathered}
\mathcal C_s(\mathcal E)=
 \{D_e:e\in\mathcal E,\ D_e\subseteq T_s\},\qquad
 t_s(\mathcal E)=\tau(\mathcal C_s(\mathcal E)),\\
\tau_3(\mathcal E)\le t_s(\mathcal E)+|J\setminus T_s|,
\qquad \nu\ge t_s(\mathcal E).
\end{gathered}
\tag{SI.227}
$$

Here $\tau$ on a family of coordinate sets means its ordinary
coordinate transversal, not a signed literal transversal. Empty slices
have transversal zero.

Proof. Choose a minimum hitting set $H_s$ for the full slice
$\mathcal C_s(\mathcal E)$, inside $T_s$. Such a choice is
possible because all its edges are subsets of $T_s$; for an empty
slice take $H_s=\varnothing$. Every edge not in the slice contains
a coordinate outside $T_s$, and every edge lies in $J$ by Theorem
37.2. Consequently $H_s\cup(J\setminus T_s)$ meets every edge
of $\mathcal E$, proving the first inequality. Also
$s\le L-1\le n-3$ since $K\ge4$. Every edge retained in the
slice is a whole actual demand, with its positive-short supplier from
Theorem 29.2. Theorem 32.1 therefore gives $\nu\ge t_s(\mathcal E)$.
No supplier is claimed for a truncated set $D_e\cap T_s$: such an
intersection need not contain the supplied label. $\square$

**Definition 37.4 (three complete cut comparisons).** Now specialize to
one graph of Assumption 21.1 with $n=9$, $K=4$, $L=6$, and an
actual consecutive terminal gap $B=(3,9)$. Retain its actual $T_3$,
$|T_3|=3$, and $A_0$, $|A_0|=5$. Let $\mathcal A_B$ be all
actual axis pairs with both incoming cells in $V_B$, and choose any
$\mathcal E_3\subseteq\mathcal A_B$ with
$t_3=\tau_3(\mathcal E_3)$. Define separately

$$
\begin{aligned}
\mathcal C(\mathcal E_3)&=
 \{D_e:e\in\mathcal E_3,\ D_e\subseteq T_3\},&
 t_C(\mathcal E_3)&=\tau(\mathcal C(\mathcal E_3)),\\
\mathcal C_{\rm all}&=
 \{D_e:e\in\mathcal A_B,\ D_e\subseteq T_3\},&
 t_C^{\rm all}&=\tau(\mathcal C_{\rm all}).
\end{aligned}
\tag{SI.228}
$$

The first is the complete cut slice of the chosen family: it omits none
of that family's cut-contained demands. The second is the graph-complete
actual axis cut slice in this gap. Both consist of actual whole demands,
with the actual witnesses of Theorem 29.2.

A third comparison uses all available positive-short labels, independently
of whether an axis pair demands them. Put

$$
\begin{gathered}
Z_+=\{j\in[9]:\text{an installed state with label }j
                         \text{ has positive short exits}\},\\
Z_{\rm cut}=Z_+\cap T_3,\qquad Z_A=Z_+\cap A_0,\qquad
\mathcal C_{\rm av}=\{\{j\}:j\in Z_{\rm cut}\},\\
c=\tau(\mathcal C_{\rm av})=|Z_{\rm cut}|.
\end{gathered}
\tag{SI.229}
$$

Every singleton in $\mathcal C_{\rm av}$ has its defining installed
positive-short supplier. Thus it is a valid Theorem 32.1 demand at
$T_3$, without an assertion that it is an actual axis disagreement.
Equivalently one can take all nonempty $D\subseteq T_3$ satisfying
$D\cap Z_{\rm cut}\ne\varnothing$; this larger valid cut family
has the same transversal $c$ because it contains precisely those
available singletons as singleton members.

Retain an arbitrary optional cut family $\mathcal E_{\rm cut}$ of
Definition 36.1 and its $t_{\rm cut}$. It need not be an axis
subfamily. A cut subfamily of $\mathcal C_{\rm all}$ has transversal
at most $t_C^{\rm all}$, but no ordering of a general optional
$t_{\rm cut}$ and $t_C^{\rm all}$ is built into the definitions.
Available labels in $Z_A\setminus J$, when $J$ exists, can come
from other or unused installed states and are not deleted.

**Theorem 37.5 (the single-exception cut lift).** In Definition 37.4,
if any actual axis pair exists on the graph, its concentrated intersection
satisfies

$$
T_3\subseteq J,\qquad |J|=5-\alpha,\qquad
\varepsilon:=|J\setminus T_3|=2-\alpha\in\{0,1\}.
\tag{SI.230}
$$

In particular $\alpha\in\{1,2\}$. If $\alpha=2$, then
$J=T_3$ and all actual axis demands are cut-pinned, including any
unequal-depth pairs with $(\alpha,b)=(2,3)$. Every such pair in
$\mathcal A_B$ has lower depth $z_e=5$. If $\alpha=1$, there
is one graph-owned coordinate $x$ with $J=T_3\sqcup\{x\}$.
For every selected $\mathcal E_3$,

$$
\begin{gathered}
t_C(\mathcal E_3)\le t_C^{\rm all}\le c\le3,
\qquad \nu\ge c,\qquad t_{\rm cut}\le c,\\
t_3\le t_C(\mathcal E_3)+\varepsilon
     \le t_C^{\rm all}+\varepsilon
     \le c+\varepsilon\le c+1,\qquad t_3\le |Z_A|.
\end{gathered}
\tag{SI.231}
$$

If no axis pair exists, set $\varepsilon=0$ for these numerical
inequalities only; all axis slices are empty and $t_3=0$.
No upper support is required in that case.

Proof. Apply (SI.226) at the actual depth three. It gives
$T_3\subseteq J$ and $|J\setminus T_3|=5-\alpha-3$.
Since $\alpha\ge1$, its nonnegative value is zero or one, proving
(SI.230). For a pair in $V_B$, its lower live depth is four or
five. Actual ancestry at $T_3$ gives $T_3\subseteq I_e$.
If $\alpha=2$, then $|I_e|=z_e-2\ge3$, so $z_e=5$;
this argument does not require equal upper and lower depths.

Corollary 37.3 at $s=3$ proves the first bound for $t_3$ using
the complete chosen-family slice. Explicitly, every edge outside that
slice contains the same $x$ if $\varepsilon=1$; if
$\varepsilon=0$, no such edge exists. Add that one coordinate to a
minimum hitting set of the slice. Inclusion of the two actual slices
gives $t_C(\mathcal E_3)\le t_C^{\rm all}$. For each edge of
$\mathcal C_{\rm all}$, Theorem 29.2 supplies a positive-short
label in that whole edge, hence in $Z_{\rm cut}$. Thus
$t_C^{\rm all}\le c$. Theorem 32.1 applies to every available
singleton at $T_3$, giving $\nu\ge c$, and $c\le|T_3|=3$.
The equality $\tau(\mathcal C_{\rm av})=c$ also follows directly:
each singleton forces its own coordinate into a hitting set, and their
union hits the entire family.

For a general optional cut family in Definition 36.1, every applicable
cut has depth at most six, hence at most three by consecutiveness of
$B=(3,9)$. The actual common supports form a chain, so each of these
supports lies in $T_3$. Each optional demand therefore has a supplier
with label in that demand and in $Z_{\rm cut}$. The set
$Z_{\rm cut}$ hits every optional demand, proving $t_{\rm cut}\le c$.
It does not make that optional family an axis subfamily. Taking all the
available singleton labels attains the maximum transversal over these
allowed cut families.

For every actual axis demand, Theorem 29.2 supplies a label in $D_e$,
and Theorem 37.2 places $D_e$ in $J\subseteq A_0$. Thus
$Z_+\cap J$ hits every selected axis edge, and $Z_A$ does too.
More explicitly,

$$
t_3\le |Z_+\cap J|
   =c+|(Z_+\cap J)\setminus T_3|
   \le c+\varepsilon.
$$

This does not assert $|Z_A|\le c+1$: labels in $A_0\setminus J$
need not belong to any axis demand. The empty cases follow from the
zero transversal convention. If the chosen family is cut-pinned, then
$t_3=t_C(\mathcal E_3)$, independent of an optional family's
choice. For an arbitrary optional subfamily, (SI.231) supplies no
replacement of $t_C(\mathcal E_3)$ or $c$ by its possibly smaller
$t_{\rm cut}$. Such a replacement would discard the completeness
premise; no actual-graph counterexample to it is asserted here.
$\square$

**Proposition 37.6 (paid private sizes and the one-hit-prefix restriction).**
In Definition 37.4 every actual selected axis family satisfies

$$
t_3\le3.
\tag{SI.232}
$$

More precisely, in the $\alpha=1$ case, $b\in\{1,2\}$.
If $b=1$, every axis demand has size three and $t_3\le2$.
If $b=2$, every axis demand has size at least two. If
$\alpha=1$ and $t_3=3$, then every separated family
$\mathcal E_\perp$ of Definition 36.1 on this same graph obeys

$$
t_\perp\le2.
\tag{SI.233}
$$

Proof. The private-set bounds are those of Theorem 37.2. The paid
supplier used here is the upper-private-one implication in
[Support Barriers, Lemma 2.3][SB37], equivalently the Boolean
instance of [PE, Theorem 3.1(2)--(3)][PE]. In its notation the
correspondence is

$$
(k,h,g,S,T,X,Y,U,a,b)
  =(4,0,3,S_e,T_e,X^*,Y^*,[9]\setminus(S_e\cup T_e),\alpha,b).
$$

The original $c_i$ are unchanged. The lower private bits are all zero,
so the supplied lower-private-zero implication is already applicable.
If all upper private bits are one, the other supplied implication gives
$b\le\alpha$ and $C_{Y^*}\le C_{X^*}$; together the two give
$b=\alpha$ and equality of the two private costs. These are the
published one-sided exchanges, used as intermediate facts.

The native/Boolean interface here does not identify arbitrary native
histories by a count label. SI Convention 1.3 lifts this original
Boolean graph unchanged to the selected literals after the paid profile
front. Each of the present Boolean histories becomes an actual selected
cube history there, with the same $S_e,T_e,\rho_e$, the same fixed
selected successors, and original selected costs. The lift's simultaneous
native bounds are $n+1,W+3$, with its profile charge included; PE
Theorem 3.1 has $n=9,k=4$ in its permitted range. Support Barriers
Lemma 2.3 states precisely the Boolean implications at bounds $n,W$.
Thus the supplied conclusion concerns this graph and its actual
completions, including the paid private repeats in the exchanged suffix.
It assumes neither subset-sum nonresonance nor free certified traffic.

If $\alpha=2$, then $J=T_3$ has size three, and $t_3\le3$
follows immediately. Suppose $\alpha=1$. For $b=1$, an actual
pair with $\beta_e=1$ would have all upper private bits one.
The supplied exchanges would force $C_{X^*}=C_{Y^*}$ for two
nonempty disjoint singletons. Their coordinates differ, while the
individual original costs are distinct, a contradiction. Hence
$\beta_e=0$ for every pair, and $|D_e|=3-\beta_e=3$.
Every two-element subset of the four-element $J$ meets every such
three-element edge, proving $t_3\le2$. Equality of general subset
sums is not excluded or used in this singleton argument.

For $b=2$, the case $\beta_e=2$ would instead have all upper
private bits one and force $2=b\le\alpha=1$, another contradiction.
Thus $\beta_e\le1$, so every actual edge has size at least two
inside the four-element $J$. Every three-element subset of $J$
meets every such edge. This proves (SI.232), including the empty
family, and excludes precisely the indicated upper-private-one cases.

Now assume $\alpha=1$ and $t_3=3$. The $b=1$ case is
impossible, so $b=2$, $J=T_3\sqcup\{x\}$, and the selected
actual edges all have size at least two. No two-element subset
$H\subseteq J$ can hit every selected edge. Therefore some actual
$D_e$ is disjoint from $H$, hence contained in the two-element
$J\setminus H$. Its minimum size forces
$D_e=J\setminus H$. As $H$ ranges over all two-element subsets,
this proves that all six two-element subsets of $J$ occur as actual
demands in $\mathcal E_3$. They are consequences of its assumed
actual transversal value, not postulated formal patterns.

In particular, for every $u\in T_3$ there is an actual pair with
$D_e=\{x,u\}$. Extend it to $q_5$ by Theorem 37.2. Its upper
assignment on $T_3$ is one at $u$ and zero at the other two
coordinates: on $J$ the upper ones are exactly $D_e$, since the
added coordinates $C_e$ are all zero. Its upper final support is
$T^*$, with $|T^*|=6$. The actual depth-three ancestor of this
upper history has support $T_3$ and that one-hit assignment.

For each $u\in T_3$, let $r_u$ be the unique actual depth-three
host with this assignment, as in the proof of Corollary 36.3.
Its uniqueness is deterministic: two completions agreeing on $T_3$
follow the same first three queries, each in their depth-three support
$T_3$, with the same replies. Existence here is also witnessed by the
actual upper history just obtained. Its next coordinate is fresh, and
is read before that history's final depth six, so

$$
i(r_u)\in T^*\setminus T_3\qquad(u\in T_3).
\tag{SI.234}
$$

Theorem 36.2 and Corollary 36.3 say that every separated singleton
label is $i(r_u)\notin A_0$ for one of these three actual one-hit
prefixes. Combining this fact with (SI.234) gives

$$
\{j_e:e\in\mathcal E_\perp\}
 \subseteq\{i(r_u):u\in T_3\}\setminus A_0
 \subseteq T^*\setminus A_0=Y^*.
$$

The last set has size $b=2$. The separated transversal equals the
number of distinct such singleton labels by Corollary 36.3, proving
(SI.233). Coincident hosts or labels only reduce that number. All
prefixes, final supports and separated labels refer to this one actual
graph. No existence of a graph with $t_3=3$ is asserted. $\square$

**Corollary 37.7 (complete-cut redundancy and the exact capacity consumer).**
Retain Definition 37.4 and the separated and literal families of
Definition 36.1, with $\mathcal E_{\rm lit}$ containing
$\mathcal E_\perp$. Write $p=t_\perp$, so
$0\le p\le3$ and $t_{\rm lit}\ge p$. Use the same actual
$\lambda,\gamma,C=\nu+\lambda+\gamma$ of (SI.213), with
$\lambda\ge1$, $\gamma\ge1$, and define the comparisons using
all available cut labels by

$$
\begin{gathered}
M_0(c)=\max\{2,t_3,t_{\rm lit},c+2\},\qquad
M_1(c)=\max\{M_0(c),c+p\},\\
M_{\rm mix}=t_3+p-1.
\end{gathered}
\tag{SI.235}
$$

On this same graph the retained-diagonal bound is

$$
\begin{aligned}
C&\ge\lambda+\max\{t_{\rm lit}-1,c+\gamma,c+p-1\}\\
 &\ge\max\{t_{\rm lit},c+2,c+p\}
   =M_1(c),\\
M_0(c)&=\max\{t_{\rm lit},c+2\},\qquad
M_1(c)=\max\{t_{\rm lit},c+\max\{2,p\}\},\\
M_{\rm mix}&\le c+p\le M_1(c).
\end{aligned}
\tag{SI.236}
$$

Thus both the $t_3$ branch of the complete $M_0$ comparison and
the extra mixed branch after the complete $M_1$ comparison are
universally redundant. The same redundancy after $M_1$ holds when
$c$ is replaced throughout by $t_C^{\rm all}$ or by
$t_C(\mathcal E_3)$, using the corresponding complete valid cut
family for its capacity bound.

For comparison with $M_0(c)$ alone, the strongest restriction supplied
by these relations and Proposition 37.6 is the exact conditional test

$$
\begin{gathered}
M_{\rm mix}\le M_0(c)+1,\\
M_{\rm mix}>M_0(c)
\quad\Longleftrightarrow\quad
(c,t_3,p,t_{\rm lit})=(1,2,3,3).
\end{gathered}
\tag{SI.237}
$$

This equivalence compares the expressions for actual graph/family data.
It does not assert a graph realizing the displayed tuple. In that
conditional tuple $M_0(c)=3$ and $M_{\rm mix}=M_1(c)=4$.
Universal $M_{\rm mix}\le M_0(c)$ is not concluded.

Proof. For each $j\in Z_{\rm cut}$ choose one installed
positive-short state with fixed label $j$. Different labels require
different states. Theorem 32.1 puts every chosen state globally in
$Q\setminus Q_{\rm live}$, giving $\nu\ge c$.
For each distinct singleton label demanded by $\mathcal E_\perp$,
choose one supplying positive terminal literal gate from Theorem 25.3.
There are $p$ such chosen gates by Theorem 36.2 and Corollary 36.3.
Their fixed labels lie outside $A_0$, whereas the $c$ cut states
have labels in $T_3\subseteq A_0$. These two chosen state sets
are therefore disjoint.

Every live occurrence of a chosen literal gate is at the corner
$(3,5)$, by Theorem 25.3. Consequently their disjoint union is
contained in $(Q\setminus Q_{\rm live})\cup F_{(3,5)}$.
Its cardinality gives the actual same-graph inequality

$$
c+p\le\nu+b_{(3,5)}=\nu+\gamma+1.
\tag{SI.238}
$$

A gate supplying several demands is chosen once per distinct required
label; a state belongs to just one chosen set here. In particular a
never-live gate is not charged again as a separate corner resource.
The source literal-family bound is
$t_{\rm lit}\le\nu+b_{(3,5)}=\nu+\gamma+1$ by Theorem 26.2.
Together with $\nu\ge c$ and (SI.238), these give respectively

$$
C\ge t_{\rm lit}+\lambda-1,\qquad
C\ge c+\lambda+\gamma,\qquad
C\ge c+p+\lambda-1.
$$

Their maximum is the first line of (SI.236). These are three lower
bounds on one pool; their transversal contributions have not been added.
Using only $\lambda,\gamma\ge1$ gives its second line. By
Theorem 37.5, $t_3\le c+1<c+2$, and $c+2\ge2$.
The simplifications of $M_0(c)$ and $M_1(c)$ follow, as does
$M_{\rm mix}\le c+p$. For either complete actual slice in
(SI.228), Corollary 37.3 supplies $t_3\le t_C+1$, Theorem
32.1 supplies $\nu\ge t_C$, and the identical disjoint union
argument supplies $t_C+p\le\nu+b_{(3,5)}$. Thus the same
$M_1$ domination holds without identifying either $t_C$ with $c$.

For the strict $M_0(c)$ comparison, $p\le3$ and $t_3\le c+1$
first give $M_{\rm mix}\le c+3\le M_0(c)+1$.
Strictness over its $c+2$ branch requires
$t_3+p\ge c+4$. The two upper bounds force $p=3$ and
$t_3=c+1$. Strictness over $t_{\rm lit}$ is then exactly
$t_{\rm lit}\le c+2$. Conversely these three integer conditions
give $M_{\rm mix}=c+3>M_0(c)=c+2$.

Now $t_{\rm lit}\ge p=3$ implies $c\ge1$, and
$t_3\le3$ from Proposition 37.6 implies $c\le2$.
If $c=2$, then $t_3=3$. The case $\alpha=2$ would be
cut-pinned and give $t_3\le c$, impossible. Hence $\alpha=1$,
and (SI.233) gives $p\le2$, also impossible. It follows that
$c=1$, $t_3=2$ and
$3=p\le t_{\rm lit}\le c+2=3$, proving the forward implication
of (SI.237). Conversely the displayed tuple directly gives the stated
values $3,4,4$, proving the reverse implication as a comparison of
expressions. If the axis class is empty, $t_3=0$ and none of these
strictness conditions can arise. If the selected axis family is
cut-pinned, $t_3\le c$ and
$M_{\rm mix}\le c+p-1\le c+2\le M_0(c)$ instead.

For an arbitrary optional $t_{\rm cut}$, its $M_0$ or $M_1$
can be smaller than the complete comparison. The proof neither replaces
$c$ by every optional selection in $t_3\le c+1$, nor claims
$M_{\rm mix}\le M_1(t_{\rm cut})$ for every such choice.
It proves that the complete applicable cut bound on this same graph
already absorbs the mixed term. Omitting available demands cannot
establish a gain against all applicable capacity bounds. $\square$

**Proposition 37.8 (unchanged unrestricted deficit and source boundaries).**
In the scope of Corollary 37.7 the exact incidence identity is still

$$
\begin{gathered}
m=24+R+E_B^{\setminus\Pi_4}-D_B+C,\qquad R\ge0,\\
m\ge24\quad\Longleftrightarrow\quad
R+E_B^{\setminus\Pi_4}+C\ge D_B.
\end{gathered}
\tag{SI.239}
$$

A sufficient substitution supplied by (SI.236) is

$$
R+E_B^{\setminus\Pi_4}
 +\lambda+\max\{t_{\rm lit}-1,c+\gamma,c+p-1\}\ge D_B.
\tag{SI.240}
$$

The weaker sufficient substitution uses
$\max\{t_{\rm lit},c+\max\{2,p\}\}$ in place of the retained
$\lambda,\gamma$ expression. None of the foregoing inequalities
establishes either sufficient substitution uniformly for every permitted
graph and original tuple.

Proof and mathematical correspondence. Equation (SI.239) is Corollary
33.1 with $\Pi=\Pi_4$, or (SI.214), on the same installed graph.
Substitution of its actual capacity lower bound (SI.236) proves the
sufficiency of (SI.240), without replacing any of the other incidence
terms. In particular no new transversal equality or relation bounds the
full unrestricted $D_B$ by these resources.

The substantive composition in this section is the actual continuation
to a single zero-axis host, preservation of both private sets, the
resulting common intersection with at most one coordinate outside the
actual cut, and its complete-cut capacity consumer. SI Theorem 2.2
supplies exact live depths, actual fixed successors, freshness and the
unique zero axis. Theorem 29.2 supplies the required depth slack,
nonempty disagreements and actual short-exit witnesses. PE Lemma 4.1,
through SI Section 2, supplies equal-hit support rigidity directly;
it is not reproved as new content. SI Lemma 9.2 supplies the actual
ancestors and common-cut support chain. The paid refinement uses the
already published upper-private-one exchange in Support Barriers
Lemma 2.3 and PE Theorem 3.1, with the parameter and source mapping
in Proposition 37.6. Theorem 36.2 supplies the actual one-hit prefixes
and their fixed fourth-query labels; the extra restriction (SI.233)
uses those prefixes of actual edges forced by $t_3=3$. Sections
26, 30--33 and 36 supply gate localization, cut pinning, diagonal
excess and the finite same-graph capacity unions.

These are repo-derived paper deductions from the cited suppliers.
The overlap already supplied by equal-hit rigidity, one-sided exchanges,
short-exit witnesses and cut-pinned counting is retained as such. The
classical comparison remains bounded by [Bryant, Section 2, Definition
1][Bryant] and [Cook, Edmonds, Medabalimi and Pitassi, Section
2.1][CEMP]: strict increase of variable indices in the former and
acyclicity with semantic read-once restrictions on consistent accepting
paths in the latter are additional model hypotheses. Neither supplies
this graph with a size-preserving normalization, and neither justifies
removing paid certified queries. The concentration and prefix deductions
use actual histories of the original graph throughout; ordinary
hypergraph transversals and finite union bounds do not assert that every
formal edge pattern or numerical capacity profile is realizable. No
worldwide novelty or physical-memory conclusion is attached to these
paper deductions.

The remaining requirement is a uniform proof of the exact inequality
in (SI.239), or another sufficient condition paying its full deficit.
The whole-table condition (SI.166), [CP, (CP.28)][CP] and the
unrestricted nine-input minimum $24$ remain unresolved by this section.
The $T_3$ and prefix conclusions here are not transferred to terminal
gaps $(1,9)$ or $(2,9)$, and the complete mixed comparison here uses
$\Pi_4$, not the separate unequal-depth $\Pi_R$ consumer.
Every assertion is quantified separately over every original position
tuple and every permitted graph for that tuple. $\square$

[SB37]: FIB_NATIVE_SUPPORT_BARRIERS_AND_SHORT_BLOCK_COMPENSATION.md

## 追加锚（本行以下为增补区）
