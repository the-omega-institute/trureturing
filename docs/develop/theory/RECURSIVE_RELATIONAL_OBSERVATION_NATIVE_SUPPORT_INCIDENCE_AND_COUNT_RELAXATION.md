# Actual support incidence and the exact count relaxation in native threshold preparation

## 1. Fixed source, prescribed entry and counted graph

**Definition 1.1 (original source and prescribed entry).** Use the finite
ordered trees and homomorphism of [WTF, Definitions 1.1–1.4][WTF]:

$$
\mathcal T::=\alpha\mid\beta\mid\langle\mathcal T,\mathcal T\rangle,
\qquad \rho\alpha=\beta,\quad
\rho\beta=\langle\beta,\alpha\rangle,
\quad \rho\langle v,w\rangle=\langle\rho v,\rho w\rangle.
$$

The complete current row at the cut $\{L,R\}^3$ has equality classes

$$
\{LLL,LRL\}=a,\quad \{LLR\}=b_1,\quad \{LRR\}=b_2,
\quad \{RLL,RRL\}=c,\quad \{RLR\}=b_3,\quad \{RRR\}=b_4.
$$

Different classes are disequal. Write this row as $R_*$ and retain the
entire unbounded original fiber

$$
\mathcal U_* = \{u\in\mathcal T:R_{\{L,R\}^3}(\rho u)=R_*\}.
$$

A complete predecessor row includes its ordered exterior, occurrences,
canonical equality partition, disequalities and strict-prefix guards.
There is no bound on the size, depth or interior shape of a source.

Fix $n\ge6$, $3\le k\le n-2$, distinct positive original positions
$A=\{s_1<\cdots<s_n\}$ and $r\ge0$. Put

$$
w_i=L^{s_i}R,\qquad a_i=LLLw_i,\qquad c_i=s_i+4,
\qquad C_B=\sum_{i\in B}c_i,\qquad W=C_{[n]}.
\tag{SI.1}
$$

For a branch image $B$, let
$\theta_i(B)=\mathbf1_{\{r_B(w_i)=\mathsf{branch}\}}$; alpha, beta
and absent each contribute zero. Keep the original eleven profiles and
the literal pointwise code

$$
\sigma_{A,k}(u)=
\begin{cases}
0,&u\in\Pi_1\cup\Pi_2,\\
1,&u\in\Pi_3\cup\Pi_4,\\
\mathbf1_{\{\sum_i\theta_i(x_a)\ge k\}},&u\in Z_{b_3},\\
0,&u\text{ is in another zero profile}.
\end{cases}
\tag{SI.2}
$$

The required result of preparation is the original latch
$\widehat e_{\sigma_{A,k}(u)}$, followed by the original complete entry
$e_{\sigma_{A,k}(u)}$. The separate reader of [WTF, Convention 1.3][WTF]
has eight installed states and uses at most two fresh queries and six
fresh letters. Returning another usable entry does not meet (SI.2).

**Definition 1.2 (Boolean execution model).** A graph $P$ has a finite
set $Q$ of installed running states, two distinct output terminals
$\mathsf0,\mathsf1$, a fixed running start, a fixed coordinate
$i(q)\in[n]$ at each $q\in Q$, and two fixed successors
$\delta(q,0),\delta(q,1)$. Its entire changing configuration is its
current state. On $\theta\in\{0,1\}^n$, a visit to $q$ reads
$\theta_{i(q)}$, costs one query and $c_{i(q)}$ letters, and follows
the indicated successor. Set $m=|Q|$; even unused installed states count.

Unless explicitly called a relaxation, $P$ must terminate on every
input with output $\mathbf1_{\{|\theta|\ge k\}}$, and must satisfy
simultaneously

$$
t_P(\theta)\le n,\qquad J_P(\theta)\le W
\quad(\theta\in\{0,1\}^n).
\tag{SI.3}
$$

Arbitrary coordinate orders, sharing, repeated queries, paid queries
after certification and syntactic cycles are allowed. Only actual runs
must terminate. A path assigning two different replies to the same
coordinate need not be an actual run. No counter, clock, history,
computed-address register or other changing configuration is supplied.

Write

$$
K=k,\qquad L=n-k+1,\qquad
V=\{0,\ldots,K-1\}\times\{0,\ldots,L-1\},\qquad G=KL.
\tag{SI.4}
$$

**Convention 1.3 (native correspondence and separate services).**
The supplied [WTF, Theorem 4.1][WTF] identifies native uniform
feasibility with the Boolean model by

$$
\mathsf N_{A,k,r}(H,p,\ell)
\quad\Longleftrightarrow\quad
\mathsf B_{c,k}(H-4-r,p-1,\ell-3).
\tag{SI.5}
$$

Its lift installs the Boolean graph unchanged at the shortest literals
$a_i$, adds the two profile states and the original-entry latches, and
works on every source in $\mathcal U_*$. Its projection follows actual
selected-state subsequences. Neither direction asserts read-once or
grid normalization. A Boolean graph with $m$ running states has $m+2$
states including its terminals, and the native lift has $m+4+r$
preparation states. The terminals are not charged a second time.

Actual source binding, the fixed register, acquired same-version row,
authentication, permission, export, access isolation, code-only handoff,
lawful complete entry and stationary service remain the supplied
assumptions of [WTF, Assumption 1.5][WTF]. Installed-state count,
retained export alphabet, table and address representation, workspace,
elapsed time and physical memory are distinct resource quantities.

## 2. Actual support and live-host incidence

**Definition 2.1 (histories and incidence).** A history is an actual
finite run prefix ending immediately before a query. Its exposed
support $S\subseteq[n]$ consists of coordinates already read. Its
exposed assignment is denoted by $\eta_S$. Put

$$
h=|\eta_S^{-1}(1)|,\qquad z=|\eta_S^{-1}(0)|.
$$

It is live when both threshold outputs have completions, equivalently
$(h,z)\in V$. For $p=(h,z)\in V$, define

$$
\begin{aligned}
F_p&=\{q\in Q:\text{some actual live history of counts }p
                         \text{ ends at }q\},\\
\mathcal S_p&=\{S:\text{some such history has support }S\},\\
\mathcal R&=\{(p,S,q):\text{one actual live history witnesses all three}\},\\
b_p&=|F_p|,\qquad a_p=|\mathcal S_p|.
\end{aligned}
\tag{SI.6}
$$

A state in $F_p$ is a live host of $p$. A cell is support-ambiguous
when $a_p>1$. These sets are mathematical indices of actual histories;
they add no accessible coordinates to the running graph.

The native lift in (SI.5) transports every actual Boolean history to
an actual cube history after its paid profile front. The saturation
and exclusion facts used below are precisely [PCA, Theorems 34.3 and
35.1][PCA], [PE, Lemma 4.1][PE], and [WTF, Convention 6.1 and Theorem
9.1][WTF]. In Boolean language they give fresh queries at live histories;
exclude properly nested supports at a common state; exclude different
supports with equal hits at a common state; exclude equal supports with
unequal hits; and, for different count pairs at a common state, require
the orientation

$$
(h,z),(g,w),\ h<g
\quad\Longrightarrow\quad g-h\ge2,
\qquad z-w\ge2.
\tag{SI.7}
$$

Their hypotheses include both caps in (SI.3) and the original distinct
costs. These are supplied local facts, not consequences of assigning
abstract count labels to nodes.

**Theorem 2.2 (actual support incidence and fixed successors).** For
every graph in Definition 1.2 and every $p=(h,z)\in V$, the following
properties hold.

1. $F_p$ and $\mathcal S_p$ are nonempty. Each support in
   $\mathcal S_p$ has size $h+z$, and every witnessing history has
   exactly $h+z$ preceding queries.
2. At fixed $p$ and $q$, there is at most one $S$ with
   $(p,S,q)\in\mathcal R$. Consequently $b_p\ge a_p\ge1$.
3. If $(p,S,q)\in\mathcal R$, then $i(q)\notin S$. For
   $\varepsilon\in\{0,1\}$ put
   $p_\varepsilon=(h+\varepsilon,z+1-\varepsilon)$. Whenever
   $p_\varepsilon\in V$,

$$
(p_\varepsilon,S\cup\{i(q)\},\delta(q,\varepsilon))\in\mathcal R.
\tag{SI.8}
$$

   In particular both live children of one history have the same
   exposed support, and their hosts are the actual fixed successors
   of that history's state.
4. Every positive-depth live occurrence has an actual live predecessor.
   The cells on either axis have one support and one host:
   $a_{0,z}=b_{0,z}=a_{h,0}=b_{h,0}=1$.

Proof. Every completion of an exposed assignment follows the same
history, by deterministic induction. Freshness at live histories follows
from the cited saturation theorem applied to the full-fiber lift.
All earlier prefixes of a live history are live: their hit and zero
counts cannot exceed the current live counts. Thus each preceding
query was fresh, proving the depth assertion and the predecessor claim.

Every $p=(h,z)$ is realized by answering the first $h$ fresh queries
one and the next $z$ fresh queries zero. All prefixes stay live. A live
prefix cannot halt, and its next coordinate is fresh. The simultaneous
cube supplier realizes every completion, so these are actual histories.
This is also the Boolean form of the witness construction in
[PE, Theorem 4.2][PE].

Two different supports at fixed $p,q$ would have equal hits at a
common state, contrary to PE Lemma 4.1. The resulting map from $F_p$
onto $\mathcal S_p$ proves $b_p\ge a_p$. Freshness gives
$i(q)\notin S$. Either value of this unread bit can be completed to
an actual input following the old history. When its new counts are
live, its successor cannot be a terminal. This proves (SI.8) with
the installed successor, rather than a separately chosen host.

Finally, a live history with no ones follows the unique deterministic
all-zero reply prefix from the fixed start, and has exactly $z$
queries. There is therefore just one support and host at $(0,z)$.
The all-one prefix proves the other axis assertion. $\square$

## 3. Disjoint live families and support multiplicity

**Definition 3.1 (count separation).** Give $V$ the strict partial order

$$
(h,z)\prec(g,w)
\quad\Longleftrightarrow\quad
g-h\ge2\ \text{ and }\ z-w\ge2.
\tag{SI.9}
$$

An antichain is a set containing no two comparable distinct cells.
Put $w_0=2K+2L-4=2n-2$. For $0\le j\le K-2$, define

$$
\begin{aligned}
\mathcal A_j={}&
  (\{j,j+1\}\times\{0,\ldots,L-1\})\\
&\cup(\{0,\ldots,j-1\}\times\{0,1\})\\
&\cup(\{j+2,\ldots,K-1\}\times\{L-2,L-1\}),
\end{aligned}
\tag{SI.10}
$$

where an empty integer range contributes nothing.

**Theorem 3.2 (support and host multiplicity inequalities).** If
$\mathcal A\subseteq V$ is an antichain, its live-host sets are
pairwise disjoint and

$$
m\ge\sum_{p\in\mathcal A}b_p
   \ge\sum_{p\in\mathcal A}a_p.
\tag{SI.11}
$$

Each $\mathcal A_j$ is an antichain of size $w_0$, and their union
is $V$. In particular, for every such $j$,

$$
\begin{aligned}
\sum_{p\in\mathcal A_j}(b_p-1)&\le m-w_0,\\
\sum_{p\in\mathcal A_j}(a_p-1)&\le m-w_0.
\end{aligned}
\tag{SI.12}
$$

Proof. If $F_p$ and $F_q$ intersect for different cells, their actual
histories satisfy (SI.7), so $p$ and $q$ are comparable. Antichain
cells therefore have disjoint host sets. Their union lies in $Q$;
Theorem 2.2 then proves (SI.11). This counts distinct installed states,
including every host at each chosen cell, rather than adding costs
or separators from incompatible source runs.

For (SI.10), two middle-row cells have hit gap at most one. Two cells
in the earlier rows have zero gap at most one, as do two cells in the
later rows. From an earlier row to a middle row the zero decrease is
at most one, since the earlier zero count is at most one. From a
middle row to a later row it is at most one, since the later zero
count is at least $L-2$. From an earlier row to a later row it is
also at most one. None can satisfy (SI.9).

The three row ranges are disjoint, giving
$|\mathcal A_j|=2L+2(K-2)=w_0$. A cell in row $h$ belongs to the
middle rows for some $j$: use $j=h$ if $h\le K-2$, and $j=K-2$
for the last row. Thus these sets cover $V$. Subtracting their
cardinality from (SI.11) gives (SI.12). $\square$

## 4. Rigidity of supports and hosts

**Theorem 4.1 (singleton supports force one live coordinate order).**
Suppose $a_p=1$ for every $p\in V$. There are sets

$$
\varnothing=T_0\subsetneq T_1\subsetneq\cdots
\subsetneq T_{n-1}\subsetneq T_n=[n],\qquad |T_d|=d,
\tag{SI.13}
$$

such that $\mathcal S_{h,z}=\{T_{h+z}\}$. If
$T_{d+1}\setminus T_d=\{x_{d+1}\}$, every live query at depth
$d$ tests $x_{d+1}$. The $x_1,\ldots,x_n$ form a permutation of
$[n]$. Different cells have disjoint live-host sets, and hence

$$
m\ge\sum_{p\in V}b_p\ge G.
\tag{SI.14}
$$

If instead the hypothesis is stated as $b_p=1$ for every cell, it
implies all these conclusions. Its unique hosts $q_p$ are distinct,
and every live edge from $q_p$ is the edge to the unique host of
the corresponding child cell.

Proof. Consider consecutive cells $(h,z)$ and $(h+1,z-1)$ on one
depth diagonal, where $z\ge1$. Their common parent $(h,z-1)$ is
live. Take one actual history at that parent. Its zero and one
children are live and, by (SI.8), have the same support. Since the
two child cells each have a singleton support family, their supports
are equal. The admissible hit counts on a diagonal form an integer
interval, so this comparison connects the entire diagonal. Denote
its common support by $T_d$. This argument also shows that whenever
all cells of a particular diagonal have singleton support families,
that diagonal has a common support; no singleton premise is needed
on its parents.

For $d<n-1$, any cell at depth $d$ has at least one live child.
At any of its actual histories, (SI.8) yields
$T_{d+1}=T_d\cup\{i(q)\}$. Sizes and freshness give strict
containment and determine $i(q)=x_{d+1}$ uniquely. At depth $n-1$
there is one cell, $(K-1,L-1)$. Its support omits just one coordinate,
so freshness determines the final query as well. This proves
(SI.13) and the common live order.

At one depth, different cells have equal supports and unequal hits,
so PCA Theorem 35.1 excludes a common host. At different depths
their supports are properly nested, so PE Lemma 4.1 excludes a common
host. Their host sets are disjoint, proving (SI.14). Finally
$b_p=1$ implies $a_p=1$ by Theorem 2.2, and the fixed-successor law
identifies each live child with its unique host. $\square$

**Theorem 4.2 (one support-ambiguous cell cannot produce a saving).**
Suppose at most one cell $e\in V$ has $a_e>1$. Then the sets
$F_p$, $p\in V$, are pairwise disjoint and

$$
m\ge\sum_{p\in V}b_p\ge\sum_{p\in V}a_p\ge G.
\tag{SI.15}
$$

If there is exactly one such cell, write $e=(h_e,z_e)$ and put
$d=h_e+z_e$. There are sets $T_-\subset T_+\subseteq[n]$,
$|T_-|=d-1$, $|T_+|=d+1$, and distinct $x,y$ with
$T_+\setminus T_-=\{x,y\}$, such that

$$
\mathcal S_e=\{T_-\cup\{x\},T_-\cup\{y\}\}.
\tag{SI.16}
$$

Every support at depth $d$ is one of these two sets. A live host
with support $T_-\cup\{x\}$ tests $y$, and one with support
$T_-\cup\{y\}$ tests $x$.

Proof. The case with no exceptional cell is Theorem 4.1. Otherwise
$d\ge1$, since the empty history has only the empty support.
Every depth $t\ne d$ has singleton support families at all its
cells. The diagonal argument in Theorem 4.1 supplies its common
support $T_t$. Where neither of two consecutive depths is exceptional,
(SI.8) gives $T_t\subsetneq T_{t+1}$.

Every actual history at depth $d$ has an actual live predecessor,
so its support $S$ contains $T_-:=T_{d-1}$. If $d<n-1$, it also has
at least one live child, whose support is $T_+:=T_{d+1}$, and hence
$S\subset T_+$. If $d=n-1$, put $T_+=[n]$ instead. In either case

$$
T_-\subset S\subset T_+,\qquad
|T_-|=d-1,\quad |S|=d,\quad |T_+|=d+1.
\tag{SI.17}
$$

Thus there are only the two intermediate sets displayed in (SI.16).
The exceptional family contains both because it is not a singleton.

When $d<n-1$, a live child of a history with support $S$ has support
$T_+$, so its next query must be the unique element of $T_+\setminus S$.
When $d=n-1$, freshness gives the same conclusion with $T_+=[n]$.
The two intermediate supports consequently demand different fixed
query labels. They cannot occur at the same installed state, even
when their count cells differ.

For two cells at depth $d$, equal supports and unequal hits are
excluded at a common state by PCA Theorem 35.1; different supports
are separated by the preceding fixed-label argument. At any other
one depth, supports coincide and unequal hits exclude sharing.
Across different depths, all supports are properly nested: before
depth $d$ they lie in the chain ending at $T_-$, and after that depth
they lie in the chain beginning at $T_+$. PE Lemma 4.1 therefore
excludes every remaining common host. This proves (SI.15). $\square$

## 5. Necessary incidence for a strict subgrid graph

**Definition 5.1 (duplicate live incidence and other installed states).**
Put

$$
\begin{aligned}
Q_{\mathrm{live}}&=\bigcup_{p\in V}F_p,&
u&=|Q\setminus Q_{\mathrm{live}}|,\\
d(q)&=|\{p\in V:q\in F_p\}|\quad(q\in Q_{\mathrm{live}}),&
D&=\sum_{q\in Q_{\mathrm{live}}}(d(q)-1),\\
E&=\sum_{p\in V}(b_p-1).
\end{aligned}
\tag{SI.18}
$$

Here $D$ measures duplicate count-cell incidences of actual live
states. The number $u$ includes unused states and states reached only
after certification. A state live on one input contributes to
$Q_{\mathrm{live}}$ even if another input visits it after certification.

**Theorem 5.2 (requirements for a strict saving).** If $m<G$, then
at least two distinct cells are support-ambiguous. They lie off both
axes and each has at least two live hosts. There is also a state
shared by different count cells, necessarily obeying (SI.7). The exact
incidence identity holds for every graph; under $m<G$ its strict-saving
consequence is

$$
m-G=E-D+u,\qquad D>E+u.
\tag{SI.19}
$$

Every such graph must also satisfy all inequalities (SI.12) and the
actual fixed-label successor law (SI.8).

Proof. Theorem 4.2 rules out zero or one support-ambiguous cell when
$m<G$. The axis assertion and $b_p\ge a_p$ follow from Theorem 2.2.
If the host sets of different cells were disjoint, their nonemptiness
would already force $m\ge G$, so a shared state exists. Its actual
histories satisfy (SI.7).

Double-counting the finite incidence relation between $V$ and
$Q_{\mathrm{live}}$ gives

$$
\sum_{p\in V}b_p
=\sum_{q\in Q_{\mathrm{live}}}d(q)
=|Q_{\mathrm{live}}|+D.
$$

The left side is $G+E$, and $m=|Q_{\mathrm{live}}|+u$. Substitution
proves (SI.19). The other conditions have already been proved for
every qualifying graph. In particular a proposed compensation for
sharing must account for all live incidences: a paid separator that
is live elsewhere does not automatically contribute to $u$, and
one separator cannot be counted several times as distinct installed
states. $\square$

## 6. The exact relaxation retaining only counts

**Definition 6.1 (count incidence with live transition closure).** In
this section let $K,L\ge2$ be arbitrary integers, $n=K+L-1$, and
$V=\{0,\ldots,K-1\}\times\{0,\ldots,L-1\}$. A count incidence
consists of a finite label set $\Lambda$ and nonempty subsets
$\mathcal H_p\subseteq\Lambda$, $p\in V$, whose union is
$\Lambda$. Require $\mathcal H_{(0,0)}=\{\lambda_*\}$ and require
that two different cells whose label sets intersect be comparable
under (SI.9). Multiple labels at one cell are allowed.

For the version with transition closure, give each label two fixed
successors in $\Lambda\cup\{\mathsf0,\mathsf1\}$ and use the
start $\lambda_*$. For $p=(h,z)$ put
$p_\varepsilon=(h+\varepsilon,z+1-\varepsilon)$ and require only

$$
p_\varepsilon\in V,\quad \lambda\in\mathcal H_p
\quad\Longrightarrow\quad
\delta(\lambda,\varepsilon)\in\mathcal H_{p_\varepsilon},
\qquad \varepsilon\in\{0,1\}.
\tag{SI.20}
$$

A transition leaving $V$ imposes no constraint. In particular, if a
label represents both an exiting transition and a live transition for
the same reply, the latter fixes the successor while the former
imposes no terminal requirement. This definition retains count
separation and all live count transitions, but discards actual supports,
old assignments and correctness after a certificate. A functional
count labeling is the special case
$\mathcal H_p=\{\gamma(p)\}$, with $\gamma:V\to\Lambda$
surjective.

Every correct graph of Definition 1.2 gives such a count incidence
with $\Lambda=Q_{\mathrm{live}}$ and $\mathcal H_p=F_p$.
Keep its fixed successor for a reply if any live occurrence of that
state has a live child for that reply. That successor is in
$Q_{\mathrm{live}}$ by Theorem 2.2. If no such live child occurs,
replace the reply's successor by the corresponding terminal. This
replacement affects no obligation in (SI.20); paid post-certificate
paths have deliberately been discarded. Thus no unique-host
assumption is used in passing to this relaxation.

**Theorem 6.2 (sharp size of the count relaxation).** Both without and
with the fixed-successor requirement (SI.20), the minimum number of
labels in the count-incidence relaxation of Definition 6.1 is

$$
2K+2L-4=2n-2.
\tag{SI.21}
$$

The maximum antichain size in (SI.9) has the same value. The minimum
is attained already by the functional labeling

$$
\gamma(h,z)=(h+z,h\bmod2).
\tag{SI.22}
$$

Proof. The set

$$
\mathcal C=\{(h,z)\in V:h\le1\text{ or }z\ge L-2\}
\tag{SI.23}
$$

has size $2L+2(K-2)$. Two cells in its first two rows have hit
gap at most one, and two in its last two columns have zero gap
at most one. For a remaining comparison, the cell with the larger
hit count has zero count at least $L-2$, so the oriented zero
decrease is at most one. Thus $\mathcal C$ is an antichain and
the nonempty label sets at its cells must be disjoint. This gives
the lower bound even for multiple labels at a cell.

In (SI.22), two different cells with the same label have equal
depth and distinct hit counts of the same parity. Their oriented
hit increase and zero decrease are equal positive even integers.
Both gaps are at least two. Thus the singleton label sets of this
labeling are allowed.

Depths $0$ and $n-1$ each contain one cell. Every intermediate
depth contains at least two cells: its admissible hit counts are
the interval

$$
\max(0,d-L+1)\le h\le\min(K-1,d),
$$

which has at least two integers when $1\le d\le n-2$ and
$K,L\ge2$. Consecutive hit counts supply both parities. There
are consequently $1+2(n-2)+1=2n-2$ labels.

For a fixed label $(d,e)$, every existing live zero successor has
label $(d+1,e)$, and every existing live one successor has label
$(d+1,1-e)$. These are independent of the representative cell.
Install that successor whenever at least one representative has
a live successor for the reply; when none does, install the
corresponding terminal $\mathsf0$ or $\mathsf1$. This defines
two fixed successors and proves (SI.20) for these singleton sets.
All running edges increase $d$, so the resulting label graph terminates.

Finally every label class in (SI.22) is a chain under (SI.9).
An antichain meets each such chain at most once, giving the upper
bound on antichain size as well. Alternatively, repeatedly joining
$(h,z)$ to $(h+2,z-2)$ partitions the rectangle into chains whose
initial points are exactly (SI.23). No general chain decomposition
theorem is needed. $\square$

For the threshold parameters in (SI.4), this relaxation has the
strict positive gap

$$
G-(2n-2)=(K-2)(L-2).
\tag{SI.24}
$$

Thus count separation together with (SI.20), by itself, cannot
exclude a $2n-2$-label object. This says exactly what those
requirements permit; it does not bound a method that also uses
actual supports, assignments, weighted charges or terminal correctness.

## 7. A complete graph passing the budgets and giving a false positive

**Definition 7.1 (coordinate realization of the label graph).** For
$K,L\ge2$, put $n=K+L-1$ and use $V,\gamma$ from Section 6. Take
the running states

$$
q_{d,e}\quad\text{for }(d,e)\in\gamma(V)
$$

and terminals $\mathsf0,\mathsf1$. Start at $q_{0,0}$ and query
coordinate $d+1$ at $q_{d,e}$. For reply
$\varepsilon\in\{0,1\}$, if there is a representative
$(h,z)\in V$ with $\gamma(h,z)=(d,e)$ and
$(h+\varepsilon,z+1-\varepsilon)\in V$, set

$$
\delta(q_{d,e},\varepsilon)=q_{d+1,(e+\varepsilon)\bmod2}.
\tag{SI.25}
$$

If no such representative exists, set the successor to terminal
$\mathsf\varepsilon$. The existence test concerns the fixed
finite table definition, not a computation performed during a run.
Theorem 6.2 makes (SI.25) unambiguous.

**Theorem 7.2 (execution bounds do not give threshold correctness).**
The graph of Definition 7.1 has $2n-2$ installed running states.
For any positive costs $c_1,\ldots,c_n$, every input terminates
with at most $n$ queries and $W=\sum_i c_i$ letters. One input
attains both maxima. Nevertheless, for $n=6$, $K=3$, $L=4$, the
graph does not compute threshold three. With the original positions
$s_i=i$ it has the complete table

| Running state | Coordinate | Reply zero | Reply one |
| --- | --- | --- | --- |
| $q_{0,0}$ | $1$ | $q_{1,0}$ | $q_{1,1}$ |
| $q_{1,0}$ | $2$ | $q_{2,0}$ | $q_{2,1}$ |
| $q_{1,1}$ | $2$ | $q_{2,1}$ | $q_{2,0}$ |
| $q_{2,0}$ | $3$ | $q_{3,0}$ | $q_{3,1}$ |
| $q_{2,1}$ | $3$ | $q_{3,1}$ | $q_{3,0}$ |
| $q_{3,0}$ | $4$ | $q_{4,0}$ | $q_{4,1}$ |
| $q_{3,1}$ | $4$ | $q_{4,1}$ | $q_{4,0}$ |
| $q_{4,0}$ | $5$ | $q_{5,0}$ | $\mathsf1$ |
| $q_{4,1}$ | $5$ | $\mathsf0$ | $q_{5,0}$ |
| $q_{5,0}$ | $6$ | $\mathsf0$ | $\mathsf1$ |

On $\theta=000011$ it returns $\mathsf1$ after five queries and
$35$ letters, although $|\theta|=2<3$.

Proof. The state count is Theorem 6.2. Every running edge increases
$d$ by one, and the coordinate at that state is $d+1$. Thus every
actual run queries a prefix of $1,\ldots,n$, without repetition,
and then terminates. Its two charges are at most $n,W$.

Take an input whose first $n-1$ replies contain $K-1$ ones and
$L-1$ zeros. All these proper count prefixes lie in $V$.
Equation (SI.20) follows them to $q_{n-1,(K-1)\bmod2}$, which
queries coordinate $n$ and then terminates. Hence this input pays
exactly $n$ queries and $W$ letters.

For the six-coordinate instance the displayed table is the direct
evaluation of (SI.25). The false-positive run is

$$
q_{0,0}\xrightarrow{0}q_{1,0}
\xrightarrow{0}q_{2,0}\xrightarrow{0}q_{3,0}
\xrightarrow{0}q_{4,0}\xrightarrow{1}\mathsf1.
\tag{SI.26}
$$

The charges are $5$ and $5+6+7+8+9=35$; the last input bit is
not read. After its fourth zero the actual history already has a
negative certificate, but its label $q_{4,0}$ was retained because
the live cell $(2,2)$ has that label. The abstract live transition
constraints therefore do not determine the correct continuation
for this certified history. This is precisely an obligation omitted
by Definition 6.1.

The graph also violates the actual-support exclusions before either
certificate: reply prefixes $00$ and $11$ both reach $q_{2,0}$,
have the same exposed support $\{1,2\}$ and unequal hits $0,2$,
and are both live for threshold three on six coordinates. They meet
the two-gap count rule but violate the equal-support conclusion of
PCA Theorem 35.1. Hence the graph is not a witness satisfying all
the stronger supplied necessary conditions. $\square$

**Theorem 7.3 (the same failure at the original native entry).** For
$A=\{1,2,3,4,5,6\}$ and any $r\ge0$, installing the graph in
Theorem 7.2 at the original selected literals and using the original
two-state profile front gives a terminating native table with
$14+r$ preparation states and uniform bounds of seven calls and
$48$ letters on the full $\mathcal U_*$. It fails the prescribed
entry requirement on an actual source in that fiber. In particular
it is not a smaller feasible native preparer.

Proof. Here $W=45$. Replace each coordinate-$i$ state by literal
$a_i$, use the Boolean-one successor for branch and the Boolean-zero
successor separately for alpha, beta and absent, and replace the two
terminals by $\widehat e_0,\widehat e_1$. Install the profile states
from the constructive direction of [WTF, Theorem 4.1][WTF]:

| Profile state | Literal | alpha | beta | branch | absent |
| --- | --- | --- | --- | --- | --- |
| $D$ | $RLR$ | $\widehat e_1$ | $q_{0,0}$ | $T$ | $\widehat e_0$ |
| $T$ | $RRR$ | $\widehat e_1$ | $\widehat e_0$ | $\widehat e_0$ | $\widehat e_0$ |

Start at $D$ and include the $r$ further mandated latches. The ten
selected states, two profile states and $2+r$ latches give $14+r$.
Every source in $Z_{b_3}$ has a fixed indicator vector, even when its
branch image is not a cube comb and selected addresses are absent.
The occurrence identity makes the selected route exactly a run of
Definition 7.1 on that vector. The preceding theorem therefore
gives termination, at most $1+6=7$ calls and at most $3+45=48$
letters on that same source. Every other profile terminates within
two calls and six letters by the displayed profile front. These
claims use only the execution part of the lift, whose threshold
correctness hypothesis is absent here.

By [WTF, Supplier 2.1][WTF], the vector $000011$ has an actual
finite origin $u_\theta\in Z_{b_3}$ with all original repeated
occurrences, disequalities and guards. Its first profile reply is
beta, followed by (SI.26). It therefore latches
$\widehat e_1$ after six calls and $38$ letters. Equation (SI.2)
requires $\widehat e_0$ on this source. The original complete entries
are distinct, so the pointwise prescribed-code condition fails.
All installed states and calls remain charged; changing the required
code or restricting the source family would change the problem.
$\square$

## 8. The remaining global comparison and the literature hypotheses

**Definition 8.1 (remaining comparison).** The global grid comparison
for Definition 1.2 is the assertion $m\ge G$ for every correct graph
satisfying (SI.3). In the full actual-incidence notation (SI.18), it
is equivalent to

$$
D\le E+u.
\tag{SI.27}
$$

Theorems 4.1–4.2 establish this comparison when at most one count cell
has more than one actual support. Theorem 5.2 states necessary
conditions for any graph violating it. Theorem 6.2 settles exactly
the weaker count-label problem. Theorems 7.2–7.3 supply an execution
feasible graph violating the prescribed output, rather than a
counterexample to (SI.27). The unrestricted comparison with multiple
support-ambiguous cells is not established by these results.

The classical comparison is [Ingo Wegener, *The Complexity of Boolean
Functions*, Chapter 14, Section 4, Definition 4.1 and Theorems
4.1–4.3][Wegener]. Its optimal synchronous
form and residual count are for read-once branching programs. The proof
on printed page 424 explicitly uses realizability of every graph path
in that model and states that it fails for general branching programs.
Likewise [R. E. Bryant, *Graph-Based Algorithms for Boolean Function
Manipulation*, Section 2, Definition 1][Bryant] requires variable
indices to increase strictly along nonterminal edges. Definition 1.2
has neither premise. The common live order in Theorem 4.1 is deduced
under its singleton-support hypothesis; it is not imposed on a general
competitor, and it does not constrain paid post-certificate behavior.

The support-incidence, rigidity and relaxation results above are
ordinary deductions from the stated repository suppliers and their
explicit finite combinatorial arguments. The external results just
cited are literature-attested comparisons, not unrestricted lower-bound
suppliers. The new deductions are repo-derived, with no priority claim
over other literature. The local paired-completion and sharing
constructions of [PE, Sections 7–9][PE] are compatible with this
distinction: none supplies (SI.27) by counting local discriminators as
globally distinct states.

For the native consumer, any proof of the unrestricted Boolean grid
comparison would transfer through (SI.5) to $H\ge G+4+r$, matching
the supplied full-domain grid of [PCA, Theorem 26.1][PCA]. Conversely,
a smaller native upper would require a correct graph, the original
full-fiber lift and both simultaneous execution caps. No acquisition,
authentication, export, handoff, physical-memory or four-view realization
theorem follows from this installed-state comparison.

[WTF]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_WEIGHTED_THRESHOLD_FRONTIER.md
[PE]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_PAID_PRIVATE_EXCHANGE.md
[PCA]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_PRESCRIBED_CODE_ACQUISITION.md
[Wegener]: https://eccc.weizmann.ac.il/resources/pdf/cobf.pdf
[Bryant]: https://www.cs.cmu.edu/~bryant/pubdir/ieeetc86.pdf

## 追加锚（本行以下为增补区）

## 9. Common-support cuts and compensation in short intervals

**Definition 9.1 (cuts and interval incidence on one complete graph).**
Fix one graph of Definition 1.2, with correctness, actual termination
and both caps (SI.3). All notation and original costs remain those of
(SI.1), (SI.4), (SI.6) and (SI.18). For $0\le d<n$, put
$V_d=\{(h,z)\in V:h+z=d\}$. Call $d$ a common-support depth if
every actual live history at that depth has the same support $T_d$.
By the diagonal argument in Theorem 4.1, this is equivalent to
$a_p=1$ for every $p\in V_d$: that argument requires no singleton
hypothesis on other diagonals. Depth zero is common, with
$T_0=\varnothing$.

Adjoin the mathematical endpoint $n$, with $T_n=[n]$, and list all
common-support depths together with that endpoint as

$$
0=d_0<d_1<\cdots<d_s=n.
\tag{SI.28}
$$

Write $\mathcal C=\{d_0,\ldots,d_{s-1}\}$ and let $\mathcal B$
be the set of open intervals $B=(d_j,d_{j+1})$. The length of
$B=(a,b)$ means $\beta_B=b-a$, including its boundary spacing.
There is no live cell at the formal endpoint $n$. Define

$$
\begin{aligned}
V_B&=\{p\in V:a<h(p)+z(p)<b\},&
Q_B&=\bigcup_{p\in V_B}F_p,\\
E_B&=\sum_{p\in V_B}(b_p-1),&
D_B&=\sum_{q\in Q_B}
       \bigl(|\{p\in V_B:q\in F_p\}|-1\bigr),\\
Q_a^{\mathrm{cut}}&=\bigcup_{p\in V_a}F_p,&
E_a&=\sum_{p\in V_a}(b_p-1),\qquad
E_{\mathrm{cut}}=\sum_{a\in\mathcal C}E_a.
\end{aligned}
\tag{SI.29}
$$

An empty interval contributes empty sets and zero sums. For the same
installed coordinate multiplicity vector, put

$$
\begin{aligned}
m_i&=|\{q\in Q:i(q)=i\}|,&
m(X)&=\sum_{i\in X}m_i,\\
X_B&=T_b\setminus T_a,&
u_B&=|\{q\in Q\setminus Q_{\mathrm{live}}:i(q)\in X_B\}|,\\
g_B&=|V_a|+|V_B|.&&
\end{aligned}
\tag{SI.30}
$$

Cuts, depths, supports and coordinate blocks are indices used to
describe actual histories. They supply no running clock, block entry,
reset, selector or additional state to $P$.

**Lemma 9.2 (actual extension and support envelopes).** Every actual
live history at depth $d$ extends through actual live histories to
every specified depth $e$ with $d\le e\le n-1$. The supports at
the depths in (SI.28) form a strictly increasing chain, with
$|T_a|=a$. For $B=(a,b)\in\mathcal B$ and any actual live
occurrence $(p,S,q)\in\mathcal R$ at depth $a\le d<b$,

$$
T_a\subseteq S\subsetneq T_b,\qquad
i(q)\in T_b\setminus S\subseteq X_B.
\tag{SI.31}
$$

At a common-support depth, different cells have disjoint host sets.
No state hosted at that depth is live at another depth.

Proof. If $h+z<n-1$ and $(h,z)\in V$, it is not the corner
$(K-1,L-1)$. At least one of the replies zero and one therefore has
its child count still in $V$. The next query is fresh by Theorem 2.2,
and (SI.8) makes that child an actual live history with the installed
successor. Iterating to the specified depth proves extension. At each
step the chosen reply fixes an unread coordinate, so a completion of
the resulting exposed assignment follows the entire finite prefix.
No inconsistent syntactic path is used.

Extending a history between two common depths gives containment of
their supports; Theorem 2.2 gives their cardinalities and hence strict
containment. The same statement at the endpoint $n$ follows from
$T_n=[n]$. An occurrence at depth $d\ge a$ has an actual live
ancestor at depth $a$, so its support contains $T_a$. If $b<n$,
extend the occurrence to depth $b$. Since $d<b\le n-1$, this
extension includes its next query and gives both $S\subsetneq T_b$
and $i(q)\in T_b\setminus S$. If $b=n$, these assertions follow
from $|S|<n$ and freshness. This proves (SI.31).

At a common depth all supports coincide, and different cells have
unequal hits. Their hosts are disjoint by the equal-support exclusion
supplied in Section 2. Any live support at an earlier depth is a
proper subset of the common support, by extension; any live support
at a later depth properly contains it, by ancestry. The supplied
nested-support exclusion therefore forbids the last asserted sharing.
$\square$

**Theorem 9.3 (exact localization on the original installed vector).**
For every graph in Definition 9.1, the sets $X_B$, $B\in\mathcal B$,
partition $[n]$, and all live sharing between different count cells is
confined to one $V_B$. More precisely, all the pools $Q_B$ and
$Q_a^{\mathrm{cut}}$ are pairwise disjoint, and a state in
$Q_a^{\mathrm{cut}}$ hosts exactly one count cell. Consequently

$$
\begin{gathered}
D=\sum_{B\in\mathcal B}D_B,\qquad
E=E_{\mathrm{cut}}+\sum_{B\in\mathcal B}E_B,\qquad
u=\sum_{B\in\mathcal B}u_B,\\
m(X_B)-g_B=E_a+E_B-D_B+u_B\qquad(B=(a,b)),\\
m-G=E_{\mathrm{cut}}+u+
             \sum_{B\in\mathcal B}(E_B-D_B).
\end{gathered}
\tag{SI.32}
$$

Proof. The chain in Lemma 9.2 starts at the empty set and ends at
$[n]$, so its successive differences $X_B$ partition $[n]$.
Equation (SI.31) places the fixed label of every live host at depths
$a\le d<b$ in $X_B$. Since these coordinate blocks are disjoint,
one installed state cannot be live in two such half-open depth ranges.
Within one range, Lemma 9.2 separates its lower cut pool from the
interior and separates the cells of that cut. This proves every stated
disjointness and localizes all duplicate incidences.

Every live state belongs to one of these pools. In the coordinate block
$X_B$ the installed states are precisely the disjoint union of
$Q_a^{\mathrm{cut}}$, $Q_B$ and the states counted by $u_B$.
The cut pool has cardinality $|V_a|+E_a$. Double-counting the
incidences restricted to $V_B$ gives

$$
\sum_{p\in V_B}b_p=|Q_B|+D_B,\qquad
|Q_B|=|V_B|+E_B-D_B.
\tag{SI.33}
$$

Their sum proves the block identity in (SI.32). The half-open cell
ranges partition $V$, so $\sum_B g_B=G$. The coordinate blocks
partition all installed states by their fixed labels, including those
that are never live. Thus $\sum_B m(X_B)=m$ and
$\sum_B u_B=u$. Summation proves the remaining identities, also
recovering (SI.19).

A state live in one pool but visited after certification on another
input stays in that one live pool. It is not included in any $u_B$.
Actual certified traffic need not obey the live support envelope; none
of its visits is deleted or made free by the decomposition. $\square$

**Theorem 9.4 (compensation for every gap of at most three).** For
every $B=(a,b)\in\mathcal B$ with $b-a\le3$,

$$
D_B\le E_B,\qquad |Q_B|\ge|V_B|.
\tag{SI.34}
$$

The other intervals may have arbitrary lengths. For lengths one and
two, $D_B=0$. For length three, every shared live host in the interval
belongs to exactly two cells at depth $a+1$. They must be the unique
possible pair on that diagonal consisting of a cell with $z=L-1$
and a cell with $h=K-1$. This is a necessary classification of
sharing, not an assertion that the pair or a sharing state exists.

Proof. Length one has no internal cells. At length two put
$X_B=\{x,y\}$. Every internal support is either
$T_a\cup\{x\}$ or $T_a\cup\{y\}$. By (SI.31), its next
fixed label must be the other member of $X_B$. Distinct supports
therefore cannot share a state; equal supports at distinct cells cannot
share by the equal-support/unequal-hit exclusion. Thus $D_B=0$.

Now let $b-a=3$, so $|X_B|=3$. At the last internal depth
$a+2$, each support consists of $T_a$ and two members of $X_B$.
Its next fixed label is the unique omitted member. Different supports
require different labels, while equal supports in different cells have
unequal hits. Hence no state at that depth hosts different cells.

There is also no sharing between depths $a+1$ and $a+2$.
Their supports have the form $T_a\cup\{x\}$ and
$T_a\cup\{y,z\}$ with $y\ne z$. If $x\in\{y,z\}$,
they are properly nested, which excludes sharing. Otherwise their
union is $T_b$. A shared host would have to query a label in
$T_b$ fresh for both supports, by (SI.31), which is impossible.

All duplicate incidences are therefore at depth $d=a+1$. For a
host $q$ there, let $\mathcal H(q)\subseteq V_d$ be its set of
hosted cells, and for each $p\in\mathcal H(q)$ let

$$
L(p)=\{\varepsilon\in\{0,1\}:p_\varepsilon\in V\}.
$$

Here $d\le n-2$, so every $L(p)$ is nonempty. If the same
reply $\varepsilon$ belonged to $L(p)$ and $L(p')$ for distinct
hosted cells, (SI.8) would put both distinct child cells at the one
fixed successor $\delta(q,\varepsilon)$. Those children are at
depth $a+2$, where such sharing has just been excluded. Thus the
nonempty sets $L(p)$ are pairwise disjoint subsets of $\{0,1\}$.
A shared host has exactly two cells, with opposite singleton live-reply
sets. Since zero remains live exactly when $z<L-1$, and one remains
live exactly when $h<K-1$, the cells must be

$$
p_-=(d-(L-1),L-1),\qquad
p_+=(K-1,d-(K-1)).
\tag{SI.35}
$$

If either displayed cell is outside $V_d$, sharing is impossible.
The exclusions (SI.7) still apply whenever the pair is hosted together.

Let $s_B$ be the number of shared states in this interval. Each has
exactly two cell incidences, and all other hosts have one, so
$D_B=s_B$. If $s_B\ge2$, both cells in (SI.35) have at least
$s_B$ hosts. Therefore the excess on their diagonal is at least
$2s_B-2\ge s_B$. If $s_B=1$, use that $a,b$ are consecutive
in the complete cut list: depth $a+1$ is not common-support. By
Definition 9.1 some cell on this diagonal has $a_p>1$, and
Theorem 2.2 gives $b_p\ge a_p\ge2$. The excess on this diagonal
is at least one. If $s_B=0$ there is nothing to compensate. In all
cases,

$$
D_B=s_B\le\sum_{p\in V_{a+1}}(b_p-1)\le E_B.
\tag{SI.36}
$$

Equation (SI.33) gives the host lower bound. The fixed-successor
argument uses two actual live children with the same reply whenever
both are live. It imposes no restriction on a certified child or its
subsequent paid continuation. $\square$

**Corollary 9.5 (the qualified Boolean and full-fiber native minima).**
Within the class of Definition 1.2 graphs for which every consecutive
common-support gap has length at most three,

$$
D\le E,\qquad |Q_{\mathrm{live}}|\ge G,\qquad m\ge G+u.
\tag{SI.37}
$$

The minimum Boolean running-state count in this class, at both caps
$n,W$, is exactly $G$. For complete original native preparers at
both caps $n+1,W+3$ whose supplied Boolean projection in (SI.5)
has this gap property, the minimum installed preparation count is
exactly $G+4+r$.

Proof. Sum (SI.34) over the intervals. Equation (SI.32), with
$E_{\mathrm{cut}}\ge0$, gives $D\le E$ and $m\ge G+u$;
subtracting $u$ gives the live-state assertion. The existing grid of
[PCA, Theorem 26.1][PCA] has $G$ Boolean running states and a fixed
live coordinate order. Every depth is common-support, so every gap
has length one. It supplies equality and needs no new construction.

For a native competitor with the stated projection property, the
projection in [WTF, Theorem 4.1][WTF] is a complete correct Boolean
graph satisfying both caps, with at most $H_P-4-r$ running states.
Applying (SI.37) proves $H_P\ge G+4+r$. The same supplied grid
and full-fiber lift attain this count and both native execution bounds.
The class condition concerns that projection's actual selected-history
supports; it is not asserted for every native competitor.

The native quantifier remains over the entire original
$\mathcal U_*$ of Definition 1.1, with all finite tree sizes,
depths and shapes. The lower-witness cube supplies the projection;
the reused upper is correct on the full fiber. The original pointwise
code, literal latches and complete $e_0,e_1$ entries, all four native
replies and all original addresses remain fixed. The unchanged reader
returns the whole predecessor row, including its exterior, occurrences,
equality partition, repetitions, disequalities and strict-prefix guards.
Its eight states remain separately priced. All installed unused states
and all actual invocations, including constants, repeats and visits
after certification, retain their original charges. The separate
services in Convention 1.3 remain assumptions; no acquisition or
physical implementation follows. $\square$

**Proposition 9.6 (the exact residual global obligation and a necessary
long interval).** Partition $\mathcal B$ as
$\mathcal B_{\le3}=\{B:\beta_B\le3\}$ and
$\mathcal B_{\ge4}=\{B:\beta_B\ge4\}$. For this one complete
graph, $m\ge G$ is equivalent to

$$
\sum_{B\in\mathcal B_{\ge4}}(D_B-E_B)
\le E_{\mathrm{cut}}+u+
       \sum_{B\in\mathcal B_{\le3}}(E_B-D_B).
\tag{SI.38}
$$

Every correct strict-subgrid graph at both original caps therefore
has an interval $B=(a,b)$ with

$$
b-a\ge4,\qquad D_B>E_B,\qquad |Q_B|<|V_B|.
\tag{SI.39}
$$

Every internal depth of this interval contains a support-ambiguous
cell. In particular there are at least three consecutive such depths.
The same necessary condition holds for the supplied projection of
any complete original native preparer with $H_P<G+4+r$ and
both native caps $n+1,W+3$.

Proof. Rearrange (SI.32) to obtain

$$
m-G=E_{\mathrm{cut}}+u+
 \sum_{B\in\mathcal B_{\le3}}(E_B-D_B)
 -\sum_{B\in\mathcal B_{\ge4}}(D_B-E_B).
\tag{SI.40}
$$

This proves the equivalence with (SI.38). Each term on the right
of (SI.38) is nonnegative by Theorem 9.4. If $m<G$, the inequality
in (SI.38) is reversed strictly, so at least one long interval has
$D_B-E_B>0$. Equation (SI.33) gives its host deficit. Consecutivity
of the cuts means none of the internal depths is common-support;
the equivalence in Definition 9.1 then supplies an ambiguous cell
at each. The native projection has $m\le H_P-4-r<G$ and both
Boolean caps by (SI.5), so the same argument applies. $\square$

The remaining global obligation is (SI.38) for every original complete
graph; it is not proved here when long intervals occur. A separate
inequality $D_B\le E_B$ for each long interval
would suffice, but is stronger than the required global sum: excess
at cuts or other intervals and the genuine nonlive states can also
compensate a local deficit. In a four-coordinate block the support
patterns $T_a\cup\{x\}$ and $T_a\cup\{y,z\}$, with
$x,y,z,w$ distinct, are incomparable and leave $w$ fresh for both.
Thus the nested-support-or-full-union exclusion used for the two
internal depths of a three-coordinate block no longer applies. These
sets only identify the failure of that exclusion; they do not provide
actual count-compatible histories, fixed successors or a correct table.
Actual assignments, certified exits and both whole-run caps remain
obligations for any proposed long-interval compensation or construction.

The actual-prefix inequalities of [CP, Theorem 5.1][CP] continue to
hold simultaneously on the same vector $(m_i)$ used in (SI.30).
An interval here is not supplied with an independent total-threshold
entry: different actual entry assignments and count cells may reach
its states, and certified traffic may visit states live elsewhere.
Neither independent residual lower bounds nor subtraction of lower
bounds on overlapping coordinate sets establishes (SI.38). No
cost-preserving normalization into the short-gap class is supplied.
For $\min(k,n-k+1)\ge4$, neither the unrestricted compensation nor
a complete correct strict-subgrid graph is established here. The
unrestricted-budget $H_{\min}$ is a separate question.

The new deductions are repo-derived ordinary mathematics: the support
envelopes and localization concern all actual histories of one complete
table, and Theorem 9.4 compensates every short interval without selecting
representative histories or separator packs. Theorem 2.2, the local
diagonal argument of Theorem 4.1, the identity of Theorem 5.2 and
the exclusions cited in Section 2 are reused suppliers. The native
feasibility equivalence and full-domain grid are reused without
reproving their source or entry contracts. The fixed-representative
obstructions of [WTF, Theorem 11.7][WTF] remain compatible with these
incidence sums; no capacity bound for those separators is a premise.

The literature comparisons retain the hypotheses stated in Section 8.
Wegener's Chapter 14, Section 4, printed page 424 uses realizability
of every graph path for BP1, and Bryant's Section 2, Definition 1
requires strictly increasing variable indices. In addition,
[Cook, Edmonds, Medabalimi and Pitassi, *Lower Bounds for
Nondeterministic Semantic Read-Once Branching Programs*, Section
2.1][CEMP] defines an acyclic nondeterministic graph and constrains
every consistent accepting path to be read-once. Live freshness in
Definition 1.2 does not impose that condition on paid post-certificate
traffic. These are comparisons with distinct model hypotheses; no
external unrestricted threshold lower bound is used in (SI.34) or
(SI.38), and no worldwide priority assertion is made.

[CP]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_COMMON_PREFIX_MEMORY_FRONTIER.md
[CEMP]: https://doi.org/10.4230/LIPIcs.ICALP.2016.36

## 追加锚（本行以下为增补区）
