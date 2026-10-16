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

## 10. Four-coordinate compensation, right-cut separation and inherited residual cuts

**Convention 10.1 (one original table and ordinary-paper scope).**
Throughout this section fix one complete graph of Definitions 1.2 and
9.1, correct and terminating on every Boolean input and satisfying
both caps $t\le n$, $J\le W$. Retain $n\ge6$,
$K=k$, $L=n-k+1$, $3\le k\le n-2$, the distinct original costs
$c_i=s_i+4$, and every incidence quantity of Sections 2, 5 and 9.
In particular $\mathcal B$ uses the complete list of common-support
cuts and the formal endpoint $n$. The results below are ordinary-paper
deductions from the cited suppliers; no Lean verification is asserted.

For a live cell $p=(h,z)$ set
$\mathcal L(p)=\{\varepsilon:p_\varepsilon\in V\}$.
Except at the final corner this set is nonempty. Its singleton
possibilities are $\{1\}$ at $z=L-1$, $h<K-1$, and $\{0\}$
at $h=K-1$, $z<L-1$. Supports, depths and the incidence diagrams
below are mathematical indices, with no added running configuration.

**Lemma 10.2 (last-layer exclusivity and universal right-cut
separation).** Let $B=(a,b)\in\mathcal B$. Every host at depth
$b-1$ hosts no other count cell in $V_B$. If distinct
$p=(h,z),p'=(g,w)\in V_B$ share a host, orient them by $h<g$.
Then

$$
g-h\ge\max(2,n-b+1),\qquad
z-w\ge\max(2,n-b+1).
\tag{SI.41}
$$

Put $d_*=\min(K,L)$ and $e_*=\max(K,L)$. Every interval ending
at $b\le e_*$ has $D_B=0$, regardless of its length.

Proof. At a live occurrence $(p,S,q)$ of depth $b-1$, (SI.31)
and freshness imply

$$
S=T_b\setminus\{i(q)\}.
\tag{SI.42}
$$

Any other live occurrence of this state inside $B$ has a support
$S'$ contained in $T_b\setminus\{i(q)\}$. At an earlier depth
this containment is proper, contradicting the nested-support
exclusion of Section 2. At the same depth the supports coincide;
a different cell has unequal hits, contradicting the equal-support
exclusion. This proves exclusivity. It also applies when $b=n$:
then $T_b=[n]$, with no need for a live history at depth $n$.

The supplied separation (SI.7) gives $g-h,z-w\ge2$. Suppose,
toward the stronger assertion, that
$\min(g-h,z-w)\le n-b$. Set

$$
M=\max(h+z,g+w),\quad t=b-1-M,\quad
A_1=K-1-g,\quad A_0=L-1-z.
$$

Here $t,A_1,A_0$ are nonnegative. Since $n=K+L-1$,

$$
\begin{aligned}
g+z-M&=\min(g-h,z-w),\\
A_1+A_0-t&=n-b-(g+z-M)\ge0.
\end{aligned}
\tag{SI.43}
$$

Choose nonnegative integers $t_1\le A_1$ and $t_0\le A_0$
with $t_1+t_0=t$; for example take
$t_1=\min(t,A_1)$ and $t_0=t-t_1$. Append the same reply word
$1^{t_1}0^{t_0}$ to the two histories. All its partial count pairs
are live for both histories, since the final counts satisfy their
live bounds and counts only increase. This word is actual for each
history separately. Indeed, at every step the two occurrences have
the same installed state, its label is fresh for both by Theorem
2.2, and either requested reply has a completion following that
history. Their fixed successors are identical. Induction therefore
produces two actual live extensions at the same state after every
step. Agreement of their previously exposed assignments is unnecessary.

At the end the larger depth is $b-1$. The count differences are
unchanged and nonzero, so this gives a host at depth $b-1$ shared
with another cell in $V_B$, contradicting exclusivity. The case
$t=0$ is the same immediate contradiction without an extension.
Thus both integer differences exceed $n-b$, proving (SI.41).
This argument realizes just the constructed paired live extensions;
it makes no assertion about arbitrary syntactic paths.

If $b\le e_*$, then
$n-b+1\ge n-e_*+1=d_*$. One of the hit and zero ranges has
diameter $d_*-1$. The two differences in (SI.41) cannot both
exist in those ranges. Hence no two cells in $V_B$ share a state
and $D_B=0$. $\square$

**Lemma 10.3 (all sharing pairs in a four-coordinate interval).**
Suppose $B=(a,a+4)$, and put $d=a+1$,

$$
\begin{aligned}
\alpha&=d-L+1,&\beta&=K-1,\\
A&=(\alpha,L-1),&
C&=(\alpha+1,L-2),\\
Y&=(K-2,d-K+2),&
Z&=(K-1,d-K+1),\\
U&=(\alpha+1,L-1),&
V'&=(K-1,d-K+2).
\end{aligned}
\tag{SI.44}
$$

The first four displayed cells have depth $d$; $U,V'$ have
depth $d+1$. Every state shared by distinct cells of $V_B$ hosts
exactly two cells. Its pair is one of

$$
AZ,\quad CZ,\quad AY,\quad UV',\quad AV',\quad ZU.
\tag{SI.45}
$$

A displayed pair denotes two distinct valid cells; omit invalid cells,
coincident endpoints and pairs failing (SI.7). A state at depth
$d+2$ shares with no other cell of $V_B$. Moreover every $CZ$
host has its actual zero successor at a shared $UV'$ host, and
every $AY$ host has its actual one successor at a shared $UV'$
host. These successor assertions do not assert injectivity.

Proof. The last-depth assertion is Lemma 10.2, since $d+2=b-1$.
If two distinct cells at depth $d+1$ share a state and have a
common live reply, Theorem 2.2 puts their distinct child cells at
its one fixed successor at depth $d+2$, which is forbidden.
Their nonempty live-reply sets must therefore be opposite
singletons. The only possible pair is $UV'$.

For a state shared between depths $d$ and $d+1$, a common live
reply would similarly share its successor between depths $d+1$
and $d+2$, again forbidden. Thus the two live-reply sets are
opposite singletons. The unique possibilities are $AV'$ and $ZU$.

Consider two hosted cells at depth $d$. If they have no common live
reply, the pair is $AZ$. If zero is common, their two child cells
at depth $d+1$ must be $U,V'$ by the preceding same-depth
classification. Subtracting the zero increment $(0,1)$ from these
cells gives precisely $C,Z$. If one is common, subtracting $(1,0)$
instead gives $A,Y$. This proves (SI.45), and the same actual
fixed-successor argument proves its two successor assertions. In
particular, a common reply cannot be treated as a new independently
chosen child host.

It remains to exclude a state with three or more hosted cells.
Write $H=\beta-\alpha=n-1-d$, so $H\ge2$. If $H=2$, (SI.7)
deletes every pair in (SI.45) except $AZ$: the pairs $CZ,AY,UV'$
have hit and zero gaps only one, and the two cross-depth pairs have
one gap only one. Thus no triple is possible, including when $C=Y$.
If $H\ge3$, all six formal cells in (SI.44) are distinct.
Among depth-$d$ cells the allowed pairs form the path
$C-Z-A-Y$, which has no triple of pairwise adjacent cells.
Deleting invalid cells or forbidden pairs cannot introduce such a
triple. Any shared state hosts at most the two cells $U,V'$
on depth $d+1$.

A mixed triple with two cells at depth $d+1$ would contain $U,V'$.
A depth-$d$ cell sharing with each would need a live-reply set
disjoint from both opposite singletons, which is impossible.
A mixed triple with two cells at depth $d$ and one at depth $d+1$
would require both earlier cells to have the same singleton live-reply
set opposite to the later cell's set. At a given depth there is at
most one cell with either specified singleton live-reply set.
The earlier cells would coincide, a contradiction. The last layer
cannot participate in any triple by exclusivity. All possibilities
are excluded. $\square$

**Theorem 10.4 (compensation for every span-four gap).** For every
consecutive common-support interval $B=(a,a+4)$, without any
restriction on the other gaps,

$$
D_B\le E_B,\qquad |Q_B|\ge |V_B|.
\tag{SI.46}
$$

Proof. Put $d=a+1$ and let

$$
e_j=\sum_{p\in V_{d+j-1}}(b_p-1)\qquad(1\le j\le3).
$$

Each of these depths is internal to a consecutive gap, so it is not
common-support. Definition 9.1 and $b_p\ge a_p$ give $e_j\ge1$.
In particular $E_B=e_1+e_2+e_3\ge3$.

By Lemma 10.3, every multiply hosted state has exactly two cell
incidences. Let $s$ be the number of these states, so $D_B=s$.
Regard each as an edge between its two cells in (SI.45), retaining
parallel edges when distinct installed states have the same pair.
Let $v$ be the number of cells incident to these edges. Then $v\le6$,
and at each incident cell its number of hosts is at least its degree.
The last internal layer has none of these incident cells and has
excess at least one. All other cells have nonnegative excess.
Consequently

$$
E_B\ge2s-v+1\ge2s-5.
\tag{SI.47}
$$

These inequalities include empty sharing: no assumption of positive
degree is imposed on a cell absent from the edge relation.

Suppose $E_B<s$. The bounds $E_B\ge3$ and $E_B\ge2s-5$
force $s=4$ and $E_B=3$. Equation (SI.47) then forces $v=6$.
Thus all six cells in (SI.44) are distinct and valid. Furthermore
$e_1=e_2=e_3=1$. The excess at the six incident cells is at least
$2s-v=2$, while the last layer already contributes one. Equality
forces every incident cell to have exactly its degree many hosts,
and every other cell on the first two layers to have exactly one
host. This also handles every boundary deletion: if even one of the
six formal vertices is missing or identified with another, the
assumed strict deficit has already become impossible.

Let $x,y,z_*,u_*,v_*,w_*$ be the edge multiplicities of
$CZ,AY,UV',AZ,AV',ZU$, respectively. Since all six vertices
are incident and $C,Y$ have only their displayed pendant edges,
$x,y\ge1$. The successor assertion of Lemma 10.3 forces
$z_*\ge1$. Counting degrees separately on the first two layers,
using the just established equality between degree and host count,
gives

$$
\begin{aligned}
x+y+z_*+u_*+v_*+w_*&=4,\\
2x+2y+2u_*+v_*+w_*-4&=e_1=1,\\
2z_*+v_*+w_*-2&=e_2=1.
\end{aligned}
\tag{SI.48}
$$

The last equation and $z_*\ge1$ imply $z_*=1$ and
$v_*+w_*=1$: the alternative $z_*\ge2$ is impossible, and
$z_*=1$ fixes that sum. The middle equation now gives
$x+y+u_*=2$, whence $x=y=1$ and $u_*=0$.

If $v_*=1$, only $A$ among the depth-$d$ cells has more
than one host. All cells from $C$ through $Z$ on that diagonal
therefore have singleton support families. Consecutive such cells
have equal supports: they are the two live children of a common
parent, and Theorem 2.2 gives those children equal supports. This
is the local diagonal argument of Theorem 4.1; no singleton
condition on their parents is needed. The admissible hit counts
form an integer interval, so the supports at $C$ and $Z$
coincide. But $x=1$ gives a state shared by these unequal-hit
cells, contradicting the equal-support exclusion.

If $w_*=1$, only $Z$ has more than one host on that first
diagonal. The same argument from $A$ through $Y$ makes their
supports equal, contradicting the shared $AY$ state given by
$y=1$. These are the only possibilities since $v_*+w_*=1$.
The assumed deficit is impossible, proving $D_B\le E_B$.
Equation (SI.33) gives the equivalent host lower bound.

Every edge and successor used here is witnessed by actual live
histories of the original graph. No certified successor is prescribed,
and no post-certificate invocation is deleted or counted as a fresh
allocation. $\square$

**Corollary 10.5 (strict positive margin for a terminal span-four
gap).** If $B=(n-4,n)$ is consecutive, then

$$
E_B-D_B\ge2,\qquad |Q_B|\ge |V_B|+2.
\tag{SI.49}
$$

The only possible shared pair in this interval is

$$
(K-3,L-1),\qquad(K-1,L-3).
\tag{SI.50}
$$

No attainment of the margin two is asserted.

Proof. Here $d=n-3$ and $H=2$ in Lemma 10.3, so only its
$AZ$ pair survives (SI.7); it is exactly (SI.50).
These cells are valid because $K,L\ge3$. Let $s$ be their
number of shared states, and let $e_j$ denote the three diagonal
excesses defined in the proof of Theorem 10.4. Then $D_B=s$.
If $s>0$, both cells have at least $s$ hosts, giving $e_1\ge2s-2$.
For $s=0$ the same inequality is automatic. Consecutivity still
gives $e_j\ge1$ for all three internal layers. Hence

$$
E_B-D_B\ge2+\max(1,2s-2)-s\ge2.
\tag{SI.51}
$$

For $s=0$ the first bound is three; for $s=1$ it is two;
for $s\ge2$ it is $s\ge2$. Equation (SI.33) completes
the proof. $\square$

**Corollary 10.6 (enlarged qualified exact whole-table minima).**
Consider the class of complete original Boolean graphs for which

$$
B=(a,b)\in\mathcal B,\quad b>e_*
\quad\Longrightarrow\quad b-a\le4.
\tag{SI.52}
$$

Intervals ending at $b\le e_*$ may have arbitrary lengths.
Every graph in this class satisfies

$$
D\le E,\qquad |Q_{\mathrm{live}}|\ge G,\qquad m\ge G+u.
\tag{SI.53}
$$

The minimum Boolean running-state count in this class, at both
uniform caps $n,W$, is exactly $G=K L$. The subclass with all
gaps of span at most four has the same exact minimum. For complete
original native preparers whose supplied Boolean projection in
(SI.5) belongs to either stated class, at both native caps
$n+1,W+3$, the exact preparation minimum is $G+4+r$.

If a graph in the enlarged class actually has a consecutive terminal
gap $(n-4,n)$, its stronger lower bound is $m\ge G+u+2$.
The corresponding native preparation count is at least $G+6+r$.
These stronger conditional bounds carry no attainment assertion.

Proof. Every interval ending early has $D_B=0$ by Lemma 10.2.
The other intervals have span at most four and satisfy $D_B\le E_B$
by Theorems 9.4 and 10.4. Sum in (SI.32) to obtain (SI.53).
If the terminal span-four gap is present, Corollary 10.5 contributes
at least two to that sum and gives the stronger bound.

The supplied grid of [PCA, Theorem 26.1][PCA] has $G$ Boolean
running states and every depth common-support. It belongs to both
classes and satisfies both caps on all inputs in the same graph,
giving equality for the class minima. For a native competitor the
projection of [WTF, Theorem 4.1][WTF] has
$m\le H_P-4-r$ and both Boolean caps, so the respective Boolean
lower bounds give the native lower bounds. The supplied full-fiber
grid lift gives $G+4+r$ preparation states and both uniform native
caps in one table, proving the exact class minima.

This native upper is over every source in the unbounded original
$\mathcal U_*$, with its original $\rho$, prescribed pointwise
code, literal latches and complete $e_0,e_1$ entries. Its four
successors at every installed address remain those of the supplied
construction. The unchanged, independently priced eight-state reader
returns the entire predecessor row, including ordered exterior,
occurrences, equality partition, repetitions, disequalities and
strict-prefix guards. The cube is a lower-witness projection only.
Every installed running, output, unused and latch state retains its
price, as does every actual constant, repeated or post-certificate
invocation. Acquired binding, authentication, permission, same-source
export, isolation, handoff and continuity remain the separate
operational services of Convention 1.3. $\square$

**Proposition 10.7 (a genuine span-four support gap).** If
$\min(K,L)\ge4$, there exists a complete correct graph at both
caps whose common-support cuts include the consecutive pair $1,5$.
Thus allowing span four strictly enlarges the support-gap class of
Corollary 9.5.

Proof. Take a fully unfolded finite decision tree, querying coordinate
$1$ first. In the zero child use the order $2,3,4,5$; in the one
child use $3,4,5,2$. After those four queries, use the remaining
coordinates in the same fixed order in both subtrees. Read all $n$
coordinates on every path and attach the threshold output at each
leaf. Each tree node has its fixed query and fixed successors, and
every node is an installed counted state. There is no free branch
selector. Every actual input pays exactly $n$ queries and $W$
letters, including the full suffix after any earlier certificate,
and receives the correct output.

At depths $2,3,4$, the respective supports after first reply zero
and one are

$$
\begin{array}{c|cc}
\text{depth}&\text{first reply zero}&\text{first reply one}\\
2&\{1,2\}&\{1,3\}\\
3&\{1,2,3\}&\{1,3,4\}\\
4&\{1,2,3,4\}&\{1,3,4,5\}.
\end{array}
\tag{SI.54}
$$

Each displayed support has an actual live history: choose the replies
to have one one and one zero at depth two, two ones and one zero
at depth three, and two of each at depth four, with either specified
first reply. All proper prefixes of these live histories are live.
The count bounds hold since $K,L\ge4$. Thus none of these three
depths is common-support. At depth one the support is $\{1\}$,
and at depth five every live history has support
$\{1,2,3,4,5\}$. Such depth-five live histories exist with two
ones and three zeros. Therefore $1,5$ are consecutive cuts.
The supplied full-fiber lift also realizes this example with the
unchanged native task and its original charges. $\square$

**Theorem 10.8 (actual-prefix inheritance and conditional sharp
residual-grid constraints).** Fix an actual live prefix of the
original Boolean graph, with exposed set $S$, assignment $\eta_S$
and $h$ ones. Put

$$
t=|S|,\qquad R=[n]\setminus S,\qquad
N=|R|,\qquad q=k-h.
\tag{SI.55}
$$

Use the residual graph on $R$ supplied by [CP, Theorem 5.1][CP].
For every original common-support depth $b$ with $t<b<n$,
the residual depth $b-t$ is common-support, with support $T_b\setminus S$.
The formal endpoint $n$ becomes its formal endpoint $N$.

Form the increasing list consisting of $t$, all original common-support
depths strictly greater than $t$, and $n$. If all successive distances
in this list are at most four, and $N\ge6$, $3\le q\le N-2$,
then, on the original installed coordinate vector,

$$
m(R)\ge q(N-q+1).
\tag{SI.56}
$$

The bound is the exact grid minimum for the qualified residual class;
it asserts no simultaneous attainment of all prefix constraints in
one original graph. All inequalities (SI.56) for qualifying prefixes
hold simultaneously on that graph's single vector $(m_i)$.
There is no restriction on gaps lying before this prefix.

For one complete native preparer at both original native caps, take
its supplied Boolean projection and an actual live cube prefix.
Under the same inherited-cut and residual-parameter conditions,

$$
M(R)\ge q(N-q+1),
\tag{SI.57}
$$

where $M_i$ counts all its installed selected states in the original
classes $E_i$ of CP Definition 1.2. These inequalities likewise
concern one installed vector $(M_i)$.

Proof. CP Theorem 5.1 gives a complete correct residual threshold-$q$
graph on $R$, with at most $m(R)$ installed states and both
uniform caps $N,C_R$ together. It fixes the old $S$ values,
retains realized $R$-labelled states, and suppresses fixed
$S$-labelled chains. No state is copied.

At a live residual prefix with $j$ ones and $z'$ zeros,
the corresponding original counts are
$(h+j,t-h+z')$. Its residual liveness inequalities give

$$
h+j\le k-1,\qquad
t-h+z'\le t-h+N-q=n-k=L-1.
\tag{SI.58}
$$

Thus the original prefix remains live. Original live freshness excludes
any intervening visit to an $S$ label. Induction on the live residual
prefix therefore identifies it with an actual original extension,
with identical current state and the same exposed $R$ assignment.
Conversely every live original extension of this fixed prefix appears
in the residual graph by its subsequence construction. Impossible
edges assigned arbitrary successors in CP's restriction cannot occur
on these actual histories.

At residual depth $b-t$, the corresponding original live extension
has depth $b$. Its support is $T_b$ if $b$ is an original cut.
Consequently its residual support is $T_b\setminus S$; in
particular $S\subseteq T_b$. This proves inheritance. Residual
depth zero is common even when $t$ was not an original cut, and
the residual formal endpoint is $N$. The inherited cuts divide
its depth range into intervals of length at most four under the
stated condition. Any additional residual common-support cuts
only subdivide those intervals. All gaps in the residual graph
therefore have span at most four.

The residual costs are the same distinct original $c_i=s_i+4$
for $i\in R$, reindexed in their original order. Apply Corollary
10.6 to this one complete residual graph at both $N,C_R$ caps:
its installed count is at least $q(N-q+1)$ and at most $m(R)$.
This proves (SI.56). Repeating this argument for different prefixes
never changes the meaning of any $m_i$. The different proof
restrictions are not disjoint allocated pieces of the original graph.

For the native assertion, CP Corollary 5.2 and the projection in WTF
Theorem 4.1 preserve the actual selected-state subsequence and give
projected multiplicities $m_i\le M_i$. A live cube prefix has the
same $S,h$ in that projection; a possible live cube-constant profile
call changes neither. Apply (SI.56) there and sum $m_i\le M_i$
over $R$. All calls suppressed in these mathematical restrictions
remain paid on the original native runs. The original apparatus
acquires no restriction, reset, residual entry or free transition.
$\square$

**Proposition 10.9 (late long-gap obstruction and the exact surviving
global sum).** For every complete graph in Convention 10.1,
the original comparison $m\ge G$ is equivalent to each of

$$
\begin{aligned}
\sum_{\substack{B\in\mathcal B\\\beta_B\ge5}}(D_B-E_B)
&\le E_{\mathrm{cut}}+u+
 \sum_{\substack{B\in\mathcal B\\\beta_B\le4}}(E_B-D_B),\\
\sum_{B\in\mathcal L_*}(D_B-E_B)
&\le E_{\mathrm{cut}}+u+
 \sum_{B\in\mathcal A_*}(E_B-D_B),
\end{aligned}
\tag{SI.59}
$$

where

$$
\mathcal L_*=\{(a,b)\in\mathcal B:b-a\ge5,\ b>e_*\},
\qquad \mathcal A_*=\mathcal B\setminus\mathcal L_*.
$$

Every summand on the right of either inequality is nonnegative.
A correct strict-subgrid graph at both caps must therefore have a
consecutive gap $B=(a,b)$ with

$$
b-a\ge5,\qquad b>e_*,\qquad
D_B>E_B,\qquad |Q_B|<|V_B|.
\tag{SI.60}
$$

Each internal depth of that gap contains a support-ambiguous cell,
so there are at least four consecutive such depths.
The right endpoint lies in $\{e_*+1,\ldots,n\}$, a set of
$d_*-1$ possible depths. The same necessity applies to the supplied
projection of every complete original native preparer with
$H_P<G+4+r$ at both native caps.

Proof. Split the exact identity (SI.32) first at span four and
then at the partition $\mathcal L_*,\mathcal A_*$. This proves
both equivalences (SI.59), without discarding any term. Theorems
9.4 and 10.4 make every span-at-most-four contribution
$E_B-D_B$ nonnegative. Any remaining interval in $\mathcal A_*$
ends at $b\le e_*$, and Lemma 10.2 gives $D_B=0$ there.
Thus all right-hand terms have the stated signs.

If $m<G$, the second inequality is strictly reversed. Some
$B\in\mathcal L_*$ has $D_B-E_B>0$; otherwise its left side
would be nonpositive. Equation (SI.33) gives the host deficit.
There are no common-support depths internal to this consecutive gap,
and Definition 9.1 supplies an ambiguous cell on each internal
diagonal. Its span supplies at least four of them. Finally
$n-e_*=\min(K,L)-1=d_*-1$. For a native strict saving,
$m\le H_P-4-r<G$ in its supplied projection, so this entire
argument applies to that same complete projected graph. $\square$

The unrestricted inequality (SI.59), in particular the late gaps of
span at least five, remains unresolved here. No complete correct
strict-subgrid graph is constructed. Proving $D_B\le E_B$ for
each remaining gap would suffice but is stronger than the stated
global sum, which permits cut excess, other interval excess and
genuinely nonlive states to compensate a deficit. With five or more
block coordinates there are more internal support layers; a common
live reply can lead to another shareable internal layer. The proof
of Lemma 10.3 therefore supplies no corresponding six-cell
classification or compensation at those spans. The simultaneous
CP inequalities and (SI.56) constrain one vector; subtracting lower
bounds on overlapping coordinate sets cannot assign their differences
as available states. The unrestricted-budget $H_{\min}$ also
retains its separate unresolved meaning.

These new deductions are repo-derived. Their mathematical suppliers
are Theorem 2.2, the local diagonal argument in Theorem 4.1, the
support exclusions cited in Section 2, and the exact localization
of Theorem 9.3; the span-at-most-three theorem is reused.
CP Theorem 5.1 supplies actual-prefix restriction, and WTF Theorem
4.1 with PCA Theorem 26.1 supplies the original full-fiber resource
map and grid. The fixed-representative obstructions of WTF Section
11 do not supply a separator-capacity premise here.

The literature boundaries are those of Section 8: Wegener,
Chapter 14.4, printed pages 423–425, treats BP1 and explicitly
uses realizability of every graph path in the normalization proof
on page 424; Bryant, Section 2, Definition 1, requires increasing
variable indices; CEMP, Section 2.1, assumes an acyclic graph and
read-once consistent accepting paths. None of these extra hypotheses
is imposed on the original paid graph by the arguments above.
The proofs use paired actual live extensions and charged installed
incidence, and make no worldwide priority assertion.

## 追加锚（本行以下为增补区）

## 11. All-history set-pairs capacity and an unbounded qualified gap class

**Convention 11.1 (the same complete paid graph).** Retain every
source, entry, cost, correctness and simultaneous-cap hypothesis of
Convention 10.1. In particular the graph is correct on every Boolean
input, at both $n,W$ caps, and its native consumer has the original
full-fiber meaning of (SI.5). Common-support cuts, pools and the
partition $\mathcal L_*,\mathcal A_*$ are exactly those of (SI.59).
The unrestricted inequality there remains the main unresolved target.
The condition below is imposed only on the actual live states of
remaining late-long pools. No order, read-once condition after a
certificate, or acyclicity of the syntactic union graph is imposed
on a competitor.

### 11.1 Actual prefixes, their multiplicity and normalized cell mass

**Definition 11.2 (all-history indices and both directed conflicts).**
Let $\mathscr H_p$ be the set of distinct actual live run prefixes
of count cell $p=(h,z)$, ending immediately before a query, and let
$\mathscr H(q)$ consist of all such prefixes ending at the installed
state $q$. A prefix records its finite sequence of states, queried
coordinates and replies, including its ending state. All completing
inputs that follow that identical prefix define one member, counted
once. Prefixes with the same ending state are not thereby identified.
For $H$ put

$$
A_H=\{i:\text{the exposed value at }i\text{ is }1\},\qquad
B_H=\{i:\text{the exposed value at }i\text{ is }0\}.
\tag{SI.61}
$$

Thus $A_H\cap B_H=\varnothing$, $S_H=A_H\cup B_H$, and
$|A_H|=h$, $|B_H|=z$. Assign the proof weight

$$
\omega(H)=\binom{h+z}{h}^{-1},\qquad
\lambda_p(q)=\sum_{H\in\mathscr H_p\cap\mathscr H(q)}\omega(H),
\qquad \lambda(q)=\sum_{H\in\mathscr H(q)}\omega(H).
\tag{SI.62}
$$

Call $q$ a both-conflict state when for every two distinct members
$H,H'\in\mathscr H(q)$,

$$
A_H\cap B_{H'}\ne\varnothing
\quad\hbox{and}\quad
A_{H'}\cap B_H\ne\varnothing.
\tag{SI.63}
$$

This is a condition on all its actual live prefixes, including different
prefixes in the same count cell. These weights are neither source
probabilities nor a distribution on actual inputs. The prefix sets,
assignments and sums are mathematical indices; no archive, accessible
history, randomization, counter or extra control is installed.

**Lemma 11.3 (exact all-history counting and faithful set-pair indices).**
For every $p=(h,z)\in V$, reply words with $h$ ones and $z$ zeros
are in bijection with $\mathscr H_p$. Consequently

$$
|\mathscr H_p|=\binom{h+z}{h},\qquad
\sum_{H\in\mathscr H_p}\omega(H)=1,
\qquad \sum_{q\in F_p}\lambda_p(q)=1.
\tag{SI.64}
$$

At a fixed installed state, different actual live prefixes give different
ordered pairs $(A_H,B_H)$. Any two such prefixes have incompatible
exposed assignments: at least one of their two directed intersections
in (SI.63) is nonempty. At a fixed cell and state, two distinct prefixes
have both directed intersections nonempty.

Proof. Theorem 2.2 makes each query in a live prefix fresh and its
query depth exactly $h+z$. Starting from the fixed start, a reply word
therefore determines at most one prefix, including its fixed states and
coordinate choices. Conversely every initial subword of a word with
these counts has counts bounded by $(h,z)$ and is live. Inductively
the current state cannot be terminal, its query is fresh, and either
requested value has an actual completion following the preceding
prefix. The fixed successor supplies the next live state. After the
whole word, any completion of its distinct-coordinate assignment is
one actual input realizing this entire prefix. This proves the
bijection and (SI.64), including the empty word and both axes. It
counts words, not choices of completions and not distinct endpoints.
In particular the total number of live prefixes is finite even if the
syntactic union graph contains cycles.

More generally every completion of an exposed assignment follows its
prefix, by deterministic induction. If two distinct prefixes ending
at $q$ had compatible assignments, choose one input completing both.
They would be prefixes of its same actual run. Equal lengths would
make them identical. Unequal lengths would visit $q$ twice on that
run. From the first repeated state, the stationary fixed-input
successors repeat forever, contradicting actual termination. Thus
compatibility is impossible. Since compatibility means that both
cross intersections are empty, at least one is nonempty. Equal set
pairs in particular would be compatible and are excluded. This also
shows that a purported duplicate index cannot be retained merely
because a different completing input was used.

Finally fix $p,q$. Theorem 2.2 gives one support $S$ for all these
prefixes. Their one sets are distinct subsets of $S$ of the same
cardinality $h$: equal one sets would give equal set pairs. Neither
one set can contain the other, so each has an element outside the
other. As their zero sets are their complements in $S$, this is exactly
both directed intersections. No uniqueness of history at $p,q$ is
asserted. $\square$

**Theorem 11.4 (classical capacity for all actual live histories).**
If $q\in Q_{\mathrm{live}}$ satisfies (SI.63), then

$$
\lambda(q)\le1.
\tag{SI.65}
$$

Proof. Use the classical nonuniform Bollobás set-pairs inequality in
[O'Neill and Verstraëte, Theorem 1, page 1][OV]: for a finite indexed
family of finite set pairs with disjoint diagonals and
$A_i\cap B_j\ne\varnothing$ whenever $i\ne j$,

$$
\sum_i\binom{|A_i|+|B_i|}{|A_i|}^{-1}\le1.
$$

Index the pairs by the actual members of $\mathscr H(q)$, rather
than by inputs, endpoints, or a representative chosen at each cell.
Lemma 11.3 gives a finite family and removes duplicate set pairs.
Equation (SI.61) gives every disjoint diagonal. Condition (SI.63)
gives every ordered off-diagonal intersection: the two directions
are both required, even when the two sizes or the two depths differ.
The denominator is exactly that in (SI.62), by live freshness.
Every hypothesis of the cited inequality is therefore matched.

A singleton family has weight at most one directly. This includes an
empty history, where $\binom00=1$, and an axis history, where the
weight is also one. If a pair in a both-conflict family has an empty
one set or empty zero set, it cannot have a second member, since one
required cross intersection would be empty. Thus these cases require
no implicit nonempty-set assumption on the classical supplier. The
empty live family, when considered, has mass zero. The proof uses no
probability law on the source and realizes no additional graph path.
$\square$

**Corollary 11.5 (arbitrary-span pool compensation).** For any
consecutive common-support gap $B=(a,b)$, the exact mass identities are

$$
\sum_{q\in Q_B}\lambda(q)=|V_B|,\qquad
\sum_{q\in Q_B}(1-\lambda(q))=E_B-D_B.
\tag{SI.66}
$$

If every $q\in Q_B$ is a both-conflict state, then, regardless of
the span and of every other gap,

$$
D_B\le E_B,\qquad |Q_B|\ge|V_B|.
\tag{SI.67}
$$

Proof. Theorem 9.3 says that all live occurrences of each $q\in Q_B$
belong to $V_B$, and that every history in a cell of $V_B$ ends in
$Q_B$. Sum the cell mass one in (SI.64), using these actual indices,
to obtain the first identity. Equation (SI.33) then gives the second.
Under the stated condition every term $1-\lambda(q)$ is nonnegative
by Theorem 11.4, proving (SI.67). Empty interiors give zero on both
sides. No independently acquired block entry, restriction operation,
or allocation of a paid separator is used. $\square$

### 11.2 Exact whole-table and original native consumers

**Definition 11.6 (the qualified class).** Let $\mathfrak C$ consist
of the complete graphs of Convention 11.1 for which

$$
B\in\mathcal L_*,\quad q\in Q_B
\quad\Longrightarrow\quad q\text{ satisfies (SI.63)}.
\tag{SI.68}
$$

There is no both-conflict requirement on cut states or on pools in
$\mathcal A_*$. In particular the entire class of Corollary 10.6,
whose late gaps have span at most four, is contained in $\mathfrak C$.

**Theorem 11.7 (qualified exact minima at both original caps).**
Every graph in $\mathfrak C$ satisfies

$$
D\le E,\qquad |Q_{\mathrm{live}}|\ge G,
\qquad m\ge G+u.
\tag{SI.69}
$$

For every original $n,k,A$ in Convention 11.1, the minimum Boolean
running-state count within $\mathfrak C$, at both caps $n,W$ on
one graph, is exactly $G=k(n-k+1)$. For complete original native
preparers whose supplied Boolean projection belongs to $\mathfrak C$,
the exact preparation minimum at both native caps $n+1,W+3$ is
$G+4+r$.

Proof. For $B\in\mathcal L_*$ apply Corollary 11.5. For every
other pool reuse the existing suppliers: Theorems 9.4 and 10.4
compensate spans at most four; Lemma 10.2 gives $D_B=0$ when
$b\le e_*$. These cover exactly $\mathcal A_*$, with no condition
on its state-history families. Summing on the same installed graph
in (SI.32), and retaining $E_{\mathrm{cut}}\ge0$, proves (SI.69).
No graph is changed between different pool arguments.

The supplied grid of PCA Theorem 26.1 has $G$ running states,
satisfies both caps and has every depth common-support. Thus
$\mathcal L_*$ is empty and it belongs to $\mathfrak C$, proving
equality. Its states generally have many actual live prefixes. More
explicitly, at its state of cell $(h,z)$ every prefix has the same
fixed support consisting of the first $h+z$ coordinates in its order.
Distinct histories give distinct $h$-element one sets in that support,
so Lemma 11.3 gives both conflicts and (SI.64) gives total mass one
at that state. This is the fixed-cell, fixed-support argument; the
grid's membership does not depend on a false unique-history premise.

For a native competitor, WTF Theorem 4.1 gives a complete correct
projection with both Boolean caps and $m\le H_P-4-r$. Its class
membership is an explicit hypothesis, so (SI.69) gives
$H_P\ge G+4+r$. Conversely the same supplied grid has the original
full-fiber lift with exactly $G+4+r$ preparation states and both
native caps. Its projection is the grid just discussed. Hence the
native projection-class minimum is attained as claimed.

The native quantifier remains over all finite nonempty ordered trees
in $\mathcal U_*$, of unbounded size, depth and shape, with the
original homomorphic $\rho$, complete current row and fixed pointwise
code (SI.2). The original repeated occurrences and different-class
disequalities are retained. The upper is the supplied full-fiber
upper, rather than a cube-only upper; the cube is a lower-witness
projection. Every finite original address and its alpha, beta, branch
and absent replies retain their original permission and meaning.
The original latches hand off literally to the complete $e_0,e_1$.
The independent original eight-state reader, with its three running
states and five whole-row halts, returns the ordered predecessor
exterior, all reached occurrences, its canonical equality partition,
repetitions, disequalities and strict-prefix guards. Its at most two
fresh queries and six letters remain separate charges.

All installed running, output, unused and latch states count; the
Boolean terminals are replaced by native latches, not charged twice.
Every actual constant, repeated or post-certificate invocation is
paid. Binding, authentication, acquired same-version data, native
access, export, isolation, code-only handoff, lawful complete entry
and stationary continuity remain the separate supplied services of
Convention 1.3. No free source copy, archive re-read, selector,
acquisition, record register, clock or address calculation follows.
This is an exact qualified installed-control theorem, not unrestricted
grid optimality or a physical realization theorem. $\square$

### 11.3 A complete interacting family with unbounded late gaps

**Proposition 11.8 (strict enlargement with actual live sharing and
paid post-certificate repeats).** For every integer $v\ge3$, set

$$
n=2v+4,\qquad k=v+2,\qquad s_i=i,\quad c_i=i+4,
\qquad a=v+2.
\tag{SI.70}
$$

There is a complete correct Boolean graph in $\mathfrak C$ whose
common-support depths are exactly $0,1,\ldots,a$, with formal
endpoint $n$. It has a consecutive late gap $(a,n)$ of span $v+2$,
genuine sharing by different live count cells, and actual paid repeated
queries after certification. Its exact installed running count and
attained simultaneous maxima are

$$
M_v=2^{2v+4}-2^{v+2}+2v+3,\qquad
\max t=n,\qquad \max J=W.
\tag{SI.71}
$$

Its full-fiber native lift has exactly $M_v+4+r$ preparation states,
attains both maxima $n+1,W+3$ on one actual source, and retains the
original separate eight-state reader. The family is above-grid and
lies outside the class of Corollary 10.6. It proves a strict infinite
enlargement of that class, with no strict-subgrid upper assertion.
Only the legitimate original cost family in (SI.70) is claimed here.

Proof, complete fixed table. Use the coordinate partition

$$
C=\{1,2,\ldots,v+2\},\quad I=\{3,\ldots,v+2\},\quad
x=v+3,\quad y=v+4,\quad
u_j=v+4+j\ (1\le j\le v),\quad U=\{u_1,\ldots,u_v\},
\tag{SI.72}
$$

so $C,\{x\},\{y\},U$ partition $[n]$ and $|C|=a$.
First define a full binary decision
tree with a distinct running state at every vertex of depth less
than $n$. It queries $1,2,\ldots,v+2$ in that order. At a depth-$a$
vertex use the remaining order $(y,x,u_1,\ldots,u_v)$ precisely
when its old assignment is $(\theta_1,\theta_2)=10$, $I=1^v$;
at every other depth-$a$ vertex use $(x,y,u_1,\ldots,u_v)$.
Each of these orders is fixed in the literals of its separate subtree.
Every zero or one edge goes to its corresponding child; a depth-$n$
edge goes to the common terminal $\mathsf0$ or $\mathsf1$ according
to the threshold of that leaf's complete assignment. This specifies
every state, query and successor of the full tree. No order is selected
or evaluated by an auxiliary runtime operation.

Delete exactly the two entire subtrees whose incoming histories are

$$
\begin{aligned}
\mathcal A:&\quad (\theta_1,\theta_2)=01,\quad I=0^v,\quad x=0,\\
\mathcal B:&\quad (\theta_1,\theta_2)=10,\quad I=1^v,\quad y=0.
\end{aligned}
\tag{SI.73}
$$

Each incoming history has depth $v+3$ and $v+1$ unread
coordinates. Redirect its incoming edge to the same new state $V$.
Install only the following additional running states, all distinct
from retained tree vertices and from the two terminals:

| State | Queried coordinate | Zero successor | One successor |
| --- | --- | --- | --- |
| $V$ | $u_1$ | $Z_2$ | $B_Y$ |
| $Z_j$, $2\le j<v$ | $u_j$ | $Z_{j+1}$ | $J$ |
| $Z_v$ | $u_v$ | $B_X$ | $J$ |
| $B_X$ | $x$ | $\mathsf0$ | $\mathsf1$ |
| $B_Y$ | $y$ | $J$ | $A_2$ |
| $A_j$, $2\le j<v$ | $u_j$ | $\mathsf0$ | $A_{j+1}$ |
| $A_v$ | $u_v$ | $\mathsf0$ | $\mathsf1$ |
| $J$ | $1$ | $\mathsf0$ | $\mathsf1$ |

The start is the retained tree root. All edges are now specified;
there is no transition to a deleted vertex. In particular $J$ is a
new ordinary query state at old coordinate $1$, not an uncharged
context selector. State names carry no accessible indices beyond the
counted current state. The $A_j$ rows form a distinct installed AND
chain; they are not an implicit call to a free residual solver.

Proof, correctness on every input. An input avoiding (SI.73) follows
a retained full-scan tree path and receives its exact threshold. The
only inputs entering $V$ are precisely those two contexts. Context
$\mathcal A$ has one old one and therefore needs all $v+1$ unread
bits in $\{y\}\cup U$; context $\mathcal B$ has $v+1$ old ones
and needs at least one unread bit in $\{x\}\cup U$. Their residuals
are AND and OR, respectively. Their old coordinate $1$ is respectively
zero and one, and their old private values are $x=0$ and $y=0$.

If $u_1=0$, the $Z$ chain reads until the first later one or until
all $U$ bits have been read. A later one makes the AND context
negative and the OR context positive; $J$ rereads coordinate $1$
and returns these respective values. If all $U$ bits are zero,
$B_X$ returns the correct zero from old $x=0$ on $\mathcal A$,
and computes the only remaining OR variable $x$ on $\mathcal B$.
If $u_1=1$, $B_Y$ reads $y$. When it is zero, $J$ returns the
negative AND answer and positive OR answer. When it is one, only
$\mathcal A$ is possible, since $\mathcal B$ has old $y=0$.
The remaining $A$ chain computes exactly the conjunction of
$u_2,\ldots,u_v$. These cases exhaust every completion of each
context and hence every Boolean input. Every tree path and every
suffix chain is finite, so all actual inputs terminate. Acyclicity
of this constructed example is not a restriction on competitors.

Proof, both caps with repeats charged. Write $C_X=\sum_{i\in X}c_i$
for subsets here, and $U_{\le j}=\{u_1,\ldots,u_j\}$. The two
prefixes pay respectively $C_C+c_x$ and $C_C+c_y$, with $v+3$
queries. The suffix has at most $v+1$ queries: an all-zero $U$
route uses $v$ scan states and $B_X$; a first later one at $u_j$
uses $j$ scan states and $J$; a $u_1=1,y=0$ route uses
$V,B_Y,J$, with $3\le v+1$; the remaining route uses $V,B_Y$
and at most $v-1$ AND states. Thus every such input has at most
$2v+4=n$ queries on this same table.

For all-zero $U$, the complete selected letter charges are

$$
\begin{aligned}
\mathcal A:&\ C_C+2c_x+C_U=W+c_x-c_y<W,\\
\mathcal B:&\ C_C+c_y+C_U+c_x=W.
\end{aligned}
\tag{SI.74}
$$

The first line includes the genuine repeated $x$. For the first
later one at $u_j$, $2\le j\le v$, the respective charges are
$C_C+c_x+C_{U_{\le j}}+c_1$ and
$C_C+c_y+C_{U_{\le j}}+c_1$, both at most $W$, because
$c_1<c_y$ and $c_1<c_x$, respectively. For $u_1=1,y=0$ they are

$$
C_C+c_x+c_{u_1}+c_y+c_1\le W,\qquad
C_C+2c_y+c_{u_1}+c_1\le W.
\tag{SI.75}
$$

The first uses $c_1<c_{u_2}\le C_{U\setminus\{u_1\}}$.
The second uses
$c_y+c_1<c_x+c_{u_2}\le c_x+C_{U\setminus\{u_1\}}$;
indeed $c_1<c_x$ and $c_y<c_{u_2}$ for the costs in (SI.70).
This pays for both the old $y$ and old coordinate $1$ on
$\mathcal B$. If $u_1=y=1$, only $\mathcal A$ occurs, and
all its queried coordinates are distinct, so it pays at most $W$.
Every retained ordinary tree route queries all $n$ coordinates once,
with charge $W$, including all visits after an early certificate.
Both caps have now been proved on every input, without deleting a
repeat or substituting a different table for a cost objective.

For simultaneous equality take a retained path with
$(\theta_1,\theta_2)=00$, $I=1^v$, $x=1$, $y=0$, and $U=0^v$.
It avoids both redirected prefixes, reads all coordinates and pays
$n,W$. For actual interaction, take $\mathcal A$ with $U=0^v$:
the AND is already negative after $u_1$, but $B_X$ still rereads $x$.
The same $B_X$ is live on $\mathcal B$ with $U=0^v$, where it
must decide the unread $x$. Likewise $\mathcal A$ and
$\mathcal B$ with $u_1=0,u_2=1$ both reach the paid $J$, after
opposite certificates, and require opposite outputs. These are real
old-coordinate visits in a shared continuation, not a common
certificate permitting that continuation to be erased globally.

Proof, exact installed count. The full tree has $2^n-1$ running
vertices. Each of the two deleted, disjoint subtrees has
$2^{v+1}-1$ running vertices. The replacement has one $V$,
$v-1$ states $Z_j$, two states $B_X,B_Y$, $v-1$ states $A_j$
and one $J$, totaling $2v+2$. Thus

$$
(2^n-1)-2(2^{v+1}-1)+(2v+2)=M_v.
\tag{SI.76}
$$

The Boolean total including its two distinct terminals is $M_v+2$.
All retained tree states after certification are still installed and
counted. Every retained running vertex is reachable by a completion
of its tree prefix, and every new suffix state has a realizing input;
no unused running states are added. This does not exclude genuinely
nonlive states: for example $J$ is reached only after certification.
The retained core alone contains $2^{v+2}-1>(v+2)(v+3)=G$
running states for $v\ge3$. The inequality holds at $v=3$ and
persists by doubling the exponential term. Hence $M_v>G$.

Proof, all-history class membership. A retained tree vertex has a
unique incoming prefix. Every actual live prefix of $Z_j$ or $B_X$
is in context $\mathcal B$ with all previously read $U$ bits zero;
context $\mathcal A$ was already certified by $u_1=0$. Every
actual live prefix of $B_Y$ or $A_j$ is in context $\mathcal A$
with all previously read residual bits one; context $\mathcal B$
was certified by $u_1=1$, and cannot enter $A_2$ because its old
$y$ is zero. These statements specify one live prefix per such state.
The incoming contexts of $J$ have both been certified, so it has no
live prefix. Only $V$ has two distinct live prefixes. Their one and
zero sets are

$$
\begin{array}{c|cc}
& A_H&B_H\\
\mathcal A&\{2\}&\{1\}\cup I\cup\{x\}\\
\mathcal B&\{1\}\cup I&\{2,y\}.
\end{array}
\tag{SI.77}
$$

Both are live: their count pairs are $(1,v+2)$ and $(v+1,2)$,
within $0\le h\le v+1$, $0\le z\le v+2$. Every completion is
an actual Boolean input. The two directed intersections are
$\{2\}$ and $\{1\}\cup I$, both nonempty. Thus every live
state of this example satisfies (SI.63), in particular every state
of its remaining late-long pool. At $V$ its exact mass is

$$
\lambda(V)=\binom{v+3}{1}^{-1}
             +\binom{v+3}{v+1}^{-1}
           =\frac{v+4}{(v+3)(v+2)}<1.
\tag{SI.78}
$$

This verifies genuine cross-count live sharing while retaining the
full family of histories rather than discarding either context.

Proof, consecutive late gap. All live histories through depth $a$
have support equal to the corresponding prefix of $C$, so every depth
$0,\ldots,a$ is common-support. At each depth $a+j$,
$1\le j\le v+1$, context $\mathcal B$ with its first $j-1$
$U$ bits zero is still live and has support

$$
S_j^{\mathcal B}=C\cup\{y\}\cup U_{\le j-1}.
\tag{SI.79}
$$

At $j=v+1$ this is its live prefix at $B_X$, before reading $x$.
For comparison the retained input used for cap equality has live
prefixes all the way to depth $n-1$: after $x=1$ its hit count is
$v+1$, and its zeros never exceed $v+2$. Their supports are

$$
S_1^{\mathrm{tree}}=C\cup\{x\},\qquad
S_j^{\mathrm{tree}}=C\cup\{x,y\}\cup U_{\le j-2}
\quad(2\le j\le v+1).
\tag{SI.80}
$$

Use $U_{\le0}=\varnothing$. At $j=1$ the two supports differ
by $x,y$; thereafter they differ by $x,u_{j-1}$. Thus no depth
strictly between $a$ and $n$ is common-support. The pair $(a,n)$
is consecutive, with span $v+2\ge5$ and right endpoint
$n>e_*=v+3$. Its span is unbounded over this infinite family.
Equations (SI.77) and the preceding singleton analysis prove membership
in $\mathfrak C$, whereas this very gap excludes the family from
Corollary 10.6. Together with that corollary's class inclusion, this
proves strict enlargement, not just a different numerical instance.

Proof, complete native realization of this table. Apply the existing
full-fiber lift of WTF Theorem 4.1 to exactly this Boolean graph.
Every coordinate-$i$ row above and every retained tree row queries
the fixed original literal $a_i=LLL L^iR$. Its four successors are
installed as $(\mathsf{alpha},\mathsf{beta},\mathsf{branch},
\mathsf{absent})\mapsto(\delta_0,\delta_0,\delta_1,\delta_0)$,
with the two terminals replaced by the original latches. Add the
original profile rows $D,T$ from that theorem: $D$ queries $RLR$
with successors $(\widehat e_1,\text{tree root},T,\widehat e_0)$,
and $T$ queries $RRR$ with successors
$(\widehat e_1,\widehat e_0,\widehat e_0,\widehat e_0)$ in the
same four-reply order. Start at $D$ and install all $r$ further
mandated distinct latches even though unused. This specifies all
native edges; no auxiliary phase state, reset or service is added.

On any source in $Z_{b_3}$, including arbitrary noncomb branch
images and absent selected nodes, the original all-address occurrence
identity gives one fixed Boolean indicator vector. The every-input
proof above therefore gives its exact prescribed latch. The other
ten profiles are handled by the unchanged profile front. This is a
full-$\mathcal U_*$ upper on the identical original code, not an
upper restricted to the cube. All selected runs pay their original
literal charges, including the actual repeats; $D$ adds one call and
three letters. Other profiles use at most two calls and six letters.
The actual cube supplier realizes the cap-attaining vector above by
a finite original source with every original disequality, so one
source attains $n+1,W+3$ together. There are exactly $M_v$ selected
running states, two profile states, two original-entry latches and
$r$ additional latches, totaling $M_v+4+r$. The separate reader
and every complete whole-row output are unchanged as in Theorem
11.7. $\square$

### 11.4 Necessary overload and the collective problem that remains

**Theorem 11.9 (overloaded-state and one-way cross-count obstruction).**
Any complete correct strict-subgrid graph at both original caps must
have a gap $B\in\mathcal L_*$ with $D_B>E_B$, a state $q\in Q_B$
with $\lambda(q)>1$, and two distinct actual live prefixes at that
same $q$, in different count cells, for which exactly one of

$$
A_H\cap B_{H'},\qquad A_{H'}\cap B_H
\tag{SI.81}
$$

is empty. Their distinct supports are incomparable; their count cells
obey (SI.7) and the stronger right-cut separation (SI.41). The gap
has span at least five, ends after $e_*$ and contains at least four
consecutive noncommon-support depths. The same necessity holds for
the supplied projection of an original native preparer with
$H_P<G+4+r$ at both native caps.

Proof. Proposition 10.9 gives the positive-deficit late gap and all
its stated span and cut properties. Equation (SI.66) then gives
$\sum_{q\in Q_B}\lambda(q)=|V_B|>|Q_B|$, forcing a mass
strictly larger than one at some installed state. By Theorem 11.4,
that state's all-history family fails (SI.63). For a witnessing pair,
Lemma 11.3 excludes compatible assignments, so the other directed
intersection is nonempty. The same lemma proves both intersections
nonempty for distinct histories at fixed $p,q$, so this pair must
come from different cells. Section 2's supplied exclusions forbid
nested supports and equal supports with unequal hits; they also give
(SI.7). Lemma 10.2 supplies (SI.41) within this same pool. The native
projection has $m\le H_P-4-r<G$, and the whole argument applies
to it without changing its installed vector. $\square$

**Proposition 11.10 (exact collective capacity balance).** Without
any both-conflict hypothesis, put

$$
\begin{aligned}
O_*&=\sum_{B\in\mathcal L_*}\sum_{q\in Q_B}
                         (\lambda(q)-1)_+,\\
S_*&=\sum_{B\in\mathcal L_*}\sum_{q\in Q_B}
                         (1-\lambda(q))_+,
\qquad x_+=\max(x,0).
\end{aligned}
\tag{SI.82}
$$

For this one complete graph the unrestricted comparison $m\ge G$
is equivalent to

$$
O_*\le S_*+E_{\mathrm{cut}}+u+
                  \sum_{B\in\mathcal A_*}(E_B-D_B).
\tag{SI.83}
$$

Proof. Equation (SI.66) gives
$D_B-E_B=\sum_{q\in Q_B}(\lambda(q)-1)$ for each remaining
pool. Split positive and negative parts and substitute in the second
inequality of (SI.59). The pools are disjoint by Theorem 9.3, so no
state or surplus is counted twice. All the other terms on the right
are the nonnegative supplied terms of SI9–SI10. $\square$

Equation (SI.83), equivalently the original unrestricted (SI.59), is
not proved for arbitrary competitors here. The class theorem forces
$O_*=0$ by an explicit sufficient condition; arbitrary graphs can
have overload. Neither a one-way pair nor an overloaded state by
itself suffices for a strict saving. Its positive mass can be paid by
underloaded states in the same or other remaining pools, by cut or
other-pool excess, or by genuinely nonlive installed states. Requiring
separate compensation in every long gap would be stronger than this
collective target. No normalization of an arbitrary competitor into
$\mathfrak C$ is supplied. The original general unrestricted-budget
$H_{\min}$ retains its separate unresolved meaning.

There are already complete above-grid overload suppliers. In PE
Theorem 8.1 the shared state $V$ has actual histories (PE.35) of
counts $(0,m+1)$ and $(m,1)$, giving
$\lambda(V)\ge1+1/(m+1)>1$. In PCA Proposition 36.1 its state
$V$ has histories (PCA.91) of counts $(0,3)$ and $(3,0)$, each of
weight one, hence $\lambda(V)\ge2$. Their full tables satisfy both
original caps and exceed the grid. These suppliers refute universal
pointwise capacity. They do not refute (SI.59) or its equivalent
(SI.83); a failure of the both-conflict sufficient condition is not
a failure of collective compensation.

### 11.5 Reuse, source fidelity and bounded attribution

The classical supplier in Theorem 11.4 is the nonuniform inequality,
not a new set-pairs theorem. Its precise accessible source is Jason
O'Neill and Jacques Verstraëte, *A generalization of the Bollobás set
pairs inequality*, arXiv:1812.00537v2, Theorem 1 on page 1 [OV].
That statement requires every ordered off-diagonal intersection and
disjoint diagonals. The original Bollobás text is not claimed as
independently obtained. An unordered incompatibility condition would
supply only at least one direction and would not justify the cited
inequality; the deterministic exclusion of Lemma 11.3 is deliberately
kept separate from the additional condition (SI.63).

The repository suppliers are Theorem 2.2 for live freshness and
fixed-cell support, Theorem 9.3 for all-actual localization, SI9–SI10
for all other pools, CP's actual-prefix restrictions on one installed
vector, WTF Theorem 4.1 for the original full-fiber native map, PCA
Theorem 26.1 for the attaining grid, and NBP Propositions 9.3, 15.2
and Theorem 15.5 for the actual fiber, exhaustive profiles and original
complete reader. These are reused with their stated source and
permission contracts. The all-history mass bridge, its qualified
consumer and its application to the unbounded-gap family are
repo-derived ordinary-paper deductions, with no local kernel
verification or independent whole-paper acceptance asserted.

Proposition 11.8 uses the existing PE Sections 5 and 8 and PCA
Section 36 private-prefix/shared-continuation motifs: an AND/OR pair,
paid old-coordinate discrimination, and repeated queries supported
by omitted costs. Its two opposing marker assignments are what
make both directed intersections hold. The complete construction,
all-history membership and consecutive unbounded late-gap proof
supply the strict class separation needed by Theorem 11.7. The
example's state count is above-grid; the example alone is not the
capacity theorem or an optimum improvement. WTF Section 11's
fixed-representative separator counterexamples are also retained as
suppliers and are not repackaged as this bridge.

The overlap comparison is bounded to the complete SI and CP volumes
and the cited WTF, PE, PCA and NBP passages, together with the stated
primary set-pairs source. It makes no worldwide novelty or exhaustive
private-library claim. The ordered hypothesis in Bryant Section 2,
Definition 1, and the acyclic semantic read-once hypotheses in CEMP
Section 2.1 remain distinct from the current paid graph. They are not
imported as lower-bound premises. The separately contracted quantum
acquisition, endpoint-timing and other formal suppliers provide no
numerical native installed-state transfer here. No unrelated axis,
arrival or private-discrepancy conditional class is needed for
(SI.68)–(SI.83), and no acquisition, physical-time or memory law is
inferred from these finite control counts.

[OV]: https://arxiv.org/pdf/1812.00537v2

## 追加锚（本行以下为增补区）

## 12. A proper prefix-hit cut between two block-swapped live orders

**Definition 12.1 (the two-order class on actual live histories).**
Retain Definitions 1.1–1.2 and Convention 1.3, including $n\ge6$,
$3\le k\le n-2$, the original distinct positive integer positions
$s_1<\cdots<s_n$, $c_i=s_i+4$, and both bounds (SI.3) on every
input of one complete correct terminating graph. Partition $[n]$
into fixed disjoint ordered lists
$\mathsf I,\mathsf X,\mathsf U,\mathsf Y,\mathsf V$, where

$$
|\mathsf I|=p\ge1,\qquad
\mathsf X=(x_1,\ldots,x_b),\quad
\mathsf Y=(y_1,\ldots,y_b),\quad b\ge1,
\qquad 1\le B\le p,\qquad c_{x_j}<c_{y_j}\ (1\le j\le b).
\tag{SI.84}
$$

The lists $\mathsf U,\mathsf V$ may be empty. A list used in a set
expression denotes its underlying set; $V$ without the sans-serif
font continues to denote the count rectangle (SI.4). Define the two
permutations by concatenation:

$$
\pi_0=(\mathsf I,\mathsf X,\mathsf U,\mathsf Y,\mathsf V),
\qquad
\pi_1=(\mathsf I,\mathsf Y,\mathsf U,\mathsf X,\mathsf V).
\tag{SI.85}
$$

The class condition quantifies over every actual live history of the
given installed graph. Before $\mathsf I$ has been completely read,
its next query is the next member of $\mathsf I$. Thereafter, writing
$h_{\mathsf I}$ for the number of its exposed ones in that block,
its next query at depth $d$ is $\pi_0(d+1)$ if
$h_{\mathsf I}<B$, and $\pi_1(d+1)$ if $h_{\mathsf I}\ge B$.
Thus every live portion follows the corresponding permutation prefix.
This is a property of actual histories, not an available operation for
choosing an order or computing a count. No selector, counter, phase,
archive or extra changing register is installed. After certification
there is no order restriction: all original paid repeats, certified/live
reuse, sharing and syntactic cycles remain permitted, subject to actual
termination and both bounds on each complete input run.

**Theorem 12.2 (one global injection of actual live hosts).** Every
graph satisfying Definition 12.1 admits an injection

$$
\Phi:V\longrightarrow Q_{\mathrm{live}},\qquad
\Phi(h,z)\in F_{(h,z)}.
\tag{SI.86}
$$

Consequently, on that same installed graph,

$$
|Q_{\mathrm{live}}|\ge G=k(n-k+1),\qquad
D\le E,\qquad m\ge G+u.
\tag{SI.87}
$$

There is no bound on common-support gap spans or on the lengths of
$\mathsf U,\mathsf V$. No attainment assertion for a fixed proper
switch $B$ is part of this theorem.

Proof. The live freshness and support exclusions are the supplied
facts in Section 2: Theorem 2.2, [PE, Lemma 4.1][PE] and
[PCA, Theorem 35.1][PCA]. We also use [PE, Theorem 3.1(2)][PE]
with its stated $n,k$ range. Its Boolean consequence is obtained by
lifting this entire graph through (SI.5): if lower-hit and higher-hit
actual live histories with incomparable supports $S,T$ share a host,
and all old bits in $T\setminus S$ on the higher-hit history are one,
then

$$
C_{T\setminus S}\le C_{S\setminus T}.
\tag{SI.88}
$$

The lift is correct on the full original fiber and obeys both native
caps, so every hypothesis of that supplier applies to the two actual
lifted cube histories. This use of the supplier adds no residual
predicate attached to a state and no restriction on certified traffic.

For a depth $d$, let $S_0(d),S_1(d)$ be the sets of the first $d$
coordinates in (SI.85). Suppose first that these sets differ, and put

$$
P_d=S_0(d)\setminus S_1(d),\qquad
Q_d=S_1(d)\setminus S_0(d),\qquad q_d=|P_d|=|Q_d|>0.
\tag{SI.89}
$$

The entire $\mathsf I$ block has then been read. During the first
swapped block, $P_d,Q_d$ are matched nonempty prefixes of
$\mathsf X,\mathsf Y$; during $\mathsf U$ they are the full
blocks; during the second swapped block they are matched nonempty
suffixes. Thus (SI.84) gives

$$
C_{P_d}<C_{Q_d},\qquad q_d\le d-p.
\tag{SI.90}
$$

A mode-zero exposed assignment on $S_0(d)$ can have any total number
of ones in the integer interval $[0,B-1+d-p]$: its $\mathsf I$
count ranges over $[0,B-1]$ and its other exposed bits are free.
A mode-one assignment on $S_1(d)$ with every $Q_d$ bit one can have
any total in $[B+q_d,d]$: its $\mathsf I$ count ranges over $[B,p]$
and the other $d-p-q_d$ bits are free. For every live cell
$(h,d-h)$ choose a mode-zero assignment if $h\le B+q_d-1$;
otherwise choose a mode-one assignment with $Q_d$ all one. The first
choice is possible by $q_d\le d-p$, and the second is possible by
the displayed mode-one interval. These choices cover every live cell,
including when one of the two ranges contains no live count.

Each chosen assignment realizes an actual history. Its final counts
satisfy $h<k$ and $d-h\le n-k$, so every earlier prefix of its
chosen permutation has live counts as well. Induct from the fixed
start on any completion of the assigned bits. Correctness forbids a
terminal while both outputs remain possible, and Definition 12.1
forces exactly the next permutation coordinate. Before the switch the
order is common; after it the completed $\mathsf I$ assignment
forces the chosen mode. Fixed successors then realize the entire
prefix and its ending live host. No arbitrary syntactic path has been
assumed actual. At a depth with $S_0(d)=S_1(d)$, all actual live
histories have that common support; Theorem 2.2 supplies a history for
every live count cell there. Select any one of its hosts.

At one depth, selected histories in the same mode have equal supports
and different hit counts, so cannot share a host. This also separates
all selected cells at a common-support depth. At a differing-support
depth, a selected cross-mode pair has strictly fewer hits on its
mode-zero member, and all private $Q_d$ bits are one on its
mode-one member. Their equal-sized distinct supports are incomparable.
A shared host would therefore give $C_{Q_d}\le C_{P_d}$ by
(SI.88), contradicting (SI.90). The selected hosts at each depth are
distinct.

To separate different depths, use each installed state's single fixed
coordinate label. Every coordinate of $\mathsf I,\mathsf U,
\mathsf V$ occupies the same unique position in both permutations,
so such a state cannot be live at two different depths. For $x_j$,
the only possible predecessor supports at its early and late live
positions are respectively

$$
\mathsf I\cup\{x_1,\ldots,x_{j-1}\},\qquad
\mathsf I\cup\mathsf Y\cup\mathsf U
                  \cup\{x_1,\ldots,x_{j-1}\}.
\tag{SI.91}
$$

They are properly nested, since $b\ge1$. For $y_j$ the corresponding
supports are $\mathsf I\cup\{y_1,\ldots,y_{j-1}\}$ and
$\mathsf I\cup\mathsf X\cup\mathsf U
\cup\{y_1,\ldots,y_{j-1}\}$, again properly nested. PE Lemma 4.1
excludes a common live host in each case. This derives cross-depth
separation from actual live positions; it does not level the installed
graph.

There is now one distinct selected actual host for every
$(h,z)\in V$, proving (SI.86). There are $G$ such cells. Since
$|Q_{\mathrm{live}}|=G+E-D$ by Theorem 5.2, the remaining
assertions follow. A selected state may also be visited after
certification on another input; it is counted once. No paid
discriminator is assigned automatically to $u$ or outside the selected
image, and unused installed states retain their original count.
$\square$

**Corollary 12.3 (the original native lower consumer).** Let an
original complete native preparer be correct on every
$u\in\mathcal U_*$ at both caps $n+1,W+3$. If its particular
Boolean projection supplied by [WTF, Theorem 4.1][WTF] satisfies
Definition 12.1, its installed preparation count obeys

$$
H_P\ge k(n-k+1)+4+r.
\tag{SI.92}
$$

Proof. That projection is one complete correct Boolean graph at both
caps $n,W$, with $m\le H_P-4-r$. Apply Theorem 12.2. Membership
is required of this projection; it is not inferred for arbitrary native
competitors. The source, fixed pointwise code (SI.2), original latch
output and literal complete $e_0,e_1$ entries are those of Definition
1.1 and Convention 1.3. All finite original addresses and all four
replies remain legal. The independent reader retains its three running
states and five whole-row halts, hence its separately priced eight
states and fresh bounds two queries and six letters. It returns the
entire predecessor exterior, occurrences, canonical equality partition,
repetitions, disequalities and strict-prefix guards. Every installed
running, output, latch and unused state, and every actual constant,
repeated or postcertificate invocation, retains its original charge.
The services and resource distinctions in Convention 1.3 remain
assumptions, not consequences of (SI.92). $\square$

**Proposition 12.4 (complete feasible overload at unbounded span
outside the prior classes).** For every integer $a\ge2$, set

$$
\begin{gathered}
n=2a+5,\quad k=a+2,\quad s_i=i,\quad c_i=i+4,\quad t_0=1,\\
\mathsf I=(1,6,7,\ldots,a+5),\quad
\mathsf X=(2,3),\quad \mathsf Y=(4,5),\quad
\mathsf U=(a+6,a+7,\ldots,2a+5),\quad
\mathsf V=\varnothing,\quad B=1.
\end{gathered}
\tag{SI.93}
$$

There is a complete graph in Definition 12.1 with exactly

$$
M_a=2^n-2^{a+3}+2a+5>G=(a+2)(a+4)
\tag{SI.94}
$$

installed running states, correct on every input with simultaneous
maxima $n,W$. Its common-support depths are exactly
$0,1,\ldots,a+1$, followed by the formal endpoint $n$. In the
consecutive terminal gap $(a+1,n)$, of unbounded span $a+4\ge6$,
an actual live state $R$ has

$$
\lambda(R)=1+\binom{a+3}{2}^{-1}>1.
\tag{SI.95}
$$

The graph belongs neither to $\mathfrak C$ of Definition 11.6 nor
to the enlarged terminal-exception class $\mathfrak C_5$ of
[TS, Definition 6.3][TS]. Its full-fiber native lift has exactly
$M_a+4+r$ preparation states and simultaneous maxima $n+1,W+3$,
with the unchanged separately priced complete reader. This is an
inclusion witness for Theorem 12.2, not a strict-subgrid upper.

Proof, complete fixed graph. Begin with a full binary tree with a
distinct running vertex at every depth less than $n$. Read
$\mathsf I$ first. At each depth-$a+1$ vertex use the remaining
order $\mathsf X,\mathsf U,\mathsf Y$ if its literal
$\mathsf I$ assignment is all zero, and
$\mathsf Y,\mathsf U,\mathsf X$ otherwise. These labels are fixed
in the separate descendant vertices; no runtime mode selection is
supplied. Each edge goes to its corresponding child, except that the
last edge goes to the common terminal whose value is the threshold of
that leaf's complete assignment. This defines every parent edge.

Delete precisely the two disjoint full running subtrees after the
following depth-$a+3$ prefixes, and redirect their incoming edges to
one new state $R$:

$$
\mathcal A:\quad \mathsf I=0^{a+1},\quad \mathsf X=00,
\qquad
\mathcal D:\quad \mathsf I=1^{a+1},\quad \mathsf Y=00.
\tag{SI.96}
$$

Write $\mathsf U=(u_1,\ldots,u_a)$. Install the following table,
with all its states distinct from retained tree vertices and terminals.
Ranges $2\le j<a$ are empty when $a=2$.

| State | Coordinate | Zero successor | One successor |
| --- | --- | --- | --- |
| $R$ | $u_1$ | $Z_2$ | $O_2$ |
| $Z_j$, $2\le j<a$ | $u_j$ | $Z_{j+1}$ | $J$ |
| $Z_a$ | $u_a$ | $X_1$ | $J$ |
| $O_j$, $2\le j<a$ | $u_j$ | $J$ | $O_{j+1}$ |
| $O_a$ | $u_a$ | $J$ | $Y_1$ |
| $X_1$ | $2$ | $X_2$ | $\mathsf1$ |
| $X_2$ | $3$ | $\mathsf0$ | $\mathsf1$ |
| $Y_1$ | $4$ | $J$ | $Y_2$ |
| $Y_2$ | $5$ | $\mathsf0$ | $\mathsf1$ |
| $J$ | $t_0=1$ | $\mathsf0$ | $\mathsf1$ |

The start is the retained tree root. There is no edge to a deleted
vertex, and these are all additional states and edges. The scan has
$2a-1$ states: one start and two homogeneous-prefix chains. It exits
to $J$ at the first mixture of zero and one in $\mathsf U$, to
$X_1$ when all of $\mathsf U$ is zero, and to $Y_1$ when all of
$\mathsf U$ is one. The five remaining rows are ordinary paid states.

Proof, every-input correctness and the live-order rule. Exactly the
two cylinders (SI.96) enter the new suffix. At $\mathcal A$ the
residual is AND on $\mathsf U\cup\mathsf Y$, since there are no
old ones and $a+2$ unread bits. At $\mathcal D$ it is OR on
$\mathsf U\cup\mathsf X$, since there are $a+1=k-1$ old ones.
The old bit $t_0$ is respectively zero and one.

A mixed $\mathsf U$ certifies zero for $\mathcal A$ and one for
$\mathcal D$; $J$ returns those values. If $\mathsf U$ is all
zero, $X_1,X_2$ compute the remaining OR for $\mathcal D$; on
$\mathcal A$ their old $00$ returns the already certified zero.
If $\mathsf U$ is all one, $Y_1$ with reply one proceeds to
$Y_2$, computing the remaining AND for $\mathcal A$. Reply zero
at $Y_1$ goes to $J$, which returns zero on $\mathcal A$ and
one on $\mathcal D$; the latter always has old $y_1=0$.
These cases exhaust all assignments in both cylinders. Every other
input follows its retained full threshold-tree path. All routes terminate.

The retained tree follows (SI.85) even after certification. In the
shared suffix, $\mathcal A$ stays live only along the all-one
$\mathsf U$ scan and then its fresh $\mathsf Y$ queries;
$\mathcal D$ stays live only along the all-zero scan and then its
fresh $\mathsf X$ queries. Every old-coordinate repeat occurs on an
already certified history. In particular $J$ is reached only after
certification, while $X_1,X_2,Y_1$ can be certified on one origin
and live on the other. Thus every actual live history obeys Definition
12.1 without assigning a single residual to these shared states.

Proof, both caps on every complete run. The redirected prefix uses
$a+3$ queries, the scan at most $a$, and each exit at most two;
the total is at most $2a+5=n$. Retained paths read each coordinate
once, so their charge is exactly $n,W$, including postcertificate
visits. For letters, the relevant identities are

$$
c_{t_0}=5,\qquad C_{\mathsf X}=13,\qquad C_{\mathsf Y}=17,
\qquad c_{y_1}+c_{t_0}=8+5=13=C_{\mathsf X}.
\tag{SI.97}
$$

On all-zero $\mathsf U$, the $\mathcal A$ run pays
$C_{\mathsf I}+2C_{\mathsf X}+C_{\mathsf U}=W-4$;
the $\mathcal D$ run pays at most
$C_{\mathsf I}+C_{\mathsf Y}+C_{\mathsf U}+C_{\mathsf X}=W$.
On all-one $\mathsf U$, $\mathcal A$ pays either $W$ through
$Y_1,Y_2$, or $W-4$ through $Y_1,J$. The $\mathcal D$ run
pays $C_{\mathsf I}+C_{\mathsf Y}+C_{\mathsf U}
+c_{y_1}+c_{t_0}=W$, including both repeated coordinates.
For a mixed scan exiting at $u_j$, put
$\mathsf U_{\le j}=\{u_1,\ldots,u_j\}$. Its complete charges are

$$
C_{\mathsf I}+C_{\mathsf X}+C_{\mathsf U_{\le j}}+c_{t_0},
\qquad
C_{\mathsf I}+C_{\mathsf Y}+C_{\mathsf U_{\le j}}+c_{t_0}.
\tag{SI.98}
$$

Both are at most $W$: the first omits $\mathsf Y$, the second
omits $\mathsf X$, and each omitted block costs more than
$c_{t_0}$, in addition to any unread $\mathsf U$ tail. These
are bounds on each actual input, with every repeat paid. Taking
$\mathcal A$, $\mathsf U=1^a$, $\mathsf Y=11$ reads all $n$
distinct coordinates and attains $n,W$ together.

Proof, all installed states. The parent has $2^n-1$ running vertices.
Each deleted subtree has $2^{a+2}-1$, since $a+2$ coordinates remain
at its incoming edge. The replacement installs $(2a-1)+5=2a+4$
running states. Hence its full installed running count is

$$
(2^n-1)-2(2^{a+2}-1)+(2a+4)=M_a.
\tag{SI.99}
$$

Every retained or added state counts, whether live, certified-only or
unused. Already the retained vertices at depths $0,\ldots,a+2$
number $2^{a+3}-1>(a+2)(a+4)$ for $a\ge2$: this holds at
$a=2$ and persists under doubling. Thus the graph is above-grid.
Its Boolean total including the two shared terminals is $M_a+2$.

Proof, actual overload and the consecutive late gap. Exactly the two
prefixes (SI.96) reach $R$, both live, with counts $(0,a+3)$ and
$(a+1,2)$. Their one and zero sets are

$$
\begin{array}{c|cc}
& A_H&B_H\\
\mathcal A&\varnothing&\mathsf I\cup\mathsf X\\
\mathcal D&\mathsf I&\mathsf Y.
\end{array}
\tag{SI.100}
$$

Thus $A_{\mathcal A}\cap B_{\mathcal D}=\varnothing$ and
$A_{\mathcal D}\cap B_{\mathcal A}=\mathsf I\ne\varnothing$.
The exact all-history weights (SI.62) give (SI.95). No other live
prefix is hidden in that mass calculation.

All live histories through depth $p=a+1$ read the same prefix of
$\mathsf I$. For every later depth through $n-1$, compare the
actual input $\mathcal A$, $\mathsf U=1^a$, $\mathsf Y=11$
with $\mathcal D$, $\mathsf U=0^a$, $\mathsf X=00$. Both
remain live before their last query: their counts never exceed
$k-1=a+1$ ones or $n-k=a+3$ zeros there. At depth $p+1$ their
supports differ by $x_1,y_1$; at depths $p+2$ through $p+2+a$
they contain respectively the full $\mathsf X$ and full
$\mathsf Y$ blocks and the same $\mathsf U$ prefix; at depth
$n-1$ they omit respectively $y_2$ and $x_2$. Every one of these
pairs differs. Hence there is no further common-support depth.
The terminal gap has span $n-p=a+4\ge6$ and ends at
$n>e_*=a+4$. The overloaded $R$, at depth $a+3$, lies in its
remaining late-long pool. It violates (SI.68). Since this gap is not
the terminal span-five interval, its violation also lies outside the
exception allowed in [TS, Definition 6.3][TS]. This proves exclusion
from $\mathfrak C_5$, and hence also from its subclass
$\mathfrak A_5$, without assuming pointwise capacity for other states.

Proof, full original native lift. Use the constructive direction of
WTF Theorem 4.1 on this entire correct table. For each retained tree
row and each displayed coordinate-$i$ row install the original literal
$a_i=LLL L^iR$, with four successors
$(\mathsf{alpha},\mathsf{beta},\mathsf{branch},\mathsf{absent})
\mapsto(\delta_0,\delta_0,\delta_1,\delta_0)$, replacing terminals
by $\widehat e_0,\widehat e_1$. Add the two original paid profile
rows: $D_0$ queries $RLR$ with successors
$(\widehat e_1,\text{tree root},T_0,\widehat e_0)$, and $T_0$
queries $RRR$ with successors
$(\widehat e_1,\widehat e_0,\widehat e_0,\widehat e_0)$, in that
same four-reply order. Start at $D_0$ and install all $r$ further
mandated distinct latches, even though unused.

For every source of $Z_{b_3}$, an arbitrary branch image determines
one fixed indicator vector. The all-address occurrence identity makes
its entire selected run the Boolean run on that vector, including
absent replies and all paid repeats. The other ten profiles are
handled by the two original profile rows. This proves correctness on
the entire original $\mathcal U_*$ of unbounded finite nonempty
ordered alpha/beta trees with the homomorphic $\rho$, complete current
row, every actual inverse source, all repeated occurrences and all
different-class disequalities. The prescribed pointwise code and the
literal complete entries are unchanged. The selected route adds one
call and three letters; the other profiles use at most two calls and
six letters. The actual cube supplier realizes the cap-attaining vector
above, so one actual source attains $n+1,W+3$ simultaneously. The
count is exactly $M_a+4+r$, including the two profile rows, both
original-entry latches and every unused mandated latch. The separate
eight-state reader and the full predecessor target remain exactly as
in Corollary 12.3. Binding, authentication, access, same-source export,
code-only handoff, lawful complete entry and stationary continuity
remain the separate supplied and priced services of Convention 1.3.
No source copy, code reread, computed address or new work register
is obtained. $\square$

Theorem 12.2 is a deduction from the credited local exclusions and
one-sided private charge, using a choice of actual representatives
and fixed-label cross-depth separation on one complete graph.
Proposition 12.4 adapts the private-exchange continuation motifs of
PE Sections 5 and 8 and PCA Section 36 solely to establish actual
overloaded inclusion outside the earlier sufficient classes. The
SI11 all-history capacity, [the strict short-block bounds,
Theorems 4.1–4.2][SB], [TS, Theorem 6.4][TS] and
[TC, Sections 1–9][TC] remain prior results. In particular the new
injection is neither the both-conflict premise nor the sparse-run
alternative of TC Theorem 9.1. The witness's overload does not imply
a state saving, and the theorem does not require each late gap
separately to compensate its deficit.

The literature comparisons retain their exact hypotheses. Bryant's
Section 2, Definition 1 and Theorem 1 [Bryant] concern graphs with
strictly increasing indices on every nonterminal edge. Wegener's
Chapter 14, Section 4, printed pages 423–425 [Wegener] concerns BP1;
its normalization uses realizability of every graph path. Neither
hypothesis follows from the live-only condition (SI.85), which allows
paid certified repeats. Király, Nagy, Pálvölgyi and Visontai,
*On weakly intersecting pairs of sets*, Definition 1.1 [KNPV], require
at least one directed cross intersection for each pair, whereas SI11
requires both. That abstract set-system condition supplies no actual
fixed-successor realization or original-cost bridge. No external
normalization or worldwide priority claim is used here.

For $\min(k,n-k+1)\ge4$, the unrestricted collective inequality
(SI.59), equivalently (SI.83), and the alternative of a complete correct
strict-subgrid graph at both original caps remain unresolved. The
unrestricted-budget $H_{\min}$ remains a separate question. No
transformation of arbitrary competitors into Definition 12.1, no
necessity of its cost orientation, and no attained minimum for each
fixed proper switch has been established. No installed-state number,
operation or acquisition permission is transferred from a quantum,
calibration, stochastic timing, analytic or expanded-storage contract;
no physical memory, time or realization bound follows.

[TS]: FIB_NATIVE_TERMINAL_SPAN_FIVE_STRICT_COMPENSATION.md
[SB]: FIB_NATIVE_SUPPORT_BARRIERS_AND_SHORT_BLOCK_COMPENSATION.md
[TC]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_THRESHOLD_COST_CERTIFICATES.md
[KNPV]: https://domotorp.web.elte.hu/cikkek/setpairs.pdf

## 追加锚（本行以下为增补区）
